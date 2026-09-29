'use strict';
/* おうちアプローチ — 自宅用アプローチ計測器
   セキュリティ方針:
   - カメラ映像はこの端末の中だけで処理し、保存も送信もしない
   - 端末間で送るのは数値だけ(WebRTCで暗号化された直接通信。中継サーバーは使わない)
   - 受け取ったデータは種類・数値範囲・大きさを検査してから使い、画面にはテキストとしてのみ表示する */
(() => {
// ===== ball physics (real golf ball equivalent) =====
const SIM = (() => {
  const G = 9.81, RHO = 1.2, R = 0.02135, M = 0.04593, A = Math.PI * R * R;
  const CUP_R = 0.054;
  function zoneAt(course, x, z) {
    const dx = (x - course.green.cx) / course.green.rx;
    const dz = (z - course.green.cz) / course.green.rz;
    const d = Math.sqrt(dx * dx + dz * dz);
    if (d <= 1) return 'green';
    if (d <= 1 + 1.2 / Math.min(course.green.rx, course.green.rz)) return 'fringe';
    return 'rough';
  }
  const SURF = {
    green:  { e: 0.42, mu: 0.40, muk: 0.35, dig: 0.055 },
    fringe: { e: 0.30, mu: 0.55, muk: 0.5, dig: 0.09 },
    rough:  { e: 0.18, mu: 0.70, muk: 0.7, dig: 0.12 }
  };
  function rollDecel(course, zone) {
    if (zone === 'green') return 5.49 / course.stimp;
    if (zone === 'fringe') return 1.6;
    return 3.6;
  }
  // shot: {speed m/s, angle deg, dir deg (+ = right), spin rpm}
  function simulate(shot, course) {
    const dt = 1 / 240;
    const th = shot.angle * Math.PI / 180, ph = shot.dir * Math.PI / 180;
    let p = [0, 0.0, 0];
    let v = [shot.speed * Math.cos(th) * Math.cos(ph), shot.speed * Math.sin(th), shot.speed * Math.cos(th) * Math.sin(ph)];
    let w = shot.spin * 2 * Math.PI / 60; // backspin rad/s (+)
    const pts = [[0, p[0], p[1], p[2]]];
    let t = 0, phase = 'air', carry = null, bounces = 0, holed = false;
    const cup = course.pin;
    for (let i = 0; i < 240 * 30; i++) {
      t += dt;
      if (phase === 'air') {
        const sp = Math.hypot(v[0], v[1], v[2]);
        const S = sp > 0.1 ? R * Math.abs(w) / sp : 0;
        const Cl = Math.sign(w) * (S < 0.3 ? 1.99 * S - 3.25 * S * S : 0.305);
        const Cd = 0.3;
        const k = 0.5 * RHO * A / M * sp;
        // lift dir: perpendicular to v in vertical plane, up
        const hs = Math.hypot(v[0], v[2]) || 1e-6;
        const hx = v[0] / hs, hz = v[2] / hs;
        const lx = -v[1] * hx / sp, ly = hs / sp, lz = -v[1] * hz / sp;
        v[0] += (-k * Cd * v[0] + k * sp * Cl * lx) * dt;
        v[1] += (-G - k * Cd * v[1] + k * sp * Cl * ly) * dt;
        v[2] += (-k * Cd * v[2] + k * sp * Cl * lz) * dt;
        w *= Math.exp(-dt / 25);
        p[0] += v[0] * dt; p[1] += v[1] * dt; p[2] += v[2] * dt;
        if (p[1] <= 0) {
          p[1] = 0;
          if (carry === null) carry = { x: p[0], z: p[2] };
          bounces++;
          const zone = zoneAt(course, p[0], p[2]);
          const s = SURF[zone];
          const vy = Math.abs(v[1]);
          const e = Math.max(0.08, s.e - 0.045 * vy);
          const hs2 = Math.hypot(v[0], v[2]);
          const ux = hs2 > 1e-6 ? v[0] / hs2 : 1, uz = hs2 > 1e-6 ? v[2] / hs2 : 0;
          let vt = hs2 * Math.max(0.35, 1 - s.dig * vy);
          const need = (2 / 7) * (vt + R * w);
          const avail = s.mu * (1 + e) * vy;
          if (avail >= Math.abs(need)) {
            vt = (5 * vt - 2 * R * w) / 7; w = -vt / R;
          } else {
            const sg = Math.sign(vt + R * w);
            vt -= sg * avail; w -= sg * (5 / (2 * R)) * avail;
          }
          v = [ux * vt, e * vy, uz * vt];
          if (e * vy < 0.45) { v[1] = 0; phase = 'roll'; }
        }
      } else {
        const zone = zoneAt(course, p[0], p[2]);
        const s = SURF[zone];
        const hs2 = Math.hypot(v[0], v[2]);
        const ux = hs2 > 1e-6 ? v[0] / hs2 : 1, uz = hs2 > 1e-6 ? v[2] / hs2 : 0;
        let vt = hs2;
        const slip = vt + R * w;
        if (Math.abs(slip) > 0.03) {
          const a = s.muk * G * Math.sign(slip);
          vt -= a * dt; w -= (5 / (2 * R)) * a * dt;
        } else {
          const dec = rollDecel(course, zone);
          vt = Math.max(0, vt - dec * dt); w = -vt / R;
        }
        v[0] = ux * vt; v[2] = uz * vt;
        if (zone === 'green') {
          v[0] += (5 / 7) * G * course.slope.x * dt;
          v[2] += (5 / 7) * G * course.slope.z * dt;
          if (vt < 0.0 ) {}
        }
        p[0] += v[0] * dt; p[2] += v[2] * dt;
        const dc = Math.hypot(p[0] - cup.x, p[2] - cup.z);
        const spd = Math.hypot(v[0], v[2]);
        if (dc < CUP_R && spd < 1.6) { holed = true; p[0] = cup.x; p[2] = cup.z; p[1] = -0.03; pts.push([t, p[0], p[1], p[2]]); break; }
        const slopeMag = zone === 'green' ? Math.hypot(course.slope.x, course.slope.z) : 0;
        if (spd < 0.02 && Math.abs(slip) < 0.03 && slopeMag < 0.035) break;
        if (spd < 0.02 && Math.abs(slip) < 0.03) { v = [0, 0, 0]; }
      }
      if (i % 4 === 0) pts.push([t, p[0], p[1], p[2]]);
    }
    pts.push([t, p[0], p[1], p[2]]);
    const end = { x: p[0], z: p[2] };
    return {
      pts, carry: carry || end, end, holed, bounces,
      toPin: holed ? 0 : Math.hypot(end.x - cup.x, end.z - cup.z),
      total: Math.hypot(end.x, end.z), duration: t
    };
  }
  return { simulate, zoneAt };
})();



const $ = (id) => document.getElementById(id);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const yd = (m) => m / 0.9144;
const store = {
  get(k, d) { try { const v = localStorage.getItem('oa_' + k); return v == null ? d : JSON.parse(v); } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem('oa_' + k, JSON.stringify(v)); } catch (e) {} }
};
function toast(t) { const el = $('toast'); el.textContent = t; el.hidden = false; clearTimeout(toast._t); toast._t = setTimeout(() => { el.hidden = true; }, 3200); }
function setConn(state, text) { $('connDot').className = 'dot ' + (state || ''); $('connText').textContent = text; }

/* ---------------- role ---------------- */
let role = store.get('role', null);
function showRole(r) {
  role = r; store.set('role', r);
  $('roleView').hidden = !!r;
  $('camView').hidden = r !== 'camera';
  $('greenView').hidden = r !== 'green';
  $('switchRole').hidden = !r;
  if (r === 'green') { Green.init(); Net.host(); }
  if (r === 'camera') Net.initCamera();
}
$('pickCam').onclick = () => showRole('camera');
$('pickGreen').onclick = () => showRole('green');
$('switchRole').onclick = () => { store.set('role', null); location.reload(); };

/* ---------------- network (PeerJS / WebRTC) ---------------- */
const Net = (() => {
  const ALPHA = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789'; // 紛らわしい文字(0/O, 1/I/L)を除外
  const PREFIX = 'ouchi-approach-v1-';
  const PEER_OPTS = { debug: 0, config: { iceServers: [{ urls: 'stun:stun.l.google.com:19302' }] } }; // TURN中継は使わない
  let peer = null, conn = null, code = null;
  function randCode(n) { const a = new Uint32Array(n); crypto.getRandomValues(a); let s = ''; for (const v of a) s += ALPHA[v % ALPHA.length]; return s; }
  function fmt(c) { return c.slice(0, 4) + '-' + c.slice(4); }
  function norm(s) { return String(s || '').toUpperCase().replace(/[^A-Z0-9]/g, ''); }
  function safeParse(data) {
    // PeerJS json serialization gives objects; reject anything large or odd
    let obj = data;
    if (typeof data === 'string') { if (data.length > 2000) return null; try { obj = JSON.parse(data); } catch (e) { return null; } }
    if (!obj || typeof obj !== 'object' || Array.isArray(obj)) return null;
    try { if (JSON.stringify(obj).length > 2000) return null; } catch (e) { return null; }
    return obj;
  }

  /* iPad side: waits for one iPhone */
  function host(fresh) {
    if (peer && !fresh) return;
    if (peer) { try { peer.destroy(); } catch (e) {} peer = null; conn = null; }
    code = randCode(8);
    $('codeOut').textContent = fmt(code);
    $('pairNote').textContent = 'iPhoneでこのコードを入力してください。';
    setConn('wait', '接続待ち');
    if (!window.Peer) { setConn('off', '通信ライブラリを読み込めません'); return; }
    peer = new Peer(PREFIX + code.toLowerCase(), PEER_OPTS);
    peer.on('error', (e) => {
      if (e && e.type === 'unavailable-id') { host(true); return; }
      setConn('off', '接続サーバーに届きません'); Green.setReady('off');
    });
    peer.on('disconnected', () => { if (!conn || !conn.open) setConn('off', '接続サーバーから切れました'); try { peer.reconnect(); } catch (e) {} });
    peer.on('connection', (c) => {
      if (conn && conn.open) { c.on('open', () => c.close()); return; } // 2台目は受け付けない
      conn = c;
      c.on('open', () => {
        setConn('on', 'iPhoneと接続中'); $('pairNote').textContent = 'iPhoneとつながりました。';
        toast('iPhoneとつながりました'); sendInfo();
      });
      c.on('data', (d) => { const m = safeParse(d); if (m) Green.onMessage(m); });
      c.on('close', () => { if (conn === c) { conn = null; setConn('wait', '接続待ち'); Green.setReady('off'); $('pairNote').textContent = 'iPhoneとの接続が切れました。もう一度コードを入力してください。'; } });
    });
  }
  $('newCode').onclick = () => host(true);
  function sendInfo() { if (conn && conn.open && role === 'green') conn.send(Object.assign({ type: 'info' }, Green.info())); }

  /* iPhone side */
  function initCamera() {
    const saved = store.get('code', '');
    if (saved) $('codeIn').value = fmt(saved);
  }
  function connect() {
    const c = norm($('codeIn').value);
    if (c.length !== 8) { toast('コードは8文字です'); return; }
    store.set('code', c);
    if (!window.Peer) { setConn('off', '通信ライブラリを読み込めません'); return; }
    if (peer) { try { peer.destroy(); } catch (e) {} }
    setConn('wait', '接続中…');
    peer = new Peer(PREFIX + 'cam-' + randCode(12).toLowerCase(), PEER_OPTS);
    peer.on('error', (e) => { setConn('off', e && e.type === 'peer-unavailable' ? 'コードが違うか、iPadが待機していません' : '接続できませんでした'); });
    peer.on('open', () => {
      conn = peer.connect(PREFIX + c.toLowerCase(), { reliable: true, serialization: 'json' });
      conn.on('open', () => { setConn('on', 'iPadと接続中'); toast('iPadとつながりました'); Cam.pushStatus(true); });
      conn.on('data', (d) => { const m = safeParse(d); if (m && m.type === 'info') Cam.onInfo(m); });
      conn.on('close', () => setConn('off', 'iPadとの接続が切れました'));
    });
  }
  $('connectBtn').onclick = connect;
  $('codeIn').addEventListener('keydown', (e) => { if (e.key === 'Enter') connect(); });
  function send(msg) { if (conn && conn.open) { conn.send(msg); return true; } return false; }
  return { host, initCamera, send, sendInfo, connected: () => !!(conn && conn.open) };
})();

/* ======================================================================
   CAMERA (iPhone): live ball detection
   ====================================================================== */
const Cam = (() => {
  const vid = $('vid'), ov = $('overlay'), octx = ov.getContext('2d');
  const proc = document.createElement('canvas'); const pctx = proc.getContext('2d', { willReadFrequently: true });
  const PW = 320; let PH = 180;
  let stream = null, wake = null, running = false;
  let model = store.get('ballModel', null); // {nx,ny,nr,color}
  let state = 'off', lastSent = '', prev = null;
  let rest = null, stable = 0, lastPos = null, readyFrac = 0, low = 0;
  let pts = [], trackStart = 0, lost = 0, cooldownUntil = 0, lastTrack = null, needTap = false;
  const ftimes = [];
  const S = { diam: store.get('diam', 42.7), rad: 1, factor: store.get('factor', 1), angOff: store.get('angOff', 0), spin: store.get('spin', 1), sens: store.get('sens', 1) };
  [['sDiam','oDiam','diam',v=>v.toFixed(1)+' mm'],['sRad','oRad','rad',v=>'×'+v.toFixed(2)],['sFactor','oFactor','factor',v=>'×'+v.toFixed(2)],
   ['sAngOff','oAngOff','angOff',v=>(v>0?'+':'')+v.toFixed(1)+'°'],['sSpin','oSpin','spin',v=>'×'+v.toFixed(2)],['sSens','oSens','sens',v=>'×'+v.toFixed(2)]]
  .forEach(([s,o,k,f]) => { const el=$(s); el.value=S[k]; $(o).textContent=f(+el.value); el.oninput=()=>{ S[k]=+el.value; $(o).textContent=f(+el.value); if(k!=='rad') store.set(k,+el.value); }; });

  const STATE_TEXT = { off: 'カメラを開始してください', tap: '映像のボールをタップして登録', wait: 'ボールを置いてください', ready: '打ってOK', track: '計測中…', error: '' };
  function setState(s, text) {
    state = s;
    $('stateBar').dataset.state = s;
    $('stateText').textContent = text || STATE_TEXT[s] || '';
    pushStatus();
  }
  function pushStatus(force) {
    const st = state === 'tap' ? 'wait' : state === 'error' ? 'wait' : state;
    if (!force && st === lastSent) return;
    lastSent = st; Net.send({ type: 'status', state: st });
  }
  function onInfo(m) {
    const next = typeof m.next === 'string' ? m.next.slice(0, 16) : '';
    if (next && state === 'ready') $('stateText').textContent = `打ってOK(${next})`;
  }

  async function start() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { toast('このブラウザではカメラを使えません(SafariでHTTPSのページを開いてください)'); return; }
    try {
      stream = await navigator.mediaDevices.getUserMedia({ audio: false, video: { facingMode: { ideal: 'environment' }, width: { ideal: 1280 }, height: { ideal: 720 }, frameRate: { ideal: 60, max: 60 } } });
    } catch (e) { setState('error', 'カメラの使用が許可されませんでした。設定 → Safari → カメラ を確認してください'); return; }
    vid.srcObject = stream;
    try { await vid.play(); } catch (e) {}
    await new Promise(r => { if (vid.videoWidth) r(); else vid.onloadedmetadata = () => r(); });
    PH = Math.round(PW * vid.videoHeight / vid.videoWidth); proc.width = PW; proc.height = PH;
    $('stage').style.aspectRatio = vid.videoWidth + ' / ' + vid.videoHeight;
    $('stageEmpty').hidden = true; $('camStart').disabled = true; $('camStop').disabled = false;
    try { if ('wakeLock' in navigator) wake = await navigator.wakeLock.request('screen'); } catch (e) { wake = null; }
    running = true; prev = null; resetToWait();
    if (!model) { needTap = true; setState('tap'); }
    loop();
  }
  function stop(msg) {
    running = false;
    if (stream) { stream.getTracks().forEach(t => t.stop()); stream = null; }
    vid.srcObject = null;
    try { if (wake) wake.release(); } catch (e) {} wake = null;
    $('stageEmpty').hidden = false; $('camStart').disabled = false; $('camStop').disabled = true;
    octx.clearRect(0, 0, ov.width, ov.height);
    setState('off', msg);
  }
  $('camStart').onclick = start;
  $('camStop').onclick = () => stop();
  // 画面を離れたらカメラを必ず止める
  document.addEventListener('visibilitychange', () => { if (document.hidden && running) stop('画面を離れたのでカメラを止めました。「カメラを開始」で再開します'); });
  window.addEventListener('pagehide', () => { if (running) stop(); });

  function grab() { pctx.drawImage(vid, 0, 0, PW, PH); return pctx.getImageData(0, 0, PW, PH).data; }
  const cdist = (d, i, c) => Math.abs(d[i] - c[0]) + Math.abs(d[i + 1] - c[1]) + Math.abs(d[i + 2] - c[2]);

  function measureBallAt(d, px, py) {
    px = Math.round(px); py = Math.round(py);
    let c = [0, 0, 0], n = 0;
    for (let y = py - 1; y <= py + 1; y++) for (let x = px - 1; x <= px + 1; x++) { if (x < 0 || y < 0 || x >= PW || y >= PH) continue; const i = (y * PW + x) * 4; c[0] += d[i]; c[1] += d[i + 1]; c[2] += d[i + 2]; n++; }
    c = c.map(v => v / Math.max(1, n));
    const seen = new Uint8Array(PW * PH), q = [py * PW + px]; seen[q[0]] = 1; let area = 0;
    while (q.length && area < 4000) {
      const k = q.pop(); const x = k % PW, y = (k / PW) | 0; area++;
      for (const [dx, dy] of [[1,0],[-1,0],[0,1],[0,-1]]) {
        const nx = x + dx, ny = y + dy; if (nx < 0 || ny < 0 || nx >= PW || ny >= PH || Math.hypot(nx - px, ny - py) > 40) continue;
        const kk = ny * PW + nx; if (seen[kk]) continue; seen[kk] = 1; if (cdist(d, kk * 4, c) < 70) q.push(kk);
      }
    }
    return { color: c, r: clamp(Math.sqrt(area / Math.PI), 2, 30) };
  }
  function videoBox() {
    const W = ov.width, H = ov.height, va = (vid.videoWidth || 16) / (vid.videoHeight || 9), ca = W / H;
    if (va > ca) { const h = W / va; return { x: 0, y: (H - h) / 2, w: W, h }; }
    const w = H * va; return { x: (W - w) / 2, y: 0, w, h: H };
  }
  ov.addEventListener('click', (e) => {
    if (!running || !vid.videoWidth) return;
    if (!needTap) return;
    const rect = ov.getBoundingClientRect(), b = videoBox();
    const nx = ((e.clientX - rect.left) * devicePixelRatio - b.x) / b.w, ny = ((e.clientY - rect.top) * devicePixelRatio - b.y) / b.h;
    if (nx < 0 || nx > 1 || ny < 0 || ny > 1) return;
    const m = measureBallAt(grab(), nx * PW, ny * PH);
    model = { nx, ny, nr: m.r / PW, color: m.color }; store.set('ballModel', model);
    needTap = false; resetToWait(); toast('ボールを登録しました');
  });
  $('retap').onclick = () => { model = null; store.set('ballModel', null); needTap = true; if (running) setState('tap'); else toast('カメラを開始してからボールをタップしてください'); };

  function resetToWait() { rest = null; stable = 0; lastPos = null; low = 0; pts = []; lost = 0; if (running && model) setState('wait'); }

  function params() {
    const br = Math.max(2, model.nr * PW * S.rad);
    return { br, area: Math.PI * br * br, CT: 75 * S.sens, DT: 28 / S.sens, zx: model.nx * PW, zy: model.ny * PH, zR: Math.max(8 * br, 36) };
  }
  // 登録位置のまわりで、ボールの色の塊を探す
  function findBall(d, P) {
    const x0 = Math.max(0, Math.floor(P.zx - P.zR)), x1 = Math.min(PW - 1, Math.ceil(P.zx + P.zR));
    const y0 = Math.max(0, Math.floor(P.zy - P.zR)), y1 = Math.min(PH - 1, Math.ceil(P.zy + P.zR));
    const vis = new Uint8Array(PW * PH); let best = null;
    for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) {
      const k = y * PW + x; if (vis[k]) continue; vis[k] = 1;
      if (cdist(d, k * 4, model.color) >= P.CT) continue;
      const q = [k]; let n = 0, sx = 0, sy = 0, mnx = x, mxx = x, mny = y, mxy = y;
      while (q.length) {
        const kk = q.pop(); const xx = kk % PW, yy = (kk / PW) | 0; n++; sx += xx; sy += yy;
        if (xx < mnx) mnx = xx; if (xx > mxx) mxx = xx; if (yy < mny) mny = yy; if (yy > mxy) mxy = yy;
        for (const o of [1, -1, PW, -PW]) { const nk = kk + o; if (nk < 0 || nk >= vis.length || vis[nk]) continue; const nx = nk % PW, ny = (nk / PW) | 0; if (nx < x0 || nx > x1 || ny < y0 || ny > y1) continue; vis[nk] = 1; if (cdist(d, nk * 4, model.color) < P.CT) q.push(nk); }
      }
      if (n < P.area * 0.35 || n > P.area * 2.8) continue;
      const bw = mxx - mnx + 1, bh = mxy - mny + 1; if (bw / bh > 2 || bh / bw > 2) continue;
      const cx = sx / n, cy = sy / n, dist = Math.hypot(cx - P.zx, cy - P.zy);
      if (!best || dist < best.dist) best = { x: cx, y: cy, n, dist };
    }
    return best;
  }
  function fracAt(d, P, x, y) {
    let hit = 0, n = 0; const R = Math.max(1.5, P.br * 0.8);
    for (let yy = Math.floor(y - R); yy <= y + R; yy++) for (let xx = Math.floor(x - R); xx <= x + R; xx++) {
      if (xx < 0 || yy < 0 || xx >= PW || yy >= PH || Math.hypot(xx - x, yy - y) > R) continue;
      n++; if (cdist(d, (yy * PW + xx) * 4, model.color) < P.CT) hit++;
    }
    return n ? hit / n : 0;
  }
  function trackStep(d, t, P) {
    let pred, wx0, wx1, wy0, wy1;
    if (!pts.length) { pred = [rest.x, rest.y]; wx0 = rest.x - 14 * P.br; wx1 = rest.x + 14 * P.br; wy0 = rest.y - 14 * P.br; wy1 = rest.y + 1.5 * P.br; }
    else {
      const L = pts[pts.length - 1]; let vx = 0, vy = 0;
      if (pts.length >= 2) { const Q = pts[pts.length - 2]; const dt = (L.t - Q.t) || 1 / 60; vx = (L.x - Q.x) / dt; vy = (L.y - Q.y) / dt; }
      const dtn = t - L.t; pred = [L.x + vx * dtn, L.y + vy * dtn];
      const rad = Math.max(6 * P.br, 1.8 * Math.hypot(vx, vy) * dtn);
      wx0 = pred[0] - rad; wx1 = pred[0] + rad; wy0 = pred[1] - rad; wy1 = Math.min(pred[1] + rad, rest.y + 1.5 * P.br);
    }
    wx0 = Math.max(0, Math.floor(wx0)); wx1 = Math.min(PW - 1, Math.ceil(wx1)); wy0 = Math.max(0, Math.floor(wy0)); wy1 = Math.min(PH - 1, Math.ceil(wy1));
    const mask = new Uint8Array(PW * PH);
    for (let y = wy0; y <= wy1; y++) for (let x = wx0; x <= wx1; x++) {
      if (!pts.length && Math.hypot(x - rest.x, y - rest.y) < P.br) continue;
      const i = (y * PW + x) * 4;
      const mv = Math.abs(d[i] - prev[i]) + Math.abs(d[i + 1] - prev[i + 1]) + Math.abs(d[i + 2] - prev[i + 2]);
      if (mv > P.DT && cdist(d, i, model.color) < P.CT * 1.25) mask[y * PW + x] = 1;
    }
    const vis = new Uint8Array(PW * PH); let best = null;
    for (let y = wy0; y <= wy1; y++) for (let x = wx0; x <= wx1; x++) {
      const k = y * PW + x; if (!mask[k] || vis[k]) continue;
      const q = [k]; vis[k] = 1; let n = 0, sx = 0, sy = 0;
      while (q.length) { const kk = q.pop(); n++; sx += kk % PW; sy += (kk / PW) | 0; for (const o of [1, -1, PW, -PW]) { const nk = kk + o; if (nk >= 0 && nk < mask.length && mask[nk] && !vis[nk]) { vis[nk] = 1; q.push(nk); } } }
      if (n < Math.max(2, P.area * 0.12) || n > P.area * 9) continue;
      const cx = sx / n, cy = sy / n, dist = Math.hypot(cx - pred[0], cy - pred[1]);
      if (!best || dist < best.dist) best = { x: cx, y: cy, dist };
    }
    if (best) { pts.push({ t, x: best.x, y: best.y }); lost = 0; }
    else if (pts.length) lost++;
    const edge = best && (best.x < 2 || best.x > PW - 3 || best.y < 2);
    return pts.length >= 10 || lost >= 4 || edge || (t - trackStart) > 0.5;
  }
  function finishTrack() {
    const P = params();
    lastTrack = pts.slice();
    if (pts.length < 3) {
      // 誤検出(クラブが重なった等)なら、ボールがまだ置いてあるか確認して待機に戻る
      setState('error', 'ボールを追えませんでした。明るさや背景を確認して、もう一度どうぞ');
      cooldownUntil = performance.now() + 1500; return;
    }
    const ppm = (2 * P.br) / (S.diam / 1000), g = 9.81 * ppm, T0 = pts[0].t;
    const fit = (xs, ys) => { const n = xs.length, mx = xs.reduce((a, b) => a + b) / n, my = ys.reduce((a, b) => a + b) / n; let a = 0, b = 0; for (let i = 0; i < n; i++) { a += (xs[i] - mx) * (ys[i] - my); b += (xs[i] - mx) ** 2; } return b ? a / b : 0; };
    const use = pts.slice(0, 8), ts = use.map(p => p.t - T0);
    const vx = fit(ts, use.map(p => p.x)), vy = fit(ts, use.map((p, i) => p.y - 0.5 * g * ts[i] * ts[i]));
    const mSpeed = Math.hypot(vx, vy) / ppm, mAngle = Math.atan2(-vy, Math.abs(vx)) * 180 / Math.PI;
    if (!(mSpeed > 0.5 && mSpeed < 60) || mAngle < -10 || mAngle > 80) {
      setState('error', `計測値が不自然でした(${mSpeed.toFixed(1)}m/s, ${mAngle.toFixed(0)}°)。ボールを登録し直してください`);
      cooldownUntil = performance.now() + 2000; return;
    }
    const speed = clamp(mSpeed * S.factor, 1, 40), angle = clamp(mAngle + S.angOff, 0, 70);
    const spin = clamp(Math.round(290 * speed * (0.75 + angle / 120) * S.spin / 50) * 50, 500, 11000);
    const shot = { type: 'shot', id: Date.now().toString(36) + Math.random().toString(36).slice(2, 6), speed: +speed.toFixed(2), angle: +angle.toFixed(1), dir: 0, spin };
    $('cSpeed').textContent = speed.toFixed(1) + ' m/s'; $('cAngle').textContent = angle.toFixed(1) + '°'; $('cSpin').textContent = spin + ' rpm';
    $('cMeta').textContent = `練習ボールの計測値 ${mSpeed.toFixed(1)} m/s・${mAngle.toFixed(1)}° / 追跡 ${pts.length} コマ`;
    $('camResult').hidden = false;
    const ok = Net.send(shot);
    setState('error', ok ? '計測しました。iPadを見てください' : '計測しました(iPadと未接続のため送れていません)');
    cooldownUntil = performance.now() + 2500;
  }

  function drawOverlay() {
    const r = ov.getBoundingClientRect(); const W = Math.round(r.width * devicePixelRatio), H = Math.round(r.height * devicePixelRatio);
    if (ov.width !== W || ov.height !== H) { ov.width = W; ov.height = H; }
    octx.clearRect(0, 0, W, H);
    const b = videoBox(), sx = b.w / PW, sy = b.h / PH, dpr = devicePixelRatio;
    if (model) {
      const P = params();
      octx.strokeStyle = 'rgba(255,255,255,.45)'; octx.setLineDash([6 * dpr, 6 * dpr]); octx.lineWidth = 2 * dpr;
      octx.beginPath(); octx.arc(b.x + P.zx * sx, b.y + P.zy * sy, P.zR * sx, 0, Math.PI * 2); octx.stroke(); octx.setLineDash([]);
      if (rest || lastPos) {
        const p = rest || lastPos;
        octx.strokeStyle = state === 'ready' ? '#3ddc84' : '#ffd24a'; octx.lineWidth = 3 * dpr;
        octx.beginPath(); octx.arc(b.x + p.x * sx, b.y + p.y * sy, P.br * sx + 5 * dpr, 0, Math.PI * 2); octx.stroke();
      }
    }
    const tr = state === 'track' ? pts : (performance.now() < cooldownUntil ? lastTrack : null);
    if (tr) { octx.fillStyle = '#ff5a3c'; tr.forEach(p => { octx.beginPath(); octx.arc(b.x + p.x * sx, b.y + p.y * sy, 5 * dpr, 0, Math.PI * 2); octx.fill(); }); }
    if (needTap) {
      octx.fillStyle = 'rgba(0,0,0,.55)'; octx.fillRect(0, H - 44 * dpr, W, 44 * dpr);
      octx.fillStyle = '#fff'; octx.font = `${15 * dpr}px sans-serif`; octx.textAlign = 'center';
      octx.fillText('止まっているボールをタップしてください', W / 2, H - 16 * dpr);
    }
  }

  function frame(t) {
    const d = grab();
    ftimes.push(t); if (ftimes.length > 30) ftimes.shift();
    if (ftimes.length > 10) $('fpsText').textContent = Math.round((ftimes.length - 1) / (ftimes[ftimes.length - 1] - ftimes[0])) + ' fps';
    if (model && !needTap) {
      const P = params();
      if (state === 'track') {
        if (trackStep(d, t, P)) finishTrack();
      } else if (performance.now() < cooldownUntil) {
        // 結果表示中
      } else if (state === 'ready') {
        const f = fracAt(d, P, rest.x, rest.y);
        if (f < readyFrac * 0.4) { low++; if (low >= 2) { setState('track'); trackStart = t; pts = []; lost = 0; } }
        else low = 0;
      } else {
        if (state !== 'wait') setState('wait');
        const b = findBall(d, P);
        if (b) {
          if (lastPos && Math.hypot(b.x - lastPos.x, b.y - lastPos.y) < 0.4 * P.br) stable++; else stable = 0;
          lastPos = b;
          if (stable >= 20) { rest = { x: b.x, y: b.y }; readyFrac = Math.max(0.2, fracAt(d, P, rest.x, rest.y)); low = 0; setState('ready'); }
        } else { stable = 0; lastPos = null; rest = null; }
      }
    }
    prev = d;
    drawOverlay();
  }
  function loop() {
    if (!running) return;
    if ('requestVideoFrameCallback' in vid) {
      const cb = (now, meta) => { if (!running) return; const ms = meta && (meta.captureTime || meta.presentationTime || now); frame(ms / 1000); vid.requestVideoFrameCallback(cb); };
      vid.requestVideoFrameCallback(cb);
    } else {
      const cb = (now) => { if (!running) return; frame(now / 1000); requestAnimationFrame(cb); };
      requestAnimationFrame(cb);
    }
  }
  // 状態がreadyのまま一定時間が過ぎたら、置き直しに備えて再確認する
  setInterval(() => { if (running && state === 'ready') pushStatus(true); }, 3000);
  return { pushStatus, onInfo };
})();

/* ======================================================================
   GREEN (iPad): 3D course + game
   ====================================================================== */
const Green = (() => {
  let inited = false, renderer, scene, cam, courseGroup, ballMesh, shadowMesh, trailGroup, markers;
  let course = null, anim = null, queue = [], viewMode = 'follow';
  const camPos = new THREE.Vector3(-4, 2, 0), camLook = new THREE.Vector3(10, 0, 0);
  const COLORS = ['#d9472f', '#2f63c8'];
  const seen = new Set();
  const game = {
    mode: store.get('mode', 'solo'), holes: 9, hole: 1, turn: 0,
    players: [{ name: store.get('p0', 'プレイヤー1'), wins: 0, sum: 0 }, { name: store.get('p1', 'プレイヤー2'), wins: 0, sum: 0 }],
    shots: [], log: []
  };
  const rand = (a, b) => a + Math.random() * (b - a);
  function newCourse() {
    const D = rand(9, 30), rx = rand(7, 10.5), rz = rand(6, 8.5);
    let cx = D + rand(-1.5, 3); if (cx - rx < 4) cx = 4 + rx;
    return { pin: { x: D, z: rand(-1.8, 1.8) }, green: { cx, cz: rand(-1, 1), rx, rz }, stimp: Math.round(rand(8.5, 11.5) * 2) / 2, slope: { x: rand(-0.022, 0.008), z: rand(-0.015, 0.015) } };
  }
  function texCanvas(w, h, draw) { const c = document.createElement('canvas'); c.width = w; c.height = h; draw(c.getContext('2d'), w, h); const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; return t; }
  function noise(ctx, w, h, base, amp, n) { ctx.fillStyle = base; ctx.fillRect(0, 0, w, h); for (let i = 0; i < n; i++) { const a = Math.random() * amp; ctx.fillStyle = Math.random() < .5 ? `rgba(0,0,0,${a})` : `rgba(255,255,255,${a * .6})`; ctx.fillRect(Math.random() * w, Math.random() * h, 2, 2); } }

  function init() {
    if (inited) { resize(); return; }
    inited = true;
    if (!window.THREE) { toast('3D表示ライブラリを読み込めませんでした'); return; }
    const world = $('world');
    renderer = new THREE.WebGLRenderer({ antialias: true });
    renderer.setPixelRatio(Math.min(2, devicePixelRatio)); renderer.shadowMap.enabled = true;
    world.prepend(renderer.domElement);
    scene = new THREE.Scene(); scene.background = new THREE.Color('#bcdbe8'); scene.fog = new THREE.Fog('#bcdbe8', 45, 110);
    cam = new THREE.PerspectiveCamera(50, 16 / 10, 0.05, 300);
    scene.add(new THREE.HemisphereLight('#eaf6ff', '#3d5a2c', 0.75));
    const sun = new THREE.DirectionalLight('#fff6e5', 0.8); sun.position.set(-10, 25, 12); sun.castShadow = true;
    sun.shadow.mapSize.set(1024, 1024); Object.assign(sun.shadow.camera, { left: -30, right: 30, top: 30, bottom: -30, far: 80 });
    sun.target.position.set(15, 0, 0); scene.add(sun, sun.target);
    const roughTex = texCanvas(256, 256, (c, w, h) => noise(c, w, h, '#3f7a34', .18, 5000)); roughTex.repeat.set(40, 40);
    const rough = new THREE.Mesh(new THREE.PlaneGeometry(240, 240), new THREE.MeshLambertMaterial({ map: roughTex }));
    rough.rotation.x = -Math.PI / 2; rough.position.x = 40; rough.receiveShadow = true; scene.add(rough);
    const treeMat = new THREE.MeshLambertMaterial({ color: '#2b5a2a' });
    for (let i = 0; i < 70; i++) { const a = Math.random() * Math.PI * 2, r = rand(55, 80); const t = new THREE.Mesh(new THREE.ConeGeometry(rand(2, 3.5), rand(6, 11), 7), treeMat); t.position.set(20 + Math.cos(a) * r, 4, Math.sin(a) * r); scene.add(t); }
    const mat = new THREE.Mesh(new THREE.BoxGeometry(1.5, 0.02, 1.5), new THREE.MeshLambertMaterial({ color: '#1f4d2b' })); mat.position.set(0, 0.01, 0); mat.receiveShadow = true; scene.add(mat);
    ballMesh = new THREE.Mesh(new THREE.SphereGeometry(0.047, 20, 14), new THREE.MeshLambertMaterial({ color: '#ffffff' })); ballMesh.castShadow = true; scene.add(ballMesh);
    shadowMesh = new THREE.Mesh(new THREE.CircleGeometry(0.05, 16), new THREE.MeshBasicMaterial({ color: '#000', transparent: true, opacity: .25 })); shadowMesh.rotation.x = -Math.PI / 2; scene.add(shadowMesh);
    trailGroup = new THREE.Group(); scene.add(trailGroup); markers = new THREE.Group(); scene.add(markers);
    new ResizeObserver(resize).observe(world); resize();
    buildHole(newCourse()); renderPanel(); requestAnimationFrame(loop);
  }
  function resize() { if (!renderer) return; const w = $('world').clientWidth, h = $('world').clientHeight; if (!w || !h) return; renderer.setSize(w, h, false); cam.aspect = w / h; cam.updateProjectionMatrix(); }

  function buildHole(c) {
    course = c;
    if (courseGroup) scene.remove(courseGroup);
    courseGroup = new THREE.Group();
    const g = c.green;
    const fringeTex = texCanvas(128, 128, (x, w, h) => noise(x, w, h, '#4f9a45', .12, 1500)); fringeTex.repeat.set(6, 6);
    const fr = new THREE.Mesh(new THREE.CircleGeometry(1, 64), new THREE.MeshLambertMaterial({ map: fringeTex }));
    fr.scale.set(g.rx + 1.2, g.rz + 1.2, 1); fr.rotation.x = -Math.PI / 2; fr.position.set(g.cx, 0.004, g.cz); fr.receiveShadow = true;
    const stripe = texCanvas(256, 256, (x, w, h) => { for (let i = 0; i < 8; i++) { x.fillStyle = i % 2 ? '#5fb24f' : '#56a847'; x.fillRect(i * w / 8, 0, w / 8, h); } for (let i = 0; i < 2500; i++) { x.fillStyle = `rgba(0,0,0,${Math.random() * .06})`; x.fillRect(Math.random() * w, Math.random() * h, 1, 1); } });
    const gr = new THREE.Mesh(new THREE.CircleGeometry(1, 72), new THREE.MeshLambertMaterial({ map: stripe }));
    gr.scale.set(g.rx, g.rz, 1); gr.rotation.x = -Math.PI / 2; gr.position.set(g.cx, 0.008, g.cz); gr.receiveShadow = true;
    const cup = new THREE.Mesh(new THREE.CircleGeometry(0.054, 24), new THREE.MeshBasicMaterial({ color: '#101010' })); cup.rotation.x = -Math.PI / 2; cup.position.set(c.pin.x, 0.012, c.pin.z);
    const pole = new THREE.Mesh(new THREE.CylinderGeometry(0.012, 0.012, 2.1, 8), new THREE.MeshLambertMaterial({ color: '#f4f4f4' })); pole.position.set(c.pin.x, 1.05, c.pin.z); pole.castShadow = true;
    const flag = new THREE.Mesh(new THREE.PlaneGeometry(0.5, 0.32), new THREE.MeshLambertMaterial({ color: '#e0412a', side: THREE.DoubleSide })); flag.position.set(c.pin.x, 1.9, c.pin.z + 0.25); flag.rotation.y = Math.PI / 2; flag.castShadow = true;
    courseGroup.add(fr, gr, cup, pole, flag); scene.add(courseGroup);
    clearTrails(); placeBall(0, 0, 0); viewIdle();
    $('hHole').textContent = game.mode === 'duo' ? `ホール ${game.hole}/${game.holes}` : `ホール ${game.hole}`;
    $('hDist').textContent = `ピンまで ${Math.round(yd(Math.hypot(c.pin.x, c.pin.z)))} ヤード`;
    const sx = c.slope.x, sz = c.slope.z;
    const fb = Math.abs(sx) < 0.004 ? '平ら' : sx < 0 ? `受け ${(-sx * 100).toFixed(1)}%` : `奥に下り ${(sx * 100).toFixed(1)}%`;
    const lr = Math.abs(sz) < 0.004 ? '' : sz > 0 ? `・左→右 ${(sz * 100).toFixed(1)}%` : `・右→左 ${(-sz * 100).toFixed(1)}%`;
    $('hGreen').textContent = `速さ ${c.stimp}ft・${fb}${lr}`;
    $('banner').hidden = true;
  }
  function placeBall(x, y, z) { ballMesh.position.set(x, y + 0.047, z); shadowMesh.position.set(x, 0.015, z); }
  function clearTrails() { while (trailGroup.children.length) { const o = trailGroup.children.pop(); o.geometry.dispose(); } while (markers.children.length) markers.children.pop(); }
  function viewIdle() {
    const p = course.pin;
    if (viewMode === 'top') { camPos.set(p.x * 0.55, Math.max(14, p.x * 1.15), p.z * 0.5 + 0.01); camLook.set(p.x * 0.55, 0, p.z * 0.5); }
    else { camPos.set(-3.2, 1.9, 0); camLook.set(p.x * 0.8, 0, p.z * 0.8); }
  }
  function setView(v) { viewMode = v; $('vFollow').setAttribute('aria-pressed', v === 'follow'); $('vTop').setAttribute('aria-pressed', v === 'top'); if (!anim) viewIdle(); }
  $('vFollow').onclick = () => setView('follow'); $('vTop').onclick = () => setView('top');
  function makeTrail(color) { const geo = new THREE.BufferGeometry(); geo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(3 * 4000), 3)); geo.setDrawRange(0, 0); const line = new THREE.Line(geo, new THREE.LineBasicMaterial({ color })); trailGroup.add(line); return line; }
  function addMarker(x, z, color) {
    const m = new THREE.Mesh(new THREE.SphereGeometry(0.06, 16, 10), new THREE.MeshLambertMaterial({ color })); m.position.set(x, 0.06, z); markers.add(m);
    const ring = new THREE.Mesh(new THREE.RingGeometry(0.12, 0.16, 24), new THREE.MeshBasicMaterial({ color, side: THREE.DoubleSide })); ring.rotation.x = -Math.PI / 2; ring.position.set(x, 0.015, z); markers.add(ring);
  }

  // iPhoneから届くデータは信用せず、形と範囲を検査する
  function num(v, a, b) { v = Number(v); return Number.isFinite(v) ? clamp(v, a, b) : null; }
  function onMessage(m) {
    if (m.type === 'status') { if (['wait', 'ready', 'track', 'off'].includes(m.state)) setReady(m.state); return; }
    if (m.type === 'shot') {
      const s = { id: String(m.id || '').slice(0, 32), speed: num(m.speed, 1, 40), angle: num(m.angle, 0, 70), dir: num(m.dir, -30, 30) ?? 0, spin: num(m.spin, 0, 12000) };
      if (!s.id || s.speed == null || s.angle == null || s.spin == null) return;
      receive(s);
    }
  }
  const READY_TEXT = { off: 'カメラ待ち', wait: 'ボールを置いてください', ready: '打ってOK', track: '計測中…' };
  function setReady(s) { const el = $('readyMark'); el.dataset.state = s; $('readyText').textContent = READY_TEXT[s] || ''; }

  function receive(shot) {
    if (!inited) init();
    if (seen.has(shot.id)) return; seen.add(shot.id);
    if (game.mode === 'duo' && game.shots.length >= 2) { toast('このホールは終了しました。「次のホール」を押してください'); return; }
    if (anim) { queue.push(shot); return; }
    play(shot);
  }
  function play(shot) {
    const res = SIM.simulate(shot, course);
    let apex = 0; for (const p of res.pts) if (p[2] > apex) apex = p[2];
    res.apex = apex;
    const player = game.mode === 'duo' ? game.turn : 0;
    if (game.mode === 'solo') while (trailGroup.children.length >= 6) { const o = trailGroup.children.shift(); trailGroup.remove(o); o.geometry.dispose(); }
    const color = game.mode === 'duo' ? COLORS[player] : '#ffffff';
    anim = { shot, res, player, line: makeTrail(color), start: performance.now(), color };
    $('banner').hidden = true;
    $('gSpeed').textContent = shot.speed.toFixed(1) + ' m/s'; $('gAngle').textContent = shot.angle.toFixed(1) + '°'; $('gSpin').textContent = Math.round(shot.spin) + ' rpm';
    $('gCarry').textContent = '…'; $('gTotal').textContent = '…'; $('gPin').textContent = '…';
  }
  const fmtDist = (m) => m < 1 ? `${Math.round(m * 100)}cm` : `${m.toFixed(2)}m`;
  function showBanner(t, ms) { const b = $('banner'); b.textContent = t; b.hidden = false; clearTimeout(showBanner._t); if (ms) showBanner._t = setTimeout(() => { b.hidden = true; }, ms); }
  function finishShot() {
    const { shot, res, player, color } = anim; anim = null;
    addMarker(res.end.x, res.end.z, color);
    $('gCarry').textContent = yd(res.carry.x).toFixed(1) + ' yd'; $('gTotal').textContent = yd(res.total).toFixed(1) + ' yd';
    $('gPin').textContent = res.holed ? 'カップイン' : fmtDist(res.toPin);
    game.shots.push({ player, res, shot });
    if (res.holed) showBanner('チップイン!', 3000);
    if (game.mode === 'duo') {
      game.turn = 1 - game.turn;
      if (game.shots.length >= 2) {
        const [a, b] = game.shots; const d0 = a.player === 0 ? a.res.toPin : b.res.toPin, d1 = a.player === 0 ? b.res.toPin : a.res.toPin;
        const w = d0 < d1 ? 0 : d1 < d0 ? 1 : -1;
        if (w >= 0) game.players[w].wins++;
        game.players[0].sum += d0; game.players[1].sum += d1;
        game.log.push({ hole: game.hole, d: [d0, d1], w });
        showBanner(w < 0 ? `ホール${game.hole} 引き分け` : `ホール${game.hole} ${game.players[w].name} の勝ち`);
        game.turn = game.hole % 2;
        if (game.hole >= game.holes) setTimeout(() => showBanner(finalText()), 2200);
      } else showBanner(`次は ${game.players[game.turn].name}`, 2500);
    } else game.log.push({ hole: game.hole, n: game.shots.length, d: res.toPin, carry: res.carry.x, total: res.total });
    renderPanel(); Net.sendInfo();
    if (viewMode === 'follow') { const e = res.end; camLook.set((e.x + course.pin.x) / 2, 0, (e.z + course.pin.z) / 2); }
    if (queue.length) setTimeout(() => { const s = queue.shift(); if (s && !(game.mode === 'duo' && game.shots.length >= 2)) play(s); }, 1200);
  }
  function finalText() {
    const [p, q] = game.players;
    if (p.wins === q.wins) return p.sum === q.sum ? '最終結果 引き分け' : `最終結果 ${p.sum < q.sum ? p.name : q.name} の勝ち(距離差)`;
    return `最終結果 ${p.wins > q.wins ? p.name : q.name} の勝ち`;
  }
  function loop(now) {
    requestAnimationFrame(loop);
    if (!renderer || $('greenView').hidden) return;
    if (anim) {
      const t = (now - anim.start) / 1000, pts = anim.res.pts; let i = 0;
      while (i < pts.length - 1 && pts[i + 1][0] < t) i++;
      const a = pts[i], b = pts[Math.min(i + 1, pts.length - 1)];
      const f = b[0] > a[0] ? clamp((t - a[0]) / (b[0] - a[0]), 0, 1) : 1;
      const x = a[1] + (b[1] - a[1]) * f, y = a[2] + (b[2] - a[2]) * f, z = a[3] + (b[3] - a[3]) * f;
      placeBall(x, y, z);
      const arr = anim.line.geometry.attributes.position.array, n = Math.min(i + 1, 3999);
      for (let k = 0; k < n; k++) { arr[k * 3] = pts[k][1]; arr[k * 3 + 1] = pts[k][2] + 0.03; arr[k * 3 + 2] = pts[k][3]; }
      arr[n * 3] = x; arr[n * 3 + 1] = y + 0.03; arr[n * 3 + 2] = z;
      anim.line.geometry.setDrawRange(0, n + 1); anim.line.geometry.attributes.position.needsUpdate = true;
      if (viewMode === 'follow') { camPos.set(Math.max(-3.2, x - 5.5), Math.max(1.6, y + 1.8), z * 0.8); camLook.set(x + 2, y * 0.6, z); }
      if (t >= anim.res.duration + 0.05) finishShot();
    } else if (viewMode === 'top') viewIdle();
    cam.position.lerp(camPos, 0.06);
    const cur = cam.userData.look || camLook.clone(); cur.lerp(camLook, 0.08); cam.userData.look = cur; cam.lookAt(cur);
    renderer.render(scene, cam);
  }

  function el(tag, cls, text) { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; }
  function renderPanel() {
    $('mDuo').setAttribute('aria-pressed', game.mode === 'duo'); $('mSolo').setAttribute('aria-pressed', game.mode === 'solo');
    const pw = $('players'); pw.textContent = ''; pw.hidden = game.mode !== 'duo';
    game.players.forEach((p, i) => {
      const isTurn = game.turn === i && game.shots.length < 2;
      const d = el('div', 'pcard c' + (i + 1) + (isTurn ? ' turn' : ''));
      d.append(el('div', 'tag', isTurn ? '打つ番' : ''));
      const nm = el('div', 'nm'); nm.append(el('span', 'sw'));
      const inp = el('input'); inp.id = 'pname' + i; inp.maxLength = 12; inp.value = p.name; inp.setAttribute('aria-label', `プレイヤー${i + 1}の名前`);
      inp.oninput = () => { p.name = inp.value || `プレイヤー${i + 1}`; store.set('p' + i, p.name); Net.sendInfo(); };
      nm.append(inp); d.append(nm);
      const s1 = el('div', 'stat'); s1.append(el('span', null, '勝ちホール'), el('b', null, String(p.wins)));
      const s2 = el('div', 'stat'); s2.append(el('span', null, 'ピンまで累計'), el('b', null, p.sum ? p.sum.toFixed(1) + 'm' : '–'));
      d.append(s1, s2); pw.append(d);
    });
    const th = $('logTable').tHead, tb = $('logTable').tBodies[0]; th.textContent = ''; tb.textContent = '';
    const heads = game.mode === 'duo' ? ['ホール', game.players[0].name, game.players[1].name] : ['#', 'キャリー', '合計', 'ピンまで'];
    const hr = el('tr'); heads.forEach((h, i) => hr.append(el('th', i ? 'n' : null, h))); th.append(hr);
    const rows = game.log.slice().reverse();
    if (!rows.length) { const r = el('tr'); const c = el('td', 'empty', 'まだ打球がありません。iPhoneから打つか、試し打ちをどうぞ。'); c.colSpan = heads.length; r.append(c); tb.append(r); }
    rows.forEach(l => {
      const r = el('tr');
      const cells = game.mode === 'duo' ? [l.hole, fmtDist(l.d[0]) + (l.w === 0 ? ' ●' : ''), fmtDist(l.d[1]) + (l.w === 1 ? ' ●' : '')]
        : [`${l.hole}-${l.n}`, yd(l.carry).toFixed(1) + 'yd', yd(l.total).toFixed(1) + 'yd', l.d === 0 ? 'IN' : fmtDist(l.d)];
      cells.forEach((v, i) => r.append(el('td', i ? 'n' : null, String(v)))); tb.append(r);
    });
    $('logTitle').textContent = game.mode === 'duo' ? 'ホールごとの結果(●が勝ち)' : '打球の記録';
    $('nextHole').disabled = game.mode === 'duo' && game.hole >= game.holes && game.shots.length >= 2;
  }
  function reset() { game.hole = 1; game.turn = 0; game.shots = []; game.log = []; game.players.forEach(p => { p.wins = 0; p.sum = 0; }); anim = null; queue = []; buildHole(newCourse()); renderPanel(); Net.sendInfo(); }
  $('mDuo').onclick = () => { game.mode = 'duo'; store.set('mode', 'duo'); reset(); };
  $('mSolo').onclick = () => { game.mode = 'solo'; store.set('mode', 'solo'); reset(); };
  $('resetGame').onclick = reset;
  $('nextHole').onclick = () => {
    if (game.mode === 'duo' && game.shots.length === 1) { toast('もう1人が打ってから次のホールへ進めます'); return; }
    if (game.mode === 'duo' && game.hole >= game.holes) return;
    game.hole++; game.shots = []; anim = null; queue = []; buildHole(newCourse()); renderPanel(); Net.sendInfo();
  };
  const tfmt = { tSpeed: v => v + ' m/s', tAngle: v => v + '°', tDir: v => (v > 0 ? '+' : '') + v + '°', tSpin: v => v + ' rpm' };
  Object.keys(tfmt).forEach(k => { const e = $(k), o = $('o' + k); const u = () => { o.textContent = tfmt[k](+e.value); }; e.oninput = u; u(); });
  $('testShot').onclick = () => receive({ id: 't' + Date.now(), speed: +$('tSpeed').value, angle: +$('tAngle').value, dir: +$('tDir').value, spin: +$('tSpin').value });
  function info() { return { mode: game.mode, hole: game.hole, next: game.mode === 'duo' && game.shots.length < 2 ? game.players[game.turn].name : '' }; }
  return { init, onMessage, setReady, info };
})();

if (role === 'camera' || role === 'green') showRole(role);
})();
