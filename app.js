'use strict';
/* おうちアプローチ — 56度で寄せる、自宅のアプローチ場
   セキュリティ方針:
   - カメラ映像はiPhoneの中だけで処理し、保存も送信もしない
   - 端末間で送るのは数値と状態だけ(WebRTCで暗号化された直接通信。データを中継するサーバーは使わない)
   - 受け取ったデータは種類・数値範囲・大きさを検査してから使い、画面にはテキストとしてのみ表示する */
(() => {
// ===== ball physics (real golf ball equivalent, 56° wedge) =====
const SIM = (() => {
  const G = 9.81, RHO = 1.2, R = 0.02135, M = 0.04593, A = Math.PI * R * R;
  const CUP_R = 0.054;
  const SURF = {
    green:   { e: 0.42, mu: 0.40, muk: 0.35, dig: 0.055 },
    fringe:  { e: 0.32, mu: 0.52, muk: 0.48, dig: 0.08, decel: 1.6 },
    fairway: { e: 0.30, mu: 0.55, muk: 0.50, dig: 0.085, decel: 1.9 },
    rough:   { e: 0.16, mu: 0.70, muk: 0.72, dig: 0.13, decel: 4.2 }
  };
  const inEll = (s, x, z, grow) => { const dx = (x - s.cx) / (s.rx + (grow || 0)), dz = (z - s.cz) / (s.rz + (grow || 0)); return dx * dx + dz * dz <= 1; };
  const inRect = (s, x, z) => x >= s.x0 && x <= s.x1 && z >= s.z0 && z <= s.z1;
  function inPoly(p, x, z) { let c = false; for (let i = 0, j = p.length - 1; i < p.length; j = i++) { const [xi, zi] = p[i], [xj, zj] = p[j]; if (((zi > z) !== (zj > z)) && (x < (xj - xi) * (z - zi) / (zj - zi) + xi)) c = !c; } return c; }
  function inShape(s, x, z, grow) { return s.kind === 'ellipse' ? inEll(s, x, z, grow) : s.kind === 'rect' ? inRect(s, x, z) : inPoly(s.pts, x, z); }
  function zoneAt(c, x, z) {
    if (c.allGreen) return 'green';
    for (const s of c.shapes) if (s.type === 'green' && inShape(s, x, z)) return 'green';
    for (const s of c.shapes) if (s.top && inShape(s, x, z)) return s.type;
    for (const s of c.shapes) if ((s.type === 'chasm' || s.type === 'water') && inShape(s, x, z)) return s.type;
    for (const s of c.shapes) if (s.type === 'green' && inShape(s, x, z, 1.2)) return 'fringe';
    for (const s of c.shapes) if (s.type === 'fairway' && inShape(s, x, z)) return 'fairway';
    return 'rough';
  }
  const isHaz = (z) => z === 'water' || z === 'chasm';
  function rollDecel(c, zone) { return zone === 'green' ? 5.49 / c.stimp : SURF[zone].decel; }
  // shot: {speed m/s, angle deg, dir deg(+右), spin rpm}; start {x,z}; heading rad (0 = +x)
  function simulate(shot, c, start, heading) {
    const dt = 1 / 240;
    const th = shot.angle * Math.PI / 180, ph = heading + shot.dir * Math.PI / 180;
    const hx0 = Math.cos(ph), hz0 = Math.sin(ph);
    let p = [start.x, 0, start.z];
    let v = [shot.speed * Math.cos(th) * hx0, shot.speed * Math.sin(th), shot.speed * Math.cos(th) * hz0];
    let w = shot.spin * 2 * Math.PI / 60;
    const pts = [[0, p[0], p[1], p[2]]];
    let t = 0, phase = 'air', carry = null, holed = false, hazard = null;
    const cup = c.pin;
    for (let i = 0; i < 240 * 30; i++) {
      t += dt;
      if (phase === 'air') {
        const sp = Math.hypot(v[0], v[1], v[2]);
        const S = sp > 0.1 ? R * Math.abs(w) / sp : 0;
        const Cl = Math.sign(w) * (S < 0.3 ? 1.99 * S - 3.25 * S * S : 0.305);
        const k = 0.5 * RHO * A / M * sp, Cd = 0.3;
        const hs = Math.hypot(v[0], v[2]) || 1e-6, hx = v[0] / hs, hz = v[2] / hs;
        const lx = -v[1] * hx / sp, ly = hs / sp, lz = -v[1] * hz / sp;
        v[0] += (-k * Cd * v[0] + k * sp * Cl * lx) * dt;
        v[1] += (-G - k * Cd * v[1] + k * sp * Cl * ly) * dt;
        v[2] += (-k * Cd * v[2] + k * sp * Cl * lz) * dt;
        w *= Math.exp(-dt / 25);
        p[0] += v[0] * dt; p[1] += v[1] * dt; p[2] += v[2] * dt;
        if (p[1] <= 0) {
          p[1] = 0;
          if (carry === null) carry = { x: p[0], z: p[2] };
          const zone = zoneAt(c, p[0], p[2]);
          if (isHaz(zone)) { hazard = zone; pts.push([t, p[0], zone === 'chasm' ? -2.5 : -0.05, p[2]]); break; }
          const s = SURF[zone], vy = Math.abs(v[1]);
          const e = Math.max(0.08, s.e - 0.045 * vy);
          const hs2 = Math.hypot(v[0], v[2]);
          const ux = hs2 > 1e-6 ? v[0] / hs2 : hx0, uz = hs2 > 1e-6 ? v[2] / hs2 : hz0;
          let vt = hs2 * Math.max(0.35, 1 - s.dig * vy);
          const need = (2 / 7) * (vt + R * w), avail = s.mu * (1 + e) * vy;
          if (avail >= Math.abs(need)) { vt = (5 * vt - 2 * R * w) / 7; w = -vt / R; }
          else { const sg = Math.sign(vt + R * w); vt -= sg * avail; w -= sg * (5 / (2 * R)) * avail; }
          v = [ux * vt, e * vy, uz * vt];
          if (e * vy < 0.45) { v[1] = 0; phase = 'roll'; }
        }
      } else {
        const zone = zoneAt(c, p[0], p[2]);
        if (isHaz(zone)) { hazard = zone; pts.push([t, p[0], zone === 'chasm' ? -2.5 : -0.05, p[2]]); break; }
        const s = SURF[zone];
        const hs2 = Math.hypot(v[0], v[2]);
        const ux = hs2 > 1e-6 ? v[0] / hs2 : hx0, uz = hs2 > 1e-6 ? v[2] / hs2 : hz0;
        let vt = hs2;
        const slip = vt + R * w;
        if (Math.abs(slip) > 0.03) { const a = s.muk * G * Math.sign(slip); vt -= a * dt; w -= (5 / (2 * R)) * a * dt; }
        else { vt = Math.max(0, vt - rollDecel(c, zone) * dt); w = -vt / R; }
        v[0] = ux * vt; v[2] = uz * vt;
        const slopeOn = zone === 'green' || c.allGreen;
        if (slopeOn) { v[0] += (5 / 7) * G * c.slope.x * dt; v[2] += (5 / 7) * G * c.slope.z * dt; }
        p[0] += v[0] * dt; p[2] += v[2] * dt;
        const dc = Math.hypot(p[0] - cup.x, p[2] - cup.z), spd = Math.hypot(v[0], v[2]);
        if (dc < CUP_R && spd < 1.6) { holed = true; p[0] = cup.x; p[2] = cup.z; p[1] = -0.03; pts.push([t, p[0], p[1], p[2]]); break; }
        const slopeMag = slopeOn ? Math.hypot(c.slope.x, c.slope.z) : 0;
        if (spd < 0.02 && Math.abs(slip) < 0.03 && slopeMag < 0.035) break;
        if (spd < 0.02 && Math.abs(slip) < 0.03) v = [0, 0, 0];
      }
      if (i % 4 === 0) pts.push([t, p[0], p[1], p[2]]);
    }
    if (!hazard) pts.push([t, p[0], p[1], p[2]]);
    const end = { x: p[0], z: p[2] };
    const cr = carry || end;
    return {
      pts, end, holed, hazard, duration: t,
      carry: Math.hypot(cr.x - start.x, cr.z - start.z),
      total: Math.hypot(end.x - start.x, end.z - start.z),
      toPin: holed ? 0 : Math.hypot(end.x - cup.x, end.z - cup.z),
      zone: hazard || zoneAt(c, end.x, end.z)
    };
  }
  return { simulate, zoneAt, inShape };
})();


// ===== 6 holes (1 course = 1 hole). Units: meters. +x = toward the hole, +z = right =====
const COURSES = (() => {
  const YD = 0.9144;
  const unitYd = (limitYd) => Math.round(limitYd * 32 / 35); // 35yd limit -> 32yd
  const E = (type, cx, cz, rx, rz, extra) => Object.assign({ type, kind: 'ellipse', cx, cz, rx, rz }, extra || {});
  const Rc = (type, x0, x1, z0, z1, extra) => Object.assign({ type, kind: 'rect', x0, x1, z0, z1 }, extra || {});
  const defs = [
    { id: 'p3s', par: 2, style: 'シンプル', name: 'ファーストステップ', desc: '広いグリーンへまっすぐ寄せる、基本のパー2。',
      build: (f) => ({ pin: { x: f, z: 0.5 }, stimp: 9.5, slope: { x: -0.012, z: 0.004 }, route: [],
        shapes: [E('green', f + 1, 0.5, 7.5, 6.5), Rc('fairway', -3, f - 5, -6, 6)] }) },
    { id: 'p3t', par: 2, style: 'テクニカル', name: '浮島グリーン', desc: '池に浮かぶ小さなグリーン。届かなくても、越えすぎても池。',
      build: (f) => ({ pin: { x: f, z: -0.8 }, stimp: 11, slope: { x: 0.006, z: -0.01 }, route: [],
        shapes: [E('green', f, -0.5, 5.5, 4.8), E('water', f, -0.5, 11, 10), Rc('fairway', -3, f - 12, -6, 6)] }) },
    { id: 'p4s', par: 3, style: 'シンプル', name: 'まっすぐロード', desc: '真っすぐなフェアウェイ。刻んで確実に寄せる。',
      build: (f) => ({ pin: { x: 2 * f, z: -0.5 }, stimp: 10, slope: { x: -0.015, z: -0.006 }, route: [],
        shapes: [E('green', 2 * f + 1, 0, 8, 7), Rc('fairway', -3, 2 * f - 5, -7, 7)] }) },
    { id: 'p4t', par: 3, style: 'テクニカル', name: '崖越えショートカット', desc: '右に曲がるドッグレッグ。崖を越えれば近道、落ちたら1打罰。',
      build: (f) => ({ pin: { x: f, z: f + 0.5 }, stimp: 10.5, slope: { x: 0.008, z: -0.012 }, route: [{ x: f, z: 0 }],
        shapes: [E('green', f, f + 0.5, 7, 7), Rc('fairway', -3, f + 6, -6, 6), Rc('fairway', f - 6, f + 6, -6, f - 6),
          Rc('chasm', 0.3 * f, 0.65 * f, Math.max(6.5, 0.3 * f), 0.7 * f)] }) },
    { id: 'p5s', par: 4, style: 'シンプル', name: 'ゆったり湖畔', desc: '右手に湖が見える長いホール。3打でリズムよく。',
      build: (f) => ({ pin: { x: 3 * f, z: 0 }, stimp: 10, slope: { x: -0.01, z: 0.008 }, route: [],
        shapes: [E('green', 3 * f + 1, 0, 8, 7), Rc('fairway', -3, 3 * f - 6, -8, 8), E('water', 1.6 * f, 16, 12, 5)] }) },
    { id: 'p5t', par: 4, style: 'テクニカル', name: 'アイランドチェイン', desc: '島から島へ渡っていく。左の陸地を回れば安全だが遠回り。',
      build: (f) => ({ pin: { x: 3 * f, z: 0.4 }, stimp: 11, slope: { x: 0.004, z: 0.01 }, route: [{ x: 1.0 * f, z: 0 }, { x: 2.0 * f, z: 0.1 * f }],
        shapes: [E('green', 3 * f, 0, 6.5, 5.5),
          E('fairway', 1.0 * f, 0, 0.28 * f, 0.22 * f, { top: true }), E('fairway', 2.0 * f, 0.1 * f, 0.28 * f, 0.22 * f, { top: true }),
          Rc('water', 0.4 * f, 3 * f + 12, -0.5 * f, 0.5 * f), Rc('fairway', -3, 0.4 * f, -6, 6)] }) }
  ];
  function make(id, limitYd) {
    const d = defs.find(x => x.id === id);
    const f = unitYd(limitYd) * YD;
    const c = d.build(f);
    return Object.assign({ id: d.id, par: d.par, style: d.style, name: d.name, desc: d.desc, lengthYd: unitYd(limitYd) * (d.par - 1), tee: { x: 0, z: 0 } }, c);
  }
  function practice(yd) {
    return { id: 'practice', allGreen: true, pin: { x: yd * YD, z: 0 }, stimp: 10, slope: { x: -0.006, z: 0.003 }, shapes: [], route: [], tee: { x: 0, z: 0 } };
  }
  return { defs, make, practice, unitYd };
})();



const $ = (id) => document.getElementById(id);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const YD = 0.9144;
const yd = (m) => m / YD;
const fy = (m) => yd(m).toFixed(1);
const fDist = (m) => m < 1 ? `${Math.round(m * 100)}cm` : `${m.toFixed(1)}m`;
const store = {
  get(k, d) { try { const v = localStorage.getItem('oa_' + k); return v == null ? d : JSON.parse(v); } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem('oa_' + k, JSON.stringify(v)); } catch (e) {} }
};
function toast(t) { const el = $('toast'); el.textContent = t; el.hidden = false; clearTimeout(toast._t); toast._t = setTimeout(() => { el.hidden = true; }, 3200); }
function setConn(state, text) { $('connDot').className = 'dot ' + (state || ''); $('connText').textContent = text; }
function el(tag, cls, text) { const e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; }

/* ---------------- views & role ---------------- */
const VIEWS = ['roleView', 'camView', 'homeView', 'freeView', 'courseView', 'playView'];
function show(v) { VIEWS.forEach(id => { $(id).hidden = id !== v; }); if (v === 'playView') World.resize(); window.scrollTo(0, 0); }
let role = store.get('role', null);
const hashCode = ((location.hash || '').match(/p=([A-Za-z0-9]{8})/) || [])[1];
if (hashCode) {
  role = 'camera'; store.set('role', 'camera'); store.set('code', hashCode.toUpperCase());
  try { history.replaceState(null, '', location.pathname + location.search); } catch (e) {} // コードをアドレスバーに残さない
}
function startRole(r) {
  role = r; store.set('role', r); $('switchRole').hidden = false;
  if (r === 'camera') { show('camView'); Net.initCamera(); }
  else { show('homeView'); App.initHome(); Net.host(); Power.keepAwake(); }
}
$('pickCam').onclick = () => startRole('camera');
$('pickGreen').onclick = () => startRole('green');
$('switchRole').onclick = () => { store.set('role', null); location.reload(); };

/* ---------------- screen wake lock (iPad) ---------------- */
const Power = (() => {
  let lock = null, want = false;
  async function keepAwake() { want = true; try { if ('wakeLock' in navigator && !lock) { lock = await navigator.wakeLock.request('screen'); lock.addEventListener('release', () => { lock = null; }); } } catch (e) { lock = null; } }
  document.addEventListener('visibilitychange', () => { if (!document.hidden && want) keepAwake(); });
  return { keepAwake };
})();

/* ---------------- network (PeerJS / WebRTC) ---------------- */
const Net = (() => {
  const ALPHA = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789'; // 紛らわしい文字(0/O, 1/I/L)を除外
  const PREFIX = 'ouchi-approach-v1-';
  const PEER_OPTS = { debug: 0, config: { iceServers: [{ urls: 'stun:stun.l.google.com:19302' }] } }; // TURN中継は使わない
  let peer = null, conn = null, code = null, retryT = null, tries = 0, hostTries = 0;
  const randCode = (n) => { const a = new Uint32Array(n); crypto.getRandomValues(a); let s = ''; for (const v of a) s += ALPHA[v % ALPHA.length]; return s; };
  const fmt = (c) => c.slice(0, 4) + '-' + c.slice(4);
  const norm = (s) => String(s || '').toUpperCase().replace(/[^A-Z0-9]/g, '');
  const isOpen = () => !!(conn && conn.open);
  function safeParse(data) {
    let obj = data;
    if (typeof data === 'string') { if (data.length > 2000) return null; try { obj = JSON.parse(data); } catch (e) { return null; } }
    if (!obj || typeof obj !== 'object' || Array.isArray(obj)) return null;
    try { if (JSON.stringify(obj).length > 2000) return null; } catch (e) { return null; }
    return obj;
  }
  function drawQR(text) {
    const cv = $('qr'), ctx = cv.getContext('2d');
    const size = Math.round(232 * Math.min(3, devicePixelRatio || 1)); cv.width = cv.height = size;
    ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, size, size);
    if (!window.qrcode) return;
    const q = qrcode(0, 'M'); q.addData(text); q.make();
    const n = q.getModuleCount(), cell = Math.floor(size / (n + 8)), off = Math.floor((size - cell * n) / 2);
    ctx.fillStyle = '#000';
    for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (q.isDark(r, c)) ctx.fillRect(off + c * cell, off + r * cell, cell, cell);
  }
  function destroy() { if (peer) { try { peer.destroy(); } catch (e) {} } peer = null; conn = null; }

  /* ---- iPad: waits for one iPhone ---- */
  function host(fresh) {
    if (peer && !fresh) return;
    destroy();
    const saved = store.get('hostCode', null);
    code = (!fresh && saved && saved.c && Date.now() - saved.t < 24 * 3600e3) ? saved.c : randCode(8);
    store.set('hostCode', { c: code, t: Date.now() });
    $('codeOut').textContent = fmt(code);
    drawQR(location.origin + location.pathname + '#p=' + code);
    unpaired();
    if (!window.Peer) { setConn('off', '通信ライブラリを読み込めません'); return; }
    hostTries = 0; openHost();
  }
  function unpaired() { $('connectCard').classList.remove('paired'); $('pairNote').textContent = 'iPhoneのカメラアプリでこのQRコードを読み取ってください。'; setConn('wait', 'iPhoneを待っています'); }
  function openHost() {
    if (peer) { try { peer.destroy(); } catch (e) {} }
    peer = new Peer(PREFIX + code.toLowerCase(), PEER_OPTS);
    peer.on('open', () => { hostTries = 0; if (!isOpen()) setConn('wait', 'iPhoneを待っています'); });
    peer.on('error', (e) => {
      const t = e && e.type;
      if (t === 'unavailable-id') { if (++hostTries <= 5) setTimeout(openHost, 3000); else host(true); return; }
      if (['network', 'server-error', 'socket-error', 'socket-closed'].includes(t)) { setConn('off', '接続サーバーに届きません。再試行中'); setTimeout(() => { if (!isOpen()) openHost(); }, 5000); }
    });
    peer.on('disconnected', () => { try { peer.reconnect(); } catch (e) {} });
    peer.on('connection', (c) => {
      if (isOpen()) { c.on('open', () => c.close()); return; } // 2台目は受け付けない
      conn = c;
      c.on('open', () => {
        setConn('on', 'iPhoneと接続中'); $('connectCard').classList.add('paired'); $('pairNote').textContent = 'iPhoneとつながっています。';
        toast('iPhoneとつながりました'); App.sendInfo();
      });
      c.on('data', (d) => { const m = safeParse(d); if (m) App.onMessage(m); });
      c.on('close', () => { if (conn === c) { conn = null; unpaired(); App.setReady('off'); } });
    });
  }
  $('newCode').onclick = () => host(true);

  /* ---- iPhone ---- */
  function initCamera() {
    const c = store.get('code', '');
    if (c) { $('codeIn').value = fmt(c); connect(false); }
    else setConn('', '未接続');
  }
  function connect(manual) {
    const c = manual ? norm($('codeIn').value) : store.get('code', '');
    if (c.length !== 8) { if (manual) toast('コードは8文字です'); return; }
    store.set('code', c); clearTimeout(retryT);
    destroy();
    if (!window.Peer) { setConn('off', '通信ライブラリを読み込めません'); return; }
    setConn('wait', 'iPadにつないでいます…');
    peer = new Peer(PREFIX + 'cam-' + randCode(12).toLowerCase(), PEER_OPTS);
    peer.on('error', (e) => { setConn('off', e && e.type === 'peer-unavailable' ? 'iPadが見つかりません。iPadの画面を開いてください' : '接続できませんでした。再試行中'); retry(); });
    peer.on('open', () => {
      const cc = peer.connect(PREFIX + c.toLowerCase(), { reliable: true, serialization: 'json' }); conn = cc;
      cc.on('open', () => { tries = 0; setConn('on', 'iPadと接続中'); $('camPair').hidden = true; toast('iPadとつながりました'); Cam.pushStatus(true); });
      cc.on('data', (d) => { const m = safeParse(d); if (m && m.type === 'info') Cam.onInfo(m); });
      cc.on('close', () => { if (conn === cc) { conn = null; setConn('off', 'iPadとの接続が切れました。再接続中'); $('camPair').hidden = false; retry(); } });
    });
  }
  function retry() { clearTimeout(retryT); if (tries++ > 40) return; retryT = setTimeout(() => { if (!isOpen()) connect(false); }, 3000); }
  document.addEventListener('visibilitychange', () => { if (!document.hidden && role === 'camera' && !isOpen() && store.get('code', '')) { tries = 0; connect(false); } });
  $('connectBtn').onclick = () => { tries = 0; connect(true); };
  $('codeIn').addEventListener('keydown', (e) => { if (e.key === 'Enter') { tries = 0; connect(true); } });
  function send(msg) { if (isOpen()) { try { conn.send(msg); return true; } catch (e) {} } return false; }
  return { host, initCamera, send, isOpen };
})();

/* ======================================================================
   CAMERA (iPhone): live ball detection
   ====================================================================== */
const Cam = (() => {
  const vid = $('vid'), ov = $('overlay'), octx = ov.getContext('2d');
  const proc = document.createElement('canvas'); const pctx = proc.getContext('2d', { willReadFrequently: true });
  const PW = 320; let PH = 180;
  let stream = null, wake = null, running = false, frameN = 0;
  let model = store.get('ballModel', null); // {nx,ny,nr,color}
  let state = 'off', lastSent = '', prev = null, info = { next: '', lie: '' };
  let rest = null, stable = 0, lastPos = null, readyFrac = 0, low = 0;
  let pts = [], trackStart = 0, lost = 0, cooldownUntil = 0, lastTrack = null, needTap = false;
  let lastTouch = Date.now(), lastActive = Date.now(), dark = false;
  const IDLE_DARK = 20000, IDLE_STOP = 10 * 60000;
  const ftimes = [];
  const S = { diam: store.get('diam', 42.7), rad: 1, factor: store.get('factor', 1), angOff: store.get('angOff', 0), spin: store.get('spin', 1), sens: store.get('sens', 1) };
  [['sDiam','oDiam','diam',v=>v.toFixed(1)+' mm'],['sRad','oRad','rad',v=>'×'+v.toFixed(2)],['sFactor','oFactor','factor',v=>'×'+v.toFixed(2)],
   ['sAngOff','oAngOff','angOff',v=>(v>0?'+':'')+v.toFixed(1)+'°'],['sSpin','oSpin','spin',v=>'×'+v.toFixed(2)],['sSens','oSens','sens',v=>'×'+v.toFixed(2)]]
  .forEach(([s,o,k,f]) => { const e=$(s); e.value=S[k]; $(o).textContent=f(+e.value); e.oninput=()=>{ S[k]=+e.value; $(o).textContent=f(+e.value); if(k!=='rad') store.set(k,+e.value); }; });

  const TEXT = {
    off: ['カメラを開始してください', '三脚のiPhoneを横向きにして、ボールを挟んで自分と向かい合う位置(1〜1.5m)に置きます'],
    tap: ['ボールをタップして登録', 'ボールを置いて、映像の中のボールを1回タップしてください'],
    wait: ['ボールを置いてください', '登録した位置のまわりに置くと自動で認識します'],
    ready: ['打ってOK', ''],
    track: ['計測中…', ''],
    done: ['計測しました', 'iPadを見てください'],
    error: ['もう一度どうぞ', '']
  };
  function infoLine() { if (!info.next && !info.lie) return ''; return [info.next ? `次は ${info.next}` : '', info.lie ? `${info.lie}から打つ` : ''].filter(Boolean).join('・'); }
  function setState(s, sub) {
    state = s;
    const t = TEXT[s] || ['', ''];
    $('camStatus').dataset.state = s;
    $('stateText').textContent = t[0];
    $('stateSub').textContent = sub || ((s === 'ready' || s === 'wait') && infoLine()) || t[1];
    $('boText').textContent = t[0];
    pushStatus();
  }
  function pushStatus(force) {
    const st = state === 'tap' || state === 'error' || state === 'done' ? 'wait' : state;
    if (!force && st === lastSent) return;
    lastSent = st; Net.send({ type: 'status', state: st });
  }
  function onInfo(m) {
    info.next = typeof m.next === 'string' ? m.next.slice(0, 16) : '';
    info.lie = m.lie === 'マット' || m.lie === '絨毯' ? m.lie : '';
    if (state === 'ready' || state === 'wait') setState(state);
  }
  function setButtons() { $('camStart').hidden = running; $('camStop').hidden = !running; $('retap').hidden = !running; }

  async function start() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { toast('このブラウザではカメラを使えません(Safariで開いてください)'); return; }
    try {
      // 解像度を抑えて発熱を減らす(計測は320px幅で行うため十分)
      stream = await navigator.mediaDevices.getUserMedia({ audio: false, video: { facingMode: { ideal: 'environment' }, width: { ideal: 960 }, height: { ideal: 540 }, frameRate: { ideal: 60, max: 60 } } });
    } catch (e) { setState('error', 'カメラの使用が許可されませんでした。設定 → Safari → カメラ を確認してください'); return; }
    vid.srcObject = stream;
    try { await vid.play(); } catch (e) {}
    await new Promise(r => { if (vid.videoWidth) r(); else vid.onloadedmetadata = () => r(); });
    PH = Math.round(PW * vid.videoHeight / vid.videoWidth); proc.width = PW; proc.height = PH;
    $('stage').style.aspectRatio = vid.videoWidth + ' / ' + vid.videoHeight;
    $('stageEmpty').hidden = true;
    try { if ('wakeLock' in navigator) wake = await navigator.wakeLock.request('screen'); } catch (e) { wake = null; }
    running = true; prev = null; lastTouch = lastActive = Date.now(); setButtons();
    if (!model) { needTap = true; setState('tap'); } else resetToWait();
    loop();
  }
  function stop(msg) {
    running = false;
    if (stream) { stream.getTracks().forEach(t => t.stop()); stream = null; }
    vid.srcObject = null;
    try { if (wake) wake.release(); } catch (e) {} wake = null;
    $('stageEmpty').hidden = false; setButtons(); setDark(false);
    octx.clearRect(0, 0, ov.width, ov.height);
    setState('off', msg);
  }
  $('camStart').onclick = start;
  $('camStop').onclick = () => stop();
  document.addEventListener('visibilitychange', () => { if (document.hidden && running) stop('画面を離れたのでカメラを止めました。「カメラを開始」で再開します'); });
  window.addEventListener('pagehide', () => { if (running) stop(); });

  // 省電力: しばらく触らなければ画面を暗く、長時間打たなければカメラを休止
  function setDark(on) { dark = on; $('blackout').hidden = !on; }
  document.addEventListener('pointerdown', () => { lastTouch = lastActive = Date.now(); if (dark) setDark(false); }, true);
  setInterval(() => {
    if (!running || role !== 'camera') return;
    const now = Date.now();
    if (now - lastActive > IDLE_STOP) { stop('10分間打たなかったので、カメラを休止しました。「カメラを開始」で再開します'); return; }
    if (!dark && !needTap && now - lastTouch > IDLE_DARK) setDark(true);
    if (state === 'ready') pushStatus(true);
  }, 1000);

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
    // 黒い点の分を補うため、少し大きめに見積もる
    return { color: c, r: clamp(Math.sqrt(area / Math.PI) * 1.05, 2, 30) };
  }
  function videoBox() {
    const W = ov.width, H = ov.height, va = (vid.videoWidth || 16) / (vid.videoHeight || 9), ca = W / H;
    if (va > ca) { const h = W / va; return { x: 0, y: (H - h) / 2, w: W, h }; }
    const w = H * va; return { x: (W - w) / 2, y: 0, w, h: H };
  }
  ov.addEventListener('click', (e) => {
    if (!running || !vid.videoWidth || !needTap) return;
    const rect = ov.getBoundingClientRect(), b = videoBox();
    const nx = ((e.clientX - rect.left) * devicePixelRatio - b.x) / b.w, ny = ((e.clientY - rect.top) * devicePixelRatio - b.y) / b.h;
    if (nx < 0 || nx > 1 || ny < 0 || ny > 1) return;
    const m = measureBallAt(grab(), nx * PW, ny * PH);
    model = { nx, ny, nr: m.r / PW, color: m.color }; store.set('ballModel', model);
    needTap = false; resetToWait(); toast('ボールを登録しました');
  });
  $('retap').onclick = () => { model = null; store.set('ballModel', null); needTap = true; if (running) setState('tap'); };
  function resetToWait() { rest = null; stable = 0; lastPos = null; low = 0; pts = []; lost = 0; if (running && model) setState('wait'); }

  function params() {
    const br = Math.max(2, model.nr * PW * S.rad);
    return { br, area: Math.PI * br * br, CT: 75 * S.sens, DT: 28 / S.sens, zx: model.nx * PW, zy: model.ny * PH, zR: Math.max(8 * br, 36) };
  }
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
      if (n < P.area * 0.3 || n > P.area * 2.8) continue;
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
    lastTrack = pts.slice(); lastActive = Date.now();
    if (pts.length < 3) { setState('error', 'ボールを追えませんでした。明るさや背景を確認して、もう一度どうぞ'); cooldownUntil = performance.now() + 1500; return; }
    const ppm = (2 * P.br) / (S.diam / 1000), g = 9.81 * ppm, T0 = pts[0].t;
    const fit = (xs, ys) => { const n = xs.length, mx = xs.reduce((a, b) => a + b) / n, my = ys.reduce((a, b) => a + b) / n; let a = 0, b = 0; for (let i = 0; i < n; i++) { a += (xs[i] - mx) * (ys[i] - my); b += (xs[i] - mx) ** 2; } return b ? a / b : 0; };
    const use = pts.slice(0, 8), ts = use.map(p => p.t - T0);
    const vx = fit(ts, use.map(p => p.x)), vy = fit(ts, use.map((p, i) => p.y - 0.5 * g * ts[i] * ts[i]));
    const mSpeed = Math.hypot(vx, vy) / ppm, mAngle = Math.atan2(-vy, Math.abs(vx)) * 180 / Math.PI;
    if (!(mSpeed > 0.5 && mSpeed < 60) || mAngle < -10 || mAngle > 80) { setState('error', `計測値が不自然でした(${mSpeed.toFixed(1)}m/s, ${mAngle.toFixed(0)}°)。うまくいかない場合はボールを登録し直してください`); cooldownUntil = performance.now() + 2000; return; }
    const speed = clamp(mSpeed * S.factor, 1, 40), angle = clamp(mAngle + S.angOff, 0, 70);
    const spin = clamp(Math.round(290 * speed * (0.75 + angle / 120) * S.spin / 50) * 50, 500, 11000);
    const shot = { type: 'shot', id: Date.now().toString(36) + Math.random().toString(36).slice(2, 6), speed: +speed.toFixed(2), angle: +angle.toFixed(1), dir: 0, spin };
    $('cSpeed').textContent = speed.toFixed(1) + ' m/s'; $('cAngle').textContent = angle.toFixed(1) + '°'; $('cSpin').textContent = spin + ' rpm';
    $('cMeta').textContent = `練習ボールの計測値 ${mSpeed.toFixed(1)} m/s・${mAngle.toFixed(1)}° / 追跡 ${pts.length} コマ`;
    $('camResult').hidden = false;
    const ok = Net.send(shot);
    setState('done', ok ? 'iPadを見てください' : 'iPadと未接続のため送れていません');
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
      const p = rest || lastPos;
      if (p) { octx.strokeStyle = state === 'ready' ? '#3ddc84' : '#ffd24a'; octx.lineWidth = 3 * dpr; octx.beginPath(); octx.arc(b.x + p.x * sx, b.y + p.y * sy, P.br * sx + 5 * dpr, 0, Math.PI * 2); octx.stroke(); }
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
    frameN++;
    const busy = state === 'ready' || state === 'track';
    // ボール待ちの間は3コマに1回だけ解析して発熱を抑える
    if (!busy && frameN % 3 !== 0) return;
    const d = grab();
    ftimes.push(t); if (ftimes.length > 30) ftimes.shift();
    if (model && !needTap) {
      const P = params();
      if (state === 'track') { if (trackStep(d, t, P)) finishTrack(); }
      else if (performance.now() < cooldownUntil) { /* 結果表示中 */ }
      else if (state === 'ready') {
        const f = fracAt(d, P, rest.x, rest.y);
        if (f < readyFrac * 0.4) { low++; if (low >= 2) { setState('track'); trackStart = t; pts = []; lost = 0; } }
        else low = 0;
      } else {
        if (state !== 'wait') setState('wait');
        const b = findBall(d, P);
        if (b) {
          if (lastPos && Math.hypot(b.x - lastPos.x, b.y - lastPos.y) < 0.4 * P.br) stable++; else stable = 0;
          lastPos = b;
          if (stable >= 7) { rest = { x: b.x, y: b.y }; readyFrac = Math.max(0.2, fracAt(d, P, rest.x, rest.y)); low = 0; setState('ready'); }
        } else { stable = 0; lastPos = null; rest = null; }
      }
    }
    prev = d;
    if (!dark) drawOverlay();
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
  setButtons();
  return { pushStatus, onInfo };
})();

/* ======================================================================
   WORLD (iPad): 3D course, rendered only when something changes
   ====================================================================== */
const World = (() => {
  let renderer, scene, cam, root, ball, shadow, aimGroup, markerGroup, trailGroup, ballsGroup;
  let course = null, anim = null, dirty = true, inited = false, viewMode = 'follow', tapCb = null;
  let focus = { x: 0, z: 0 }, heading = 0, reach = 30;
  const camPos = new THREE.Vector3(-4, 2, 0), camLook = new THREE.Vector3(10, 0, 0), curLook = new THREE.Vector3(10, 0, 0);
  const rand = (a, b) => a + Math.random() * (b - a);
  function texCanvas(w, h, draw, rep) { const c = document.createElement('canvas'); c.width = w; c.height = h; draw(c.getContext('2d'), w, h); const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.repeat.set(rep, rep); return t; }
  function noise(ctx, w, h, base, amp, n) { ctx.fillStyle = base; ctx.fillRect(0, 0, w, h); for (let i = 0; i < n; i++) { const a = Math.random() * amp; ctx.fillStyle = Math.random() < .5 ? `rgba(0,0,0,${a})` : `rgba(255,255,255,${a * .6})`; ctx.fillRect(Math.random() * w, Math.random() * h, 2, 2); } }
  let TEX = null;
  function textures() {
    if (TEX) return TEX;
    TEX = {
      rough: texCanvas(256, 256, (c, w, h) => noise(c, w, h, '#3c7331', .2, 6000), 0.25),
      fairway: texCanvas(256, 256, (c, w, h) => { for (let i = 0; i < 4; i++) { c.fillStyle = i % 2 ? '#5aa548' : '#529c41'; c.fillRect(0, i * h / 4, w, h / 4); } for (let i = 0; i < 2500; i++) { c.fillStyle = `rgba(0,0,0,${Math.random() * .07})`; c.fillRect(Math.random() * w, Math.random() * h, 1.5, 1.5); } }, 1 / 12),
      green: texCanvas(256, 256, (c, w, h) => { for (let i = 0; i < 8; i++) { c.fillStyle = i % 2 ? '#68bd55' : '#5fb14c'; c.fillRect(i * w / 8, 0, w / 8, h); } for (let i = 0; i < 2500; i++) { c.fillStyle = `rgba(0,0,0,${Math.random() * .05})`; c.fillRect(Math.random() * w, Math.random() * h, 1, 1); } }, 1 / 8),
      fringe: texCanvas(128, 128, (c, w, h) => noise(c, w, h, '#4f9a45', .12, 1500), 0.5)
    };
    return TEX;
  }
  function init() {
    if (inited) return; inited = true;
    const world = $('world');
    renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: 'low-power' });
    renderer.setPixelRatio(Math.min(1.5, devicePixelRatio)); renderer.shadowMap.enabled = true;
    world.prepend(renderer.domElement);
    scene = new THREE.Scene(); scene.background = new THREE.Color('#bcdbe8'); scene.fog = new THREE.Fog('#bcdbe8', 70, 190);
    cam = new THREE.PerspectiveCamera(50, 16 / 10, 0.05, 400);
    scene.add(new THREE.HemisphereLight('#eaf6ff', '#3d5a2c', 0.78));
    const sun = new THREE.DirectionalLight('#fff6e5', 0.75); sun.position.set(-20, 40, 18); sun.castShadow = true;
    sun.shadow.mapSize.set(1024, 1024); Object.assign(sun.shadow.camera, { left: -70, right: 70, top: 70, bottom: -70, far: 140 });
    sun.target.position.set(40, 0, 0); scene.add(sun, sun.target);
    const treeMat = new THREE.MeshLambertMaterial({ color: '#2b5a2a' });
    for (let i = 0; i < 44; i++) { const a = Math.random() * Math.PI * 2, r = rand(120, 160); const t = new THREE.Mesh(new THREE.ConeGeometry(rand(3, 5), rand(9, 16), 6), treeMat); t.position.set(50 + Math.cos(a) * r, 5, Math.sin(a) * r); scene.add(t); }
    ball = new THREE.Mesh(new THREE.SphereGeometry(0.06, 20, 14), new THREE.MeshLambertMaterial({ color: '#ffffff' })); ball.castShadow = true; scene.add(ball);
    shadow = new THREE.Mesh(new THREE.CircleGeometry(0.07, 16), new THREE.MeshBasicMaterial({ color: '#000', transparent: true, opacity: .25 })); shadow.rotation.x = -Math.PI / 2; decal(shadow, 55); scene.add(shadow);
    aimGroup = new THREE.Group(); markerGroup = new THREE.Group(); trailGroup = new THREE.Group(); ballsGroup = new THREE.Group();
    scene.add(aimGroup, markerGroup, trailGroup, ballsGroup);
    new ResizeObserver(resize).observe(world);
    // タップで狙いを決める(ドラッグは無視)
    let down = null;
    renderer.domElement.addEventListener('pointerdown', (e) => { down = [e.clientX, e.clientY]; });
    renderer.domElement.addEventListener('pointerup', (e) => {
      if (!down || Math.hypot(e.clientX - down[0], e.clientY - down[1]) > 8 || !tapCb) return;
      const r = renderer.domElement.getBoundingClientRect();
      const ndc = new THREE.Vector2(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
      const rc = new THREE.Raycaster(); rc.setFromCamera(ndc, cam);
      const hit = new THREE.Vector3(); if (rc.ray.intersectPlane(new THREE.Plane(new THREE.Vector3(0, 1, 0), 0), hit)) tapCb(hit.x, hit.z);
    });
    requestAnimationFrame(loop);
  }
  function resize() { if (!renderer) return; const w = $('world').clientWidth, h = $('world').clientHeight; if (!w || !h) return; renderer.setSize(w, h, false); cam.aspect = w / h; cam.updateProjectionMatrix(); dirty = true; }

  function shapeOf(s, grow) {
    const g = grow || 0, sh = new THREE.Shape();
    if (s.kind === 'ellipse') sh.absellipse(s.cx, -s.cz, s.rx + g, s.rz + g, 0, Math.PI * 2, false, 0);
    else if (s.kind === 'rect') { sh.moveTo(s.x0 - g, -s.z0 + g); sh.lineTo(s.x1 + g, -s.z0 + g); sh.lineTo(s.x1 + g, -s.z1 - g); sh.lineTo(s.x0 - g, -s.z1 - g); sh.closePath(); }
    else { s.pts.forEach(([x, z], i) => i ? sh.lineTo(x, -z) : sh.moveTo(x, -z)); sh.closePath(); }
    return sh;
  }
  // 地面の層は重なり順(renderOrder)で描き分け、奥行きのちらつきを防ぐ
  function flat(shape, y, mat, recv) { const m = new THREE.Mesh(new THREE.ShapeGeometry(shape, 48), mat); m.rotation.x = -Math.PI / 2; m.position.y = y; m.receiveShadow = recv !== false; if (y >= 0) { mat.depthWrite = false; m.renderOrder = Math.round(y * 1000); } return m; }
  function decal(m, order) { m.material.depthWrite = false; m.renderOrder = order; return m; }
  function load(c) {
    init(); course = c;
    if (root) { scene.remove(root); root.traverse(o => { if (o.geometry) o.geometry.dispose(); }); }
    root = new THREE.Group();
    const T = textures();
    const lam = (opt) => new THREE.MeshLambertMaterial(opt);
    // ground with holes for chasms
    const g = new THREE.Shape(); g.moveTo(-120, 200); g.lineTo(260, 200); g.lineTo(260, -200); g.lineTo(-120, -200); g.closePath();
    const chasms = c.shapes.filter(s => s.type === 'chasm');
    chasms.forEach(s => g.holes.push(shapeOf(s)));
    root.add(flat(g, 0, lam({ map: T.rough })));
    if (c.allGreen) {
      root.add(flat(shapeOf({ kind: 'rect', x0: -6, x1: c.pin.x + 22, z0: -26, z1: 26 }), 0.004, lam({ map: T.green })));
    }
    c.shapes.filter(s => s.type === 'fairway' && !s.top).forEach(s => root.add(flat(shapeOf(s), 0.008, lam({ map: T.fairway }))));
    c.shapes.filter(s => s.type === 'water').forEach(s => {
      root.add(flat(shapeOf(s, 0.6), 0.012, lam({ color: '#8a7a55' })));
      root.add(flat(shapeOf(s), 0.016, new THREE.MeshPhongMaterial({ color: '#2d7fb8', shininess: 80, specular: '#bfe3ff' })));
    });
    c.shapes.filter(s => s.top).forEach(s => root.add(flat(shapeOf(s), 0.024, lam({ map: T.fairway }))));
    const greens = c.shapes.filter(s => s.type === 'green');
    greens.forEach(s => {
      const inWater = c.shapes.some(w => w.type === 'water' && SIM.inShape(w, s.cx, s.cz));
      if (!inWater) root.add(flat(shapeOf(s, 1.2), 0.03, lam({ map: T.fringe })));
      root.add(flat(shapeOf(s), 0.036, lam({ map: T.green })));
    });
    chasms.forEach(s => {
      const depth = 6, rock = lam({ color: '#5b4a3a', side: THREE.DoubleSide });
      const bottom = flat(shapeOf(s), -depth, lam({ color: '#1d1712' })); bottom.renderOrder = -2; root.add(bottom);
      const w = s.x1 - s.x0, d = s.z1 - s.z0;
      [[s.x0 + w / 2, s.z0, w, 0], [s.x0 + w / 2, s.z1, w, 0], [s.x0, s.z0 + d / 2, d, Math.PI / 2], [s.x1, s.z0 + d / 2, d, Math.PI / 2]].forEach(([x, z, len, ry]) => {
        const wall = new THREE.Mesh(new THREE.PlaneGeometry(len, depth), rock); wall.position.set(x, -depth / 2, z); wall.rotation.y = ry; wall.renderOrder = -1; root.add(wall);
      });
    });
    // cup, flag, 2m OK circle
    const P = c.pin;
    const okFill = new THREE.Mesh(new THREE.CircleGeometry(2, 64), new THREE.MeshBasicMaterial({ color: '#fff3a0', transparent: true, opacity: .22, depthWrite: false }));
    okFill.rotation.x = -Math.PI / 2; okFill.position.set(P.x, 0.042, P.z); root.add(decal(okFill, 42));
    const okRing = new THREE.Mesh(new THREE.RingGeometry(1.93, 2.07, 72), new THREE.MeshBasicMaterial({ color: '#ffffff', transparent: true, opacity: .95, side: THREE.DoubleSide }));
    okRing.rotation.x = -Math.PI / 2; okRing.position.set(P.x, 0.046, P.z); root.add(decal(okRing, 46));
    const cup = new THREE.Mesh(new THREE.CircleGeometry(0.054, 24), new THREE.MeshBasicMaterial({ color: '#101010' })); cup.rotation.x = -Math.PI / 2; cup.position.set(P.x, 0.05, P.z); root.add(decal(cup, 50));
    const pole = new THREE.Mesh(new THREE.CylinderGeometry(0.014, 0.014, 2.2, 8), lam({ color: '#f4f4f4' })); pole.position.set(P.x, 1.1, P.z); pole.castShadow = true; root.add(pole);
    const flag = new THREE.Mesh(new THREE.PlaneGeometry(0.55, 0.35), lam({ color: '#e0412a', side: THREE.DoubleSide })); flag.position.set(P.x, 2.0, P.z + 0.27); flag.rotation.y = Math.PI / 2; flag.castShadow = true; root.add(flag);
    // tee mat
    const tee = new THREE.Mesh(new THREE.BoxGeometry(1.6, 0.03, 1.6), lam({ color: '#1f4d2b' })); tee.position.set(c.tee.x, 0.015, c.tee.z); tee.receiveShadow = true; root.add(tee);
    scene.add(root);
    clearMarkers(); clearTrails(); ballsGroup.clear(); aimGroup.clear();
    placeBall(c.tee.x, 0, c.tee.z);
    dirty = true;
  }
  function placeBall(x, y, z) { ball.position.set(x, y + 0.06, z); shadow.position.set(x, 0.055, z); dirty = true; }
  function clearTrails() { while (trailGroup.children.length) { const o = trailGroup.children.pop(); o.geometry.dispose(); } }
  function clearMarkers() { markerGroup.clear(); }
  function setBalls(list) {
    ballsGroup.clear();
    list.forEach(b => {
      const m = new THREE.Mesh(new THREE.SphereGeometry(0.09, 16, 10), new THREE.MeshLambertMaterial({ color: b.color })); m.position.set(b.x, 0.09, b.z); ballsGroup.add(m);
      const ring = new THREE.Mesh(new THREE.RingGeometry(0.2, 0.28, 24), new THREE.MeshBasicMaterial({ color: b.color, side: THREE.DoubleSide })); ring.rotation.x = -Math.PI / 2; ring.position.set(b.x, 0.055, b.z); ballsGroup.add(decal(ring, 55));
    });
    dirty = true;
  }
  function addMarker(x, z, color) {
    while (markerGroup.children.length >= 24) markerGroup.remove(markerGroup.children[0]);
    const m = new THREE.Mesh(new THREE.SphereGeometry(0.06, 12, 8), new THREE.MeshLambertMaterial({ color })); m.position.set(x, 0.06, z); markerGroup.add(m);
    dirty = true;
  }
  function setAim(pos, hd, reachM) {
    focus = { x: pos.x, z: pos.z }; heading = hd; reach = reachM;
    aimGroup.clear();
    const dx = Math.cos(hd), dz = Math.sin(hd);
    const geo = new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(pos.x, 0.07, pos.z), new THREE.Vector3(pos.x + dx * reachM, 0.07, pos.z + dz * reachM)]);
    const line = new THREE.Line(geo, new THREE.LineDashedMaterial({ color: '#ffe066', dashSize: 0.8, gapSize: 0.5 })); line.computeLineDistances(); aimGroup.add(decal(line, 70));
    const arc = new THREE.Mesh(new THREE.RingGeometry(reachM - 0.18, reachM + 0.18, 48, 1, -hd - 0.5, 1.0), new THREE.MeshBasicMaterial({ color: '#ff8a5c', transparent: true, opacity: .85, side: THREE.DoubleSide }));
    arc.rotation.x = -Math.PI / 2; arc.position.set(pos.x, 0.06, pos.z); aimGroup.add(decal(arc, 60));
    placeBall(pos.x, 0, pos.z);
    idleCamera(); dirty = true;
  }
  function hideAim() { aimGroup.clear(); dirty = true; }
  function idleCamera() {
    if (!course) return;
    const dx = Math.cos(heading), dz = Math.sin(heading);
    if (viewMode === 'top') {
      const P = course.pin, cx = (focus.x + P.x) / 2, cz = (focus.z + P.z) / 2;
      const d = Math.max(Math.hypot(P.x - focus.x, P.z - focus.z), reach, 12);
      const h = d * 1.15 + 6;
      camPos.set(cx - dx * h * 0.28, h, cz - dz * h * 0.28); camLook.set(cx, 0, cz);
    } else {
      const L = Math.min(reach, Math.max(8, Math.hypot(course.pin.x - focus.x, course.pin.z - focus.z))) * 0.8;
      camPos.set(focus.x - dx * 4.5, 2.1, focus.z - dz * 4.5); camLook.set(focus.x + dx * L, 0, focus.z + dz * L);
    }
    dirty = true;
  }
  function setView(v) { viewMode = v; $('vFollow').setAttribute('aria-pressed', v === 'follow'); $('vTop').setAttribute('aria-pressed', v === 'top'); if (!anim) idleCamera(); }
  $('vFollow').onclick = () => setView('follow'); $('vTop').onclick = () => setView('top');
  function play(res, color, onDone) {
    hideAim();
    const geo = new THREE.BufferGeometry(); geo.setAttribute('position', new THREE.BufferAttribute(new Float32Array(3 * 4000), 3)); geo.setDrawRange(0, 0);
    const line = new THREE.Line(geo, new THREE.LineBasicMaterial({ color })); trailGroup.add(line);
    while (trailGroup.children.length > 8) { const o = trailGroup.children.shift(); trailGroup.remove(o); o.geometry.dispose(); }
    anim = { res, line, start: performance.now(), onDone };
  }
  function loop(now) {
    requestAnimationFrame(loop);
    if (!renderer || $('playView').hidden) return;
    let moving = false;
    if (anim) {
      moving = true;
      const t = (now - anim.start) / 1000, pts = anim.res.pts; let i = 0;
      while (i < pts.length - 1 && pts[i + 1][0] < t) i++;
      const a = pts[i], b = pts[Math.min(i + 1, pts.length - 1)];
      const f = b[0] > a[0] ? clamp((t - a[0]) / (b[0] - a[0]), 0, 1) : 1;
      const x = a[1] + (b[1] - a[1]) * f, y = a[2] + (b[2] - a[2]) * f, z = a[3] + (b[3] - a[3]) * f;
      placeBall(x, y, z);
      const arr = anim.line.geometry.attributes.position.array, n = Math.min(i + 1, 3999);
      for (let k = 0; k < n; k++) { arr[k * 3] = pts[k][1]; arr[k * 3 + 1] = pts[k][2] + 0.04; arr[k * 3 + 2] = pts[k][3]; }
      arr[n * 3] = x; arr[n * 3 + 1] = y + 0.04; arr[n * 3 + 2] = z;
      anim.line.geometry.setDrawRange(0, n + 1); anim.line.geometry.attributes.position.needsUpdate = true;
      if (viewMode === 'follow') { const s = anim.res.pts[0], e = pts[Math.min(i + 3, pts.length - 1)]; let dx = e[1] - s[1], dz = e[3] - s[3]; const L = Math.hypot(dx, dz) || 1; dx /= L; dz /= L; if (L < 0.5) { dx = Math.cos(heading); dz = Math.sin(heading); } camPos.set(x - dx * 5.5, Math.max(1.6, y + 1.8), z - dz * 5.5); camLook.set(x + dx * 2, y * 0.6, z + dz * 2); }
      if (t >= anim.res.duration + 0.05) { const cb = anim.onDone; anim = null; if (cb) cb(); }
    }
    if (cam.position.distanceTo(camPos) > 0.01 || curLook.distanceTo(camLook) > 0.01) { moving = true; cam.position.lerp(camPos, 0.07); curLook.lerp(camLook, 0.09); }
    if (!moving && !dirty) return; // 何も動いていないときは描画しない(発熱対策)
    cam.lookAt(curLook);
    renderer.render(scene, cam);
    dirty = false;
  }
  function focusOn(x, z) { camLook.set(x, 0, z); dirty = true; }
  return { init, load, setAim, hideAim, setBalls, addMarker, clearMarkers, clearTrails, play, placeBall, resize, focusOn, onTap: (cb) => { tapCb = cb; }, busy: () => !!anim };
})();

/* ======================================================================
   APP (iPad): home, free practice, course play
   ====================================================================== */
const App = (() => {
  let limit = store.get('limit', 35), nPlayers = store.get('np', 1);
  const names = [store.get('name0', 'プレイヤー1'), store.get('name1', 'プレイヤー2')];
  const COLORS = ['#e2553a', '#3f78e0'];
  let G = null, readyState = 'off';
  const seen = new Set();
  const limitM = () => limit * YD;
  const freeReach = () => (G && G.yd ? G.yd + 3 : 30) * YD;
  const dist = (a, b) => Math.hypot(a.x - b.x, a.z - b.z);
  const headingTo = (a, b) => Math.atan2(b.z - a.z, b.x - a.x);

  /* ---- home ---- */
  function initHome() {
    [...$('limitSeg').children].forEach(b => { b.setAttribute('aria-pressed', +b.dataset.v === limit); b.onclick = () => { limit = +b.dataset.v; store.set('limit', limit); initHome(); }; });
    const u = COURSES.unitYd(limit);
    $('limitNote').textContent = `コースの長さ:パー2 ${u}ヤード/パー3 ${u * 2}ヤード/パー4 ${u * 3}ヤード`;
    setReady(readyState);
  }
  $('goFree').onclick = () => { buildDist(); show('freeView'); };
  $('goCourse').onclick = () => { buildCourses(); show('courseView'); };
  document.querySelectorAll('[data-back]').forEach(b => { b.onclick = () => { show('homeView'); initHome(); }; });

  function buildDist() {
    const g = $('distGrid'); g.textContent = '';
    [5, 10, 15, 20, 25, 30, 35, 40, 45, 60].forEach(d => {
      const b = el('button', d === 60 ? 'strong' : null); b.append(String(d), el('small', null, d === 60 ? 'ヤード・強めに' : 'ヤード'));
      b.onclick = () => startFree(d); g.append(b);
    });
  }
  function buildCourses() {
    [...$('playerSeg').children].forEach(b => { b.setAttribute('aria-pressed', +b.dataset.v === nPlayers); b.onclick = () => { nPlayers = +b.dataset.v; store.set('np', nPlayers); buildCourses(); }; });
    $('name1wrap').hidden = nPlayers < 2;
    [0, 1].forEach(i => { const inp = $('name' + i); inp.value = names[i]; inp.oninput = () => { names[i] = inp.value.trim() || `プレイヤー${i + 1}`; store.set('name' + i, names[i]); }; });
    const g = $('courseGrid'); g.textContent = '';
    COURSES.defs.forEach(d => {
      const c = COURSES.make(d.id, limit);
      const b = el('button', 'ccard');
      const cv = document.createElement('canvas'); cv.width = 320; cv.height = 200; drawMini(cv, c);
      const meta = el('div', 'meta'); meta.append(el('span', 'par', `パー${c.par}・${c.lengthYd}ヤード`), el('span', 'style' + (d.style === 'テクニカル' ? ' tech' : ''), d.style));
      b.append(cv, meta, el('b', null, c.name), el('span', 'd', c.desc));
      b.onclick = () => startCourse(d.id);
      g.append(b);
    });
  }
  // 上から見たミニマップ(ティーが下、ピンが上)
  function drawMini(cv, c) {
    const ctx = cv.getContext('2d'), W = cv.width, H = cv.height;
    let minX = -4, maxX = c.pin.x + 8, minZ = -8, maxZ = 8;
    c.shapes.forEach(s => { if (s.kind === 'ellipse') { minX = Math.min(minX, s.cx - s.rx); maxX = Math.max(maxX, s.cx + s.rx); minZ = Math.min(minZ, s.cz - s.rz); maxZ = Math.max(maxZ, s.cz + s.rz); } else if (s.kind === 'rect') { minZ = Math.min(minZ, s.z0); maxZ = Math.max(maxZ, s.z1); } });
    minZ = Math.max(minZ, -60); maxZ = Math.min(maxZ, 60); maxX = Math.min(maxX, c.pin.x + 14);
    const sc = Math.min((H - 16) / (maxX - minX), (W - 16) / (maxZ - minZ));
    const ox = W / 2 - ((minZ + maxZ) / 2) * sc, oy = H - 8 + minX * sc;
    const P = (x, z) => [ox + z * sc, oy - x * sc];
    ctx.fillStyle = '#3c7331'; ctx.fillRect(0, 0, W, H);
    const drawS = (s, col, grow) => {
      ctx.fillStyle = col; ctx.beginPath();
      if (s.kind === 'ellipse') { const [x, y] = P(s.cx, s.cz); ctx.ellipse(x, y, (s.rz + (grow || 0)) * sc, (s.rx + (grow || 0)) * sc, 0, 0, Math.PI * 2); }
      else { const [x0, y0] = P(s.x1, s.z0), [x1, y1] = P(s.x0, s.z1); ctx.rect(x0, y0, x1 - x0, y1 - y0); }
      ctx.fill();
    };
    c.shapes.filter(s => s.type === 'fairway' && !s.top).forEach(s => drawS(s, '#5aa548'));
    c.shapes.filter(s => s.type === 'water').forEach(s => drawS(s, '#2d7fb8'));
    c.shapes.filter(s => s.type === 'chasm').forEach(s => drawS(s, '#1d1712'));
    c.shapes.filter(s => s.top).forEach(s => drawS(s, '#5aa548'));
    c.shapes.filter(s => s.type === 'green').forEach(s => { drawS(s, '#8ad672'); });
    const [px, py] = P(c.pin.x, c.pin.z), [tx, ty] = P(0, 0);
    ctx.strokeStyle = 'rgba(255,255,255,.75)'; ctx.setLineDash([5, 5]); ctx.lineWidth = 2; ctx.beginPath(); ctx.moveTo(tx, ty);
    c.route.forEach(r => { const [x, y] = P(r.x, r.z); ctx.lineTo(x, y); }); ctx.lineTo(px, py); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle = '#fff'; ctx.beginPath(); ctx.arc(tx, ty, 4, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#e0412a'; ctx.beginPath(); ctx.arc(px, py, 4.5, 0, Math.PI * 2); ctx.fill();
  }

  /* ---- play common ---- */
  function enterPlay(mode) {
    show('playView');
    $('sideFree').hidden = mode !== 'free'; $('sideCourse').hidden = mode !== 'course';
    $('aimBar').hidden = mode !== 'course'; $('resultBox').hidden = true; $('banner').hidden = true;
    ['gSpeed', 'gAngle', 'gSpin', 'gCarry', 'gTotal', 'gPin'].forEach(id => { $(id).textContent = '–'; });
    setReady(readyState);
  }
  function banner(t, sub, ms) {
    const b = $('banner'); b.textContent = t; if (sub) b.append(el('small', null, sub)); b.hidden = false;
    clearTimeout(banner._t); if (ms) banner._t = setTimeout(() => { b.hidden = true; }, ms);
  }
  function showShotStart(shot) { $('gSpeed').textContent = shot.speed.toFixed(1) + ' m/s'; $('gAngle').textContent = shot.angle.toFixed(1) + '°'; $('gSpin').textContent = Math.round(shot.spin) + ' rpm'; ['gCarry', 'gTotal', 'gPin'].forEach(id => { $(id).textContent = '…'; }); $('banner').hidden = true; }
  function showShotEnd(res) { $('gCarry').textContent = fy(res.carry) + ' yd'; $('gTotal').textContent = fy(res.total) + ' yd'; $('gPin').textContent = res.hazard ? '–' : res.holed ? 'カップイン' : fDist(res.toPin); }

  /* ---- free practice ---- */
  function startFree(d) {
    const c = COURSES.practice(d);
    G = { mode: 'free', yd: d, course: c, shots: [], busy: false };
    enterPlay('free');
    World.load(c); World.setAim(c.tee, 0, freeReach());
    $('hTitle').textContent = 'フリー練習'; $('hMain').textContent = `ピンまで ${d}ヤード`;
    $('hTurn').textContent = 'グリーン'; $('hSub').textContent = `速さ ${c.stimp}ft`;
    World.onTap(null);
    renderFree(); sendInfo();
  }
  function afterFree(res) {
    const over = false, ok = res.holed || res.toPin <= 2;
    G.shots.push({ total: res.total, toPin: res.toPin, ok, over, holed: res.holed });
    World.addMarker(res.end.x, res.end.z, over ? '#ff5a3c' : ok ? '#ffe066' : '#ffffff');
    if (res.holed) banner('カップイン!', null, 2500);
    else if (over) banner('上限オーバー', `総距離 ${fy(res.total)}ヤード`, 2500);
    else if (ok) banner('OK!', `ピンまで ${fDist(res.toPin)}`, 2500);
    else banner(`ピンまで ${fDist(res.toPin)}`, null, 2000);
    renderFree();
    setTimeout(() => { if (G && G.mode === 'free') { World.setAim(G.course.tee, 0, freeReach()); G.busy = false; } }, 1600);
  }
  function renderFree() {
    const s = G.shots, n = s.length;
    $('fsN').textContent = n;
    $('fsOk').textContent = n ? `${Math.round(s.filter(x => x.ok && !x.over).length / n * 100)}%` : '–';
    const valid = s.filter(x => !x.over);
    $('fsAvg').textContent = valid.length ? fDist(valid.reduce((a, b) => a + b.toPin, 0) / valid.length) : '–';
    $('fsBest').textContent = valid.length ? fDist(Math.min(...valid.map(x => x.toPin))) : '–';
    const t = $('freeLog'); t.textContent = '';
    const hr = el('tr'); ['#', '総距離', 'ピンまで', ''].forEach((h, i) => hr.append(el('th', i ? 'n' : null, h))); t.append(hr);
    if (!n) { const r = el('tr'); const c = el('td', 'empty', 'iPhoneの「打ってOK」を確認して打ってみましょう。'); c.colSpan = 4; r.append(c); t.append(r); }
    s.map((x, i) => [x, i]).reverse().forEach(([x, i]) => {
      const r = el('tr');
      r.append(el('td', null, String(i + 1)), el('td', 'n', fy(x.total) + 'yd'), el('td', 'n', x.holed ? 'IN' : fDist(x.toPin)), el('td', 'n' + (x.over ? ' bad' : x.ok ? ' good' : ''), x.over ? 'オーバー' : x.ok ? 'OK' : ''));
      t.append(r);
    });
  }
  $('changeDist').onclick = () => { buildDist(); show('freeView'); };

  /* ---- course ---- */
  let lastCourseId = null;
  function startCourse(id) {
    lastCourseId = id;
    const c = COURSES.make(id, limit);
    const players = [];
    for (let i = 0; i < nPlayers; i++) players.push({ name: names[i], color: COLORS[i], cls: 'c' + (i + 1), pos: { ...c.tee }, strokes: 0, done: false, score: null, note: '', log: [] });
    G = { mode: 'course', course: c, players, cur: 0, aim: 0, busy: false };
    enterPlay('course');
    World.load(c);
    $('hTitle').textContent = `${c.name}・パー${c.par}`; $('hMain').textContent = `${c.lengthYd}ヤード`;
    $('aimRoute').hidden = !c.route.length;
    World.onTap((x, z) => { if (!G || G.mode !== 'course' || G.busy) return; const p = G.players[G.cur]; if (Math.hypot(x - p.pos.x, z - p.pos.z) < 1) return; G.aim = headingTo(p.pos, { x, z }); World.setAim(p.pos, G.aim, limitM()); });
    beginTurn();
  }
  const lieOf = (pos) => SIM.zoneAt(G.course, pos.x, pos.z) === 'rough' ? '絨毯' : 'マット';
  function nextPlayer() { let bi = -1, bd = -1; G.players.forEach((p, i) => { if (p.done) return; const d = dist(p.pos, G.course.pin); if (d > bd + 0.01) { bd = d; bi = i; } }); return bi; }
  function beginTurn() {
    const i = nextPlayer();
    if (i < 0) { finishHole(); return; }
    G.cur = i; G.busy = false;
    const p = G.players[i];
    G.aim = headingTo(p.pos, G.course.pin);
    World.setBalls(G.players.filter((q, k) => k !== i && !q.done && dist(q.pos, p.pos) > 0.4).map(q => ({ x: q.pos.x, z: q.pos.z, color: q.color })));
    World.setAim(p.pos, G.aim, limitM());
    const lie = lieOf(p.pos);
    $('hTurn').textContent = `${G.players.length > 1 ? p.name + '・' : ''}${p.strokes + 1}打目`;
    $('hSub').textContent = `残り ${fy(dist(p.pos, G.course.pin))}yd・${lie}から`;
    if (lie === '絨毯') banner('ラフです', '絨毯の上から打ってください', 3000);
    else if (G.players.length > 1) banner(`${p.name} の番`, `${lie}から打ってください`, 2200);
    renderCourse(); sendInfo();
  }
  function aimStep(deg) { if (!G || G.mode !== 'course' || G.busy) return; G.aim += deg * Math.PI / 180; World.setAim(G.players[G.cur].pos, G.aim, limitM()); }
  $('aimL').onclick = () => aimStep(-2);
  $('aimR').onclick = () => aimStep(2);
  $('aimPin').onclick = () => { if (!G || G.mode !== 'course' || G.busy) return; const p = G.players[G.cur]; G.aim = headingTo(p.pos, G.course.pin); World.setAim(p.pos, G.aim, limitM()); };
  $('aimRoute').onclick = () => {
    if (!G || G.mode !== 'course' || G.busy) return;
    const p = G.players[G.cur], pin = G.course.pin, dp = dist(p.pos, pin);
    const r = G.course.route.find(rp => dist(rp, pin) < dp - 3 && dist(p.pos, rp) > 4);
    G.aim = headingTo(p.pos, r || pin); World.setAim(p.pos, G.aim, limitM());
  };
  function afterCourse(p, res) {
    const par = G.course.par; let msg = '', sub = '', kind = '';
    if (res.hazard) { p.strokes += 2; msg = res.hazard === 'water' ? '池ポチャ' : '崖から落下'; sub = '1打罰・元の場所から打ち直し'; kind = 'ペナルティ'; }
    else if (res.total >= limitM() - 1e-6) { p.strokes += 2; msg = '上限オーバー'; sub = `総距離 ${fy(res.total)}ヤード・1打罰・元の場所から打ち直し`; kind = '上限オーバー'; }
    else {
      p.strokes += 1; p.pos = { x: res.end.x, z: res.end.z };
      if (res.holed) { p.done = true; p.score = p.strokes; msg = 'カップイン!'; kind = 'カップイン'; }
      else if (res.toPin <= 2) { p.done = true; p.score = p.strokes + 1; msg = 'OK!'; sub = `ピンまで ${fDist(res.toPin)}・+1打で上がり`; kind = 'OK'; }
      else { const z = SIM.zoneAt(G.course, p.pos.x, p.pos.z); msg = `残り ${fy(res.toPin)}ヤード`; sub = z === 'rough' ? 'ラフ:次は絨毯から' : z === 'green' ? 'グリーン' : 'フェアウェイ'; kind = z === 'rough' ? 'ラフ' : z === 'green' ? 'グリーン' : 'フェアウェイ'; }
    }
    if (!p.done && p.strokes >= 2 * par) { p.done = true; p.gaveUp = true; p.score = 2 * par; msg = 'ギブアップ'; sub = `ダブルパー(${2 * par}打)で打ち切り`; }
    if (p.done && p.score > 2 * par) p.score = 2 * par;
    p.log.push({ n: p.strokes, total: res.total, toPin: res.hazard ? null : res.toPin, kind });
    banner(msg, sub, 2600);
    if (!res.hazard && p.pos) World.addMarker(res.end.x, res.end.z, p.color);
    renderCourse();
    setTimeout(() => { if (G && G.mode === 'course') beginTurn(); }, 2700);
  }
  const SCORE_NAME = { '-3': 'アルバトロス', '-2': 'イーグル', '-1': 'バーディー', '0': 'パー', '1': 'ボギー', '2': 'ダブルボギー' };
  const scoreName = (s, par) => { const d = s - par; return SCORE_NAME[String(d)] || (d < -3 ? `${d}` : `+${d}`); };
  function renderCourse() {
    const par = G.course.par, wrap = $('scPlayers'); wrap.textContent = '';
    $('scTitle').textContent = `スコア(パー${par})`;
    G.players.forEach((p, i) => {
      const c = el('div', `pcard ${p.cls}` + (i === G.cur && !p.done ? ' turn' : ''));
      c.append(el('i'), el('b', null, p.name), el('span', 'sc', p.done ? String(p.score) : String(p.strokes)));
      c.append(el('span', 'st', p.done ? `${p.gaveUp ? 'ギブアップ' : '上がり'}・${scoreName(p.score, par)}` : `${p.strokes}打・残り ${fy(dist(p.pos, G.course.pin))}yd・${lieOf(p.pos)}から`));
      wrap.append(c);
    });
    const t = $('courseLog'); t.textContent = '';
    const hr = el('tr'); ['', '打数', '総距離', '結果'].forEach((h, i) => hr.append(el('th', i ? 'n' : null, h))); t.append(hr);
    const rows = []; G.players.forEach(p => p.log.forEach((l, k) => rows.push({ p, l, k })));
    if (!rows.length) { const r = el('tr'); const c = el('td', 'empty', '狙いを決めて、iPhoneの「打ってOK」を確認して打ちましょう。'); c.colSpan = 4; r.append(c); t.append(r); }
    rows.reverse().forEach(({ p, l }) => { const r = el('tr'); r.append(el('td', null, p.name), el('td', 'n', String(l.n)), el('td', 'n', fy(l.total) + 'yd'), el('td', 'n' + (l.kind === 'ペナルティ' || l.kind === '上限オーバー' ? ' bad' : l.kind === 'OK' || l.kind === 'カップイン' ? ' good' : ''), l.kind)); t.append(r); });
  }
  function finishHole() {
    G.busy = true; World.hideAim(); World.setBalls([]);
    const par = G.course.par, ps = G.players;
    const tb = $('resTable'); tb.textContent = '';
    const best = Math.min(...ps.map(p => p.score));
    const hr = el('tr'); ['', '打数', ''].forEach((h, i) => hr.append(el('th', i === 1 ? 'n' : null, h))); tb.append(hr);
    ps.forEach(p => { const r = el('tr', ps.length > 1 && p.score === best ? 'win' : null); r.append(el('td', null, p.name), el('td', 'n', String(p.score)), el('td', null, (p.gaveUp ? 'ギブアップ ' : '') + scoreName(p.score, par))); tb.append(r); });
    if (ps.length > 1) { const w = ps.filter(p => p.score === best); $('resTitle').textContent = w.length > 1 ? '引き分け' : `${w[0].name} の勝ち`; }
    else $('resTitle').textContent = `ホールアウト:${scoreName(ps[0].score, par)}`;
    $('resultBox').hidden = false; $('banner').hidden = true;
    sendInfo();
  }
  $('resAgain').onclick = () => startCourse(lastCourseId);
  $('resCourse').onclick = () => { G = null; buildCourses(); show('courseView'); sendInfo(); };
  $('resHome').onclick = () => { G = null; show('homeView'); initHome(); sendInfo(); };
  let quitArm = 0;
  $('quitPlay').onclick = () => {
    if (Date.now() - quitArm > 3000) { quitArm = Date.now(); $('quitPlay').textContent = 'もう一度押すとホームへ戻ります'; setTimeout(() => { $('quitPlay').textContent = 'やめてホームへ'; }, 3000); return; }
    G = null; $('quitPlay').textContent = 'やめてホームへ'; show('homeView'); initHome(); sendInfo();
  };

  /* ---- shots & messages ---- */
  function onShot(s) {
    if (seen.has(s.id)) return; seen.add(s.id);
    if (!G || $('playView').hidden) { toast('iPadでモードを選んでから打ってください'); return; }
    if (G.busy || World.busy()) { toast('前の打球を表示中です'); return; }
    G.busy = true; showShotStart(s);
    if (G.mode === 'free') {
      const res = SIM.simulate(s, G.course, G.course.tee, 0);
      World.play(res, '#ffffff', () => { showShotEnd(res); afterFree(res); });
    } else {
      const p = G.players[G.cur];
      const res = SIM.simulate(s, G.course, p.pos, G.aim);
      World.play(res, p.color, () => { showShotEnd(res); afterCourse(p, res); });
    }
  }
  const num = (v, a, b) => { v = Number(v); return Number.isFinite(v) ? clamp(v, a, b) : null; };
  function onMessage(m) {
    if (m.type === 'status') { if (['wait', 'ready', 'track', 'off'].includes(m.state)) setReady(m.state); return; }
    if (m.type === 'shot') {
      const s = { id: String(m.id || '').slice(0, 32), speed: num(m.speed, 1, 40), angle: num(m.angle, 0, 70), dir: num(m.dir, -30, 30) ?? 0, spin: num(m.spin, 0, 12000) };
      if (!s.id || s.speed == null || s.angle == null || s.spin == null) return;
      onShot(s);
    }
  }
  const READY_TEXT = { off: 'カメラ待ち', wait: 'ボールを置いてください', ready: '打ってOK', track: '計測中…' };
  const HOME_TEXT = { off: 'iPhoneのカメラ待ち', wait: 'iPhone:ボールを置いてください', ready: 'iPhone:打ってOK', track: 'iPhone:計測中' };
  function setReady(s) {
    readyState = s;
    $('readyMark').dataset.state = s; $('readyText').textContent = READY_TEXT[s] || '';
    $('homeReady').dataset.state = s; $('homeReadyText').textContent = HOME_TEXT[s] || '';
  }
  function sendInfo() {
    let next = '', lie = '';
    if (G && G.mode === 'course' && $('resultBox').hidden) { const p = G.players[G.cur]; if (p && !p.done) { next = G.players.length > 1 ? p.name : ''; lie = lieOf(p.pos); } }
    else if (G && G.mode === 'free') lie = 'マット';
    Net.send({ type: 'info', next, lie });
  }
  // test shot
  const tfmt = { tSpeed: v => v + ' m/s', tAngle: v => v + '°', tSpin: v => v + ' rpm' };
  Object.keys(tfmt).forEach(k => { const e = $(k), o = $('o' + k); const u = () => { o.textContent = tfmt[k](+e.value); }; e.oninput = u; u(); });
  $('testShot').onclick = () => onShot({ id: 't' + Date.now() + Math.random(), speed: +$('tSpeed').value, angle: +$('tAngle').value, dir: 0, spin: +$('tSpin').value });
  return { initHome, onMessage, setReady, sendInfo };
})();

/* ---------------- boot ---------------- */
if (role === 'camera' || role === 'green') startRole(role); else show('roleView');
})();
