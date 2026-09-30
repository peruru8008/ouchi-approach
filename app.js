'use strict';
/* おうちアプローチ — 56° WEDGE CHALLENGE
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
  // 曲がったフェアウェイ:中心線の点列と半幅から多角形を作る
  function corridor(type, pts, hw, extra) {
    const L = [], R = [];
    for (let i = 0; i < pts.length; i++) {
      const a = pts[Math.max(0, i - 1)], b = pts[Math.min(pts.length - 1, i + 1)];
      let dx = b[0] - a[0], dz = b[1] - a[1]; const l = Math.hypot(dx, dz) || 1; dx /= l; dz /= l;
      L.push([pts[i][0] + dz * hw, pts[i][1] - dx * hw]); R.push([pts[i][0] - dz * hw, pts[i][1] + dx * hw]);
    }
    // 両端を少し丸める
    const s = pts[0], e = pts[pts.length - 1];
    const cap = (p, a, b, back) => { const out = []; for (let k = 1; k < 6; k++) { const t = k / 6 * Math.PI; const mx = (a[0] + b[0]) / 2, mz = (a[1] + b[1]) / 2; const rx = a[0] - mx, rz = a[1] - mz; const c = Math.cos(t), sn = Math.sin(t); out.push([mx + rx * c + back[0] * sn * hw * 0.6, mz + rz * c + back[1] * sn * hw * 0.6]); } return out; };
    const d0 = [pts[0][0] - pts[1][0], pts[0][1] - pts[1][1]], l0 = Math.hypot(d0[0], d0[1]) || 1;
    const n = pts.length, d1 = [pts[n - 1][0] - pts[n - 2][0], pts[n - 1][1] - pts[n - 2][1]], l1 = Math.hypot(d1[0], d1[1]) || 1;
    const poly = [...L, ...cap(e, L[n - 1], R[n - 1], [d1[0] / l1, d1[1] / l1]), ...R.reverse(), ...cap(s, R[R.length - 1], L[0], [d0[0] / l0, d0[1] / l0])];
    return Object.assign({ type, kind: 'poly', pts: poly }, extra || {});
  }
  const defs = [
    { id: 'p2s', par: 2, style: 'シンプル', name: 'ファーストステップ', desc: '右に少し振ったグリーン。手前左のラフに気をつけて、まずは基本の1打。',
      build: (f) => ({ pin: { x: f, z: 2.5 }, stimp: 9.5, slope: { x: -0.012, z: -0.006 }, route: [],
        shapes: [E('green', f + 1, 2, 8, 7), corridor('fairway', [[-3, 0], [0.5 * f, 0.5], [f - 6, 2]], 10),
          E('rough', 0.6 * f, -7.5, 4.5, 3, { top: true }), E('rough', 0.8 * f, 9, 4, 2.6, { top: true })] }) },
    { id: 'p2t', par: 2, style: 'テクニカル', name: '浮島グリーン', desc: '池に浮かぶ小さなグリーン。届かなくても、越えすぎても池。',
      build: (f) => ({ pin: { x: f, z: -0.8 }, stimp: 11, slope: { x: 0.006, z: -0.01 }, route: [],
        shapes: [E('green', f, -0.5, 6, 5.2), E('water', f, -0.5, 12.5, 11.5), corridor('fairway', [[-3, 0], [0.4 * f, 0], [f - 13.5, -0.5]], 9),
          E('rough', 0.3 * f, 7, 4, 2.6, { top: true })] }) },
    { id: 'p3s', par: 3, style: 'シンプル', name: 'リバーサイド', desc: 'ゆるやかに左へ曲がるホール。曲がり角の外側のラフは避けたい。',
      build: (f) => ({ pin: { x: 1.85 * f, z: -0.55 * f }, stimp: 10, slope: { x: -0.012, z: 0.008 }, route: [{ x: 1.0 * f, z: 0 }],
        shapes: [E('green', 1.85 * f + 1, -0.55 * f, 8, 7), corridor('fairway', [[-3, 0], [0.9 * f, 0], [1.3 * f, -0.2 * f], [1.72 * f, -0.5 * f]], 9),
          E('rough', 1.12 * f, 0.26 * f, 5, 3.5, { top: true }), E('rough', 0.45 * f, -8.5, 4, 2.4, { top: true })] }) },
    { id: 'p3t', par: 3, style: 'テクニカル', name: '崖越えアイランド', desc: '右ドッグレッグ。崖の真ん中の浮島に止められれば近道、落ちたら1打罰。',
      build: (f) => ({ pin: { x: f, z: f + 0.5 }, stimp: 10.5, slope: { x: 0.008, z: -0.012 }, route: [{ x: 0.47 * f, z: 0.53 * f }, { x: f, z: 0 }],
        shapes: [E('green', f, f + 0.5, 7, 7), corridor('fairway', [[-3, 0], [f, 0], [f, f - 6]], 8),
          E('fairway', 0.47 * f, 0.53 * f, 0.13 * f, 0.11 * f, { top: true, island: true }),
          Rc('chasm', 0.25 * f, f - 9.5, Math.max(9.5, 0.32 * f), 0.76 * f),
          E('rough', f + 9, 0.35 * f, 3, 5, { top: true })] }) },
    { id: 'p4s', par: 4, style: 'シンプル', name: 'ゆったり湖畔', desc: 'S字にうねるフェアウェイ。左の湖を眺めながら、3打でリズムよく。',
      build: (f) => ({ pin: { x: 3 * f, z: 0.3 }, stimp: 10, slope: { x: -0.01, z: 0.008 }, route: [{ x: 0.85 * f, z: 0 }, { x: 1.8 * f, z: 0.35 * f }],
        shapes: [E('green', 3 * f + 1, 0, 8, 7), corridor('fairway', [[-3, 0], [0.8 * f, 0], [1.4 * f, 0.35 * f], [2.2 * f, 0.35 * f], [2.75 * f, 0.05 * f]], 9),
          E('water', 1.55 * f, -0.36 * f, 0.32 * f, 0.14 * f), E('rough', 2.0 * f, 0.58 * f, 5, 3, { top: true }), E('rough', 1.15 * f, 0.1 * f, 4, 2.5, { top: true })] }) },
    { id: 'p4t', par: 4, style: 'テクニカル', name: 'アイランドチェイン', desc: '島から島へ渡っていく。左の陸地を回れば安全だが遠回り。',
      build: (f) => ({ pin: { x: 3 * f, z: 0.4 }, stimp: 11, slope: { x: 0.004, z: 0.01 }, route: [{ x: 1.0 * f, z: 0 }, { x: 2.0 * f, z: 0.1 * f }],
        shapes: [E('green', 3 * f, 0, 7, 6),
          E('fairway', 1.0 * f, 0, 0.3 * f, 0.24 * f, { top: true }), E('fairway', 2.0 * f, 0.1 * f, 0.3 * f, 0.24 * f, { top: true }),
          Rc('water', 0.4 * f, 3 * f + 13, -0.55 * f, 0.55 * f), corridor('fairway', [[-3, 0], [0.4 * f - 1, 0]], 8),
          Rc('fairway', 0.4 * f, 3 * f + 6, -0.55 * f - 9, -0.55 * f - 1)] }) }
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


// ===== ボール認識:緑のマットの上に乗っている「丸くて緑でない物」を探す =====
// 色・穴・黒い点・写る大きさに左右されないよう、ボールそのものの色ではなく
// 「下側がマットの緑に接している円形の輪郭」を手がかりにする。
const DETECT = (() => {
  let cap = 0, G = null, bottom = null, tmp = null;
  function ensure(n, w) { if (cap < n) { cap = n; G = new Uint8Array(n); tmp = new Uint8Array(n); } if (!bottom || bottom.length < w) bottom = new Int32Array(w); }

  // 緑(マット)かどうか。暗い影の部分も、緑寄りならマットとみなす
  function isGreenPx(r, g, b) {
    const mx = r > b ? r : b;
    if (g < 48) return g >= r && g >= b - 2 && g > 10;
    return g > r * 1.12 && g > b * 1.05 && g - mx > 10;
  }
  function greenMask(d, W, H) {
    const N = W * H;
    for (let i = 0, p = 0; i < N; i++, p += 4) tmp[i] = isGreenPx(d[p], d[p + 1], d[p + 2]) ? 1 : 0;
    // 3x3の多数決でマットのきらめき(白い点)を消す
    for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
      let s = 0, n = 0;
      for (let dy = -1; dy <= 1; dy++) { const yy = y + dy; if (yy < 0 || yy >= H) continue; const o = yy * W; for (let dx = -1; dx <= 1; dx++) { const xx = x + dx; if (xx < 0 || xx >= W) continue; s += tmp[o + xx]; n++; } }
      G[y * W + x] = s * 2 > n ? 1 : 0;
    }
  }
  // 各列について、下から見て「マットの緑が続いたあと最初に緑でなくなる行」= マットに乗っている物の下端
  function bottomProfile(W, H) {
    for (let x = 0; x < W; x++) {
      let y = H - 1, run = 0, found = -1;
      // マットに入るまで(緑が4行続くまで)上がる
      for (; y >= 0; y--) { if (G[y * W + x]) { if (++run >= 4) break; } else run = 0; }
      if (y < 0) { bottom[x] = -2; continue; }        // この列にマットがない
      // マットのきらめきで止まらないよう、緑でない行が4行以上続いたら物の下端とする
      for (; y >= 0; y--) { if (!G[y * W + x]) { let k = 1; while (k < 4 && y - k >= 0 && !G[(y - k) * W + x]) k++; if (k >= 4 || y - k < 0) { found = y; break; } } }
      bottom[x] = found;                               // -1 ならマットが画面上端まで続いている
    }
  }
  // 最小二乗で円を当てる(Kasa法)
  function fitCircle(px, py) {
    const n = px.length; if (n < 5) return null;
    let mx = 0, my = 0; for (let i = 0; i < n; i++) { mx += px[i]; my += py[i]; } mx /= n; my /= n;
    let suu = 0, svv = 0, suv = 0, suuu = 0, svvv = 0, suvv = 0, svuu = 0;
    for (let i = 0; i < n; i++) { const u = px[i] - mx, v = py[i] - my; suu += u * u; svv += v * v; suv += u * v; suuu += u * u * u; svvv += v * v * v; suvv += u * v * v; svuu += v * u * u; }
    const det = suu * svv - suv * suv; if (Math.abs(det) < 1e-9) return null;
    const a = 0.5 * (suuu + suvv), b = 0.5 * (svvv + svuu);
    const uc = (a * svv - b * suv) / det, vc = (b * suu - a * suv) / det;
    const r = Math.sqrt(uc * uc + vc * vc + (suu + svv) / n);
    return { x: uc + mx, y: vc + my, r };
  }
  function residual(c, px, py) { let s = 0; for (let i = 0; i < px.length; i++) { const e = Math.hypot(px[i] - c.x, py[i] - c.y) - c.r; s += e * e; } return Math.sqrt(s / px.length); }

  function detect(d, W, H) {
    ensure(W * H, W); greenMask(d, W, H); bottomProfile(W, H);
    // 1列だけ飛び出た値(穴やきらめき)を、左右5列の中央値でならす
    const raw = bottom.slice(0, W);
    for (let x = 0; x < W; x++) { const v = []; for (let k = x - 2; k <= x + 2; k++) if (k >= 0 && k < W && raw[k] >= -1) v.push(raw[k]); if (v.length >= 3 && raw[x] >= -1) { v.sort((a, b) => a - b); bottom[x] = v[v.length >> 1]; } }
    // マットの上端(物が乗っていない所の下端)を、列ごとの値のなめらかな基準線として求める
    const base = new Float32Array(W), win = Math.max(8, Math.round(W * 0.12));
    for (let x = 0; x < W; x++) {
      const vals = [];
      for (let k = Math.max(0, x - win); k <= Math.min(W - 1, x + win); k++) if (bottom[k] >= -1) vals.push(bottom[k]);
      if (!vals.length) { base[x] = NaN; continue; }
      vals.sort((a, b) => a - b); base[x] = vals[Math.floor(vals.length * 0.25)];
    }
    // 基準線より下に垂れ下がっている区間 = マットの上に乗っている物
    const minDip = 2, out = [];
    let x = 0;
    while (x < W) {
      if (!(bottom[x] >= 0 && bottom[x] - base[x] >= minDip)) { x++; continue; }
      let x2 = x; while (x2 + 1 < W && bottom[x2 + 1] >= 0 && bottom[x2 + 1] - base[x2 + 1] >= minDip) x2++;
      const w = x2 - x + 1;
      if (w >= 5 && x > 0 && x2 < W - 1) {
        let px = [], py = [];
        for (let k = x; k <= x2; k++) { px.push(k); py.push(bottom[k]); }
        let c = fitCircle(px, py);
        // 外れ値(穴や影)を除いてもう一度
        if (c) { const e = px.map((q, i) => Math.abs(Math.hypot(q - c.x, py[i] - c.y) - c.r)); const lim = [...e].sort((a, b) => a - b)[Math.floor(e.length * 0.8)] + 0.5; const qx = [], qy = []; px.forEach((q, i) => { if (e[i] <= lim) { qx.push(q); qy.push(py[i]); } }); if (qx.length >= 5) { const c2 = fitCircle(qx, qy); if (c2) { c = c2; px = qx; py = qy; } } }
        if (c) {
          // 区間の両脇にあるマットの縁(物が乗っていない所)の高さ
          const side = []; for (let k = 1; k <= 6; k++) { if (x - k >= 0 && bottom[x - k] >= -1) side.push(bottom[x - k]); if (x2 + k < W && bottom[x2 + k] >= -1) side.push(bottom[x2 + k]); }
          const edge = side.length ? side.reduce((a, b) => a + b, 0) / side.length : -1;
          c.depth = (c.y - edge) / c.r;
          const cand = score(d, W, H, c, x, x2, px, py);
          if (cand) out.push(cand);
        }
      }
      x = x2 + 1;
    }
    out.sort((a, b) => b.score - a.score);
    return out[0] || null;
  }

  function score(d, W, H, c, xL, xR, px, py) {
    const r = c.r;
    if (!(r >= 3 && r <= Math.min(W, H) * 0.3)) return null;
    // ボールはマットの奥の縁より手前に乗っている(縁のくぼみや角を除く)
    if (c.depth < -0.3) return null;
    if (c.x < xL - r * 0.2 || c.x > xR + r * 0.2) return null;
    const chord = xR - xL + 1; if (chord < r * 1.1 || chord > r * 2.4) return null;
    const res = residual(c, px, py); if (res > Math.max(0.9, r * 0.1)) return null;
    // 区間の最下点は円の下端に近いこと(下半分の弧であること)
    const lowY = Math.max(...py); if (Math.abs(lowY - (c.y + r)) > Math.max(1.5, r * 0.15)) return null;
    // 円の内側はほぼ緑でない、円のすぐ下はマットの緑
    let inN = 0, inT = 0, ringG = 0, ringT = 0;
    const r2 = r * 0.82, x0 = Math.max(0, Math.floor(c.x - r)), x1 = Math.min(W - 1, Math.ceil(c.x + r));
    for (let y = Math.max(0, Math.floor(c.y - r)); y <= Math.min(H - 1, Math.ceil(c.y + r)); y++) for (let xx = x0; xx <= x1; xx++) { if (Math.hypot(xx - c.x, y - c.y) > r2) continue; inT++; if (!G[y * W + xx]) inN++; }
    for (let a = 25; a <= 155; a += 5) { const t = a * Math.PI / 180; for (const k of [1.18, 1.3, 1.45]) { const xx = Math.round(c.x + Math.cos(t) * r * k), y = Math.round(c.y + Math.sin(t) * r * k); if (xx < 0 || y < 0 || xx >= W || y >= H) continue; ringT++; if (G[y * W + xx]) ringG++; } }
    if (!inT || !ringT) return null;
    const fin = inN / inT, fring = ringG / ringT;
    if (fin < 0.6 || fring < 0.7) return null;
    // ボールらしい色(明るい白、または鮮やかな色)がある程度含まれること。クラブや指を除く
    let like = 0, tot = 0;
    for (let y = Math.max(0, Math.floor(c.y - r)); y <= Math.min(H - 1, Math.ceil(c.y + r)); y += 1) for (let xx = x0; xx <= x1; xx += 1) {
      if (Math.hypot(xx - c.x, y - c.y) > r * 0.8 || G[y * W + xx]) continue;
      const p = (y * W + xx) * 4, R = d[p], Gg = d[p + 1], B = d[p + 2];
      const mx = Math.max(R, Gg, B), mn = Math.min(R, Gg, B); tot++;
      if ((mn > 165 && mx - mn < 70) || mx - mn > 95) like++;
    }
    const flike = tot ? like / tot : 0;
    if (flike < 0.2) return null;
    const s = fin + fring + Math.min(1, chord / (r * 1.8)) - res / r;
    return { x: c.x, y: c.y, r, score: s + flike * 0.5, fin, fring, flike, depth: c.depth };
  }

  // ボールの2色(例:白とオレンジ)を覚える。打ったあとの追跡に使う
  function palette(d, W, H, b) {
    const pts = [];
    for (let y = Math.max(0, Math.floor(b.y - b.r)); y <= Math.min(H - 1, Math.ceil(b.y + b.r)); y++) for (let x = Math.max(0, Math.floor(b.x - b.r)); x <= Math.min(W - 1, Math.ceil(b.x + b.r)); x++) {
      if (Math.hypot(x - b.x, y - b.y) > b.r * 0.8 || G[y * W + x]) continue; const p = (y * W + x) * 4; pts.push([d[p], d[p + 1], d[p + 2]]);
    }
    if (pts.length < 4) return null;
    const lum = (q) => q[0] + q[1] + q[2];
    pts.sort((a, c) => lum(a) - lum(c));
    let c1 = pts[Math.floor(pts.length * 0.25)].slice(), c2 = pts[Math.floor(pts.length * 0.8)].slice();
    for (let it = 0; it < 6; it++) {
      const s1 = [0, 0, 0, 0], s2 = [0, 0, 0, 0];
      for (const q of pts) { const d1 = Math.abs(q[0] - c1[0]) + Math.abs(q[1] - c1[1]) + Math.abs(q[2] - c1[2]), d2 = Math.abs(q[0] - c2[0]) + Math.abs(q[1] - c2[1]) + Math.abs(q[2] - c2[2]); const s = d1 < d2 ? s1 : s2; s[0] += q[0]; s[1] += q[1]; s[2] += q[2]; s[3]++; }
      if (s1[3]) c1 = [s1[0] / s1[3], s1[1] / s1[3], s1[2] / s1[3]]; if (s2[3]) c2 = [s2[0] / s2[3], s2[1] / s2[3], s2[2] / s2[3]];
    }
    return [c1, c2];
  }
  function isGreenAt(i) { return G[i] === 1; }
  return { detect, palette, isGreenPx, isGreenAt };
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
/* 生成したイラスト。img/ に同名ファイルがあればそちらを優先する */
const ART_CDN = 'https://d8j0ntlcm91z4.cloudfront.net/user_3HJhNJAXEinI1BPtZI7pPcGddZP/hf_20260930_035851_';
const ART = { hero: 'f7f7c32d-d4e0-4a8f-9766-afc2f2b7cdd4', free: '9315a2f3-e9b5-4faa-9aa4-aa445136cbfc', course: '40d67dd4-2854-49a6-883d-7488665e4e7b',
  p2s: 'fb58a3a6-7a83-4f3d-ade8-4605a950cb68', p2t: '1ba9554f-54ca-48b5-96e0-0167c3e4f6d9', p3s: 'e9c16715-1d85-4718-b731-c10f0524dff9',
  p3t: '39cc3ca0-15fa-4eb1-b9b8-5da0cda21fe2', p4s: '3a78c7e0-3b1b-44b1-9287-4ccff75cd0a2', p4t: '9c388d3e-2d97-4b43-a67b-b15e95b4c754' };
const artCache = {};
function artUrl(key) {
  if (!artCache[key]) artCache[key] = new Promise(res => {
    const local = new Image();
    local.onload = () => res(`img/${key}.webp`);
    local.onerror = () => { const cdn = ART[key] ? `${ART_CDN}${ART[key]}_min.webp` : null; if (!cdn) return res(null); const im = new Image(); im.onload = () => res(cdn); im.onerror = () => res(null); im.src = cdn; };
    local.src = `img/${key}.webp`;
  });
  return artCache[key];
}
function paintArt(node, key) { artUrl(key).then(u => { if (u) node.style.backgroundImage = `url("${u}")`; }); }
function paintAll(root) { (root || document).querySelectorAll('[data-img]').forEach(n => paintArt(n, n.dataset.img)); }
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

/* ---------------- screen wake lock ---------------- */
const Power = (() => {
  let lock = null, want = false;
  async function keepAwake() { want = true; try { if ('wakeLock' in navigator && !lock) { lock = await navigator.wakeLock.request('screen'); lock.addEventListener('release', () => { lock = null; }); } } catch (e) { lock = null; } }
  document.addEventListener('visibilitychange', () => { if (!document.hidden && want) keepAwake(); });
  return { keepAwake };
})();

/* ---------------- sound (iPad) ---------------- */
const Sound = (() => {
  let ctx = null;
  const on = () => store.get('sound', true);
  document.addEventListener('pointerdown', () => { try { if (!ctx) ctx = new (window.AudioContext || window.webkitAudioContext)(); if (ctx.state === 'suspended') ctx.resume(); } catch (e) {} }, true);
  function tone(freq, t0, dur, vol) { const o = ctx.createOscillator(), g = ctx.createGain(); o.type = 'sine'; o.frequency.value = freq; g.gain.setValueAtTime(0, t0); g.gain.linearRampToValueAtTime(vol, t0 + 0.02); g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur); o.connect(g).connect(ctx.destination); o.start(t0); o.stop(t0 + dur + 0.05); }
  function ready() { if (!on() || !ctx) return; try { const t = ctx.currentTime; tone(880, t, 0.25, 0.18); tone(1318, t + 0.12, 0.35, 0.16); } catch (e) {} }
  function good() { if (!on() || !ctx) return; try { const t = ctx.currentTime; [784, 988, 1175, 1568].forEach((f, i) => tone(f, t + i * 0.09, 0.3, 0.12)); } catch (e) {} }
  function bad() { if (!on() || !ctx) return; try { const t = ctx.currentTime; tone(330, t, 0.3, 0.14); tone(262, t + 0.18, 0.4, 0.14); } catch (e) {} }
  return { ready, good, bad, on };
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
    const size = Math.round(212 * Math.min(3, devicePixelRatio || 1)); cv.width = cv.height = size;
    ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, size, size);
    if (!window.qrcode) return;
    const q = qrcode(0, 'M'); q.addData(text); q.make();
    const n = q.getModuleCount(), cell = Math.floor(size / (n + 8)), off = Math.floor((size - cell * n) / 2);
    ctx.fillStyle = '#000';
    for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (q.isDark(r, c)) ctx.fillRect(off + c * cell, off + r * cell, cell, cell);
  }
  function destroy() { if (peer) { try { peer.destroy(); } catch (e) {} } peer = null; conn = null; }

  /* ---- iPad ---- */
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
  function unpaired() { $('connectCard').classList.remove('paired'); $('pairNote').textContent = 'iPhoneのカメラアプリでこのQRコードを読み取ってください。'; setConn('wait', 'iPhoneを待っています'); App.setPaired(false); }
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
        toast('iPhoneとつながりました'); App.setPaired(true); App.sendInfo();
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
   CAMERA (iPhone): ball recognition (DETECT) + launch measurement
   ====================================================================== */
const Cam = (() => {
  const vid = $('vid'), ov = $('overlay'), octx = ov.getContext('2d');
  const proc = document.createElement('canvas'); const pctx = proc.getContext('2d', { willReadFrequently: true });
  const LONG = 640;                      // 解析する画像の長辺(px)
  let PW = 640, PH = 360, srcW = 0, srcH = 0;
  let stream = null, wake = null, running = false, frameN = 0;
  let state = 'off', lastSent = '', prev = null, info = { next: '', lie: '' }, issue = null;
  let ball = null, pal = null;           // 認識したボール {x,y,r} と、その2色
  let cand = null, stable = 0, readyFrac = 0, low = 0, needTap = false;
  let pts = [], trackStart = 0, lost = 0, cooldownUntil = 0, lastTrack = null, lastPresentT = 0;
  let lastTouch = Date.now(), lastActive = Date.now(), dark = false;
  const ftimes = [];
  const IDLE_DARK = 20000, IDLE_STOP = 10 * 60000, STABLE = 6;
  const S = { diam: store.get('diam', 42.7), rad: 1, factor: store.get('factor', 1), angOff: store.get('angOff', 0), spin: store.get('spin', 1), sens: store.get('sens', 1) };
  [['sDiam','oDiam','diam',v=>v.toFixed(1)+' mm'],['sRad','oRad','rad',v=>'×'+v.toFixed(2)],['sFactor','oFactor','factor',v=>'×'+v.toFixed(2)],
   ['sAngOff','oAngOff','angOff',v=>(v>0?'+':'')+v.toFixed(1)+'°'],['sSpin','oSpin','spin',v=>'×'+v.toFixed(2)],['sSens','oSens','sens',v=>'×'+v.toFixed(2)]]
  .forEach(([s,o,k,f]) => { const e=$(s); e.value=S[k]; $(o).textContent=f(+e.value); e.oninput=()=>{ S[k]=+e.value; $(o).textContent=f(+e.value); if(k!=='rad') store.set(k,+e.value); }; });

  const TEXT = {
    off: ['カメラを開始してください', '三脚のiPhoneを横向きにして、ボールを挟んで自分と向かい合う位置(約1m)に置きます'],
    search: ['ボールを置いてください', 'マットの上に置いたボールを自動で見つけます'],
    tap: ['ボールをタップして登録', '映像の中の、止まっているボールを1回タップしてください'],
    ready: ['打ってOK', ''],
    track: ['計測中…', ''],
    done: ['計測しました', 'iPadを見てください'],
    error: ['もう一度どうぞ', '']
  };
  // 計測できない置き方のときの案内。iPadには記号(portrait/near/far)だけを送る
  const ISSUE = {
    portrait: ['iPhoneを横向きにしてください', '縦向きだと、打ったボールがすぐ画面の外に出てしまい、球速を測れません'],
    near: ['カメラが近すぎます', 'ボールから1m前後離してください。今の距離だと、打った瞬間にボールが画面の外に出てしまいます'],
    far: ['カメラが遠すぎます', 'ボールが小さすぎて正確に測れません。もう少し近づけてください']
  };
  function infoLine() { if (!info.next && !info.lie) return ''; return [info.next ? `次は ${info.next}` : '', info.lie ? `${info.lie}から打つ` : ''].filter(Boolean).join('、'); }
  function setState(s, sub) {
    state = s;
    const t = s === 'adjust' ? ISSUE[issue] : (TEXT[s] || ['', '']);
    $('camStatus').dataset.state = s === 'adjust' ? 'error' : s;
    $('stateText').textContent = t[0];
    $('stateSub').textContent = sub || ((s === 'ready' || s === 'search') && infoLine()) || t[1];
    $('boText').textContent = t[0];
    pushStatus();
  }
  function pushStatus(force) {
    const st = state === 'ready' ? 'ready' : state === 'track' ? 'track' : state === 'off' ? 'off' : state === 'adjust' ? 'adjust' : 'wait';
    const key = st + (st === 'adjust' ? issue : '');
    if (!force && key === lastSent) return;
    lastSent = key; Net.send(st === 'adjust' ? { type: 'status', state: st, issue } : { type: 'status', state: st });
  }
  function onInfo(m) {
    info.next = typeof m.next === 'string' ? m.next.slice(0, 16) : '';
    info.lie = m.lie === 'マット' || m.lie === '絨毯' ? m.lie : '';
    if (state === 'ready' || state === 'search') setState(state);
  }
  function setButtons() { $('camStart').hidden = running; $('camStop').hidden = !running; }
  function setupProc() {
    srcW = vid.videoWidth; srcH = vid.videoHeight;
    const s = LONG / Math.max(srcW, srcH); PW = Math.round(srcW * s); PH = Math.round(srcH * s);
    proc.width = PW; proc.height = PH; prev = null;
    $('stage').style.aspectRatio = srcW + ' / ' + srcH;
  }

  async function start() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { toast('このブラウザではカメラを使えません(Safariで開いてください)'); return; }
    try {
      stream = await navigator.mediaDevices.getUserMedia({ audio: false, video: { facingMode: { ideal: 'environment' }, width: { ideal: 1280 }, height: { ideal: 720 }, frameRate: { ideal: 60, max: 60 } } });
    } catch (e) { setState('error', 'カメラの使用が許可されませんでした。設定 → Safari → カメラ を確認してください'); return; }
    vid.srcObject = stream;
    try { await vid.play(); } catch (e) {}
    await new Promise(r => { if (vid.videoWidth) r(); else vid.onloadedmetadata = () => r(); });
    setupProc();
    $('stageEmpty').hidden = true;
    try { if ('wakeLock' in navigator) wake = await navigator.wakeLock.request('screen'); } catch (e) { wake = null; }
    running = true; lastTouch = lastActive = Date.now(); setButtons();
    toSearch();
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

  // 省電力
  function setDark(on) { dark = on; $('blackout').hidden = !on; }
  document.addEventListener('pointerdown', () => { lastTouch = lastActive = Date.now(); if (dark) setDark(false); }, true);
  setInterval(() => {
    if (!running || role !== 'camera') return;
    const now = Date.now();
    if (now - lastActive > IDLE_STOP) { stop('10分間打たなかったので、カメラを休止しました。「カメラを開始」で再開します'); return; }
    if (!dark && !needTap && state !== 'adjust' && now - lastTouch > IDLE_DARK) setDark(true);
    if (state === 'ready' || state === 'adjust') pushStatus(true);
  }, 1000);

  function grab() { pctx.drawImage(vid, 0, 0, PW, PH); return pctx.getImageData(0, 0, PW, PH).data; }
  const L1 = (d, i, c) => Math.abs(d[i] - c[0]) + Math.abs(d[i + 1] - c[1]) + Math.abs(d[i + 2] - c[2]);
  const palDist = (d, i) => pal ? Math.min(L1(d, i, pal[0]), L1(d, i, pal[1])) : 999;
  const fps = () => ftimes.length > 10 ? (ftimes.length - 1) / (ftimes[ftimes.length - 1] - ftimes[0]) : 0;

  function toSearch() { ball = null; cand = null; stable = 0; low = 0; pts = []; lost = 0; issue = null; if (running) setState(needTap ? 'tap' : 'search'); }
  function setupIssue(b) {
    if (PH > PW) return 'portrait';
    const dia = 2 * b.r / PW;
    if (dia > 0.12) return 'near';
    if (dia < 0.018) return 'far';
    return null;
  }

  // 予備:タップで登録
  function measureAt(d, px, py) {
    px = Math.round(px); py = Math.round(py);
    let c = [0, 0, 0], n = 0;
    for (let y = py - 1; y <= py + 1; y++) for (let x = px - 1; x <= px + 1; x++) { if (x < 0 || y < 0 || x >= PW || y >= PH) continue; const i = (y * PW + x) * 4; c[0] += d[i]; c[1] += d[i + 1]; c[2] += d[i + 2]; n++; }
    c = c.map(v => v / Math.max(1, n));
    const seen = new Uint8Array(PW * PH), q = [py * PW + px]; seen[q[0]] = 1; let area = 0, sx = 0, sy = 0;
    while (q.length && area < 8000) {
      const k = q.pop(); const x = k % PW, y = (k / PW) | 0; area++; sx += x; sy += y;
      for (const [dx, dy] of [[1,0],[-1,0],[0,1],[0,-1]]) {
        const nx = x + dx, ny = y + dy; if (nx < 0 || ny < 0 || nx >= PW || ny >= PH || Math.hypot(nx - px, ny - py) > 60) continue;
        const kk = ny * PW + nx; if (seen[kk]) continue; seen[kk] = 1; const p = kk * 4; if (!DETECT.isGreenPx(d[p], d[p + 1], d[p + 2])) q.push(kk);
      }
    }
    return { x: sx / area, y: sy / area, r: clamp(Math.sqrt(area / Math.PI), 2, 60) };
  }
  function videoBox() {
    const W = ov.width, H = ov.height, va = (srcW || 16) / (srcH || 9), ca = W / H;
    if (va > ca) { const h = W / va; return { x: 0, y: (H - h) / 2, w: W, h }; }
    const w = H * va; return { x: (W - w) / 2, y: 0, w, h: H };
  }
  ov.addEventListener('click', (e) => {
    if (!running || !vid.videoWidth || !needTap) return;
    const rect = ov.getBoundingClientRect(), b = videoBox();
    const nx = ((e.clientX - rect.left) * devicePixelRatio - b.x) / b.w, ny = ((e.clientY - rect.top) * devicePixelRatio - b.y) / b.h;
    if (nx < 0 || nx > 1 || ny < 0 || ny > 1) return;
    const d = grab(); DETECT.detect(d, PW, PH);
    const m = measureAt(d, nx * PW, ny * PH);
    needTap = false; becomeReady(d, m); toast('ボールを登録しました');
  });
  $('retap').onclick = () => { if (!running) { toast('先に「カメラを開始」を押してください'); return; } needTap = true; setDark(false); toSearch(); $('stage').scrollIntoView({ behavior: 'smooth', block: 'center' }); };

  function params() { const br = Math.max(2, ball.r * S.rad); return { br, area: Math.PI * br * br, CT: 85 * S.sens, DT: 26 / S.sens }; }
  // ボールの下側(マットに重なる部分)で、ボールの色の画素がどれだけ残っているか
  function ballFrac(d) {
    let hit = 0, n = 0; const R = Math.max(1.5, ball.r * 0.8), CT = 85 * S.sens;
    for (let yy = Math.floor(ball.y - R * 0.4); yy <= ball.y + R; yy++) for (let xx = Math.floor(ball.x - R); xx <= ball.x + R; xx++) {
      if (xx < 0 || yy < 0 || xx >= PW || yy >= PH || Math.hypot(xx - ball.x, yy - ball.y) > R) continue;
      const p = (yy * PW + xx) * 4; n++;
      if (!DETECT.isGreenPx(d[p], d[p + 1], d[p + 2]) && palDist(d, p) < CT) hit++;
    }
    return n ? hit / n : 0;
  }
  function becomeReady(d, b) {
    ball = { x: b.x, y: b.y, r: b.r }; lastPresentT = performance.now() / 1000;
    pal = DETECT.palette(d, PW, PH, ball) || pal;
    readyFrac = Math.max(0.2, ballFrac(d)); low = 0;
    // 計測はできるが、もっと良くなる置き方があれば一言添える
    const tip = ball.y < PH * 0.55 ? 'ボールが画面の下の方に写るようにすると、高く上がる球も追いやすくなります' : '';
    setState('ready', tip || undefined);
  }
  function trackStep(d, t, P) {
    let pred, wx0, wx1, wy0, wy1;
    if (!pts.length) { pred = [ball.x, ball.y]; wx0 = ball.x - 16 * P.br; wx1 = ball.x + 16 * P.br; wy0 = ball.y - 16 * P.br; wy1 = ball.y + 1.5 * P.br; }
    else {
      const L = pts[pts.length - 1]; let vx = 0, vy = 0;
      // 1点目しかないときは、止まっていた位置からの動きで速さを見積もる
      const Q = pts.length >= 2 ? pts[pts.length - 2] : { x: ball.x, y: ball.y, t: lastPresentT };
      const dt = Math.max(1 / 240, L.t - Q.t); vx = (L.x - Q.x) / dt; vy = (L.y - Q.y) / dt;
      const dtn = t - L.t; pred = [L.x + vx * dtn, L.y + vy * dtn];
      const rad = Math.max(6 * P.br, (pts.length >= 2 ? 1.8 : 2.4) * Math.hypot(vx, vy) * dtn);
      wx0 = pred[0] - rad; wx1 = pred[0] + rad; wy0 = pred[1] - rad; wy1 = Math.min(pred[1] + rad, ball.y + 1.5 * P.br);
    }
    wx0 = Math.max(0, Math.floor(wx0)); wx1 = Math.min(PW - 1, Math.ceil(wx1)); wy0 = Math.max(0, Math.floor(wy0)); wy1 = Math.min(PH - 1, Math.ceil(wy1));
    const W = wx1 - wx0 + 1, H = wy1 - wy0 + 1; if (W <= 0 || H <= 0 || !prev) { lost++; return lost >= 4; }
    const mask = new Uint8Array(W * H);
    for (let y = wy0; y <= wy1; y++) for (let x = wx0; x <= wx1; x++) {
      if (!pts.length && Math.hypot(x - ball.x, y - ball.y) < P.br) continue;
      const i = (y * PW + x) * 4;
      const mv = Math.abs(d[i] - prev[i]) + Math.abs(d[i + 1] - prev[i + 1]) + Math.abs(d[i + 2] - prev[i + 2]);
      if (mv > P.DT && palDist(d, i) < P.CT * 1.25 && !DETECT.isGreenPx(d[i], d[i + 1], d[i + 2])) mask[(y - wy0) * W + (x - wx0)] = 1;
    }
    const seen = new Uint8Array(W * H); let best = null;
    for (let k0 = 0; k0 < W * H; k0++) {
      if (!mask[k0] || seen[k0]) continue;
      const q = [k0]; seen[k0] = 1; let n = 0, sx = 0, sy = 0;
      while (q.length) { const k = q.pop(); const x = k % W, y = (k / W) | 0; n++; sx += x; sy += y;
        if (x > 0 && mask[k - 1] && !seen[k - 1]) { seen[k - 1] = 1; q.push(k - 1); }
        if (x < W - 1 && mask[k + 1] && !seen[k + 1]) { seen[k + 1] = 1; q.push(k + 1); }
        if (y > 0 && mask[k - W] && !seen[k - W]) { seen[k - W] = 1; q.push(k - W); }
        if (y < H - 1 && mask[k + W] && !seen[k + W]) { seen[k + W] = 1; q.push(k + W); } }
      if (n < Math.max(3, P.area * 0.12) || n > P.area * 9) continue;
      const cx = sx / n + wx0, cy = sy / n + wy0, dist = Math.hypot(cx - pred[0], cy - pred[1]);
      if (!best || dist < best.dist) best = { x: cx, y: cy, dist };
    }
    if (best) { pts.push({ t, x: best.x, y: best.y }); lost = 0; }
    else if (pts.length) lost++;
    else lost++;
    const edge = best && (best.x < 2 || best.x > PW - 3 || best.y < 2);
    return pts.length >= 10 || lost >= 4 || edge || (t - trackStart) > 0.5;
  }
  function finishTrack() {
    const P = params();
    lastTrack = pts.slice(); lastActive = Date.now();
    const f = Math.round(fps());
    if (pts.length < 2) {
      const tip = f && f < 45 ? `今は約${f}fpsで撮影されています。` : '';
      setState('error', `飛んでいくボールを追えませんでした。${tip}ボールが画面の下の方に写るように置くと、上がっていく球を長く追えます`);
      cooldownUntil = performance.now() + 2000; return;
    }
    const ppm = (2 * P.br) / (S.diam / 1000), g = 9.81 * ppm, T0 = pts[0].t;
    const fit = (xs, ys) => { const n = xs.length, mx = xs.reduce((a, b) => a + b) / n, my = ys.reduce((a, b) => a + b) / n; let a = 0, b = 0; for (let i = 0; i < n; i++) { a += (xs[i] - mx) * (ys[i] - my); b += (xs[i] - mx) ** 2; } return b ? a / b : 0; };
    const use = pts.slice(0, 8), ts = use.map(p => p.t - T0);
    const vx = fit(ts, use.map(p => p.x)), vy = fit(ts, use.map((p, i) => p.y - 0.5 * g * ts[i] * ts[i]));
    const mSpeed = Math.hypot(vx, vy) / ppm, mAngle = Math.atan2(-vy, Math.abs(vx)) * 180 / Math.PI;
    if (!(mSpeed > 0.5 && mSpeed < 60) || mAngle < -10 || mAngle > 80) { setState('error', `計測値が不自然でした(${mSpeed.toFixed(1)}m/s、${mAngle.toFixed(0)}°)。もう一度どうぞ`); cooldownUntil = performance.now() + 2000; return; }
    const speed = clamp(mSpeed * S.factor, 1, 40), angle = clamp(mAngle + S.angOff, 0, 70);
    const spin = clamp(Math.round(290 * speed * (0.75 + angle / 120) * S.spin / 50) * 50, 500, 11000);
    const shot = { type: 'shot', id: Date.now().toString(36) + Math.random().toString(36).slice(2, 6), speed: +speed.toFixed(2), angle: +angle.toFixed(1), dir: 0, spin };
    $('cSpeed').textContent = speed.toFixed(1) + ' m/s'; $('cAngle').textContent = angle.toFixed(1) + '°'; $('cSpin').textContent = spin + ' rpm';
    $('cMeta').textContent = `練習ボールの計測値 ${mSpeed.toFixed(1)} m/s、${mAngle.toFixed(1)}°。追跡 ${pts.length} コマ、約${f}fps`;
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
    const p = ball || cand;
    if (p) {
      octx.strokeStyle = state === 'ready' ? '#1f9d55' : state === 'adjust' ? '#d63a2a' : '#ffd24a'; octx.lineWidth = 3 * dpr;
      octx.beginPath(); octx.arc(b.x + p.x * sx, b.y + p.y * sy, p.r * sx + 5 * dpr, 0, Math.PI * 2); octx.stroke();
    }
    const tr = state === 'track' ? pts : (performance.now() < cooldownUntil ? lastTrack : null);
    if (tr) { octx.fillStyle = '#d63a2a'; tr.forEach(q => { octx.beginPath(); octx.arc(b.x + q.x * sx, b.y + q.y * sy, 5 * dpr, 0, Math.PI * 2); octx.fill(); }); }
    if (needTap) {
      octx.fillStyle = 'rgba(0,0,0,.6)'; octx.fillRect(0, H - 44 * dpr, W, 44 * dpr);
      octx.fillStyle = '#fff'; octx.font = `${15 * dpr}px sans-serif`; octx.textAlign = 'center';
      octx.fillText('止まっているボールをタップしてください', W / 2, H - 16 * dpr);
    }
  }

  function frame(t) {
    frameN++;
    ftimes.push(t); if (ftimes.length > 30) ftimes.shift();
    if (vid.videoWidth !== srcW || vid.videoHeight !== srcH) { setupProc(); toSearch(); }   // 向きが変わった
    const busy = state === 'ready' || state === 'track';
    // ボールを探している間は2コマに1回だけ解析して、発熱を抑える
    if (!busy && frameN % 2 !== 0) return;
    const d = grab();
    if (state === 'track') { if (trackStep(d, t, params())) finishTrack(); }
    else if (performance.now() < cooldownUntil) { /* 結果表示中 */ }
    else if (state === 'ready') {
      const f = ballFrac(d);
      // ボールの色が消えたコマ=打った瞬間。そのコマから追跡を始める
      if (f < readyFrac * 0.4) { setState('track'); trackStart = t; pts = []; lost = 0; if (trackStep(d, t, params())) finishTrack(); }
      else lastPresentT = t;
    } else if (!needTap) {
      const c = DETECT.detect(d, PW, PH);
      if (c && cand && Math.hypot(c.x - cand.x, c.y - cand.y) < Math.max(1.2, 0.3 * c.r) && Math.abs(c.r - cand.r) < 0.25 * cand.r) stable++;
      else stable = 0;
      cand = c;
      if (!c) { if (state !== 'search') toSearch(); }
      else if (stable >= STABLE) {
        issue = setupIssue(c);
        if (issue) { if (state !== 'adjust' || lastSent !== 'adjust' + issue) setState('adjust'); }
        else becomeReady(d, c);
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
   WORLD (iPad): 3D course. Renders only when something moves.
   ====================================================================== */
const World = (() => {
  let renderer, scene, cam, root, ballM, shadow, aimGroup, markerGroup, trailGroup, ballsGroup;
  let course = null, anim = null, dirty = true, inited = false, viewMode = 'follow', tapCb = null, progressCb = null;
  let focus = { x: 0, z: 0 }, heading = 0, reach = 30;
  const camPos = new THREE.Vector3(-4, 2, 0), camLook = new THREE.Vector3(10, 0, 0), curLook = new THREE.Vector3(10, 0, 0);
  let seed = 1; const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
  const rand = (a, b) => a + rnd() * (b - a);
  function texCanvas(w, h, draw, rep) { const c = document.createElement('canvas'); c.width = w; c.height = h; draw(c.getContext('2d'), w, h); const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.repeat.set(rep, rep); t.anisotropy = 4; return t; }
  function grass(ctx, w, h, base, amp, n, blade) {
    ctx.fillStyle = base; ctx.fillRect(0, 0, w, h);
    for (let i = 0; i < n; i++) { const a = Math.random() * amp; ctx.fillStyle = Math.random() < .55 ? `rgba(0,0,0,${a})` : `rgba(255,255,230,${a * .5})`; const x = Math.random() * w, y = Math.random() * h; if (blade) ctx.fillRect(x, y, 1, 2 + Math.random() * 3); else ctx.fillRect(x, y, 2, 2); }
  }
  let TEX = null;
  function textures() {
    if (TEX) return TEX;
    TEX = {
      rough: texCanvas(256, 256, (c, w, h) => grass(c, w, h, '#2f6a2b', .22, 9000, true), 0.25),
      fairway: texCanvas(256, 256, (c, w, h) => { for (let i = 0; i < 4; i++) { c.fillStyle = i % 2 ? '#4f9c40' : '#468f38'; c.fillRect(0, i * h / 4, w, h / 4); } for (let i = 0; i < 4000; i++) { c.fillStyle = `rgba(0,0,0,${Math.random() * .07})`; c.fillRect(Math.random() * w, Math.random() * h, 1.5, 1.5); } }, 1 / 12),
      green: texCanvas(256, 256, (c, w, h) => { for (let i = 0; i < 8; i++) { c.fillStyle = i % 2 ? '#5fb64e' : '#57ab47'; c.fillRect(i * w / 8, 0, w / 8, h); } for (let i = 0; i < 3000; i++) { c.fillStyle = `rgba(0,0,0,${Math.random() * .045})`; c.fillRect(Math.random() * w, Math.random() * h, 1, 1); } }, 1 / 8),
      fringe: texCanvas(128, 128, (c, w, h) => grass(c, w, h, '#478e3c', .12, 1800), 0.5),
      water: texCanvas(256, 256, (c, w, h) => { c.fillStyle = '#2b78ad'; c.fillRect(0, 0, w, h); for (let i = 0; i < 260; i++) { c.strokeStyle = `rgba(255,255,255,${0.04 + Math.random() * 0.08})`; c.lineWidth = 1; const x = Math.random() * w, y = Math.random() * h; c.beginPath(); c.moveTo(x, y); c.quadraticCurveTo(x + 8, y - 2, x + 16, y); c.stroke(); } }, 1 / 10),
      rock: texCanvas(128, 128, (c, w, h) => grass(c, w, h, '#6a5642', .25, 2500), 0.25)
    };
    return TEX;
  }
  function init() {
    if (inited) return; inited = true;
    const world = $('world');
    renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: 'low-power' });
    renderer.setPixelRatio(Math.min(1.5, devicePixelRatio)); renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    world.prepend(renderer.domElement);
    scene = new THREE.Scene(); scene.fog = new THREE.Fog('#dfe6dc', 80, 260);
    cam = new THREE.PerspectiveCamera(48, 16 / 10, 0.05, 600);
    // sky dome with vertical gradient
    const skyGeo = new THREE.SphereGeometry(500, 32, 16); const cols = []; const pos = skyGeo.attributes.position;
    const top = new THREE.Color('#5c9bd1'), hor = new THREE.Color('#f3e2c4'), tmp = new THREE.Color();
    for (let i = 0; i < pos.count; i++) { const y = pos.getY(i) / 500; tmp.copy(hor).lerp(top, clamp(y * 1.6, 0, 1)); cols.push(tmp.r, tmp.g, tmp.b); }
    skyGeo.setAttribute('color', new THREE.Float32BufferAttribute(cols, 3));
    scene.add(new THREE.Mesh(skyGeo, new THREE.MeshBasicMaterial({ vertexColors: true, side: THREE.BackSide, fog: false })));
    scene.add(new THREE.HemisphereLight('#fff6e6', '#3a5230', 0.7));
    // 朝日と雲
    const glow = texCanvas(128, 128, (c2, w, h) => { const g2 = c2.createRadialGradient(64, 64, 4, 64, 64, 64); g2.addColorStop(0, 'rgba(255,248,225,1)'); g2.addColorStop(0.25, 'rgba(255,226,170,.8)'); g2.addColorStop(1, 'rgba(255,210,150,0)'); c2.fillStyle = g2; c2.fillRect(0, 0, w, h); }, 1);
    const sunS = new THREE.Sprite(new THREE.SpriteMaterial({ map: glow, fog: false, depthWrite: false, transparent: true })); sunS.scale.set(120, 120, 1); sunS.position.set(420, 70, 160); scene.add(sunS);
    const cloudT = texCanvas(256, 128, (c2, w, h) => { for (let i = 0; i < 18; i++) { const x = 40 + Math.random() * 176, y = 50 + Math.random() * 40, r = 18 + Math.random() * 26; const g2 = c2.createRadialGradient(x, y, 2, x, y, r); g2.addColorStop(0, 'rgba(255,255,255,.9)'); g2.addColorStop(1, 'rgba(255,255,255,0)'); c2.fillStyle = g2; c2.fillRect(0, 0, w, h); } }, 1);
    for (let i = 0; i < 9; i++) { const cl = new THREE.Sprite(new THREE.SpriteMaterial({ map: cloudT, fog: false, depthWrite: false, transparent: true, opacity: 0.85 })); const a2 = -0.9 + i * 0.22 + rand(-.05, .05); cl.scale.set(rand(90, 150), rand(30, 50), 1); cl.position.set(60 + Math.cos(a2) * 380, rand(60, 120), Math.sin(a2) * 380); scene.add(cl); }
    const sun = new THREE.DirectionalLight('#ffe9c4', 0.9); sun.position.set(-40, 45, 30); sun.castShadow = true;
    sun.shadow.mapSize.set(2048, 2048); Object.assign(sun.shadow.camera, { left: -90, right: 90, top: 90, bottom: -90, far: 200 });
    sun.target.position.set(45, 0, 0); scene.add(sun, sun.target);
    // distant hills
    const hillMat = new THREE.MeshLambertMaterial({ color: '#7d9f86', flatShading: true });
    for (let i = 0; i < 26; i++) { const a = (i / 26) * Math.PI * 2 + rand(-.1, .1), r = rand(230, 300); const h = new THREE.Mesh(new THREE.SphereGeometry(1, 10, 6), hillMat); h.scale.set(rand(40, 80), rand(14, 34), rand(40, 80)); h.position.set(60 + Math.cos(a) * r, -4, Math.sin(a) * r); scene.add(h); }
    ballM = new THREE.Mesh(new THREE.SphereGeometry(0.065, 24, 16), new THREE.MeshPhongMaterial({ color: '#ffffff', shininess: 60 })); ballM.castShadow = true; scene.add(ballM);
    shadow = new THREE.Mesh(new THREE.CircleGeometry(0.075, 16), new THREE.MeshBasicMaterial({ color: '#000', transparent: true, opacity: .28, depthWrite: false })); shadow.rotation.x = -Math.PI / 2; shadow.renderOrder = 60; scene.add(shadow);
    aimGroup = new THREE.Group(); markerGroup = new THREE.Group(); trailGroup = new THREE.Group(); ballsGroup = new THREE.Group();
    scene.add(aimGroup, markerGroup, trailGroup, ballsGroup);
    new ResizeObserver(resize).observe(world);
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
  // 地面の層は重なり順で描き分け、奥行きのちらつきを防ぐ
  function flat(shape, y, mat) { const m = new THREE.Mesh(new THREE.ShapeGeometry(shape, 64), mat); m.rotation.x = -Math.PI / 2; m.position.y = y; m.receiveShadow = true; if (y >= 0) { mat.depthWrite = false; m.renderOrder = Math.round(y * 1000); } return m; }
  function decal(m, order) { m.material.depthWrite = false; m.renderOrder = order; return m; }
  function bounds(c) {
    let x0 = -10, x1 = c.pin.x + 15, z0 = -20, z1 = 20;
    c.shapes.forEach(s => { if (s.kind === 'ellipse') { x0 = Math.min(x0, s.cx - s.rx); x1 = Math.max(x1, s.cx + s.rx); z0 = Math.min(z0, s.cz - s.rz); z1 = Math.max(z1, s.cz + s.rz); } else if (s.kind === 'rect') { x0 = Math.min(x0, s.x0); x1 = Math.max(x1, s.x1); z0 = Math.min(z0, s.z0); z1 = Math.max(z1, s.z1); } else s.pts.forEach(([x, z]) => { x0 = Math.min(x0, x); x1 = Math.max(x1, x); z0 = Math.min(z0, z); z1 = Math.max(z1, z); }); });
    return { x0, x1, z0, z1 };
  }
  function load(c) {
    init(); course = c; seed = 7;
    if (root) { scene.remove(root); root.traverse(o => { if (o.geometry) o.geometry.dispose(); }); }
    root = new THREE.Group();
    const T = textures();
    const lam = (opt) => new THREE.MeshLambertMaterial(opt);
    const g = new THREE.Shape(); g.moveTo(-200, 300); g.lineTo(360, 300); g.lineTo(360, -300); g.lineTo(-200, -300); g.closePath();
    const chasms = c.shapes.filter(s => s.type === 'chasm');
    chasms.forEach(s => g.holes.push(shapeOf(s)));
    root.add(flat(g, 0, lam({ map: T.rough })));
    if (c.allGreen) root.add(flat(shapeOf({ kind: 'rect', x0: -8, x1: c.pin.x + 24, z0: -30, z1: 30 }), 0.004, lam({ map: T.green })));
    c.shapes.filter(s => s.type === 'fairway' && !s.top).forEach(s => { root.add(flat(shapeOf(s, 0.8), 0.006, lam({ map: T.fringe }))); root.add(flat(shapeOf(s), 0.008, lam({ map: T.fairway }))); });
    c.shapes.filter(s => s.type === 'water').forEach(s => {
      root.add(flat(shapeOf(s, 0.9), 0.012, lam({ color: '#b8a57a' })));
      root.add(flat(shapeOf(s), 0.016, new THREE.MeshPhongMaterial({ map: T.water, shininess: 90, specular: '#cfeaff' })));
    });
    c.shapes.filter(s => s.top && s.type === 'rough').forEach(s => root.add(flat(shapeOf(s), 0.02, lam({ map: T.rough, color: '#c8d8b8' }))));
    c.shapes.filter(s => s.top && s.type === 'fairway').forEach(s => { root.add(flat(shapeOf(s, 0.6), 0.022, lam({ map: T.fringe }))); root.add(flat(shapeOf(s), 0.024, lam({ map: T.fairway }))); });
    const greens = c.shapes.filter(s => s.type === 'green');
    greens.forEach(s => {
      const inWater = c.shapes.some(w => w.type === 'water' && SIM.inShape(w, s.cx, s.cz));
      if (!inWater) root.add(flat(shapeOf(s, 1.2), 0.03, lam({ map: T.fringe })));
      root.add(flat(shapeOf(s), 0.036, lam({ map: T.green })));
    });
    chasms.forEach(s => {
      const depth = 9, rock = lam({ map: T.rock, side: THREE.DoubleSide });
      const bottom = flat(shapeOf(s), -depth, lam({ color: '#15110d' })); bottom.renderOrder = -2; root.add(bottom);
      const w = s.x1 - s.x0, d = s.z1 - s.z0;
      [[s.x0 + w / 2, s.z0, w, 0], [s.x0 + w / 2, s.z1, w, 0], [s.x0, s.z0 + d / 2, d, Math.PI / 2], [s.x1, s.z0 + d / 2, d, Math.PI / 2]].forEach(([x, z, len, ry]) => {
        const wall = new THREE.Mesh(new THREE.PlaneGeometry(len, depth), rock); wall.position.set(x, -depth / 2, z); wall.rotation.y = ry; wall.renderOrder = -1; root.add(wall);
      });
      // 崖の中の浮島(岩の柱)
      c.shapes.filter(t => t.island).forEach(t => { const p = new THREE.Mesh(new THREE.CylinderGeometry(1, 0.8, depth, 24), lam({ map: T.rock })); p.scale.set(t.rx, 1, t.rz); p.position.set(t.cx, -depth / 2 - 0.02, t.cz); p.renderOrder = -1; root.add(p); });
    });
    // trees (instanced) outside play areas
    const bb = bounds(c), spots = [];
    for (let i = 0; i < 700 && spots.length < 120; i++) {
      const x = rand(bb.x0 - 30, bb.x1 + 30), z = rand(bb.z0 - 30, bb.z1 + 30);
      let ok = true;
      for (const [dx, dz] of [[0, 0], [9, 0], [-9, 0], [0, 9], [0, -9], [6, 6], [-6, -6], [6, -6], [-6, 6]]) { const zn = SIM.zoneAt(c, x + dx, z + dz); if (zn !== 'rough' || (c.allGreen && Math.abs(z) < 34 && x < c.pin.x + 28)) { ok = false; break; } }
      if (ok && Math.hypot(x, z) > 10) spots.push([x, z, rand(0.8, 1.5)]);
    }
    const coneG = new THREE.ConeGeometry(2.2, 6.5, 7), trunkG = new THREE.CylinderGeometry(0.25, 0.35, 2, 6);
    const leaves = new THREE.InstancedMesh(coneG, lam({ color: '#27572b', flatShading: true }), spots.length * 2);
    const trunks = new THREE.InstancedMesh(trunkG, lam({ color: '#5a4030' }), spots.length);
    const m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), sc = new THREE.Vector3(), p = new THREE.Vector3();
    spots.forEach(([x, z, s], i) => {
      sc.set(s, s, s); p.set(x, 1 * s, z); m4.compose(p, q, sc); trunks.setMatrixAt(i, m4);
      p.set(x, 4.2 * s, z); m4.compose(p, q, sc); leaves.setMatrixAt(i * 2, m4);
      sc.set(s * 0.75, s * 0.8, s * 0.75); p.set(x, 7 * s, z); m4.compose(p, q, sc); leaves.setMatrixAt(i * 2 + 1, m4);
    });
    leaves.castShadow = true; trunks.castShadow = true; root.add(leaves, trunks);
    // cup, flag, 2m OK circle
    const P = c.pin;
    const okFill = new THREE.Mesh(new THREE.CircleGeometry(2, 72), new THREE.MeshBasicMaterial({ color: '#fff3a0', transparent: true, opacity: .2 }));
    okFill.rotation.x = -Math.PI / 2; okFill.position.set(P.x, 0.042, P.z); root.add(decal(okFill, 42));
    const okRing = new THREE.Mesh(new THREE.RingGeometry(1.92, 2.08, 96), new THREE.MeshBasicMaterial({ color: '#ffffff', transparent: true, opacity: .95, side: THREE.DoubleSide }));
    okRing.rotation.x = -Math.PI / 2; okRing.position.set(P.x, 0.046, P.z); root.add(decal(okRing, 46));
    const cup = new THREE.Mesh(new THREE.CircleGeometry(0.054, 24), new THREE.MeshBasicMaterial({ color: '#0c0c0c' })); cup.rotation.x = -Math.PI / 2; cup.position.set(P.x, 0.05, P.z); root.add(decal(cup, 50));
    const pole = new THREE.Mesh(new THREE.CylinderGeometry(0.014, 0.014, 2.2, 8), lam({ color: '#f4f4f4' })); pole.position.set(P.x, 1.1, P.z); pole.castShadow = true; root.add(pole);
    const flagG = new THREE.PlaneGeometry(0.6, 0.38, 6, 1); const fp = flagG.attributes.position; for (let i = 0; i < fp.count; i++) { const x = fp.getX(i) + 0.3; fp.setZ(i, Math.sin(x * 6) * 0.05 * x); }
    const flag = new THREE.Mesh(flagG, lam({ color: '#e0412a', side: THREE.DoubleSide })); flag.position.set(P.x, 1.98, P.z + 0.3); flag.rotation.y = Math.PI / 2; flag.castShadow = true; root.add(flag);
    // tee mat
    const tee = new THREE.Mesh(new THREE.BoxGeometry(1.6, 0.04, 1.6), lam({ color: '#1d4a2a' })); tee.position.set(c.tee.x, 0.02, c.tee.z); tee.receiveShadow = true; root.add(tee);
    scene.add(root);
    markerGroup.clear(); clearTrails(); ballsGroup.clear(); aimGroup.clear();
    placeBall(c.tee.x, 0, c.tee.z);
    dirty = true;
  }
  function placeBall(x, y, z) { ballM.position.set(x, y + 0.065, z); shadow.position.set(x, 0.056, z); shadow.visible = y > -0.02; dirty = true; }
  function clearTrails() { while (trailGroup.children.length) { const o = trailGroup.children.pop(); o.geometry.dispose(); } }
  function setBalls(list) {
    ballsGroup.clear();
    list.forEach(b => {
      const m = new THREE.Mesh(new THREE.SphereGeometry(0.1, 16, 10), new THREE.MeshLambertMaterial({ color: b.color })); m.position.set(b.x, 0.1, b.z); ballsGroup.add(m);
      const ring = new THREE.Mesh(new THREE.RingGeometry(0.22, 0.32, 24), new THREE.MeshBasicMaterial({ color: b.color, side: THREE.DoubleSide, transparent: true })); ring.rotation.x = -Math.PI / 2; ring.position.set(b.x, 0.057, b.z); ballsGroup.add(decal(ring, 57));
    });
    dirty = true;
  }
  function addMarker(x, z, color) {
    while (markerGroup.children.length >= 24) markerGroup.remove(markerGroup.children[0]);
    const m = new THREE.Mesh(new THREE.SphereGeometry(0.07, 12, 8), new THREE.MeshLambertMaterial({ color })); m.position.set(x, 0.07, z); markerGroup.add(m);
    dirty = true;
  }
  function setAim(pos, hd, reachM) {
    focus = { x: pos.x, z: pos.z }; heading = hd; reach = reachM;
    aimGroup.clear();
    const dx = Math.cos(hd), dz = Math.sin(hd);
    const geo = new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(pos.x + dx * 0.4, 0.07, pos.z + dz * 0.4), new THREE.Vector3(pos.x + dx * reachM, 0.07, pos.z + dz * reachM)]);
    const line = new THREE.Line(geo, new THREE.LineDashedMaterial({ color: '#ffe38a', dashSize: 0.9, gapSize: 0.6 })); line.computeLineDistances(); aimGroup.add(decal(line, 70));
    const arc = new THREE.Mesh(new THREE.RingGeometry(reachM - 0.22, reachM + 0.22, 48, 1, -hd - 0.5, 1.0), new THREE.MeshBasicMaterial({ color: '#ff8a5c', transparent: true, opacity: .9, side: THREE.DoubleSide }));
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
      const h = d * 1.1 + 6;
      camPos.set(cx - dx * h * 0.3, h, cz - dz * h * 0.3); camLook.set(cx, 0, cz);
    } else {
      const L = Math.min(reach, Math.max(8, Math.hypot(course.pin.x - focus.x, course.pin.z - focus.z))) * 0.75;
      camPos.set(focus.x - dx * 4.8, 2.0, focus.z - dz * 4.8); camLook.set(focus.x + dx * L, 0, focus.z + dz * L);
    }
    dirty = true;
  }
  function setView(v) { viewMode = v; $('vFollow').setAttribute('aria-pressed', v === 'follow'); $('vTop').setAttribute('aria-pressed', v === 'top'); if (!anim) idleCamera(); }
  $('vFollow').onclick = () => setView('follow'); $('vTop').onclick = () => setView('top');
  // 弾道はチューブで描き、飛んだ分だけ見せる
  function play(res, color, onDone) {
    hideAim();
    const src = res.pts, step = Math.max(1, Math.floor(src.length / 240));
    const vs = []; for (let i = 0; i < src.length; i += step) vs.push(new THREE.Vector3(src[i][1], Math.max(src[i][2], -9) + 0.05, src[i][3]));
    const last = src[src.length - 1]; vs.push(new THREE.Vector3(last[1], last[2] + 0.05, last[3]));
    if (vs.length < 2) vs.push(vs[0].clone().add(new THREE.Vector3(0.01, 0, 0)));
    const curve = new THREE.CatmullRomCurve3(vs), seg = vs.length * 2, rad = 6;
    const tube = new THREE.Mesh(new THREE.TubeGeometry(curve, seg, 0.035, rad, false), new THREE.MeshBasicMaterial({ color, transparent: true, opacity: .95 }));
    tube.geometry.setDrawRange(0, 0); trailGroup.add(tube);
    while (trailGroup.children.length > 8) { const o = trailGroup.children.shift(); trailGroup.remove(o); o.geometry.dispose(); }
    // 着弾点の輪
    const cr = res.carryPt;
    if (cr && !res.hazardAtLanding) { const ring = new THREE.Mesh(new THREE.RingGeometry(0.28, 0.4, 32), new THREE.MeshBasicMaterial({ color, transparent: true, opacity: 0, side: THREE.DoubleSide })); ring.rotation.x = -Math.PI / 2; ring.position.set(cr.x, 0.058, cr.z); trailGroup.add(decal(ring, 58)); res._ring = ring; }
    anim = { res, tube, seg, rad, start: performance.now(), onDone, total: src.length };
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
      const frac = clamp((i + f) / Math.max(1, pts.length - 1), 0, 1);
      anim.tube.geometry.setDrawRange(0, Math.floor(frac * anim.seg) * anim.rad * 6);
      if (anim.res._ring && t >= anim.res.carryT) anim.res._ring.material.opacity = 0.9;
      if (progressCb) progressCb(anim.res, frac);
      if (viewMode === 'follow') { const s = pts[0], e = pts[Math.min(i + 3, pts.length - 1)]; let dx = e[1] - s[1], dz = e[3] - s[3]; const L = Math.hypot(dx, dz) || 1; dx /= L; dz /= L; if (L < 0.5) { dx = Math.cos(heading); dz = Math.sin(heading); } camPos.set(x - dx * 5.5, Math.max(1.6, y + 1.8), z - dz * 5.5); camLook.set(x + dx * 2, Math.max(0, y) * 0.6, z + dz * 2); }
      if (t >= anim.res.duration + 0.05) {
        // 飛び終わった弾道は細い線に置き換えて、次の打席の邪魔にしない
        const tube = anim.tube, color = tube.material.color.clone();
        trailGroup.remove(tube); tube.geometry.dispose();
        const line = new THREE.Line(new THREE.BufferGeometry().setFromPoints(anim.res.pts.map(q => new THREE.Vector3(q[1], Math.max(q[2], -9) + 0.05, q[3]))), new THREE.LineBasicMaterial({ color, transparent: true, opacity: .8 }));
        trailGroup.add(line);
        const cb = anim.onDone; anim = null; if (progressCb) progressCb(null, 1); if (cb) cb();
      }
    }
    if (cam.position.distanceTo(camPos) > 0.01 || curLook.distanceTo(camLook) > 0.01) { moving = true; cam.position.lerp(camPos, 0.07); curLook.lerp(camLook, 0.09); }
    if (!moving && !dirty) return; // 何も動いていないときは描画しない(発熱対策)
    cam.lookAt(curLook);
    renderer.render(scene, cam);
    dirty = false;
  }
  return { init, load, setAim, hideAim, setBalls, addMarker, play, placeBall, resize, onTap: (cb) => { tapCb = cb; }, onProgress: (cb) => { progressCb = cb; }, busy: () => !!anim };
})();

/* ---------------- side-view trajectory chart ---------------- */
const Profile = (() => {
  const cv = $('profile'), ctx = cv.getContext('2d');
  let cur = null;
  function size() { const r = cv.getBoundingClientRect(); const W = Math.round(r.width * devicePixelRatio), H = Math.round(r.height * devicePixelRatio); if (W && (cv.width !== W || cv.height !== H)) { cv.width = W; cv.height = H; } }
  function draw(res, frac) {
    if (res) cur = { res, frac }; else if (cur) cur.frac = 1;
    size(); const W = cv.width, H = cv.height, dpr = devicePixelRatio;
    ctx.clearRect(0, 0, W, H);
    const pad = 10 * dpr, base = H - 18 * dpr;
    ctx.fillStyle = '#526a5a'; ctx.font = `600 ${11 * dpr}px sans-serif`; ctx.textAlign = 'left';
    ctx.fillText('弾道(横から)', pad, 13 * dpr);
    ctx.strokeStyle = '#2f6b3a'; ctx.lineWidth = 2 * dpr; ctx.beginPath(); ctx.moveTo(pad, base); ctx.lineTo(W - pad, base); ctx.stroke();
    if (!cur) return;
    const r = cur.res, p = r.pts, s = p[0];
    const hx = (q) => Math.hypot(q[1] - s[1], q[3] - s[3]);
    const maxD = Math.max(yd(r.total) * 1.12, 10), maxH = Math.max(r.apex * 1.3, 2);
    const X = (m) => pad + (yd(m) / maxD) * (W - 2 * pad), Y = (h) => base - (Math.max(h, 0) / maxH) * (base - 22 * dpr);
    const n = Math.max(1, Math.floor(cur.frac * (p.length - 1)));
    ctx.strokeStyle = '#d63a2a'; ctx.lineWidth = 2.4 * dpr; ctx.setLineDash([]); ctx.beginPath();
    for (let i = 0; i <= n; i++) { const q = p[i]; i ? ctx.lineTo(X(hx(q)), Y(q[2])) : ctx.moveTo(X(hx(q)), Y(q[2])); }
    ctx.stroke();
    ctx.fillStyle = '#16301f'; ctx.font = `700 ${12 * dpr}px "Avenir Next Condensed","Arial Narrow",sans-serif`;
    if (cur.frac >= 1) {
      ctx.fillStyle = '#d63a2a'; ctx.beginPath(); ctx.arc(X(r.carry), base, 3.5 * dpr, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#16301f'; ctx.textAlign = 'center';
      ctx.fillText(`キャリー ${fy(r.carry)}yd`, clamp(X(r.carry), 50 * dpr, W - 50 * dpr), H - 4 * dpr);
      ctx.textAlign = 'right'; ctx.fillText(`最高 ${r.apex.toFixed(1)}m`, W - pad, 13 * dpr);
    }
  }
  return { draw, clear: () => { cur = null; draw(null, 0); } };
})();

/* ======================================================================
   APP (iPad): home, free practice, course play
   ====================================================================== */
const App = (() => {
  let limit = store.get('limit', 35), nPlayers = store.get('np', 1);
  const names = [store.get('name0', 'プレイヤー1'), store.get('name1', 'プレイヤー2')];
  const COLORS = ['#e2432f', '#2d6fd1'];
  let G = null, readyState = 'off', paired = false;
  const seen = new Set();
  const limitM = () => limit * YD;
  const freeReach = () => (G && G.yd ? G.yd + 3 : 30) * YD;
  const dist = (a, b) => Math.hypot(a.x - b.x, a.z - b.z);
  const headingTo = (a, b) => Math.atan2(b.z - a.z, b.x - a.x);
  World.onProgress((res, frac) => Profile.draw(res, frac));

  /* ---- home ---- */
  function initHome() {
    [...$('limitSeg').children].forEach(b => { b.setAttribute('aria-pressed', +b.dataset.v === limit); b.onclick = () => { limit = +b.dataset.v; store.set('limit', limit); initHome(); }; });
    const u = COURSES.unitYd(limit);
    $('limitNote').textContent = `ホールの長さ:パー2 ${u}ヤード/パー3 ${u * 2}ヤード/パー4 ${u * 3}ヤード`;
    $('soundOn').checked = Sound.on(); $('soundOn').onchange = () => store.set('sound', $('soundOn').checked);
    setReady(readyState); setPaired(paired); paintAll($('homeView'));
  }
  function setPaired(p) { paired = p; $('gs1').classList.toggle('done', p); if (!p) $('gs2').classList.remove('done'); }
  $('goFree').onclick = () => { buildDist(); show('freeView'); };
  $('goCourse').onclick = () => { buildCourses(); show('courseView'); };
  document.querySelectorAll('[data-back]').forEach(b => { b.onclick = () => { show('homeView'); initHome(); }; });

  function buildDist() {
    const g = $('distGrid'); g.textContent = '';
    [5, 10, 15, 20, 25, 30, 35, 40, 45, 60].forEach(d => {
      const b = el('button', d === 60 ? 'strong' : null); b.append(el('b', null, String(d)), el('small', null, d === 60 ? 'ヤード 強めに打つ練習' : 'ヤード'));
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
      const art = el('span', 'art'); paintArt(art, d.id);
      const cv = document.createElement('canvas'); cv.width = 300; cv.height = 400; drawMini(cv, c); art.append(cv);
      const body = el('span', 'cbody');
      const stat = el('span', 'stat');
      const s1 = el('span'); s1.append('パー ', el('strong', null, String(c.par)));
      const s2 = el('span'); s2.append(el('strong', null, String(c.lengthYd)), ' ヤード');
      stat.append(s1, s2);
      body.append(el('b', null, c.name), stat, el('span', 'style' + (d.style === 'テクニカル' ? ' tech' : ''), d.style), el('span', 'd', c.desc));
      b.append(art, body);
      b.onclick = () => startCourse(d.id);
      g.append(b);
    });
  }
  // 上から見たコース図(ティーが下、ピンが上)
  function drawMini(cv, c) {
    const ctx = cv.getContext('2d'), W = cv.width, H = cv.height;
    let minX = -6, maxX = c.pin.x + 10, minZ = -12, maxZ = 12;
    const ext = (x, z) => { minX = Math.min(minX, x); maxX = Math.max(maxX, x); minZ = Math.min(minZ, z); maxZ = Math.max(maxZ, z); };
    c.shapes.forEach(s => { if (s.kind === 'ellipse') { ext(s.cx - s.rx, s.cz - s.rz); ext(s.cx + s.rx, s.cz + s.rz); } else if (s.kind === 'rect') { ext(s.x0, s.z0); ext(s.x1, s.z1); } else s.pts.forEach(([x, z]) => ext(x, z)); });
    minZ = Math.max(minZ, -70); maxZ = Math.min(maxZ, 70); maxX = Math.min(maxX, c.pin.x + 14); minX = Math.max(minX, -6);
    const sc = Math.min((H - 40) / (maxX - minX), (W - 28) / (maxZ - minZ));
    const ox = W / 2 - ((minZ + maxZ) / 2) * sc, oy = H - 14 + minX * sc;
    const P = (x, z) => [ox + z * sc, oy - x * sc];
    ctx.fillStyle = '#fbfaf5'; ctx.fillRect(0, 0, W, H);
    ctx.strokeStyle = 'rgba(22,48,31,.08)'; ctx.lineWidth = 1;
    for (let y = 0; y < H; y += 14) { ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(W, y); ctx.stroke(); }
    const path = (s, grow) => { ctx.beginPath(); const g2 = grow || 0; if (s.kind === 'ellipse') { const [x, y] = P(s.cx, s.cz); ctx.ellipse(x, y, Math.max(1, (s.rz + g2) * sc), Math.max(1, (s.rx + g2) * sc), 0, 0, Math.PI * 2); } else if (s.kind === 'rect') { const [x0, y0] = P(s.x1, s.z0), [x1, y1] = P(s.x0, s.z1); ctx.rect(x0, y0, x1 - x0, y1 - y0); } else { s.pts.forEach(([x, z], i) => { const [a, b] = P(x, z); i ? ctx.lineTo(a, b) : ctx.moveTo(a, b); }); ctx.closePath(); } };
    const draw = (s, fill, stroke, grow) => { path(s, grow); if (fill) { ctx.fillStyle = fill; ctx.fill(); } if (stroke) { ctx.strokeStyle = stroke; ctx.lineWidth = 1.5; ctx.stroke(); } };
    c.shapes.filter(s => s.type === 'fairway' && !s.top).forEach(s => draw(s, '#cfe6bf', '#5d8f58'));
    c.shapes.filter(s => s.type === 'water').forEach(s => draw(s, '#bcdcf0', '#3f82b5'));
    c.shapes.filter(s => s.type === 'chasm').forEach(s => { draw(s, '#e9e1d4', '#6b5540'); path(s); ctx.save(); ctx.clip(); ctx.strokeStyle = 'rgba(107,85,64,.55)'; for (let k = -H; k < W + H; k += 6) { ctx.beginPath(); ctx.moveTo(k, 0); ctx.lineTo(k + H, H); ctx.stroke(); } ctx.restore(); });
    c.shapes.filter(s => s.top && s.type === 'rough').forEach(s => draw(s, '#e8efe0', '#8aa37f'));
    c.shapes.filter(s => s.top && s.type === 'fairway').forEach(s => draw(s, '#cfe6bf', '#5d8f58'));
    c.shapes.filter(s => s.type === 'green').forEach(s => { draw(s, '#a9d690', '#2f6b3a'); for (const k of [0.35, 0.65]) { path({ ...s, rx: s.rx * k, rz: s.rz * k }); ctx.strokeStyle = 'rgba(47,107,58,.45)'; ctx.lineWidth = 1; ctx.stroke(); } });
    const [px, py] = P(c.pin.x, c.pin.z), [tx, ty] = P(0, 0);
    ctx.strokeStyle = '#16301f'; ctx.setLineDash([4, 4]); ctx.lineWidth = 1.5; ctx.beginPath(); ctx.moveTo(tx, ty);
    c.route.filter(r => !c.shapes.some(s => s.island && SIM.inShape(s, r.x, r.z))).forEach(r => { const [x, y] = P(r.x, r.z); ctx.lineTo(x, y); }); ctx.lineTo(px, py); ctx.stroke(); ctx.setLineDash([]);
    ctx.fillStyle = '#16301f'; ctx.fillRect(tx - 6, ty - 3, 12, 6);
    ctx.strokeStyle = '#16301f'; ctx.lineWidth = 1.5; ctx.beginPath(); ctx.moveTo(px, py); ctx.lineTo(px, py - 16); ctx.stroke();
    ctx.fillStyle = '#d63a2a'; ctx.beginPath(); ctx.moveTo(px, py - 16); ctx.lineTo(px + 10, py - 12.5); ctx.lineTo(px, py - 9); ctx.fill();
    ctx.fillStyle = '#16301f'; ctx.font = '600 15px "Avenir Next Condensed","Arial Narrow",sans-serif'; ctx.textAlign = 'left'; ctx.fillText(`${c.lengthYd}Y`, 8, 18);
  }

  /* ---- play common ---- */
  function enterPlay(mode) {
    show('playView');
    $('sideFree').hidden = mode !== 'free'; $('sideCourse').hidden = mode !== 'course';
    $('aimBar').hidden = mode !== 'course'; $('resultBox').hidden = true; $('banner').hidden = true;
    ['gSpeed', 'gAngle', 'gSpin', 'gCarry', 'gTotal', 'gPin'].forEach(id => { $(id).textContent = '–'; }); $('gPinU').textContent = '';
    Profile.clear();
    setReady(readyState);
  }
  function banner(t, sub, ms, kind) {
    const b = $('banner'); b.textContent = t; if (sub) b.append(el('small', null, sub)); b.className = 'banner' + (kind ? ' ' + kind : ''); b.hidden = false;
    clearTimeout(banner._t); if (ms) banner._t = setTimeout(() => { b.hidden = true; }, ms);
  }
  function showShotStart(shot) { $('gSpeed').textContent = shot.speed.toFixed(1); $('gAngle').textContent = shot.angle.toFixed(1); $('gSpin').textContent = String(Math.round(shot.spin)); ['gCarry', 'gTotal', 'gPin'].forEach(id => { $(id).textContent = '…'; }); $('gPinU').textContent = ''; $('banner').hidden = true; }
  function showShotEnd(res) {
    $('gCarry').textContent = fy(res.carry); $('gTotal').textContent = fy(res.total);
    if (res.hazard) { $('gPin').textContent = '–'; $('gPinU').textContent = ''; }
    else if (res.holed) { $('gPin').textContent = 'IN'; $('gPinU').textContent = ''; }
    else if (res.toPin < 1) { $('gPin').textContent = String(Math.round(res.toPin * 100)); $('gPinU').textContent = 'cm'; }
    else { $('gPin').textContent = res.toPin.toFixed(1); $('gPinU').textContent = 'm'; }
  }
  function simulate(s, c, start, hd) {
    const res = SIM.simulate(s, c, start, hd);
    let apex = 0, carryT = res.duration; for (const p of res.pts) if (p[2] > apex) apex = p[2];
    // 着弾点(最初に地面に触れた点)
    for (let i = 1; i < res.pts.length; i++) if (res.pts[i][2] <= 0.001 && res.pts[i - 1][2] > 0.001) { carryT = res.pts[i][0]; res.carryPt = { x: res.pts[i][1], z: res.pts[i][3] }; break; }
    res.apex = apex; res.carryT = carryT; res.hazardAtLanding = res.hazard && res.pts.length < 3;
    return res;
  }

  /* ---- free practice ---- */
  function startFree(d) {
    const c = COURSES.practice(d);
    G = { mode: 'free', yd: d, course: c, shots: [], busy: false };
    enterPlay('free');
    World.load(c); World.setAim(c.tee, 0, freeReach());
    $('hTitle').textContent = 'フリー練習'; $('hMain').textContent = `${d}ヤード`; $('hExtra').textContent = `全面グリーン、速さ${c.stimp}フィート`;
    $('hTurn').textContent = 'ピンまで'; $('hSub').textContent = `${d} yd`; $('hLie').textContent = 'マットから打つ'; $('hLie').className = 's';
    World.onTap(null);
    renderFree(); sendInfo();
  }
  function afterFree(res) {
    const ok = res.holed || res.toPin <= 2;
    G.shots.push({ total: res.total, toPin: res.toPin, ok, holed: res.holed });
    World.addMarker(res.end.x, res.end.z, ok ? '#ffd24a' : '#ffffff');
    if (res.holed) { banner('カップイン!', null, 2600, 'good'); Sound.good(); }
    else if (ok) { banner('OK!', `ピンまで ${fDist(res.toPin)}`, 2600, 'good'); Sound.good(); }
    else banner(`ピンまで ${fDist(res.toPin)}`, null, 2000);
    renderFree();
    setTimeout(() => { if (G && G.mode === 'free') { World.setAim(G.course.tee, 0, freeReach()); G.busy = false; } }, 1600);
  }
  function renderFree() {
    const s = G.shots, n = s.length;
    $('fsN').textContent = n;
    $('fsOk').textContent = n ? `${Math.round(s.filter(x => x.ok).length / n * 100)}%` : '–';
    $('fsAvg').textContent = n ? fDist(s.reduce((a, b) => a + b.toPin, 0) / n) : '–';
    $('fsBest').textContent = n ? fDist(Math.min(...s.map(x => x.toPin))) : '–';
    const t = $('freeLog'); t.textContent = '';
    const hr = el('tr'); ['#', '総距離', 'ピンまで', ''].forEach((h, i) => hr.append(el('th', i ? 'n' : null, h))); t.append(hr);
    if (!n) { const r = el('tr'); const c = el('td', 'empty', '画面上に「打ってOK」が出たら打ってみましょう。'); c.colSpan = 4; r.append(c); t.append(r); }
    s.map((x, i) => [x, i]).reverse().forEach(([x, i]) => {
      const r = el('tr');
      r.append(el('td', null, String(i + 1)), el('td', 'n', fy(x.total) + 'yd'), el('td', 'n', x.holed ? 'IN' : fDist(x.toPin)), el('td', 'n' + (x.ok ? ' good' : ''), x.ok ? 'OK' : ''));
      t.append(r);
    });
  }
  $('changeDist').onclick = () => { buildDist(); show('freeView'); };

  /* ---- course ---- */
  let lastCourseId = null, routeIdx = 0;
  function startCourse(id) {
    lastCourseId = id;
    const c = COURSES.make(id, limit);
    const players = [];
    for (let i = 0; i < nPlayers; i++) players.push({ name: names[i], color: COLORS[i], cls: 'c' + (i + 1), pos: { ...c.tee }, strokes: 0, done: false, score: null, log: [] });
    G = { mode: 'course', course: c, players, cur: 0, aim: 0, busy: false };
    enterPlay('course');
    World.load(c);
    $('hTitle').textContent = `パー${c.par}  ${c.lengthYd}ヤード`; $('hMain').textContent = c.name; $('hExtra').textContent = `上限${limit}ヤード`;
    $('aimRoute').hidden = !c.route.length;
    World.onTap((x, z) => { if (!G || G.mode !== 'course' || G.busy) return; const p = G.players[G.cur]; if (Math.hypot(x - p.pos.x, z - p.pos.z) < 1) return; G.aim = headingTo(p.pos, { x, z }); World.setAim(p.pos, G.aim, limitM()); });
    beginTurn();
  }
  const lieOf = (pos) => SIM.zoneAt(G.course, pos.x, pos.z) === 'rough' ? '絨毯' : 'マット';
  function nextPlayer() { let bi = -1, bd = -1; G.players.forEach((p, i) => { if (p.done) return; const d = dist(p.pos, G.course.pin); if (d > bd + 0.01) { bd = d; bi = i; } }); return bi; }
  function beginTurn() {
    const i = nextPlayer();
    if (i < 0) { finishHole(); return; }
    G.cur = i; G.busy = false; routeIdx = 0;
    const p = G.players[i];
    G.aim = headingTo(p.pos, G.course.pin);
    World.setBalls(G.players.filter((q, k) => k !== i && !q.done && dist(q.pos, p.pos) > 0.4).map(q => ({ x: q.pos.x, z: q.pos.z, color: q.color })));
    World.setAim(p.pos, G.aim, limitM());
    const lie = lieOf(p.pos);
    $('hTurn').textContent = `${G.players.length > 1 ? p.name + ' ' : ''}${p.strokes + 1}打目  残り`;
    $('hSub').textContent = `${fy(dist(p.pos, G.course.pin))} yd`;
    $('hLie').textContent = lie === '絨毯' ? 'ラフ:絨毯から打つ' : 'マットから打つ'; $('hLie').className = 's' + (lie === '絨毯' ? ' rough' : '');
    if (lie === '絨毯') banner('ラフ', '絨毯の上から打ってください', 3000);
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
    const cands = G.course.route.filter(rp => dist(rp, pin) < dp - 3 && dist(p.pos, rp) > 4);
    if (!cands.length) { G.aim = headingTo(p.pos, pin); }
    else { const r = cands[routeIdx % cands.length]; routeIdx++; G.aim = headingTo(p.pos, r); }
    World.setAim(p.pos, G.aim, limitM());
  };
  function afterCourse(p, res) {
    const par = G.course.par; let msg = '', sub = '', kind = '', tone = '';
    if (res.hazard) { p.strokes += 2; msg = res.hazard === 'water' ? '池ポチャ' : '崖から落下'; sub = '1打罰、元の場所から打ち直し'; kind = 'ペナルティ'; tone = 'bad'; }
    else if (res.total >= limitM() - 1e-6) { p.strokes += 2; msg = '上限オーバー'; sub = `総距離 ${fy(res.total)}ヤード、1打罰で打ち直し`; kind = '上限オーバー'; tone = 'bad'; }
    else {
      p.strokes += 1; p.pos = { x: res.end.x, z: res.end.z };
      if (res.holed) { p.done = true; p.score = p.strokes; msg = 'カップイン!'; kind = 'カップイン'; tone = 'good'; }
      else if (res.toPin <= 2) { p.done = true; p.score = p.strokes + 1; msg = 'OK!'; sub = `ピンまで ${fDist(res.toPin)}、+1打で上がり`; kind = 'OK'; tone = 'good'; }
      else { const z = SIM.zoneAt(G.course, p.pos.x, p.pos.z); msg = `残り ${fy(res.toPin)}ヤード`; const island = G.course.shapes.some(s => s.island && SIM.inShape(s, p.pos.x, p.pos.z)); sub = island ? 'ナイス!浮島にオン' : z === 'rough' ? 'ラフ:次は絨毯から' : z === 'green' ? 'グリーン' : z === 'fringe' ? 'カラー' : 'フェアウェイ'; kind = island ? '浮島' : z === 'rough' ? 'ラフ' : z === 'green' ? 'グリーン' : 'フェアウェイ'; if (island) tone = 'good'; }
    }
    if (!p.done && p.strokes >= 2 * par) { p.done = true; p.gaveUp = true; p.score = 2 * par; msg = 'ギブアップ'; sub = `ダブルパー(${2 * par}打)で打ち切り`; tone = 'bad'; }
    if (p.done && p.score > 2 * par) p.score = 2 * par;
    p.log.push({ n: p.strokes, total: res.total, kind });
    banner(msg, sub, 2600, tone);
    if (tone === 'good') Sound.good(); else if (tone === 'bad') Sound.bad();
    if (!res.hazard && res.total < limitM()) World.addMarker(res.end.x, res.end.z, p.color);
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
      c.append(el('span', 'st', p.done ? `${p.gaveUp ? 'ギブアップ' : '上がり'} ${scoreName(p.score, par)}` : `残り ${fy(dist(p.pos, G.course.pin))}yd、${lieOf(p.pos)}から`));
      wrap.append(c);
    });
    const t = $('courseLog'); t.textContent = '';
    const hr = el('tr'); ['', '打数', '総距離', '結果'].forEach((h, i) => hr.append(el('th', i ? 'n' : null, h))); t.append(hr);
    const rows = []; G.players.forEach(p => p.log.forEach(l => rows.push({ p, l })));
    if (!rows.length) { const r = el('tr'); const c = el('td', 'empty', '狙いを決めて、画面に「打ってOK」が出たら打ちましょう。'); c.colSpan = 4; r.append(c); t.append(r); }
    rows.reverse().forEach(({ p, l }) => { const r = el('tr'); r.append(el('td', null, p.name), el('td', 'n', String(l.n)), el('td', 'n', fy(l.total) + 'yd'), el('td', 'n' + (l.kind === 'ペナルティ' || l.kind === '上限オーバー' ? ' bad' : ['OK', 'カップイン', '浮島'].includes(l.kind) ? ' good' : ''), l.kind)); t.append(r); });
  }
  function finishHole() {
    G.busy = true; World.hideAim(); World.setBalls([]);
    const par = G.course.par, ps = G.players;
    const tb = $('resTable'); tb.textContent = '';
    const best = Math.min(...ps.map(p => p.score));
    const hr = el('tr'); ['プレイヤー', '打数', '結果'].forEach((h, i) => hr.append(el('th', i === 1 ? 'n' : null, h))); tb.append(hr);
    ps.forEach(p => { const r = el('tr', ps.length > 1 && p.score === best ? 'win' : null); r.append(el('td', null, p.name), el('td', 'n', String(p.score)), el('td', null, (p.gaveUp ? 'ギブアップ ' : '') + scoreName(p.score, par))); tb.append(r); });
    $('resKicker').textContent = `${G.course.name}  パー${par}`;
    if (ps.length > 1) { const w = ps.filter(p => p.score === best); $('resTitle').textContent = w.length > 1 ? '引き分け' : `${w[0].name} の勝ち`; }
    else $('resTitle').textContent = scoreName(ps[0].score, par);
    $('resultBox').hidden = false; $('banner').hidden = true;
    if (best <= par) Sound.good();
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
      const res = simulate(s, G.course, G.course.tee, 0);
      World.play(res, '#ffffff', () => { showShotEnd(res); afterFree(res); });
    } else {
      const p = G.players[G.cur];
      const res = simulate(s, G.course, p.pos, G.aim);
      World.play(res, p.color, () => { showShotEnd(res); afterCourse(p, res); });
    }
  }
  const num = (v, a, b) => { v = Number(v); return Number.isFinite(v) ? clamp(v, a, b) : null; };
  function onMessage(m) {
    if (m.type === 'status') { if (['wait', 'ready', 'track', 'off', 'adjust'].includes(m.state)) setReady(m.state, ['portrait', 'near', 'far'].includes(m.issue) ? m.issue : 'near'); return; }
    if (m.type === 'shot') {
      const s = { id: String(m.id || '').slice(0, 32), speed: num(m.speed, 1, 40), angle: num(m.angle, 0, 70), dir: num(m.dir, -30, 30) ?? 0, spin: num(m.spin, 0, 12000) };
      if (!s.id || s.speed == null || s.angle == null || s.spin == null) return;
      onShot(s);
    }
  }
  const READY_TEXT = { off: 'カメラ待ち', wait: 'ボールを置いてください', ready: '打ってOK', track: '計測中…' };
  const HOME_TEXT = { off: 'iPhoneのカメラ待ち', wait: 'ボールを置いてください', ready: '打ってOK', track: '計測中' };
  const ADJUST_TEXT = { portrait: 'iPhoneを横向きにしてください', near: 'カメラが近すぎます。1m前後離してください', far: 'カメラが遠すぎます。少し近づけてください' };
  function setReady(s, iss) {
    const was = readyState; readyState = s;
    const adj = s === 'adjust' ? ADJUST_TEXT[iss] || ADJUST_TEXT.near : '';
    $('readyMark').dataset.state = s; $('readyText').textContent = adj || READY_TEXT[s] || '';
    if (s === 'adjust') { $('world').dataset.ready = 'adjust'; $('homeReady').dataset.state = 'adjust'; $('homeReadyText').textContent = adj; $('gs2').classList.remove('done'); return; }
    $('world').dataset.ready = s;
    $('homeReady').dataset.state = s; $('homeReadyText').textContent = HOME_TEXT[s] || '';
    $('gs2').classList.toggle('done', paired && s !== 'off');
    if (s === 'ready' && was !== 'ready' && !$('playView').hidden) Sound.ready();
  }
  function sendInfo() {
    let next = '', lie = '';
    if (G && G.mode === 'course' && $('resultBox').hidden) { const p = G.players[G.cur]; if (p && !p.done) { next = G.players.length > 1 ? p.name : ''; lie = lieOf(p.pos); } }
    else if (G && G.mode === 'free') lie = 'マット';
    Net.send({ type: 'info', next, lie });
  }
  const tfmt = { tSpeed: v => v + ' m/s', tAngle: v => v + '°', tSpin: v => v + ' rpm' };
  Object.keys(tfmt).forEach(k => { const e = $(k), o = $('o' + k); const u = () => { o.textContent = tfmt[k](+e.value); }; e.oninput = u; u(); });
  $('testShot').onclick = () => onShot({ id: 't' + Date.now() + Math.random(), speed: +$('tSpeed').value, angle: +$('tAngle').value, dir: 0, spin: +$('tSpin').value });
  return { initHome, onMessage, setReady, setPaired, sendInfo };
})();

/* ---------------- boot ---------------- */
if (role === 'camera' || role === 'green') startRole(role); else show('roleView');
})();
