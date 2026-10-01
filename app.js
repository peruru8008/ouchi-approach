'use strict';
/* おうちアプローチ — 56° WEDGE CHALLENGE
   セキュリティ方針:
   - カメラ映像はiPhoneの中だけで処理し、保存も送信もしない
   - 端末間で送るのは数値と状態だけ(WebRTCで暗号化された直接通信。データを中継するサーバーは使わない)
   - 受け取ったデータは種類・数値範囲・大きさを検査してから使い、画面にはテキストとしてのみ表示する */
(() => {
// ===== おうちアプローチ 物理エンジン v3 =====
// 1) IMPACT: 練習球の打ち出し(速さ・角度)から、クラブ速度とスピンロフトを逆算し、本物のボールの打ち出しを衝突の物理で求める
// 2) SIM: スピン比に応じた揚力・抗力で飛ばし、Penner(2002)のバウンドモデルで着地させ、芝の上を滑り/転がりで止める
const PHYS = (() => {
  const G = 9.81, RHO = 1.2;
  const BALL = { m: 0.04593, r: 0.02135, k: 2.5 };          // 本物のボール。k = m r^2 / I(中実球 I=2/5 m r^2)
  const deg = Math.PI / 180;

  /* ---------- 空気力学 ---------- */
  // S = r*ω/v(スピン比)。ウェッジ域の高スピンでは揚力が頭打ちになる形にする
  // ディンプルのあるボールは、レイノルズ数が約5万を下回ると抵抗が急に増える(ドラッグクライシス)。アプローチの球速域で効く
  const AERO = { cd0: 0.22, cd1: 0.25, clMax: 0.34, clK: 5, crisis: 0.22, reC: 5.0e4, reW: 4.0e3 };
  const NU = 1.5e-5;                                           // 空気の動粘性係数 [m^2/s]
  function coeffs(v, w, P) {
    P = P || PROFILES.real;
    const S = v > 0.5 ? P.r * Math.abs(w) / v : 0;
    const Re = v * 2 * P.r / NU;
    if (P.kind === 'plastic') {
      // 穴あきの練習ボール:ウィッフルボールの風洞実験(Cd が低速で約1、高速で0.4〜0.6)に合わせる。揚力は穴で弱まる
      const cd = P.cdScale * (0.5 + 0.45 / (1 + (Re / 2.5e4) ** 2));
      const cl = P.clMax * (1 - Math.exp(-2.5 * S / P.clMax)) * Math.sign(w);
      return { cd, cl, S, Re };
    }
    const cl = AERO.clMax * (1 - Math.exp(-AERO.clK * S / AERO.clMax * 0.5)) * Math.sign(w);
    const cd = AERO.cd0 + AERO.cd1 * Math.min(S, 0.8) + AERO.crisis / (1 + Math.exp((Re - AERO.reC) / AERO.reW));
    return { cd, cl, S, Re };
  }
  // ボールの種類。spinTau はスピンが減る時定数(慣性モーメントが小さい軽い球ほど早く減る)
  const PROFILES = {
    real: { kind: 'real', m: 0.04593, r: 0.02135, k: 2.5, spinTau: 22, crater: 1, eS: 1 },
    plastic: null
  };
  function plasticProfile(o) {
    const m = clamp01((o && o.massG ? o.massG : 5), 1, 30) / 1000, r = clamp01((o && o.diamMM ? o.diamMM : 42), 30, 80) / 2000;
    // 中空の殻:I = 2/3 m r^2。スピンの減り方は I に比例してはやくなる
    const tau = 22 * ((2 / 3) * m * r * r) / (0.4 * 0.04593 * 0.02135 * 0.02135);
    // rollMul:軽い穴あき球は芝の上で本物より早く止まる(転がり抵抗の倍率)
    return { kind: 'plastic', m, r, k: 1.5, spinTau: Math.max(1, tau), cdScale: (o && o.dragScale) || 1, clMax: 0.18, crater: 0.45, eS: 0.9, rollMul: (o && o.rollMul) || 3 };
  }
  function clamp01(v, a, b) { v = Number(v); return Number.isFinite(v) ? Math.max(a, Math.min(b, v)) : a; }
  PROFILES.plastic = plasticProfile();

  /* ---------- インパクト(衝突) ---------- */
  const CLUB = { M: 0.29 };                                  // 56度ウェッジのヘッドの有効質量 [kg]
  const REAL = { m: BALL.m, r: BALL.r, k: BALL.k, mu: 0.40, e: (vn) => Math.max(0.70, Math.min(0.86, 0.885 - 0.0050 * vn)), ks: 1.37 };   // ks: 剛体モデルが実測よりスピンを少なく出す分の補正(ツアー平均で合わせた値)
  // 練習球:中空のプラスチック球(I=2/3 m r^2 → k=1.5)。重さと反発係数は設定で変えられる
  function plasticBall(o) { return { m: (o && o.massG ? o.massG : 5) / 1000, r: (o && o.diamMM ? o.diamMM : 42) / 2000, k: 1.5, mu: 0.35, e: () => (o && o.cor ? o.cor : 0.55) }; }
  // クラブ速度1あたりの、ボールの法線速度・接線速度・スピン(スピンロフトSの面に対して)
  function impactUnit(b, S, v) {
    const vnGuess = 1.5 * v * Math.cos(S);
    const e = b.e(vnGuess);
    const cn = (1 + e) * CLUB.M / (CLUB.M + b.m);
    const ctRoll = 1 / (1 + b.k + b.m / CLUB.M);
    const vn = cn * Math.cos(S);
    let vt = ctRoll * Math.sin(S);
    if (vt > b.mu * vn) vt = b.mu * vn;                       // 摩擦が足りなければ滑ったまま離れる
    return { vn, vt, beta: Math.atan2(vt, vn), speed: Math.hypot(vn, vt), w: vt * b.k / b.r };
  }
  // 本物のボールを、クラブ速度v・スピンロフトS・入射角(アタック角)aで打ったとき
  function realLaunch(v, S, a) {
    const u = impactUnit(REAL, S, v);
    const ks = REAL.ks;
    return { speed: u.speed * v, angle: (a + S - u.beta) / deg, spin: ks * u.w * v * 60 / (2 * Math.PI), smash: u.speed };
  }
  // 練習球の計測値(速さup m/s、角度thetaP度)から逆算
  function convert(up, thetaP, opts) {
    const a = (opts && opts.attack != null ? opts.attack : -3) * deg;
    const pb = plasticBall(opts);
    const target = thetaP * deg - a;                          // = S - beta_p(S)
    let lo = Math.max(0.5 * deg, target), hi = 85 * deg;
    for (let i = 0; i < 50; i++) { const mid = (lo + hi) / 2; const u = impactUnit(pb, mid, 10); if (mid - u.beta < target) lo = mid; else hi = mid; }
    const S = (lo + hi) / 2;
    let v = up / impactUnit(pb, S, 10).speed;
    for (let i = 0; i < 3; i++) v = up / impactUnit(pb, S, v).speed;
    const r = realLaunch(v, S, a);
    return { clubSpeed: v, spinLoft: S / deg, speed: r.speed, angle: r.angle, spin: r.spin, smash: r.smash };
  }

  // 練習ボールの計測値から、クラブ速度・スピンロフト・練習ボールのスピンを推定する(本物への換算はしない)
  function plasticLaunch(up, thetaP, opts) {
    const a = (opts && opts.attack != null ? opts.attack : -3) * deg;
    const pb = plasticBall(opts);
    const target = thetaP * deg - a;
    let lo = Math.max(0.5 * deg, target), hi = 85 * deg;
    for (let i = 0; i < 50; i++) { const mid = (lo + hi) / 2; const u = impactUnit(pb, mid, 10); if (mid - u.beta < target) lo = mid; else hi = mid; }
    const S = (lo + hi) / 2;
    let v = up / impactUnit(pb, S, 10).speed;
    for (let i = 0; i < 3; i++) v = up / impactUnit(pb, S, v).speed;
    const u = impactUnit(pb, S, v);
    return { clubSpeed: v, spinLoft: S / deg, speed: up, angle: thetaP, spin: u.w * v * 60 / (2 * Math.PI) };
  }

  /* ---------- コース面 ---------- */
  const inEll = (s, x, z, grow) => { const dx = (x - s.cx) / (s.rx + (grow || 0)), dz = (z - s.cz) / (s.rz + (grow || 0)); return dx * dx + dz * dz <= 1; };
  const inRect = (s, x, z) => x >= s.x0 && x <= s.x1 && z >= s.z0 && z <= s.z1;
  function inPoly(p, x, z) { let c = false; for (let i = 0, j = p.length - 1; i < p.length; j = i++) { const [xi, zi] = p[i], [xj, zj] = p[j]; if (((zi > z) !== (zj > z)) && (x < (xj - xi) * (z - zi) / (zj - zi) + xi)) c = !c; } return c; }
  function inShape(s, x, z, grow) { return s.kind === 'ellipse' ? inEll(s, x, z, grow) : s.kind === 'rect' ? inRect(s, x, z) : inPoly(s.pts, x, z); }
  function zoneAt(c, x, z) {
    if (c.allGreen) return 'green';
    for (const s of c.shapes) if (s.type === 'green' && inShape(s, x, z)) return 'green';
    for (const s of c.shapes) if (s.top && inShape(s, x, z)) return s.type;
    for (const s of c.shapes) if ((s.type === 'chasm' || s.type === 'water') && inShape(s, x, z)) return s.type;
    for (const s of c.shapes) if (s.type === 'green' && inShape(s, x, z, 1.2 * (c.scale || 1))) return 'fringe';
    for (const s of c.shapes) if (s.type === 'fairway' && inShape(s, x, z)) return 'fairway';
    return 'rough';
  }
  // crater: 着地のくぼみの深さ(Penner角の倍率)、eS: 反発の倍率、mu: 着地時の摩擦、slide: 転がり始めるまでの滑り摩擦、decel: 転がり抵抗[m/s^2]
  const SURF = {
    green:   { crater: 1.0, eS: 1.0,  mu: 0.43, slide: 0.30 },
    fringe:  { crater: 1.25, eS: 0.9, mu: 0.45, slide: 0.35, decel: 1.3 },
    fairway: { crater: 1.35, eS: 0.85, mu: 0.45, slide: 0.38, decel: 1.7 },
    rough:   { crater: 2.2, eS: 0.5,  mu: 0.55, slide: 0.65, decel: 4.5 }
  };
  const decelOf = (c, zone, P) => (zone === 'green' ? 5.49 / c.stimp : SURF[zone].decel) * ((P && P.rollMul) || 1);
  const isHaz = (z) => z === 'water' || z === 'chasm';

  /* Penner(2002)のグリーン上のバウンド:
     着地でできるくぼみの前の壁に当たる、と考えて面を θc だけ起こす
     θc = 15.4° × (v/18.6 m/s) × (θin/44.4°)、e = 0.510 − 0.0375 vn + 0.000903 vn²、μ = 0.43 */
  function bounce(vh, vy, w, surf, rr) {
    const vin = Math.hypot(vh, vy), thIn = Math.atan2(-vy, Math.max(1e-6, vh)) / deg;
    const tc = Math.min(40, 15.4 * (vin / 18.6) * (thIn / 44.4) * surf.crater) * deg;
    const sn = Math.sin(tc), cs = Math.cos(tc);
    const vn = vh * sn - vy * cs, vt = vh * cs + vy * sn;      // くぼみの壁に対する法線(押し込む向き)・接線
    const e = Math.max(0.05, Math.min(0.6, (0.510 - 0.0375 * vn + 0.000903 * vn * vn) * surf.eS));
    const r = rr || BALL.r, slip = vt + w * r;                 // 接地点のすべり(バックスピンは前向きに足す)
    let vt2, w2;
    if (surf.mu * (1 + e) * vn >= (2 / 7) * Math.abs(slip)) { vt2 = (5 * vt - 2 * r * w) / 7; w2 = -vt2 / r; }
    else { const sg = Math.sign(slip); vt2 = vt - sg * surf.mu * (1 + e) * vn; w2 = w - sg * (5 / (2 * r)) * surf.mu * (1 + e) * vn; }
    let vh2 = vt2 * cs - e * vn * sn, vy2 = vt2 * sn + e * vn * cs;
    if (vy2 < 0) vy2 = 0;
    return { vh: vh2, vy: vy2, w: w2, e, tc: tc / deg };
  }

  /* ---------- 飛行・バウンド・転がり ---------- */
  // shot: {speed m/s, angle 度, dir 度(+右), spin rpm}(本物のボールの値)
  function simulate(shot, c, start, heading, prof) {
    const P = prof || PROFILES.real;
    const dt = 1 / 480, r = P.r, k = 0.5 * RHO * Math.PI * P.r * P.r / P.m;
    const ph = heading + (shot.dir || 0) * deg, hx = Math.cos(ph), hz = Math.sin(ph);
    const th = shot.angle * deg;
    let x = start.x, y = 0, z = start.z;
    let vx = shot.speed * Math.cos(th) * hx, vy = shot.speed * Math.sin(th), vz = shot.speed * Math.cos(th) * hz;
    let w = shot.spin * 2 * Math.PI / 60;                      // バックスピン(rad/s、+が逆回転)
    const pts = [[0, x, y, z]];
    let t = 0, phase = 'air', carry = null, holed = false, hazard = null, apex = 0, landAngle = null, bounces = 0, backed = false;
    const cup = c.pin, CUP_R = 0.054;
    const ax = (shot.axis || 0) * deg, ca = Math.cos(ax), sa = Math.sin(ax);
    const acc = (vx, vy, vz, w) => {
      const v = Math.hypot(vx, vy, vz) || 1e-9, { cd, cl } = coeffs(v, w, P);
      const vhh = Math.hypot(vx, vz) || 1e-9;
      // 揚力は速度に垂直で、進行方向を含む鉛直面内(純バックスピン)
      let lx = -vy * (vx / vhh) / v, ly = vhh / v, lz = -vy * (vz / vhh) / v;
      // 回転軸の傾き(+で右へ曲がる):揚力を進行方向まわりに回す。右 = 進行方向 × 上
      if (ax) { const ux = vx / v, uy = vy / v, uz = vz / v, cx = uy * lz - uz * ly, cy = uz * lx - ux * lz, cz = ux * ly - uy * lx; lx = lx * ca + cx * sa; ly = ly * ca + cy * sa; lz = lz * ca + cz * sa; }
      return [-k * cd * v * vx + k * cl * v * v * lx, -G - k * cd * v * vy + k * cl * v * v * ly, -k * cd * v * vz + k * cl * v * v * lz];
    };
    for (let i = 0; i < 480 * 40; i++) {
      t += dt;
      if (phase === 'air') {
        // 2次のルンゲ=クッタ
        const a1 = acc(vx, vy, vz, w);
        const mx = vx + a1[0] * dt / 2, my = vy + a1[1] * dt / 2, mz = vz + a1[2] * dt / 2;
        const a2 = acc(mx, my, mz, w);
        x += mx * dt; y += my * dt; z += mz * dt;
        vx += a2[0] * dt; vy += a2[1] * dt; vz += a2[2] * dt;
        w *= Math.exp(-dt / P.spinTau);                        // 空中でのスピン減衰
        if (y > apex) apex = y;
        if (y <= 0) {
          y = 0;
          const zone = zoneAt(c, x, z);
          if (carry === null) { carry = { x, z }; landAngle = Math.atan2(-vy, Math.hypot(vx, vz)) / deg; }
          if (isHaz(zone)) { hazard = zone; pts.push([t, x, zone === 'chasm' ? -2.5 : -0.05, z]); break; }
          if (Math.hypot(x - cup.x, z - cup.z) < CUP_R - 0.01 && Math.hypot(vx, vz) < 4) { holed = true; x = cup.x; z = cup.z; y = -0.03; pts.push([t, x, y, z]); break; }
          const vh = Math.hypot(vx, vz), ux = vh > 1e-6 ? vx / vh : hx, uz = vh > 1e-6 ? vz / vh : hz;
          const sf = SURF[zone] || SURF.green; const b = bounce(vh, vy, w, { crater: sf.crater * P.crater, eS: sf.eS * P.eS, mu: sf.mu }, r); bounces++;
          vx = ux * b.vh; vz = uz * b.vh; vy = b.vy; w = b.w;
          if (vy < 0.25) { vy = 0; phase = 'ground'; }
        }
      } else {
        // 接地中:接地点のすべりがある間は滑り摩擦、すべりがなくなれば転がり抵抗
        const zone = zoneAt(c, x, z);
        if (isHaz(zone)) { hazard = zone; pts.push([t, x, zone === 'chasm' ? -2.5 : -0.05, z]); break; }
        const s = SURF[zone] || SURF.green;
        const sx = vx + w * r * hx, sz = vz + w * r * hz, sl = Math.hypot(sx, sz);
        if (sl > 0.02) {
          const ax = -s.slide * G * sx / sl, az = -s.slide * G * sz / sl;
          vx += ax * dt; vz += az * dt;
          w += (5 / (2 * r)) * (ax * hx + az * hz) * dt;
        } else {
          const v = Math.hypot(vx, vz), dec = decelOf(c, zone, P);
          if (v > 1e-6) { const nv = Math.max(0, v - dec * dt); vx *= nv / v; vz *= nv / v; }
          w = -(vx * hx + vz * hz) / r;
        }
        const slopeOn = zone === 'green' || c.allGreen;
        if (slopeOn) { vx += (5 / 7) * G * c.slope.x * dt; vz += (5 / 7) * G * c.slope.z * dt; }
        if (vx * hx + vz * hz < -0.05) backed = true;
        x += vx * dt; z += vz * dt;
        const spd = Math.hypot(vx, vz), dcup = Math.hypot(x - cup.x, z - cup.z);
        if (dcup < CUP_R && spd < 1.3) { holed = true; x = cup.x; z = cup.z; y = -0.03; pts.push([t, x, y, z]); break; }
        const slopeMag = slopeOn ? Math.hypot(c.slope.x, c.slope.z) : 0;
        if (spd < 0.015 && sl < 0.02 && slopeMag < 0.035) break;
        if (spd < 0.015 && sl < 0.02) { vx = 0; vz = 0; }
      }
      if (i % 8 === 0) pts.push([t, x, y, z]);
    }
    if (!hazard && !holed) pts.push([t, x, y, z]);
    const cr = carry || { x, z };
    return {
      pts, end: { x, z }, holed, hazard, duration: t, apex, landAngle, bounces, backed,
      carry: Math.hypot(cr.x - start.x, cr.z - start.z), carryPt: carry,
      total: Math.hypot(x - start.x, z - start.z),
      toPin: holed ? 0 : Math.hypot(x - cup.x, z - cup.z),
      zone: hazard || zoneAt(c, x, z)
    };
  }
  return { simulate, zoneAt, inShape, convert, realLaunch, plasticLaunch, plasticProfile, PROFILES, coeffs, bounce, AERO, REAL, CLUB, plasticBall, impactUnit };
})();
const SIM = PHYS;

// ===== 後方・低い位置のカメラでの計測(Down The Line)=====
// ボールの後ろ(飛ばす方向の延長線上)の低い位置から、縦向きのiPhoneで撮る前提。
//  1) 置き場所を1回タップで登録 → 置き場所だけを毎コマ見る(軽い・速い)
//  2) 何もない置き場所(背景)と比べて、丸い物が0.2秒止まったら「打ってOK」
//  3) 打ったら、飛んでいくボールの位置と見かけの大きさ(遠いほど小さい)を元の解像度で追う
//  4) 重力の向き(傾きセンサー)と距離(ボールまで)から、3Dの軌道を当てはめて球速・打ち出し角・左右の向きを出す
//  5) 最後まで追えたら、そのボールの空気抵抗を自動で合わせ込む
// 画面やカメラには触れず、コマの一部を読む関数(fr.roi)と時刻だけを受け取る。アプリと検証スクリプトで同じものを使う。
const DTL = (() => {
  const D_DEFAULT = 0.042;
  const READY_FRAMES = 12;                 // 60fpsで0.2秒
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

  // ---- 小さな道具 ----
  function lumaMean(R, ring) { let s = 0, n = 0; const { d, w, h } = R; for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) { if (ring && x > 2 && y > 2 && x < w - 3 && y < h - 3) continue; const i = (y * w + x) * 4; s += d[i] + d[i + 1] + d[i + 2]; n++; } return n ? s / n : 1; }
  // 2つの同じ範囲の画像の差(明るさの変化は全体の比で打ち消す)
  function diffMask(A, B, thr) {
    // 明るさの比は、枠の画素ごとの比の中央値(クラブなどが一部にかかっても崩れない)
    const rs = []; const { w, h } = A;
    for (let y = 0; y < h; y += 2) for (let x = 0; x < w; x += 2) { if (x > 2 && y > 2 && x < w - 3 && y < h - 3) continue; const i = (y * w + x) * 4; const a = A.d[i] + A.d[i + 1] + A.d[i + 2], b = B.d[i] + B.d[i + 1] + B.d[i + 2]; if (a > 30) rs.push(b / a); }
    rs.sort((p, q) => p - q); const g = rs.length ? clamp(rs[rs.length >> 1], 0.6, 1.6) : 1;
    const n = A.w * A.h, m = new Uint8Array(n);
    for (let k = 0, i = 0; k < n; k++, i += 4) { const dd = Math.abs(A.d[i] * g - B.d[i]) + Math.abs(A.d[i + 1] * g - B.d[i + 1]) + Math.abs(A.d[i + 2] * g - B.d[i + 2]); if (dd > thr) m[k] = 1; }
    return m;
  }
  function closeOpen(m, w, h) {
    // 1画素の穴を埋め、1画素の点を消す
    const a = m.slice();
    for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) { const k = y * w + x; if (!m[k]) { const s = m[k - 1] + m[k + 1] + m[k - w] + m[k + w]; if (s >= 3) a[k] = 1; } }
    const b = a.slice();
    for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) { const k = y * w + x; if (a[k]) { const s = a[k - 1] + a[k + 1] + a[k - w] + a[k + w]; if (s <= 1) b[k] = 0; } }
    return b;
  }
  function blobs(m, w, h, minA) {
    const seen = new Uint8Array(w * h), out = [];
    for (let k0 = 0; k0 < w * h; k0++) {
      if (!m[k0] || seen[k0]) continue;
      const q = [k0]; seen[k0] = 1; let n = 0, sx = 0, sy = 0, x0 = w, x1 = 0, y0 = h, y1 = 0; const px = [];
      while (q.length) {
        const k = q.pop(), x = k % w, y = (k / w) | 0; n++; sx += x; sy += y; px.push(k);
        if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y;
        if (x > 0 && m[k - 1] && !seen[k - 1]) { seen[k - 1] = 1; q.push(k - 1); }
        if (x < w - 1 && m[k + 1] && !seen[k + 1]) { seen[k + 1] = 1; q.push(k + 1); }
        if (y > 0 && m[k - w] && !seen[k - w]) { seen[k - w] = 1; q.push(k - w); }
        if (y < h - 1 && m[k + w] && !seen[k + w]) { seen[k + w] = 1; q.push(k + w); }
      }
      if (n >= minA) out.push({ n, x: sx / n, y: sy / n, bw: x1 - x0 + 1, bh: y1 - y0 + 1, px });
    }
    return out;
  }
  // ボールの2色(2-means)
  function palette(R, m) {
    const pts = []; for (let k = 0; k < m.length; k++) if (m[k]) { const i = k * 4; pts.push([R.d[i], R.d[i + 1], R.d[i + 2]]); }
    if (pts.length < 8) return null;
    const lum = (q) => q[0] + q[1] + q[2]; pts.sort((a, b) => lum(a) - lum(b));
    let c1 = pts[Math.floor(pts.length * 0.2)].slice(), c2 = pts[Math.floor(pts.length * 0.85)].slice(), n1 = 0, n2 = 0;
    for (let it = 0; it < 8; it++) {
      const s1 = [0, 0, 0], s2 = [0, 0, 0]; n1 = 0; n2 = 0;
      for (const q of pts) { const d1 = Math.abs(q[0] - c1[0]) + Math.abs(q[1] - c1[1]) + Math.abs(q[2] - c1[2]), d2 = Math.abs(q[0] - c2[0]) + Math.abs(q[1] - c2[1]) + Math.abs(q[2] - c2[2]); if (d1 < d2) { s1[0] += q[0]; s1[1] += q[1]; s1[2] += q[2]; n1++; } else { s2[0] += q[0]; s2[1] += q[1]; s2[2] += q[2]; n2++; } }
      if (n1) c1 = s1.map(v => v / n1); if (n2) c2 = s2.map(v => v / n2);
    }
    const sep = Math.abs(c1[0] - c2[0]) + Math.abs(c1[1] - c2[1]) + Math.abs(c1[2] - c2[2]);
    return { c: [c1, c2], two: sep > 90 && Math.min(n1, n2) > pts.length * 0.15 };
  }
  // ボールの境目の向き:色Aの重心 → 色Bの重心 の向き(境目に垂直)
  function seamAngle(R, px, pal) {
    if (!pal || !pal.two) return null;
    let ax = 0, ay = 0, an = 0, bx = 0, by = 0, bn = 0;
    for (const k of px) { const i = k * 4, x = k % R.w, y = (k / R.w) | 0, d = R.d;
      const d1 = Math.abs(d[i] - pal.c[0][0]) + Math.abs(d[i + 1] - pal.c[0][1]) + Math.abs(d[i + 2] - pal.c[0][2]);
      const d2 = Math.abs(d[i] - pal.c[1][0]) + Math.abs(d[i + 1] - pal.c[1][1]) + Math.abs(d[i + 2] - pal.c[1][2]);
      if (Math.min(d1, d2) > 120) continue;
      if (d1 < d2) { ax += x; ay += y; an++; } else { bx += x; by += y; bn++; } }
    if (an < px.length * 0.12 || bn < px.length * 0.12) return null;
    return Math.atan2(by / bn - ay / an, bx / bn - ax / an);
  }

  // 置き場所の縮小画像(6×6の平均色)。空かどうかの確認だけに使い、端末の中にだけ保存する
  function thumbOf(R) {
    const n = 6, out = []; for (let gy = 0; gy < n; gy++) for (let gx = 0; gx < n; gx++) {
      let s0 = 0, s1 = 0, s2 = 0, c = 0; const x0 = Math.floor(gx * R.w / n), x1 = Math.floor((gx + 1) * R.w / n), y0 = Math.floor(gy * R.h / n), y1 = Math.floor((gy + 1) * R.h / n);
      for (let y = y0; y < y1; y++) for (let x = x0; x < x1; x++) { const i = (y * R.w + x) * 4; s0 += R.d[i]; s1 += R.d[i + 1]; s2 += R.d[i + 2]; c++; }
      out.push(Math.round(s0 / Math.max(1, c)), Math.round(s1 / Math.max(1, c)), Math.round(s2 / Math.max(1, c)));
    }
    return out;
  }
  function thumbDiff(a, b) {
    if (!a || !b || a.length !== b.length) return 0;
    let sa = 0, sb = 0; for (let i = 0; i < a.length; i++) { sa += a[i]; sb += b[i]; } const g = sb / Math.max(1, sa);
    let d = 0, n = 0; for (let gy = 1; gy < 5; gy++) for (let gx = 1; gx < 5; gx++) for (let c = 0; c < 3; c++) { const i = (gy * 6 + gx) * 3 + c; d += Math.abs(a[i] * g - b[i]); n++; }
    return d / n;
  }
  // ---- 丸の検出(ハフ変換)。背景を覚えていなくても、手持ちで少し動いても、ボールの輪郭から見つける ----
  // R: 画像の一部、(cx,cy): 探す中心(Rの中の座標)、sr: 中心を探す半径、[rmin,rmax]: ボールの半径の範囲
  function findCircle(R, cx, cy, sr, rmin, rmax) {
    const { d, w, h } = R, n = w * h;
    const gx = new Float32Array(n), gy = new Float32Array(n), mag = new Float32Array(n);
    for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) {
      let best = 0, bx = 0, by = 0;
      for (let c = 0; c < 3; c++) {
        const p = (k) => d[k * 4 + c], k = y * w + x;
        const sx = (p(k - w + 1) + 2 * p(k + 1) + p(k + w + 1)) - (p(k - w - 1) + 2 * p(k - 1) + p(k + w - 1));
        const sy = (p(k + w - 1) + 2 * p(k + w) + p(k + w + 1)) - (p(k - w - 1) + 2 * p(k - w) + p(k - w + 1));
        const m = sx * sx + sy * sy; if (m > best) { best = m; bx = sx; by = sy; }
      }
      const k = y * w + x; mag[k] = Math.sqrt(best); gx[k] = bx; gy[k] = by;
    }
    const sorted = Array.from(mag).sort((a, b) => a - b), thr = Math.max(80, sorted[Math.floor(n * 0.9)]);
    const step = Math.max(1, (rmax - rmin) / 14), radii = []; for (let r = rmin; r <= rmax + 1e-6; r += step) radii.push(r);
    const acc = radii.map(() => new Float32Array(n));
    for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) {
      const k = y * w + x; if (mag[k] < thr) continue;
      const ux = gx[k] / mag[k], uy = gy[k] / mag[k];
      radii.forEach((r, ri) => {
        for (const s of [1, -1]) {
          const X = Math.round(x + s * ux * r), Y = Math.round(y + s * uy * r);
          if (X < 0 || Y < 0 || X >= w || Y >= h) continue;
          if ((X - cx) * (X - cx) + (Y - cy) * (Y - cy) > sr * sr) continue;
          acc[ri][Y * w + X] += 1;
        }
      });
    }
    let best = null;
    radii.forEach((r, ri) => {
      const A = acc[ri];
      for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) {
        const k = y * w + x; if (!A[k]) continue;
        const v = A[k] + 0.5 * (A[k - 1] + A[k + 1] + A[k - w] + A[k + w]);       // 少しぼかして集計
        const sc = v / (2 * Math.PI * r * 2.2);
        if (!best || sc > best.score) best = { x, y, r, score: sc };
      }
    });
    if (!best) return null;
    // 内側と外側の色がはっきり違うこと(床や芝の模様の偶然の丸を除く)
    const mean = (r0, r1) => { let s = [0, 0, 0], c = 0; for (let y = Math.floor(best.y - r1); y <= best.y + r1; y++) for (let x = Math.floor(best.x - r1); x <= best.x + r1; x++) { if (x < 0 || y < 0 || x >= w || y >= h) continue; const q = Math.hypot(x - best.x, y - best.y); if (q < r0 || q > r1) continue; const i = (y * w + x) * 4; s[0] += d[i]; s[1] += d[i + 1]; s[2] += d[i + 2]; c++; } return c ? s.map(v => v / c) : null; };
    const ins = mean(0, best.r * 0.7), out = mean(best.r * 1.25, best.r * 1.6);
    best.contrast = ins && out ? Math.abs(ins[0] - out[0]) + Math.abs(ins[1] - out[1]) + Math.abs(ins[2] - out[2]) : 0;
    // 輪郭の上に、実際に縁がどれだけあるか
    let on = 0, tot = 0; for (let a = 0; a < 48; a++) { const t = a / 48 * 2 * Math.PI; let hit = 0; for (const dr of [-1, 0, 1]) { const X = Math.round(best.x + Math.cos(t) * (best.r + dr)), Y = Math.round(best.y + Math.sin(t) * (best.r + dr)); if (X >= 0 && Y >= 0 && X < w && Y < h && mag[Y * w + X] >= thr * 0.7) hit = 1; } on += hit; tot++; }
    best.support = on / tot;
    return best;
  }
  // 画面全体の縮小画像で、カメラが動いた(画面全体がずれた)かを見る。人が動いても全体はずれないので区別できる
  function gray(a) { const n = a.w * a.h, g = new Float32Array(n); let m = 0; for (let k = 0; k < n; k++) { const i = k * 4; g[k] = a.d[i] + a.d[i + 1] + a.d[i + 2]; m += g[k]; } m /= n || 1; for (let k = 0; k < n; k++) g[k] /= m || 1; return g; }
  function shiftOf(a, b) {
    if (!a || !b || a.w !== b.w || a.h !== b.h) return null;
    const A = gray(a), B = gray(b), w = a.w, h = a.h; let best = null, zero = 0;
    for (let dy = -6; dy <= 6; dy++) for (let dx = -6; dx <= 6; dx++) {
      const ds = []; for (let y = 6; y < h - 6; y++) for (let x = 6; x < w - 6; x++) ds.push(Math.abs(A[y * w + x] - B[(y + dy) * w + x + dx]));
      ds.sort((p, q) => p - q); const md = ds[ds.length >> 1];
      if (dx === 0 && dy === 0) zero = md;
      if (!best || md < best.md) best = { dx, dy, md };
    }
    return { dx: best.dx, dy: best.dy, md: best.md, zero };
  }
  const movedBy = (sh) => sh && (((sh.dx || sh.dy) && sh.md < 0.7 * sh.zero && sh.zero > 0.04) || sh.zero > 0.4);
  function solveLin(A, b) {
    const n = b.length, M = A.map((r, i) => r.concat([b[i]]));
    for (let c = 0; c < n; c++) {
      let p = c; for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
      if (Math.abs(M[p][c]) < 1e-12) return null; [M[c], M[p]] = [M[p], M[c]];
      for (let r = 0; r < n; r++) if (r !== c) { const f = M[r][c] / M[c][c]; for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k]; }
    }
    return M.map((r, i) => r[n] / r[i]);
  }
  function session(opt) {
    // opt(): { dist: カメラ→ボールの距離[m], diamMM, massG, drag, sens, up: [x,y,z](カメラ座標の上向き。なければ水平と仮定) }
    let state = 'setup', tee = null, empty = null, snap = null, stable = 0, prevIn = null, fN = 0;
    let ball = null, pal = null, seam0 = null, ref = null, refBox = null, readyRoi = null, launchT = 0;
    let obs = [], lost = 0, lastSeen = null, exp = null, quiet = 0, removeSeen = false, armT = 0, back = 0;
    let cand = null, scene = null, movedN = 0, calmN = 0, prevState = 'wait', clearT = null, lastSmall = null;
    const S = () => opt();
    const roiBox = () => { const R = Math.max(10, Math.ceil(tee.r * 3)); return [Math.round(tee.x - R), Math.round(tee.y - R), 2 * R, 2 * R]; };

    // ---- タップしたボールを、その場で測ってすぐ「打ってOK」にする ----
    // タップした点のまわりで、輪郭(明るさ・色の変わり目)がいちばん強く一周している丸を探す
    function measureAt(fr, x, y, rHint, rLo, rHi) {
      const big = Math.round(Math.min(fr.W, fr.H) * 0.07), R = fr.roi(Math.round(x - big), Math.round(y - big), 2 * big, 2 * big);
      const { d, w, h } = R, cx0 = x - R.x, cy0 = y - R.y;
      const px = (X, Y, c) => { X = Math.max(0, Math.min(w - 1, X)); Y = Math.max(0, Math.min(h - 1, Y)); const x0 = Math.floor(X), y0 = Math.floor(Y), fx = X - x0, fy = Y - y0, x1 = Math.min(w - 1, x0 + 1), y1 = Math.min(h - 1, y0 + 1);
        const g = (xx, yy) => d[(yy * w + xx) * 4 + c]; return (g(x0, y0) * (1 - fx) + g(x1, y0) * fx) * (1 - fy) + (g(x0, y1) * (1 - fx) + g(x1, y1) * fx) * fy; };
      const edge = (cx, cy, r) => { let s = 0; for (let a = 0; a < 40; a++) { const t = a / 40 * 2 * Math.PI, c = Math.cos(t), sn = Math.sin(t); let e = 0; for (let ch = 0; ch < 3; ch++) { const ro = r + Math.max(1.5, 0.18 * r), ri = r - Math.max(1.5, 0.18 * r); e += Math.abs(px(cx + c * ro, cy + sn * ro, ch) - px(cx + c * ri, cy + sn * ri, ch)); } s += Math.min(e, 200); } return s / 40; };
      const rMin = Math.max(4, rLo || 5), rMax = Math.min(Math.max(8, big * 0.85), rHi || 1e9);
      let best = null; const perR = [];
      for (let r = rMin; r <= rMax; r *= 1.08) {
        let bR = null;
        const st = Math.max(1, r / 4);
        for (let dy = -r * 0.9; dy <= r * 0.9; dy += st) for (let dx = -r * 0.9; dx <= r * 0.9; dx += st) {
          const cx = cx0 + dx, cy = cy0 + dy; if (Math.hypot(dx, dy) > r * 0.9) continue;
          let sc = edge(cx, cy, r);
          if (rHint) sc *= Math.exp(-Math.pow(Math.log(r / rHint) / 0.35, 2) / 2) * 0.5 + 0.5;   // 前に測った大きさに近いほど少し優先
          if (!bR || sc > bR.sc) bR = { cx, cy, r, sc };
        }
        if (bR) perR.push(bR);
      }
      if (!perR.length) return null;
      // ボールの中の境目や穴も小さな丸に見えるので、十分強い丸のうち一番外側(大きい方)をボールの輪郭とする
      const top = Math.max(...perR.map(q => q.sc));
      for (const q of perR) if (q.sc >= 0.92 * top && (!best || q.r > best.r)) best = q;
      // 細かく詰める
      for (let it = 0; it < 2; it++) { let b2 = best; for (const [dx, dy, dr] of [[0.5,0,0],[-0.5,0,0],[0,0.5,0],[0,-0.5,0],[0,0,0.5],[0,0,-0.5]]) { const sc = edge(best.cx + dx, best.cy + dy, best.r + dr); if (sc > b2.sc) b2 = { cx: best.cx + dx, cy: best.cy + dy, r: best.r + dr, sc }; } best = b2; }
      return { x: best.cx + R.x, y: best.cy + R.y, r: best.r, score: best.sc };
    }
    // ボールの境目は縦にまっすぐ置く前提:タップした側の半球は「縦に直径ぶんの高さ、横に半径ぶんの幅」の半円に写る。
    // タップした色と同じ色の広がりを塗りつぶしで求め、その高さから半径、まっすぐな辺から中心を出す
    function measureHalf(fr, x, y) {
      const big = Math.round(Math.min(fr.W, fr.H) * 0.07), R = fr.roi(Math.round(x - big), Math.round(y - big), 2 * big, 2 * big);
      const { d, w, h } = R, sx = Math.round(x - R.x), sy = Math.round(y - R.y);
      const cs = []; for (let yy = sy - 2; yy <= sy + 2; yy++) for (let xx = sx - 2; xx <= sx + 2; xx++) { if (xx < 0 || yy < 0 || xx >= w || yy >= h) continue; const i = (yy * w + xx) * 4; cs.push([d[i], d[i + 1], d[i + 2]]); }
      if (!cs.length) return null;
      const med = [0, 1, 2].map(c => cs.map(q => q[c]).sort((a, b) => a - b)[cs.length >> 1]);
      for (const tol of [70, 50, 35]) {
        const m = new Uint8Array(w * h);
        for (let k = 0; k < w * h; k++) { const i = k * 4; if (Math.abs(d[i] - med[0]) + Math.abs(d[i + 1] - med[1]) + Math.abs(d[i + 2] - med[2]) < tol) m[k] = 1; }
        const cm = closeOpen(m, w, h);
        const seen = new Uint8Array(w * h), q = [sy * w + sx]; if (!cm[q[0]]) { let f = -1; for (let r = 1; r < 4 && f < 0; r++) for (let dy = -r; dy <= r && f < 0; dy++) for (let dx = -r; dx <= r && f < 0; dx++) { const k = (sy + dy) * w + sx + dx; if (k >= 0 && k < w * h && cm[k]) f = k; } if (f < 0) continue; q[0] = f; }
        seen[q[0]] = 1; let n = 0, touch = false; const L = new Map(), Rr = new Map();
        while (q.length) {
          const k = q.pop(), xx = k % w, yy = (k / w) | 0; n++;
          if (xx === 0 || yy === 0 || xx === w - 1 || yy === h - 1) touch = true;
          if (!L.has(yy) || xx < L.get(yy)) L.set(yy, xx); if (!Rr.has(yy) || xx > Rr.get(yy)) Rr.set(yy, xx);
          for (const k2 of [k - 1, k + 1, k - w, k + w]) if (k2 >= 0 && k2 < w * h && cm[k2] && !seen[k2] && Math.abs((k2 % w) - xx) <= 1) { seen[k2] = 1; q.push(k2); }
        }
        if (touch || n < 20) continue;
        const ys = [...L.keys()].sort((a, b) => a - b), y0 = ys[0], y1 = ys[ys.length - 1], r = (y1 - y0 + 1) / 2;
        if (r < 4) continue;
        // 半円のまっすぐな側(境目)を探す:各行の左端・右端のばらつきが小さい方
        const mid = ys.filter(yy => Math.abs(yy - (y0 + y1) / 2) < r * 0.7);
        const sd = (arr) => { const m0 = arr.reduce((a, b) => a + b, 0) / arr.length; return Math.sqrt(arr.reduce((a, b) => a + (b - m0) ** 2, 0) / arr.length); };
        const Ls = mid.map(yy => L.get(yy)), Rs = mid.map(yy => Rr.get(yy)), wid = Math.max(...Rs) - Math.min(...Ls) + 1;
        let cx;
        if (wid > 1.5 * r) cx = (Math.min(...Ls) + Math.max(...Rs)) / 2;                 // 1色のボール(丸ごと)
        else cx = sd(Ls) < sd(Rs) ? Ls.reduce((a, b) => a + b, 0) / Ls.length : Rs.reduce((a, b) => a + b, 0) / Rs.length + 1;
        // 面積の確かめ:半円ならπr²/2、丸ごとならπr²
        const exp = wid > 1.5 * r ? Math.PI * r * r : Math.PI * r * r / 2;
        if (n < 0.45 * exp || n > 1.6 * exp) continue;
        return { x: cx + R.x, y: (y0 + y1) / 2 + R.y, r, score: 100 };
      }
      return null;
    }
    function tapReady(fr, x, y, t) {
      // 見込みの大きさ:前に測った大きさ、なければ距離と画角から(iPhoneの広角は縦向き1080px幅で焦点距離 約1440px)
      const o = S(), fGuess = (o.fpx || 1440) * Math.min(fr.W, fr.H) / 1080, rGuess = fGuess * ((o.diamMM || 42) / 2000) / (o.dist || 1.8), rExp = tee && tee.r && Math.abs(tee.r - rGuess) < 0.5 * rGuess ? tee.r : rGuess;
      const m = measureAt(fr, x, y, rExp, 0.7 * rExp, 1.45 * rExp);
      if (!m || m.score < 25) return { ev: 'tapfail' };
      tee = { x: m.x, y: m.y, r: m.r }; ball = { x: m.x, y: m.y, r: m.r };
      const [bx, by, bw, bh] = roiBox(); const cur = fr.roi(bx, by, bw, bh);
      const px = [], cx = ball.x - cur.x, cy = ball.y - cur.y; for (let yy = 0; yy < cur.h; yy++) for (let xx = 0; xx < cur.w; xx++) if (Math.hypot(xx - cx, yy - cy) < ball.r * 0.85) px.push(yy * cur.w + xx);
      const bm = new Uint8Array(cur.w * cur.h); for (const k of px) bm[k] = 1;
      pal = palette(cur, bm); seam0 = seamAngle(cur, px, pal);
      readyRoi = cur; prevIn = null; grabRef(fr); state = 'ready'; quiet = 0; stable = 0; launchT = t || 0;
      if (fr.small) scene = fr.small(); movedN = 0;
      if (empty && (empty.w !== cur.w || empty.h !== cur.h)) empty = null;     // 置き場所の大きさが変わったら背景を覚え直す
      return { ev: 'ready', ball: Object.assign({}, ball), tee: Object.assign({}, tee), issue: placeIssue(fr) };
    }
    // ---- (旧)置き場所の登録:ボールをタップ → ボールがなくなって落ち着いたら背景を覚える ----
    function tap(fr, x, y) {
      const R = Math.round(Math.min(fr.W, fr.H) * 0.06);
      tee = { x, y, r: 0, R };
      snap = fr.roi(Math.round(x - R), Math.round(y - R), 2 * R, 2 * R);
      state = 'remove'; quiet = 0; removeSeen = false; empty = null; ball = null; scene = fr.small ? fr.small() : null; movedN = 0;
      return { ev: 'remove' };
    }
    let thumb = null;
    function useStored(t) { tee = { x: t.x, y: t.y, r: t.r }; thumb = t.thumb || null; state = 'clear'; quiet = 0; empty = null; clearT = null; scene = null; }
    function measureFromSnap(cur) {
      const thr = 60 / S().sens, m = closeOpen(diffMask(cur, snap, thr), snap.w, snap.h);
      const cx = tee.x - snap.x, cy = tee.y - snap.y;
      let best = null; for (const b of blobs(m, snap.w, snap.h, 12)) { const dd = Math.hypot(b.x - cx, b.y - cy); if (dd < Math.max(b.bw, b.bh) && (!best || dd < best.dd)) best = Object.assign({ dd }, b); }
      if (!best || best.bw > 1.35 * best.bh + 2 || best.bh > 1.35 * best.bw + 2) return null;
      if (best.n < 0.6 * Math.PI * best.bw * best.bh / 4) return null;            // 丸く詰まっていない(クラブの影など)
      return { x: best.x + snap.x, y: best.y + snap.y, r: Math.sqrt(best.n / Math.PI) };
    }
    // 置き場所の様子:背景と比べて、丸い物があるか
    function teeState(fr) {
      const [x, y, w, h] = roiBox(); const cur = fr.roi(x, y, w, h);
      // 動いているか(前のコマとの差)
      let motion = 0; if (prevIn && prevIn.w === cur.w && prevIn.h === cur.h) { const mm = diffMask(cur, prevIn, 45); for (let k = 0; k < mm.length; k++) motion += mm[k]; } else motion = 999;
      prevIn = cur;
      if (!empty || empty.w !== cur.w || empty.h !== cur.h) return { cur, present: false, motion, still: motion < Math.max(8, 0.012 * w * h) };
      const m = closeOpen(diffMask(cur, empty, 60 / S().sens), w, h);
      const cx = tee.x - x, cy = tee.y - y; let best = null;
      for (const b of blobs(m, w, h, 6)) { const dd = Math.hypot(b.x - cx, b.y - cy); if (dd < tee.r * 1.6 && (!best || b.n > best.n)) best = Object.assign({ dd }, b); }
      let present = false, b = null;
      if (best) {
        const A = Math.PI * tee.r * tee.r, round = best.bw < 1.5 * best.bh + 2 && best.bh < 1.5 * best.bw + 2;
        present = best.n > 0.4 * A && best.n < 3.2 * A && round && best.n > 0.6 * Math.PI * best.bw * best.bh / 4;
        b = { x: best.x + x, y: best.y + y, r: Math.sqrt(best.n / Math.PI), px: best.px, n: best.n };
      }
      return { cur, present, b, motion, still: motion < Math.max(8, 0.012 * w * h), mask: m };
    }

    // ---- 追跡 ----
    function trackStep(fr, t) {
      const r0 = ball.r;
      let px, py, rad;
      if (!obs.length) { px = ball.x; py = ball.y - 5 * r0; rad = 9 * r0; }
      else {
        const L = obs[obs.length - 1], Q = obs.length >= 2 ? obs[obs.length - 2] : null;
        const vx = Q ? (L.u - Q.u) / (L.t - Q.t) : 0, vy = Q ? (L.v - Q.v) / (L.t - Q.t) : -r0 * 60 * 0.7;
        const dt = t - L.t; px = L.u + vx * dt; py = L.v + vy * dt; rad = Math.max(3.5 * L.d, 1.3 * Math.hypot(vx, vy) * dt);
      }
      // 背景を覚えている範囲の中に切り詰める
      let x0 = Math.round(px - rad), y0 = Math.round(py - rad), x1 = Math.round(px + rad), y1 = Math.round(py + rad);
      if (ref) { x0 = Math.max(x0, ref.x); y0 = Math.max(y0, ref.y); x1 = Math.min(x1, ref.x + ref.w); y1 = Math.min(y1, ref.y + ref.h); }
      if (x1 - x0 < 4 || y1 - y0 < 4) { lost++; return obs.length ? lost >= 5 : false; }
      const cur = fr.roi(x0, y0, x1 - x0, y1 - y0);
      // 背景(打つ直前のコマ)の同じ範囲
      const bg = cropRef(cur.x, cur.y, cur.w, cur.h);
      let best = null;
      if (bg) {
        const m = closeOpen(diffMask(cur, bg, 55 / S().sens), cur.w, cur.h);
        const dExp = exp || 2 * r0;
        for (const b of blobs(m, cur.w, cur.h, Math.max(6, 0.12 * dExp * dExp))) {
          const d = 2 * Math.sqrt(b.n / Math.PI), gx = b.x + cur.x, gy = b.y + cur.y;
          if (d < 0.45 * dExp || d > 1.7 * dExp) continue;                     // 大きさが急に変わる物は別物
          if (d > 1.25 * 2 * r0) continue;                                     // カメラから遠ざかるので、止まっていたときより大きくは写らない
          if (b.bw > 1.8 * b.bh + 2 || b.bh > 1.8 * b.bw + 2) continue;         // 細長い物(シャフト・クラブのぶれ)
          if (!obs.length && gy > ball.y - 0.6 * r0) continue;                 // 1点目は止まっていた所より上
          // 後ろから見ると、ボールはほぼ真上へ上がっていく(左右は±35°以内)。横へ動くクラブを除く
          if (!obs.length && Math.abs(gx - ball.x) > 2 * r0 + 0.7 * (ball.y - gy)) continue;
          if (obs.length === 1 && gy > obs[0].v + 0.3 * r0) continue;          // 2点目も上へ
          if (palDist(cur, b.px) > 110) continue;                              // ボールの色と合わない(クラブ・体)
          const dd = Math.hypot(gx - px, gy - py);
          if (!best || dd < best.dd) best = { dd, u: gx, v: gy, d, px: b.px, R: cur };
        }
      }
      if (best) {
        const sa = seamAngle(best.R, best.px, pal);
        obs.push({ t, u: best.u, v: best.v, d: best.d, seam: sa }); exp = best.d; lost = 0;
      } else lost++;
      const out = best && (best.u < 3 || best.v < 3 || best.u > fr.W - 4 || best.v > fr.H - 4);
      return obs.length >= (S().maxObs || 40) || (obs.length ? lost >= 5 : lost >= 10) || out || t - launchT > (S().maxT || 0.75);
    }
    function palDist(R, px) {
      if (!pal) return 0; let s = 0, n = 0;
      for (let j = 0; j < px.length; j += 2) { const i = px[j] * 4, d = R.d; s += Math.min(...pal.c.map(c => Math.abs(d[i] - c[0]) + Math.abs(d[i + 1] - c[1]) + Math.abs(d[i + 2] - c[2]))); n++; }
      return n ? s / n : 999;
    }
    function cropRef(x, y, w, h) {
      if (!ref) return null;
      const out = new Uint8ClampedArray(w * h * 4);
      for (let yy = 0; yy < h; yy++) { const sy = y + yy - ref.y; if (sy < 0 || sy >= ref.h) return null; const sx = x - ref.x; if (sx < 0 || sx + w > ref.w) return null; out.set(ref.d.subarray(((sy * ref.w) + sx) * 4, ((sy * ref.w) + sx + w) * 4), yy * w * 4); }
      return { d: out, x, y, w, h };
    }
    function grabRef(fr) {
      const r = ball.r, W = Math.round(26 * r), top = Math.round(ball.y - 40 * r);
      ref = fr.roi(Math.round(ball.x - W), top, 2 * W, Math.round(ball.y + 4 * r) - top);
    }

    // ---- 1コマ分 ----
    function feed(fr, t) {
      fN++;
      if (state === 'setup') return null;
      if (state === 'track') {
        if (obs.length && t - obs[obs.length - 1].t < 0.002) return null;
        if (trackStep(fr, t)) { state = 'after'; quiet = 0; return { ev: 'result', res: solve(fr) }; }
        return null;
      }
      // カメラが動いていないか(6コマごと)
      if (fr.small && fN % 6 === 0) {
        const sm = fr.small();
        if (scene) {
          const toRef = shiftOf(sm, scene), toPrev = shiftOf(sm, lastSmall);
          if (state !== 'moved') {
            if (movedBy(toRef) && state !== 'armed') movedN++; else movedN = 0;
            if (movedN >= 2) { prevState = state === 'ready' ? 'wait' : state; state = 'moved'; calmN = 0; lastSmall = sm; return { ev: 'moved' }; }
          } else {
            if (toRef && !toRef.dx && !toRef.dy && toRef.zero < 0.05) { state = prevState === 'remove' ? 'remove' : 'wait'; stable = 0; prevIn = null; lastSmall = sm; return { ev: 'back', state }; }
            calmN = toPrev && !movedBy(toPrev) && toPrev.zero < 0.05 ? calmN + 1 : 0;
            // 動いたあと別の向きで止まった:置き場所の登録からやり直す
            if (calmN >= 15) { state = 'setup'; tee = null; empty = null; ball = null; scene = null; lastSmall = sm; return { ev: 'retap' }; }
          }
        } else if (state === 'wait' || state === 'ready') scene = sm;
        lastSmall = sm;
      }
      if (state === 'moved') return null;
      const ts = teeState(fr);
      if (state === 'clear' && clearT == null) clearT = t;
      if (state === 'clear' && t - clearT > 4) { state = 'setup'; tee = null; return { ev: 'retap' }; }   // 前に覚えた置き場所と違う
      if (state === 'remove' || state === 'clear' || state === 'after') {
        // 置き場所が空になって落ち着くのを待つ → 背景として覚える
        if (state === 'remove') {
          const [x, y, w, h] = [snap.x, snap.y, snap.w, snap.h];
          const cur = fr.roi(x, y, w, h); const m = diffMask(cur, snap, 60 / S().sens);
          // タップした点のまわり(半径6px)が変わった=ボールがなくなった
          const cx = Math.round(tee.x - x), cy = Math.round(tee.y - y); let ch = 0, nn = 0;
          for (let yy = cy - 6; yy <= cy + 6; yy++) for (let xx = cx - 6; xx <= cx + 6; xx++) { if ((xx - cx) ** 2 + (yy - cy) ** 2 > 36 || xx < 0 || yy < 0 || xx >= w || yy >= h) continue; nn++; ch += m[yy * w + xx]; }
          const gone = nn && ch / nn > 0.6;
          if (gone && ts.still) quiet++; else quiet = 0;
          removeSeen = gone;
          if (removeSeen && quiet >= 18) {
            const mb = measureFromSnap(cur);
            if (!mb || mb.r < 3 || mb.r > Math.min(fr.W, fr.H) * 0.06) { quiet = 0; return null; }   // クラブが重なっているだけ等。待ち続ける
            tee = { x: mb.x, y: mb.y, r: mb.r };
            const [x2, y2, w2, h2] = roiBox(); empty = fr.roi(x2, y2, w2, h2); thumb = thumbOf(empty); prevIn = null; state = 'wait'; stable = 0; if (fr.small) scene = fr.small();
            return { ev: 'teeset', tee: Object.assign({ thumb }, tee) };
          }
          return null;
        }
        if (ts.still) quiet++; else quiet = 0;
        if (quiet >= 18 && state === 'after' && readyRoi && teeChanged(ts.cur) < 0.15) { state = 'ready'; return { ev: 'ready', ball: Object.assign({}, ball) }; }   // 打っていなかった
        if (quiet >= 18 && empty && state === 'after') {
          // 前に覚えた空の置き場所と同じに見えるときだけ、新しい背景にする(クラブや足が残っているときは待つ)
          const m = diffMask(ts.cur, empty, 60 / S().sens); let ch = 0; for (let k = 0; k < m.length; k++) ch += m[k];
          if (ch > 0.04 * m.length) return null;
        }
        if (quiet >= 18) {
          // 'clear':アプリ再開時。保存した空の置き場所の縮小画像と同じに見えるときだけ、背景として使う
          if (state === 'clear' && thumb && thumbDiff(thumbOf(ts.cur), thumb) > 28) { quiet = 0; return { ev: 'notempty' }; }
          empty = ts.cur; thumb = thumbOf(empty); state = 'wait'; stable = 0; if (fr.small) scene = fr.small();
          return { ev: 'empty', thumb };
        }
        return null;
      }
      if (state === 'wait') {
        cand = ts.present ? ts.b : null;
        if (ts.present && ts.still) stable++; else stable = 0;
        if (stable >= READY_FRAMES) {
          const b = ts.b; ball = { x: b.x, y: b.y, r: b.r };
          const bm = new Uint8Array(ts.cur.w * ts.cur.h); for (const k of b.px) bm[k] = 1;
          pal = palette(ts.cur, bm); seam0 = seamAngle(ts.cur, b.px, pal);
          readyRoi = ts.cur; grabRef(fr); state = 'ready'; quiet = 0;
          return { ev: 'ready', ball: Object.assign({}, ball), issue: placeIssue(fr) };
        }
        return null;
      }
      if (state === 'armed') {
        // クラブが前に来てボールが隠れている(構え)か、打ったあと。飛んでいくボールが見つかれば追跡、ボールがまた見えれば元に戻る
        if (teeChanged(ts.cur) < 0.15) { if (++back >= 3) { state = 'ready'; back = 0; } return null; }
        back = 0;
        trackStep(fr, t);
        if (obs.length && lost >= 2) { obs = []; lost = 0; }                   // 続かなかった:クラブなど
        if (obs.length >= 3) {
          // 3点とも上へ進み、大きさがそろっていればボール
          const [a0, a1, a2] = obs, up1 = a0.v - a1.v, up2 = a1.v - a2.v, ds = Math.max(a0.d, a1.d, a2.d) / Math.min(a0.d, a1.d, a2.d);
          if (up1 > 0.25 * ball.r && up2 > 0.1 * ball.r && ds < 1.4) { state = 'track'; launchT = obs[0].t; lost = 0; return { ev: 'track' }; }
          obs = []; lost = 0;
        }
        if (t - armT > 12) { state = 'wait'; stable = 0; return { ev: 'lostball' }; }
        return null;
      }
      if (state === 'ready') {
        // ボールの所が大きく変わった=打った、またはクラブがボールの前に来た(後ろから見ると構えで隠れる)
        if (teeChanged(ts.cur) > 0.5) { state = 'armed'; armT = t; back = 0; obs = []; lost = 0; exp = 2 * ball.r; return null; }
        // 体が止まっているときだけ、追跡用の背景を新しくする(部屋の明るさの変化に追従)
        if (ts.still) { if (++quiet % 30 === 0) grabRef(fr); } else quiet = 0;
        return null;
      }
      return null;
    }
    function teeChanged(cur) {
      const m = diffMask(cur, readyRoi, 60 / S().sens), cx = ball.x - cur.x, cy = ball.y - cur.y, R = ball.r * 0.8;
      let n = 0, ch = 0; for (let y = Math.floor(cy - R); y <= cy + R; y++) for (let x = Math.floor(cx - R); x <= cx + R; x++) { if (Math.hypot(x - cx, y - cy) > R || x < 0 || y < 0 || x >= cur.w || y >= cur.h) continue; n++; ch += m[y * cur.w + x]; }
      return n ? ch / n : 0;
    }
    function placeIssue(fr) {
      const dia = 2 * ball.r / Math.min(fr.W, fr.H);
      if (dia > 0.08) return 'near';
      if (dia < 0.012) return 'far';
      return null;
    }

    // ---- 軌道の当てはめ ----
    function solve(fr) {
      const o = S(), D = (o.diamMM || 42) / 1000, Z0 = o.dist || 1.93;
      const res = { n: obs.length, obs: obs.slice() };
      // ボールが戻ってきた(打っていない)・追えなかった
      if (obs.length < 5) { res.ok = false; res.why = obs.length ? 'short' : 'none'; return res; }
      const f = (2 * ball.r) * Z0 / D, cx = fr.W / 2, cy = fr.H / 2;
      const ray = (u, v) => { const x = u - cx, y = v - cy, n = Math.hypot(x, y, f); return [x / n, y / n, f / n]; };
      const r0 = ray(ball.x, ball.y), P0 = [r0[0] * Z0, r0[1] * Z0, r0[2] * Z0];
      let up = o.up && Math.hypot(...o.up) > 0.5 ? o.up : [0, -1, 0]; const un = Math.hypot(...up); up = up.map(v => v / un);
      const g = up.map(v => -9.81 * v);
      const prof = PHYS.plasticProfile({ massG: o.massG || 5, diamMM: o.diamMM || 42, dragScale: o.drag || 1 });
      const kA = 0.5 * 1.2 * Math.PI * prof.r * prof.r / prof.m;
      // 速度ベクトルに垂直で「上」側を向く揚力。axis(rad)だけ進行方向まわりに傾ける
      function integ(p, ts, spin, axis, dScale) {
        const [t0, vx0, vy0, vz0] = p; let pos = P0.slice(), vel = [vx0, vy0, vz0], t = t0, w = spin * 2 * Math.PI / 60;
        const dt = 1 / 480, out = []; let j = 0; const order = ts.map((tt, i) => [tt, i]).sort((a, b) => a[0] - b[0]);
        const P2 = Object.assign({}, prof, { cdScale: prof.cdScale * (dScale || 1) });
        const acc = (v) => {
          const sp = Math.hypot(v[0], v[1], v[2]) || 1e-9, c = PHYS.coeffs(sp, w, P2);
          const dot = up[0] * v[0] + up[1] * v[1] + up[2] * v[2]; let l = [up[0] - dot * v[0] / (sp * sp), up[1] - dot * v[1] / (sp * sp), up[2] - dot * v[2] / (sp * sp)];
          const ln = Math.hypot(...l) || 1; l = l.map(q => q / ln);
          if (axis) { const vh = v.map(q => q / sp), cr = [vh[1] * l[2] - vh[2] * l[1], vh[2] * l[0] - vh[0] * l[2], vh[0] * l[1] - vh[1] * l[0]], ca = Math.cos(axis), sa = Math.sin(axis); l = [l[0] * ca + cr[0] * sa, l[1] * ca + cr[1] * sa, l[2] * ca + cr[2] * sa]; }
          return [0, 1, 2].map(i => g[i] - kA * c.cd * sp * v[i] + kA * c.cl * sp * sp * l[i]);
        };
        while (j < order.length) {
          while (j < order.length && order[j][0] <= t) { out[order[j][1]] = pos.slice(); j++; }
          if (j >= order.length) break;
          const a1 = acc(vel), mv = vel.map((q, i) => q + a1[i] * dt / 2), a2 = acc(mv);
          pos = pos.map((q, i) => q + mv[i] * dt); vel = vel.map((q, i) => q + a2[i] * dt); t += dt; w *= Math.exp(-dt / prof.spinTau);
          if (t - t0 > 3) break;
        }
        for (let i = 0; i < ts.length; i++) if (!out[i]) out[i] = pos.slice();
        return out;
      }
      function resid(p, use, spin, axis, dScale) {
        const X = integ(p, use.map(q => q.t), spin, axis, dScale), r = [];
        use.forEach((q, i) => { const P = X[i], z = Math.max(0.05, P[2]), w = q.w == null ? 1 : q.w, wd = q.wd == null ? 1 : q.wd; r.push(w * (cx + f * P[0] / z - q.u), w * (cy + f * P[1] / z - q.v), wd * 1.5 * (f * D / Math.hypot(...P) - q.d)); });
        return r;
      }
      // レーベンバーグ・マーカート法(数値微分)
      function lm(p, fn, iters) {
        let lam = 1e-2, r = fn(p), e = r.reduce((s, v) => s + v * v, 0);
        for (let it = 0; it < iters; it++) {
          const J = p.map((_, k) => { const h = Math.max(1e-4, Math.abs(p[k]) * 1e-3); const q = p.slice(); q[k] += h; const r2 = fn(q); return r2.map((v, i) => (v - r[i]) / h); });
          const n = p.length, A = Array.from({ length: n }, () => new Array(n).fill(0)), b = new Array(n).fill(0);
          for (let i = 0; i < n; i++) { for (let k = 0; k < n; k++) { let s = 0; for (let m = 0; m < r.length; m++) s += J[i][m] * J[k][m]; A[i][k] = s; } let s = 0; for (let m = 0; m < r.length; m++) s += J[i][m] * r[m]; b[i] = -s; }
          let improved = false;
          for (let tries = 0; tries < 6; tries++) {
            const M = A.map((row, i) => row.map((v, k) => v + (i === k ? lam * (v + 1e-9) : 0)));
            const dp = solveLin(M, b); if (!dp) { lam *= 10; continue; }
            const q = p.map((v, i) => v + dp[i]), r2 = fn(q), e2 = r2.reduce((s, v) => s + v * v, 0);
            if (e2 < e) { p = q; r = r2; e = e2; lam = Math.max(1e-6, lam / 3); improved = true; break; } else lam *= 8;
          }
          if (!improved) break;
        }
        return { p, rms: Math.sqrt(e / r.length) };
      }
      // 初期値:最初の数点を3Dにして、止まっていた所からの速度を出す
      const P3 = (q) => { const R = f * D / q.d, rr = ray(q.u, q.v); return rr.map(v => v * R); };
      const k2 = Math.min(3, obs.length - 1), A0 = P3(obs[0]), A2 = P3(obs[k2]);
      let vel = A2.map((v, i) => (v - A0[i]) / (obs[k2].t - obs[0].t));
      const sp0 = Math.hypot(...vel) || 1, t0 = obs[0].t - Math.hypot(...A0.map((v, i) => v - P0[i])) / sp0;
      const use = obs.slice(0, Math.min(obs.length, 14)).map(q => Object.assign({}, q));
      // 大きさ(=距離)の外れ値:遠ざかるほど小さくなり、距離はほぼ一定の速さで増える。1/直径 を直線で当てはめ(最小メジアン)、12%以上ずれた点の大きさは使わない
      {
        const R = use.map(q => 1 / q.d), T = use.map(q => q.t); let best = null;
        for (let i = 0; i < use.length; i++) for (let j = i + 2; j < use.length; j++) {
          const b = (R[j] - R[i]) / (T[j] - T[i]), a = R[i] - b * T[i];
          const e = R.map((r, k) => Math.abs(r - (a + b * T[k])) / r).sort((x, y) => x - y)[use.length >> 1];
          if (b > 0 && (!best || e < best.e)) best = { a, b, e };
        }
        if (best) use.forEach((q, k) => { if (Math.abs(R[k] - (best.a + best.b * T[k])) / R[k] > 0.12) q.wd = 0; });
        use.forEach(q => { if (q.d > 2.1 * ball.r) q.wd = 0; });
      }
      let p = [t0, ...vel], spin = 0, fit = null;
      const launchOf = (pp) => {
        const v = pp.slice(1), sp = Math.hypot(...v), fwd0 = [0, 0, 1], dot = fwd0[0] * up[0] + fwd0[1] * up[1] + fwd0[2] * up[2];
        let fw = fwd0.map((q, i) => q - dot * up[i]); const fn = Math.hypot(...fw); fw = fw.map(q => q / fn);
        const rt = [up[1] * fw[2] - up[2] * fw[1], up[2] * fw[0] - up[0] * fw[2], up[0] * fw[1] - up[1] * fw[0]];
        const vu = v[0] * up[0] + v[1] * up[1] + v[2] * up[2], vf = v[0] * fw[0] + v[1] * fw[1] + v[2] * fw[2], vr = v[0] * rt[0] + v[1] * rt[1] + v[2] * rt[2];
        // rt は up×fw。カメラ座標で右(+x)を向くように符号をそろえる
        const sgn = rt[0] >= 0 ? 1 : -1;
        return { speed: sp, angle: Math.atan2(vu, Math.hypot(vf, vr)) * 180 / Math.PI, dir: Math.atan2(sgn * vr, vf) * 180 / Math.PI };
      };
      // 境目の傾き → 回転軸の傾き
      let axis = 0, axisN = 0;
      if (seam0 != null) { let s = 0, c = 0; for (const q of obs) if (q.seam != null && q.d >= Math.max(14, 1.1 * ball.r)) { const d = q.seam - seam0; s += Math.sin(d); c += Math.cos(d); axisN++; } if (axisN >= 5 && Math.abs(Math.cos(seam0)) > 0.85) { const a = Math.atan2(s, c), R = Math.hypot(s, c) / axisN; if (R > 0.8) axis = clamp(a, -0.35, 0.35); } }
      for (let pass = 0; pass < 3; pass++) {
        fit = lm(p, (q) => resid(q, use, spin, axis, 1), 25); p = fit.p;
        const L = launchOf(p); spin = PHYS.plasticLaunch(L.speed, Math.max(1, L.angle), { massG: o.massG, diamMM: o.diamMM, cor: o.cor, attack: o.attack }).spin;
        // 外れた点(クラブと重なって大きく写ったコマなど)を軽くして、もう一度当てはめる
        const rr = resid(p, use.map(q => Object.assign({}, q, { w: 1, wd: q.wd === 0 ? 0 : 1 })), spin, axis, 1);
        const ep = use.map((q, i) => Math.hypot(rr[3 * i], rr[3 * i + 1])), ed = use.map((q, i) => Math.abs(rr[3 * i + 2]));
        const med = (a) => { const b = a.slice().sort((x, y) => x - y); return b[b.length >> 1] || 1; };
        const mp = Math.max(0.7, med(ep)), md = Math.max(0.7, med(ed));
        use.forEach((q, i) => { q.w = ep[i] > 3 * mp ? 3 * mp / ep[i] : 1; if (q.wd !== 0) q.wd = ed[i] > 3 * md ? 3 * md / ed[i] : 1; });
      }
      fit = { p, rms: Math.sqrt(resid(p, use, spin, axis, 1).reduce((a, v) => a + v * v, 0) / (3 * use.length)) };
      const L = launchOf(p);
      Object.assign(res, { ok: true, speed: L.speed, angle: L.angle, dir: L.dir, spin, axis: axis * 180 / Math.PI, rms: fit.rms, impactT: p[0], f, launchT });
      // 前半だけ・後半だけで当てはめても同じ速さになるか(ならなければ、別の物を追ったか大きさが乱れている)
      if (use.length >= 10) {
        const h1 = use.slice(0, Math.ceil(use.length * 0.7)), h2 = use.slice(Math.floor(use.length * 0.3));
        const s1 = launchOf(lm(p, (q) => resid(q, h1, spin, axis, 1), 15).p).speed, s2 = launchOf(lm(p, (q) => resid(q, h2, spin, axis, 1), 15).p).speed;
        res.spread = Math.abs(s1 - s2) / L.speed;
        if (res.spread > 0.4) { Object.assign(res, { ok: false, why: 'odd', speed: L.speed, angle: L.angle, dir: L.dir, rms: fit.rms, impactT: p[0], f }); return res; }
      }
      if (!(L.speed > 0.8 && L.speed < 15 && L.angle > 2 && L.angle < 80 && Math.abs(L.dir) < 30) || fit.rms > Math.max(4, 0.5 * ball.r)) { res.ok = false; res.why = 'odd'; return res; }
      // 長く追えたら、空気抵抗の倍率も合わせる(0.3秒以上)
      // 着地(画面の上で下へ動いていたのが止まる・跳ね返る)までの点で、空気抵抗の倍率を合わせる
      let cut = obs.length, top = 0;
      for (let i = 1; i < obs.length; i++) { if (obs[i].v < obs[top].v) top = i; if (i > top + 2 && obs[i].v < obs[i - 1].v - 0.5 && obs[i - 1].v >= obs[i - 2].v) { cut = i - 1; break; } }
      res.bounce = cut < obs.length ? cut : -1;
      if (cut >= 16 && obs[cut - 1].t - obs[0].t > 0.28) {
        // 着地までの長い軌道で、打ち出しと空気抵抗をいっしょに当てはめ直す(点が多いぶん、速さが安定する)
        const all = obs.slice(0, Math.min(cut, 90)).map((q, i) => Object.assign({}, q, i < use.length ? { w: use[i].w, wd: use[i].wd } : {}));
        all.forEach(q => { if (q.d > 2.1 * ball.r) q.wd = 0; });
        let best = null;
        for (const ds of [0.4, 0.5, 0.6, 0.75, 0.9, 1.1, 1.35, 1.7, 2.0]) {
          const pd = lm(p, (q) => resid(q, all, spin, axis, ds), 8);
          if (!best || pd.rms < best.rms) best = { ds, rms: pd.rms, p: pd.p };
        }
        res.dragFit = best.ds; res.dragRms = best.rms;
        const L2 = launchOf(best.p);
        if (best.rms < Math.max(4, 0.5 * ball.r) && L2.speed > 0.8 && L2.speed < 15) {
          res.short = { speed: res.speed, angle: res.angle, dir: res.dir };
          Object.assign(res, { speed: L2.speed, angle: L2.angle, dir: L2.dir, impactT: best.p[0], long: true });
          res.spin = PHYS.plasticLaunch(L2.speed, Math.max(1, L2.angle), { massG: o.massG, diamMM: o.diamMM, cor: o.cor, attack: o.attack }).spin;
        }
      }
      return res;
    }
    return {
      feed, tap, tapReady, useStored,
      reset() { state = tee ? 'clear' : 'setup'; quiet = 0; },
      get state() { return state; }, get tee() { return tee; }, get ball() { return ball; }, get obs() { return obs; },
      get cand() { return state === 'wait' ? cand : null; }, get progress() { return state === 'wait' ? Math.min(1, stable / READY_FRAMES) : state === 'ready' || state === 'armed' ? 1 : 0; },
      get emptyReady() { return !!empty; }, get thumb() { return thumb; }
    };
  }
  return { session, findCircle };
})();


const $ = (id) => document.getElementById(id);
// 予期しないエラーは画面に短く出す(原因を調べるため。外部には送らない)
window.addEventListener('error', (e) => { try { toast('エラー:' + String(e.message || '').slice(0, 100)); } catch (x) {} });
window.addEventListener('unhandledrejection', (e) => { try { toast('エラー:' + String((e.reason && e.reason.message) || e.reason || '').slice(0, 100)); } catch (x) {} });
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
const VIEWS = ['roleView', 'camView', 'playView'];
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
  else { App.start(); Net.host(); Power.keepAwake(); }
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
   CAMERA (iPhone): ボールの後ろ・低い位置から撮って計測する(DTL)
   ====================================================================== */
const Cam = (() => {
  const vid = $('vid'), ov = $('overlay'), octx = ov.getContext('2d');
  const scratch = document.createElement('canvas'); const sctx = scratch.getContext('2d', { willReadFrequently: true });
  let VW = 0, VH = 0, stream = null, wake = null, running = false, sess = null;
  let facing = store.get('facing', 'environment') === 'user' ? 'user' : 'environment';
  let state = 'off', lastSent = '', info = { next: '', lie: '' }, issue = null, cooldownUntil = 0, lastRes = null;
  let lastTouch = Date.now(), lastActive = Date.now(), dark = false;
  const ftimes = [];
  const IDLE_DARK = 20000, IDLE_STOP = 10 * 60000;
  const S = { dist: store.get('dist', 1.8), diam: store.get('diam', 42), mass: store.get('mass', 5), cor: store.get('cor', 0.55), attack: store.get('attack', -3), sens: store.get('sens', 1), drag: store.get('drag', 1) };
  let lastShot = null;

  // ---- 傾きセンサー(重力の向き)----
  // 端末の座標 → 画面の座標 → カメラの座標(右+x・下+y・前+z)の「上向き」の単位ベクトル
  let gAvg = null, motionOK = false;
  function onMotion(e) {
    const a = e.accelerationIncludingGravity; if (!a || a.x == null) return;
    const v = [a.x, a.y, a.z]; motionOK = true;
    gAvg = gAvg ? gAvg.map((q, i) => q * 0.92 + v[i] * 0.08) : v;
  }
  function upCam() {
    if (!gAvg) return null;
    const n = Math.hypot(...gAvg); if (n < 5) return null;
    let [x, y, z] = gAvg.map(q => q / n);
    const ang = ((screen.orientation && screen.orientation.angle) || window.orientation || 0) * Math.PI / 180;
    const xs = x * Math.cos(ang) + y * Math.sin(ang), ys = -x * Math.sin(ang) + y * Math.cos(ang);
    // 外カメラは画面の裏側を、インカメラは画面の表側を見る
    let u = facing === 'user' ? [-xs, -ys, z] : [xs, -ys, -z];
    if (u[1] > 0) u = u.map(q => -q);                    // 端末によって符号が逆。カメラは立てて使うので「上」は画面の上側
    return u;
  }
  const pitchDeg = () => { const u = upCam(); return u ? Math.asin(clamp(u[2], -1, 1)) * 180 / Math.PI : null; };
  async function askMotion() {
    try {
      if (typeof DeviceMotionEvent !== 'undefined' && typeof DeviceMotionEvent.requestPermission === 'function') {
        const r = await DeviceMotionEvent.requestPermission(); if (r !== 'granted') return false;
      }
      window.addEventListener('devicemotion', onMotion);
      return true;
    } catch (e) { return false; }
  }

  // ---- 設定 ----
  $('carryApply').onclick = () => {
    const cm = Number($('carryCm').value);
    if (!lastShot) { toast('先に1球打ってください'); return; }
    if (!(cm >= 20 && cm <= 3000)) { toast('落ちた距離を20〜3000cmで入力してください'); return; }
    const flat = { allGreen: false, shapes: [], pin: { x: 999, z: 0 }, stimp: 10, slope: { x: 0, z: 0 } };
    const carryAt = (ds) => PHYS.simulate(lastShot, flat, { x: 0, z: 0 }, 0, PHYS.plasticProfile({ massG: S.mass, diamMM: S.diam, dragScale: ds })).carry;
    let lo = 0.3, hi = 2.5;
    if (carryAt(lo) < cm / 100 || carryAt(hi) > cm / 100) { toast('この距離には合わせられません。計測値か入力を確認してください'); return; }
    for (let i = 0; i < 30; i++) { const mid = (lo + hi) / 2; if (carryAt(mid) > cm / 100) lo = mid; else hi = mid; }
    S.drag = +((lo + hi) / 2).toFixed(3); store.set('drag', S.drag); showDrag();
    toast(`空気抵抗の補正を×${S.drag.toFixed(2)}にしました`);
  };
  const showDrag = () => { $('oDrag').textContent = '×' + S.drag.toFixed(2); };
  $('dragReset').onclick = () => { S.drag = 1; store.set('drag', 1); showDrag(); toast('空気抵抗の補正を元に戻しました'); };
  [['sDist','oDist','dist',v=>v.toFixed(2)+' m'],['sDiam','oDiam','diam',v=>v.toFixed(1)+' mm'],['sMass','oMass','mass',v=>v.toFixed(1)+' g'],['sCor','oCor','cor',v=>v.toFixed(2)],
   ['sAttack','oAttack','attack',v=>v.toFixed(1)+'°'],['sSens','oSens','sens',v=>'×'+v.toFixed(2)]]
  .forEach(([s,o,k,f]) => { const e=$(s); e.value=S[k]; $(o).textContent=f(+e.value); e.oninput=()=>{ S[k]=+e.value; $(o).textContent=f(+e.value); store.set(k,+e.value); }; });
  showDrag();
  $('dropApply').onclick = () => {
    const h = Number($('dropCm').value);
    if (!(h > 0 && h < 100)) { toast('跳ね返った高さを1〜99cmで入力してください'); return; }
    const e = Math.round(Math.sqrt(h / 100) * 100) / 100;
    S.cor = clamp(e, 0.3, 0.85); store.set('cor', S.cor); $('sCor').value = S.cor; $('oCor').textContent = S.cor.toFixed(2);
    toast(`反発係数を${S.cor.toFixed(2)}にしました`);
  };

  // ---- 状態の表示 ----
  const TEXT = {
    off: ['カメラを開始してください', 'ボールの真後ろ1.8m・床に近い低い位置に、iPhoneを縦向きで置きます'],
    setup: ['ボールをタップ', 'ボールを置いて、映像の中のボールをタップすると、すぐ「打ってOK」になります'],
    remove: ['ボールをどけてください', '何もない置き場所を覚えます。ボールを手でどけて、少し待ってください(そのまま1球打ってもOK)'],
    moved: ['カメラが動いています', '三脚などに固定してください。止まると再開します'],
    clear: ['置き場所を確認中', 'ボールがない状態で少し待ってください'],
    wait: ['ボールを置いてください', '置いたら映像のボールをタップ(点線の丸の所に置けば自動でも見つけます)'],
    ready: ['打ってOK', ''],
    track: ['計測中…', ''],
    done: ['計測しました', 'iPadを見てください'],
    error: ['もう一度どうぞ', '']
  };
  const ISSUE = {
    near: ['カメラが近すぎます', 'ボールから1.8mくらい離してください'],
    far: ['カメラが遠すぎます', 'ボールが小さすぎます。1.8mくらいまで近づけてください'],
    landscape: ['iPhoneを縦向きにしてください', '縦向きのほうが、上がっていくボールを長く追えます']
  };
  function infoLine() { return info.lie ? `${info.lie}から打つ` : ''; }
  function setState(s, sub) {
    state = s;
    const t = s === 'adjust' ? ISSUE[issue] : (TEXT[s] || ['', '']);
    $('camStatus').dataset.state = s === 'adjust' || s === 'moved' ? 'error' : s === 'setup' || s === 'remove' || s === 'clear' ? 'tap' : s;
    $('stateText').textContent = t[0];
    $('stateSub').textContent = sub || (s === 'ready' && infoLine()) || t[1];
    $('boText').textContent = t[0];
    pushStatus();
  }
  function pushStatus(force) {
    const st = state === 'ready' ? 'ready' : state === 'track' ? 'track' : state === 'off' ? 'off' : state === 'adjust' ? 'adjust' : 'wait';
    const key = st + (st === 'adjust' ? issue : '');
    if (!force && key === lastSent) return;
    lastSent = key; Net.send(st === 'adjust' ? { type: 'status', state: st, issue: issue === 'far' ? 'far' : issue === 'landscape' ? 'portrait' : 'near' } : { type: 'status', state: st });
  }
  function onInfo(m) {
    info.next = '';
    info.lie = m.lie === 'ラフ' || m.lie === 'マット' ? m.lie : '';
    if (state === 'ready') setState(state);
  }
  function setButtons() { $('camStart').hidden = running; $('camStop').hidden = !running; }
  function showTilt() {
    const p = pitchDeg();
    $('tiltOut').textContent = p == null ? (motionOK ? '測定中…' : '取れません(水平として計算)') : `${p >= 0 ? '上向き' : '下向き'} ${Math.abs(p).toFixed(1)}°`;
  }

  // ---- 映像の一部を元の解像度で読む ----
  function roi(x, y, w, h) {
    x = Math.round(x); y = Math.round(y); w = Math.round(w); h = Math.round(h);
    const x0 = clamp(x, 0, VW - 1), y0 = clamp(y, 0, VH - 1), x1 = clamp(x + w, 1, VW), y1 = clamp(y + h, 1, VH);
    const ww = Math.max(1, x1 - x0), hh = Math.max(1, y1 - y0);
    if (scratch.width < ww) scratch.width = ww; if (scratch.height < hh) scratch.height = hh;
    sctx.drawImage(vid, x0, y0, ww, hh, 0, 0, ww, hh);
    return { d: sctx.getImageData(0, 0, ww, hh).data, x: x0, y: y0, w: ww, h: hh };
  }
  // 画面全体の縮小画像(カメラが動いたかの確認用。24×40マス)
  const tiny = document.createElement('canvas'); const tctx = tiny.getContext('2d', { willReadFrequently: true });
  function small() { const w = VW > VH ? 40 : 24, h = VW > VH ? 24 : 40; tiny.width = w; tiny.height = h; tctx.drawImage(vid, 0, 0, w, h); return { d: tctx.getImageData(0, 0, w, h).data, w, h }; }
  const frameObj = { get W() { return VW; }, get H() { return VH; }, roi, small };
  const teeKey = () => `tee_${facing}_${VW}x${VH}`;
  // 測ったボールの大きさから、カメラの焦点距離(画面の縦向き1080px幅あたり)を覚える。次のタップの見込みに使う
  const fKey = () => 'fpx_' + facing;
  function learnF(b) { if (!b || !b.r || !VW) return; const f = (2 * b.r) * S.dist / (S.diam / 1000) * 1080 / Math.min(VW, VH); if (f > 500 && f < 4000) { const old = store.get(fKey(), null); store.set(fKey(), old ? old * 0.7 + f * 0.3 : f); } }
  function newSession() {
    sess = DTL.session(() => ({ fpx: store.get(fKey(), null), dist: S.dist, diamMM: S.diam, massG: S.mass, cor: S.cor, attack: S.attack, drag: S.drag, sens: S.sens, up: upCam(), maxObs: 100, maxT: 1.6 }));
    const t = store.get(teeKey(), null);
    if (t && t.r > 2) { sess.useStored(t); setState('clear'); } else setState('setup');
  }

  // 条件をゆるめながら順に試す(カメラによっては高い設定を受け付けない)
  async function getCam(list) {
    let last = null;
    for (const c of list) { try { return await navigator.mediaDevices.getUserMedia(c); } catch (e) { last = e; if (e && e.name === 'NotAllowedError') break; } }
    throw last;
  }
  async function start() {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { toast('このブラウザではカメラを使えません(Safariで開いてください)'); return; }
    // 「カメラを開始」を押したときに、まず傾きセンサーの許可を聞き、そのあとカメラの許可を聞く(2つの確認が重ならないように)
    const motionOK0 = await askMotion();
    try {
      stream = await getCam([
        { audio: false, video: { facingMode: { ideal: facing }, width: { ideal: 1920 }, height: { ideal: 1080 }, frameRate: { ideal: 60, max: 60 } } },
        { audio: false, video: { facingMode: { ideal: facing }, width: { ideal: 1280 }, height: { ideal: 720 }, frameRate: { ideal: 60 } } },
        { audio: false, video: { facingMode: facing } }
      ]);
    } catch (e) { setState('error', `カメラを開けませんでした(${e && e.name || ''})。設定 → Safari → カメラ を確認してください`); return; }
    vid.srcObject = stream;
    try { await vid.play(); } catch (e) {}
    await new Promise(r => { if (vid.videoWidth) r(); else vid.onloadedmetadata = () => r(); });
    VW = vid.videoWidth; VH = vid.videoHeight; $('stage').style.aspectRatio = VW + ' / ' + VH;
    $('stageEmpty').hidden = true;
    if (!motionOK0) toast('傾きセンサーを使えないため、iPhoneは水平として計算します');
    try { if ('wakeLock' in navigator) wake = await navigator.wakeLock.request('screen'); } catch (e) { wake = null; }
    running = true; lastTouch = lastActive = Date.now(); setButtons();
    newSession(); loop();
  }
  function stop(msg) {
    running = false;
    if (stream) { stream.getTracks().forEach(t => t.stop()); stream = null; }
    vid.srcObject = null;
    window.removeEventListener('devicemotion', onMotion); gAvg = null;
    try { if (wake) wake.release(); } catch (e) {} wake = null;
    $('stageEmpty').hidden = false; setButtons(); setDark(false);
    octx.clearRect(0, 0, ov.width, ov.height);
    setState('off', msg);
  }
  $('camStart').onclick = start;
  // 外カメラ/インカメラの切り替え
  const showFacing = () => { $('camFlip').textContent = facing === 'user' ? '外カメラに切り替え' : 'インカメラに切り替え'; };
  $('camFlip').onclick = async () => {
    facing = facing === 'user' ? 'environment' : 'user'; store.set('facing', facing); showFacing();
    if (running) { stop(); await new Promise(r => setTimeout(r, 300)); await start(); }
    else toast(facing === 'user' ? 'インカメラを使います。「カメラを開始」を押してください' : '外カメラを使います。「カメラを開始」を押してください');
  };
  showFacing();
  $('camStop').onclick = () => stop();
  $('reTee').onclick = () => { if (!running) { toast('先に「カメラを開始」を押してください'); return; } store.set(teeKey(), null); newSession(); setDark(false); $('stage').scrollIntoView({ behavior: 'smooth', block: 'center' }); };
  document.addEventListener('visibilitychange', () => { if (document.hidden && running) stop('画面を離れたのでカメラを止めました。「カメラを開始」で再開します'); });
  window.addEventListener('pagehide', () => { if (running) stop(); });

  // 省電力
  function setDark(on) { dark = on; $('blackout').hidden = !on; }
  document.addEventListener('pointerdown', () => { lastTouch = lastActive = Date.now(); if (dark) setDark(false); }, true);
  setInterval(() => {
    if (!running || role !== 'camera') return;
    const now = Date.now(); showTilt();
    if (now - lastActive > IDLE_STOP) { stop('10分間打たなかったので、カメラを休止しました。「カメラを開始」で再開します'); return; }
    if (!dark && state !== 'setup' && state !== 'remove' && state !== 'moved' && state !== 'adjust' && now - lastTouch > IDLE_DARK) setDark(true);
    if (state === 'ready' || state === 'adjust') pushStatus(true);
  }, 1000);

  // 置き場所の登録:映像のボールをタップ
  function videoBox() {
    const W = ov.width, H = ov.height, va = (VW || 9) / (VH || 16), ca = W / H;
    if (va > ca) { const h = W / va; return { x: 0, y: (H - h) / 2, w: W, h }; }
    const w = H * va; return { x: (W - w) / 2, y: 0, w, h: H };
  }
  ov.addEventListener('pointerup', (e) => {
    // 映像のボールをタップすると、いつでも置き場所を登録し直せる(計測中を除く)
    if (!running || !sess || !VW || sess.state === 'track' || sess.state === 'armed') return;
    drawOverlay();                                       // 重ね絵の大きさを画面に合わせてから位置を計算する
    const rect = ov.getBoundingClientRect(), b = videoBox();
    const nx = ((e.clientX - rect.left) * devicePixelRatio - b.x) / b.w, ny = ((e.clientY - rect.top) * devicePixelRatio - b.y) / b.h;
    if (nx < 0 || nx > 1 || ny < 0 || ny > 1) return;
    const ev = sess.tapReady(frameObj, nx * VW, ny * VH, performance.now() / 1000);
    if (ev.ev === 'ready') { learnF(ev.ball); store.set(teeKey(), Object.assign({}, ev.tee)); issue = VW > VH ? 'landscape' : ev.issue || null; lastTouch = Date.now(); setState(issue === 'near' || issue === 'far' ? 'adjust' : 'ready'); }
    else toast('ボールが見つかりませんでした。ボールの真ん中をタップしてください');
  });

  // ---- 結果 ----
  const WHY = { none: '飛んでいくボールが見つかりませんでした', short: '追えたコマが少なすぎました', odd: '計測値が不自然でした' };
  function onResult(res) {
    lastRes = res; lastActive = Date.now();
    if (!res.ok) { setState('error', `${WHY[res.why] || '計測できませんでした'}。部屋を明るくし、ボールの上側の背景がボールと違う色になるようにしてください`); cooldownUntil = performance.now() + 2000; return; }
    // 長く追えたときは、そのボールの空気抵抗の倍率を少しずつ合わせる
    if (res.dragFit && res.dragRms < 1.3 * res.rms + 0.5) { S.drag = +clamp(S.drag * 0.7 + res.dragFit * 0.3, 0.3, 2.5).toFixed(3); store.set('drag', S.drag); showDrag(); }
    const cv = PHYS.plasticLaunch(res.speed, res.angle, { massG: S.mass, diamMM: S.diam, cor: S.cor, attack: S.attack });
    const speed = clamp(res.speed, 0.5, 40), angle = clamp(res.angle, 0, 80), spin = clamp(Math.round(cv.spin / 10) * 10, 0, 12000);
    const shot = { type: 'shot', id: Date.now().toString(36) + Math.random().toString(36).slice(2, 6), speed: +speed.toFixed(2), angle: +angle.toFixed(1), dir: +clamp(res.dir, -30, 30).toFixed(1), axis: +clamp(res.axis || 0, -35, 35).toFixed(1), spin,
      club: +cv.clubSpeed.toFixed(2), loft: +cv.spinLoft.toFixed(1), massG: S.mass, diamMM: S.diam, drag: S.drag };
    lastShot = shot; $('carryFix').hidden = false;
    $('cSpeed').textContent = speed.toFixed(1) + ' m/s'; $('cAngle').textContent = angle.toFixed(1) + '°';
    $('cDir').textContent = (shot.dir > 0.4 ? '右' : shot.dir < -0.4 ? '左' : '') + Math.abs(shot.dir).toFixed(1) + '°'; $('cSpin').textContent = spin + ' rpm';
    const f = ftimes.length > 10 ? Math.round((ftimes.length - 1) / (ftimes[ftimes.length - 1] - ftimes[0])) : 0;
    $('cMeta').textContent = `クラブ速度 ${cv.clubSpeed.toFixed(1)} m/s(推定)、回転軸の傾き ${shot.axis}°、追跡 ${res.n} コマ・約${f}fps、当てはめの誤差 ${res.rms.toFixed(1)}px、空気抵抗の補正 ×${S.drag.toFixed(2)}`;
    $('camResult').hidden = false;
    const ok = Net.send(shot);
    setState('done', ok ? 'iPadを見てください' : 'iPadと未接続のため送れていません');
    cooldownUntil = performance.now() + 1500;
  }

  function drawOverlay() {
    const r = ov.getBoundingClientRect(); const W = Math.round(r.width * devicePixelRatio), H = Math.round(r.height * devicePixelRatio);
    if (ov.width !== W || ov.height !== H) { ov.width = W; ov.height = H; }
    octx.clearRect(0, 0, W, H);
    if (!sess) return;
    const b = videoBox(), sx = b.w / VW, sy = b.h / VH, dpr = devicePixelRatio;
    const X = (x) => b.x + x * sx, Y = (y) => b.y + y * sy;
    const ring = (x, y, rad, color, width, dash) => { octx.save(); octx.strokeStyle = color; octx.lineWidth = width * dpr; octx.setLineDash(dash ? dash.map(v => v * dpr) : []); octx.beginPath(); octx.arc(X(x), Y(y), rad, 0, Math.PI * 2); octx.stroke(); octx.restore(); };
    const ss = sess.state, pulse = 0.5 + 0.5 * Math.sin(performance.now() / 180);
    const tee = sess.tee, ball = sess.ball, cand = sess.cand;
    if (ss === 'track' || (performance.now() < cooldownUntil + 1500 && lastRes)) {
      // 追跡中:追えた点と、いまのボールの丸
      const tr = ss === 'track' ? sess.obs : lastRes.obs;
      octx.fillStyle = '#d63a2a'; tr.forEach(q => { octx.beginPath(); octx.arc(X(q.u), Y(q.v), 3 * dpr, 0, Math.PI * 2); octx.fill(); });
      const L = tr[tr.length - 1]; if (L && ss === 'track') ring(L.u, L.v, L.d / 2 * sx + 4 * dpr, '#d63a2a', 3);
    } else if (cand && (ss === 'wait')) {
      // ボールを見つけた:黄色の丸と、「打ってOK」までの進み具合(緑の弧)
      const rad = cand.r * sx + 6 * dpr;
      ring(cand.x, cand.y, rad, '#ffd24a', 3);
      const pr = sess.progress; octx.save(); octx.strokeStyle = '#1f9d55'; octx.lineWidth = 5 * dpr; octx.beginPath(); octx.arc(X(cand.x), Y(cand.y), rad + 5 * dpr, -Math.PI / 2, -Math.PI / 2 + pr * Math.PI * 2); octx.stroke(); octx.restore();
    } else if (ball && (ss === 'ready' || ss === 'armed')) {
      // 打ってOK:緑の丸が脈打つ。構えでボールが隠れている間はオレンジ
      const rad = ball.r * sx + (6 + 3 * pulse) * dpr;
      ring(ball.x, ball.y, rad, ss === 'armed' ? '#f0a020' : '#1f9d55', ss === 'armed' ? 3 : 4 + 2 * pulse);
    } else if (tee && tee.r && (ss === 'wait' || ss === 'clear' || ss === 'after' || ss === 'moved')) {
      // ボール待ち:置き場所を点線の丸で示す
      ring(tee.x, tee.y, tee.r * sx + 6 * dpr, ss === 'moved' ? '#d63a2a' : 'rgba(255,255,255,.85)', 2.5, [6, 5]);
    } else if (tee && ss === 'remove') {
      ring(tee.x, tee.y, (8 + 6 * pulse) * dpr, '#ffd24a', 3);
    }
    if (ss === 'setup') {
      octx.fillStyle = 'rgba(0,0,0,.6)'; octx.fillRect(0, H - 44 * dpr, W, 44 * dpr);
      octx.fillStyle = '#fff'; octx.font = `${15 * dpr}px sans-serif`; octx.textAlign = 'center';
      octx.fillText('映像のボールをタップしてください', W / 2, H - 16 * dpr);
    }
  }

  const EVS = { remove: 'remove', teeset: 'wait', empty: 'wait', notempty: 'clear', tapfail: 'setup', track: 'track', lostball: 'wait', moved: 'moved', retap: 'setup' };
  function frame(t) {
    ftimes.push(t); if (ftimes.length > 30) ftimes.shift();
    if (vid.videoWidth !== VW || vid.videoHeight !== VH) { VW = vid.videoWidth; VH = vid.videoHeight; newSession(); }
    if (performance.now() < cooldownUntil) { if (!dark) drawOverlay(); return; }
    if (state === 'done' || state === 'error') setState(sess.state === 'ready' ? 'ready' : 'wait');
    const ev = sess.feed(frameObj, t);
    if (ev) {
      if (ev.ev === 'teeset' || ev.ev === 'empty') { const tt = Object.assign({}, sess.tee, { thumb: ev.thumb || (ev.tee && ev.tee.thumb) || sess.thumb }); store.set(teeKey(), tt); }
      if (ev.ev === 'teeset') toast('置き場所を覚えました');
      if (ev.ev === 'ready') {
        learnF(ev.ball);
        issue = VW > VH ? 'landscape' : ev.issue || null;
        if (issue === 'near' || issue === 'far') setState('adjust'); else setState('ready', issue === 'landscape' ? '縦向きのほうが、上がっていくボールを長く追えます' : undefined);
      } else if (ev.ev === 'result') onResult(ev.res);
      else if (ev.ev === 'back') setState(ev.state === 'remove' ? 'remove' : 'wait');
      else if (ev.ev === 'retap') { store.set(teeKey(), null); setState('setup', 'カメラの向きが変わったので、置き場所を登録し直します。映像のボールをタップしてください'); }
      else if (EVS[ev.ev] && state !== EVS[ev.ev]) setState(EVS[ev.ev]);
    } else if (sess.state === 'ready' && state !== 'ready' && state !== 'adjust') setState('ready');
    else if (sess.state === 'wait' && state === 'ready') setState('wait');
    if (!dark) drawOverlay();
  }
  // 1コマの処理でエラーが出ても止まらないようにし、内容を画面に出す(原因を調べるため)
  let errShown = 0;
  function safeFrame(t) {
    try { frame(t); }
    catch (e) { if (Date.now() - errShown > 3000) { errShown = Date.now(); $('stateSub').textContent = 'エラー:' + String(e && e.message || e).slice(0, 120); } }
  }
  function loop() {
    if (!running) return;
    if ('requestVideoFrameCallback' in vid) {
      const cb = (now, meta) => { if (!running) return; const ms = meta && (meta.captureTime || meta.presentationTime || now); safeFrame(ms / 1000); vid.requestVideoFrameCallback(cb); };
      vid.requestVideoFrameCallback(cb);
    } else {
      const cb = (now) => { if (!running) return; safeFrame(now / 1000); requestAnimationFrame(cb); };
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
    const K = c.scale || 1;                                   // コースの縮小率(縁取りの幅などに使う)
    if (root) { scene.remove(root); root.traverse(o => { if (o.geometry) o.geometry.dispose(); }); }
    root = new THREE.Group();
    const T = textures();
    const lam = (opt) => new THREE.MeshLambertMaterial(opt);
    const g = new THREE.Shape(); g.moveTo(-200, 300); g.lineTo(360, 300); g.lineTo(360, -300); g.lineTo(-200, -300); g.closePath();
    const chasms = c.shapes.filter(s => s.type === 'chasm');
    chasms.forEach(s => g.holes.push(shapeOf(s)));
    root.add(flat(g, 0, lam({ map: T.rough })));
    if (c.allGreen) root.add(flat(shapeOf({ kind: 'rect', x0: -5, x1: c.pin.x + 12, z0: -14, z1: 14 }), 0.004, lam({ map: T.green })));
    c.shapes.filter(s => s.type === 'fairway' && !s.top).forEach(s => { root.add(flat(shapeOf(s, 0.8 * K), 0.006, lam({ map: T.fringe }))); root.add(flat(shapeOf(s), 0.008, lam({ map: T.fairway }))); });
    c.shapes.filter(s => s.type === 'water').forEach(s => {
      root.add(flat(shapeOf(s, 0.9 * K), 0.012, lam({ color: '#b8a57a' })));
      root.add(flat(shapeOf(s), 0.016, new THREE.MeshPhongMaterial({ map: T.water, shininess: 90, specular: '#cfeaff' })));
    });
    c.shapes.filter(s => s.top && s.type === 'rough').forEach(s => root.add(flat(shapeOf(s), 0.02, lam({ map: T.rough, color: '#c8d8b8' }))));
    c.shapes.filter(s => s.top && s.type === 'fairway').forEach(s => { root.add(flat(shapeOf(s, 0.6), 0.022, lam({ map: T.fringe }))); root.add(flat(shapeOf(s), 0.024, lam({ map: T.fairway }))); });
    const greens = c.shapes.filter(s => s.type === 'green');
    greens.forEach(s => {
      const inWater = c.shapes.some(w => w.type === 'water' && SIM.inShape(w, s.cx, s.cz));
      if (!inWater) root.add(flat(shapeOf(s, 1.2 * K), 0.03, lam({ map: T.fringe })));
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
      const x = rand(bb.x0 - 22, bb.x1 + 22), z = rand(bb.z0 - 22, bb.z1 + 22);
      let ok = true;
      for (const [dx, dz] of [[0, 0], [7, 0], [-7, 0], [0, 7], [0, -7], [5, 5], [-5, -5], [5, -5], [-5, 5]]) { const zn = SIM.zoneAt(c, x + dx, z + dz); if (zn !== 'rough' || (c.allGreen && Math.abs(z) < 16 && x < c.pin.x + 14)) { ok = false; break; } }
      if (ok && Math.hypot(x, z) > 9) spots.push([x, z, rand(0.55, 1.0)]);
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
    const OK = c.okR || 0;
    if (OK > 0) {
    const okFill = new THREE.Mesh(new THREE.CircleGeometry(OK, 72), new THREE.MeshBasicMaterial({ color: '#fff3a0', transparent: true, opacity: .2 }));
    okFill.rotation.x = -Math.PI / 2; okFill.position.set(P.x, 0.042, P.z); root.add(decal(okFill, 42));
    const okRing = new THREE.Mesh(new THREE.RingGeometry(OK - 0.04, OK + 0.04, 96), new THREE.MeshBasicMaterial({ color: '#ffffff', transparent: true, opacity: .95, side: THREE.DoubleSide }));
    okRing.rotation.x = -Math.PI / 2; okRing.position.set(P.x, 0.046, P.z); root.add(decal(okRing, 46));
    }
    const cup = new THREE.Mesh(new THREE.CircleGeometry(0.054, 24), new THREE.MeshBasicMaterial({ color: '#0c0c0c' })); cup.rotation.x = -Math.PI / 2; cup.position.set(P.x, 0.05, P.z); root.add(decal(cup, 50));
    const pole = new THREE.Mesh(new THREE.CylinderGeometry(0.014, 0.014, 2.2, 8), lam({ color: '#f4f4f4' })); pole.position.set(P.x, 1.1, P.z); pole.castShadow = true; root.add(pole);
    const flagG = new THREE.PlaneGeometry(0.6, 0.38, 6, 1); const fp = flagG.attributes.position; for (let i = 0; i < fp.count; i++) { const x = fp.getX(i) + 0.3; fp.setZ(i, Math.sin(x * 6) * 0.05 * x); }
    const flag = new THREE.Mesh(flagG, lam({ color: '#e0412a', side: THREE.DoubleSide })); flag.position.set(P.x, 1.98, P.z + 0.3); flag.rotation.y = Math.PI / 2; flag.castShadow = true; root.add(flag);
    // tee mat
    const tee = new THREE.Mesh(new THREE.BoxGeometry(1.0, 0.03, 1.0), lam({ color: '#1d4a2a' })); tee.position.set(c.tee.x, 0.02, c.tee.z); tee.receiveShadow = true; root.add(tee);
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
      const d = Math.max(Math.hypot(P.x - focus.x, P.z - focus.z), reach, 6);
      const h = d * 1.1 + 6;
      camPos.set(cx - dx * h * 0.3, h, cz - dz * h * 0.3); camLook.set(cx, 0, cz);
    } else {
      const L = Math.min(reach, Math.max(4, Math.hypot(course.pin.x - focus.x, course.pin.z - focus.z))) * 0.75;
      camPos.set(focus.x - dx * 3.4, 1.35, focus.z - dz * 3.4); camLook.set(focus.x + dx * L, 0, focus.z + dz * L);
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
      if (viewMode === 'follow') { const s = pts[0], e = pts[Math.min(i + 3, pts.length - 1)]; let dx = e[1] - s[1], dz = e[3] - s[3]; const L = Math.hypot(dx, dz) || 1; dx /= L; dz /= L; if (L < 0.5) { dx = Math.cos(heading); dz = Math.sin(heading); } camPos.set(x - dx * 3.6, Math.max(1.1, y + 1.2), z - dz * 3.6); camLook.set(x + dx * 1.5, Math.max(0, y) * 0.6, z + dz * 1.5); }
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
    const maxD = Math.max(r.total * 1.12, 4.5), maxH = Math.max(r.apex * 1.3, 0.6);
    const X = (m) => pad + (m / maxD) * (W - 2 * pad), Y = (h) => base - (Math.max(h, 0) / maxH) * (base - 22 * dpr);
    const n = Math.max(1, Math.floor(cur.frac * (p.length - 1)));
    ctx.strokeStyle = '#d63a2a'; ctx.lineWidth = 2.4 * dpr; ctx.setLineDash([]); ctx.beginPath();
    for (let i = 0; i <= n; i++) { const q = p[i]; i ? ctx.lineTo(X(hx(q)), Y(q[2])) : ctx.moveTo(X(hx(q)), Y(q[2])); }
    ctx.stroke();
    ctx.fillStyle = '#16301f'; ctx.fillRect(X(App.pin()) - 1 * dpr, base - 10 * dpr, 2 * dpr, 10 * dpr);
    ctx.font = `700 ${12 * dpr}px "Avenir Next Condensed","Arial Narrow",sans-serif`;
    if (cur.frac >= 1) {
      ctx.fillStyle = '#d63a2a'; ctx.beginPath(); ctx.arc(X(r.carry), base, 3.5 * dpr, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#16301f'; ctx.textAlign = 'center';
      ctx.fillText(`キャリー ${r.carry.toFixed(2)}m`, clamp(X(r.carry), 50 * dpr, W - 50 * dpr), H - 4 * dpr);
      ctx.textAlign = 'right'; ctx.fillText(`最高 ${r.apex.toFixed(1)}m  落下角 ${Math.round(r.landAngle || 0)}°`, W - pad, 13 * dpr);
    }
  }
  return { draw, clear: () => { cur = null; draw(null, 0); } };
})();

/* ======================================================================
   APP (iPad): 3.45m先のカップを狙う、1ホールだけのアプローチゲーム
   ====================================================================== */
const App = (() => {
  // 部屋と同じ配置:ボールから2.63m先でグリーンが始まり、5.41m先にカップ(設定で変えられる)
  let PIN_M = clamp(store.get('pinM', 5.41), 1, 15), GREEN0 = clamp(store.get('green0', 2.63), 0.3, 14);
  let lie = store.get('lie', 'マット') === 'ラフ' ? 'ラフ' : 'マット';
  let COURSE = null;
  function buildCourse() {
    const g0 = Math.min(GREEN0, PIN_M - 0.3), gEnd = PIN_M + 0.9;
    COURSE = {
      id: 'cup', par: 0, pin: { x: PIN_M, z: 0 }, stimp: 10, slope: { x: 0, z: 0 }, route: [], tee: { x: 0, z: 0 }, okR: 0, scale: 0.12,
      shapes: [
        { type: 'green', kind: 'ellipse', cx: (g0 + gEnd) / 2, cz: 0, rx: (gEnd - g0) / 2, rz: 1.2 },
        { type: 'fairway', kind: 'rect', x0: -0.6, x1: g0 + 0.2, z0: -0.75, z1: 0.75 }
      ]
    };
  }
  buildCourse();
  let readyState = 'off', paired = false, busy = false;
  let log = store.get('cupLog', []);                          // {d: ピンまで[m], in: true/false}
  const seen = new Set();
  const fCm = (m) => m < 1 ? `${Math.round(m * 100)}cm` : `${m.toFixed(2)}m`;
  let ballSet = store.get('ballSet', { massG: 5, diamMM: 42, drag: 1 });
  World.onProgress((res, frac) => Profile.draw(res, frac));

  function start() {
    show('playView');
    World.load(COURSE); World.setAim(COURSE.tee, 0, PIN_M + 0.6);
    World.onTap(null);
    render(); setReady(readyState);
  }
  function setPaired(p) {
    paired = p;
    $('connectCard').classList.toggle('paired', p);
    $('pairNote').textContent = p ? 'iPhoneとつながっています' : 'iPhoneのカメラアプリでQRコードを読み取ってください';
  }

  function banner(t, sub, ms, kind) {
    const b = $('banner'); b.textContent = t; if (sub) b.append(el('small', null, sub)); b.className = 'banner' + (kind ? ' ' + kind : ''); b.hidden = false;
    clearTimeout(banner._t); if (ms) banner._t = setTimeout(() => { b.hidden = true; }, ms);
  }
  function simulate(s) {
    if (s.massG) { ballSet = { massG: s.massG, diamMM: s.diamMM, drag: s.drag }; store.set('ballSet', ballSet); }
    // ラフから打つと、フェースとボールの間に芝が挟まってスピンが減る
    const sh = Object.assign({}, s, { spin: lie === 'ラフ' ? s.spin * 0.5 : s.spin });
    const res = SIM.simulate(sh, COURSE, COURSE.tee, 0, PHYS.plasticProfile({ massG: ballSet.massG, diamMM: ballSet.diamMM, dragScale: ballSet.drag }));
    let apex = 0, carryT = res.duration; for (const p of res.pts) if (p[2] > apex) apex = p[2];
    for (let i = 1; i < res.pts.length; i++) if (res.pts[i][2] <= 0.001 && res.pts[i - 1][2] > 0.001) { carryT = res.pts[i][0]; res.carryPt = { x: res.pts[i][1], z: res.pts[i][3] }; break; }
    res.apex = apex; res.carryT = carryT;
    return res;
  }
  function onShot(s) {
    if (seen.has(s.id)) return; seen.add(s.id);
    if (busy || World.busy()) return;
    busy = true; $('banner').hidden = true;
    $('gDir').textContent = Math.abs(s.dir || 0) < 0.5 ? '0' : (s.dir > 0 ? '右' : '左') + Math.abs(s.dir).toFixed(1); $('gSpeed').textContent = s.speed.toFixed(1); $('gAngle').textContent = s.angle.toFixed(0);
    ['gCarry', 'gTotal', 'gPin'].forEach(id => { $(id).textContent = '…'; }); $('gPinU').textContent = '';
    const res = simulate(s);
    World.play(res, '#ffffff', () => finish(res));
  }
  function finish(res) {
    const into = res.holed, d = res.hazard ? 9.99 : res.toPin;
    $('gCarry').textContent = res.carry.toFixed(2); $('gTotal').textContent = res.total.toFixed(2);
    if (into) { $('gPin').textContent = 'IN'; $('gPinU').textContent = ''; }
    else if (d < 1) { $('gPin').textContent = String(Math.round(d * 100)); $('gPinU').textContent = 'cm'; }
    else { $('gPin').textContent = d.toFixed(2); $('gPinU').textContent = 'm'; }
    log.push({ d: into ? 0 : d, in: into }); if (log.length > 200) log.shift(); store.set('cupLog', log);
    const best = log.length > 1 && !into && d <= Math.min(...log.slice(0, -1).map(l => l.d));
    if (into) { banner('カップイン!', null, 3000, 'good'); Sound.good(); }
    else if (d < 0.15) banner('おしい!', `カップまで ${fCm(d)}`, 2600, 'good');
    else if (res.end.x > PIN_M) banner(`${fCm(d)} オーバー`, best ? 'ベスト更新' : null, 2400);
    else banner(`${fCm(d)} ショート`, best ? 'ベスト更新' : null, 2400);
    World.addMarker(res.end.x, res.end.z, into ? '#ffd24a' : '#ffffff');
    render();
    setTimeout(() => { World.setAim(COURSE.tee, 0, PIN_M + 0.6); busy = false; }, 1800);
  }
  function render() {
    const n = log.length, ins = log.filter(l => l.in).length;
    $('stN').textContent = n;
    $('stIn').textContent = ins;
    $('stAvg').textContent = n ? fCm(log.reduce((a, l) => a + l.d, 0) / n) : '–';
    $('stBest').textContent = n ? (ins ? 'IN' : fCm(Math.min(...log.map(l => l.d)))) : '–';
    const t = $('shotLog'); t.textContent = '';
    const hr = el('tr'); ['', 'カップまで'].forEach((h, i) => hr.append(el('th', i ? 'n' : null, h))); t.append(hr);
    if (!n) { const r = el('tr'); const c = el('td', 'empty', '「打ってOK」が出たら打ってみましょう。'); c.colSpan = 2; r.append(c); t.append(r); }
    log.map((l, i) => [l, i]).slice(-30).reverse().forEach(([l, i]) => { const r = el('tr'); r.append(el('td', null, `${i + 1}球目`), el('td', 'n' + (l.in ? ' good' : ''), l.in ? 'カップイン' : fCm(l.d))); t.append(r); });
  }
  let resetArm = 0;
  $('resetLog').onclick = () => {
    if (Date.now() - resetArm > 3000) { resetArm = Date.now(); $('resetLog').textContent = 'もう一度押すと消去します'; setTimeout(() => { $('resetLog').textContent = '記録を消去'; }, 3000); return; }
    log = []; store.set('cupLog', log); $('resetLog').textContent = '記録を消去'; World.load(COURSE); World.setAim(COURSE.tee, 0, PIN_M + 0.6); render();
  };

  const num = (v, a, b) => { v = Number(v); return Number.isFinite(v) ? clamp(v, a, b) : null; };
  function onMessage(m) {
    if (m.type === 'status') { if (['wait', 'ready', 'track', 'off', 'adjust'].includes(m.state)) setReady(m.state, ['portrait', 'near', 'far'].includes(m.issue) ? m.issue : 'near'); return; }
    if (m.type === 'shot') {
      const s = { id: String(m.id || '').slice(0, 32), speed: num(m.speed, 0.3, 60), angle: num(m.angle, 0, 80), dir: num(m.dir, -30, 30) ?? 0, axis: num(m.axis, -35, 35) ?? 0, spin: num(m.spin, 0, 12000), club: num(m.club, 0, 60), massG: num(m.massG, 1, 30) ?? 5, diamMM: num(m.diamMM, 30, 80) ?? 42, drag: num(m.drag, 0.4, 2.5) ?? 1 };
      if (!s.id || s.speed == null || s.angle == null || s.spin == null) return;
      onShot(s);
    }
  }
  const READY_TEXT = { off: 'iPhoneのカメラ待ち', wait: 'ボールを置いてください', ready: '打ってOK', track: '計測中…' };
  const ADJUST_TEXT = { portrait: 'iPhoneを横向きにしてください', near: 'カメラが近すぎます。1m前後離してください', far: 'カメラが遠すぎます。少し近づけてください' };
  function setReady(s, iss) {
    const was = readyState; readyState = s;
    $('readyMark').dataset.state = s; $('world').dataset.ready = s;
    $('readyText').textContent = s === 'adjust' ? (ADJUST_TEXT[iss] || ADJUST_TEXT.near) : READY_TEXT[s] || '';
    if (s === 'ready' && was !== 'ready') Sound.ready();
  }
  function sendInfo() { Net.send({ type: 'info', next: '', lie }); }
  $('soundOn').checked = Sound.on(); $('soundOn').onchange = () => store.set('sound', $('soundOn').checked);

  // 試し打ち:クラブ速度から練習ボールの打ち出しを計算する(スピンロフトは55度)
  const testLaunch = () => {
    const v = +$('tClub').value, S = 55 * Math.PI / 180, pb = PHYS.plasticBall({ massG: ballSet.massG, diamMM: ballSet.diamMM });
    const u = PHYS.impactUnit(pb, S, v);
    return { speed: u.speed * v, angle: (-3 * Math.PI / 180 + S - u.beta) * 180 / Math.PI, spin: u.w * v * 60 / (2 * Math.PI) };
  };
  const tUpd = () => { $('otClub').textContent = (+$('tClub').value).toFixed(1) + ' m/s'; };
  $('tClub').oninput = tUpd; tUpd();
  $('testShot').onclick = () => { const L = testLaunch(); onShot({ id: 't' + Date.now() + Math.random(), speed: L.speed, angle: L.angle, dir: 0, spin: L.spin, club: +$('tClub').value }); };
  // 打つ場所(マット/ラフ)とカップまでの距離
  function setLie(l) { lie = l; store.set('lie', l); document.querySelectorAll('#lieSel button').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.lie === l))); $('lieOut').textContent = l; sendInfo(); }
  document.querySelectorAll('#lieSel button').forEach(b => { b.onclick = () => setLie(b.dataset.lie); });
  function showPin() { $('pinOut').textContent = PIN_M.toFixed(2) + ' m'; $('oPinM').textContent = PIN_M.toFixed(2) + ' m'; $('oGreen0').textContent = GREEN0.toFixed(2) + ' m'; }
  $('sPinM').value = PIN_M; $('sGreen0').value = GREEN0;
  $('sPinM').oninput = () => { PIN_M = +$('sPinM').value; store.set('pinM', PIN_M); buildCourse(); showPin(); if (!busy) { World.load(COURSE); World.setAim(COURSE.tee, 0, PIN_M + 0.6); } };
  $('sGreen0').oninput = () => { GREEN0 = +$('sGreen0').value; store.set('green0', GREEN0); buildCourse(); showPin(); if (!busy) { World.load(COURSE); World.setAim(COURSE.tee, 0, PIN_M + 0.6); } };
  showPin(); setLie(lie);
  return { start, initHome: start, onMessage, setReady, setPaired, sendInfo, pin: () => PIN_M };
})();

/* ---------------- boot ---------------- */
if (role === 'camera' || role === 'green') startRole(role); else show('roleView');
})();
