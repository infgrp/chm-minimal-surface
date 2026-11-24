/* 최소곡면족 모음 — 바이어슈트라스 수치 적분 엔진과 삼중 주기 곡면(준위면 근사)
   모든 바이어슈트라스 곡면:  X = Re( e^{iθ} ∫ ( ½f(1−g²), ½ i f(1+g²), f g ) dz )
   θ 는 연합족 각(보네 변환). 적분값(복소수)을 저장해 두므로 θ 를 바꿀 때 다시 적분하지 않는다.
   돌려주는 꼴:
     grid  { kind:"grid", pieces:[{P,N,ST,off}], N1, N2, vid, clip(x,y,z), fit, sp:[a,b], polar, longEdge }
     tris  { kind:"tris", pos, nrm, st, clip, fit, sp }                                               */
(function (root) {
  "use strict";
  const TAU = Math.PI * 2;
  // ── 복소수 [re, im]
  const C = {
    mul: (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]],
    div: (a, b) => { const d = b[0] * b[0] + b[1] * b[1]; return [(a[0] * b[0] + a[1] * b[1]) / d, (a[1] * b[0] - a[0] * b[1]) / d]; },
    add: (a, b) => [a[0] + b[0], a[1] + b[1]], sub: (a, b) => [a[0] - b[0], a[1] - b[1]],
    pow: (z, n) => { let r = [1, 0]; for (let i = 0; i < n; i++) r = C.mul(r, z); return r; },
    exp: a => { const e = Math.exp(a[0]); return [e * Math.cos(a[1]), e * Math.sin(a[1])]; },
  };
  const GL = [[-0.9061798459, 0.2369268851], [-0.5384693101, 0.4786286705], [0, 0.5688888889], [0.5384693101, 0.4786286705], [0.9061798459, 0.2369268851]];

  // ── 바이어슈트라스 격자 적분
  // o.dom: "disk"  z = R (i/N1)^rp e^{iφ}            (원점 기준)
  //        "lp"    z = e^{s + iφ}, s ∈ [s0, s1]        (기준 줄 ib 에서 φ 방향, 다시 s 방향)
  function wGrid(o) {
    const N1 = o.n1, N2 = o.n2, NV = (N1 + 1) * (N2 + 1), vid = (i, j) => i * (N2 + 1) + j;
    const phi0 = o.phi0 || 0, phiSpan = o.phiSpan || TAU;
    const Z = new Array(NV), ST = new Float64Array(NV * 2);
    // 끝(극)이 |z| = 1 위의 각 φ = 2πm/pw 에 있으면 그 근처를 촘촘히: s 는 sinh 눈금, φ 는 극 쪽으로 세제곱 눈금
    const sOf = i => { const u = i / N1; if (!o.sw) return o.s0 + (o.s1 - o.s0) * u; const w = 2 * u - 1; return o.s1 * Math.sinh(o.sw * w) / Math.sinh(o.sw); };
    const phOf = j => {
      if (!o.pw) return phi0 + phiSpan * j / N2;
      // 극과 극 사이 한 칸을 tanh 눈금으로: 양 끝(극) 쪽이 촘촘하고 가운데는 성기다 (반 칸 밀어 극 위에 꼭짓점이 오지 않게)
      const L = TAU / o.pw, per = N2 / o.pw, m = Math.floor(j / per), v = Math.min(1, (j - m * per + 0.5) / per), a = o.pa || 2.5;
      return m * L + L * 0.5 * (1 + Math.tanh(a * (2 * v - 1)) / Math.tanh(a));
    };
    for (let i = 0; i <= N1; i++) for (let j = 0; j <= N2; j++) {
      const ph = j === N2 && o.pw ? phOf(0) + TAU : phOf(j); let rr, a;
      if (o.dom === "disk") { rr = o.R * Math.pow(i / N1, o.rp || 1); a = rr; }
      else { a = sOf(i); rr = Math.exp(a); }
      Z[vid(i, j)] = [rr * Math.cos(ph), rr * Math.sin(ph)];
      ST[vid(i, j) * 2] = ph; ST[vid(i, j) * 2 + 1] = a;
    }
    const poles = o.poles || [];
    const phi = z => {   // 세 성분의 복소 미분형식 계수
      const f = o.f(z), g = o.g(z), g2 = C.mul(g, g);
      return [C.mul([0.5, 0], C.mul(f, [1 - g2[0], -g2[1]])), C.mul([0, 0.5], C.mul(f, [1 + g2[0], g2[1]])), C.mul(f, g)];
    };
    const gauss = (za, zb, out) => {
      const m = [(za[0] + zb[0]) / 2, (za[1] + zb[1]) / 2], h = [(zb[0] - za[0]) / 2, (zb[1] - za[1]) / 2];
      for (const [x, w] of GL) {
        const p = phi([m[0] + h[0] * x, m[1] + h[1] * x]);
        for (let c = 0; c < 3; c++) { const v = C.mul(p[c], h); out[c * 2] += w * v[0]; out[c * 2 + 1] += w * v[1]; }
      }
    };
    const seg = (za, zb, out, depth = 0) => {   // 극 가까이는 잘게
      const L = Math.hypot(zb[0] - za[0], zb[1] - za[1]);
      if (depth < 12) for (const p of poles) {
        const dx = zb[0] - za[0], dy = zb[1] - za[1], t = Math.max(0, Math.min(1, ((p[0] - za[0]) * dx + (p[1] - za[1]) * dy) / (L * L || 1)));
        if (Math.hypot(za[0] + dx * t - p[0], za[1] + dy * t - p[1]) < 1.5 * L) {
          const mid = [(za[0] + zb[0]) / 2, (za[1] + zb[1]) / 2]; seg(za, mid, out, depth + 1); seg(mid, zb, out, depth + 1); return;
        }
      }
      gauss(za, zb, out);
    };
    const F = new Float64Array(NV * 6);   // (re, im) × 3
    const step = (b, from) => { const r = [0, 0, 0, 0, 0, 0]; seg(Z[from], Z[b], r); for (let c = 0; c < 6; c++) F[b * 6 + c] = F[from * 6 + c] + r[c]; };
    const ib = o.ib ?? 0;
    for (let j = 1; j <= N2; j++) step(vid(ib, j), vid(ib, j - 1));
    for (let j = 0; j <= N2; j++) {
      for (let i = ib + 1; i <= N1; i++) step(vid(i, j), vid(i - 1, j));
      for (let i = ib - 1; i >= 0; i--) step(vid(i, j), vid(i + 1, j));
    }
    const N = new Float64Array(NV * 3);
    for (let v = 0; v < NV; v++) {
      const g = o.g(Z[v]), gg = g[0] * g[0] + g[1] * g[1];
      if (!Number.isFinite(gg)) { N[v * 3 + 2] = 1; continue; }
      N[v * 3] = 2 * g[0] / (gg + 1); N[v * 3 + 1] = 2 * g[1] / (gg + 1); N[v * 3 + 2] = (gg - 1) / (gg + 1);
    }
    // 끝 둘레의 주기 (작은 원을 한 바퀴): 복소 3성분
    const period = (p, r = 1e-3) => {
      const n = 4000, out = [0, 0, 0, 0, 0, 0];
      for (let k = 0; k < n; k++) {
        const a0 = TAU * k / n, a1 = TAU * (k + 1) / n;
        gauss([p[0] + r * Math.cos(a0), p[1] + r * Math.sin(a0)], [p[0] + r * Math.cos(a1), p[1] + r * Math.sin(a1)], out);
      }
      return out;
    };
    const atTheta = (th, P = new Float64Array(NV * 3)) => {
      const c = Math.cos(th), s = Math.sin(th);
      for (let v = 0; v < NV; v++) for (let k = 0; k < 3; k++) P[v * 3 + k] = c * F[v * 6 + k * 2] - s * F[v * 6 + k * 2 + 1];
      return P;
    };
    return { N1, N2, NV, vid, Z, F, N, ST, atTheta, period };
  }
  const reP = (cplx, th) => [0, 1, 2].map(k => Math.cos(th) * cplx[k * 2] - Math.sin(th) * cplx[k * 2 + 1]);

  // ── 삼중 주기 곡면: 준위면을 사면체 행진법으로
  function tpms(fn, grad, L, n) {
    const h = 2 * L / n, M = n + 1, val = new Float64Array(M * M * M), id = (i, j, k) => (k * M + j) * M + i;
    for (let k = 0; k < M; k++) for (let j = 0; j < M; j++) for (let i = 0; i < M; i++) val[id(i, j, k)] = fn(-L + i * h, -L + j * h, -L + k * h);
    const pos = [], nrm = [], st = [];
    const TET = [[0, 5, 1, 6], [0, 1, 2, 6], [0, 2, 3, 6], [0, 3, 7, 6], [0, 7, 4, 6], [0, 4, 5, 6]];
    const CO = [[0, 0, 0], [1, 0, 0], [1, 1, 0], [0, 1, 0], [0, 0, 1], [1, 0, 1], [1, 1, 1], [0, 1, 1]];
    const P = new Array(8), V = new Float64Array(8);
    const emit = (a, b) => {   // 모서리 a–b 위 영점
      const t = V[a] / (V[a] - V[b]);
      const x = P[a][0] + (P[b][0] - P[a][0]) * t, y = P[a][1] + (P[b][1] - P[a][1]) * t, z = P[a][2] + (P[b][2] - P[a][2]) * t;
      const g = grad(x, y, z), l = Math.hypot(g[0], g[1], g[2]) || 1;
      pos.push(x, y, z); nrm.push(g[0] / l, g[1] / l, g[2] / l); st.push(x, z);
    };
    for (let k = 0; k < n; k++) for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) {
      let pz = 0, ng = 0;
      for (let c = 0; c < 8; c++) { const [a, b, d] = CO[c]; V[c] = val[id(i + a, j + b, k + d)]; P[c] = [-L + (i + a) * h, -L + (j + b) * h, -L + (k + d) * h]; V[c] >= 0 ? pz++ : ng++; }
      if (!pz || !ng) continue;
      for (const t of TET) {
        const ins = t.filter(c => V[c] < 0), out = t.filter(c => V[c] >= 0);
        if (ins.length === 0 || ins.length === 4) continue;
        if (ins.length === 1 || ins.length === 3) {
          const [s, o3] = ins.length === 1 ? [ins[0], out] : [out[0], ins];
          emit(s, o3[0]); emit(s, o3[1]); emit(s, o3[2]);
        } else {
          const [a, b] = ins, [c, d] = out;
          emit(a, c); emit(a, d); emit(b, d);
          emit(a, c); emit(b, d); emit(b, c);
        }
      }
    }
    return { pos, nrm, st };
  }

  // ── 곡면족
  const unity = k => Array.from({ length: k }, (_, j) => [Math.cos(TAU * j / k), Math.sin(TAU * j / k)]);
  const FAM = {};

  FAM.cathel = {
    name: "현수면–나선면", eyebrow: "ASSOCIATE FAMILY · CATENOID ↔ HELICOID",
    theta: true, thetaDefault: 0, anim: true,
    build() {
      const G = wGrid({ dom: "lp", s0: -1.35, s1: 1.35, n1: 64, n2: 160, ib: 32, f: z => C.div([1, 0], C.mul(z, z)), g: z => z, poles: [[0, 0]] });
      return { G, clip: null, sp: [TAU / 32, 0.18], fitR: 3.1, ctr: [32] };
    },
    rows: (p, th) => [["연합족 각 θ", `${(th * 180 / Math.PI).toFixed(0)}°`], ["모양", th < 0.05 ? "현수면" : th > 1.52 ? "나선면" : "그 사이 (등거리 변형)"], ["가우스 사상", "g = z"]],
    info: `<p><b>현수면</b>(사슬을 늘어뜨린 곡선을 돌린 곡면)과 <b>나선면</b>(나선 계단)은 같은 바이어슈트라스 자료 <span class="f">f = 1/z², g = z</span>에서 나옵니다.</p>
      <p>적분에 <span class="f">e<sup>iθ</sup></span>를 곱하면(보네 변환) <b>길이와 각도를 그대로 둔 채</b> 곡면이 휘어 바뀝니다. 모든 단계가 최소곡면이고, 법선 방향도 같은 점에서 그대로입니다.
      θ = 0°는 현수면, 90°는 나선면 한 바퀴입니다. ‘변형 재생’으로 고리가 풀려 나선이 되는 모습을 보세요.</p>`,
  };

  FAM.enneper = {
    name: "에네퍼 곡면", eyebrow: "ENNEPER SURFACE",
    param: { label: "차수 n", values: [1, 2, 3, 4, 5], def: 1 },
    build(n, sz) {
      const R = (n === 1 ? 1.45 : n === 2 ? 1.2 : 1.12) * sz;
      const G = wGrid({ dom: "disk", R, rp: 1, n1: 72, n2: 64 * (n + 1), f: () => [1, 0], g: z => C.pow(z, n) });
      return { G, clip: null, sp: [TAU / (8 * (n + 1)), R / 12], fitR: 0.5 * (R + Math.pow(R, 2 * n + 1) / (2 * n + 1)) * 1.25, ctr: [0] };
    },
    rows: n => [["차수", n], ["가우스 사상", `g = z${n > 1 ? "<sup>" + n + "</sup>" : ""}`], ["대칭", `${2 * (n + 1)}겹 회전 + 반사`]],
    info: `<p>가장 단순한 바이어슈트라스 자료 <span class="f">f = 1, g = z<sup>n</sup></span>에서 나오는 곡면입니다(1864, 에네퍼). 가운데는 말안장처럼 휘고,
      멀리 갈수록 가장자리가 <span class="f">n + 1</span>번 접혀 오르내립니다. 넓게 그리면 스스로를 뚫고 지나갑니다(넓이 조절).</p>`,
  };

  FAM.knoid = {
    name: "k-노이드", eyebrow: "JORGE–MEEKS k-NOID",
    param: { label: "끝 k", values: [2, 3, 4, 5, 6, 7], def: 3 },
    theta: true, thetaDefault: 0,
    build(k, sz) {
      const n2 = 96 * k;
      const G = wGrid({ dom: "lp", s0: -4.6, s1: 4.6, n1: 200, n2, ib: 50, sw: 5, pw: k, pa: 2.6,
        f: z => { const q = C.sub(C.pow(z, k), [1, 0]); return C.div([1, 0], C.mul(q, q)); }, g: z => C.pow(z, k - 1), poles: unity(k) });
      // 몸통 지름이 0.3~0.5 쯤이라, 구로 자를 때 반지름을 몸통 가까이 두어야 끝(현수면)이 목에서 벌어지는 모양이 보인다
      const Rc = (0.82 + 0.02 * k) * sz;
      return { G, clip: (x, y, z) => Math.hypot(x, y, z) / Rc - 1, sp: [TAU / (8 * k), 0.3], fitR: Rc * 0.92, longEdge: 0.3, ctr: [0, 200] };
    },
    rows: k => [["현수면 끝", k], ["종수", 0], ["가우스 사상", `g = z${k > 2 ? "<sup>" + (k - 1) + "</sup>" : ""}`]],
    info: `<p><b>조르지–미스 k-노이드</b>: <span class="f">f = 1/(z<sup>k</sup> − 1)², g = z<sup>k−1</sup></span>. 단위원 위의 k개 점이 <b>현수면처럼 벌어지는 끝</b>이 됩니다.
      k = 2 는 현수면 그 자체입니다. k ≥ 3 은 끝들이 서로 기울어 만나므로 매장되지는 않지만, 모든 끝의 ‘힘’(유량)이 균형을 이룹니다.</p>`,
  };

  FAM.richmond = {
    name: "리치먼드 곡면", eyebrow: "RICHMOND SURFACE",
    param: { label: "차수 m", values: [2, 3, 4], def: 2 },
    theta: true, thetaDefault: 0,
    build(m, sz) {
      const G = wGrid({ dom: "lp", s0: -3.2, s1: 1.4, n1: 138, n2: 64 * (m + 1), ib: 80, f: z => C.div([1, 0], C.mul(z, z)), g: z => C.pow(z, m), poles: [[0, 0]] });
      const Rc = 1.6 * sz;
      return { G, clip: (x, y, z) => Math.hypot(x, y, z) / Rc - 1, sp: [TAU / (8 * (m + 1)), 0.22], fitR: Rc, ctr: [96] };
    },
    rows: m => [["차수", m], ["끝", "평면형 1 · 에네퍼형 1"], ["가우스 사상", `g = z<sup>${m}</sup>`]],
    info: `<p><span class="f">f = 1/z², g = z<sup>m</sup></span> (리치먼드, 1904). 원점은 평면처럼 퍼지는 끝, 무한점은 에네퍼 곡면처럼 접히는 끝이 됩니다.
      평면 끝 둘레로 <span class="f">m − 1</span>번 휘감기는 모양을 보세요.</p>`,
  };

  // 셰르크: f = 4/(1 − z⁴), g = z.  θ = 0 → 이중 주기(날개가 위아래), θ = 90° → 한 방향 주기 탑(날개가 옆으로)
  function scherk(th, sz) {
    const G = wGrid({ dom: "lp", s0: -4.2, s1: 4.2, n1: 120, n2: 128, ib: 30, sw: 5, pw: 4,
      f: z => C.div([4, 0], C.sub([1, 0], C.pow(z, 4))), g: z => z, poles: unity(4) });
    // 끝 주기 → 붙여 놓을 격자
    const per = unity(4).map(p => reP(G.period(p), th));
    return { G, per };
  }
  FAM.scherk2 = {
    name: "셰르크 이중 주기", eyebrow: "SCHERK · DOUBLY PERIODIC",
    param: { label: "타일", values: [1, 2, 3], def: 2, names: ["1×1", "3×3", "5×5"] },
    build(t, sz) {
      const { G, per } = scherk(0, sz);
      const a = per[0], b = per[1], offs = [], n = t - 1;
      for (let i = -n; i <= n; i++) for (let j = -n; j <= n; j++) offs.push([a[0] * i + b[0] * j, a[1] * i + b[1] * j, a[2] * i + b[2] * j]);
      const W = Math.hypot(a[0], a[1]) * (n + 0.5) * 0.98, H = 0.36 * W * sz;
      return { G, theta: 0, offs, clip: (x, y, z) => Math.max(Math.abs(z) / H, Math.abs(x) / W, Math.abs(y) / W) - 1, sp: [TAU / 32, 0.25], fitR: Math.max(H, W * 0.9), longEdge: 1.2, ctr: [0, 120] };
    },
    rows: t => [["주기", "가로·세로 두 방향"], ["끝", "위아래로 번갈아 솟는 날개"], ["식", "e<sup>z</sup> cos y = cos x"]],
    info: `<p>1834년 셰르크가 찾은 곡면. 그래프로 쓰면 <span class="f">z = ln(cos y / cos x)</span>이고, 체크무늬 칸마다 위아래로 번갈아 솟은 안장이 수직선으로 이어집니다.
      바이어슈트라스 자료 <span class="f">f = 4/(1 − z⁴), g = z</span>의 한 조각을 적분하고, 네 끝 둘레의 주기(평행이동)로 이웃 조각을 붙였습니다.</p>`,
  };
  FAM.scherk1 = {
    name: "셰르크 탑", eyebrow: "SCHERK SADDLE TOWER · SINGLY PERIODIC",
    param: { label: "층", values: [1, 2, 3], def: 2, names: ["1", "3", "5"] },
    build(t, sz) {
      const { G, per } = scherk(Math.PI / 2, sz);
      const v = per.reduce((m, p) => Math.abs(p[2]) > Math.abs(m[2]) ? p : m, [0, 0, 0]), offs = [], n = t - 1;
      for (let i = -n; i <= n; i++) offs.push([v[0] * i, v[1] * i, v[2] * i]);
      const H = Math.abs(v[2]) * (n + 0.5) * 0.98, R = 0.7 * H * sz;
      return { G, theta: Math.PI / 2, offs, clip: (x, y, z) => Math.max(Math.hypot(x, y) / R, Math.abs(z) / H) - 1, sp: [TAU / 32, 0.25], fitR: Math.max(R, H), longEdge: 1.2, ctr: [0, 120] };
    },
    rows: t => [["주기", "위아래 한 방향"], ["끝", "옆으로 뻗은 날개 4장"], ["식", "sin z = sinh x sinh y"]],
    info: `<p>이중 주기 셰르크 곡면의 <b>켤레</b>(연합족 θ = 90°)입니다. 네 장의 날개가 옆으로 뻗고, 같은 무늬가 위아래로 끝없이 쌓입니다(안장 탑).
      두 곡면은 같은 점에서 법선이 같고, 한쪽의 직선이 다른 쪽에서는 대칭면이 됩니다.</p>`,
  };

  // 삼중 주기 (준위면 근사)
  const TP = {
    "P": { f: (x, y, z) => Math.cos(x) + Math.cos(y) + Math.cos(z), g: (x, y, z) => [-Math.sin(x), -Math.sin(y), -Math.sin(z)], nm: "슈바르츠 P" },
    "D": { f: (x, y, z) => Math.sin(x) * Math.sin(y) * Math.sin(z) + Math.sin(x) * Math.cos(y) * Math.cos(z) + Math.cos(x) * Math.sin(y) * Math.cos(z) + Math.cos(x) * Math.cos(y) * Math.sin(z),
           g: (x, y, z) => { const sx = Math.sin(x), cx = Math.cos(x), sy = Math.sin(y), cy = Math.cos(y), sz = Math.sin(z), cz = Math.cos(z);
             return [cx * sy * sz + cx * cy * cz - sx * sy * cz - sx * cy * sz, sx * cy * sz - sx * sy * cz + cx * cy * cz - cx * sy * sz, sx * sy * cz - sx * cy * sz - cx * sy * sz + cx * cy * cz]; }, nm: "슈바르츠 D" },
    "G": { f: (x, y, z) => Math.sin(x) * Math.cos(y) + Math.sin(y) * Math.cos(z) + Math.sin(z) * Math.cos(x),
           g: (x, y, z) => [Math.cos(x) * Math.cos(y) - Math.sin(z) * Math.sin(x), -Math.sin(x) * Math.sin(y) + Math.cos(y) * Math.cos(z), -Math.sin(y) * Math.sin(z) + Math.cos(z) * Math.cos(x)], nm: "자이로이드" },
    "N": { f: (x, y, z) => 3 * (Math.cos(x) + Math.cos(y) + Math.cos(z)) + 4 * Math.cos(x) * Math.cos(y) * Math.cos(z),
           g: (x, y, z) => [-3 * Math.sin(x) - 4 * Math.sin(x) * Math.cos(y) * Math.cos(z), -3 * Math.sin(y) - 4 * Math.cos(x) * Math.sin(y) * Math.cos(z), -3 * Math.sin(z) - 4 * Math.cos(x) * Math.cos(y) * Math.sin(z)], nm: "네오비우스" },
  };
  FAM.tpms = {
    name: "삼중 주기 곡면", eyebrow: "TRIPLY PERIODIC MINIMAL SURFACES",
    param: { label: "종류", values: ["P", "D", "G", "N"], def: "G", names: ["P", "D", "자이로이드", "네오비우스"] },
    build(key, sz) {
      const T = TP[key], L = Math.PI * 1.5 * sz, n = Math.round(64 * sz);
      const r = tpms(T.f, T.g, L * 1.02, n);
      return { kind: "tris", ...r, clip: (x, y, z) => Math.max(Math.abs(x), Math.abs(y), Math.abs(z)) / L - 1, sp: [Math.PI / 4, Math.PI / 4], fitR: L * 1.15 };
    },
    rows: key => [["곡면", TP[key].nm], ["주기", "x · y · z 세 방향"], ["그리기", "준위면 근사"]],
    info: `<p>세 방향으로 되풀이되는 최소곡면. 공간을 서로 얽힌 두 미로로 나눕니다. 비누막·나비 날개의 미세 구조·블록 공중합체에서 실제로 나타납니다.</p>
      <p>슈바르츠 P·D(1865)와 <b>자이로이드</b>(쇼언, 1970)는 같은 바이어슈트라스 자료의 연합족이기도 합니다(D 를 약 38° 돌리면 자이로이드, 90° 면 P).
      여기서는 널리 쓰는 삼각함수 준위면 근사(예: 자이로이드 <span class="f">sin x cos y + sin y cos z + sin z cos x = 0</span>)를 사면체 행진법으로 그렸습니다.</p>`,
  };

  root.MinSurf = { FAM, wGrid, tpms, C };
})(typeof window !== "undefined" ? window : globalThis);
