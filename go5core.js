// go5core.js - 5x5 바둑: 규칙, 책 조회, 수 판정 (화면과 무관한 부분)
//
// C:\vc\go5\solver 의 solver.cpp / go5gui.cpp 에서 대국과 판정에 필요한 부분만 옮긴 것이다.
// 탐색(solver)은 들어 있지 않다. 책(go5_book.txt)과 증명 결과(go5_results.txt)에 있는 것만 안다.
//
// 규칙: 중국식 계가(돌 + 집), 덤 없음, 자살수 금지, 같은 판 모양 반복 금지(국면 슈퍼코), 2연속 패스로 종국.
// 점 번호 p = (행 - 1) * 5 + 열,  a1 = 0, e5 = 24.  패스 = 25.
(function (root) {
  'use strict';
  const N = 5, NN = 25, ALL = (1 << NN) - 1, PASS = 25, NOMOVE = 255;
  let COL0 = 0, COLL = 0, EDGEM = 0;
  const NB1 = [], DIAGM = [], PERM = [], INVP = [];

  const pc = (x) => { let c = 0; while (x) { x &= x - 1; c++; } return c; };
  const lsb = (x) => 31 - Math.clz32(x & -x);
  const nb = (x) => (((x << 1) & ~COL0) | ((x >>> 1) & ~COLL) | (x << N) | (x >>> N)) & ALL;
  function flood(seed, mask) {
    let x = seed & mask;
    for (;;) { const y = (x | nb(x)) & mask; if (y === x) return x; x = y; }
  }
  (function init() {
    for (let r = 0; r < N; r++) { COL0 |= 1 << (r * N); COLL |= 1 << (r * N + N - 1); }
    for (let p = 0; p < NN; p++) NB1[p] = nb(1 << p);
    for (let p = 0; p < NN; p++) {
      const r = (p / N) | 0, c = p % N; let d = 0;
      if (r === 0 || c === 0 || r === N - 1 || c === N - 1) EDGEM |= 1 << p;
      for (let dr = -1; dr <= 1; dr += 2) for (let dc = -1; dc <= 1; dc += 2) {
        const rr = r + dr, cc = c + dc;
        if (rr >= 0 && rr < N && cc >= 0 && cc < N) d |= 1 << (rr * N + cc);
      }
      DIAGM[p] = d;
    }
    for (let s = 0; s < 8; s++) {
      PERM[s] = []; INVP[s] = [];
      for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
        let rr = r, cc = c;
        if (s & 4) cc = N - 1 - cc;
        for (let k = 0; k < (s & 3); k++) { const t = rr; rr = cc; cc = N - 1 - t; }
        PERM[s][r * N + c] = rr * N + cc; INVP[s][rr * N + cc] = r * N + c;
      }
    }
  })();
  function xf(s, x) { let o = 0; while (x) { const p = lsb(x); x &= x - 1; o |= 1 << PERM[s][p]; } return o; }

  // 착수. own = 두는 쪽 돌. 둘 수 없으면(돌 있음 / 자살수 / 단순 패) null.
  function play(own, opp, ko, p) {
    const bit = 1 << p;
    if ((own | opp) & bit) return null;
    const o2 = own | bit, empty = ALL & ~(o2 | opp);
    let cap = 0, adj = NB1[p] & opp;
    while (adj) {
      const g = flood(adj & -adj, opp);
      adj &= ~g;
      if (!(nb(g) & empty)) cap |= g;
    }
    const nc = pc(cap);
    if (p === ko && nc === 1) return null;
    let nko = -1;
    if (!cap) {
      const g = flood(bit, o2);
      if (!(nb(g) & empty)) return null;
    } else if (nc === 1 && !(NB1[p] & o2)) {
      const libs = NB1[p] & ALL & ~(o2 | (opp & ~cap));
      if (pc(libs) === 1) nko = lsb(cap);
    }
    return { no: o2, np: opp & ~cap, nko, ncap: nc };
  }
  function areaScore(own, opp) {
    const e = ALL & ~(own | opp);
    const ro = flood(nb(own) & e, e), rp = flood(nb(opp) & e, e);
    return pc(own) + pc(ro & ~rp) - pc(opp) - pc(rp & ~ro);
  }
  // Benson 무조건 삶 (MIGOS 방식 보강 포함). x 쪽이 확보한 점들.
  function bensonSafe(x, y) {
    if (!x) return 0;
    const nonx = ALL & ~x, regs = [], chs = [], chnb = [];
    for (let rem = nonx; rem;) { const r = flood(rem & -rem, nonx); regs.push(r); rem &= ~r; }
    if (regs.length < 2) return 0;
    for (let rem = x; rem;) { const c = flood(rem & -rem, x); chs.push(c); chnb.push(nb(c)); rem &= ~c; }
    const nr = regs.length, nc = chs.length, empty = nonx & ~y, vital = [], border = [];
    for (let r = 0; r < nr; r++) {
      const re = regs[r] & empty, nbr = nb(regs[r]); let v = 0, b = 0;
      for (let c = 0; c < nc; c++) if (chs[c] & nbr) { b |= 1 << c; if (!(re & ~chnb[c])) v |= 1 << c; }
      vital[r] = v; border[r] = b;
    }
    let aliveC = (1 << nc) - 1, liveR = (1 << nr) - 1;
    for (let changed = true; changed;) {
      changed = false;
      for (let r = 0; r < nr; r++) if ((liveR >> r & 1) && (border[r] & ~aliveC)) { liveR &= ~(1 << r); changed = true; }
      for (let c = 0; c < nc; c++) if (aliveC >> c & 1) {
        let cnt = 0;
        for (let r = 0; r < nr; r++) if ((liveR >> r & 1) && (vital[r] >> c & 1)) cnt++;
        if (cnt < 2) { aliveC &= ~(1 << c); changed = true; }
      }
      if (!aliveC) return 0;
    }
    let A = 0;
    for (let c = 0; c < nc; c++) if (aliveC >> c & 1) A |= chs[c];
    let safe = A; const nbA = nb(A);
    for (let rem = ALL & ~A; rem;) {
      const r = flood(rem & -rem, ALL & ~A); rem &= ~r;
      const inn = r & ~nbA;
      let E = inn & ~y; const outside = ALL & ~r;
      if (flood(outside & EDGEM, outside) === outside)
        for (let t = E; t;) {
          const p = lsb(t); t &= t - 1;
          const d = pc(DIAGM[p] & A);
          if ((EDGEM >> p & 1) ? d >= 1 : d >= 2) E &= ~(1 << p);
        }
      const k = pc(E);
      let ut = k <= 1 || (k === 2 && (nb(E & -E) & E) !== 0);
      if (!ut) { const D = E & x; if (pc(D) === 1 && !(E & ~(D | nb(D)))) ut = true; }
      if (ut) safe |= r;
    }
    return safe;
  }

  // 국면의 고유값: 회전/뒤집기 8가지 중 가장 작은 것. 결과 파일의 열쇠와 같은 16자리 16진수.
  function canon(own, opp, ko, passed) {
    let best = null, bs = 0;
    for (let s = 0; s < 8; s++) {
      const k = (((BigInt(xf(s, own)) << 25n) | BigInt(xf(s, opp))) << 5n) | BigInt(ko >= 0 ? PERM[s][ko] + 1 : 0);
      if (best === null || k < best) { best = k; bs = s; }
    }
    const key = ((best << 1n) | BigInt(passed) | (1n << 63n)).toString(16).padStart(16, '0');
    return { key, sym: bs };
  }
  const keyOf = (st) => canon(st.own, st.opp, st.ko, st.passed);

  const newState = () => ({ own: 0, opp: 0, ko: -1, passed: 0, stm: 0 });
  const boardKey = (st) => st.stm === 0 ? st.own + ',' + st.opp : st.opp + ',' + st.own;    // 흑,백
  // 수를 둔다. 반환 { st, hist } 또는 null (둘 수 없음). hist = 지나온 판 모양들.
  function applyMove(st, mv, hist) {
    const h = hist.concat([boardKey(st)]);
    if (mv === PASS) return { st: { own: st.opp, opp: st.own, ko: -1, passed: 1, stm: st.stm ^ 1 }, hist: h };
    const r = play(st.own, st.opp, st.ko, mv);
    if (!r) return null;
    const k = st.stm === 0 ? r.no + ',' + r.np : r.np + ',' + r.no;
    if (h.indexOf(k) >= 0) return null;                    // 같은 판 모양의 반복
    return { st: { own: r.np, opp: r.no, ko: r.nko, passed: 0, stm: st.stm ^ 1 }, hist: h };
  }
  const mvName = (p) => p === PASS ? 'pass' : p === NOMOVE ? '-' : 'abcde'[p % N] + (((p / N) | 0) + 1);
  function parseMove(t) {
    if (t === 'pass') return PASS;
    if (t.length !== 2) return -1;
    const c = t.toLowerCase().charCodeAt(0) - 97, r = t.charCodeAt(1) - 49;
    return (c < 0 || c >= N || r < 0 || r >= N) ? -1 : r * N + c;
  }
  function wonText(v) { return v > 0 ? '흑 ' + v + '집 승' : v < 0 ? '백 ' + (-v) + '집 승' : '무승부'; }

  // ------------------------------------------------------------------------
  // 책: 증명 결과(resDb) + 논문 책(paperBook)
  // ------------------------------------------------------------------------
  function Book() { this.resDb = new Map(); this.paperBook = new Map(); this.paperSrc = []; }
  // go5_results.txt: "열쇠 하한 상한 수" (둘 차례 기준, 수는 고유 방향)
  Book.prototype.loadResults = function (text) {
    for (const line of text.split(/\r?\n/)) {
      const f = line.trim().split(/\s+/);
      if (f.length < 4 || !/^[0-9a-f]{16}$/i.test(f[0])) continue;
      const k = f[0].toLowerCase(), lo = parseInt(f[1], 10), hi = parseInt(f[2], 10), mv = parseInt(f[3], 10);
      if (isNaN(lo) || isNaN(hi) || isNaN(mv)) continue;
      const it = this.resDb.get(k);
      if (!it) this.resDb.set(k, { lo, hi, mv });
      else {
        if (lo > it.lo) { it.lo = lo; if (mv !== NOMOVE) it.mv = mv; }
        else if (lo === it.lo && it.mv === NOMOVE && mv !== NOMOVE) it.mv = mv;
        if (hi < it.hi) it.hi = hi;
      }
    }
  };
  // 새로 알게 된 것을 책에 넣는다 (이 페이지 안에서만, 파일로 저장되지는 않는다)
  Book.prototype.addResult = function (st, lo, hi, mv) {
    const c = keyOf(st);
    let cm = mv === NOMOVE ? NOMOVE : mv === PASS ? PASS : PERM[c.sym][mv];
    const it = this.resDb.get(c.key);
    const addsMove = it && it.lo === lo && it.mv === NOMOVE && cm !== NOMOVE;
    if (it && it.lo >= lo && it.hi <= hi && !addsMove) return;
    if (it) { if (it.lo > lo) { lo = it.lo; cm = it.mv; } if (it.hi < hi) hi = it.hi; }
    this.resDb.set(c.key, { lo, hi, mv: cm });
  };
  // go5_book.txt: "값 출처 : 수순" ('|' 뒤부터의 국면만 넣는다)
  Book.prototype.loadPaperBook = function (text) {
    for (let line of text.split(/\r?\n/)) {
      const h = line.indexOf('#'); if (h >= 0) line = line.slice(0, h);
      const colon = line.indexOf(':'); if (colon < 0) continue;
      const head = line.slice(0, colon).trim().split(/\s+/);
      const vBlack = parseInt(head[0], 10); if (isNaN(vBlack)) continue;
      const srcName = head[1] || '책';
      let srcId = this.paperSrc.indexOf(srcName);
      if (srcId < 0) { srcId = this.paperSrc.length; this.paperSrc.push(srcName); }
      const mvs = []; let start = 0, bad = false;
      for (const q of line.slice(colon + 1).trim().split(/\s+/)) {
        if (!q) continue;
        if (q === '|') { start = mvs.length; continue; }
        const m = parseMove(q); if (m < 0) { bad = true; break; }
        mvs.push(m);
      }
      if (bad) continue;
      let st = newState(), hist = [];
      for (let i = 0; i <= mvs.length; i++) {
        if (i >= start) {
          const c = keyOf(st), m = i < mvs.length ? mvs[i] : NOMOVE;
          const cm = m === NOMOVE ? NOMOVE : m === PASS ? PASS : PERM[c.sym][m];
          const v = st.stm === 0 ? vBlack : -vBlack, it = this.paperBook.get(c.key);
          if (!it) this.paperBook.set(c.key, { v, mv: cm, src: srcId });
          else if (it.v === v && it.mv === NOMOVE && cm !== NOMOVE) { it.mv = cm; it.src = srcId; }
        }
        if (i === mvs.length) break;
        const r = applyMove(st, mvs[i], hist); if (!r) break;
        st = r.st; hist = r.hist;
      }
    }
  };
  // 이 국면이 책에 있는가. kind 0 = 없음, 1 = solver 증명, 2 = 논문 책.  v = 흑 기준, mv = 이 판 방향의 수
  Book.prototype.lookupKnown = function (st, hist) {
    const c = keyOf(st);
    const conv = (m) => m === NOMOVE ? NOMOVE : m === PASS ? PASS : INVP[c.sym][m];
    const r = this.resDb.get(c.key);
    if (r && r.lo === r.hi && r.mv !== NOMOVE && applyMove(st, conv(r.mv), hist))
      return { kind: 1, v: st.stm === 0 ? r.lo : -r.lo, mv: conv(r.mv), src: 'solver 증명' };
    const p = this.paperBook.get(c.key);
    if (p) {
      let mv = conv(p.mv);
      if (mv !== NOMOVE && !applyMove(st, mv, hist)) mv = NOMOVE;
      return { kind: 2, v: st.stm === 0 ? p.v : -p.v, mv, src: '논문 ' + this.paperSrc[p.src] };
    }
    return { kind: 0, v: 0, mv: NOMOVE, src: '' };
  };
  // 한 수 뒤의 국면들로 이 국면을 확정한다: 판 전체를 이기는 수가 증명돼 있거나, 둘 수 있는 수 전부의 결과가 증명돼 있을 때.
  // 반환: 둘 차례 기준 값, 확정 못 하면 null.
  Book.prototype.inferFromChildren = function (st) {
    const it = this.resDb.get(keyOf(st).key);
    if (it && it.lo === it.hi && it.mv !== NOMOVE) return it.lo;
    const childVal = (own, opp, ko, passed) => {
      const c = this.resDb.get(canon(own, opp, ko, passed).key);
      return (c && c.lo === c.hi) ? c.lo : null;
    };
    let best = -100, bm = NOMOVE, all = true;
    for (let p = 0; p < NN; p++) {
      if ((st.own | st.opp) >> p & 1) continue;
      const r = play(st.own, st.opp, st.ko, p); if (!r) continue;
      const w = childVal(r.np, r.no, r.nko, 0);
      if (w === null) { all = false; continue; }
      if (-w > best) { best = -w; bm = p; }
    }
    if (st.passed) {
      const so = bensonSafe(st.own, st.opp), sp = bensonSafe(st.opp, st.own);
      const w = areaScore((st.own & ~sp) | so, (st.opp & ~so) | sp);
      if (w > best) { best = w; bm = PASS; }
    } else {
      const w = childVal(st.opp, st.own, -1, 1);
      if (w === null) all = false; else if (-w > best) { best = -w; bm = PASS; }
    }
    if (bm === NOMOVE || !(best === NN || all)) return null;
    this.addResult(st, best, best, bm);
    return best;
  };
  // 값이 알려진 국면인가 (둘 차례 기준 값 또는 null)
  Book.prototype.knownVal = function (st) {
    const iv = this.inferFromChildren(st); if (iv !== null) return iv;
    const k = keyOf(st).key, r = this.resDb.get(k);
    if (r && r.lo === r.hi) return r.lo;
    const p = this.paperBook.get(k);
    return p ? p.v : null;
  };
  Book.prototype.rangeOf = function (st) {
    const v = this.knownVal(st); if (v !== null) return { lo: v, hi: v };
    const r = this.resDb.get(keyOf(st).key);
    return r ? { lo: r.lo, hi: r.hi } : { lo: -NN, hi: NN };
  };
  Book.prototype.lowerBoundOf = function (st) {
    let lb = this.rangeOf(st).lo;
    for (let p = 0; p < NN; p++) {
      if ((st.own | st.opp) >> p & 1) continue;
      const r = play(st.own, st.opp, st.ko, p); if (!r) continue;
      const hi = this.rangeOf({ own: r.np, opp: r.no, ko: r.nko, passed: 0, stm: st.stm ^ 1 }).hi;
      if (-hi > lb) lb = -hi;
    }
    return lb;
  };
  function finalScoreBlack(st) {
    const black = st.stm === 0 ? st.own : st.opp, white = st.stm === 0 ? st.opp : st.own;
    const sb = bensonSafe(black, white), sw = bensonSafe(white, black);
    return areaScore((black & ~sw) | sb, (white & ~sb) | sw);
  }

  // ------------------------------------------------------------------------
  // 수의 판정
  // ------------------------------------------------------------------------
  const CLS_BEST = 0, CLS_UNPROVEN = 1, CLS_MISTAKE = 2, CLS_UNPROVEN_NEXT = 3;
  // r = { pre, histPre, mv, post, histPost, endsGame }.  prev = 바로 앞의 수 (없으면 null)
  Book.prototype.classifyCore = function (r, prev) {
    const sgn = r.pre.stm === 0 ? 1 : -1;
    r.cls = CLS_UNPROVEN; r.lbOnly = r.afterUpper = r.bySolverMove = false;
    let v = this.knownVal(r.pre);
    if (v === null) {
      if (prev && prev.cls !== CLS_UNPROVEN && !prev.afterUpper) v = sgn * prev.vAfter;
      else {
        const lb = this.lowerBoundOf(r.pre); let up;
        if (lb <= -NN) return;
        if (r.endsGame) up = sgn * finalScoreBlack(r.post);
        else { const g = this.rangeOf(r.post); up = -g.lo; r.afterUpper = g.lo !== g.hi; }
        if (up < lb) { r.cls = CLS_MISTAKE; r.lbOnly = true; r.vBefore = sgn * lb; r.vAfter = sgn * up; }
        else r.afterUpper = false;
        return;
      }
    }
    r.vBefore = sgn * v;
    const k = this.lookupKnown(r.pre, r.histPre);
    if (k.kind && k.mv === r.mv) { r.cls = CLS_BEST; r.vAfter = r.vBefore; r.bySolverMove = k.kind === 1; return; }
    if (k.kind && k.mv !== NOMOVE && !r.endsGame) {       // 책의 수와 대칭인 수
      const a = applyMove(r.pre, k.mv, r.histPre);
      if (a && keyOf(a.st).key === keyOf(r.post).key) { r.cls = CLS_BEST; r.vAfter = r.vBefore; r.bySolverMove = k.kind === 1; return; }
    }
    let after;
    if (r.endsGame) after = sgn * finalScoreBlack(r.post);
    else { const w = this.knownVal(r.post); if (w === null) return; after = -w; }
    r.vAfter = sgn * after;
    r.cls = after >= v ? CLS_BEST : CLS_MISTAKE;
  };
  Book.prototype.classify = function (r, prev) {
    this.classifyCore(r, prev);
    r.nextKnown = false;
    if (r.cls !== CLS_UNPROVEN || r.endsGame) return;
    for (let p = 0; p <= 25 && !r.nextKnown; p++) {
      if (p < 25 && ((r.post.own | r.post.opp) >> p & 1)) continue;
      const mv = p === 25 ? PASS : p, a = applyMove(r.post, mv, r.histPost);
      if (!a) continue;
      const q = { pre: r.post, histPre: r.histPost, mv, post: a.st, histPost: a.hist, endsGame: mv === PASS && !!r.post.passed };
      this.classifyCore(q, r);
      if (q.cls !== CLS_UNPROVEN) r.nextKnown = true;
    }
  };
  // solver 가 증명한 최선의 수를 두었으면 두고 난 국면의 값도 정해진다
  Book.prototype.recordPost = function (r) {
    if (r.cls !== CLS_BEST || !r.bySolverMove || r.endsGame) return;
    const v = r.post.stm === 0 ? r.vBefore : -r.vBefore;
    this.addResult(r.post, v, v, NOMOVE);
  };
  const drawCls = (r) => (r.cls === CLS_UNPROVEN && r.nextKnown) ? CLS_UNPROVEN_NEXT : r.cls;

  // ------------------------------------------------------------------------
  // 대국 (수순 기록 + 판정)
  // ------------------------------------------------------------------------
  function Game(book) { this.book = book; this.reset(); }
  Game.prototype.reset = function () { this.recs = []; this.st = newState(); this.hist = []; this.over = false; };
  Game.prototype.push = function (mv) {
    if (this.over) return false;
    const a = applyMove(this.st, mv, this.hist);
    if (!a) return false;
    const prev = this.recs.length ? this.recs[this.recs.length - 1] : null;
    const r = { pre: this.st, histPre: this.hist, mv, post: a.st, histPost: a.hist, endsGame: mv === PASS && !!this.st.passed, stoneOf: [] };
    const occ = a.st.own | a.st.opp, idx = this.recs.length;
    for (let p = 0; p < NN; p++) r.stoneOf[p] = !(occ >> p & 1) ? -1 : (p === mv ? idx : (prev ? prev.stoneOf[p] : -1));
    this.book.classify(r, prev); this.book.recordPost(r);
    this.recs.push(r); this.st = a.st; this.hist = a.hist; this.over = r.endsGame;
    return true;
  };
  Game.prototype.undo = function () {
    const r = this.recs.pop(); if (!r) return;
    this.st = r.pre; this.hist = r.histPre; this.over = false;
  };
  Game.prototype.last = function () { return this.recs.length ? this.recs[this.recs.length - 1] : null; };
  // 지금 국면의 값 (흑 기준) 또는 null
  Game.prototype.curKnown = function () {
    const v = this.book.knownVal(this.st);
    if (v !== null) return this.st.stm === 0 ? v : -v;
    const l = this.last();
    return (l && l.cls !== CLS_UNPROVEN && !l.afterUpper) ? l.vAfter : null;
  };
  // 미리보기: 빈 점마다 거기에 두었을 때의 판정 (-1 = 둘 수 없음)
  Game.prototype.preview = function () {
    const out = [], occ = this.st.own | this.st.opp, prev = this.last();
    for (let p = 0; p < NN; p++) {
      out[p] = -1;
      if (this.over || (occ >> p & 1)) continue;
      const a = applyMove(this.st, p, this.hist); if (!a) continue;
      const r = { pre: this.st, histPre: this.hist, mv: p, post: a.st, histPost: a.hist, endsGame: false };
      this.book.classify(r, prev);
      out[p] = drawCls(r);
    }
    return out;
  };
  function describeMove(r) {
    let s = (r.pre.stm === 0 ? '흑 ' : '백 ') + mvName(r.mv) + '\n';
    if (r.cls === CLS_BEST) s += '증명된 최선의 수 — ' + wonText(r.vBefore);
    else if (r.cls === CLS_MISTAKE) s += '값을 잃는 수 — ' + wonText(r.vBefore) + (r.lbOnly ? ' 이상' : '') + ' → ' + wonText(r.vAfter) + (r.afterUpper ? ' 이하' : '');
    else s += '증명되지 않은 수';
    return s;
  }

  const api = { N, NN, PASS, NOMOVE, CLS_BEST, CLS_UNPROVEN, CLS_MISTAKE, CLS_UNPROVEN_NEXT,
    Book, Game, newState, applyMove, mvName, parseMove, wonText, finalScoreBlack, drawCls, describeMove, keyOf };
  if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.Go5 = api;
})(typeof self !== 'undefined' ? self : this);
