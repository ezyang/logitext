// Tests for kernel.js. Run with: node kernel-test.js
// Exercises the parser, every inference rule, substitution/freshness, and
// full end-to-end proofs of all tutorial exercises plus classic theorems.
const K = require('./kernel.js');

let passed = 0, failed = 0;
function ok(cond, name) {
  if (cond) { passed++; }
  else { failed++; console.error('FAIL: ' + name); }
}
function eq(a, b, name) { ok(a === b, name + ' [got: ' + a + ' want: ' + b + ']'); }
function seq(str) { return K.parseSequentString(str); }
function showS(str) { return K.showSequent(seq(str)); }
function throwsFailure(fn, kind, name) {
  try {
    fn();
  } catch (e) {
    if (e && e.failure === kind) { passed++; return e; }
    failed++;
    console.error('FAIL: ' + name + ' [wrong error: ' + (e && e.message) + ']');
    return null;
  }
  failed++;
  console.error('FAIL: ' + name + ' [no error thrown]');
  return null;
}

// Navigate/apply tactics in a proof tree exactly like the UI does.
function getNode(p, path) {
  let n = p;
  for (const k of path) n = (k === 0 ? n.q.a : n.q.b);
  return n;
}
function setNode(p, path, nn) {
  if (path.length === 0) return nn;
  const q = Object.assign({}, p.q);
  if (path[0] === 0) q.a = setNode(p.q.a, path.slice(1), nn);
  else q.b = setNode(p.q.b, path.slice(1), nn);
  return { t: 'Proof', s: p.s, q };
}
function step(p, path, tac) {
  const node = getNode(p, path);
  return setNode(p, path, K.refine(node.s, tac));
}
function U(str) { return K.parseUniverseString(str); }
// Prove `goal` by applying [path, tac] steps in order; assert completeness.
function prove(name, goal, steps) {
  let p = K.Goal(seq(goal));
  try {
    for (const [path, tac] of steps) p = step(p, path, tac);
  } catch (e) {
    failed++;
    console.error('FAIL: ' + name + ' [step threw: ' + (e && e.message) + ']');
    return null;
  }
  ok(K.proofComplete(p), name + ' (complete)');
  return p;
}

// ---------------------------------------------------------------- parser ---
const TUTORIAL_GOALS = [
  'A |- A', 'Γ, A |- A', 'A |- A, Δ', 'A \\/ B |- A, B',
  'Γ, A /\\ B |- A, Δ', 'Γ, A |- A \\/ B, Δ', 'Γ |- A -> A, Δ',
  '|- (A -> B) \\/ A', 'Γ, A, B |- A /\\ B, Δ', 'Γ, A \\/ B |- A, B, Δ',
  'Γ, A, A -> B |- B, Δ', 'Γ, A, ~A |- Δ', 'Γ |- ~A, A, Δ',
  'Γ, forall x. P(x) |- P(a), Δ', 'Γ, P(a) |- forall x. P(x), Δ',
  'Γ, exists x. P(x) |- P(a), Δ', 'Γ, P(a) |- exists x. P(x), Δ',
  '(forall x. P(x)) |- (forall x. P(x))',
  'A /\\ B |- B /\\ A', 'A \\/ B |- B \\/ A', '~(A \\/ B) -> ~A /\\ ~B',
  '(forall x. P(x)) /\\ (forall x. Q(x)) -> forall y. P(y) /\\ Q(y)',
  '|- exists x. P(x) -> forall y. P(y)',
  'forall x. (P(x)->P(f(x))) |- forall x. (P(x) -> P(f(f(x))))',
  '((A -> B) -> A) -> A', 'A \\/ ~A', '(forall x, P(x)) -> (exists x, P(x))'
];
for (const g of TUTORIAL_GOALS) {
  try { seq(g); passed++; }
  catch (e) { failed++; console.error('FAIL: parse tutorial goal: ' + g + ' [' + e.message + ']'); }
}

eq(showS('A -> B -> C'), ' |- (A -> (B -> C))', 'imp right assoc');
eq(showS('A /\\ B \\/ C'), ' |- ((A /\\ B) \\/ C)', 'conj over disj');
eq(showS('~A /\\ B'), ' |- ((~ A) /\\ B)', 'not over conj');
eq(showS('forall x. P(x) -> Q'), ' |- (forall x. (P(x) -> Q))', 'quantifier body extends right');
eq(showS('exists x, P(x)'), ' |- (exists x. P(x))', 'comma separator');
eq(showS('forall x y. P(x, y)'), ' |- (forall x. (forall y. P(x, y)))', 'multi binder');
eq(showS('∀x. P(x) ∧ Q ∨ R → S ↔ T'), ' |- (forall x. (((P(x) /\\ Q) \\/ R) -> (S <-> T)))', 'unicode ops');
eq(showS('⊤ ⊢ ⊥'), 'True |- False', 'unicode turnstile/top/bot');
eq(showS('True, False |- True'), 'True, False |- True', 'ascii top/bot');
eq(showS('P(f(x), a) |- Q'), 'P(f(x), a) |- Q', 'nested terms');
eq(showS('A (* comment *) |- A (* (* nested *) *)'), 'A |- A', 'comments');
eq(showS('forall. A'), ' |- A', 'zero binders');
eq(showS('|- A'), ' |- A', 'empty hyps');
eq(showS('A |-'), 'A |- ', 'empty cons');
eq(K.showSequent(seq('')), ' |- ', 'empty sequent');
eq(showS('~~A'), ' |- (~ (~ A))', 'double negation (superset of Parsec)');

// precedence rendering sanity: parsing is inverse of showing
for (const g of TUTORIAL_GOALS) {
  const s1 = seq(g);
  const s2 = seq(K.showSequent(s1));
  ok(K.showSequent(s1) === K.showSequent(s2), 'roundtrip: ' + g);
}

// failures
const BAD = ['P()', 'forall forall. A', 'P(fun)', 'A B', 'A |- |- B', '(A',
  'forall x P(x)', 'P(X)', 'x |- A', 'A |- x', '(*) A', 'A, , B', 'True X',
  'forall x. ', 'f(x)', 'A ->', 'Γ(,)', ''];
for (const g of BAD.slice(0, BAD.length - 1)) {
  throwsFailure(() => seq(g), 'ParseFailure', 'reject: ' + JSON.stringify(g));
}
for (const u of ['x', 'f(x)', 'f(f(x), a)', '(x)', 'g0(a1, b2)']) {
  try { K.parseUniverseString(u); passed++; } catch (e) { failed++; console.error('FAIL: parse term ' + u); }
}
for (const u of ['', 'X', 'f()', 'x y', 'forall', 'P(x)', 'f(X)']) {
  throwsFailure(() => K.parseUniverseString(u), 'ParseFailure', 'reject term: ' + JSON.stringify(u));
}

// ------------------------------------------------------------- substitution
(function () {
  const px = K.parseSequentString('P(x) |- Q').hyps[0];
  eq(K.showFormula(K.substFormula(px, 'x', U('z'))), 'P(z)', 'subst basic');
  const cap = K.parseSequentString('forall y. P(x, y) |- Q').hyps[0];
  const r = K.substFormula(cap, 'x', U('y'));
  ok(r.v !== 'y' && r.t === 'Forall', 'subst renames captured binder (got ' + r.v + ')');
  eq(K.showFormula(r), '(forall ' + r.v + '. P(y, ' + r.v + '))', 'subst capture-avoiding body');
  const sh = K.parseSequentString('forall x. P(x) |- Q').hyps[0];
  ok(K.equalFormula(K.substFormula(sh, 'x', U('z')), sh), 'subst shadowed is identity');
  const ho = K.parseSequentString('P(x(y)) |- Q').hyps[0];
  throwsFailure(() => K.substFormula(ho, 'x', U('z')), 'UpdateFailure', 'subst rejects function variable');
  eq(K.freshName('x', new Set()), 'x', 'fresh reuses base');
  eq(K.freshName('x', new Set(['x'])), 'x0', 'fresh x0');
  eq(K.freshName('x', new Set(['x', 'x0'])), 'x1', 'fresh x1');
  const free = K.freeNamesSequent(seq('P(a), forall x. Q(x, f(y)) |- R(g)'));
  eq([...free].sort().join(','), 'a,f,g,y', 'free names');
})();

// ------------------------------------------------- rule outputs (tutorial --
function refined(goal, tac) {
  const p = K.refine(seq(goal), tac);
  return p;
}
function kids(p) {
  const out = [];
  if (p.q.a !== undefined) out.push(K.showSequent(p.q.a.s));
  if (p.q.b !== undefined) out.push(K.showSequent(p.q.b.s));
  return out;
}
function ruleOut(name, goal, tac, want) {
  const got = kids(refined(goal, tac));
  eq(JSON.stringify(got), JSON.stringify(want), name);
}
ruleOut('LDisj', 'Γ, A \\/ B |- Δ', { t: 'LDisj', i: 1 }, ['Γ, A |- Δ', 'Γ, B |- Δ']);
ruleOut('LExact none', 'Γ, A |- A, Δ', { t: 'LExact', i: 1 }, []);
ruleOut('LNot', 'Γ, ~A |- Δ', { t: 'LNot', i: 1 }, ['Γ |- A, Δ']);
ruleOut('RNot', 'Γ |- ~A, Δ', { t: 'RNot', i: 0 }, ['A, Γ |- Δ']);
ruleOut('LConj', 'Γ, A /\\ B |- Δ', { t: 'LConj', i: 1 }, ['Γ, A, B |- Δ']);
ruleOut('RConj', 'Γ |- A /\\ B, Δ', { t: 'RConj', i: 0 }, ['Γ |- A, Δ', 'Γ |- B, Δ']);
ruleOut('RDisj', 'Γ |- A \\/ B, Δ', { t: 'RDisj', i: 0 }, ['Γ |- A, B, Δ']);
ruleOut('LImp', 'Γ, A -> B |- Δ', { t: 'LImp', i: 1 }, ['Γ |- A, Δ', 'Γ, B |- Δ']);
ruleOut('RImp', 'Γ |- A -> B, Δ', { t: 'RImp', i: 0 }, ['A, Γ |- B, Δ']);
ruleOut('LForall', 'Γ, forall x. P(x) |- Δ', { t: 'LForall', i: 1, u: U('z') }, ['Γ, P(z) |- Δ']);
ruleOut('RForall', 'Γ |- forall x. P(x), Δ', { t: 'RForall', i: 0 }, ['Γ |- P(x), Δ']);
ruleOut('LExists', 'Γ, exists x. P(x) |- Δ', { t: 'LExists', i: 1 }, ['Γ, P(x) |- Δ']);
ruleOut('RExists', 'Γ |- exists x. P(x), Δ', { t: 'RExists', i: 0, u: U('z') }, ['Γ |- P(z), Δ']);
ruleOut('LTop', 'Γ, True |- Δ', { t: 'LTop', i: 1 }, ['Γ |- Δ']);
ruleOut('RBot', 'Γ |- Δ, False', { t: 'RBot', i: 1 }, ['Γ |- Δ']);
ruleOut('LIff', 'Γ, A <-> B |- Δ', { t: 'LIff', i: 1 },
  ['Γ, (A -> B), (B -> A) |- Δ']);
ruleOut('RIff', 'Γ |- A <-> B, Δ', { t: 'RIff', i: 0 },
  ['Γ |- (A -> B), Δ', 'Γ |- (B -> A), Δ']);
ruleOut('LContract', 'Γ, A |- Δ', { t: 'LContract', i: 1 }, ['Γ, A, A |- Δ']);
ruleOut('RContract', 'Γ |- A, Δ', { t: 'RContract', i: 0 }, ['Γ |- A, A, Δ']);
ruleOut('LWeaken', 'Γ, A |- Δ', { t: 'LWeaken', i: 0 }, ['A |- Δ']);
ruleOut('RWeaken', 'Γ |- A, Δ', { t: 'RWeaken', i: 1 }, ['Γ |- A']);
// eigenvariable picks a fresh name when the binder is taken
ruleOut('RForall fresh', 'P(x) |- forall x. P(x)', { t: 'RForall', i: 0 }, ['P(x) |- P(x0)']);
ruleOut('LExists fresh', 'exists x. P(x), P(x) |- Q', { t: 'LExists', i: 0 }, ['P(x0), P(x) |- Q']);

// rule errors
throwsFailure(() => K.refine(seq('A |- B'), { t: 'LExact', i: 0 }), 'UpdateFailure', 'LExact no match');
throwsFailure(() => K.refine(seq('A |- B'), { t: 'RExact', i: 0 }), 'UpdateFailure', 'RExact no match');
(function () {
  const e = throwsFailure(() => K.refine(seq('A |- B'), { t: 'LExact', i: 0 }), 'UpdateFailure', 'LExact msg');
  if (e) eq(e.message, 'No matching atomic clause on other side of turnstile.', 'LExact message');
})();
throwsFailure(() => K.refine(seq('A /\\ B |- A'), { t: 'LDisj', i: 0 }), 'UpdateFailure', 'shape mismatch');
throwsFailure(() => K.refine(seq('A |- A'), { t: 'LExact', i: 5 }), 'UpdateFailure', 'index out of range');
throwsFailure(() => K.refine(seq('A |- A'), { t: 'Nope', i: 0 }), 'UpdateFailure', 'unknown tactic');
throwsFailure(() => K.refine(seq('A |- A'), { t: 'LExact', i: -1 }), 'UpdateFailure', 'negative index');
throwsFailure(() => K.refine(seq('forall x. P(x) |- Q'), { t: 'LForall', i: 0, u: { f: 'z' } }),
  'UpdateFailure', 'malformed term rejected');
// non-atomic exact
throwsFailure(() => K.refine(seq('A /\\ B |- A /\\ B'), { t: 'LExact', i: 0 }), 'UpdateFailure', 'LExact non-atomic');
// P(a) vs P(b) do not match
throwsFailure(() => K.refine(seq('P(a) |- P(b)'), { t: 'LExact', i: 0 }), 'UpdateFailure', 'LExact arg mismatch');

// ------------------------------------------------------------- full proofs
prove('ax', 'A |- A', [[[], { t: 'LExact', i: 0 }]]);
prove('hyp left', 'Γ, A |- A', [[[], { t: 'LExact', i: 1 }]]);
prove('con right', 'A |- A, Δ', [[[], { t: 'RExact', i: 0 }]]);
prove('backwards', 'A \\/ B |- A, B', [
  [[], { t: 'LDisj', i: 0 }],
  [[0], { t: 'LExact', i: 0 }],
  [[1], { t: 'LExact', i: 0 }]
]);
prove('trivial conj', 'Γ, A /\\ B |- A, Δ', [
  [[], { t: 'LConj', i: 1 }], [[0], { t: 'LExact', i: 1 }]
]);
prove('trivial disj', 'Γ, A |- A \\/ B, Δ', [
  [[], { t: 'RDisj', i: 0 }], [[0], { t: 'LExact', i: 1 }]
]);
prove('meta-imp', 'Γ |- A -> A, Δ', [
  [[], { t: 'RImp', i: 0 }], [[0], { t: 'LExact', i: 0 }]
]);
prove('bait and switch', '|- (A -> B) \\/ A', [
  [[], { t: 'RDisj', i: 0 }],
  [[0], { t: 'RImp', i: 0 }],
  [[0, 0], { t: 'LExact', i: 0 }]
]);
prove('branch conj', 'Γ, A, B |- A /\\ B, Δ', [
  [[], { t: 'RConj', i: 0 }],
  [[0], { t: 'LExact', i: 1 }],
  [[1], { t: 'LExact', i: 2 }]
]);
prove('branch disj', 'Γ, A \\/ B |- A, B, Δ', [
  [[], { t: 'LDisj', i: 1 }],
  [[0], { t: 'LExact', i: 1 }],
  [[1], { t: 'LExact', i: 1 }]
]);
prove('branch imp', 'Γ, A, A -> B |- B, Δ', [
  [[], { t: 'LImp', i: 2 }],
  [[0], { t: 'LExact', i: 1 }],
  [[1], { t: 'LExact', i: 2 }]
]);
prove('neg left', 'Γ, A, ~A |- Δ', [
  [[], { t: 'LNot', i: 2 }], [[0], { t: 'LExact', i: 1 }]
]);
prove('neg right', 'Γ |- ~A, A, Δ', [
  [[], { t: 'RNot', i: 0 }], [[0], { t: 'LExact', i: 0 }]
]);
prove('forall left', 'Γ, forall x. P(x) |- P(a), Δ', [
  [[], { t: 'LForall', i: 1, u: U('a') }], [[0], { t: 'LExact', i: 1 }]
]);
prove('exists right', 'Γ, P(a) |- exists x. P(x), Δ', [
  [[], { t: 'RExists', i: 0, u: U('a') }], [[0], { t: 'LExact', i: 1 }]
]);
prove('forall order good', '(forall x. P(x)) |- (forall x. P(x))', [
  [[], { t: 'RForall', i: 0 }],
  [[0], { t: 'LForall', i: 0, u: U('x') }],
  [[0, 0], { t: 'LExact', i: 0 }]
]);
// invalid direction gets stuck: eigenvariable cannot match
(function () {
  let p = K.Goal(seq('Γ, P(a) |- forall x. P(x), Δ'));
  p = step(p, [], { t: 'RForall', i: 0 });
  eq(K.showSequent(getNode(p, [0]).s), 'Γ, P(a) |- P(x), Δ', 'stuck shape');
  throwsFailure(() => K.refine(getNode(p, [0]).s, { t: 'LExact', i: 1 }), 'UpdateFailure', 'stuck exact fails');
  ok(!K.proofComplete(p), 'stuck proof incomplete');
})();
prove('ex comm conj', 'A /\\ B |- B /\\ A', [
  [[], { t: 'LConj', i: 0 }],
  [[0], { t: 'RConj', i: 0 }],
  [[0, 0], { t: 'LExact', i: 1 }],
  [[0, 1], { t: 'LExact', i: 0 }]
]);
prove('ex comm disj', 'A \\/ B |- B \\/ A', [
  [[], { t: 'RDisj', i: 0 }],
  [[0], { t: 'LDisj', i: 0 }],
  [[0, 0], { t: 'LExact', i: 0 }],
  [[0, 1], { t: 'LExact', i: 0 }]
]);
prove('ex demorgan', '~(A \\/ B) -> ~A /\\ ~B', [
  [[], { t: 'RImp', i: 0 }],
  [[0], { t: 'RConj', i: 0 }],
  [[0, 0], { t: 'RNot', i: 0 }],
  [[0, 0, 0], { t: 'LNot', i: 1 }],
  [[0, 0, 0, 0], { t: 'RDisj', i: 0 }],
  [[0, 0, 0, 0, 0], { t: 'LExact', i: 0 }],
  [[0, 1], { t: 'RNot', i: 0 }],
  [[0, 1, 0], { t: 'LNot', i: 1 }],
  [[0, 1, 0, 0], { t: 'RDisj', i: 0 }],
  [[0, 1, 0, 0, 0], { t: 'LExact', i: 0 }]
]);
prove('ex forall distr', '(forall x. P(x)) /\\ (forall x. Q(x)) -> forall y. P(y) /\\ Q(y)', [
  [[], { t: 'RImp', i: 0 }],
  [[0], { t: 'RForall', i: 0 }],
  [[0, 0], { t: 'RConj', i: 0 }],
  [[0, 0, 0], { t: 'LConj', i: 0 }],
  [[0, 0, 0, 0], { t: 'LForall', i: 0, u: U('y') }],
  [[0, 0, 0, 0, 0], { t: 'LExact', i: 0 }],
  [[0, 0, 1], { t: 'LConj', i: 0 }],
  [[0, 0, 1, 0], { t: 'LForall', i: 1, u: U('y') }],
  [[0, 0, 1, 0, 0], { t: 'LExact', i: 1 }]
]);
prove('ex drinker', '|- exists x. P(x) -> forall y. P(y)', [
  [[], { t: 'RContract', i: 0 }],
  [[0], { t: 'RExists', i: 0, u: U('z') }],
  [[0, 0], { t: 'RImp', i: 0 }],
  [[0, 0, 0], { t: 'RForall', i: 0 }],
  [[0, 0, 0, 0], { t: 'RExists', i: 1, u: U('y') }],
  [[0, 0, 0, 0, 0], { t: 'RImp', i: 1 }],
  [[0, 0, 0, 0, 0, 0], { t: 'LExact', i: 0 }]
]);
prove('ex f-chain', 'forall x. (P(x)->P(f(x))) |- forall x. (P(x) -> P(f(f(x))))', [
  [[], { t: 'RForall', i: 0 }],
  [[0], { t: 'RImp', i: 0 }],
  [[0, 0], { t: 'LContract', i: 1 }],
  [[0, 0, 0], { t: 'LForall', i: 1, u: U('x') }],
  [[0, 0, 0, 0], { t: 'LForall', i: 2, u: U('f(x)') }],
  [[0, 0, 0, 0, 0], { t: 'LImp', i: 1 }],
  [[0, 0, 0, 0, 0, 0], { t: 'LExact', i: 0 }],
  [[0, 0, 0, 0, 0, 1], { t: 'LImp', i: 2 }],
  [[0, 0, 0, 0, 0, 1, 0], { t: 'LExact', i: 1 }],
  [[0, 0, 0, 0, 0, 1, 1], { t: 'LExact', i: 2 }]
]);
prove('peirce', '((A -> B) -> A) -> A', [
  [[], { t: 'RImp', i: 0 }],
  [[0], { t: 'LImp', i: 0 }],
  [[0, 0], { t: 'RImp', i: 0 }],
  [[0, 0, 0], { t: 'LExact', i: 0 }],
  [[0, 1], { t: 'LExact', i: 0 }]
]);
prove('excluded middle', 'A \\/ ~A', [
  [[], { t: 'RDisj', i: 0 }],
  [[0], { t: 'RNot', i: 1 }],
  [[0, 0], { t: 'LExact', i: 0 }]
]);
prove('forall-exists', '(forall x, P(x)) -> (exists x, P(x))', [
  [[], { t: 'RImp', i: 0 }],
  [[0], { t: 'LForall', i: 0, u: U('z') }],
  [[0, 0], { t: 'RExists', i: 0, u: U('z') }],
  [[0, 0, 0], { t: 'LExact', i: 0 }]
]);
prove('iff refl', '|- A <-> A', [
  [[], { t: 'RIff', i: 0 }],
  [[0], { t: 'RImp', i: 0 }],
  [[0, 0], { t: 'LExact', i: 0 }],
  [[1], { t: 'RImp', i: 0 }],
  [[1, 0], { t: 'LExact', i: 0 }]
]);
prove('iff comm', 'A <-> B |- B <-> A', [
  [[], { t: 'LIff', i: 0 }],
  [[0], { t: 'RIff', i: 0 }],
  [[0, 0], { t: 'RImp', i: 0 }],
  [[0, 0, 0], { t: 'LImp', i: 2 }],
  [[0, 0, 0, 0], { t: 'LExact', i: 0 }],
  [[0, 0, 0, 1], { t: 'LExact', i: 2 }],
  [[0, 1], { t: 'RImp', i: 0 }],
  [[0, 1, 0], { t: 'LImp', i: 1 }],
  [[0, 1, 0, 0], { t: 'LExact', i: 0 }],
  [[0, 1, 0, 1], { t: 'LExact', i: 1 }]
]);
prove('ex falso', 'False |- A', [[[], { t: 'LBot', i: 0 }]]);
prove('verum', '|- True', [[[], { t: 'RTop', i: 0 }]]);
prove('drop truth', 'A, True |- A', [
  [[], { t: 'LTop', i: 1 }], [[0], { t: 'LExact', i: 0 }]
]);
prove('drop false', 'A |- A, False', [
  [[], { t: 'RBot', i: 1 }], [[0], { t: 'LExact', i: 0 }]
]);
prove('contract dup', 'A |- A', [
  [[], { t: 'LContract', i: 0 }], [[0], { t: 'LExact', i: 0 }]
]);
prove('weaken', 'A, B |- A', [
  [[], { t: 'LWeaken', i: 1 }], [[0], { t: 'LExact', i: 0 }]
]);
// invalid: True |- False gets stuck and stays incomplete
(function () {
  let p = K.Goal(seq('True |- False'));
  p = step(p, [], { t: 'LTop', i: 0 });
  p = step(p, [0], { t: 'RBot', i: 0 });
  ok(!K.proofComplete(p), 'True |- False incomplete');
  throwsFailure(() => K.refine(getNode(p, [0, 0]).s, { t: 'LExact', i: 0 }), 'UpdateFailure', 'empty exact fails');
})();

console.log(passed + ' passed, ' + failed + ' failed');
process.exit(failed === 0 ? 0 : 1);
