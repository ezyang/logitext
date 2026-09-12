// Logitext static port — trusted proof kernel for classical first-order logic.
//
// This file is the small trusted kernel. It is pure JavaScript with no DOM
// access and no dependencies. It implements:
//
//   * the abstract syntax of terms, formulas, sequents and proofs
//     (the same abstractions as ClassicalFOL.hs / logitext.ur),
//   * a parser for the concrete syntax (sequents and universe terms),
//   * one-step proof refinement: the textbook cut-free sequent calculus
//     rules for classical first-order logic (LK), and
//   * a proof-completeness check.
//
// The UI (ui.js) is untrusted: every proof step it displays is computed by
// `refine` here, so a UI bug can at worst refuse a valid step or show a
// confusing message; it cannot mark an invalid proof complete, because
// `proofComplete` only inspects kernel-built proof trees.
//
// Soundness argument (for auditors): `refine(s, tac)` pattern-matches the
// principal formula of sequent `s` and returns `Proof(s, q)` where `q`'s
// subgoals are exactly the premises of the corresponding LK rule. The
// eigenvariable rules (LExists/RForall) pick a variable fresh for the whole
// sequent, and instantiation (LForall/RExists) uses capture-avoiding
// substitution. All operations build new objects; inputs are never mutated.

(function (root) {
'use strict';

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

// User errors. The UI maps ParseFailure to "Parse error." and displays
// UpdateFailure messages verbatim. Anything else is an internal bug.
class ParseFailure extends Error {
  constructor(message) {
    super(message || 'Parse error.');
    this.name = 'ParseFailure';
    this.failure = 'ParseFailure';
  }
}
class UpdateFailure extends Error {
  constructor(message) {
    super(message || 'Update failure.');
    this.name = 'UpdateFailure';
    this.failure = 'UpdateFailure';
  }
}

// ---------------------------------------------------------------------------
// Syntax
// ---------------------------------------------------------------------------
//
// Terms (elements of the universe): Fun(name, args). A variable is a nullary
// Fun whose name is bound by an enclosing quantifier; anything else nullary
// is a constant. There are no binders inside terms (first-order logic).
//
// Formulas: Pred(p, args) | Conj(a,b) | Disj(a,b) | Imp(a,b) | Iff(a,b) |
//           Not(a) | Top | Bot | Forall(v,a) | Exists(v,a)
// Sequents: { hyps: [formula], cons: [formula] }
// Proofs: Goal(s) | Proof(s, q), where q is a tactic whose subproof slots
//         (a, b) are filled with proofs. There is no Pending state: refine
//         is synchronous, so a tactic either succeeds (Proof) or throws.
function Fun(f, args) { return { f: f, args: args || [] }; }
function Pred(p, args) { return { t: 'Pred', p: p, args: args || [] }; }
function Conj(a, b) { return { t: 'Conj', a: a, b: b }; }
function Disj(a, b) { return { t: 'Disj', a: a, b: b }; }
function Imp(a, b) { return { t: 'Imp', a: a, b: b }; }
function Iff(a, b) { return { t: 'Iff', a: a, b: b }; }
function Not(a) { return { t: 'Not', a: a }; }
function Top() { return { t: 'Top' }; }
function Bot() { return { t: 'Bot' }; }
function Forall(v, a) { return { t: 'Forall', v: v, a: a }; }
function Exists(v, a) { return { t: 'Exists', v: v, a: a }; }
function Sequent(hyps, cons) { return { hyps: hyps, cons: cons }; }
function Goal(s) { return { t: 'Goal', s: s }; }
function ProofNode(s, q) { return { t: 'Proof', s: s, q: q }; }

// Tactic skeletons (from the UI) look like { t, i, u? } where `i` is the
// index of the principal formula on its side and `u` (for LForall/RExists)
// is an already-parsed term. `refine` fills in subproofs a (and b).

// ---------------------------------------------------------------------------
// Equality (structural; terms have no binders so this is also alpha-equality)
// ---------------------------------------------------------------------------

function equalTerm(u1, u2) {
  if (u1.f !== u2.f || u1.args.length !== u2.args.length) return false;
  for (let k = 0; k < u1.args.length; k++) {
    if (!equalTerm(u1.args[k], u2.args[k])) return false;
  }
  return true;
}

function equalFormula(a, b) {
  if (a.t !== b.t) return false;
  switch (a.t) {
    case 'Pred':
      if (a.p !== b.p || a.args.length !== b.args.length) return false;
      for (let k = 0; k < a.args.length; k++) {
        if (!equalTerm(a.args[k], b.args[k])) return false;
      }
      return true;
    case 'Conj': case 'Disj': case 'Imp': case 'Iff':
      return equalFormula(a.a, b.a) && equalFormula(a.b, b.b);
    case 'Not':
      return equalFormula(a.a, b.a);
    case 'Top': case 'Bot':
      return true;
    case 'Forall': case 'Exists':
      return a.v === b.v && equalFormula(a.a, b.a);
    default:
      return false;
  }
}

// ---------------------------------------------------------------------------
// Free names and fresh variables
// ---------------------------------------------------------------------------

// Collect every "free name": any term head (variable, constant or function
// symbol — all lower-case) not bound by an enclosing quantifier. Predicate
// symbols are upper-case and never bound, so they are ignored. This is
// conservative on purpose: the eigenvariable check and capture-avoiding
// substitution must both treat free function symbols as names to avoid.
function freeNamesTerm(u, bound, out) {
  if (!bound.has(u.f)) out.add(u.f);
  for (const a of u.args) freeNamesTerm(a, bound, out);
  return out;
}

function freeNamesFormula(f, bound, out) {
  switch (f.t) {
    case 'Pred':
      for (const a of f.args) freeNamesTerm(a, bound, out);
      break;
    case 'Conj': case 'Disj': case 'Imp': case 'Iff':
      freeNamesFormula(f.a, bound, out);
      freeNamesFormula(f.b, bound, out);
      break;
    case 'Not':
      freeNamesFormula(f.a, bound, out);
      break;
    case 'Top': case 'Bot':
      break;
    case 'Forall': case 'Exists':
      bound.add(f.v);
      freeNamesFormula(f.a, bound, out);
      bound.delete(f.v);
      break;
  }
  return out;
}

function freeNamesSequent(s) {
  const out = new Set();
  const bound = new Set();
  for (const h of s.hyps) freeNamesFormula(h, bound, out);
  for (const c of s.cons) freeNamesFormula(c, bound, out);
  return out;
}

function freeNamesOfTerm(u) {
  return freeNamesTerm(u, new Set(), new Set());
}

function freeNamesOfFormula(f) {
  return freeNamesFormula(f, new Set(), new Set());
}

// Pick `base` itself when possible (so `forall x. P(x)` on a sequent with
// no free `x` gives `P(x)`), else base0, base1, ...
function freshName(base, avoid) {
  if (!avoid.has(base)) return base;
  let n = 0;
  while (avoid.has(base + n)) n++;
  return base + n;
}

// ---------------------------------------------------------------------------
// Capture-avoiding substitution
// ---------------------------------------------------------------------------

// Validate a term object (defense in depth: the UI only passes parsed terms).
function checkTerm(u) {
  if (!u || typeof u.f !== 'string' || !Array.isArray(u.args)) {
    throw new UpdateFailure('Invalid universe element.');
  }
  for (const a of u.args) checkTerm(a);
  return u;
}

// Substitute term `t` for variable `v` in term `u`. Only nullary occurrences
// of `v` are replaced. A non-nullary occurrence (bound variable used as a
// function head) is higher-order and rejected: there is no first-order
// substitution for it, and silently dropping the binder would be unsound.
function substTerm(u, v, t) {
  if (u.f === v && u.args.length === 0) return t;
  if (u.f === v) {
    throw new UpdateFailure('Cannot instantiate a function variable.');
  }
  if (u.args.length === 0) return u;
  return Fun(u.f, u.args.map(a => substTerm(a, v, t)));
}

// Substitute term `t` for variable `v` in formula `f`, renaming bound
// variables that would otherwise capture free names of `t`.
function substFormula(f, v, t) {
  const tFree = freeNamesOfTerm(t);
  return subst(f);
  function subst(g) {
    switch (g.t) {
      case 'Pred':
        return Pred(g.p, g.args.map(a => substTerm(a, v, t)));
      case 'Conj': return Conj(subst(g.a), subst(g.b));
      case 'Disj': return Disj(subst(g.a), subst(g.b));
      case 'Imp': return Imp(subst(g.a), subst(g.b));
      case 'Iff': return Iff(subst(g.a), subst(g.b));
      case 'Not': return Not(subst(g.a));
      case 'Top': case 'Bot': return g;
      case 'Forall': case 'Exists':
        if (g.v === v) return g; // shadowed: nothing to substitute
        if (tFree.has(g.v)) {
          // Rename the bound variable first to avoid capture.
          const avoid = freeNamesOfFormula(g);
          for (const x of tFree) avoid.add(x);
          avoid.add(v);
          const w2 = freshName(g.v, avoid);
          const renamed = substFormula(g.a, g.v, Fun(w2, []));
          return { t: g.t, v: w2, a: subst(renamed) };
        }
        return { t: g.t, v: g.v, a: subst(g.a) };
      default:
        throw new UpdateFailure('Invalid formula.');
    }
  }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------
//
// Concrete syntax (same as ClassicalFOL.hs):
//
//   sequent   ::= expr ("," expr)* ("|-" | "⊢" expr ("," expr)*)? | empty
//                (no turnstile means empty hypotheses)
//   expr      ::= imp           (right assoc: -> → <-> ↔ <=>)
//   imp       ::= disj          (left assoc:  \/ ∨)
//   disj      ::= conj          (left assoc:  /\ ∧)
//   conj      ::= ("~" | "¬")* term
//   term      ::= "(" expr ")"
//               | "True" | "⊤" | "False" | "⊥"
//               | ("forall" | "∀") lowerId* ("." | ",") expr
//               | ("exists" | "∃") lowerId* ("." | ",") expr
//               | Pred
//   Pred      ::= upperId ("(" universe ("," universe)* ")")?
//   universe  ::= "(" universe ")"
//               | lowerId ("(" universe ("," universe)* ")")?
//
// Identifiers start with an upper/lower-case letter (Unicode-aware, so Γ and
// Δ are propositions) and continue with letters, digits, _ or '. Reserved
// words (exists, forall, fun, True, False, and, or, ex, iff, not) cannot be
// identifiers. Whitespace and nestable (* comments *) are skipped.
//
// One deliberate deviation: the Parsec grammar rejects unspaced double
// negation ("~~A") because of how reservedOp lexing works; we accept it.

const RESERVED_WORDS = new Set([
  'exists', 'forall', 'fun', 'True', 'False',
  'and', 'or', 'ex', 'iff', 'not'
]);

function isUpperStart(ch) { return ch !== undefined && /\p{Lu}/u.test(ch); }
function isLowerStart(ch) { return ch !== undefined && /\p{Ll}/u.test(ch); }
function isIdentCont(ch) { return ch !== undefined && /[\p{L}\p{N}_']/u.test(ch); }

class Parser {
  constructor(input) { this.s = input; this.i = 0; }

  // Skip whitespace and nestable (* *) comments.
  skipWS() {
    for (;;) {
      while (this.i < this.s.length && /\s/.test(this.s[this.i])) this.i++;
      if (this.s[this.i] === '(' && this.s[this.i + 1] === '*') {
        let depth = 0;
        for (;;) {
          if (this.s[this.i] === '(' && this.s[this.i + 1] === '*') {
            depth++; this.i += 2;
          } else if (this.s[this.i] === '*' && this.s[this.i + 1] === ')') {
            depth--; this.i += 2;
            if (depth === 0) break;
          } else if (this.i >= this.s.length) {
            throw new ParseFailure('Unterminated comment.');
          } else {
            this.i++;
          }
        }
      } else {
        return;
      }
    }
  }

  // Match a fixed operator/symbol after whitespace.
  match(sym) {
    this.skipWS();
    if (this.s.substr(this.i, sym.length) === sym) {
      this.i += sym.length;
      return true;
    }
    return false;
  }

  // Match a reserved word (not followed by an identifier character).
  matchWord(w) {
    this.skipWS();
    if (this.s.substr(this.i, w.length) !== w) return false;
    if (isIdentCont(this.s[this.i + w.length])) return false;
    this.i += w.length;
    return true;
  }

  parseUpperId() {
    this.skipWS();
    if (!isUpperStart(this.s[this.i])) {
      throw new ParseFailure('Expected a capitalized identifier.');
    }
    const start = this.i++;
    while (isIdentCont(this.s[this.i])) this.i++;
    const w = this.s.slice(start, this.i);
    if (RESERVED_WORDS.has(w)) throw new ParseFailure('Reserved word: ' + w);
    return w;
  }

  parseLowerId() {
    this.skipWS();
    if (!isLowerStart(this.s[this.i])) {
      throw new ParseFailure('Expected a lower-case identifier.');
    }
    const start = this.i++;
    while (isIdentCont(this.s[this.i])) this.i++;
    const w = this.s.slice(start, this.i);
    if (RESERVED_WORDS.has(w)) throw new ParseFailure('Reserved word: ' + w);
    return w;
  }

  // Peek a lower-case identifier without consuming on failure.
  tryLowerId() {
    const save = this.i;
    try {
      return this.parseLowerId();
    } catch (e) {
      this.i = save;
      if (e && e.failure === 'ParseFailure') return null;
      throw e;
    }
  }

  expectRParen() {
    this.skipWS();
    if (this.s[this.i] !== ')') throw new ParseFailure("Expected ')'.");
    this.i++;
  }

  expectEOF() {
    this.skipWS();
    if (this.i !== this.s.length) throw new ParseFailure('Unexpected input.');
  }

  parseSequent() {
    const first = this.parseExprList();
    if (this.match('|-') || this.match('⊢')) {
      const cons = this.parseExprList();
      this.expectEOF();
      return Sequent(first, cons);
    }
    this.expectEOF();
    return Sequent([], first);
  }

  // commaSep(expr): empty when no expression follows.
  parseExprList() {
    const save = this.i;
    let first;
    try {
      first = this.parseExpr();
    } catch (e) {
      this.i = save;
      if (e && e.failure === 'ParseFailure') return [];
      throw e;
    }
    const out = [first];
    for (;;) {
      this.skipWS();
      if (this.s[this.i] !== ',') return out;
      this.i++;
      out.push(this.parseExpr());
    }
  }

  // Lowest precedence, right associative; -> and <-> share the level.
  parseImp() {
    const a = this.parseDisj();
    if (this.match('<->') || this.match('↔') || this.match('<=>')) {
      return Iff(a, this.parseImp());
    }
    if (this.match('->') || this.match('→')) {
      return Imp(a, this.parseImp());
    }
    return a;
  }

  parseExpr() { return this.parseImp(); }

  parseDisj() {
    let a = this.parseConj();
    for (;;) {
      if (this.match('\\/') || this.match('∨')) {
        a = Disj(a, this.parseConj());
      } else {
        return a;
      }
    }
  }

  parseConj() {
    let a = this.parseNot();
    for (;;) {
      if (this.match('/\\') || this.match('∧')) {
        a = Conj(a, this.parseNot());
      } else {
        return a;
      }
    }
  }

  parseNot() {
    if (this.match('~') || this.match('¬')) return Not(this.parseNot());
    return this.parseTerm();
  }

  parseTerm() {
    this.skipWS();
    if (this.s[this.i] === '(') {
      this.i++;
      const e = this.parseExpr();
      this.expectRParen();
      return e;
    }
    if (this.matchWord('True') || this.match('⊤')) return Top();
    if (this.matchWord('False') || this.match('⊥')) return Bot();
    if (this.matchWord('forall') || this.match('∀')) return this.parseQuant('Forall');
    if (this.matchWord('exists') || this.match('∃')) return this.parseQuant('Exists');
    const name = this.parseUpperId();
    this.skipWS();
    if (this.s[this.i] === '(') {
      this.i++;
      const args = this.parseUniverseList1();
      this.expectRParen();
      return Pred(name, args);
    }
    return Pred(name, []);
  }

  parseQuant(kind) {
    const binders = [];
    for (;;) {
      const id = this.tryLowerId();
      if (id === null) break;
      binders.push(id);
    }
    this.skipWS();
    const c = this.s[this.i];
    if (c !== '.' && c !== ',') {
      throw new ParseFailure("Expected '.' or ',' after quantifier binders.");
    }
    this.i++;
    let body = this.parseExpr();
    for (let k = binders.length - 1; k >= 0; k--) {
      body = { t: kind, v: binders[k], a: body };
    }
    return body;
  }

  parseUniverse() {
    this.skipWS();
    if (this.s[this.i] === '(') {
      this.i++;
      const u = this.parseUniverse();
      this.expectRParen();
      return u;
    }
    const id = this.parseLowerId();
    this.skipWS();
    if (this.s[this.i] === '(') {
      this.i++;
      const args = this.parseUniverseList1();
      this.expectRParen();
      return Fun(id, args);
    }
    return Fun(id, []);
  }

  parseUniverseList1() {
    const out = [this.parseUniverse()];
    for (;;) {
      this.skipWS();
      if (this.s[this.i] !== ',') return out;
      this.i++;
      out.push(this.parseUniverse());
    }
  }
}

function parseSequentString(str) {
  return new Parser(str).parseSequent();
}

function parseUniverseString(str) {
  const p = new Parser(str);
  const u = p.parseUniverse();
  p.expectEOF();
  return u;
}

// ---------------------------------------------------------------------------
// Refinement: the LK inference rules
// ---------------------------------------------------------------------------

// refine(s, tac) checks that tactic `tac` ({t, i, u?}) applies to sequent `s`
// and returns Proof(s, q) with the rule's premises as Goal subproofs. It
// throws UpdateFailure when the rule does not apply. The UI calls this for
// every click; invalid steps never produce proof trees.
//
// Conventions (lists model multisets; order is display order):
//   * rules that decompose a formula on its own side splice the results in
//     at the principal formula's position;
//   * rules that move a formula across the turnstile (LNot, RNot, the left
//     premise of LImp, RImp) prepend it to the other side.
// These match the rule illustrations in the tutorial.

function checkIndex(arr, i, side) {
  if (!Number.isInteger(i) || i < 0 || i >= arr.length) {
    throw new UpdateFailure('Invalid ' + side + ' index.');
  }
}

function removeAt(arr, i) {
  return arr.slice(0, i).concat(arr.slice(i + 1));
}

function spliceAt(arr, i, items) {
  return arr.slice(0, i).concat(items, arr.slice(i + 1));
}

function refine(sequent, tac) {
  const H = sequent.hyps;
  const C = sequent.cons;
  const sub = (hyps, cons) => Goal(Sequent(hyps, cons));
  const done = q => ProofNode(sequent, q);
  const i = tac.i;

  switch (tac.t) {
    // Axioms: an atomic formula occurring on both sides closes the branch.
    case 'LExact': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Pred') throw new UpdateFailure('Not an atomic proposition.');
      if (!C.some(c => equalFormula(f, c))) {
        throw new UpdateFailure('No matching atomic clause on other side of turnstile.');
      }
      return done({ t: 'LExact', i });
    }
    case 'RExact': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Pred') throw new UpdateFailure('Not an atomic proposition.');
      if (!H.some(h => equalFormula(f, h))) {
        throw new UpdateFailure('No matching atomic clause on other side of turnstile.');
      }
      return done({ t: 'RExact', i });
    }

    // Ex falso (left) and verum (right) close their branch.
    case 'LBot': {
      checkIndex(H, i, 'hypothesis');
      if (H[i].t !== 'Bot') throw new UpdateFailure('Not falsity.');
      return done({ t: 'LBot', i });
    }
    case 'RTop': {
      checkIndex(C, i, 'conclusion');
      if (C[i].t !== 'Top') throw new UpdateFailure('Not truth.');
      return done({ t: 'RTop', i });
    }

    // Trivially true hypotheses and trivially false conclusions drop out.
    case 'LTop': {
      checkIndex(H, i, 'hypothesis');
      if (H[i].t !== 'Top') throw new UpdateFailure('Not truth.');
      return done({ t: 'LTop', i, a: sub(removeAt(H, i), C) });
    }
    case 'RBot': {
      checkIndex(C, i, 'conclusion');
      if (C[i].t !== 'Bot') throw new UpdateFailure('Not falsity.');
      return done({ t: 'RBot', i, a: sub(H, removeAt(C, i)) });
    }

    // Conjunction / disjunction.
    case 'LConj': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Conj') throw new UpdateFailure('Not a conjunction.');
      return done({ t: 'LConj', i, a: sub(spliceAt(H, i, [f.a, f.b]), C) });
    }
    case 'RDisj': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Disj') throw new UpdateFailure('Not a disjunction.');
      return done({ t: 'RDisj', i, a: sub(H, spliceAt(C, i, [f.a, f.b])) });
    }
    case 'LDisj': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Disj') throw new UpdateFailure('Not a disjunction.');
      return done({ t: 'LDisj', i,
        a: sub(spliceAt(H, i, [f.a]), C),
        b: sub(spliceAt(H, i, [f.b]), C) });
    }
    case 'RConj': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Conj') throw new UpdateFailure('Not a conjunction.');
      return done({ t: 'RConj', i,
        a: sub(H, spliceAt(C, i, [f.a])),
        b: sub(H, spliceAt(C, i, [f.b])) });
    }

    // Implication. LImp's left premise moves the antecedent across.
    case 'LImp': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Imp') throw new UpdateFailure('Not an implication.');
      return done({ t: 'LImp', i,
        a: sub(removeAt(H, i), [f.a].concat(C)),
        b: sub(spliceAt(H, i, [f.b]), C) });
    }
    case 'RImp': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Imp') throw new UpdateFailure('Not an implication.');
      return done({ t: 'RImp', i,
        a: sub([f.a].concat(H), spliceAt(C, i, [f.b])) });
    }

    // Negation moves its subject across the turnstile.
    case 'LNot': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Not') throw new UpdateFailure('Not a negation.');
      return done({ t: 'LNot', i, a: sub(removeAt(H, i), [f.a].concat(C)) });
    }
    case 'RNot': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Not') throw new UpdateFailure('Not a negation.');
      return done({ t: 'RNot', i, a: sub([f.a].concat(H), removeAt(C, i)) });
    }

    // Iff, via its two implications: A↔B on the left becomes A→B, B→A;
    // on the right it branches into one implication per premise.
    case 'LIff': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Iff') throw new UpdateFailure('Not an iff.');
      return done({ t: 'LIff', i,
        a: sub(spliceAt(H, i, [Imp(f.a, f.b), Imp(f.b, f.a)]), C) });
    }
    case 'RIff': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Iff') throw new UpdateFailure('Not an iff.');
      return done({ t: 'RIff', i,
        a: sub(H, spliceAt(C, i, [Imp(f.a, f.b)])),
        b: sub(H, spliceAt(C, i, [Imp(f.b, f.a)])) });
    }

    // Quantifiers. LForall/RExists instantiate with the given term (with
    // capture-avoiding substitution); LExists/RForall introduce a variable
    // fresh for the whole sequent (the eigenvariable condition).
    case 'LForall': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Forall') throw new UpdateFailure('Not a universal quantification.');
      const u = checkTerm(tac.u);
      const inst = substFormula(f.a, f.v, u);
      return done({ t: 'LForall', i, u, a: sub(spliceAt(H, i, [inst]), C) });
    }
    case 'RExists': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Exists') throw new UpdateFailure('Not an existential quantification.');
      const u = checkTerm(tac.u);
      const inst = substFormula(f.a, f.v, u);
      return done({ t: 'RExists', i, u, a: sub(H, spliceAt(C, i, [inst])) });
    }
    case 'LExists': {
      checkIndex(H, i, 'hypothesis');
      const f = H[i];
      if (f.t !== 'Exists') throw new UpdateFailure('Not an existential quantification.');
      const fresh = freshName(f.v, freeNamesSequent(sequent));
      const inst = substFormula(f.a, f.v, Fun(fresh, []));
      return done({ t: 'LExists', i, a: sub(spliceAt(H, i, [inst]), C) });
    }
    case 'RForall': {
      checkIndex(C, i, 'conclusion');
      const f = C[i];
      if (f.t !== 'Forall') throw new UpdateFailure('Not a universal quantification.');
      const fresh = freshName(f.v, freeNamesSequent(sequent));
      const inst = substFormula(f.a, f.v, Fun(fresh, []));
      return done({ t: 'RForall', i, a: sub(H, spliceAt(C, i, [inst])) });
    }

    // Structural rules: contraction duplicates a formula (needed for
    // completeness without cut), weakening drops one.
    case 'LContract': {
      checkIndex(H, i, 'hypothesis');
      return done({ t: 'LContract', i, a: sub(spliceAt(H, i, [H[i], H[i]]), C) });
    }
    case 'RContract': {
      checkIndex(C, i, 'conclusion');
      return done({ t: 'RContract', i, a: sub(H, spliceAt(C, i, [C[i], C[i]])) });
    }
    case 'LWeaken': {
      checkIndex(H, i, 'hypothesis');
      return done({ t: 'LWeaken', i, a: sub(removeAt(H, i), C) });
    }
    case 'RWeaken': {
      checkIndex(C, i, 'conclusion');
      return done({ t: 'RWeaken', i, a: sub(H, removeAt(C, i)) });
    }

    default:
      throw new UpdateFailure('Unknown tactic.');
  }
}

// A proof is complete when every branch ends in an axiom (a Proof node with
// no Goal descendants). Goal nodes are open; that is all this checks, which
// is all it needs to: only `refine` builds Proof nodes.
function proofComplete(p) {
  if (p.t === 'Goal') return false;
  if (p.t !== 'Proof') return false;
  if (p.q.a !== undefined && !proofComplete(p.q.a)) return false;
  if (p.q.b !== undefined && !proofComplete(p.q.b)) return false;
  return true;
}

// ---------------------------------------------------------------------------
// Canonical printing (for tests and debugging; fully parenthesized)
// ---------------------------------------------------------------------------

function showTerm(u) {
  if (u.args.length === 0) return u.f;
  return u.f + '(' + u.args.map(showTerm).join(', ') + ')';
}

function showFormula(f) {
  switch (f.t) {
    case 'Pred':
      return f.args.length === 0 ? f.p : f.p + '(' + f.args.map(showTerm).join(', ') + ')';
    case 'Conj': return '(' + showFormula(f.a) + ' /\\ ' + showFormula(f.b) + ')';
    case 'Disj': return '(' + showFormula(f.a) + ' \\/ ' + showFormula(f.b) + ')';
    case 'Imp': return '(' + showFormula(f.a) + ' -> ' + showFormula(f.b) + ')';
    case 'Iff': return '(' + showFormula(f.a) + ' <-> ' + showFormula(f.b) + ')';
    case 'Not': return '(~ ' + showFormula(f.a) + ')';
    case 'Top': return 'True';
    case 'Bot': return 'False';
    case 'Forall': return '(forall ' + f.v + '. ' + showFormula(f.a) + ')';
    case 'Exists': return '(exists ' + f.v + '. ' + showFormula(f.a) + ')';
    default: return '?';
  }
}

function showSequent(s) {
  return s.hyps.map(showFormula).join(', ') + ' |- ' + s.cons.map(showFormula).join(', ');
}

// ---------------------------------------------------------------------------
// Exports
// ---------------------------------------------------------------------------

const LogitextKernel = {
  ParseFailure, UpdateFailure,
  Fun, Pred, Conj, Disj, Imp, Iff, Not, Top, Bot, Forall, Exists,
  Sequent, Goal,
  parseSequentString, parseUniverseString,
  refine, proofComplete,
  equalTerm, equalFormula,
  substTerm, substFormula,
  freeNamesSequent, freshName,
  showTerm, showFormula, showSequent
};

root.LogitextKernel = LogitextKernel;
if (typeof module !== 'undefined' && module.exports) {
  module.exports = LogitextKernel;
}

})(typeof globalThis !== 'undefined' ? globalThis : this);
