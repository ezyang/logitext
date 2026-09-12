// Logitext static port — UI layer (untrusted).
//
// This file renders sequents and proof trees, handles clicks, tooltips and
// error display. It is deliberately "hairy": all soundness-critical work is
// delegated to kernel.js (`refine`, `proofComplete`). This file never builds
// Proof nodes itself and never decides completeness on its own.
//
// Rendering and interaction match logitext.ur: the same DOM structure and
// CSS classes (proof, inference, tagBox, junct, turnstile, commaList, ...),
// the same tactic labels and tooltip texts, hover tooltips for underlined
// terms, and a click-to-instantiate prompt (with Contraction) for the
// ∀-left and ∃-right rules.
(function (root) {
'use strict';

const K = root.LogitextKernel;
if (!K) throw new Error('kernel.js must be loaded before ui.js');

// [label, tooltip] for each tactic, as in logitext.ur.
const TACTIC_INFO = {
  LExact: ['', ''],
  LConj: ['(∧l)', 'conjunction left'],
  LDisj: ['(∨l)', 'disjunction left'],
  LImp: ['(→l)', 'implication left'],
  LIff: ['(↔l)', 'iff left'],
  LBot: ['', ''],
  LTop: ['', ''],
  LNot: ['(¬l)', 'negation left'],
  LForall: ['(∀l)', 'universal quantification left'],
  LExists: ['(∃l)', 'existential quantification left'],
  LContract: ['', ''],
  LWeaken: ['', ''],
  RExact: ['', ''],
  RConj: ['(∧r)', 'conjunction right'],
  RDisj: ['(∨r)', 'disjunction right'],
  RImp: ['(→r)', 'implication right'],
  RIff: ['(↔r)', 'iff right'],
  RTop: ['', ''],
  RBot: ['', ''],
  RNot: ['(¬r)', 'negation right'],
  RForall: ['(∀r)', 'universal quantification right'],
  RExists: ['(∃r)', 'existential quantification right'],
  RContract: ['', ''],
  RWeaken: ['', '']
};

const QUANT_HELP = 'To apply this inference rule, you need to specify an ' +
  'individual to instantiate the quantified variable with. This can be any ' +
  'lower-case expression, e.g. z or f(z). Contraction lets you use a ' +
  'hypothesis multiple times.';

const ATOMIC_TITLE = 'A statement of logic which has no logical ' +
  'connectives in it. Examples: A and P(x) are atomic clauses, but A → ' +
  'B is not.';
const TURNSTILE_TITLE = 'The name for the symbol ⊢, which separates ' +
  'hypotheses and conclusions in a sequent. It can be thought of as a kind ' +
  'of meta-implication, distinct from normal implication (→).';

let uidCounter = 0;
function uniqueId(prefix) {
  uidCounter++;
  return (prefix || 'id') + '-' + uidCounter;
}

function textNode(s) { return document.createTextNode(s); }

// ---------------------------------------------------------------------------
// Formula rendering (matches renderLogic/renderUniverse/renderName)
// ---------------------------------------------------------------------------

// Split off a trailing numeric subscript: "x0" -> "x" + sub("0").
function renderName(name) {
  const frag = document.createDocumentFragment();
  let i = 0;
  while (i < name.length && (name[i] < '0' || name[i] > '9')) i++;
  frag.appendChild(textNode(name.slice(0, i)));
  const sub = document.createElement('sub');
  sub.textContent = name.slice(i);
  frag.appendChild(sub);
  return frag;
}

function commaList(items, render) {
  const ul = document.createElement('ul');
  ul.className = 'commaList';
  for (const it of items) {
    const li = document.createElement('li');
    li.appendChild(render(it));
    ul.appendChild(li);
  }
  return ul;
}

function renderUniverse(u) {
  const frag = document.createDocumentFragment();
  frag.appendChild(renderName(u.f));
  if (u.args.length > 0) {
    frag.appendChild(textNode('('));
    frag.appendChild(commaList(u.args, renderUniverse));
    frag.appendChild(textNode(')'));
  }
  return frag;
}

// top: highlight the primary connective; p: parent precedence.
function renderLogic(top, p, f) {
  function sym(s) {
    if (top) {
      const e = document.createElement('span');
      e.className = 'primaryConnective';
      e.textContent = s;
      return e;
    }
    return textNode(s);
  }
  function seq(nodes) {
    const frag = document.createDocumentFragment();
    for (const n of nodes) frag.appendChild(n);
    return frag;
  }
  function paren(cond, node) {
    if (!cond) return node;
    return seq([textNode('('), node, textNode(')')]);
  }
  switch (f.t) {
    case 'Pred': {
      if (f.args.length === 0) return textNode(f.p);
      return seq([textNode(f.p + '('),
        commaList(f.args, renderUniverse), textNode(')')]);
    }
    case 'Conj':
      return paren(p > 3, seq([renderLogic(false, 3, f.a), textNode(' '),
        sym('∧'), textNode(' '), renderLogic(false, 3, f.b)]));
    case 'Disj':
      return paren(p > 2, seq([renderLogic(false, 2, f.a), textNode(' '),
        sym('∨'), textNode(' '), renderLogic(false, 2, f.b)]));
    case 'Imp':
      return paren(p > 1, seq([renderLogic(false, 2, f.a), textNode(' '),
        sym('→'), textNode(' '), renderLogic(false, 1, f.b)]));
    case 'Iff':
      return paren(p > 1, seq([renderLogic(false, 2, f.a), textNode(' '),
        sym('↔'), textNode(' '), renderLogic(false, 2, f.b)]));
    case 'Not':
      return paren(p > 4, seq([sym('¬'), renderLogic(false, 5, f.a)]));
    case 'Top': return textNode('⊤');
    case 'Bot': return textNode('⊥');
    case 'Forall':
      return paren(p > 0, seq([sym('∀'), renderName(f.v), textNode('. '),
        renderLogic(false, 0, f.a)]));
    case 'Exists':
      return paren(p > 0, seq([sym('∃'), renderName(f.v), textNode('. '),
        renderLogic(false, 0, f.a)]));
    default:
      return textNode('?');
  }
}

// ---------------------------------------------------------------------------
// Tooltips (tipsy styling, no dependency)
// ---------------------------------------------------------------------------

let currentTip = null; // { el, timer }

function hideTooltip() {
  if (currentTip && currentTip.timer) clearTimeout(currentTip.timer);
  if (currentTip && currentTip.el.parentNode) {
    currentTip.el.parentNode.removeChild(currentTip.el);
  }
  currentTip = null;
}

document.addEventListener('keydown', function (ev) {
  if (ev.key === 'Escape' || ev.keyCode === 27) hideTooltip();
});

function buildTip() {
  const el = document.createElement('div');
  el.className = 'tipsy tipsy-n';
  el.style.opacity = '0';
  const arrow = document.createElement('div');
  arrow.className = 'tipsy-arrow tipsy-arrow-n';
  const inner = document.createElement('div');
  inner.className = 'tipsy-inner';
  el.appendChild(arrow);
  el.appendChild(inner);
  if (typeof requestAnimationFrame === 'function') {
    requestAnimationFrame(function () {
      el.style.transition = 'opacity 0.15s';
      el.style.opacity = '1';
    });
  } else {
    el.style.opacity = '1';
  }
  return { el, inner };
}

// Gravity 'n': below the anchor, centered.
function positionTip(tipEl, anchorEl) {
  const r = anchorEl.getBoundingClientRect();
  const xOff = window.pageXOffset || document.documentElement.scrollLeft || 0;
  const yOff = window.pageYOffset || document.documentElement.scrollTop || 0;
  let left = r.left + xOff + r.width / 2 - tipEl.offsetWidth / 2;
  if (left < 4) left = 4;
  tipEl.style.left = Math.round(left) + 'px';
  tipEl.style.top = Math.round(r.top + yOff + r.height) + 'px';
}

// Hover tooltip for an element with a title attribute. Like tipsy, the
// title is consumed (so no native tooltip appears) and the element gets
// the 'explained' underline (suppressed inside proofs by the stylesheet).
function attachHover(el) {
  if (el._logitextTip) return;
  const title = el.getAttribute && el.getAttribute('title');
  if (!title) return;
  el._logitextTip = true;
  el.classList.add('explained');
  el.addEventListener('mouseenter', function () {
    hideTooltip();
    const text = el.getAttribute('title') || el.getAttribute('data-orig-title');
    if (!text) return;
    el.removeAttribute('title');
    el.setAttribute('data-orig-title', text);
    const tip = buildTip();
    tip.inner.textContent = text;
    document.body.appendChild(tip.el);
    positionTip(tip.el, el);
    currentTip = { el: tip.el, timer: null };
  });
  el.addEventListener('mouseleave', function () {
    hideTooltip();
  });
}

// Click prompt for ∀-left / ∃-right: a term input with Go and Contraction.
function showQuantPrompt(ws, anchorEl, path, side, index) {
  hideTooltip();
  const tip = buildTip();
  const input = document.createElement('input');
  input.type = 'text';
  input.size = 6;
  const goBtn = document.createElement('button');
  goBtn.textContent = 'Go';
  const contractBtn = document.createElement('button');
  contractBtn.textContent = 'Contract';
  const help = document.createElement('div');
  help.textContent = QUANT_HELP;
  tip.inner.appendChild(input);
  tip.inner.appendChild(textNode(' '));
  tip.inner.appendChild(goBtn);
  tip.inner.appendChild(textNode(' '));
  tip.inner.appendChild(contractBtn);
  tip.inner.appendChild(help);
  document.body.appendChild(tip.el);
  positionTip(tip.el, anchorEl);
  currentTip = { el: tip.el, timer: null };
  // Auto-hide once the mouse has left both the anchor and the tooltip.
  function armLeave() {
    if (currentTip && currentTip.el === tip.el && !currentTip.timer) {
      currentTip.timer = setTimeout(function () {
        if (currentTip && currentTip.el === tip.el) hideTooltip();
      }, 600);
    }
  }
  function cancelLeave() {
    if (currentTip && currentTip.el === tip.el && currentTip.timer) {
      clearTimeout(currentTip.timer);
      currentTip.timer = null;
    }
  }
  anchorEl.addEventListener('mouseleave', armLeave);
  tip.el.addEventListener('mouseleave', armLeave);
  anchorEl.addEventListener('mouseenter', cancelLeave);
  tip.el.addEventListener('mouseenter', cancelLeave);
  function doGo() {
    let u;
    try {
      u = K.parseUniverseString(input.value);
    } catch (e) {
      showError(ws, 'Parse error.');
      return;
    }
    hideTooltip();
    applyTactic(ws, path, side === 'left'
      ? { t: 'LForall', i: index, u }
      : { t: 'RExists', i: index, u });
  }
  input.addEventListener('keydown', function (ev) {
    if (ev.keyCode === 13) {
      ev.preventDefault();
      doGo();
    }
  });
  goBtn.addEventListener('click', doGo);
  contractBtn.addEventListener('click', function () {
    hideTooltip();
    applyTactic(ws, path, side === 'left'
      ? { t: 'LContract', i: index }
      : { t: 'RContract', i: index });
  });
  input.focus();
}

// ---------------------------------------------------------------------------
// Sequent and proof rendering
// ---------------------------------------------------------------------------

// The tactic a click applies, by side and formula shape. Null means "ask
// the user for a term first" (the quantifier prompt).
function tacticForLeft(f, i) {
  switch (f.t) {
    case 'Pred': return { t: 'LExact', i };
    case 'Conj': return { t: 'LConj', i };
    case 'Disj': return { t: 'LDisj', i };
    case 'Imp': return { t: 'LImp', i };
    case 'Iff': return { t: 'LIff', i };
    case 'Not': return { t: 'LNot', i };
    case 'Top': return { t: 'LTop', i };
    case 'Bot': return { t: 'LBot', i };
    case 'Forall': return null;
    case 'Exists': return { t: 'LExists', i };
    default: return null;
  }
}

function tacticForRight(f, i) {
  switch (f.t) {
    case 'Pred': return { t: 'RExact', i };
    case 'Conj': return { t: 'RConj', i };
    case 'Disj': return { t: 'RDisj', i };
    case 'Imp': return { t: 'RImp', i };
    case 'Iff': return { t: 'RIff', i };
    case 'Not': return { t: 'RNot', i };
    case 'Top': return { t: 'RTop', i };
    case 'Bot': return { t: 'RBot', i };
    case 'Forall': return { t: 'RForall', i };
    case 'Exists': return null;
    default: return null;
  }
}

function clauseItem(ws, f, side, index, path) {
  const li = document.createElement('li');
  li.id = uniqueId('c');
  const span = document.createElement('span');
  span.className = 'junct';
  span.appendChild(renderLogic(true, 0, f));
  const tac = side === 'left' ? tacticForLeft(f, index) : tacticForRight(f, index);
  if (tac === null) {
    span.addEventListener('click', function (ev) {
      ev.stopPropagation();
      showQuantPrompt(ws, li, path, side, index);
    });
  } else {
    span.addEventListener('click', function (ev) {
      ev.stopPropagation();
      applyTactic(ws, path, tac);
    });
  }
  li.appendChild(span);
  return li;
}

function renderSequent(ws, s, path) {
  const div = document.createElement('div');
  div.id = uniqueId('seq');
  const left = document.createElement('ul');
  left.className = 'commaList';
  s.hyps.forEach(function (f, i) {
    left.appendChild(clauseItem(ws, f, 'left', i, path));
  });
  const right = document.createElement('ul');
  right.className = 'commaList';
  s.cons.forEach(function (f, i) {
    right.appendChild(clauseItem(ws, f, 'right', i, path));
  });
  const turn = document.createElement('span');
  turn.className = 'turnstile';
  turn.textContent = '⊢';
  turn.setAttribute('title', 'reset');
  turn.addEventListener('click', function (ev) {
    ev.stopPropagation();
    resetNode(ws, path);
  });
  div.appendChild(left);
  div.appendChild(textNode(' '));
  div.appendChild(turn);
  div.appendChild(textNode(' '));
  div.appendChild(right);
  return div;
}

function proofKids(q) {
  if (q.a !== undefined && q.b !== undefined) return [q.a, q.b];
  if (q.a !== undefined) return [q.a];
  return [];
}

function renderProof(ws, proof, path) {
  if (proof.t === 'Goal') {
    const table = document.createElement('table');
    const tr = document.createElement('tr');
    const td = document.createElement('td');
    td.appendChild(renderSequent(ws, proof.s, path));
    const tag = document.createElement('td');
    tag.className = 'tagBox';
    tag.innerHTML = '&nbsp;';
    tr.appendChild(td);
    tr.appendChild(tag);
    table.appendChild(tr);
    return table;
  }
  const wrap = document.createElement('div');
  const top = document.createElement('div');
  proofKids(proof.q).forEach(function (child, k) {
    const sib = document.createElement('div');
    sib.className = 'sibling';
    sib.appendChild(renderProof(ws, child, path.concat([k])));
    top.appendChild(sib);
  });
  wrap.appendChild(top);
  const table = document.createElement('table');
  const tr = document.createElement('tr');
  const td = document.createElement('td');
  td.className = 'inference';
  td.appendChild(renderSequent(ws, proof.s, path));
  const tagBox = document.createElement('td');
  tagBox.className = 'tagBox';
  const tagDiv = document.createElement('div');
  tagDiv.className = 'tag';
  const info = TACTIC_INFO[proof.q.t] || ['?', ''];
  const tag = document.createElement('span');
  tag.id = uniqueId('tag');
  tag.setAttribute('title', info[1]);
  tag.textContent = info[0];
  tagDiv.appendChild(tag);
  tagBox.appendChild(tagDiv);
  tr.appendChild(td);
  tr.appendChild(tagBox);
  table.appendChild(tr);
  wrap.appendChild(table);
  return wrap;
}

// ---------------------------------------------------------------------------
// Workspaces
// ---------------------------------------------------------------------------

function getNode(proof, path) {
  let n = proof;
  for (const k of path) n = (k === 0 ? n.q.a : n.q.b);
  return n;
}

function setNode(proof, path, nn) {
  if (path.length === 0) return nn;
  const q = Object.assign({}, proof.q);
  if (path[0] === 0) q.a = setNode(proof.q.a, path.slice(1), nn);
  else q.b = setNode(proof.q.b, path.slice(1), nn);
  return { t: 'Proof', s: proof.s, q };
}

function makeWorkspace(container, goalString, seed) {
  const ws = { proof: null };
  const working = document.createElement('div');
  working.className = 'working';
  const status = document.createElement('div');
  status.className = 'proofIsIncomplete';
  const proofEl = document.createElement('div');
  proofEl.className = 'proof';
  status.appendChild(proofEl);
  working.appendChild(status);
  const err = document.createElement('div');
  container.appendChild(working);
  container.appendChild(err);
  ws.statusEl = status;
  ws.proofEl = proofEl;
  ws.errEl = err;
  try {
    const s = K.parseSequentString(goalString);
    let proof = K.Goal(s);
    if (seed) proof = K.refine(s, seed);
    ws.proof = proof;
  } catch (e) {
    ws.proof = null;
    if (e && e.failure === 'ParseFailure') showError(ws, 'Parse error.');
    else if (e && e.failure === 'UpdateFailure') showError(ws, e.message);
    else throw e;
  }
  renderWorkspace(ws);
  return ws;
}

function renderWorkspace(ws) {
  hideTooltip();
  while (ws.proofEl.firstChild) ws.proofEl.removeChild(ws.proofEl.firstChild);
  if (ws.proof) {
    ws.proofEl.appendChild(renderProof(ws, ws.proof, []));
    ws.statusEl.className = K.proofComplete(ws.proof) ? 'proofIsDone' : 'proofIsIncomplete';
  } else {
    ws.statusEl.className = 'proofIsIncomplete';
  }
  const spans = ws.proofEl.querySelectorAll('span[title]');
  for (const sp of spans) attachHover(sp);
}

function applyTactic(ws, path, tac) {
  hideTooltip();
  clearError(ws);
  try {
    const node = getNode(ws.proof, path);
    ws.proof = setNode(ws.proof, path, K.refine(node.s, tac));
  } catch (e) {
    if (e && e.failure === 'UpdateFailure') {
      showError(ws, e.message);
      return;
    }
    throw e;
  }
  renderWorkspace(ws);
}

function resetNode(ws, path) {
  hideTooltip();
  clearError(ws);
  const node = getNode(ws.proof, path);
  ws.proof = setNode(ws.proof, path, K.Goal(node.s));
  renderWorkspace(ws);
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

function errorContent(msg) {
  if (msg === 'No matching atomic clause on other side of turnstile.') {
    const frag = document.createDocumentFragment();
    frag.appendChild(textNode('No matching '));
    const a = document.createElement('span');
    a.textContent = 'atomic clause';
    a.setAttribute('title', ATOMIC_TITLE);
    frag.appendChild(a);
    frag.appendChild(textNode(' on other side of '));
    const b = document.createElement('span');
    b.textContent = 'turnstile';
    b.setAttribute('title', TURNSTILE_TITLE);
    frag.appendChild(b);
    frag.appendChild(textNode('.'));
    return frag;
  }
  return textNode(msg);
}

function showError(ws, msg) {
  clearError(ws);
  const d = document.createElement('div');
  d.className = 'errorStyle';
  d.id = uniqueId('err');
  d.appendChild(errorContent(msg));
  d.appendChild(textNode(' '));
  const btn = document.createElement('button');
  btn.textContent = 'Dismiss';
  btn.addEventListener('click', function () { clearError(ws); });
  d.appendChild(btn);
  ws.errEl.appendChild(d);
  const spans = d.querySelectorAll('span[title]');
  for (const sp of spans) attachHover(sp);
}

function clearError(ws) {
  while (ws.errEl.firstChild) ws.errEl.removeChild(ws.errEl.firstChild);
}

// ---------------------------------------------------------------------------
// Init
// ---------------------------------------------------------------------------

function init(pageRoot) {
  pageRoot = pageRoot || document;
  const wss = pageRoot.querySelectorAll('[data-workspace]');
  for (const d of wss) {
    makeWorkspace(d, d.getAttribute('data-workspace'), null);
  }
  const exs = pageRoot.querySelectorAll('[data-example]');
  for (const d of exs) {
    const seed = {
      t: d.getAttribute('data-tactic'),
      i: parseInt(d.getAttribute('data-index'), 10)
    };
    const term = d.getAttribute('data-term');
    if (term !== null) seed.u = K.parseUniverseString(term);
    makeWorkspace(d, d.getAttribute('data-goal'), seed);
  }
  const spans = pageRoot.querySelectorAll('span[title]');
  for (const sp of spans) attachHover(sp);
}

root.LogitextUI = {
  init, makeWorkspace, applyTactic, resetNode,
  renderLogic, renderUniverse, renderName,
  attachHover, hideTooltip
};

})(typeof globalThis !== 'undefined' ? globalThis : this);
