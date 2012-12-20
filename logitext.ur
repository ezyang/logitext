open Json
open Style
open Common

task initialize = Haskell.initClassicalFOL

fun renderName (f : string) : xbody =
  let val i = strcspn f "0123456789"
  in <xml>{[substring f 0 i]}<sub>{[substring f i (strlen f - i)]}</sub></xml>
  end

structure Universe = Json.Recursive(struct
  con t a = string * list a
  fun json_t [a] (_ : json a) : json (t a) = json_record ("1", "2")
end)
type universe = Universe.r
fun renderUniverse ((Universe.Rec (f,xs)) : universe) : xbody =
  <xml>{renderName f}{
    case xs of
    | Cons _ => <xml>(<ul class={commaList}>{List.mapX (fn x => <xml><li>{renderUniverse x}</li></xml>) xs}</ul>)</xml>
    | Nil => <xml/>
    }</xml>
fun zapParseUniverse x : transaction string = return (Haskell.parseUniverseClassicalFOL x)

con logic' a = [Pred = string * list universe,
                Conj = a * a,
                Disj = a * a,
                Imp = a * a,
                Iff = a * a,
                Not = a,
                Top = unit,
                Bot = unit,
                Forall = string * a,
                Exists = string * a]
structure Logic = Json.Recursive(struct
  con t a = variant (logic' a)
  fun json_t [a] (_ : json a) : json (t a) =
    let val json_pred : json (string * list universe) = json_record ("1", "2")
        val json_compound : json (a * a) = json_record ("1", "2")
        val json_quantifier : json (string * a) = json_record ("1", "2")
    in json_variant {Pred = "Pred", Conj = "Conj", Disj = "Disj", Imp = "Imp", Iff = "Iff",
          Not = "Not", Top = "Top", Bot = "Bot", Forall = "Forall", Exists = "Exists"}
    end
end)
type logic = Logic.r

(* hat tip http://blog.sigfpe.com/2010/12/generalising-godels-theorem-with_24.html
   the parser in ClassicalLogic.hs should support this syntax. *)
fun renderParen (b : bool) (r : xbody) : xbody = if b then <xml>({r})</xml> else r
fun renderLogic top p ((Logic.Rec r) : logic) : xbody =
  let fun symbol s = if top then <xml><span class={primaryConnective}>{[s]}</span></xml> else <xml>{[s]}</xml>
  in match r
  {Pred = fn (f, xs) =>
    case xs of
      | Nil => <xml>{[f]}</xml>
      | Cons _ => <xml>{[f]}(<ul class={commaList}>{List.mapX (fn x => <xml><li>{renderUniverse x}</li></xml>) xs}</ul>)</xml>,
   Conj = fn (a, b) => renderParen (p>3) <xml>{renderLogic False 3 a} {symbol "∧"} {renderLogic False 3 b}</xml>,
   Disj = fn (a, b) => renderParen (p>2) <xml>{renderLogic False 2 a} {symbol "∨"} {renderLogic False 2 b}</xml>,
   Imp = fn (a, b) => renderParen (p>1) <xml>{renderLogic False 2 a} {symbol "→"} {renderLogic False 1 b}</xml>,
   Iff = fn (a, b) => renderParen (p>1) <xml>{renderLogic False 2 a} {symbol "↔"} {renderLogic False 2 b}</xml>,
   Not = fn a => renderParen (p>4) <xml>{symbol "¬"}{renderLogic False 5 a}</xml>,
   Top = fn _ => <xml>⊤</xml>,
   Bot = fn _ => <xml>⊥</xml>,
   Forall = fn (x, a) => renderParen (p>0) <xml>{symbol "∀"}{renderName x}. {renderLogic False 0 a}</xml>,
   Exists = fn (x, a) => renderParen (p>0) <xml>{symbol "∃"}{renderName x}. {renderLogic False 0 a}</xml>}
  end

type sequent = { Hyps : list logic, Cons : list logic }
val json_sequent : json sequent = json_record {Hyps = "hyps", Cons = "cons"}

(* our protocol kind of precludes incremental updates or smooth
redrawing. It would be nice if Ur/Web did this for us. *)

con fol_tactic' a = [Cut = logic * a * a,
                     LExact = int,
                     LConj = int * a,
                     LDisj = int * a * a,
                     LImp = int * a * a,
                     LIff = int * a,
                     LBot = int,
                     LTop = int * a,
                     LNot = int * a,
                     LForall = int * universe * a,
                     LExists = int * a,
                     LContract = int * a,
                     LWeaken = int * a]

con constr_tactic' a = fol_tactic' a ++
                     [RExact = unit,
                      RConj = a * a,
                      RDisj = a,
                      RImp = a,
                      RIff = a * a,
                      RTop = unit,
                      RBot = a,
                      RNot = a,
                      RForall = a,
                      RExists = universe * a,
                     ]

con tactic' a = fol_tactic' a ++
                [RExact = int,
                 RConj = int * a * a,
                 RDisj = int * a,
                 RImp = int * a,
                 RIff = int * a * a,
                 RTop = int,
                 RBot = int * a,
                 RNot = int * a,
                 RForall = int * a,
                 RExists = int * universe * a,
                 RWeaken = int * a,
                 RContract = int * a]
con tactic a = variant (tactic' a)
fun json_tactic [a] (_ : json a) : json (tactic a) =
  let val json_cut : json (logic * a * a) = json_record ("1", "2", "3")
      val json_single : json (int * a) = json_record ("1", "2")
      val json_double : json (int * a * a) = json_record ("1", "2", "3")
      val json_instance : json (int * universe * a) = json_record ("1", "2", "3")
  in json_variant {Cut = "Cut", LExact = "LExact", LConj = "LConj", LDisj = "LDisj",
        LImp = "LImp", LIff = "LIff", LBot = "LBot", LTop = "LTop", LNot = "LNot", LForall = "LForall", LExists = "LExists",
        LContract = "LContract", LWeaken = "LWeaken", RExact = "RExact", RConj = "RConj", RDisj = "RDisj",
        RImp = "RImp", RIff = "RIff", RTop = "RTop", RBot = "RBot", RNot = "RNot", RForall = "RForall", RExists = "RExists",
        RWeaken = "Rweaken", RContract = "RContract"}
  end

fun tacticDescription [a] (t : tactic a) : string = match t
   {
     Cut        = fn _ => "logical cut"
   , LExact     = fn _ => ""
   , LConj      = fn _ => "conjunction left"
   , LDisj      = fn _ => "disjunction left"
   , LImp       = fn _ => "implication left"
   , LIff       = fn _ => "iff left"
   , LBot       = fn _ => ""
   , LTop       = fn _ => ""
   , LNot       = fn _ => "negation left"
   , LForall    = fn _ => "universal quantification left"
   , LExists    = fn _ => "existential quantification left"
   , LContract  = fn _ => ""
   , LWeaken    = fn _ => ""
   , RExact     = fn _ => ""
   , RConj      = fn _ => "conjunction right"
   , RDisj      = fn _ => "disjunction right"
   , RImp       = fn _ => "implication right"
   , RIff       = fn _ => "iff right"
   , RTop       = fn _ => ""
   , RBot       = fn _ => ""
   , RNot       = fn _ => "negation right"
   , RForall    = fn _ => "universal quantification right"
   , RExists    = fn _ => "existential quantification right"
   , RContract  = fn _ => ""
   , RWeaken    = fn _ => ""
   }

fun tacticRenderName [a] (t : tactic a) : string = match t
   {
     Cut        = fn _ => "(cut)"
   , LExact     = fn _ => ""
   , LConj      = fn _ => "(∧l)"
   , LDisj      = fn _ => "(∨l)"
   , LImp       = fn _ => "(→l)"
   , LIff       = fn _ => "(↔l)"
   , LBot       = fn _ => ""
   , LTop       = fn _ => ""
   , LNot       = fn _ => "(¬l)"
   , LForall    = fn _ => "(∀l)"
   , LExists    = fn _ => "(∃l)"
   , LContract  = fn _ => ""
   , LWeaken    = fn _ => ""
   , RExact     = fn _ => ""
   , RConj      = fn _ => "(∧r)"
   , RDisj      = fn _ => "(∨r)"
   , RImp       = fn _ => "(→r)"
   , RIff       = fn _ => "(↔r)"
   , RTop       = fn _ => ""
   , RBot       = fn _ => ""
   , RNot       = fn _ => "(¬r)"
   , RForall    = fn _ => "(∀r)"
   , RExists    = fn _ => "(∃r)"
   , RContract  = fn _ => ""
   , RWeaken    = fn _ => ""
   }

con end_user_failure = variant [UpdateFailure = unit, ParseFailure = unit]
val json_end_user_failure : json end_user_failure = json_variant {UpdateFailure = "UpdateFailure", ParseFailure = "ParseFailure"}

con result a = variant [EndUserFailure = end_user_failure, InternalFailure = string, Success = a]
fun json_result [a] (_ : json a) : json (result a) =
    json_variant {EndUserFailure = "EndUserFailure", InternalFailure = "InternalFailure", Success = "Success"}

structure Proof = Json.Recursive(struct
  con t a = variant [Goal = sequent,
                     Pending = sequent * tactic int,
                     Proof = sequent * tactic a]
  fun json_t [a] (j : json a) : json (t a) =
    let val json_tactic : json (tactic a) = json_tactic
        val json_pending : json (sequent * tactic int) = json_record ("1", "2")
        val json_proof : json (sequent * tactic a) = json_record ("1", "2")
    in json_variant {Goal = "Goal", Pending = "Pending", Proof = "Proof"}
    end
end)
type proof = Proof.r

fun proofComplete (Proof.Rec p) : bool =
    match p {Goal = fn _ => False,
             Pending = fn _ => False,
             Proof = fn (_, t) =>
                let val empty   = declareCase (fn _ (_ : int) => True)
                    val single  = declareCase (fn _ (_ : int, a) => proofComplete a)
                    val singleQ = declareCase (fn _ (_ : int, _ : Universe.r, a) => proofComplete a)
                    val double  = declareCase (fn _ (_ : int, a, b) => andB (proofComplete a) (proofComplete b))
                    val cut     = declareCase (fn _ (_ : Logic.r, a, b) => andB (proofComplete a) (proofComplete b))
                in typeCase t end
             }

fun renderSequent showError (h : proof -> transaction unit) (s : sequent) : transaction xbody =
    let fun makePending (x : tactic int) : transaction unit = h (Proof.Rec (make [#Pending] (s, x)))
        fun makePendingU (f : universe -> tactic int) (g : tactic int) : transaction xbody =
                r <- source "";
                let val doPrompt =
                    rawu <- get r;
                    u <- rpc (zapParseUniverse rawu);
                    match (fromJson u : result universe)
                    { Success = fn x => makePending (f x)
                    , EndUserFailure = fn e => match e
                        { UpdateFailure = fn () => showError <xml>Invalid universe element.</xml>
                        , ParseFailure = fn () => showError <xml>Parse error.</xml>
                        }
                    , InternalFailure = fn s => showError <xml>{[s]}</xml>
                    }
                in nid <- fresh;
                   return <xml><div>
                      <ctextbox id={nid} size=6 source={r}
                        onkeyup={fn k => if k.KeyCode = 13
                            then doPrompt
                            else return ()} />
                      {activeCode (giveFocus nid)}
                      <button value="Go" onclick={fn _ => doPrompt} />
                      <button value="Contract" onclick={fn _ => makePending g} />
                      <div>
                        To apply this inference rule, you need to specify an individual to instantiate the quantified variable with.  This can be any lower-case expression, e.g. z or f(z). Contraction lets you use a hypothesis multiple times.
                      </div>
                    </div></xml>
                end
    in
    left <- List.mapXiM (fn i (Logic.Rec x) =>
              nid <- fresh;
              let val bod = <xml><li id={nid}><span class={junct} onclick={fn _ =>
                  match x {
                    Pred   = fn _ => makePending (make [#LExact] i),
                    Conj   = fn _ => makePending (make [#LConj] (i, 0)),
                    Disj   = fn _ => makePending (make [#LDisj] (i, 0, 1)),
                    Imp    = fn _ => makePending (make [#LImp] (i, 0, 1)),
                    Iff    = fn _ => makePending (make [#LIff] (i, 0)),
                    Not    = fn _ => makePending (make [#LNot] (i, 0)),
                    Top    = fn _ => makePending (make [#LTop] (i, 0)),
                    Bot    = fn _ => makePending (make [#LBot] i),
                    Forall = fn _ => return (),
                    Exists = fn _ => makePending (make [#LExists] (i, 0))
                    }}>{renderLogic True 0 (Logic.Rec x)}</span></li></xml>
                  val default = fn [a] => declareCase (fn _ (_ : a) => return bod : transaction xbody)
              in @typeCase x (_ ++ {
                   Forall = declareCase (fn _ _ =>
                     r <- makePendingU (fn u => make [#LForall] (i, u, 0)) (make [#LContract] (i, 0));
                     return (activate bod (Js.tipHTML nid r)))
                 }) _
              end
            ) s.Hyps;
    right <- List.mapXiM (fn i (Logic.Rec x) =>
              nid <- fresh;
              let val bod = <xml><li id={nid}><span class={junct} onclick={fn _ => match x {
                    Pred   = fn _ => makePending (make [#RExact] i),
                    Conj   = fn _ => makePending (make [#RConj] (i, 0, 1)),
                    Disj   = fn _ => makePending (make [#RDisj] (i, 0)),
                    Imp    = fn _ => makePending (make [#RImp] (i, 0)),
                    Iff    = fn _ => makePending (make [#RIff] (i, 0, 1)),
                    Not    = fn _ => makePending (make [#RNot] (i, 0)),
                    Top    = fn _ => makePending (make [#RTop] i),
                    Bot    = fn _ => makePending (make [#RBot] (i, 0)),
                    Forall = fn _ => makePending (make [#RForall] (i, 0)),
                    Exists = fn _ => return ()
                    }}>
                {renderLogic True 0 (Logic.Rec x)}</span></li></xml>
                val default = fn [a] => declareCase (fn _ (_ : a) => return bod : transaction xbody)
              in @typeCase x (_ ++ {
                   Exists = declareCase (fn _ _ =>
                     r <- makePendingU (fn u => make [#RExists] (i, u, 0)) (make [#RContract] (i, 0));
                     return (activate bod (Js.tipHTML nid r)))
                 }) _
              end
        ) s.Cons;
    nid <- fresh;
    return <xml><div id={nid}><ul class={commaList}>{left}</ul> <span class={turnstile} title="reset" onclick={fn _ => h (Proof.Rec (make [#Goal] s))}>⊢</span> <ul class={commaList}>{right}</ul></div></xml>
  end

fun renderProof showError (h : proof -> transaction unit) ((Proof.Rec r) : proof) : transaction xbody = match r
  {Goal = fn s =>
       (* XXX It would be neat if mouse over caused this to change to show what the result would be, but a little difficult due to the necessity of a redraw *)
       sequent <- renderSequent showError h s;
       return <xml><table><tr><td>{sequent}</td><td class={tagBox}>&nbsp;</td></tr></table></xml>,
   Pending = fn (s, t) => return <xml>...</xml>,
   Proof = fn (s, t) =>
       sequent <- renderSequent showError h s;
       let fun render f t : transaction xbody =
                sib <- renderProof showError (fn x => h (Proof.Rec (make [#Proof] (s, f x)))) t;
                return <xml><div class={sibling}>{sib}</div></xml>
           val cut     = declareCase (fn f (l : logic, a : proof, b : proof) =>
                Monad.liftM2 join
                    (render (fn x => f (l, x, b)) a)
                    (render (fn x => f (l, a, x)) b) : transaction xbody)
           val empty   = declareCase (fn _ (_ : int) =>
                return <xml/> : transaction xbody)
           val single  = declareCase (fn f (n : int, a : proof) =>
                render (fn x => f (n, x)) a : transaction xbody)
           val singleQ = declareCase (fn f (n : int, u : universe, a : proof) =>
                render (fn x => f (n, u, x)) a : transaction xbody)
           val double  = declareCase (fn f (n : int, a : proof, b : proof) =>
                Monad.liftM2 join
                    (render (fn x => f (n, x, b)) a)
                    (render (fn x => f (n, a, x)) b) : transaction xbody)
       in
       top <- typeCase t;
       nid <- fresh;
       return <xml>
        <div>{top}</div>
        <table>
          <tr>
            <td class={inference}>{sequent}</td>
            <td class={tagBox}>
                <div class={tag}>{activate <xml><span title={tacticDescription t} id={nid}>{[tacticRenderName t]}</span></xml> (Js.tip nid)}</div>
            </td>
          </tr>
        </table></xml>
       end
    }

fun zapRefine (x : proof) : transaction string  = return (Haskell.refineClassicalFOL (toJson x))

val wSequent : xbody =
    <xml><span title="A statement of provability.  Γ ⊢ Δ states that given the
    hypotheses Γ, one of the conclusions Δ is provable.">sequent</span></xml>

val wClause : xbody =
    <xml><span title="A statement of logic. Inside a sequent, clauses
    are either hypotheses or conclusions.">clause</span></xml>

val wTurnstile : xbody =
    <xml><span title="The name for the symbol ⊢, which separates hypotheses
    and conclusions in a sequent.  It can be thought of as a kind of
    meta-implication, distinct from normal implication (→).">turnstile</span></xml>

val wImplication : xbody =
    <xml><span title="Denoted by the arrow →, as in A → B, it means that
    if A is true, then B is true.  Note that A → B and B → A are
    different statements.">implication</span></xml>

val wAtomicClause : xbody =
    <xml><span title="A statement of logic which has no logical
    connectives in it.  Examples: A and P(x) are atomic clauses, but A →
    B is not.">atomic clause</span></xml>

val wConjunction : xbody =
    <xml><span title="Denoted by the symbol ∧, conjunction is
    logical AND, which is true only when both sides are
    true.">conjunction</span></xml>

val wDisjunction : xbody =
    <xml><span title="Denoted by the symbol ∨, disjunction is
    logical OR, which is true as long as one or another side
    is true (or both).">disjunction</span></xml>

val wProgress : xbody =
    <xml><span title="A proof can make progress if there is a valid
    deductive step proceeding from it; that is, you can click a clause
    and have more goals be generated.  Otherwise, it is stuck.">progress</span></xml>

val wLogicalOperator : xbody =
    <xml><span title="Any symbol which operates on logical propositions.
    Examples include conjunction, disjunction and implication.  A clause with
    no logical operators is atomic.">logical operator</span></xml>

val wGoal : xbody =
    <xml><span title="Any sequent which needs to be proved in order to
    complete the proof tree.  You can visually identify these as sequents
    on the top of the proof tree with no bar on top.">goal</span></xml>

val wBackwardsDeduction : xbody =
    <xml><span title="A style of logical inference, where you start with
    the desired conclusion and work backwards.  Opposite of forward inference,
    where you start with axioms and then deduce statements.">backwards deduction</span></xml>

val wInferenceRule : xbody =
    <xml><span title="A rule which says what valid inferences are.  An inference
    rule is specified by writing hypotheses, a horizontal bar, and then the valid
    conclusion.  In backwards deduction, an inference rule says what you need
    to prove in order to show the current goal to be true.">inference rule</span></xml>

val wQuantifier : xbody =
    <xml><span title="Any logical operator which binds a new variable.  For all (∀) and exists (∃)
    are the two quantifiers in first order logic.">quantifier</span></xml>

fun handleResultProof handler v proofStatus err (z : string) =
    let val clearError = set err <xml/>
        fun showError (e : xbody) =
            nid <- fresh;
            set err (activate <xml><div class={errorStyle} id={nid}>{e} <button onclick={fn _ => clearError} value="Dismiss" /></div></xml> (Js.tipInner nid))
    in match (fromJson z : result proof)
        { Success = fn r => clearError;
                            bind (renderProof showError handler r) (set v);
                            set proofStatus (if proofComplete r then proofIsDone else proofIsIncomplete)
        , EndUserFailure = fn e => set proofStatus proofIsIncomplete; match e
           (* XXX makes assumption about what update failures are... *)
            { UpdateFailure = fn () => showError <xml>No matching {wAtomicClause} on other side of {wTurnstile}.</xml>
            , ParseFailure = fn () => showError <xml>Parse error.</xml>
            }
        , InternalFailure = fn s => showError <xml>{[s]}</xml>
        }
    end

fun mkWorkspaceRaw showErrors pf =
  v <- source <xml/>;
  err <- source <xml/>;
  proofStatus <- source proofIsIncomplete; (* should actually be a datatype *)
  bamf <- source <xml/>;
  let fun handler x =
    set proofStatus proofIsPending;
    set bamf (activeCode Js.clearTooltips);
    bind (rpc (zapRefine x)) (handleResultProof handler v proofStatus err)
  in return <xml>
          <div class={working}>
            <dyn signal={signal bamf} />
            <div dynClass={signal proofStatus}>
              <div class={proof}>
                <dyn signal={signal v}/>
              </div>
            </div>
          </div>
          {if showErrors then <xml><dyn signal={signal err}/></xml> else <xml/>}
          {activeCode (handleResultProof handler v proofStatus err pf)}
    </xml>
  end

fun workspace goal =
  let val parsedGoal = Haskell.startClassicalFOL goal
  in <xml><active code={mkWorkspaceRaw True parsedGoal} /></xml>
  end
fun example proof = <xml><active code={mkWorkspaceRaw True proof} /></xml>

fun tutorial () =
  return <xml>
  <head>
    <title>Interactive Tutorial of the Sequent Calculus</title>
    {headTemplate}
  </head>
  <body>
    <div class={page}>

      <p><i>This interactive tutorial will teach you how to use the
      sequent calculus, a simple set of rules with which you can use
      to show the truth of statements in first order logic.  It
      is geared towards anyone with some background in writing software
      for computers, with knowledge of basic boolean logic.</i></p>

      <h2>Introduction</h2>

      <p><i>Proving theorems is not for the mathematicians anymore: with
      theorem provers, it's now a job for the hacker.</i> — Martin Rinard</p>

      <p>I want to tell you about a neat system called the <i>sequent
      calculus</i>. It's a way of deducing whether or not a statement is
      true, but unlike proofs where the prover makes wild leaps
      of deduction from one statement to another, the sequent calculus
      always has a simple set of rules that is easy to check the
      validity of.</p>

      <p>An ordinary software engineer rarely has any need for proof,
      even though he deals with the issues of truth and falsehood on a
      daily basis.  His tool is boolean logic, where there are
      propositions, and they are either true or false, and even in the
      most complicated cases, the truth of a statement like "A or not A"
      can be checked by checking all of the possible cases using a truth
      table.</p>

      <p>However, as a tool for describing the world, Boolean logic is
      inflexible.  Suppose I claim "all men are mortal" and "Socrates is
      a man". I should then be able to deduce "Socrates is mortal";
      however, in Boolean logic, these three propositions have no
      relationship with each other.  Instead, I would like a way to say the word "all", a
      <i>quantifier</i>, is special in some sense.  It deserves to be
      an operator like AND/OR/NOT, and have some meaning assigned to it.</p>

      <p>However, now there's a problem: we can't figure out if a
      logical statement is true anymore by writing out the truth table.
      We can't check that a statement about "all" individuals is true by
      checking each individual one-by-one: there may be too many.  We need another way of
      reasoning about these statements, which are called statements
      in <i>first-order logic</i>.</p>

      <p>There are a lot of ways to think about first-order logic.  In
      this tutorial, we'll focus on one fundamental way of dealing with
      statements.  It will be a little unintuitive at times, but it will
      have the benefit of being precise, unambiguous and simple.  It is
      so precise and simple we can program it into a computer.  But it
      is also powerful enough to let us derive any true statement in
      first-order logic.  You should come out of this tutorial with
      an appreciation of how to do the symbolic manipulation of
      the sequent calculus.</p>

      <h2>How it works</h2>

      <p>The sequent calculus operates by a set of rules, not all of
      which are intuitively obvious.  Our goal is to <b>learn the rules
      of the game</b>, while at the same time becoming familiar with the
      <b>notation</b> and <b>terminology</b> which is conventionally
      used by mathematicians on pen and paper.</p>

      <p>All of the examples in this document are interactive.
      Technical terms are <span title="This is an explanation of the
      term.">underlined</span>; you can mouse over them for a
      definition.  You can reset your changes to an example by clicking
      the {wTurnstile} symbol (⊢).</p>

      <p><b>Sequents and axioms.</b> The turnstile is always included
      in a {wSequent}, an example of which is displayed below.  You can
      interact with it by clicking on the A, which are {wClause}s.  You
      can read the sequent as "A implies A": the {wTurnstile} can be
      thought of as a sort of {wImplication}. In this example, when you
      click on the A, a bar appears on top, which indicates the sequent
      is <span title="That is, we can assume it is true without
      proof.">axiomatically true</span>.  The only axioms in this system
      are when some {wAtomicClause} appears on both sides of the
      {wTurnstile}.  We're done when all sequents have bars
      over them.</p>

      {workspace "A |- A"}

      <p><b>Hypotheses on the left.</b> Read the following {wSequent} as "Γ and A imply A."
      If you click on A, you will successfully complete the proof, but if you click
      on Γ, you will fail (because it is not a conclusion you are proving.) Γ (a capital Greek gamma)
      conventionally indicates hypotheses which are not relevant.</p>

      {workspace "Γ, A |- A"}

      <p><b>Conclusions on the right.</b>  Read the following sequent as
      "A implies A or Δ". Δ (a capital Greek delta) conventionally
      indicates conclusions which are not relevant.  Notice that the
      comma means {wConjunction} on the left but <b>{wDisjunction}</b>
      on the right. One reason for this is that it makes it very easy to
      identify axiomatically true statements: if an {wAtomicClause} is
      on the left and on the right, then you're done.)</p>

      {workspace "A |- A, Δ"}

      <p><b>Backwards deduction.</b>  Up until now, clicking on a {wClause} has either
      told us "this {wSequent} is axiomatically true" (completing the
      proof) or given us an error.  These make for very boring proofs:
      what about {wLogicalOperator}s?  When you click on a clause that contains
      a logical operator, the system generates one or more further {wGoal}s,
      which you need to prove.  It's its way of saying, "In order to show
      A ∨ B ⊢ A, B is true, you need to show A ⊢ A, B is true and B ⊢ A, B is true."
      Notice that in both of the subgoals, there no longer is a {wDisjunction}; in
      sequent calculus, we use {wBackwardsDeduction} to get rid of logical
      operators until we have {wAtomicClause}s.</p>

      {workspace "A \/ B |- A, B"}

      <p><b>Inference rules.</b>  Now, it is great that the computer has
      told you what new {wGoal}s you need to prove, but what if you
      wanted to write out the proof by hand?  You need to know what to
      write down.  Fortunately, for each {wLogicalOperator}, there are
      exactly two {wInferenceRule}s which say what new goals are
      generated: one for when it's on the left side of the {wTurnstile}
      (hypothesis), and one when it's on the right (conclusion).
      You applied the rule for left-{wDisjunction} in the previous example:
      here is the rule written out in general.</p>

      <div class={proofIsDone}>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Disj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LDisj\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}}]}}}}}}}"}</div>

      <p>The Γ and Δ are placeholders for other hypotheses and conclusions:
      in the previous example Γ was empty, and Δ was "A, B" (two clauses).
      The text on the right of the bar indicates what rule was
      applied: the first letter indicates the logical operator involved,
      and the second letter indicates <b>l</b>eft or <b>r</b>ight.
      Together, axioms and inference rules make up the entirety of our
      deductive system: they are <i>all you need</i>. We'll now go on a
      tour of all the inference rules in first-order logic.</p>

      <p><b>Trivial rules.</b>  Recall that all of the hypotheses on the
      left side of the {wTurnstile} can be thought of as ANDed together, and
      the conclusions on the right side ORed together.  Thus, if I have a hypothesis
      which is an AND, or a conclusion which is an OR, we can very easily get
      rid of the logical operator.</p>

      <table class={centerTable}>
        <tr>
          <td>{workspace "Γ, A /\ B |- A, Δ"}</td>
          <td>{workspace "Γ, A |- A \/ B, Δ"}</td>
        </tr>
      </table>

      <p><b>Meta-implication rule.</b>  The {wTurnstile} itself can be thought
      of as implication, so to prove A → B, I can assume A as a hypothesis
      and prove B instead ("moving" the clause to the left side of the turnstile.)</p>

      {workspace "Γ |- A -> A, Δ"}

      <p>It's worth noting that, because this is classical logic, you can use
      any hypothesis generated this way for any other conclusion (a sort
      of "bait and switch").  It's worth taking some time to convince yourself why this
      is allowed, since it shows up in other {wInferenceRule}s too.  Here is a simple example of this:</p>

      {workspace "|- (A -> B) \/ A"}

      <p><b>Branching rules.</b>  What about {wConjunction}, {wDisjunction} and {wImplication}
      on the other side of the {wTurnstile}?  All of these generate <i>two</i> new
      {wGoal}s, both of which need to be proved.</p>

      <table class={centerTable}>
        <tr>
          <td>{workspace "Γ, A, B |- A /\ B, Δ"}</td>
          <td>{workspace "Γ, A \/ B |- A, B, Δ"}</td>
        </tr>
        <tr>
          <td colspan=2>{workspace "Γ, A, A -> B |- B, Δ"}</td>
        </tr>
      </table>

      <p><b>Negation rules.</b> Negation is a strange operator: applying its inference
      rule moves the un-negated clause to the other side of the turnstile.</p>

      <table class={centerTable}>
        <tr>
          <td>{workspace "Γ, A, ~A |- Δ"}</td>
          <td>{workspace "Γ |- ~A, A, Δ"}</td>
        </tr>
      </table>

      <p><b>Quantifier rules.</b> The rules for the {wQuantifier}s are
      quite interesting.  Which of these four statements is true?</p>

      <table class={centerTable}>
        <tr>
          <td>{workspace "Γ, forall x. P(x) |- P(a), Δ"}</td>
          <td>{workspace "Γ, P(a) |- forall x. P(x), Δ"}</td>
        </tr>
        <tr>
          <td>{workspace "Γ, exists x. P(x) |- P(a), Δ"}</td>
          <td>{workspace "Γ, P(a) |- exists x. P(x), Δ"}</td>
        </tr>
      </table>

      <p>You should only be able to prove two of the four: forall left
      (∀l) and exists right (∃r).  In both cases, the system asks you
      for an individual to instantiate the variable with.  This variable
      can be anything, including variables which already exist in the
      expression.  Intuitively, it should make sense why these are the
      two true statements: in the case of forall, if I know something
      about all individuals, I know something about a particular
      individual too; in the case of exists, in order to show the
      existence of something, all you need to do is produce it.  The
      "particular individual" and "the individual which exists" are
      precisely what the system asks you for.</p>

      <p>In the case of the forall right (∀r) rule and the exists left
      (∃l), the system picks a variable for you. But it doesn't pick any
      old variable: the variable it picks is required to be distinct from
      anything pre-existing in the sequent: this is often referred to as
      the "no free occurrence" rule.  One intuition for why the system
      is constrained in this way is to consider this: it is generally
      harder to prove something is true for all individuals than it is
      to show it is true for only one.</p>

      <p>In practice, this means is that the order you apply tactics is
      important:</p>

      {workspace "(forall x. P(x)) |- (forall x. P(x))"}

      <p>If you start off with the left-forall, when you apply the
      right-forall, the system will always give you something that
      doesn't match what you originally picked, and then you are stuck!
      But it is easy to complete in the other direction.</p>

      <p>One last note: the "contraction" button duplicates a hypothesis
      or goal, so you can reuse it later (say, you want to say that
      because all people are mortal, then Bob is mortal, AND Sally is
      mortal).  Use of this <i>structural rule</i> may be critical to
      certain proofs; you will get stuck otherwise.  (This rule is
      somewhat paradoxically called contraction because when you read the
      rule in the normal top-down direction, it "contracts" two identical
      hypotheses into a single one.)</p>

      <p><b>Summary.</b> Here are all the inference rules for first order logic:</p>

      <table class={classes rules green}>
        <tr>
          <td colspan=2>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}}]},\"2\":{\"LExact\":1}}}}"}</td>
        </tr>
        <tr>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Not\":{\"Pred\":{\"1\":\"A\",\"2\":[]}}}]},\"2\":{\"LNot\":{\"1\":1,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}"}</td>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Not\":{\"Pred\":{\"1\":\"A\",\"2\":[]}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RNot\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}"}</td>
        </tr>
        <tr>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Conj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LConj\":{\"1\":1,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}}}}}}}"}</td>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Conj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RConj\":{\"1\":0,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"B\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}"}</td>
        </tr>
        <tr>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Disj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LDisj\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}}]}}}}}}}"}</td>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Disj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RDisj\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}"}</td>
        </tr>
        <tr>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Imp\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LImp\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}"}</td>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Imp\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RImp\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"B\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}"}</td>
        </tr>
        <tr>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Forall\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}}]},\"2\":{\"LForall\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"z\",\"2\":[]}]}}]}},\"2\":{\"1\":\"z\",\"2\":[]}}}}}}"}</td>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Forall\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RForall\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}"}</td>
        </tr>
        <tr>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Exists\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}}]},\"2\":{\"LExists\":{\"1\":1,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}]}}}}}}}"}</td>
          <td>{example "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Exists\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RExists\":{\"1\":0,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"z\",\"2\":[]}]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}},\"2\":{\"1\":\"z\",\"2\":[]}}}}}}"}</td>
        </tr>
      </table>

      <p>With these {wInferenceRule}s, you have the capability to
      prove everything in first-order logic.</p>

      <h2>Exercises</h2>

      {workspace "A /\ B |- B /\ A"}
      {workspace "A \/ B |- B \/ A"}
      {workspace "~(A \/ B) -> ~A /\ ~B"}
      {workspace "(forall x. P(x)) /\ (forall x. Q(x)) -> forall y. P(y) /\ Q(y)"}

      <p>Hint: these two require <span title="...which duplicates a hypothesis or conclusion and lets you use it twice, with different instantiations of the variables.">contraction</span>.</p>

      {workspace "|- exists x. P(x) -> forall y. P(y)"}
      {workspace "forall x. (P(x)->P(f(x))) |- forall x. (P(x) -> P(f(f(x))))"}

      <h2>Conclusion</h2>

      <p>I want to leave you with some parting words about why I find
      this topic interesting.</p>

      <p>First-order logic is well worth studying, because it is a
      simple yet powerful tool for modelling the world and writing
      specifications and constraints.  These constraints can be given to
      tools called SMT solvers, which can then automatically determine
      how to satisfy these constraints.  You can't do that with plain
      English!</p>

      <p>A common complaint with a formal systems like the sequent
      calculus is the "I clicked around and managed to prove this, but
      I'm not really sure what happened!" This is what Martin means by
      the hacker mentality: it is now possible for people to prove
      things, even when they don't know what they're doing.  The
      computer will ensure that, in the end, they will have gotten it
      <i>right</i>.  (You don't even have to test it, and there are no
      bugs!  Of course, it does help to know what you are doing.)  Writ
      large, working with this demo is like working with a proof
      assistant.  If you're interested in tackling more complicated
      problems than presented here, I suggest checking out a textbook
      like <a href="http://www.cis.upenn.edu/~bcpierce/sf/">Software
      Foundations</a>.</p>

      <p>One primary motivation for this tutorial, which constrained the
      user interface design considerably, was to demonstrate the
      notation and concepts relied upon heavily in the academic type
      theory literature.  As an undergraduate, I always found inference
      rules to be some of the most intimidating parts of academic papers
      in programming languages.  Studying how these conventions work in
      a simpler setting is a key step on the way to being able to "read
      the Greek." While some of the notational choices may seem
      hair-brained to a modern viewer, overall the system is very well
      optimized.  Inference rules are a remarkably compact and efficient
      way to describe many types of systems: the space savings are
      analogous to using BNFs to specify grammars.</p>

      <p>Overall, my hope is that this tutorial has helped you take your
      first step into the fascinating world of formal systems, type
      theory and theorem proving.  Return to <a link={main ()}>the main
      page</a>, and try coming up with some theorems of your own!</p>

      <p><i>Colophon.</i> This tutorial is powered by <a href="http://coq.inria.fr/">Coq</a>,
        <a href="http://www.haskell.org">Haskell</a> and <a href="http://www.impredicative.com/ur/">Ur/Web</a>.</p>

    </div>
  </body>
  </xml>

and proving goal =
  return <xml>
        <head>
          <title>Proving {[goal]}</title>
          {headTemplate}
        </head>
        <body>
        <div class={page}>
          <p>The <a href="http://en.wikipedia.org/wiki/Sequent_calculus">sequent calculus</a>
          is a form of backwards reasoning, with left and right inference rules which operate
          on sequents.  Inference rules correspond closely to <i>clauses</i> in the sequent,
          so in Logitext (and other proof-by-pointing systems), all you need to do is click
          on a clause to see what inference rule is triggered. In some cases, an input box will pop up;
          enter a lower case expression like <i>z</i> or <i>f(x)</i>.
          (You can also choose to duplicate the rules by clicking "Contraction").
          If that made no sense to you, check out <a link={tutorial ()}>the tutorial</a>.
          Or, you can <a link={main ()}>return to main page...</a></p>
          {workspace goal}
        </div>
        </body>
      </xml>
      (* XXX initially, the proof box should glow, so the user knows that it is special *)

and provingTrampoline r =
  redirect (url (proving r.Goal))

and main () =
  let fun tryProof s = <xml><li><a link={proving s}>{[s]}</a></li></xml>
  in
  return <xml>
      <head>
        <title>Logitext</title>
          {headTemplate}
      </head>
      <body>
      <div class={page}>
        <p>Logitext is an educational proof assistant for <i>first-order classical
        logic</i> using the <i>sequent calculus</i>, in the same tradition as Jape, Pandora, Panda and Yoda.
        It is intended to assist students who are learning <i>Gentzen trees</i>
        as a way of structuring derivations of logical statements.
        Underneath the hood, Logitext interfaces with <a href="http://coq.inria.fr/">Coq</a> in order to check
        the validity of your proof steps.  The frontend is written in
        <a href="http://www.haskell.org">Haskell</a> and <a href="http://www.impredicative.com/ur/">Ur/Web</a>, and there is an
        interesting story behind it which you can <a href="http://blog.ezyang.com/2012/05/what-happens-when-you-mix-three-research-programming-languages-together/">read about</a>. Alternatively, get the source at
        <a href="https://github.com/ezyang/logitext">GitHub</a>.</p>
        <p>To get started, check out the <a link={tutorial ()}>tutorial</a>, or dive right
        in and type in something to prove:</p>
        <form>
          <textbox{#Goal}/><submit action={provingTrampoline} value="Prove"/>
        </form>
        <p>Here are some examples:</p>
        <ul>
          {tryProof "((A -> B) -> A) -> A"}
          {tryProof "A \/ ~A"}
          {tryProof "(forall x, P(x)) -> (exists x, P(x))"}
        </ul>
        <p>Logitext is case-sensitive: capitalized identifiers represent
        propositions and predicates, while lower-case identifiers
        represent functions and elements of the universe.</p>
        <p>If you don't like classical logic, check out the <a link={Intuitionistic.main ()}>intuitionistic
        version!</a></p>
        </div>
      </body>
    </xml>
    end
