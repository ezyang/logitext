open Json
open List
open Common
open Style

task initialize = Haskell.initVanilla

con logic' a = [Prop = string,
                Conj = a * a,
                Disj = a * a,
                Imp = a * a,
                Bot = unit,
                (* erased from IR *)
                Iff = a * a,
                Not = a,
                Top = unit,
                ]
structure Logic = Json.Recursive(struct
  con t a = variant (logic' a)
  fun json_t [a] (_ : json a) : json (t a) =
    let val json_compound : json (a * a) = json_record ("1", "2")
    in json_variant {Prop = "Prop", Conj = "Conj", Disj = "Disj", Imp = "Imp", Iff = "Iff",
          Not = "Not", Top = "Top", Bot = "Bot"}
    end
end)
type rawlogic = Logic.r
datatype logic = Prop of string
               | Conj of logic * logic
               | Disj of logic * logic
               | Imp of logic * logic
               | Bot
fun convlogic ((Logic.Rec l) : rawlogic) = match l
  { Prop = Prop
  , Conj = fn (a,b) => Conj (convlogic a, convlogic b)
  , Disj = fn (a,b) => Disj (convlogic a, convlogic b)
  , Imp = fn (a,b) => Imp (convlogic a, convlogic b)
  , Iff = fn (a,b) =>
        let val a' = convlogic a
            val b' = convlogic b
        in Conj (Imp (a', b'), Imp (b', a'))
        end
  , Not = fn a => Imp (convlogic a, Bot)
  , Top = fn _ => Imp (Bot, Bot) (* hack *)
  , Bot = fn _ => Bot
  }
(* no decompiling kthxbai *)
fun logicconv l = Logic.Rec (case l of
    Prop s => make [#Prop] s
  | Conj (a,b) => make [#Conj] (logicconv a, logicconv b)
  | Disj (a,b) => make [#Disj] (logicconv a, logicconv b)
  | Imp (a,b) => make [#Imp] (logicconv a, logicconv b)
  | Bot => make [#Bot] ()
  )

val json_logic : json logic = mkJson {
  ToJson = fn a => toJson (logicconv a),
  FromJson = fn a => case (fromJson' a) of (x,y) => (convlogic x, y)}

fun renderParen (b : bool) (r : xbody) : xbody = if b then <xml>({r})</xml> else r
fun renderLogic top p (r : logic) : xbody =
  let fun symbol s = if top then <xml><span class={primaryConnective}>{[s]}</span></xml> else <xml>{[s]}</xml>
  in case r of
     Prop x => <xml>{[x]}</xml>
   | Conj (a, b) => renderParen (p>3) <xml>{renderLogic False 3 a} {symbol "∧"} {renderLogic False 3 b}</xml>
   | Disj (a, b) => renderParen (p>2) <xml>{renderLogic False 2 a} {symbol "∨"} {renderLogic False 2 b}</xml>
   (* pretty-printing... (not implemented for iff, which requires an equality check...)
      this might be confusing for users, since the UI isn't going to be totally consistent about this. *)
   | Imp (Bot, Bot) => <xml>⊤</xml>
   | Imp (a, Bot) => renderParen (p>4) <xml>{symbol "¬"}{renderLogic False 5 a}</xml>
   | Imp (a, b) => renderParen (p>1) <xml>{renderLogic False 2 a} {symbol "→"} {renderLogic False 1 b}</xml>
   | Bot => <xml>⊥</xml>
  end

type sequent = { Hyps : list logic, Goal : logic }
val json_sequent : json sequent = json_record {Hyps = "hyps", Goal = "goal"}
fun mkSequent hyps goal = { Hyps = hyps, Goal = goal }

con tactic' a = [LExact = int,
                 LConj = int * a,
                 LDisj = int * a * a,
                 LImpProp = int * a,
                 LImpConj = int * a,
                 LImpDisj = int * a,
                 LImpImp = int * a * a,
                 LImpBot = int * a, (* erasure *)
                 LBot = int,
                 RExact = unit,
                 RConj = a * a,
                 RDisjL = a,
                 RDisjR = a,
                 RImp = a,
                 ]
con tactic a = variant (tactic' a)

fun tacticDescription [a] (t : tactic a) : string = match t
   {
     LExact     = fn _ => ""
   , LConj      = fn _ => "conjunction left"
   , LDisj      = fn _ => "disjunction left"
   (* maybe distinguish these? *)
   , LImpProp   = fn _ => "implication left"
   , LImpConj   = fn _ => "implication left"
   , LImpDisj   = fn _ => "implication left"
   , LImpImp    = fn _ => "implication left"
   , LImpBot    = fn _ => "implication left"
   , LBot       = fn _ => "ex falso"
   , RExact     = fn _ => ""
   , RConj      = fn _ => "conjunction right"
   , RDisjL     = fn _ => "left disjunction right"
   , RDisjR     = fn _ => "right disjunction right"
   , RImp       = fn _ => "implication right"
   }

fun tacticRenderName [a] (t : tactic a) : xbody = match t
   { LExact     = fn _ => <xml/>
   , LConj      = fn _ => <xml>(∧l)</xml>
   , LDisj      = fn _ => <xml>(∨l)</xml>
   , LImpProp   = fn _ => <xml>(→l)</xml>
   , LImpConj   = fn _ => <xml>(→l)</xml>
   , LImpDisj   = fn _ => <xml>(→l)</xml>
   , LImpImp    = fn _ => <xml>(→l)</xml>
   , LImpBot    = fn _ => <xml>(→l)</xml>
   , LBot       = fn _ => <xml></xml>
   , RExact     = fn _ => <xml></xml>
   , RConj      = fn _ => <xml>(∧r)</xml>
   , RDisjL     = fn _ => <xml>(∨r<sub>1</sub>)</xml>
   , RDisjR     = fn _ => <xml>(∨r<sub>2</sub>)</xml>
   , RImp       = fn _ => <xml>(→r)</xml>
   }

con end_user_failure = variant [UpdateFailure = unit, ParseFailure = unit]
val json_end_user_failure : json end_user_failure = json_variant {UpdateFailure = "UpdateFailure", ParseFailure = "ParseFailure"}

con result a = variant [EndUserFailure = end_user_failure, InternalFailure = string, Success = a]
fun json_result [a] (_ : json a) : json (result a) =
    json_variant {EndUserFailure = "EndUserFailure", InternalFailure = "InternalFailure", Success = "Success"}

datatype proof = Goal of sequent | Pending of sequent * tactic int | Proof of sequent * tactic proof

fun proofComplete p : bool =
    case p of
      Goal _ => False
    | Pending _ => False
    | Proof (_, t) =>
         let val empty   = declareCase (fn _ (_ : int) => True)
             val emptyR  = declareCase (fn _ () => True)
             val single  = declareCase (fn _ (_ : int, a) => proofComplete a)
             val singleR = declareCase (fn _ a => proofComplete a)
             val double  = declareCase (fn _ (_ : int, a, b) => andB (proofComplete a) (proofComplete b))
             val doubleR = declareCase (fn _ (a, b) => andB (proofComplete a) (proofComplete b))
         in typeCase t end

(* h is a callback to the proof renderer, which instructs the proof renderer
to replace the Goal with a Pending proof object.  A proof renderer will
take a Pending proof object and attempt to convert it into a Proof object. *)
fun renderSequent (showError : xbody -> transaction unit) (h : proof -> transaction unit) (s : sequent) : transaction xbody =
    let fun makePending (x : tactic int) : transaction unit = h (Pending (s, x)) in
    persistent <- List.mapXiM (fn i x =>
              nid <- fresh;
              let val bod = <xml><li id={nid}><span class={junct} onclick={fn _ =>
                  case x of
                    Prop _ => makePending (make [#LExact] i)
                  | Conj _ => makePending (make [#LConj] (i, 0))
                  | Disj _ => makePending (make [#LDisj] (i, 0, 1))
                  | Imp (Prop _, _) => makePending (make [#LImpProp] (i, 0))
                  | Imp (Conj _, _) => makePending (make [#LImpConj] (i, 0))
                  | Imp (Disj _, _) => makePending (make [#LImpDisj] (i, 0))
                  | Imp (Imp _, _) => makePending (make [#LImpImp] (i, 0, 1))
                  | Imp (Bot, _) => makePending (make [#LImpBot] (i, 0)) (* could also return () *)
                  | Bot    => makePending (make [#LBot] i)
                    }>{renderLogic True 0 x}</span></li></xml>
              in return bod
              end
            ) s.Hyps;
    let val right =
      case s.Goal of
        Disj (x,y) => <xml><span>
          <span class={primaryExpr} onclick={fn _ => makePending (make [#RDisjL] (0))}>{renderLogic False 2 x}</span> ∨
          <span class={primaryExpr} onclick={fn _ => makePending (make [#RDisjR] (0))}>{renderLogic False 2 y}</span>
          </span></xml>
      | _ =>
        <xml><span class={junct} onclick={fn _ => case s.Goal of
            Prop _ => makePending (make [#RExact] ())
          | Conj _ => makePending (make [#RConj] (0, 1))
          | Disj _ => error <xml>impossible</xml>
          | Imp  _ => makePending (make [#RImp] 0)
          | Bot    => return ()
            }>
        {renderLogic True 0 s.Goal}</span></xml>
    in
    nid <- fresh;
    return <xml><div id={nid}><ul class={commaList}>{persistent}</ul> <span class={turnstile} title="reset" onclick={fn _ => h (Goal s)}>⊢</span> {right}</div></xml>
    end
  end

fun refine showError (s : sequent) (t : tactic int) : transaction proof =
  let fun err e = showError e; return (Goal s)
      fun pf x = return (Proof (s, x))
      fun xgGoal       concl = Goal (mkSequent s.Hyps concl)
      fun xpgGoal hyps concl = Goal (mkSequent hyps concl)
      fun xpGoal  hyps       = Goal (mkSequent hyps s.Goal)
  in match t
   { LExact     = fn i =>
      case (nth s.Hyps i, s.Goal) of
        (Some (Prop x), Prop x') =>
          if x <> x' then err <xml>Not axiomatically valid</xml>
                     else pf (make [#LExact] i)
      | (_, _) => err <xml>Not an atomic proposition</xml>
   , LConj      = fn (i,_) =>
      case splitAt i s.Hyps of
        (pre, (Conj (x,y)) :: post) =>
          pf (make [#LConj] (i, xpGoal (append pre (x :: y :: post))))
      | _ => err <xml>Not a conjunction</xml>
   , LDisj      = fn (i,_,_) =>
      case splitAt i s.Hyps of
        (pre, (Disj (x,y)) :: post) =>
          pf (make [#LDisj] (i, xpGoal (append pre (x :: post)), xpGoal (append pre (y :: post))))
      | _ => err <xml>Not a disjunction</xml>
   , LImpProp   = fn (i,_) =>
      case splitAt i s.Hyps of
        (pre, (Imp (Prop x,y)) :: post) =>
            if foldl (fn c z => z || (case c of
                          Prop x' => x = x'
                        | _ => False)) False s.Hyps
              then pf (make [#LImpProp] (i, xpGoal (append pre (y :: post))))
              else err <xml>Couldn't find matching hypothesis</xml>
      | _ => err <xml>Not an implication with an atomic proposition hypothesis</xml>
   , LImpConj   = fn (i,_) =>
      case splitAt i s.Hyps of
        (pre, (Imp (Conj (x1,x2),y)) :: post) =>
          pf (make [#LImpConj] (i, xpGoal (append pre (Imp (x1, Imp (x2, y)) :: post))))
      | _ => err <xml>Not an implication with conjunction hypothesis</xml>
   , LImpDisj   = fn (i,_) =>
      case splitAt i s.Hyps of
        (pre, (Imp (Disj (x1,x2),y)) :: post) =>
          pf (make [#LImpDisj] (i, xpGoal (append pre (Imp (x1, y) :: Imp (x2, y) :: post))))
      | _ => err <xml>Not an implication with disjunction hypothesis</xml>
   , LImpImp    = fn (i,_,_) =>
      case splitAt i s.Hyps of
        (pre, (Imp (Imp (x1,x2),y)) :: post) =>
          pf (make [#LImpImp] (i, xpgGoal (append pre (Imp (x2, y) :: post)) (Imp (x1, x2)), xpGoal (append pre (y :: post))))
      | _ => err <xml>Not an implication with implication hypothesis</xml>
   , LImpBot    = fn (i,_) =>
      case splitAt i s.Hyps of
        (pre, (Imp (Bot,y)) :: post) =>
          pf (make [#LImpBot] (i, xpGoal (append pre post)))
      | _ => err <xml>Not an implication with bottom hypothesis</xml>
   , LBot       = fn i =>
      case nth s.Hyps i of
        Some Bot => pf (make [#LBot] i)
      | _ => err <xml>Not a bottom</xml>
   , RExact     = fn _ =>
      case s.Goal of
        Prop x => if foldl (fn c z => z || (case c of
                                Prop x' => x = x'
                              | _ => False)) False s.Hyps
                    then pf (make [#RExact] ())
                    else err <xml>Not axiomatically true</xml>
      | _ => err <xml>Not an atomic proposition</xml>
   , RConj      = fn _ =>
      case s.Goal of
        Conj (x,y) =>
          pf (make [#RConj] (xgGoal x, xgGoal y))
      | _ => err <xml>Not a conjunction</xml>
   , RDisjL     = fn _ =>
      case s.Goal of
        Disj (x,_) =>
          pf (make [#RDisjL] (xgGoal x))
      | _ => error <xml>Not a disjunction</xml>
   , RDisjR     = fn _ =>
      case s.Goal of
        Disj (_,y) =>
          pf (make [#RDisjR] (xgGoal y))
      | _ => error <xml>Not a disjunction</xml>
   , RImp       = fn _ =>
      case s.Goal of
        Imp (x,y) =>
          pf (make [#RImp] (xpgGoal (snoc s.Hyps x) y))
      | _ => err <xml>Not an implication</xml>
   }
   end

(* Renders a proof fragment, and is responsible for wiring up the
   proof callbacks for subsegments. If the proof shifts from one
   type to another, we'll invoke our parent to calculate the
   appropriate change. *)
fun renderProof showError topcall (h : proof -> transaction unit) (r : proof) : transaction xbody = case r of
   Goal s =>
       sequent <- renderSequent showError h s;
       return <xml><table><tr><td>{sequent}</td><td class={tagBox}>&nbsp;</td></tr></table></xml>
 | Pending (s, t) =>
       (* better not return a pending! XXX can type system that *)
       bind (refine showError s t) (renderProof showError topcall h)
 | Proof (s, t) =>
       (* do not call h, do not pass go... *)
       sequent <- renderSequent showError h s;
       let fun render t : transaction xbody =
                childSource <- source <xml/>;
                let fun childHandler x =
                    topcall;
                    r <- renderProof showError topcall childHandler x;
                    set childSource r
                in
                childHandler t;
                return <xml><div class={sibling}><dyn signal={signal childSource} /></div></xml>
                end
           val empty   = declareCase (fn _ (_ : int) =>
                return <xml/> : transaction xbody)
           val emptyR  = declareCase (fn _ () =>
                return <xml/> : transaction xbody)
           val single  = declareCase (fn _ (_ : int, a : proof) =>
                render a : transaction xbody)
           val singleR = declareCase (fn _ (a : proof) =>
                render a : transaction xbody)
           val double  = declareCase (fn _ (n : int, a : proof, b : proof) =>
                Monad.liftM2 join (render a) (render b) : transaction xbody)
           val doubleR = declareCase (fn _ (a : proof, b : proof) =>
                Monad.liftM2 join (render a) (render b) : transaction xbody)
       in
       top <- typeCase t;
       nid <- fresh;
       return <xml>
        <div>{top}</div>
        <table>
          <tr>
            <td class={inference}>{sequent}</td>
            <td class={tagBox}>
                <div class={tag}>{activate <xml><span title={tacticDescription t} id={nid}>{tacticRenderName t}</span></xml> (Js.tip nid)}</div>
            </td>
          </tr>
        </table></xml>
       end

fun mkWorkspaceRaw showErrors (pf : proof) =
  v <- source <xml/>;
  err <- source <xml/>;
  proofStatus <- source proofIsIncomplete; (* should actually be a datatype *)
  bamf <- source <xml/>;
  let val clearError = set err <xml/>
      fun showError (e : xbody) =
        nid <- fresh;
        set err (activate <xml>
          <div class={errorStyle} id={nid}>
            {e} <button onclick={fn _ => clearError} value="Dismiss" />
          </div>
        </xml> (Js.tipInner nid))
      val topcall =
        clearError;
        set bamf (activeCode Js.clearTooltips)
      fun handler pf =
        bind (renderProof showError topcall handler pf) (set v)
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
          {activeCode (handler pf)}
    </xml>
  end

fun workspace goal =
  let val parsedGoal = Haskell.parseIntuitionistic goal
  in match (fromJson parsedGoal : result sequent)
    { Success = fn r => <xml><active code={mkWorkspaceRaw True (Goal r)} /></xml>
    , EndUserFailure = fn e => match e
        { UpdateFailure = fn () => <xml><div class={errorStyle}>Impossible! Report this as a bug.</div></xml>
        , ParseFailure = fn () => <xml><div class={errorStyle}>Expression did not parse.</div></xml>
        }
    , InternalFailure = fn s => <xml><div class={errorStyle}>{[s]}</div></xml>
    }
  end

fun proving goal =
  return <xml>
        <head>
          <title>Proving {[goal]}</title>
          {headTemplate}
        </head>
        <body>
        <div class={page}>
          {workspace goal}
        </div>
        </body>
      </xml>

and provingTrampoline r =
  redirect (url (proving r.Goal))

and main () : transaction page =
  let fun tryProof s = <xml><li><a link={proving s}>{[s]}</a></li></xml>
  in
  return <xml>
      <head>
        <title>Logitext/Intuitionistic</title>
          {headTemplate}
      </head>
      <body>
      <div class={page}>
        <p>This is a variant of Logitext for <i>propositional intuitionistic logic</i>.
        The calculus we have implemented is
        <a href="http://www.inf.kcl.ac.uk/staff/urbanc/Prover/G4ip.html">G4ip</a>,
        which has the notable property that it does not need contraction to be complete.
        This implementation is not backed by Coq, so there may be bugs;
        please let me know if you find any.</p>
        <form>
          <textbox{#Goal}/><submit action={provingTrampoline} value="Prove"/>
        </form>
        <p>Here are some examples. (Warning: some of these are impossible to prove in
        intuitionistic logic!)</p>
        <ul>
          {tryProof "(A -> B) \/ (A -> C) |- A -> (B \/ C)"}
          {tryProof "A -> (B \/ C) |- (A -> B) \/ (A -> C)"}
          {tryProof "((A -> (B -> R) -> R) -> (A -> R) -> R) -> (A -> R) -> R"}
        </ul>
        <p>Logitext/Intuitionistic is case-sensitive: capitalized identifiers represent
        propositions.</p>
        </div>
      </body>
    </xml>
    end
