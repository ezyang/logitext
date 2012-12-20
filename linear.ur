open Json
open List
open Common
open Style

task initialize = Haskell.initVanilla

con logic' a = [Prop = string,
                Conj = a * a,
                Disj = a * a,
                Imp = a * a,
                Iff = a * a,
                Not = a,
                Top = unit,
                Bot = unit]
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
               | Iff of logic * logic
               | Not of logic
               | Top
               | Bot
fun convlogic ((Logic.Rec l) : rawlogic) = match l
  { Prop = Prop
  , Conj = fn (a,b) => Conj (convlogic a, convlogic b)
  , Disj = fn (a,b) => Disj (convlogic a, convlogic b)
  , Imp = fn (a,b) => Imp (convlogic a, convlogic b)
  , Iff = fn (a,b) => Iff (convlogic a, convlogic b)
  , Not = fn a => Not (convlogic a)
  , Top = fn _ => Top
  , Bot = fn _ => Bot
  }
fun logicconv l = Logic.Rec (case l of
    Prop s => make [#Prop] s
  | Conj (a,b) => make [#Conj] (logicconv a, logicconv b)
  | Disj (a,b) => make [#Disj] (logicconv a, logicconv b)
  | Imp (a,b) => make [#Imp] (logicconv a, logicconv b)
  | Iff (a,b) => make [#Iff] (logicconv a, logicconv b)
  | Not a => make [#Not] (logicconv a)
  | Top => make [#Top] ()
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
   | Imp (a, b) => renderParen (p>1) <xml>{renderLogic False 2 a} {symbol "→"} {renderLogic False 1 b}</xml>
   | Iff (a, b) => renderParen (p>1) <xml>{renderLogic False 2 a} {symbol "↔"} {renderLogic False 2 b}</xml>
   | Not a => renderParen (p>4) <xml>{symbol "¬"}{renderLogic False 5 a}</xml>
   | Top => <xml>⊤</xml>
   | Bot => <xml>⊥</xml>
  end

type sequent = { Persistent : list logic, Ephemeral : list logic, Goal : logic }
val json_sequent : json sequent = json_record {Persistent = "persistent", Ephemeral = "ephemeral", Goal = "goal"}
fun mkSequent per eph goal = { Persistent = per, Ephemeral = eph, Goal = goal }

con tactic' a = [LExact = int,
                 LConj = int * a,
                 LDisj = int * a * a,
                 LImp = int * a * a,
                 LIff = int * a,
                 LBot = int,
                 LTop = int * a,
                 LNot = int * a,
                 LContract = int * a,
                 LWeaken = int * a,
                 RExact = unit,
                 RConj = a * a,
                 RDisjL = a,
                 RDisjR = a,
                 RImp = a,
                 RIff = a * a,
                 RTop = unit,
                 RNot = a,
                 ]
con tactic a = variant (tactic' a)

fun tacticDescription [a] (t : tactic a) : string = match t
   {
     LExact     = fn _ => ""
   , LConj      = fn _ => "conjunction left"
   , LDisj      = fn _ => "disjunction left"
   , LImp       = fn _ => "implication left"
   , LIff       = fn _ => "iff left"
   , LBot       = fn _ => ""
   , LTop       = fn _ => ""
   , LNot       = fn _ => "negation left"
   , LContract  = fn _ => ""
   , LWeaken    = fn _ => ""
   , RExact     = fn _ => ""
   , RConj      = fn _ => "conjunction right"
   , RDisjL     = fn _ => "left disjunction right"
   , RDisjR     = fn _ => "right disjunction right"
   , RImp       = fn _ => "implication right"
   , RIff       = fn _ => "iff right"
   , RTop       = fn _ => ""
   , RNot       = fn _ => "negation right"
   }

fun tacticRenderName [a] (t : tactic a) : string = match t
   { LExact     = fn _ => ""
   , LConj      = fn _ => "(∧l)"
   , LDisj      = fn _ => "(∨l)"
   , LImp       = fn _ => "(→l)"
   , LIff       = fn _ => "(↔l)"
   , LBot       = fn _ => ""
   , LTop       = fn _ => ""
   , LNot       = fn _ => "(¬l)"
   , LContract  = fn _ => ""
   , LWeaken    = fn _ => ""
   , RExact     = fn _ => ""
   , RConj      = fn _ => "(∧r)"
   , RDisjL     = fn _ => "(∨r1)"
   , RDisjR     = fn _ => "(∨r2)"
   , RImp       = fn _ => "(→r)"
   , RIff       = fn _ => "(↔r)"
   , RTop       = fn _ => ""
   , RNot       = fn _ => "(¬r)"
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
                  | Imp  _ => makePending (make [#LImp] (i, 0, 1))
                  | Iff  _ => makePending (make [#LIff] (i, 0))
                  | Not  _ => makePending (make [#LNot] (i, 0))
                  | Top    => makePending (make [#LTop] (i, 0))
                  | Bot    => makePending (make [#LBot] i)
                    }>{renderLogic True 0 x}</span></li></xml>
              in return bod
              end
            ) s.Persistent;
    ephemeral <- List.mapXiM (fn i x =>
              nid <- fresh;
              let val bod = <xml><li id={nid}><span class={junct} onclick={fn _ =>
                  case x of
                    Prop _ => makePending (make [#LExact] i)
                  | Conj _ => makePending (make [#LConj] (i, 0))
                  | Disj _ => makePending (make [#LDisj] (i, 0, 1))
                  | Imp  _ => makePending (make [#LImp] (i, 0, 1))
                  | Iff  _ => makePending (make [#LIff] (i, 0))
                  | Not  _ => makePending (make [#LNot] (i, 0))
                  | Top    => makePending (make [#LTop] (i, 0))
                  | Bot    => makePending (make [#LBot] i)
                    }>{renderLogic True 0 x}</span></li></xml>
              in return bod
              end
            ) s.Ephemeral;
    let val right =
      case s.Goal of
        Disj (x,y) => <xml><span class={junct}>
          <span class={primaryExpr} onclick={fn _ => makePending (make [#RDisjL] (0))}>{renderLogic False 2 x}</span> ∨
          <span class={primaryExpr} onclick={fn _ => makePending (make [#RDisjR] (0))}>{renderLogic False 2 y}</span>
          </span></xml>
      | _ =>
        <xml><span class={junct} onclick={fn _ => case s.Goal of
            (* XXX see something, say something... *)
            Prop _ => return () (* makePending (make [#RExact] ()) *)
          | Conj _ => makePending (make [#RConj] (0, 1))
          | Disj _ => error <xml>impossible</xml>
          | Imp  _ => makePending (make [#RImp] 0)
          | Iff  _ => makePending (make [#RIff] (0, 1))
          | Not  _ => makePending (make [#RNot] 0)
          | Top    => makePending (make [#RTop] ())
          | Bot    => return ()
            }>
        {renderLogic True 0 s.Goal}</span></xml>
    in
    nid <- fresh;
    return <xml><div id={nid}><ul class={commaList}>{persistent}</ul> <span class={turnstile} title="reset" onclick={fn _ => h (Goal s)}>⊢</span> {right}</div></xml>
    end
  end

(* ephemeral?! *)
fun refine showError (s : sequent) (t : tactic int) : transaction proof =
  let fun err e = showError e; return (Goal s)
      fun pf x = return (Proof (s, x))
      fun xgGoal       concl = Goal (mkSequent s.Persistent s.Ephemeral concl)
      fun xpgGoal hyps concl = Goal (mkSequent hyps s.Ephemeral concl)
      fun xegGoal hyps concl = Goal (mkSequent s.Persistent hyps concl)
      fun xpGoal  hyps       = Goal (mkSequent hyps s.Ephemeral s.Goal)
  in match t
   { LExact     = fn i =>
      case (nth s.Persistent i, s.Goal) of
        (Some (Prop x), Prop x') =>
          if x <> x' then err <xml>Not axiomatically valid</xml>
                     else pf (make [#LExact] i)
      | (_, _) => err <xml>Not an atomic proposition</xml>
   , LConj      = fn (i,_) =>
      case splitAt i s.Persistent of
        (pre, (Conj (x,y)) :: post) =>
          pf (make [#LConj] (i, xpGoal (append pre (x :: y :: post))))
      | _ => err <xml>Not a conjunction</xml>
   , LDisj      = fn (i,_,_) =>
      case splitAt i s.Persistent of
        (pre, (Disj (x,y)) :: post) =>
          pf (make [#LDisj] (i, xpGoal (append pre (x :: post)), xpGoal (append pre (y :: post))))
      | _ => err <xml>Not a disjunction</xml>
   , LImp       = fn (i,_,_) =>
      case splitAt i s.Persistent of
        (pre, (Imp (x,y)) :: post) =>
          (* pf (make [#LImp] (i, xgGoal x, xpGoal (y :: append pre (Imp (x,y) :: post)))) *)
          pf (make [#LImp] (i, xpgGoal (append pre post) x, xpGoal (y :: append pre post)))
      | _ => err <xml>Not an implication</xml>
   , LIff       = fn (i,_) =>
      case splitAt i s.Persistent of
        (pre, (Iff (x,y)) :: post) =>
          pf (make [#LIff] (i, xpGoal (append pre (Imp (x,y) :: Imp (y,x) :: post))))
      | _ => err <xml>Not an iff</xml>
   , LBot       = fn i =>
      case nth s.Persistent i of
        Some Bot => pf (make [#LBot] i)
      | _ => err <xml>Not a bottom</xml>
   , LTop       = fn (i,_) =>
      case splitAt i s.Persistent of
        (pre, Top :: post) =>
          pf (make [#LTop] (i, xpGoal (append pre post)))
      | _ => err <xml>Not a top</xml>
   , LNot       = fn (i,_) =>
      case splitAt i s.Persistent of
        (pre, (Not x) :: post) =>
          (* pf (make [#LNot] (i, xgGoal x)) *)
          pf (make [#LNot] (i, xpgGoal (append pre post) x))
      | _ => err <xml>Not a negation</xml>
   , LContract  = fn _ => err <xml>Unimplemented</xml>
   , LWeaken    = fn _ => err <xml>Unimplemented</xml>
   , RExact     = fn _ => err <xml>Unimplemented</xml> (* XXX lazy bastard... *)
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
          pf (make [#RImp] (xpgGoal (x :: s.Persistent) y))
      | _ => err <xml>Not an implication</xml>
   , RIff       = fn _ =>
      case s.Goal of
        Iff (x,y) =>
          pf (make [#RIff] (xgGoal (Imp (x,y)), xgGoal (Imp (y,x))))
      | _ => err <xml>Not an iff</xml>
   , RTop       = fn _ =>
      case s.Goal of
        Top => pf (make [#RTop] ())
      | _ => error <xml>Not a top</xml>
   , RNot       = fn _ =>
      case s.Goal of
        Not x => pf (make [#RNot] (xpgGoal (x :: s.Persistent) Bot))
      | _ => error <xml>Not a negation</xml>
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
                <div class={tag}>{activate <xml><span title={tacticDescription t} id={nid}>{[tacticRenderName t]}</span></xml> (Js.tip nid)}</div>
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
  let val parsedGoal = Haskell.parseLinear goal
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
          {head}
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
        <title>Logitext/Linear</title>
          {head}
      </head>
      <body>
      <div class={page}>
        <form>
          <textbox{#Goal}/><submit action={provingTrampoline} value="Prove"/>
        </form>
        <p>Here are some examples:</p>
        <ul>
          {tryProof "((A -> B) -> A) -> A"}
          {tryProof "A \/ ~A"}
        </ul>
        <p>Logitext/Linear is case-sensitive: capitalized identifiers represent
        propositions.</p>
        </div>
      </body>
    </xml>
    end
