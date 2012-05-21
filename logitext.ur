style proof
style proofIsDone
style proofIsIncomplete
style rules
style inference
style tagBox
style tag
style sibling
style junct
style viewport
style commaList
style relMark
style offsetBox
style working
style page
style error

open Json

task initialize = Haskell.init

structure Universe = Json.Recursive(struct
  con t a = string * list a
  fun json_t [a] (_ : json a) : json (t a) = json_record ("1", "2")
end)
type universe = Universe.r
fun renderUniverse ((Universe.Rec (f,xs)) : universe) : xbody =
  <xml>{[f]}{
    case xs of
    | Cons _ => <xml>(<ul class={commaList}>{List.mapX (fn x => <xml><li>{renderUniverse x}</li></xml>) xs}</ul>)</xml>
    | Nil => <xml></xml>
    }</xml>
fun zapParseUniverse x : transaction string = return (Haskell.parseUniverse x)

structure Logic = Json.Recursive(struct
  con t a = variant [Pred = string * list universe,
                     Conj = a * a,
                     Disj = a * a,
                     Imp = a * a,
                     Not = a,
                     Top = unit,
                     Bot = unit,
                     Forall = string * a,
                     Exists = string * a]
  fun json_t [a] (_ : json a) : json (t a) =
    let val json_pred : json (string * list universe) = json_record ("1", "2")
        val json_compound : json (a * a) = json_record ("1", "2")
        val json_quantifier : json (string * a) = json_record ("1", "2")
    in json_variant {Pred = "Pred", Conj = "Conj", Disj = "Disj", Imp = "Imp",
          Not = "Not", Top = "Top", Bot = "Bot", Forall = "Forall", Exists = "Exists"}
    end
end)
type logic = Logic.r

(* hat tip http://blog.sigfpe.com/2010/12/generalising-godels-theorem-with_24.html
   the parser in ClassicalLogic.hs should support this syntax. *)
fun renderParen (b : bool) (r : xbody) : xbody = if b then <xml>({r})</xml> else r
fun renderLogic p ((Logic.Rec r) : logic) : xbody = match r
  {Pred = fn (f, xs) =>
    case xs of
      | Nil => <xml>{[f]}</xml>
      | Cons _ => <xml>{[f]}(<ul class={commaList}>{List.mapX (fn x => <xml><li>{renderUniverse x}</li></xml>) xs}</ul>)</xml>,
   Conj = fn (a, b) => renderParen (p>3) <xml>{renderLogic 3 a} ∧ {renderLogic 3 b}</xml>,
   Disj = fn (a, b) => renderParen (p>2) <xml>{renderLogic 2 a} ∨ {renderLogic 2 b}</xml>,
   Imp = fn (a, b) => renderParen (p>1) <xml>{renderLogic 2 a} → {renderLogic 1 b}</xml>,
   Not = fn a => renderParen (p>4) <xml>¬{renderLogic 5 a}</xml>,
   Top = fn _ => <xml>⊤</xml>,
   Bot = fn _ => <xml>⊥</xml>,
   Forall = fn (x, a) => renderParen (p>0) <xml>∀{[x]}. {renderLogic 0 a}</xml>,
   Exists = fn (x, a) => renderParen (p>0) <xml>∃{[x]}. {renderLogic 0 a}</xml>}

type sequent = { Hyps : list logic, Cons : list logic }
val json_sequent : json sequent = json_record {Hyps = "hyps", Cons = "cons"}

(* our protocol kind of precludes incremental updates or smooth
redrawing. It would be nice if Ur/Web did this for us. *)

con tactic a = variant [Cut = logic * a * a,
                        LExact = int,
                        LConj = int * a,
                        LDisj = int * a * a,
                        LImp = int * a * a,
                        LBot = int,
                        LTop = int * a,
                        LNot = int * a,
                        LForall = int * universe * a,
                        LExists = int * a,
                        LContract = int * a,
                        LWeaken = int * a,
                        RExact = int,
                        RConj = int * a * a,
                        RDisj = int * a,
                        RImp = int * a,
                        RTop = int,
                        RBot = int * a,
                        RNot = int * a,
                        RForall = int * a,
                        RExists = int * universe * a,
                        RWeaken = int * a,
                        RContract = int * a]
fun json_tactic [a] (_ : json a) : json (tactic a) =
  let val json_cut : json (logic * a * a) = json_record ("1", "2", "3")
      val json_single : json (int * a) = json_record ("1", "2")
      val json_double : json (int * a * a) = json_record ("1", "2", "3")
      val json_instance : json (int * universe * a) = json_record ("1", "2", "3")
  in json_variant {Cut = "Cut", LExact = "LExact", LConj = "LConj", LDisj = "LDisj",
        LImp = "LImp", LBot = "LBot", LTop = "LTop", LNot = "LNot", LForall = "LForall", LExists = "LExists",
        LContract = "LContract", LWeaken = "LWeaken", RExact = "RExact", RConj = "RConj", RDisj = "RDisj",
        RImp = "RImp", RTop = "RTop", RBot = "RBot", RNot = "RNot", RForall = "RForall", RExists = "RExists",
        RWeaken = "Rweaken", RContract = "RContract"}
  end

fun tacticRenderName [a] (t : tactic a) : string = match t
   {
     Cut        = fn _ => "(cut)"
   , LExact     = fn _ => ""
   , LConj      = fn _ => "(∧l)"
   , LDisj      = fn _ => "(∨l)"
   , LImp       = fn _ => "(→l)"
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

fun andB a b = if a then b else False

fun proofComplete (Proof.Rec p) : bool =
    match p {Goal = fn _ => False,
             Pending = fn _ => False,
             Proof = fn (_, t) =>
                let fun empty _ = True
                    fun single (_, a) = proofComplete a
                    fun singleQ (_, _, a) = proofComplete a
                    fun double (_, a, b) = andB (proofComplete a) (proofComplete b)
                in match t {Cut       = fn (_, a, b) => andB (proofComplete a) (proofComplete b),
                            LExact    = empty,
                            LBot      = empty,
                            RExact    = empty,
                            RTop      = empty,
                            LConj     = single,
                            LNot      = single,
                            LExists   = single,
                            LContract = single,
                            LWeaken   = single,
                            LTop      = single,
                            RDisj     = single,
                            RImp      = single,
                            RNot      = single,
                            RBot      = single,
                            RForall   = single,
                            RContract = single,
                            RWeaken   = single,
                            LForall   = singleQ,
                            RExists   = singleQ,
                            LDisj     = double,
                            LImp      = double,
                            RConj     = double
                            }
                end
             }

fun renderSequent (h : proof -> transaction unit) (s : sequent) : transaction xbody =
    let fun makePending (x : tactic int) : transaction unit = h (Proof.Rec (make [#Pending] (s, x)))
        fun makePendingU prompter (f : universe -> tactic int) (g : tactic int) : transaction unit =
                r <- source "";
                (* XXX would be nice if the ctextbox automatically grabbed focus *)
                set prompter <xml><div class={relMark}><div class={offsetBox}>
                      <ctextbox size=6 source={r}
                        onkeyup={fn k => if eq k 13
                            then (
                                rawu <- get r;
                                u <- rpc (zapParseUniverse rawu);
                                match (fromJson u : result universe)
                                { Success = fn x => makePending (f x)
                                , InternalFailure = fn _ => return ()
                                , EndUserFailure = fn _ => return ()
                                })
                            else return ()}
                        onblur={set prompter <xml></xml>} />
                      or
                      <button value="Contract" onclick={makePending g} />
                    </div></div></xml>
    in
    left <- List.mapXiM (fn i (Logic.Rec x) =>
              (* XXX suboptimal; only want to allocate prompter when necessary *)
              prompter <- source <xml></xml>;
              return <xml><li><dyn signal={signal prompter}/><span class={junct} onclick={match x {
                    Pred   = fn _ => makePending (make [#LExact] i),
                    Conj   = fn _ => makePending (make [#LConj] (i, 0)),
                    Disj   = fn _ => makePending (make [#LDisj] (i, 0, 1)),
                    Imp    = fn _ => makePending (make [#LImp] (i, 0, 1)),
                    Not    = fn _ => makePending (make [#LNot] (i, 0)),
                    Top    = fn _ => makePending (make [#LTop] (i, 0)),
                    Bot    = fn _ => makePending (make [#LBot] i),
                    Forall = fn _ => makePendingU prompter (fn u => make [#LForall] (i, u, 0)) (make [#LContract] (i, 0)),
                    Exists = fn _ => makePending (make [#LExists] (i, 0))
                    }}>
                {renderLogic 0 (Logic.Rec x)}</span></li></xml>) s.Hyps;
    right <- List.mapXiM (fn i (Logic.Rec x) =>
              prompter <- source <xml></xml>;
              return <xml><li><dyn signal={signal prompter}/><span class={junct} onclick={match x {
                    Pred   = fn _ => makePending (make [#RExact] i),
                    Conj   = fn _ => makePending (make [#RConj] (i, 0, 1)),
                    Disj   = fn _ => makePending (make [#RDisj] (i, 0)),
                    Imp    = fn _ => makePending (make [#RImp] (i, 0)),
                    Not    = fn _ => makePending (make [#RNot] (i, 0)),
                    Top    = fn _ => makePending (make [#RTop] i),
                    Bot    = fn _ => makePending (make [#RBot] (i, 0)),
                    Forall = fn _ => makePending (make [#RForall] (i, 0)),
                    Exists = fn _ => makePendingU prompter (fn u => make [#RExists] (i, u, 0)) (make [#RContract] (i, 0)),
                    }}>
                {renderLogic 0 (Logic.Rec x)}</span></li></xml>) s.Cons;
    return <xml><ul class={commaList}>{left}</ul> ⊢ <ul class={commaList}>{right}</ul></xml>
  end
fun renderProof (h : proof -> transaction unit) ((Proof.Rec r) : proof) : transaction xbody = match r
  {Goal = fn s =>
       (* XXX It would be neat if mouse over caused this to change, but a little difficult *)
       sequent <- renderSequent h s;
       return <xml><table><tr><td>{sequent}</td><td class={tagBox}>&nbsp;</td></tr></table></xml>,
   Pending = fn (s, t) => return <xml>...</xml>,
   Proof = fn (s, t) =>
       sequent <- renderSequent h s;
       let fun render f t : transaction xbody =
                sib <- renderProof (fn x => h (Proof.Rec (make [#Proof] (s, f x)))) t;
                return <xml><div class={sibling}>{sib}</div></xml>
           fun empty (_ : int) : transaction xbody = return <xml></xml>
           (* explicit signatures here to avoid "too-deep unification variable" problems *)
           fun single f (n : int, a : proof) : transaction xbody = render (fn x => f (n, x)) a
           fun singleQ f (n : int, u : universe, a : proof) : transaction xbody =
                render (fn x => f (n, u, x)) a
           fun double f (n : int, a : proof, b : proof) : transaction xbody =
                Monad.liftM2 join (render (fn x => f (n, x, b)) a) (render (fn x => f (n, a, x)) b)
       in
       top <- match t {
          Cut       = fn (l, a, b) => Monad.liftM2 join (render (fn x => make [#Cut] (l, x, b)) a) (render (fn x => make [#Cut] (l, a, x)) b),
          LExact    = empty,
          LBot      = empty,
          RExact    = empty,
          RTop      = empty,
          LConj     = single (make [#LConj]),
          LNot      = single (make [#LNot]),
          LExists   = single (make [#LExists]),
          LContract = single (make [#LContract]),
          LWeaken   = single (make [#LWeaken]),
          LTop      = single (make [#LTop]),
          RDisj     = single (make [#RDisj]),
          RImp      = single (make [#RImp]),
          RNot      = single (make [#RNot]),
          RBot      = single (make [#RBot]),
          RForall   = single (make [#RForall]),
          RContract = single (make [#RContract]),
          RWeaken   = single (make [#RWeaken]),
          LForall   = singleQ (make [#LForall]),
          RExists   = singleQ (make [#RExists]),
          LDisj     = double (make [#LDisj]),
          LImp      = double (make [#LImp]),
          RConj     = double (make [#RConj])
       };
       return <xml>
        <div>{top}</div>
        <table>
          <tr>
            <td class={inference}>{sequent}</td>
            <td class={tagBox}>
                <div class={tag}>{[tacticRenderName t]}</div>
            </td>
          </tr>
        </table></xml>
       end
    }

fun zapRefine (x : proof) : transaction string  = return (Haskell.refine (toJson x))
fun zapStart x : transaction string = return (Haskell.start x)

val head = <xml><link rel="stylesheet" type="text/css" href="http://localhost/logitext/style.css" /></xml>

fun handleResultProof handler v proofStatus err (z : string) =
    let val clearError = set err <xml></xml>
        fun showError e = set err <xml><div class={error}>{[e]} <button onclick={clearError} value="Dismiss" /></div></xml>
    in match (fromJson z : result proof)
        { Success = fn r => clearError;
                            bind (renderProof handler r) (set v);
                            set proofStatus (if proofComplete r then proofIsDone else proofIsIncomplete)
        , EndUserFailure = fn e => match e
            { UpdateFailure = fn () => showError "The inference you attempted to make is invalid."
            , ParseFailure = fn () => showError "Parse failure; check your syntax."
            }
        , InternalFailure = fn s => showError s
        }
    end

fun mkWorkspaceRaw showErrors mproof =
  v <- source <xml></xml>;
  err <- source <xml></xml>;
  proofStatus <- source proofIsIncomplete;
  let fun handler x = bind (rpc (zapRefine x)) (handleResultProof handler v proofStatus err)
  in return {
    Onload = bind mproof (handleResultProof handler v proofStatus err),
    Widget = <xml>
          <div class={working}>
            <div dynClass={signal proofStatus}>
              <div class={proof}>
                <dyn signal={signal v}/>
              </div>
            </div>
          </div>
          {if showErrors then <xml><dyn signal={signal err}/></xml> else <xml></xml>}
    </xml>
    }
  end

fun mkWorkspace goal = mkWorkspaceRaw True (rpc (zapStart goal))
fun mkExample proof = mkWorkspaceRaw False (return proof)

fun tutorial () =
  exBasic <- mkWorkspace "Γ |- Δ";
  exSequent <- mkWorkspaceRaw False (rpc (zapStart "A, B |- C, D"));
  (* XXX ewwwwwww *)
  exAxiom <- mkWorkspace "A |- A";
  exAxiomDone <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}}]},\"2\":{\"LExact\":0}}}}";
  exLeft <- mkWorkspace "Γ, A |- A";
  exRight <- mkWorkspace "A |- A, Δ";
  (*
    (Proof.Rec (make [#Proof] (
        {Hyps = Cons (Logic.Rec (make [#Pred] ("A", Nil)), Nil), Cons = Cons (Logic.Rec (make [#Pred] ("A", Nil)), Nil)},
        make [#LExact] 0
        )));
  *)
  exLDisj <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Disj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LDisj\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}}]}}}}}}}";
  infAxiom <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}}]},\"2\":{\"LExact\":1}}}}";
  infLConj <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Conj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LConj\":{\"1\":1,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}}}}}}}";
  infRConj <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Conj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RConj\":{\"1\":0,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"B\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}";
  infLImp <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Imp\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LImp\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}";
  infRImp <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Imp\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RImp\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"B\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}";
  infLNot <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Not\":{\"Pred\":{\"1\":\"A\",\"2\":[]}}}]},\"2\":{\"LNot\":{\"1\":1,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}";
  infRNot <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Not\":{\"Pred\":{\"1\":\"A\",\"2\":[]}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RNot\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}";
  infLForall <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Forall\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}}]},\"2\":{\"LForall\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"z\",\"2\":[]}]}}]}},\"2\":{\"1\":\"z\",\"2\":[]}}}}}}";
  infRForall <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Forall\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RForall\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}";
  infLExists <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Exists\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}}]},\"2\":{\"LExists\":{\"1\":1,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}]}}}}}}}";
  infRExists <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Exists\":{\"1\":\"x\",\"2\":{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"x\",\"2\":[]}]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RExists\":{\"1\":0,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"P\",\"2\":[{\"1\":\"z\",\"2\":[]}]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}},\"2\":{\"1\":\"z\",\"2\":[]}}}}}}";
  infLDisj <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Disj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}}]},\"2\":{\"LDisj\":{\"1\":1,\"3\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}}]}},\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}},{\"Pred\":{\"1\":\"A\",\"2\":[]}}]}}}}}}}";
  infRDisj <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Disj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Pred\":{\"1\":\"B\",\"2\":[]}}}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]},\"2\":{\"RDisj\":{\"1\":0,\"2\":{\"Goal\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Pred\":{\"1\":\"B\",\"2\":[]}},{\"Pred\":{\"1\":\"Δ\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"Γ\",\"2\":[]}}]}}}}}}}";
  exAOrNotA <- mkWorkspace "|- A \/ ~ A";
  exAOrNotADone <- mkExample "{\"Success\":{\"Proof\":{\"1\":{\"cons\":[{\"Disj\":{\"1\":{\"Pred\":{\"1\":\"A\",\"2\":[]}},\"2\":{\"Not\":{\"Pred\":{\"1\":\"A\",\"2\":[]}}}}}],\"hyps\":[]},\"2\":{\"RDisj\":{\"1\":0,\"2\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}},{\"Not\":{\"Pred\":{\"1\":\"A\",\"2\":[]}}}],\"hyps\":[]},\"2\":{\"RNot\":{\"1\":1,\"2\":{\"Proof\":{\"1\":{\"cons\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}}],\"hyps\":[{\"Pred\":{\"1\":\"A\",\"2\":[]}}]},\"2\":{\"LExact\":0}}}}}}}}}}}}";
  exForallIdentity <- mkWorkspace "(forall x. P(x)) |- (forall x. P(x))";
  exAndIdentity <- mkWorkspace "A /\ B |- B /\ A";
  exOrIdentity <- mkWorkspace "A \/ B |- B \/ A";
  exDeMorgan <- mkWorkspace "~(A \/ B) -> ~A /\ ~B";
  exForallDist <- mkWorkspace "(forall x. P(x)) /\ (forall x. Q(x)) -> forall y. P(y) /\ Q(y)";
  exForallContract <- mkWorkspace "forall x. (P(x)->P(f(x))) |- forall x. (P(x) -> P(f(f(x))))";
  return <xml>
  <head>
    <title>Tutorial on Sequent Calculus and First-Order Logic</title>
    {head}
  </head>
  <body onload={
    exBasic.Onload; exAxiom.Onload; exAxiomDone.Onload; exLeft.Onload; exRight.Onload;
    exSequent.Onload; exAOrNotA.Onload; exAOrNotADone.Onload; exLDisj.Onload;
    infAxiom.Onload; infLConj.Onload; infRConj.Onload; infLImp.Onload; infRImp.Onload;
    infLDisj.Onload; infRDisj.Onload; infLNot.Onload; infRNot.Onload; infLForall.Onload; infRForall.Onload;
    infLExists.Onload; infRExists.Onload; exForallIdentity.Onload; exAndIdentity.Onload; exOrIdentity.Onload;
    exDeMorgan.Onload; exForallDist.Onload; exForallContract.Onload
  }>
    <div class={page}>

      <p><i>This interactive tutorial is intended to explain what
      first-order logic and the sequent calculus are to an interested
      software engineer who has some familiarity with basic logic, but
      no experience with formal logic.</i></p>

      <h2>Motivation</h2>

      <p>One of the first things an software engineer learns about is
      the Boolean, and how logical operators like AND/OR/NOT let you
      manipulate these values.  Boolean logic lies behind
      primitive constructs such as the conditional and the loop,
      and a simple understanding based on truth tables is usually
      sufficient for the everyday programming.</p>

      <p>However, if we want logic as a tool to describe the world,
      Boolean logic is fairly inflexible.  Suppose I claim
      "all men are mortal" and "Socrates is a man". I should then be
      able to deduce "Socrates is mortal";  however, in Boolean logic, these three statements
      have no relationship with each other.  We need more structure, so to speak.</p>

      <p>We can achieve this structure using a <i>quantifier</i>,
      encapsulating what we mean by "all men".  Formally, we'd say, "for all <i>x</i>,
      if <i>x</i> is a man, <i>x</i> is a mortal"; symbolically,
      we'd say "∀x. P(x) -> Q(x)", where <i>P</i> is true if <i>x</i>
      is a man, and <i>Q</i> is true if <i>x</i> is mortal.  Use of quantifiers
      takes us from Boolean logic to first-order logic.</p>

      <p>However, now there's a problem: we can't figure out if
      something is true anymore by writing out the truth table.  When a
      quantifier is involved, there may be infinitely many values of
      <i>x</i> in the world, and we can't check if something is true for
      each one.  So we need another way of reasoning about statements in
      first-order logic.  In this tutorial, we'll focus on the question:
      when is a statement in first-order logic <i>valid</i>, that is, it
      is true no matter what predicates or individuals are involved.
      Such statements make up the <i>tautologies</i> (trivially true
      statements) of first-order logic.</p>

      <p>The sequent calculus is one such way of reasoning about statements in
      first-order logic.  It sets up a formal system (similar to
      a state machine or a Turing machine) which precisely specifies
      what valid inferences we can make.  This specification is so precise
      we can program it into a computer, and it is also powerful enough to let us
      derive any true statement in first-order logic (this property is called
      completeness.)</p>

      <p>First-order logic is well worth studying, because it is a
      simple yet powerful tool for modelling the world and writing
      specifications and constraints.  These constraints can be given to
      tools called SMT solvers, which can then automatically determine
      how to satisfy these constraints.  You can't do that with plain
      English!</p>

      <p>The sequent calculus is one tool for understanding how
      first-order logic works on the inside.  It doesn't quite map to
      how humans usually reason about logic, but it is very simple to
      apply, which makes it useful when your intuition is broken.
      However, perhaps more importantly, the notation and concepts
      introduced in sequent calculus are relied upon heavily in the
      academic type theory literature, where inference rules are
      considerably more complicated.  Studying how to understand these
      rules in a simpler setting is essential to being able to "read the
      Greek."  But even if you're not an academic, inference rules are
      a remarkably quick way to understand the type systems of languages.</p>

      <h2>How it works</h2>

      <p>All of the examples in this document are interactive.</p>

      <p><b>Sequents.</b> Below is a sequent.  You can interact with it by clicking
      on the Γ or the Δ, which are <i>clauses</i>, but for this
      particular example, you will get errors, because there are no
      valid deductions for this sequent.  The sequent reads as "Γ
      implies Δ"; the symbol ⊢ is often called a <i>turnstile</i>.</p>

      {exBasic.Widget}

      <p><b>Axioms.</b> Here is a sequent which can make progress. When
      you click on the A, a bar appears on top, which indicates that the
      sequent is axiomatically true: we can assume it without proof.
      The only axioms in this system are when some <i>atomic clause</i>
      (clause containing no logical operators) appears on both sides of
      the turnstile.  A proof is complete when all sequents have bars
      over them.</p>

      {exAxiom.Widget}

      <p><b>Hypotheses on the left.</b> Read the following sequent as "Γ and A imply A."
      If you click on A, you will successfully complete the proof, but if you click
      on Γ, you will fail (because it is not a conclusion you are proving.)</p>

      {exLeft.Widget}

      <p><b>Conclusions on the right.</b>  Read the following sequent as
      "A implies A or Δ".  (Yes, comma means conjunction (AND) on the
      left, and disjunction (OR) on the right. Blame the
      mathematicians.)</p>

      {exRight.Widget}

      <p><b>Inference rules.</b>  We haven't seen any logical operators
      in our sequents, and up until now, clicking on a clause has either
      told us "this sequent is axiomatically true" (completing the
      proof) or given us an error.</p>

      <p>The real meat of sequent calculus has to do with inference rules which
      let us handle sequents which are not axiomatically true.  Here is an example
      of an inference rule:</p>

      {exLDisj.Widget}

      <p>(By convention, Δ and Γ are used as placeholders for other hypotheses
      and conclusions which are not important for the inference rule.)  What
      does this say?  It says that if Γ, A ⊢ Δ and Γ, B ⊢ Δ are true, then
      Γ, A ∨ B ⊢ Δ is true.  (Nota bene: ∨ means disjunction, i.e. "or".)
      It should be pretty clear why this is the case: if I can get to Δ
      using just A, and I can get to Δ using just B, then I can get to Δ
      using A or B.</p>

      <p>Here is another way of looking at it: if I want to prove Γ, A ∨ B ⊢ Δ,
      then all I need to prove is Γ, A ⊢ Δ and Γ, B ⊢ Δ.  This style of thinking,
      where I start with the goal and decide what I need to do to prove it,
      is called <i>backwards deduction</i>.  Sequent calculus is a backwards
      deductive system, because the choice of inference rule is constrained
      by what you want to prove.  The inference
      rule shown above is called the "left-disjunction" rule, because it
      is the rule you use if you see a disjunction on the left side of
      the turnstile.  This lets you do some fairly mindless proofs:</p>

      {exAOrNotA.Widget}

      <p>The above example is an interactive example (actually, all of the
      examples have been interactive, although the earlier ones have been
      fairly constrained).  Try mousing over it;
      elements which are highlighted can be clicked on.  Clicking on a clause
      applies the inference rule associated with that connective, and generates
      a new goal for you to try.  If you click around for a little bit, you'll
      very quickly end up with a complete inference tree:</p>

      {exAOrNotADone.Widget}

      <p>Easy, right?  So, to recap, a sequent calculus proof develops from
      bottom up, and each bar indicates the application of an inference rule.
      Your goal is to get to a statement which is axiomatically true.</p>

      <p>Now that the preliminaries are out of the way, let's see all of
      the inference rules for first order logic:</p>

      <table class={rules}>
      <tr><td colspan=2>{infAxiom.Widget}</td></tr>
      <tr><td>{infLNot.Widget}</td><td>{infRNot.Widget}</td></tr>
      <tr><td>{infLConj.Widget}</td><td>{infRConj.Widget}</td></tr>
      <tr><td>{infLDisj.Widget}</td><td>{infRDisj.Widget}</td></tr>
      <tr><td>{infLImp.Widget}</td><td>{infRImp.Widget}</td></tr>
      <tr><td>{infLForall.Widget}</td><td>{infRForall.Widget}</td></tr>
      <tr><td>{infLExists.Widget}</td><td>{infRExists.Widget}</td></tr>
      </table>

      <p>A few of these rules deserve special attention.  The rules for
      negation are rather odd, because they encode "proof by contradiction".
      It's worth convincing yourself that they work.</p>

      <p>The rules for the quantifiers are particularly interesting.  The
      left and right rules look symmetrical, but there's an important difference:
      in the case of a the left-forall rule, you (the prover) get to pick what
      to replace <i>x</i> with (ignore the button that says "Contract" for now).  In the right-forall rule, the system picks a
      variable that doesn't match anything you've seen before. (In the case
      of exists, the situation is swapped.)  This is important if you
      want to prove this statement:</p>

      {exForallIdentity.Widget}

      <p>If you start off with the left-forall, you are asked for a value
      to instantiate the quantifier with.  By convention, you're allowed to
      assume the existence of an individual (in the lingo, the universe
      is non-empty); you can refer to this individual as <i>z</i>.  But if
      you then apply the right-forall, the system gives you a different
      individual, and you are stuck!  If you try the proof the other way,
      it goes through, because the system gives you an arbitrary variable,
      and you can then pass that to the left-forall prompt.  In general,
      it's a good idea to have the system pick as many variables for you as
      possible, before you do any choosing.</p>

      <p>The final piece of the puzzle is the "contract" button, which
      duplicates a hypothesis or goal, so you can reuse it later.  Use
      of this <i>structural rule</i> may be critical to certain proofs.</p>

      <p>With these inference rules, you now have the capability to
      prove everything in first-order logic!  The next section will contain some exercises
      for you to try.</p>

      <h2>Exercises</h2>

      <p>Nota bene: the last one requires contraction.</p>

      {exAndIdentity.Widget}
      {exOrIdentity.Widget}
      {exDeMorgan.Widget}
      {exForallDist.Widget}
      {exForallContract.Widget}

      <p>Return to <a link={main ()}>the main page.</a></p>

    </div>
  </body>
  </xml>

and proving goal =
  wksp <- mkWorkspace goal;
  return <xml>
        <head>
          <title>Proving {[goal]}</title>
          {head}
        </head>
        <body onload={wksp.Onload}>
        <div class={page}>
          <p>The <a href="http://en.wikipedia.org/wiki/Sequent_calculus">sequent calculus</a>
          is a form of backwards reasoning, with left and right inference rules which operate
          on sequents.  Inference rules correspond closely to <i>clauses</i> in the sequent,
          so in Logitext (and other proof-by-pointing systems), all you need to do is click
          on a clause to see what inference rule is triggered (some rules will need a
          member of the universe, try using <i>z</i>), in which case an input box will pop up
          (you can also choose to duplicate the rules by clicking "Contract").
          If that made no sense to you, check out <a link={tutorial ()}>the tutorial</a>.
          Or, you can <a link={main ()}>return to main page...</a></p>
          {wksp.Widget}
        </div>
        </body>
      </xml>
      (* XXX initially, the proof box should glow, so the user nows that this is special *)
      (* XXX we can't factor out the proof box, because there is no way to compose onload attributes *)
  (*
  seqid <- fresh;
        <body onload={bind (renderProof handler pf) (set v); Js.infinitedrag seqid <xml><dyn signal={signal v}/></xml>}>
          <div class={viewport}>
            <div id={seqid} class={proof}>&nbsp;</div>
          </div>
          *)

and provingTrampoline r =
  redirect (url (proving r.Goal))

and main () =
  let fun tryProof s = <xml><li><a link={proving s}>{[s]}</a></li></xml>
  in
  return <xml>
      <head>
        <title>Logitext</title>
          {head}
      </head>
      <body>
      <div class={page}>
        <p>Logitext is an educational proof assistant for <i>first-order classical
        logic</i> using the <i>sequent calculus</i>, in the same tradition as Jape, Pandora, Panda and Yoda.
        It is intended to assist students who are learning <i>Gentzen trees</i>
        as a way of structuring derivations of logical statements.
        Underneath the hood, Logitext interfaces with Coq in order to check
        the validity of your proof steps. Get the source at
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
        <p>The following variables are in scope for use in your statements:</p>
        <ul>
            <li>A B C : Prop</li>
            <li>P Q R : U -> Prop</li>
            <li>f g h : U -> U</li>
            <li>z : U (our universe is non-empty, so z is always a valid member
            of the universe)</li>
        </ul>
        </div>
      </body>
    </xml>
    end
