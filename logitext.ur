style proof
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
   , LContract  = fn _ => "(contract:l)"
   , LWeaken    = fn _ => "(weaken:l)"
   , RExact     = fn _ => ""
   , RConj      = fn _ => "(∧r)"
   , RDisj      = fn _ => "(∨r)"
   , RImp       = fn _ => "(→r)"
   , RTop       = fn _ => ""
   , RBot       = fn _ => ""
   , RNot       = fn _ => "(¬r)"
   , RForall    = fn _ => "(∀r)"
   , RExists    = fn _ => "(∃r)"
   , RContract  = fn _ => "(contract:r)"
   , RWeaken    = fn _ => "(weaken:r)"
   }

con end_user_failure = variant [UpdateFailure = unit, ParseFailure = unit]
val json_end_user_failure : json end_user_failure = json_variant {UpdateFailure = "UpdateFailure", ParseFailure = "ParseFailure"}

con result a = variant [EndUserFailure = end_user_failure, InternalFailure = string, Success = a]
fun json_result [a] (_ : json a) : json (result a) =
    json_variant {EndUserFailure = "EndUserFailure", InternalFailure = "InternalFailure", Success = "Success"}

fun mapXiM [m ::: (Type -> Type)] (_ : monad m) [a] [ctx ::: {Unit}] (f : int -> a -> m (xml ctx [] [])) : list a -> m (xml ctx [] []) =
    let
        fun mapXiM' i ls =
            case ls of
                [] => return <xml/>
              | x :: ls =>
                this <- f i x;
                rest <- mapXiM' (i+1) ls;
                return <xml>{this}{rest}</xml>
    in
        mapXiM' 0
    end

fun liftM2 [m ::: (Type -> Type)] (_ : monad m) [a] [b] [c] (f : a -> b -> c) (mx : m a) (my : m b) : m c =
    x <- mx;
    y <- my;
    return (f x y)

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
fun renderSequent (h : proof -> transaction unit) (s : sequent) : transaction xbody =
    let fun makePending (x : tactic int) : transaction unit = h (Proof.Rec (make [#Pending] (s, x)))
        fun makePendingU prompter (f : universe -> tactic int) : transaction unit =
                r <- source "";
                (* XXX would be nice if the ctextbox automatically grabbed focus *)
                set prompter <xml><div class={relMark}>
                    <div class={offsetBox}>
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
                    </div>
                  </div></xml>
    in
    left <- mapXiM (fn i (Logic.Rec x) =>
              (* XXX suboptimal; only want to allocate prompter when necessary *)
              prompter <- source <xml></xml>;
              return <xml><li><span class={junct} onclick={match x {
                    Pred   = fn _ => makePending (make [#LExact] i),
                    Conj   = fn _ => makePending (make [#LConj] (i, 0)),
                    Disj   = fn _ => makePending (make [#LDisj] (i, 0, 1)),
                    Imp    = fn _ => makePending (make [#LImp] (i, 0, 1)),
                    Not    = fn _ => makePending (make [#LNot] (i, 0)),
                    Top    = fn _ => makePending (make [#LTop] (i, 0)),
                    Bot    = fn _ => makePending (make [#LBot] i),
                    Forall = fn _ => makePendingU prompter (fn u => make [#LForall] (i, u, 0)),
                    Exists = fn _ => makePending (make [#LExists] (i, 0))
                    }}>
                {renderLogic 0 (Logic.Rec x)}</span><dyn signal={signal prompter}/></li></xml>) s.Hyps;
    right <- mapXiM (fn i (Logic.Rec x) =>
              prompter <- source <xml></xml>;
              return <xml><li><span class={junct} onclick={match x {
                    Pred   = fn _ => makePending (make [#RExact] i),
                    Conj   = fn _ => makePending (make [#RConj] (i, 0, 1)),
                    Disj   = fn _ => makePending (make [#RDisj] (i, 0)),
                    Imp    = fn _ => makePending (make [#RImp] (i, 0)),
                    Not    = fn _ => makePending (make [#RNot] (i, 0)),
                    Top    = fn _ => makePending (make [#RTop] i),
                    Bot    = fn _ => makePending (make [#RBot] (i, 0)),
                    Forall = fn _ => makePending (make [#RForall] (i, 0)),
                    Exists = fn _ => makePendingU prompter (fn u => make [#RExists] (i, u, 0)),
                    }}>
                {renderLogic 0 (Logic.Rec x)}</span><dyn signal={signal prompter}/></li></xml>) s.Cons;
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
                liftM2 join (render (fn x => f (n, x, b)) a) (render (fn x => f (n, a, x)) b)
       in
       top <- match t {
          Cut       = fn (l, a, b) => liftM2 join (render (fn x => make [#Cut] (l, x, b)) a) (render (fn x => make [#Cut] (l, a, x)) b),
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

fun proving goal =
  v <- source <xml></xml>;
  err <- source <xml></xml>;
  let fun showError e = set err <xml><div class={error}>{[e]}</div></xml>
      val clearError = set err <xml></xml>
      fun handler x =
        z <- rpc (zapRefine x);
        (* XXX duplication *)
        match (fromJson z : result proof)
            { Success = fn r => clearError; bind (renderProof handler r) (set v)
            , EndUserFailure = fn e => match e
                { UpdateFailure = fn () => showError "No valid inference rule."
                , ParseFailure = fn () => showError "Parse failure."
                }
            , InternalFailure = fn s => showError s
            }
  in
  return <xml>
        <head>
          <title>Proving {[goal]}</title>
          {head}
        </head>
        <body onload={
          x <- rpc (zapStart goal);
          match (fromJson x : result proof)
              { Success = fn r => clearError; bind (renderProof handler r) (set v)
              , EndUserFailure = fn e => match e
                { UpdateFailure = fn () => showError "Oops! Something bad happened."
                , ParseFailure = fn () => showError "Parse failure."
                }
              , InternalFailure = fn s => showError s
              }
        }>
        <div class={page}>
          <p>Sequent calculus is a form of <i>backwards reasoning</i>, where
          you start with the goal and make deductions until you reach an axiomatically
          valid statement (A ⊢ A). The turnstile (⊢) is a meta-implication which
          divides your hypotheses (on the left) and your goals (on the right).  All
          of the hypotheses are available to you, and as a system for classical
          logic you only need to manage to prove one of the goals (it's a disjunction).
          Sequent calculus inference steps involve the backwards elimination of
          a clause (on the left side or right side); you can find out what happens
          if you try to eliminate a clause by clicking on it.  Some inference rules
          require you to specify a value to instantiate a variable to; type it in and press enter.
          <a link={main ()}>Or try something else...</a></p>
          <div class={working}>
              <div class={proof}>
                <dyn signal={signal v}/>
                <dyn signal={signal err}/>
              </div>
          </div>
        </div>
        </body>
      </xml>
      (* XXX initially, the proof box should glow, so the user nows that this is special *)
      (* XXX we can't factor out the proof box, because there is no way to compose onload attributes *)
  end
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
        the validity of your proof steps.</p>
        <p>To get started, type in something to prove:</p>
        <form>
          <textbox{#Goal}/><submit action={provingTrampoline} value="Prove"/>
        </form>
        <p>The syntax is basically what you would expect, but here are some examples to get you started:</p>
        <ul>
          {tryProof "((A -> B) -> A) -> A"}
          {tryProof "A \/ ~A"}
          {tryProof "(forall x, P(x)) -> (exists x, P(x))"}
        </ul>
        <p>Unfortunately, we don't currently support contraction/weakening rules,
        so there may be some statements you cannot prove yet.</p>
        </div>
      </body>
    </xml>
    end
