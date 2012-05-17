style proof
style inference
style tagBox
style tag
style upper
style sibling
style junct

style viewport
style commaList

open Json

task initialize = Haskell.init

structure Universe = Json.Recursive(struct
  con t a = variant [Fun = string * list a,
                     Var = string]
  fun json_t [a] (_ : json a) : json (t a) =
    let val json_fun : json (string * list a) = json_record ("1", "2")
    in json_variant {Fun = "Fun", Var = "Var"}
    end
end)
type universe = Universe.r
fun renderUniverse ((Universe.Rec r) : universe) : xbody = match r
  {Fun = fn (f, xs) => <xml>{[f]}(<ul class={commaList}>{List.mapX (fn x => <xml><li>{renderUniverse x}</li></xml>) xs}</ul>)</xml>,
   Var = fn x => <xml>{[x]}</xml>}

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
      | _ => <xml>{[f]}(<ul class={commaList}>{List.mapX (fn x => <xml><li>{renderUniverse x}</li></xml>) xs}</ul>)</xml>,
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

(* our protocol kind of precludes incremental updates. It would be nice
if Ur/Web did this for us. *)

con tactic a = variant [Cut = logic * a * a,
                        LExact = int,
                        LConj = int * a,
                        LDisj = int * a * a,
                        LImp = int * a * a,
                        LBot = int,
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
        LImp = "LImp", LBot = "LBot", LNot = "LNot", LForall = "LForall", LExists = "LExists",
        LContract = "LContract", LWeaken = "LWeaken", RExact = "RExact", RConj = "RConj", RDisj = "RDisj",
        RImp = "RImp", RTop = "RTop", RNot = "RNot", RForall = "RForall", RExists = "Rexists",
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
   , RNot       = fn _ => "(¬r)"
   , RForall    = fn _ => "(∀r)"
   , RExists    = fn _ => "(∃r)"
   , RContract  = fn _ => "(contract:r)"
   , RWeaken    = fn _ => "(weaken:r)"
   }

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
fun renderSequent (h : proof -> transaction unit) (s : sequent) : xbody =
    let fun makePending x = h (Proof.Rec (make [#Pending] (s, x)))
    in
    <xml><ul class={commaList}>{List.mapXi (fn i (Logic.Rec x) =>
      <xml><li><span class={junct} onclick={match x {
            Pred   = fn _ => makePending (make [#LExact] i),
            Conj   = fn _ => makePending (make [#LConj] (i, 0)),
            Disj   = fn _ => makePending (make [#LDisj] (i, 0, 1)),
            Imp    = fn _ => makePending (make [#LImp] (i, 0, 1)),
            Not    = fn _ => makePending (make [#LNot] (i, 0)),
            Top    = fn _ => return (),
            Bot    = fn _ => makePending (make [#LBot] i),
            Forall = fn _ => return (),
            Exists = fn _ => makePending (make [#LExists] (i, 0))
            }}>
        {renderLogic 0 (Logic.Rec x)}</span></li></xml>) s.Hyps}
    </ul>
      ⊢
    <ul class={commaList}>{List.mapXi (fn i (Logic.Rec x) =>
      <xml><li><span class={junct} onclick={match x {
            Pred   = fn _ => makePending (make [#RExact] i),
            Conj   = fn _ => makePending (make [#RConj] (i, 0, 1)),
            Disj   = fn _ => makePending (make [#RDisj] (i, 0)),
            Imp    = fn _ => makePending (make [#RImp] (i, 0)),
            Not    = fn _ => makePending (make [#RNot] (i, 0)),
            Top    = fn _ => makePending (make [#RTop] i),
            Bot    = fn _ => return (),
            Forall = fn _ => makePending (make [#RForall] (i, 0)),
            Exists = fn _ => return ()
            }}>
        {renderLogic 0 (Logic.Rec x)}</span></li></xml>) s.Cons}</ul>
  </xml>
  end
fun renderProof (h : proof -> transaction unit) ((Proof.Rec r) : proof) : xbody = match r
  {Goal = fn s => 
       (* XXX It would be neat if mouse over caused this to change, but a little difficult *)
       <xml><table><tr><td>{renderSequent h s}</td><td class={tagBox}>&nbsp;</td></tr></table></xml>,
   Pending = fn (s, t) => <xml></xml>,
   Proof = fn (s, t) =>
       let fun render f t = <xml><div class={sibling}>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, f x)))) t}</div></xml>
           fun empty (_ : int) = <xml></xml>
       in <xml>
          <div>{match t {
            Cut       = fn (l, a, b) => join (render (fn x => make [#Cut] (l, x, b)) a) (render (fn x => make [#Cut] (l, a, x)) b),
            LExact    = empty,
            LBot      = empty,
            RExact    = empty,
            RTop      = empty,
            (* XXX could use some metaprogramming.  However, doing it the obvious
               way runs into "Substitution in constructor is blocked by a too-deep unification variable";
               if you add more type annotations, you then get "Can't unify record constructors"
            *)
            LConj     = fn (n, a) => render (fn x => make [#LConj]     (n, x)) a,
            LNot      = fn (n, a) => render (fn x => make [#LNot]      (n, x)) a,
            LExists   = fn (n, a) => render (fn x => make [#LExists]   (n, x)) a,
            LContract = fn (n, a) => render (fn x => make [#LContract] (n, x)) a,
            LWeaken   = fn (n, a) => render (fn x => make [#LWeaken]   (n, x)) a,
            RDisj     = fn (n, a) => render (fn x => make [#RDisj]     (n, x)) a,
            RImp      = fn (n, a) => render (fn x => make [#RImp]      (n, x)) a,
            RNot      = fn (n, a) => render (fn x => make [#RNot]      (n, x)) a,
            RForall   = fn (n, a) => render (fn x => make [#RForall]   (n, x)) a,
            RContract = fn (n, a) => render (fn x => make [#RContract] (n, x)) a,
            RWeaken   = fn (n, a) => render (fn x => make [#RWeaken]   (n, x)) a,
            LForall   = fn (n, u, a) => render (fn x => make [#LForall] (n, u, x)) a,
            RExists   = fn (n, u, a) => render (fn x => make [#RExists] (n, u, x)) a,
            LDisj     = fn (n, a, b) => join (render (fn x => make [#LDisj] (n, x, b)) a) (render (fn x => make [#LDisj] (n, a, x)) b),
            LImp      = fn (n, a, b) => join (render (fn x => make [#LImp]  (n, x, b)) a) (render (fn x => make [#LImp]  (n, a, x)) b),
            RConj     = fn (n, a, b) => join (render (fn x => make [#RConj] (n, x, b)) a) (render (fn x => make [#RConj] (n, a, x)) b),
        }}</div>
        <table>
          <tr>
            <td class={inference}>{renderSequent h s}</td>
            <td class={tagBox}>
                <div class={tag}>{[tacticRenderName t]}</div>
            </td>
          </tr>
        </table></xml>
       end
    }

fun zapRefine (x : proof) : transaction (option string)  = return (Haskell.refine (toJson x))
fun zapStart x : transaction (option string) = return (Haskell.start x)

val head = <xml><link rel="stylesheet" type="text/css" href="http://localhost/logitext/style.css" /></xml>

fun proving goal =
  v <- source <xml></xml>;
  let fun handler x = z <- rpc (zapRefine x); case z of
        | None => return ()
        | Some r => set v (renderProof handler (fromJson r : proof))
  in
  return <xml>
        <head>
          <title>Proving {[goal]}</title>
          {head}
        </head>
        <body onload={
          x <- rpc (zapStart goal);
          case x of
              | None => return ()
              | Some r => set v (renderProof handler (fromJson r : proof))
        }>
          <p><a link={main ()}>Try something else...</a></p>
          <div class={proof}>
            <dyn signal={signal v}/>
          </div>
        </body>
      </xml>
  end
  (*
  seqid <- fresh;
        <body onload={set v (renderProof handler pf); Js.infinitedrag seqid <xml><dyn signal={signal v}/></xml>}>
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
      </head>
      <body>
        <p>Type in something to prove (XXX syntax):</p>
        <form>
          <textbox{#Goal}/><submit action={provingTrampoline} value="Prove"/>
        </form>
        <p>Here are some examples:</p>
        <ul>
          {tryProof "((P -> Q) -> P) -> P"}
          {tryProof "A \/ ~A"}
        </ul>
      </body>
    </xml>
    end
