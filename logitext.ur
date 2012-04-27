style sequent
style preview
style viewport
style commaList
style inference
style tag
style tagRow
style step

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

(* hat tip http://blog.sigfpe.com/2010/12/generalising-godels-theorem-with_24.html *)
fun renderParen (b : bool) (r : xbody) : xbody = if b then <xml>({r})</xml> else r
fun renderLogic p ((Logic.Rec r) : logic) : xbody = match r
  {Pred = fn (f, xs) =>
    case xs of
      | Nil => <xml>{[f]}</xml>
      | _ => <xml>{[f]}(<ul class={commaList}>{List.mapX (fn x => <xml><li>{renderUniverse x}</li></xml>) xs}</ul>)</xml>,
   Conj = fn (a, b) => renderParen (p>3) <xml>{renderLogic 3 a} ∧ {renderLogic 3 b}</xml>,
   Disj = fn (a, b) => renderParen (p>2) <xml>{renderLogic 2 a} ∨ {renderLogic 2 b}</xml>,
   Imp = fn (a, b) => renderParen (p>1) <xml>{renderLogic 1 a} → {renderLogic 1 b}</xml>,
   Not = fn a => renderParen (p>4) <xml>¬{renderLogic 5 a}</xml>,
   Top = fn _ => <xml>⊤</xml>,
   Bot = fn _ => <xml>⊥</xml>,
   Forall = fn (x, a) => renderParen (p>0) <xml>∀{[x]}. {renderLogic 0 a}</xml>,
   Exists = fn (x, a) => renderParen (p>0) <xml>∃{[x]}. {renderLogic 0 a}</xml>}

type sequent = { Hyps : list logic, Cons : list logic }
val json_sequent : json sequent = json_record {Hyps = "hyps", Cons = "cons"}

(* our protocol kind of precludes incremental updates. It would be nice
if Ur/Web did this for us. *)

con tactic a = variant [Exact = int,
                        Cut = logic * a * a,
                        LConj = int * a,
                        LDisj = int * a * a,
                        LImp = int * a * a,
                        LBot = int,
                        LNot = int * a,
                        LForall = int * universe * a,
                        LExists = int * a,
                        LContract = int * a,
                        LWeaken = int * a,
                        RConj = int * a * a,
                        RDisj = int * a,
                        RImp = int * a,
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
  in json_variant {Exact = "Exact", Cut = "Cut", LConj = "LConj", LDisj = "LDisj",
        LImp = "LImp", LBot = "LBot", LNot = "LNot", LForall = "LForall", LExists = "LExists",
        LContract = "LContract", LWeaken = "LWeaken", RConj = "RConj", RDisj = "RDisj",
        RImp = "RImp", RNot = "RNot", RForall = "RForall", RExists = "Rexists",
        RWeaken = "Rweaken", RContract = "RContract"}
  end

fun tacticRenderName [a] (t : tactic a) : string = match t
   { Exact      = fn _ => ""
   , Cut        = fn _ => "(cut)"
   , LConj      = fn _ => "(∧l)"
   , LDisj      = fn _ => "(∨l)"
   , LImp       = fn _ => "(→l)"
   , LBot       = fn _ => ""
   , LNot       = fn _ => "(¬l)"
   , LForall    = fn _ => "(∀l)"
   , LExists    = fn _ => "(∃l)"
   , LContract  = fn _ => "(contract:l)"
   , LWeaken    = fn _ => "(weaken:l)"
   , RConj      = fn _ => "(∧r)"
   , RDisj      = fn _ => "(∨r)"
   , RImp       = fn _ => "(→r)"
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
fun renderSequent (h : proof -> transaction unit) (s : sequent) : xbody = <xml>
    <ul class={commaList}>{List.mapXi (fn i (Logic.Rec x) =>
      <xml><li><a onclick={match x {Pred = fn _ => h (Proof.Rec (make [#Pending] (s, make [#Exact] i))),
                                    Conj = fn _ => h (Proof.Rec (make [#Pending] (s, make [#LConj] (i, -1)))),
                                    Disj = fn _ => h (Proof.Rec (make [#Pending] (s, make [#LDisj] (i, -1, -1)))),
                                    Imp = fn _ => h (Proof.Rec (make [#Pending] (s, make [#LImp] (i, -1, -1)))),
                                    Not = fn _ => h (Proof.Rec (make [#Pending] (s, make [#LNot] (i, -1)))),
                                    Top = fn _ => return (),
                                    Bot = fn _ => h (Proof.Rec (make [#Pending] (s, make [#LBot] i))),
                                    Forall = fn _ => return (),
                                    Exists = fn _ => h (Proof.Rec (make [#Pending] (s, make [#LExists] (i, -1))))
                                    }}>
        {renderLogic 0 (Logic.Rec x)}</a></li></xml>) s.Hyps}
    </ul>
      ⊢
    <ul class={commaList}>{List.mapXi (fn i (Logic.Rec x) =>
      <xml><li><a onclick={match x {Pred = fn _ => return (),
                                    Conj = fn _ => h (Proof.Rec (make [#Pending] (s, make [#RConj] (i, -1, -1)))),
                                    Disj = fn _ => h (Proof.Rec (make [#Pending] (s, make [#RDisj] (i, -1)))),
                                    Imp = fn _ => h (Proof.Rec (make [#Pending] (s, make [#RImp] (i, -1)))),
                                    Not = fn _ => h (Proof.Rec (make [#Pending] (s, make [#RNot] (i, -1)))),
                                    Top = fn _ => return (), (*h (Proof.Rec (make [#Pending] (s, make [#RTop] i))),*)
                                    Bot = fn _ => return (),
                                    Forall = fn _ => h (Proof.Rec (make [#Pending] (s, make [#RForall] (i, -1)))),
                                    Exists = fn _ => return ()
                                    }}>
        {renderLogic 0 (Logic.Rec x)}</a></li></xml>) s.Cons}</ul>
  </xml>
fun renderProof (h : proof -> transaction unit) ((Proof.Rec r) : proof) : xbody = match r
  {Goal = fn s => <xml>{renderSequent h s}</xml>, (* XXX do this actively *)
   Pending = fn (s, t) => <xml></xml>,
   Proof = fn (s, t) =>
       <xml><table>
         (* XXX could use some metaprogramming yo *)
          <tr><td rowspan=2>{match t {
            Exact = fn _ => <xml>&nbsp;</xml>,
            Cut = fn (l, a, b) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#Cut] (l, x, b))))) a}</td>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#Cut] (l, a, x))))) b}</td>
              </tr></table></xml>,
            LConj = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LConj] (n, x))))) a}</td>
              </tr></table></xml>,
            LDisj = fn (n, a, b) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LDisj] (n, x, b))))) a}</td>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LDisj] (n, a, x))))) b}</td>
              </tr></table></xml>,
            LImp = fn (n, a, b) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LImp] (n, x, b))))) a}</td>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LImp] (n, a, x))))) b}</td>
              </tr></table></xml>,
            LBot = fn n => <xml>&nbsp;</xml>,
            LNot = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LNot] (n, x))))) a}</td>
              </tr></table></xml>,
            LForall = fn (n, u, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LForall] (n, u, x))))) a}</td>
              </tr></table></xml>,
            LExists = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LExists] (n, x))))) a}</td>
              </tr></table></xml>,
            LContract = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LContract] (n, x))))) a}</td>
              </tr></table></xml>,
            LWeaken = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LWeaken] (n, x))))) a}</td>
              </tr></table></xml>,
            RConj = fn (n, a, b) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RConj] (n, x, b))))) a}</td>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RConj] (n, a, x))))) b}</td>
              </tr></table></xml>,
            RDisj = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RDisj] (n, x))))) a}</td>
              </tr></table></xml>,
            RImp = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RImp] (n, x))))) a}</td>
              </tr></table></xml>,
            RNot = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RNot] (n, x))))) a}</td>
              </tr></table></xml>,
            RForall = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RForall] (n, x))))) a}</td>
              </tr></table></xml>,
            RExists = fn (n, u, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#LForall] (n, u, x))))) a}</td>
              </tr></table></xml>,
            RContract = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RContract] (n, x))))) a}</td>
              </tr></table></xml>,
            RWeaken = fn (n, a) => <xml><table><tr>
                <td>{renderProof (fn x => h (Proof.Rec (make [#Proof] (s, make [#RWeaken] (n, x))))) a}</td>
              </tr></table></xml>
          }}</td><td>&nbsp;</td></tr>
          <tr class={tagRow}><td rowspan=2 class={tag}>{[tacticRenderName t]}</td></tr>
          <tr class={step}><td>{renderSequent h s}</td></tr>
       </table></xml>
    }

fun zap (x : proof) : transaction (option string)  = return (Haskell.refine (toJson x))

fun main () =
  seqid <- fresh;
  v <- source <xml></xml>;
  let val pf =
    (Proof.Rec (make [#Goal]
      {Hyps = Nil,
       Cons = Cons
        (Logic.Rec (make [#Disj]
          (Logic.Rec (make [#Pred] ("A", Nil)),
           Logic.Rec (make [#Pred] ("B", Nil)))),
        Nil)}))
      val rec handler = (fn x => z <- rpc (zap x); case z of
        | None => return ()
        | Some r => set v (renderProof handler (fromJson r : proof))
        )
  in
  return <xml>
        <head>
          <link rel="stylesheet" type="text/css" href="http://localhost/logitext/style.css" />
        </head>
        <body onload={set v (renderProof handler pf); Js.infinitedrag seqid <xml><dyn signal={signal v}/></xml>}>
          <div class={viewport}>
            <div id={seqid} class={sequent}>&nbsp;</div>
          </div>
        </body>
      </xml>
  end
