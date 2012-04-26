style sequent
style preview
style viewport

open Json

task initialize = Haskell.init

(* This hack is HILARIOUS. Also a little sad. *)

structure Universe = Json.Recursive(struct
  con t a = variant [Fun = string * list a,
                     Var = string]
  fun json_t [a] (_ : json a) : json (t a) =
    let val json_fun : json (string * list a) = json_record ("1", "2")
    in json_variant {Fun = "Fun", Var = "Var"}
    end
end)
type universe = Universe.r

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

type sequent = { Hyps : list logic, Cons : list logic }
val json_sequent : json sequent = json_record {Hyps = "Hyps", Cons = "Cons"}

con tactic a = variant [Exact = int,
                        Cut = logic * a * a,
                        LConj = int * a,
                        LDisj = int * a * a,
                        LImp = int * a * a,
                        LBot = int,
                        LNot = int * a,
                        LForall = int * universe * a,
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
        LImp = "LImp", LBot = "LBot", LNot = "LNot", LForall = "LForall",
        LContract = "LContract", LWeaken = "LWeaken", RConj = "RConj", RDisj = "RDisj",
        RImp = "RImp", RNot = "RNot", RForall = "RForall", RExists = "Rexists",
        RWeaken = "Rweaken", RContract = "RContract"}
  end

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

con state = int
datatype action = Inc | Dec
datatype mode = Preview | Final

fun calculate s a : state =
  case a of
    | Inc => s + 1
    | Dec => s - 1

(* distinct from rendering *)
fun available (s : state) : list action =
  Cons (Dec, Cons (Inc, Nil))

fun speculate (s : state) : xbody =
  <xml><div class={preview}><button value="-1"/>, <button value="+1"/> ⊢ {[s]}</div></xml>

(* rpc should be able to deal with anonymous expressions; just lambda-lift that
fun zorp n : transaction int =
    <button onclick={v <- rpc (zorp 2); set k <xml>{[v]}</xml>} value="+1" />*)

fun generate s =
  previewChan <- source <xml/>;
  finalChan <- source <xml/>;
  status <- source Preview;
  let val speculations = List.mp (fn a => speculate (calculate s a)) (available s)
      fun blank () = set previewChan <xml/>
      fun preview n = set previewChan (Option.get <xml/> (List.nth speculations n))
      fun run a = generate (calculate s a)
      fun apply a =
        r <- rpc (run a);
        set finalChan r;
        set status Final
  (* Tables here are wrong:
        - you can't nest more than 28ish, so it doesn't work for large
          proof trees (though, arguably, we shouldn't need really large trees)
        - you can't actually make consistent update (all previous
          elements stay at the same place when you make a new one) work properly
     ...So we actually want to absolutely position things
  *)
  in return <xml><table>
      <tr><td><dyn signal={
        stat <- signal status;
        case stat of
          | Preview => signal previewChan
          | Final => signal finalChan
      }/></td></tr>
      <tr><td>
        <button onclick={apply Dec} onmouseover={preview 0} onmouseout={blank ()} value="-1" />,
        <button onclick={apply Inc} onmouseover={preview 1} onmouseout={blank ()} value="+1" />
        ⊢ {[s]}
      </td></tr>
     </table></xml>
  end

fun main () =
  tbl <- generate 0;
  seqid <- fresh;
  let val x = Option.get "" (Haskell.refine "{\"Proof\":{\"2\":{\"RNot\":{\"2\":{\"Proof\":{\"2\":{\"Exact\":0},\"1\":{\"cons\":[{\"Pred\":{\"2\":[],\"1\":\"A\"}}],\"hyps\":[{\"Pred\":{\"2\":[],\"1\":\"A\"}}]}}},\"1\":1}},\"1\":{\"cons\":[{\"Pred\":{\"2\":[],\"1\":\"A\"}},{\"Not\":{\"Pred\":{\"2\":[],\"1\":\"A\"}}}],\"hyps\":[]}}}"
  )
  in return <xml>
        <head>
          <link rel="stylesheet" type="text/css" href="http://localhost/logitext/style.css" />
        </head>
        <body onload={Js.infinitedrag seqid tbl}>
          <div>{[x]}</div>
          <div class={viewport}>
            <div id={seqid} class={sequent}>&nbsp;</div>
          </div>
        </body>
      </xml>
  end
