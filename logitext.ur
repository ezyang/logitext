style sequent
style preview
style viewport

open Json

task initialize = Haskell.init

con tests a :: {Type} = [TestA = int, TestB = int * a]
con test a :: Type = variant (tests a)

val testb = make [#TestB] (2, True)
val testbint = match testb {TestA = (fn n => n), TestB = (fn (n, _) => n)}


datatype universe =
    Fun of string * list universe
  | Var of string
datatype logic =
    Pred of string * list universe
  | Conj of logic * logic
  | Disj of logic * logic
  | Imp of logic * logic
  | Not of logic
  | Top
  | Bot
  | Forall of string * logic
  | Exists of string * logic
datatype sequent =
    Sequent of list logic * list logic
datatype tactic a =
    Exact of int
  | Cut of logic * a * a
  | LConj of int * a
  | LDisj of int * a * a
  | LImp of int * a * a
  | LBot of int
  | LNot of int * a
  | LForall of int * universe * a
  | LContract of int * a
  | LWeaken of int * a
  | RConj of int * a * a
  | RDisj of int * a
  | RImp of int * a
  | RNot of int * a
  | RForall of int * a
  | RExists of int * universe * a
  | RWeaken of int * a
  | RContract of int * a
datatype proof =
    Goal of sequent
  | Pending of sequent * tactic int
  | Proof of sequent * tactic proof

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
  let val x = Option.get "" (Haskell.refine "{\"Proof\":{\"1\":{\"RNot\":{\"1\":{\"Proof\":{\"1\":{\"Exact\":0},\"0\":{\"cons\":[{\"Pred\":{\"1\":[],\"0\":\"A\"}}],\"hyps\":[{\"Pred\":{\"1\":[],\"0\":\"A\"}}]}}},\"0\":1}},\"0\":{\"cons\":[{\"Pred\":{\"1\":[],\"0\":\"A\"}},{\"Not\":{\"Pred\":{\"1\":[],\"0\":\"A\"}}}],\"hyps\":[]}}}"
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
