style sequent
style preview
style viewport

open Json

task initialize = Haskell.init

con godz' a = [1 = string, 2 = list a]
con godz a =
  [Fun = $(godz' a),
   Var = string]
con gods a = variant (godz a)
val json_gods [a ::: Type] (fl : folder (godz a)) (fl' : folder (godz' a)) (j : json a) : json (gods a) =
    @json_variant fl
        {Fun = @json_record _
                (json_string, json_list)
                ("1", "2"),
         Var = json_string}
        {Fun = "Fun",
         Var = "Var"}
datatype god = God of gods god
val json_god' (fl : folder (godz god)) (fl' : folder (godz' god)) () : json god =
  let val rec god_to_json (God r) = let val j : json (gods god) = jf ()
                                    in toJson r
                                    end
      and     god_from_json s = let val j = jf ()
                                    val (r, s') = fromJson' s
                                in (God r, s')
                                end
      and     jf () : json (gods god) = @json_gods fl fl' (tc ())
      and     tc () : json god = mkJson {ToJson = god_to_json,
                                         FromJson = god_from_json}
  in tc ()
  end
val json_god : json god = json_god' ()

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
