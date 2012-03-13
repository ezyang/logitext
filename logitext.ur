style sequent
style viewport

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
  <xml><div><button value="-1"/>, <button value="+1"/> ⊢ {[s]}</div></xml>

(* rpc should be able to deal with anonymous expressions; just lambda-lift that
fun zorp n : transaction int = return (Coq.test n)
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
  return <xml>
    <head>
      <link rel="stylesheet" type="text/css" href="http://localhost/logitext/style.css" />
    </head>
    <body onload={Js.infinitedrag seqid tbl}>
      <div class={viewport}>
        <div id={seqid} class={sequent}>&nbsp;</div>
      </div>
    </body>
  </xml>
