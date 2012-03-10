style sequent

con state = int
datatype action = Inc | Dec

fun calculate s a : state =
  case a of
    | Inc => s + 1
    | Dec => s - 1

(* distinct from rendering *)
fun available (s : state) : list action =
  Cons (Inc, Cons (Dec, Nil))

fun speculate (s : state) : xbody =
  <xml><div><button value="+1"/>, <button value="-1"/> ⊢ {[s]}</div></xml>

fun generate s =
  k <- source <xml></xml>;
  let val foo = "asdf" in
  (*let val speculah = mp (fn a => speculate (calculate s a)) (available s) in*)
    return <xml><table>
      <tr><td><dyn signal={signal k}/></td></tr>
      <tr><td>
        <button onclick={set k <xml>foo</xml>} value="test" />
        ⊢ {[s]}
      </td></tr>
    </table></xml>
  end
  (*end*)

fun main () =
  tbl <- generate 0;
  return <xml>
    <head>
      <link rel="stylesheet" type="text/css" href="http://localhost/logitext/style.css" />
    </head>
    <body>
      <div class={sequent}>
        {tbl}
      </div>
    </body>
  </xml>
