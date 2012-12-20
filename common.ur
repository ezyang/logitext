val declareCase = @@Variant.declareCase
val typeCase = @@Variant.typeCase

fun activeCode m = <xml><active code={m; return <xml/>} /></xml>
fun activate x m = <xml>{x}{activeCode m}</xml>

val headTemplate = <xml>
    <link rel="stylesheet" type="text/css" href="http://localhost/logitext/style.css" />
    <link rel="stylesheet" type="text/css" href="http://localhost/logitext/tipsy.css" />
    </xml>

fun andB a b = if a then b else False

fun snoc [a] (xs : list a) (x : a) : list a = List.append xs (x :: [])
