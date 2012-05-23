val infinitedrag : id -> xbody -> transaction unit
val tip : id -> xbody -> xbody
val tipInner : id -> xbody -> xbody
val tipHTML : id -> xbody -> xbody -> transaction xbody
val autofocus : id -> xbody -> xbody
val clearTooltips : transaction unit
val activate : id -> string -> transaction xbody
