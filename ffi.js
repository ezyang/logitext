/* Don't use append; interacts poorly with Urweb embedded objects
 * due to how scripts work. */

function infinitedrag(draggable, contents) {
    jQuery.infinitedrag("#" + draggable, {}, {width: 800, height: 500, oncreate: function(el, col, row) {
        if (col == 0 && row == 0) {
            div = document.createElement('div');
            div.innerHTML = contents;
            for (var i = 0; i < div.childNodes.length; i++) {
                el["0"].appendChild(div.childNodes[i]);
            }
            runScripts(el["0"]);
        }
    }});
}
