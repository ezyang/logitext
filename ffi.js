/* Don't use append; interacts poorly with Urweb embedded objects
 * due to how scripts work. */

function infinitedrag(draggable, contents) {
    jQuery.infinitedrag("#" + draggable, {}, {width: 800, height: 500, oncreate: function(el, col, row) {
        if (col == 0 && row == 0) {
            el["0"].innerHTML = contents;
        }
    }});
}
