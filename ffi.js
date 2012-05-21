/* Don't use append; interacts poorly with Urweb embedded objects
 * due to how scripts work. */

// known infelicity: does weird shit if the item you are dragging leaves
// the screen; this is because the /scroller/ activates. You can fix
// this by doing overflow:hidden
function infinitedrag(draggable, contents) {
    jQuery.infinitedrag("#" + draggable, {}, {width: 800, height: 500, oncreate: function(el, col, row) {
        if (col == 0 && row == 0) {
            setInnerHTML(el["0"], contents);
            el.addClass("zeropoint");
        }
    }});
}

$(document).ready(function(){
    $('span[title]').tipsy({opacity:1});
});
