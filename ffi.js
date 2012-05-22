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

function tooltipify(contents) {
    nid = fresh();
    // lol lol undocument Ur/Web stuff
    return cat(cat("<div id=\"" + nid + "\">", contents), "<script type=\"text/javascript\">runtip(\"" + nid + "\");</script></div>");
}

function runtip(nid) {
    // Ur/Web runs the embedded JavaScript too early, so you need to
    // schedule it later
    setTimeout(function() {$("#" + nid + " *[title]").tipsy().addClass("explained")}, 0);
}

$(document).ready(function(){
    // doesn't hit rpc generated things
    $('span[title]').tipsy().addClass("explained");
});
