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

function addOnloadHandler(nid, contents, func) {
    // undocumented Ur/Web function 'cat'
    return cat(contents, "<script type=\"text/javascript\">setTimeout(function() {" + func + "(\"" + nid + "\")},0);</script>");
}

function tip(nid, contents) { return addOnloadHandler(nid, contents, "dotip"); }
function dotip(nid) { $("#" + nid).tipsy().addClass("explained"); }

function tipInner(nid, contents) { return addOnloadHandler(nid, contents, "dotipInner"); }
function dotipInner(nid) { $("#" + nid + " span[title]").tipsy().addClass("explained"); }

function autofocus(nid, contents) { return addOnloadHandler(nid, contents, "doautofocus"); }
function doautofocus(nid) { $("#" + nid).focus(); }

$(document).ready(function(){
    $('span[title]').tipsy().addClass("explained"); // only runs once, before rpcs
});
