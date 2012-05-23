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

function activate(nid, code) {
    console.log("activate");
    return "<script type=\"text/javascript\">setTimeout(function() {" + code + "(\"" + nid + "\");},0);</script>";
}

function addOnloadHandler(nid, fid, contents, func) {
    // undocumented Ur/Web function 'cat'
    return cat(contents, "<script type=\"text/javascript\">setTimeout(function() {" + func + "(\"" + fid + "\", \"" + nid + "\")},0);</script>");
}

var globalTempData = {}
function tipHTML(nid, contents, tipcontents) {
    fid = fresh();
    globalTempData[fid] = tipcontents;
    return addOnloadHandler(nid, fid, contents, "dotipHTML");
}
function dotipHTML(fid, nid) {
    var data = globalTempData[fid];
    delete globalTempData[fid];
    $("#" + nid).tipsy({html: true, value: data, trigger: "click", fade: true}).addClass("explained");
}

function tip(nid, contents) { return addOnloadHandler(nid, "", contents, "dotip"); }
function dotip(fid, nid) {
    $("#" + nid).tipsy().addClass("explained");
}

function tipInner(nid, contents) { return addOnloadHandler(nid, "", contents, "dotipInner"); }
function dotipInner(fid, nid) {
    $("#" + nid + " span[title]").tipsy().addClass("explained");
}

function autofocus(nid, contents) { return addOnloadHandler(nid, "", contents, "doautofocus"); }
function doautofocus(fid, nid) { $("#" + nid).focus(); }

function clearTooltips() { console.log("clearTooltips"); if (activeTooltip) { activeTooltip.hide(); globalHoverState = 'out'; } }

$(document).ready(function(){
    $('span[title]').tipsy().addClass("explained"); // only runs once, before rpcs
});
