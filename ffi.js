function addOnloadHandler(nid, fid, contents, func) {
    // undocumented Ur/Web function 'cat'
    return cat(contents, "<script type=\"text/javascript\">setTimeout(function() {" + func + "(\"" + fid + "\", \"" + nid + "\")},50);</script>");
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
    clearTooltips();
    $("#" + nid).tipsy({html: true, value: data, trigger: "oneway", fade: true}).addClass("explained");
}

function tip(nid, contents) { return addOnloadHandler(nid, "", contents, "dotip"); }
function dotip(fid, nid) {
    $("#" + nid).tipsy().addClass("explained");
}

function tipInner(nid, contents) { return addOnloadHandler(nid, "", contents, "dotipInner"); }
function dotipInner(fid, nid) {
    $("#" + nid + " span[title]").tipsy().addClass("explained");
}

function clearTooltips() { if (activeTooltip) { activeTooltip.hide(); globalHoverState = 'out'; } }

$(document).ready(function(){
    $('span[title]').tipsy().addClass("explained"); // only runs once, before rpcs
    $(document).keyup(function(e) {if (uw_event.keyCode == 27) clearTooltips();});
});
