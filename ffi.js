function tipHTML(nid, data) {
    $("#" + nid).tipsy({html: true, value: data, trigger: "oneway", fade: true}).addClass("explained");
}
function tip(nid) {
    $("#" + nid).tipsy().addClass("explained");
}
function tipInner(nid) {
    $("#" + nid + " span[title]").tipsy().addClass("explained");
}

function clearTooltips() { if (activeTooltip) { activeTooltip.hide(); globalHoverState = 'out'; } }

$(document).ready(function(){
    $('span[title]').tipsy().addClass("explained"); // only runs once, before rpcs
    $(document).keyup(function(e) {if (e.keyCode == 27) clearTooltips();});
});
