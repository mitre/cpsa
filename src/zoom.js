// Zoom support for use with cpsagraph and option --zoom

// Find the g element within a near by svg element and apply a transform
function zoom(evt) {
    var g = evt.target.parentNode.lastElementChild.firstElementChild;
    g.setAttribute("transform", "scale("+evt.target.value+")");
}
