// Slider support for use with cpsagraph and option --zoom

// Check to see if HTML5 sliders are available.
function have_input_type(t) {
    var ns = document.documentElement.namespaceURI;
    var i = document.createElementNS(ns, "input");
    i.setAttribute("type", t);
    return i.type !== "text";
}

var have_sliders = have_input_type("range");

// Create an element that controls scaling
function scaler(ns) {
    if (have_sliders)
	return slider(ns);
    else
	return selector(ns);
}

// Create an HTML5 slider for scaling
function slider(ns) {
    var i = document.createElementNS(ns, "input");
    i.setAttribute("type", "range");
    i.setAttribute("min", 0.2);
    i.setAttribute("max", 1.0);
    i.setAttribute("step", 0.2);
    i.setAttribute("value", 1.0);
    i.addEventListener("change", zoom, false);
    return i;
}

// Create an old style select element for scaling
function selector(ns) {
    var s = document.createElementNS(ns, "select");
    s.appendChild(option(ns, "1.0"));
    s.appendChild(option(ns, "0.8"));
    s.appendChild(option(ns, "0.6"));
    s.appendChild(option(ns, "0.4"));
    s.appendChild(option(ns, "0.2"));
    s.addEventListener("change", zoom, false);
    return s;
}

// Create one option for use within a select element
function option(ns, val) {
    var o = document.createElementNS(ns, "option");
    o.setAttribute("value", val);
    o.appendChild(document.createTextNode(val));
    return o;
}

// At load time, insert browser appropriate scaler
function init() {
    var ns = document.documentElement.namespaceURI;
    var nodes = document.getElementsByTagName("div");
    var i;
    for (i = 0; i < nodes.length; i++) {
	var n = nodes.item(i);
	var b = document.createElementNS(ns, "br");
	n.insertBefore(b, n.firstChild);
	n.insertBefore(scaler(ns), n.firstChild);
    }
}

// Find the g element within a near by svg element and apply a transform
function zoom(evt) {
    var g = evt.target.parentNode.lastElementChild.firstElementChild;
    g.setAttribute("transform", "scale("+evt.target.value+")");
}
