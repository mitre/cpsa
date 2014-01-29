// Slide presentation support for Firefox
// John D. Ramsdell -- January 2008

// This code assumes the variable slides holds an array containing the
// basename of each slide that makes up a presentation.  The slides
// variable should be defined in slides.js, and each slide should
// include the following in its header.

// <head>
//   ...
//   <script type='application/ecmascript' src="slides.js"></script>
//   <script type='application/ecmascript' src="navigation.js"></script>
// </head>
//
// <body onload="init()">

// The body font size will be adjusted dynamically if the variable
// ratio is a number giving the ratio of the font size to the window
// height.  The variable is usually also defined in slides.js.  A
// ratio of zero disables dynamic font size selection.

// Navigation support

// Returns the index of this slide, or -1 on error.
function thisSlide() {
    var basename = document.URL;
    var i = basename.lastIndexOf('/');
    basename = basename.substr(i + 1);
    for (i = 0; i < slides.length; i++)
	if (basename == slides[i])
	    return i;
    return -1;
}

// Navigate to the next slide or wrap around to the first one
function nextSlide() {
    var i = thisSlide();
    if (i >= slides.length - 1)
	moveTo(0);
    else if (i >= 0) {
	moveTo(i + 1);
    }
}

// Navigate to the previous slide or wrap around to the last one
function previousSlide() {
    var i = thisSlide();
    if (i == 0)
	moveTo(slides.length - 1);
    else if (i > 0) {
	moveTo(i - 1);
    }
}

function firstSlide() {
    moveTo(0);
}

function lastSlide() {
    moveTo(slides.length - 1);
}

function moveTo(i) {
    if (i >= 0 && i < slides.length)
	window.location = slides[i];
}

function keyDown(event) {
    switch (event.keyCode) {
    case 32: nextSlide(); break;     // space
    case 13: nextSlide(); break;     // enter
    case 39: nextSlide(); break;     // right
    case 34: nextSlide(); break;     // page down
    case  8: previousSlide(); break; // backspace
    case 37: previousSlide(); break; // left
    case 33: previousSlide(); break; // page up
    case 36: firstSlide(); break;    // home
    case 35: lastSlide(); break;     // end
    }
    event.returnValue = false;
}

// Resize the body font if the variable ratio is not zero.  Its value
// the ratio of the font size to the window height.

function resize() {
    if (ratio) {
	var content = document.getElementById('content');
	var footer = document.getElementById('footer');
	if (window.innerHeight) {
	    var size = ratio * window.innerHeight + 'px';
	    content.style.fontSize = size;
	    footer.style.fontSize = size;
	}
    }
}

function addResize() {
    resize();
    window.onresize = resize;
}

function addDivs() {
    var content = document.createElement('div');
    content.setAttribute('id', 'content');
    var kids = document.body.childNodes;
    for (var i = 0; i < kids.length; i++)
	if (kids.item(i).nodeType == 1) // Move elements only
	    content.appendChild(kids.item(i));
    document.body.appendChild(content);
    var footer = document.createElement('div');
    footer.setAttribute('id', 'footer');
    document.body.appendChild(footer);
}

function init() {
    addDivs();
    addResize();
    document.onkeydown = keyDown;
}
