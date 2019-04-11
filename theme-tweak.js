var Theme = {
    'props': JSON.parse(localStorage.getItem('theme/'+window.location.pathname)),
    'propUnits': {
	'--luminosity': '%',
	'--prim-hue': 'deg',
	'--low-hue': 'deg',
	'--high-hue': 'deg',
	'--prim-saturation': '%',
	'--low-saturation': '%',
	'--high-saturation': '%',
	'--min-contrast': '%',
	'--max-contrast': '%',
	'font-size': '%',
    },
    'propNames': ['--prim-hue','--prim-saturation','--low-hue','--low-saturation','--high-hue','--high-saturation', '--min-contrast', '--max-contrast', '--luminosity', 'font-size'],
    'setProp': function (e,prop,val) {
	var oldval = this.props[prop];
	this.props[prop] = val;
	localStorage.setItem('theme/'+window.location.pathname,JSON.stringify(this.props));

	if(prop == 'light') {
	    if(oldval != this.props[prop]) {
		var lst = e.classList; lst.toggle('ground-dark'); lst.toggle('ground-light');
	    }
	}
	else {
	    var stl = "", p;
	    for(var p in this.propNames) {
		stl = stl + " " + this.propNames[p]+': '+this.props[this.propNames[p]] + ";"
	    }
	    e.setAttribute('style', stl);

	    var spans = e.getElementsByClassName('theme-prop-display');
	    for (var spanI in spans) {
		var span = spans.item(spanI);
		if(span !== null) {
		    span.textContent = this.props[span.getAttribute('data-prop-name')];
		}
	    }
	}
	

    },

    'attach': function (e) {
	this.setProp(e,'font-size',this.props['font-size']);
	
	if(! this.props['light']) {
	    e.classList.toggle('ground-dark');
	    e.classList.toggle('ground-light');
	}

	var elts = e.getElementsByClassName('theme-slider');
	for(var x in elts) {
	    var elt = elts.item(x);
	    (function (tw,elt,slide) {
		var th_val = elt.getElementsByClassName('theme-prop-display')[0];
		var prop = th_val.getAttribute('data-prop-name');
		slide.value = parseInt(tw.props[prop]);
		slide.addEventListener('input',function () {
		    tw.setProp(e,prop,this.value + tw.propUnits[prop]);
		});
	    })(this,elt,elt.getElementsByTagName('input')[0]);
	}
    }
};

if(Theme.props === null) {
    Theme.props = {
	'light': true,
	'--prim-hue': '53deg', '--prim-saturation': '36%',
	'--low-hue': '-50deg', '--low-saturation': '30%',
	'--high-hue': '50deg', '--high-saturation': '30%',
	'--min-contrast': '50%', '--max-contrast': '85%',
	'font-size': '100%'
    };
}

