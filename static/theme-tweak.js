function rawUnit(u) { return function (x) {
    alert('adding unit '+u+' to value '+x);
    '' + x.toString() + u; }; }

var Theme = {
    'props': JSON.parse(localStorage.getItem('theme/'+window.location.pathname)),
    'propUnits': {
	'--luminosity': function (n) { return (n / 100).toString(); },
	'--prim-hue': rawUnit('deg'),
	'--low-hue': rawUnit('deg'),
	'--high-hue': rawUnit('deg'),
	'--prim-saturation': rawUnit('%'),
	'--low-saturation': rawUnit('%'),
	'--high-saturation': rawUnit('%'),
	'--min-contrast': rawUnit('%'),
	'--max-contrast': rawUnit('%'),
	'font-size': rawUnit('%'),
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
		var prop = this.propNames[p];
		stl = stl + " " + prop+': '+this.propUnits[prop](this.props[prop]) + ";"
	    }
	    e.setAttribute('style', stl);

	    var spans = e.getElementsByClassName('theme-prop-display');
	    for (var spanI in spans) {
		var span = spans.item(spanI);
		if(span !== null) {
		    var prop = span.getAttribute('data-prop-name');
		    span.textContent = this.propUnits[prop](this.props[prop]);
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
		    tw.setProp(e,prop,this.value);
		});
	    })(this,elt,elt.getElementsByTagName('input')[0]);
	}
    }
};

if(Theme.props === null) {
    Theme.props = {
	'light': true,
	'--prim-hue': 53, '--prim-saturation': 36,
	'--low-hue': -50, '--low-saturation': 30,
	'--high-hue': 50, '--high-saturation': 30,
	'--min-contrast': 50, '--max-contrast': 85,
	'--luminosity': 50,
	'font-size': 100
    };
}

