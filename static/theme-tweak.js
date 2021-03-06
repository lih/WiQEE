function rawUnit(u) { return function (x) { return x.toString() + u; }; }

var ThemeConfig = {
    defaultAmbiance: 'day',
    defaultProps: {
	'day': {
	    'light': true,
	    '--prim-hue': 53, '--prim-saturation': 36,
	    '--low-hue': -50, '--low-saturation': 30,
	    '--high-hue': 50, '--high-saturation': 30,
	    '--min-contrast': 50, '--max-contrast': 85,
	    '--luminosity': 50,
	    'font-size': 100
	},
	
	'night': {
	    'light': false,
	    '--prim-hue': 53, '--prim-saturation': 36,
	    '--low-hue': -50, '--low-saturation': 30,
	    '--high-hue': 50, '--high-saturation': 30,
	    '--min-contrast': 30, '--max-contrast': 65,
	    '--luminosity': 30,
	    'font-size': 100
	}
    },
    propUnits: {
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

    propNames: ['--prim-hue','--prim-saturation',
		'--low-hue','--low-saturation',
		'--high-hue','--high-saturation',
		'--min-contrast', '--max-contrast',
		'--luminosity',
		'font-size']
};

function setLightGround(e,isLight) {
    if(isLight) {
	e.classList.replace('ground-dark', 'ground-light');
    }
    else {
	e.classList.replace('ground-light', 'ground-dark');
    }
}

var Theme = {
    roots: [],
    sliders: [],
    config: ThemeConfig,
    props: JSON.parse(window.localStorage.getItem('theme/'+window.location.pathname)) || ThemeConfig.defaultProps,
    ambiance: window.localStorage.getItem('theme-ambiance') || ThemeConfig.defaultAmbiance,
    
    attach: function (root) {
	this.roots.push(root);
	var rootI = this.roots.length - 1;

	setLightGround(root,this.getPropVal('light'));
	this.updateElement(rootI);

	{
	    var amb = root.getElementsByClassName('theme-ambiance-select')[0];
	    var tw = this;
	    amb.value = tw.ambiance;
	    amb.addEventListener('change', function() {
		tw.setAmbiance(amb.value).updateAll();
	    });
	};
	
	var elts = root.getElementsByClassName('theme-slider');
	for(var x in elts) {
	    var elt = elts.item(x);
	    (function (tw,elt,slide) {
		var th_val = elt.getElementsByClassName('theme-prop-display')[0];
		var prop = th_val.getAttribute('data-prop-name');
		tw.sliders.push({ slide: slide, prop: prop });
		slide.value = tw.getPropVal(prop);
		slide.addEventListener('input',function () {
		    tw.setProp(prop,this.value).updateElement(null);
		});
	    })(this,elt,elt.getElementsByTagName('input')[0]);
	}

	return rootI;
    },
    getPropVal: function(p) {
	return this.props[this.ambiance][p];
    },
    getPropText: function(p) {
	return this.config.propUnits[p](this.getPropVal(p));
    },
    setProp: function (p,v) {
	this.props[this.ambiance][p] = v;
	window.localStorage.setItem('theme/'+window.location.pathname, JSON.stringify(this.props));
	return this;
    },
    setAmbiance: function(ambiance) {
	this.ambiance = ambiance;
	window.localStorage.setItem('theme-ambiance', this.ambiance);
	return this;
    },
    getStyleText: function() {
	var stl = "", p;
	for(var p in this.config.propNames) {
	    var prop = this.config.propNames[p];
	    stl = stl + " " + prop+': '+this.getPropText(prop) + ";"
	}
	return stl;
    },
    updateElement: function (i) {
	if(i === null) {
	    for(var j=0; j<this.roots.length; j++)
		this.updateElement(j);
	    return;
	}
	var elt = this.roots[i];
	elt.setAttribute('style', this.getStyleText());
	setLightGround(elt,this.getPropVal('light'));
	
	var spans = elt.getElementsByClassName('theme-prop-display');
	for (var spanI in spans) {
	    var span = spans.item(spanI);
	    if(span !== null) {
		var prop = span.getAttribute('data-prop-name');
		span.textContent = this.getPropText(prop);
	    }
	}
    },
    updateSlider: function(i) {
	if(i === null) {
	    for(var j=0; j<this.sliders.length; j++)
		this.updateSlider(j);
	    return;
	}
	var x = this.sliders[i];
	x.slide.value = this.getPropVal(x.prop);
    },
    updateAll: function() {
	this.updateElement(null);
	this.updateSlider(null);
    }
};


