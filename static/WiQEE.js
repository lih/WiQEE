function escapeHtml(str) {
    var div = document.createElement('div');
    div.appendChild(document.createTextNode(str));
    return div.innerHTML;
}
function cons_html() {
    var syms = arguments[0];
    var ret = "";
    for (var i=1;i < arguments.length; i++) {
	ret += ((syms[i-1] !== undefined) ? syms[i-1] : "") + escapeHtml(arguments[i]);
    }
    ret += syms[i-1];
    var p = new DOMParser();
      return p.parseFromString(ret,'application/xhtml+xml').documentElement;
}

function foldrM(stIni,l,f) {
    var rec = function(i) {
	return function(st) {
	    if(i<l.length) {
		f(st,l[i],rec(i+1));
	    }
	};
    };
    rec(0)(stIni);
}

window.addEventListener('load',function () {
    "use strict";
    
    var wloc = window.location.pathname.substring(0, window.location.pathname.lastIndexOf('/'));
    window.console.log('window location: ' + wloc);
    var capriconWorker = new Worker(wloc + '/capricon-worker.js');

    var workerCallbacks = [];
    capriconWorker.onmessage = function (e) {
	var callback = workerCallbacks[e.data[0]];
	callback(e.data[1]);
    };
    
    var runCaPriCon = function(state,code,then) {
	var nextCallback = workerCallbacks.length;
	workerCallbacks.push(then);
	capriconWorker.postMessage([0,nextCallback,state,code]);
    };
    var evalCaPriCon = function(state,code,then) {
	var nextCallback = workerCallbacks.length;
	workerCallbacks.push(then);
	capriconWorker.postMessage([1,nextCallback,state,code]);
    };
    var execCaPriCon = function(state,code,then) {
	var nextCallback = workerCallbacks.length;
	workerCallbacks.push(then);
	capriconWorker.postMessage([2,nextCallback,state,code]);
    };
    
    var prel = document.getElementById('capricon-prelude').textContent;
    var roots = Array.prototype.slice.call(document.getElementsByClassName('capricon-steps'));
    var console = document.getElementById('capricon-console');

    runCaPriCon(0,prel,function (stIni) {
	foldrM(stIni,roots,function (st,root,cont) {
	    if(root.tagName == 'CODE') {
		runCaPriCon(st,root.textContent + " mustache.",cont);
	    }
	    else {
		var mainInput = root.getElementsByClassName('capricon-input')[0];
		mainInput.classList.add('pending');

		var consoleRoot = root.cloneNode(true);
		var consoleBar = document.createElement('div');
		var consoleTitle = document.createElement('h4');
		var consoleClose = document.createElement('button');
		var consoleInput = consoleRoot.getElementsByClassName('capricon-input')[0];
		var consoleOutput = consoleRoot.getElementsByClassName('capricon-output')[0];
		
		var mainExamples = root.getElementsByClassName('capricon-example');

		consoleClose.textContent = "Close";
		consoleClose.addEventListener('click', function() {
		    consoleRoot.classList.remove('active');
		    mainInput.value = consoleInput.value;
		});
		consoleClose.classList.add('right');
		
		consoleTitle.textContent = "CaPriCon Console";
		consoleTitle.classList.add('left');
		
		consoleBar.appendChild(consoleTitle);
		consoleBar.appendChild(consoleClose);
		consoleBar.classList.add('header');

		consoleRoot.insertBefore(consoleBar,consoleRoot.firstChild);
		console.appendChild(consoleRoot);

		var text = root.getElementsByClassName('capricon')[0].textContent;
		runCaPriCon(st,text,function(st0) {
		    var mainTrigger = root.getElementsByClassName('capricon-trigger')[0];
		    var runConsole = function () {
			consoleRoot.classList.add('active');
			consoleInput.value = mainInput.value;
			evalCaPriCon(st0,consoleInput.value,function(ret) { consoleOutput.textContent = ret; });
			consoleInput.focus();
		    };
		    
		    for(var j = 0; j < mainExamples.length; j++) {
			(function () {
			    var example = mainExamples[j];
			    example.addEventListener('click', function (ev) {
				mainInput.value = example.getAttribute('data-code');
				runConsole();
			    });
			})();
		    }
		    
		    mainInput.classList.add('ready'); mainInput.classList.remove('pending');
		    mainTrigger.addEventListener('click', function (ev) { runConsole(); });

		    consoleInput.addEventListener('keypress', function (ev) {
			if(ev.keyCode == 13) { // Press Enter
			    evalCaPriCon(st0,consoleInput.value,function(ret) { consoleOutput.textContent = ret; });
			}
		    });
		    
		    mainInput.addEventListener('keypress', function (ev) {
			if(ev.keyCode == 13) { // Press Enter
			    consoleRoot.classList.add('active');
			    consoleInput.value = mainInput.value;
			    evalCaPriCon(st0,mainInput.value,function(ret) { consoleOutput.textContent = ret; });
			    consoleInput.focus();
			}
		    });

		    cont(st0);
		});
	    }
	    
	});
    });
});
