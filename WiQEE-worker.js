window = self;
importScripts('WiQEE.js');

CaPriCon = {
    'states': [],
    'initFS': function (ev) {
	// console.log('Initializing DB schema');
	var db = ev.currentTarget.result;
	db.createObjectStore('filesystem', { keyPath: 'filePath' });
    },
    'newFS': function(ini,db,onsuc,onerr) {
	// console.log('newFS: '+db);
	var req = window.indexedDB.open(db,3);
	req.onupgradeneeded = ini;
	req.onsuccess = function (ev) {
	    // console.log('database opened: '+ev.target.result);
	    return onsuc(ev.target.result);
	};
	req.onerror = onerr;
    },
    'getFSItem': function (fs,file,onSuc,onErr) {
	// console.log('getFSItem: '+fs);
	var req = fs.transaction(['filesystem']).objectStore('filesystem').get(file);
	req.onerror = onErr;
	req.onsuccess = function(ev) {
	    if(ev.target.result !== undefined) {
		console.log('Success getting '+file+" ( ev.target = " + ev.target + ")");
		onSuc(ev.target.result.fileData);
	    } else {
		onErr(ev);
	    }
	};
    },
    'setFSItem': function (fs,file,dat,onSuc,onErr) {
	// console.log('setFSItem: '+fs+' '+dat);
	var req = fs.transaction(['filesystem'],"readwrite")
	    .objectStore('filesystem')
	    .add({ 'filePath': file, 'fileData': dat });
	req.onerror = function (e) {
	    // console.log('Error loading '+file+": "+e);
	    onErr(e);
	};
	req.onsuccess = onSuc;
    },
    'ajaxGetString': function (url,onSuc,onErr) {
	var xhttp = new XMLHttpRequest();
	xhttp.responseType = "text";
	xhttp.onreadystatechange = function() {
	    if(xhttp.readyState == 4) {
		if (xhttp.status === 200 || xhttp.status === 304) {
		    onSuc(xhttp.responseText);
		}
		else {
		    onErr([xhttp.status,xhttp.statusText]);
		}
	    }
	};
	// console.log('getting URL:' + url);
	xhttp.open("GET", url, true);
	xhttp.send();
    }
};

onmessage = function(e) {
    // console.log('onmessage: '+e.data);
    CaPriCon.event = e;
    hasteMain();
};
