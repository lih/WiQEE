"use strict";
var __haste_prog_id = 'c8343a54b77c845114220eaf04f1d83c0675ef93b56b0e7f8385b747926bb895';
var __haste_script_elem = typeof document == 'object' ? document.currentScript : null;
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined' && typeof global !== 'undefined') window = global;
window['__haste_crypto'] = window.crypto || window.msCrypto;
if(window['__haste_crypto'] && !window['__haste_crypto'].subtle && window.crypto.webkitSubtle) {
    window['__haste_crypto'].subtle = window.crypto.webkitSubtle;
}

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(738919189, 2683596561, true)
  var y = new Long(3648966346, 573393410, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var len = buffer.byteLength;
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': len % 2 ? null : new Int16Array(buffer)
        , 'i32': len % 4 ? null : new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': len % 2 ? null : new Uint16Array(buffer)
        , 'w32': len % 4 ? null : new Uint32Array(buffer)
        , 'f32': len % 4 ? null : new Float32Array(buffer)
        , 'f64': len % 8 ? null : new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __isUndef = function(x) {return typeof x == 'undefined';}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

/* Code for creating and querying the static pointer table. */
window.__hs_spt = [];

function __spt_insert(ptr) {
    ptr = E(B(ptr));
    var ks = [ (ptr.a.a.low>>>0).toString(16)
             , (ptr.a.a.high>>>0).toString(16)
             , (ptr.a.b.low>>>0).toString(16)
             , (ptr.a.b.high>>>0).toString(16)
             ]
    var key = ks.join();
    window.__hs_spt[key] = ptr;
}

function hs_spt_lookup(k) {
    var ks = [ k['v']['w32'][0].toString(16)
             , k['v']['w32'][1].toString(16)
             , k['v']['w32'][2].toString(16)
             , k['v']['w32'][3].toString(16)
             ]
    var key = ks.join();
    return window.__hs_spt[key];
}

var _0=function(_1,_2){var _3=E(_1);return (_3._==0)?E(_2):new T2(1,_3.a,new T(function(){return _0(_3.b,_2);}));},_4=function(_5,_){while(1){var _6=E(_5);if(!_6._){return 0;}else{var _7=_6.b,_8=E(_6.a);switch(_8._){case 0:var _9=B(A1(_8.a,_));_5=_0(_7,new T2(1,_9,__Z));continue;case 1:_5=_0(_7,_8.a);continue;default:_5=_7;continue;}}}},_a=function(_b,_c,_){var _d=E(_b);switch(_d._){case 0:var _e=B(A1(_d.a,_));return _4(_0(_c,new T2(1,_e,__Z)),_);case 1:return _4(_0(_c,_d.a),_);default:return _4(_c,_);}},_f=function(_g,_){var _h=E(_g);if(!_h._){return __Z;}else{var _i=_f(_h.b,_);return new T2(1,_h.a,_i);}},_j=function(_k){return E(E(_k).a);},_l=function(_m){return E(E(_m).d);},_n=function(_o){return E(_o);},_p=new T2(0,_n,function(_q,_r){return C > 19 ? new F(function(){return A2(_l,_j(_q),new T1(1,_r));}) : (++C,A2(_l,_j(_q),new T1(1,_r)));}),_s=function(_t,_u,_){var _v=B(A1(_t,_)),_w=B(A1(_u,_));return new T(function(){return B(A1(_v,_w));});},_x=function(_y,_z,_){var _A=B(A1(_z,_));return new T(function(){return B(A1(_y,_A));});},_B=function(_C,_){return _C;},_D=function(_E,_F,_){var _G=B(A1(_E,_));return C > 19 ? new F(function(){return A1(_F,_);}) : (++C,A1(_F,_));},_H=new T(function(){return unCStr("base");}),_I=new T(function(){return unCStr("GHC.IO.Exception");}),_J=new T(function(){return unCStr("IOException");}),_K=function(_L){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_H,_I,_J),__Z,__Z));},_M=function(_N){return E(E(_N).a);},_O=function(_P,_Q,_R){var _S=B(A1(_P,_)),_T=B(A1(_Q,_)),_U=hs_eqWord64(_S.a,_T.a);if(!_U){return __Z;}else{var _V=hs_eqWord64(_S.b,_T.b);return (!_V)?__Z:new T1(1,_R);}},_W=new T(function(){return unCStr(": ");}),_X=new T(function(){return unCStr(")");}),_Y=new T(function(){return unCStr(" (");}),_Z=new T(function(){return unCStr("interrupted");}),_10=new T(function(){return unCStr("system error");}),_11=new T(function(){return unCStr("unsatisified constraints");}),_12=new T(function(){return unCStr("user error");}),_13=new T(function(){return unCStr("permission denied");}),_14=new T(function(){return unCStr("illegal operation");}),_15=new T(function(){return unCStr("end of file");}),_16=new T(function(){return unCStr("resource exhausted");}),_17=new T(function(){return unCStr("resource busy");}),_18=new T(function(){return unCStr("does not exist");}),_19=new T(function(){return unCStr("already exists");}),_1a=new T(function(){return unCStr("resource vanished");}),_1b=new T(function(){return unCStr("timeout");}),_1c=new T(function(){return unCStr("unsupported operation");}),_1d=new T(function(){return unCStr("hardware fault");}),_1e=new T(function(){return unCStr("inappropriate type");}),_1f=new T(function(){return unCStr("invalid argument");}),_1g=new T(function(){return unCStr("failed");}),_1h=new T(function(){return unCStr("protocol error");}),_1i=function(_1j,_1k){switch(E(_1j)){case 0:return _0(_19,_1k);case 1:return _0(_18,_1k);case 2:return _0(_17,_1k);case 3:return _0(_16,_1k);case 4:return _0(_15,_1k);case 5:return _0(_14,_1k);case 6:return _0(_13,_1k);case 7:return _0(_12,_1k);case 8:return _0(_11,_1k);case 9:return _0(_10,_1k);case 10:return _0(_1h,_1k);case 11:return _0(_1g,_1k);case 12:return _0(_1f,_1k);case 13:return _0(_1e,_1k);case 14:return _0(_1d,_1k);case 15:return _0(_1c,_1k);case 16:return _0(_1b,_1k);case 17:return _0(_1a,_1k);default:return _0(_Z,_1k);}},_1l=new T(function(){return unCStr("}");}),_1m=new T(function(){return unCStr("{handle: ");}),_1n=function(_1o,_1p,_1q,_1r,_1s,_1t){var _1u=new T(function(){var _1v=new T(function(){var _1w=new T(function(){var _1x=E(_1r);if(!_1x._){return E(_1t);}else{var _1y=new T(function(){return _0(_1x,new T(function(){return _0(_X,_1t);},1));},1);return _0(_Y,_1y);}},1);return _1i(_1p,_1w);}),_1z=E(_1q);if(!_1z._){return E(_1v);}else{return _0(_1z,new T(function(){return _0(_W,_1v);},1));}}),_1A=E(_1s);if(!_1A._){var _1B=E(_1o);if(!_1B._){return E(_1u);}else{var _1C=E(_1B.a);if(!_1C._){var _1D=new T(function(){var _1E=new T(function(){return _0(_1l,new T(function(){return _0(_W,_1u);},1));},1);return _0(_1C.a,_1E);},1);return _0(_1m,_1D);}else{var _1F=new T(function(){var _1G=new T(function(){return _0(_1l,new T(function(){return _0(_W,_1u);},1));},1);return _0(_1C.a,_1G);},1);return _0(_1m,_1F);}}}else{return _0(_1A.a,new T(function(){return _0(_W,_1u);},1));}},_1H=function(_1I){var _1J=E(_1I);return _1n(_1J.a,_1J.b,_1J.c,_1J.d,_1J.f,__Z);},_1K=function(_1L){return new T2(0,_1M,_1L);},_1N=function(_1O,_1P){var _1Q=E(_1O);return _1n(_1Q.a,_1Q.b,_1Q.c,_1Q.d,_1Q.f,_1P);},_1R=function(_1S,_1T,_1U){var _1V=E(_1T);if(!_1V._){return unAppCStr("[]",_1U);}else{var _1W=new T(function(){var _1X=new T(function(){var _1Y=function(_1Z){var _20=E(_1Z);if(!_20._){return E(new T2(1,93,_1U));}else{var _21=new T(function(){return B(A2(_1S,_20.a,new T(function(){return _1Y(_20.b);})));});return new T2(1,44,_21);}};return _1Y(_1V.b);});return B(A2(_1S,_1V.a,_1X));});return new T2(1,91,_1W);}},_1M=new T(function(){return new T5(0,_K,new T3(0,function(_22,_23,_24){var _25=E(_23);return _1n(_25.a,_25.b,_25.c,_25.d,_25.f,_24);},_1H,function(_26,_27){return _1R(_1N,_26,_27);}),_1K,function(_28){var _29=E(_28);return _O(_M(_29.a),_K,_29.b);},_1H);}),_2a=new T(function(){return E(_1M);}),_2b=function(_2c){return E(E(_2c).c);},_2d=function(_2e){return new T6(0,__Z,7,__Z,_2e,__Z,__Z);},_2f=function(_2g,_){var _2h=new T(function(){return B(A2(_2b,_2a,new T(function(){return B(A1(_2d,_2g));})));});return die(_2h);},_2i=function(_2j,_){return _2f(_2j,_);},_2k=function(_2l,_2m,_){var _2n=B(A1(_2l,_));return C > 19 ? new F(function(){return A2(_2m,_2n,_);}) : (++C,A2(_2m,_2n,_));},_2o=new T2(0,new T5(0,new T5(0,new T2(0,_x,function(_2p,_2q,_){var _2r=B(A1(_2q,_));return _2p;}),_B,_s,_D,function(_2s,_2t,_){var _2u=B(A1(_2s,_)),_2v=B(A1(_2t,_));return _2u;}),_2k,_D,_B,function(_2w){return C > 19 ? new F(function(){return A1(_2i,_2w);}) : (++C,A1(_2i,_2w));}),_n),_2x=function(_2y){return E(E(_2y).a);},_2z=function(_2A){return E(E(_2A).b);},_2B=function(_2C,_2D){var _2E=E(_2D);if(!_2E._){return _2z(_2C);}else{return C > 19 ? new F(function(){return A3(_2x,_2C,_2E.a,new T(function(){return B(_2B(_2C,_2E.b));}));}) : (++C,A3(_2x,_2C,_2E.a,new T(function(){return B(_2B(_2C,_2E.b));})));}},_2F=new T3(0,new T2(0,_B,new T2(0,_x,function(_2G,_2H,_){var _2I=B(A1(_2G,_));return _x(_2I,_2H,_);})),function(_2J,_){var _2K=B(A1(_2J,_));return C > 19 ? new F(function(){return A1(_2K,_);}) : (++C,A1(_2K,_));},_2k),_2L=new T(function(){return err(new T(function(){return unCStr("Prelude.undefined");}));}),_2M=new T2(0,function(_2N,_2O){return E(_2L);},_2L),_2P=function(_2Q){return E(E(_2Q).a);},_2R=function(_2S){return E(E(_2S).a);},_2T=function(_2U){return E(E(_2U).b);},_2V=function(_2W){return E(E(_2W).a);},_2X=function(_2Y){return E(E(_2Y).c);},_2Z=function(_30,_31,_32,_33){var _34=new T(function(){return E(E(_33).a);}),_35=new T(function(){return _2V(new T(function(){return _2P(_31);}));}),_36=new T(function(){return _2x(_30);}),_37=function(_38){var _39=new T(function(){return E(E(_38).c);}),_3a=function(_3b){var _3c=new T(function(){return B(A2(_36,_39,new T(function(){return E(E(_3b).c);})));});return C > 19 ? new F(function(){return A1(_35,new T3(0,new T(function(){return E(E(_3b).a);}),new T(function(){return E(E(_3b).b);}),_3c));}) : (++C,A1(_35,new T3(0,new T(function(){return E(E(_3b).a);}),new T(function(){return E(E(_3b).b);}),_3c)));};return C > 19 ? new F(function(){return A3(_2X,_31,new T(function(){var _3d=E(_38);return B(A1(_3d.a,new T2(0,_34,_3d.b)));}),_3a);}) : (++C,A3(_2X,_31,new T(function(){var _3d=E(_38);return B(A1(_3d.a,new T2(0,_34,_3d.b)));}),_3a));},_3e=new T(function(){return B(A1(_32,new T2(0,_34,new T(function(){return E(E(_33).b);}))));});return C > 19 ? new F(function(){return A3(_2X,_31,_3e,_37);}) : (++C,A3(_2X,_31,_3e,_37));},_3f=function(_3g,_3h,_3i){var _3j=new T(function(){var _3k=_2R(_2T(_2P(_3g))),_3l=function(_3m){var _3n=new T(function(){var _3o=function(_3p){var _3q=new T(function(){return B(A1(E(_3m).a,new T(function(){return E(E(_3p).a);})));});return new T3(0,_3q,new T(function(){return E(E(_3p).b);}),new T(function(){return E(E(_3p).c);}));};return B(A1(_3k,_3o));}),_3r=function(_3s){return C > 19 ? new F(function(){return A1(_3n,new T(function(){return B(A1(_3i,_3s));}));}) : (++C,A1(_3n,new T(function(){return B(A1(_3i,_3s));})));};return new T3(0,_3r,new T(function(){return E(E(_3m).b);}),new T(function(){return E(E(_3m).c);}));};return B(A1(_3k,_3l));}),_3t=function(_3u){return C > 19 ? new F(function(){return A1(_3j,new T(function(){return B(A1(_3h,_3u));}));}) : (++C,A1(_3j,new T(function(){return B(A1(_3h,_3u));})));};return function(_3v){return C > 19 ? new F(function(){return _2Z(_2M,_3g,_3t,_3v);}) : (++C,_2Z(_2M,_3g,_3t,_3v));};},_3w=function(_3x,_3y,_3z,_3A){var _3B=new T(function(){return B(A1(_3z,new T(function(){return B(A1(_3x,_3A));})));});return C > 19 ? new F(function(){return A1(_3y,_3B);}) : (++C,A1(_3y,_3B));},_3C=function(_3D,_3E){return E(_3E);},_3F=function(_3G){return E(_3G);},_3H=function(_3I,_3J,_3K){return C > 19 ? new F(function(){return A1(_3I,new T(function(){return B(A1(_3J,_3K));}));}) : (++C,A1(_3I,new T(function(){return B(A1(_3J,_3K));})));},_3L=function(_3M){return E(_3M);},_3N=function(_3O){return E(_3O);},_3P=function(_3Q){return E(_3Q);},_3R=function(_3S){return new T2(0,_2L,_3S);},_3T=function(_3U,_3V){return C > 19 ? new F(function(){return A1(_3U,new T(function(){return _3R(_3V);}));}) : (++C,A1(_3U,new T(function(){return _3R(_3V);})));},_3W=function(_3X){return E(E(_3X).b);},_3Y=function(_3Z,_40){return C > 19 ? new F(function(){return A1(_3Z,new T(function(){return _3W(_40);}));}) : (++C,A1(_3Z,new T(function(){return _3W(_40);})));},_41=function(_42){var _43=E(_42);return new T2(0,_43.b,_43.a);},_44=function(_45){return new T3(0,new T(function(){return E(E(_45).b);}),new T(function(){return E(E(_45).a);}),_2L);},_46=function(_47){return E(_47);},_48=function(_49,_4a,_4b,_4c){var _4d=new T(function(){var _4e=new T(function(){var _4f=new T(function(){return B(A1(_4a,_41));}),_4g=function(_4h){return C > 19 ? new F(function(){return A1(_4f,_4h);}) : (++C,A1(_4f,_4h));};return B(A1(_4b,function(_4i,_4j){return C > 19 ? new F(function(){return _3H(_4g,_4i,_4j);}) : (++C,_3H(_4g,_4i,_4j));}));}),_4k=new T(function(){return B(A1(_49,_44));}),_4l=function(_4m){return C > 19 ? new F(function(){return A1(_4k,_4m);}) : (++C,A1(_4k,_4m));};return B(A2(_4c,function(_4i,_4j){return C > 19 ? new F(function(){return _3H(_4l,_4i,_4j);}) : (++C,_3H(_4l,_4i,_4j));},_4e));}),_4n=new T(function(){return B(A2(_4c,_3Y,new T(function(){return B(A1(_4b,_3T));})));}),_4o=new T(function(){return B(A2(_4c,_3N,new T(function(){return B(A1(_4b,_3L));})));}),_4p=new T(function(){return B(A2(_4c,_3P,new T(function(){return B(A1(_4b,_46));})));}),_4q=function(_4r){var _4s=new T(function(){var _4t=new T(function(){return B(A1(_4o,new T(function(){return B(A1(_4p,_4r));})));});return B(A1(_4n,_4t));});return C > 19 ? new F(function(){return A1(_4d,_4s);}) : (++C,A1(_4d,_4s));};return _4q;},_4u=function(_4v,_4w){var _4x=new T(function(){return _2P(_4v);}),_4y=new T(function(){return _2R(new T(function(){return _2T(_4x);}));}),_4z=new T(function(){return _2V(_4x);}),_4A=function(_4B){var _4C=new T(function(){var _4D=B(A1(_4w,new T2(0,_2L,new T(function(){return E(E(_4B).e);}))));return new T2(0,_4D.a,_4D.b);}),_4E=new T(function(){var _4F=E(_4B);return new T5(0,_4F.a,_4F.b,_4F.c,_4F.d,new T(function(){return E(E(_4C).b);}));});return C > 19 ? new F(function(){return A1(_4z,new T2(0,_4E,new T(function(){return E(E(_4C).a);})));}) : (++C,A1(_4z,new T2(0,_4E,new T(function(){return E(E(_4C).a);}))));};return C > 19 ? new F(function(){return A(_48,[_4y,_4y,_3C,_3w,_3F,_4A]);}) : (++C,A(_48,[_4y,_4y,_3C,_3w,_3F,_4A]));},_4G=function(_4H,_4I){return new T3(0,_4H,new T(function(){return E(E(_4I).b);}),_2L);},_4J=function(_4K,_4L,_4M){var _4N=new T(function(){return B(A1(_4L,_4M));}),_4O=new T(function(){return B(A1(_4K,new T(function(){return E(E(_4N).a);})));});return new T3(0,_4O,new T(function(){return E(E(_4N).b);}),new T(function(){return E(E(_4N).c);}));},_4P=function(_4Q,_4R){return C > 19 ? new F(function(){return A1(_4Q,_4R);}) : (++C,A1(_4Q,_4R));},_4S=new T3(0,new T2(0,function(_4T){return E(_4T);},new T2(0,_4P,function(_4U,_4V){return C > 19 ? new F(function(){return A1(_4U,_4V);}) : (++C,A1(_4U,_4V));})),function(_4W){return E(_4W);},function(_4X,_4Y){return C > 19 ? new F(function(){return A1(_4Y,_4X);}) : (++C,A1(_4Y,_4X));}),_4Z=function(_50,_51,_52){return C > 19 ? new F(function(){return _2Z(_2M,_4S,function(_53){return _4J(_51,_50,_53);},_52);}) : (++C,_2Z(_2M,_4S,function(_53){return _4J(_51,_50,_53);},_52));},_54=function(_55){var _56=new T(function(){return E(E(_55).b);});return new T3(0,_56,_56,_2L);},_57=function(_58,_59){var _5a=new T(function(){return B(A1(_58,new T(function(){return E(E(_59).b);})));});return new T3(0,0,_5a,_2L);},_5b=function(_5c){return E(E(_5c).a);},_5d=function(_5e){return E(E(_5e).b);},_5f=function(_5g,_5h){var _5i=new T(function(){return B(A2(_5h,_3C,_3F));});return C > 19 ? new F(function(){return A3(_2R,_2T(_2P(_5b(_5g))),function(_5j){return C > 19 ? new F(function(){return A1(_5i,_5j);}) : (++C,A1(_5i,_5j));},new T(function(){return _5d(_5g);}));}) : (++C,A3(_2R,_2T(_2P(_5b(_5g))),function(_5j){return C > 19 ? new F(function(){return A1(_5i,_5j);}) : (++C,A1(_5i,_5j));},new T(function(){return _5d(_5g);})));},_5k=function(_5l){return E(E(_5l).d);},_5m=function(_5n,_5o,_5p){var _5q=_5b(_5n),_5r=new T(function(){return _2R(new T(function(){return _2T(new T(function(){return _2P(_5q);}));}));}),_5s=function(_5t){var _5u=new T(function(){return B(A1(_5p,_5t));}),_5v=new T(function(){return E(E(_5u).b);}),_5w=new T(function(){var _5x=new T(function(){var _5y=new T(function(){return E(E(_5u).a);});return B(A2(_5o,_4P,function(_5z){return E(_5y);}));});return B(A2(_5k,_5n,function(_5A){return C > 19 ? new F(function(){return A1(_5x,_5A);}) : (++C,A1(_5x,_5A));}));});return C > 19 ? new F(function(){return A2(_5r,function(_5B){return E(_5v);},_5w);}) : (++C,A2(_5r,function(_5B){return E(_5v);},_5w));};return C > 19 ? new F(function(){return A3(_2X,_5q,new T(function(){return B(_5f(_5n,_5o));}),_5s);}) : (++C,A3(_2X,_5q,new T(function(){return B(_5f(_5n,_5o));}),_5s));},_5C=function(_5D,_5E,_5F){var _5G=new T(function(){return B(A1(_5E,new T(function(){return E(E(_5F).d);})));});return C > 19 ? new F(function(){return A2(_5D,function(_5H){var _5I=E(_5F);return new T4(0,_5I.a,_5I.b,_5I.c,_5H);},_5G);}) : (++C,A2(_5D,function(_5H){var _5I=E(_5F);return new T4(0,_5I.a,_5I.b,_5I.c,_5H);},_5G));},_5J=new T(function(){return B(_4u(_2F,new T(function(){return B(_5m(new T4(0,new T3(0,new T2(0,_4G,new T2(0,_4J,function(_5K,_5L){return _3f(_4S,_5K,_5L);})),function(_5M,_5N){return C > 19 ? new F(function(){return _2Z(_2M,_4S,_5M,_5N);}) : (++C,_2Z(_2M,_4S,_5M,_5N));},_4Z),_54,function(_5O,_5P){return new T3(0,0,_5O,_2L);},_57),_5C,function(_5Q){return new T2(0,_n,_5Q);}));})));}),_5R=function(_5S,_){var _5T=B(A2(_5J,_5S,_)),_5U=new T(function(){return B(A1(E(_5T).a,__Z));}),_5V=function(_5W,_){return new T3(0,_5U,new T(function(){return E(E(_5W).b);}),_2L);};return new T3(0,_5V,new T(function(){return E(E(_5T).b);}),new T(function(){return E(E(_5T).c);}));},_5X=function(_5Y){return C > 19 ? new F(function(){return _2Z(_2M,_2F,_5R,_5Y);}) : (++C,_2Z(_2M,_2F,_5R,_5Y));},_5Z=function(_60,_61){return new T2(0,_60,new T(function(){return _2z(_61);}));},_62=function(_63,_64,_65){return C > 19 ? new F(function(){return A1(_63,new T(function(){return B(A1(_64,_65));}));}) : (++C,A1(_63,new T(function(){return B(A1(_64,_65));})));},_66=new T2(0,_3H,_n),_67=function(_68){return E(E(_68).b);},_69=function(_6a,_6b){return new T2(0,_6a,new T(function(){return _67(_6b);}));},_6c=function(_6d,_6e,_6f){return C > 19 ? new F(function(){return A1(_6e,new T(function(){return B(A1(_6d,_6f));}));}) : (++C,A1(_6e,new T(function(){return B(A1(_6d,_6f));})));},_6g=new T(function(){return _69(_6c,_66);}),_6h=new T(function(){return _5Z(_62,_6g);}),_6i=function(_6j,_6k,_){return new T3(0,0,new T(function(){return E(E(_6k).b);}),_2L);},_6l=function(_6m,_6n){while(1){var _6o=E(_6m);if(!_6o._){return (E(_6n)._==0)?true:false;}else{var _6p=E(_6n);if(!_6p._){return false;}else{if(E(_6o.a)!=E(_6p.a)){return false;}else{_6m=_6o.b;_6n=_6p.b;continue;}}}}},_6q=new T2(0,_6l,function(_6r,_6s){return (!_6l(_6r,_6s))?true:false;}),_6t=function(_6u,_6v){while(1){var _6w=E(_6u);if(!_6w._){return (E(_6v)._==0)?1:0;}else{var _6x=E(_6v);if(!_6x._){return 2;}else{var _6y=E(_6w.a),_6z=E(_6x.a);if(_6y!=_6z){return (_6y>_6z)?2:0;}else{_6u=_6w.b;_6v=_6x.b;continue;}}}}},_6A={_:0,a:_6q,b:_6t,c:function(_6B,_6C){return (_6t(_6B,_6C)==0)?true:false;},d:function(_6D,_6E){return (_6t(_6D,_6E)==2)?false:true;},e:function(_6F,_6G){return (_6t(_6F,_6G)==2)?true:false;},f:function(_6H,_6I){return (_6t(_6H,_6I)==0)?false:true;},g:function(_6J,_6K){return (_6t(_6J,_6K)==2)?E(_6J):E(_6K);},h:function(_6L,_6M){return (_6t(_6L,_6M)==2)?E(_6M):E(_6L);}},_6N=new T(function(){return unCStr("base");}),_6O=new T(function(){return unCStr("Control.Exception.Base");}),_6P=new T(function(){return unCStr("PatternMatchFail");}),_6Q=function(_6R){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_6N,_6O,_6P),__Z,__Z));},_6S=function(_6T){return E(E(_6T).a);},_6U=function(_6V,_6W){return _0(E(_6V).a,_6W);},_6X=new T(function(){return new T5(0,_6Q,new T3(0,function(_6Y,_6Z,_70){return _0(E(_6Z).a,_70);},_6S,function(_71,_72){return _1R(_6U,_71,_72);}),function(_73){return new T2(0,_6X,_73);},function(_74){var _75=E(_74);return _O(_M(_75.a),_6Q,_75.b);},_6S);}),_76=new T(function(){return unCStr("Non-exhaustive patterns in");}),_77=function(_78,_79){return die(new T(function(){return B(A2(_2b,_79,_78));}));},_7a=function(_7b,_7c){return _77(_7b,_7c);},_7d=function(_7e,_7f){var _7g=E(_7f);if(!_7g._){return new T2(0,__Z,__Z);}else{var _7h=_7g.a;if(!B(A1(_7e,_7h))){return new T2(0,__Z,_7g);}else{var _7i=new T(function(){var _7j=_7d(_7e,_7g.b);return new T2(0,_7j.a,_7j.b);});return new T2(0,new T2(1,_7h,new T(function(){return E(E(_7i).a);})),new T(function(){return E(E(_7i).b);}));}}},_7k=new T(function(){return unCStr("\n");}),_7l=function(_7m){return (E(_7m)==124)?false:true;},_7n=function(_7o,_7p){var _7q=_7d(_7l,unCStr(_7o)),_7r=_7q.a,_7s=function(_7t,_7u){var _7v=new T(function(){var _7w=new T(function(){return _0(_7p,new T(function(){return _0(_7u,_7k);},1));});return unAppCStr(": ",_7w);},1);return _0(_7t,_7v);},_7x=E(_7q.b);if(!_7x._){return _7s(_7r,__Z);}else{if(E(_7x.a)==124){return _7s(_7r,new T2(1,32,_7x.b));}else{return _7s(_7r,__Z);}}},_7y=function(_7z){return _7a(new T1(0,new T(function(){return _7n(_7z,_76);})),_6X);},_7A=new T(function(){return B(_7y("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_7B=function(_7C,_7D){while(1){var _7E=(function(_7F,_7G){var _7H=E(_7F);switch(_7H._){case 0:var _7I=E(_7G);if(!_7I._){return __Z;}else{_7C=B(A1(_7H.a,_7I.a));_7D=_7I.b;return __continue;}break;case 1:var _7J=B(A1(_7H.a,_7G)),_7K=_7G;_7C=_7J;_7D=_7K;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_7H.a,_7G),new T(function(){return _7B(_7H.b,_7G);}));default:return E(_7H.a);}})(_7C,_7D);if(_7E!=__continue){return _7E;}}},_7L=function(_7M,_7N){var _7O=function(_7P){var _7Q=E(_7N);if(_7Q._==3){return new T2(3,_7Q.a,new T(function(){return _7L(_7M,_7Q.b);}));}else{var _7R=E(_7M);if(_7R._==2){return _7Q;}else{if(_7Q._==2){return _7R;}else{var _7S=function(_7T){if(_7Q._==4){var _7U=function(_7V){return new T1(4,new T(function(){return _0(_7B(_7R,_7V),_7Q.a);}));};return new T1(1,_7U);}else{if(_7R._==1){var _7W=_7R.a;if(!_7Q._){return new T1(1,function(_7X){return _7L(B(A1(_7W,_7X)),_7Q);});}else{var _7Y=function(_7Z){return _7L(B(A1(_7W,_7Z)),new T(function(){return B(A1(_7Q.a,_7Z));}));};return new T1(1,_7Y);}}else{if(!_7Q._){return E(_7A);}else{var _80=function(_81){return _7L(_7R,new T(function(){return B(A1(_7Q.a,_81));}));};return new T1(1,_80);}}}};switch(_7R._){case 1:if(_7Q._==4){var _82=function(_83){return new T1(4,new T(function(){return _0(_7B(B(A1(_7R.a,_83)),_83),_7Q.a);}));};return new T1(1,_82);}else{return _7S(_);}break;case 4:var _84=_7R.a;switch(_7Q._){case 0:var _85=function(_86){var _87=new T(function(){return _0(_84,new T(function(){return _7B(_7Q,_86);},1));});return new T1(4,_87);};return new T1(1,_85);case 1:var _88=function(_89){var _8a=new T(function(){return _0(_84,new T(function(){return _7B(B(A1(_7Q.a,_89)),_89);},1));});return new T1(4,_8a);};return new T1(1,_88);default:return new T1(4,new T(function(){return _0(_84,_7Q.a);}));}break;default:return _7S(_);}}}}},_8b=E(_7M);switch(_8b._){case 0:var _8c=E(_7N);if(!_8c._){var _8d=function(_8e){return _7L(B(A1(_8b.a,_8e)),new T(function(){return B(A1(_8c.a,_8e));}));};return new T1(0,_8d);}else{return _7O(_);}break;case 3:return new T2(3,_8b.a,new T(function(){return _7L(_8b.b,_7N);}));default:return _7O(_);}},_8f=new T(function(){return unCStr("(");}),_8g=new T(function(){return unCStr(")");}),_8h=function(_8i,_8j){while(1){var _8k=E(_8i);if(!_8k._){return (E(_8j)._==0)?true:false;}else{var _8l=E(_8j);if(!_8l._){return false;}else{if(E(_8k.a)!=E(_8l.a)){return false;}else{_8i=_8k.b;_8j=_8l.b;continue;}}}}},_8m=function(_8n,_8o){return E(_8n)==E(_8o);},_8p=new T2(0,_8m,function(_8q,_8r){return E(_8q)!=E(_8r);}),_8s=function(_8t,_8u){var _8v=E(_8t);switch(_8v._){case 0:return new T1(0,function(_8w){return C > 19 ? new F(function(){return _8s(B(A1(_8v.a,_8w)),_8u);}) : (++C,_8s(B(A1(_8v.a,_8w)),_8u));});case 1:return new T1(1,function(_8x){return C > 19 ? new F(function(){return _8s(B(A1(_8v.a,_8x)),_8u);}) : (++C,_8s(B(A1(_8v.a,_8x)),_8u));});case 2:return new T0(2);case 3:return _7L(B(A1(_8u,_8v.a)),new T(function(){return B(_8s(_8v.b,_8u));}));default:var _8y=function(_8z){var _8A=E(_8z);if(!_8A._){return __Z;}else{var _8B=E(_8A.a);return _0(_7B(B(A1(_8u,_8B.a)),_8B.b),new T(function(){return _8y(_8A.b);},1));}},_8C=_8y(_8v.a);return (_8C._==0)?new T0(2):new T1(4,_8C);}},_8D=new T0(2),_8E=function(_8F){return new T2(3,_8F,_8D);},_8G=function(_8H,_8I){var _8J=E(_8H);if(!_8J){return C > 19 ? new F(function(){return A1(_8I,0);}) : (++C,A1(_8I,0));}else{var _8K=new T(function(){return B(_8G(_8J-1|0,_8I));});return new T1(0,function(_8L){return E(_8K);});}},_8M=function(_8N,_8O,_8P){var _8Q=new T(function(){return B(A1(_8N,_8E));}),_8R=function(_8S,_8T,_8U,_8V){while(1){var _8W=B((function(_8X,_8Y,_8Z,_90){var _91=E(_8X);switch(_91._){case 0:var _92=E(_8Y);if(!_92._){return C > 19 ? new F(function(){return A1(_8O,_90);}) : (++C,A1(_8O,_90));}else{var _93=_8Z+1|0,_94=_90;_8S=B(A1(_91.a,_92.a));_8T=_92.b;_8U=_93;_8V=_94;return __continue;}break;case 1:var _95=B(A1(_91.a,_8Y)),_96=_8Y,_93=_8Z,_94=_90;_8S=_95;_8T=_96;_8U=_93;_8V=_94;return __continue;case 2:return C > 19 ? new F(function(){return A1(_8O,_90);}) : (++C,A1(_8O,_90));break;case 3:var _97=new T(function(){return B(_8s(_91,_90));});return C > 19 ? new F(function(){return _8G(_8Z,function(_98){return E(_97);});}) : (++C,_8G(_8Z,function(_98){return E(_97);}));break;default:return C > 19 ? new F(function(){return _8s(_91,_90);}) : (++C,_8s(_91,_90));}})(_8S,_8T,_8U,_8V));if(_8W!=__continue){return _8W;}}};return function(_99){return _8R(_8Q,_99,0,_8P);};},_9a=function(_9b){return C > 19 ? new F(function(){return A1(_9b,__Z);}) : (++C,A1(_9b,__Z));},_9c=function(_9d,_9e){var _9f=function(_9g){var _9h=E(_9g);if(!_9h._){return _9a;}else{var _9i=_9h.a;if(!B(A1(_9d,_9i))){return _9a;}else{var _9j=new T(function(){return _9f(_9h.b);}),_9k=function(_9l){var _9m=new T(function(){return B(A1(_9j,function(_9n){return C > 19 ? new F(function(){return A1(_9l,new T2(1,_9i,_9n));}) : (++C,A1(_9l,new T2(1,_9i,_9n)));}));});return new T1(0,function(_9o){return E(_9m);});};return _9k;}}};return function(_9p){return C > 19 ? new F(function(){return A2(_9f,_9p,_9e);}) : (++C,A2(_9f,_9p,_9e));};},_9q=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_9r=function(_9s,_9t){var _9u=function(_9v,_9w){var _9x=E(_9v);if(!_9x._){var _9y=new T(function(){return B(A1(_9w,__Z));});return function(_9z){return C > 19 ? new F(function(){return A1(_9z,_9y);}) : (++C,A1(_9z,_9y));};}else{var _9A=E(_9x.a),_9B=function(_9C){var _9D=new T(function(){return _9u(_9x.b,function(_9E){return C > 19 ? new F(function(){return A1(_9w,new T2(1,_9C,_9E));}) : (++C,A1(_9w,new T2(1,_9C,_9E)));});}),_9F=function(_9G){var _9H=new T(function(){return B(A1(_9D,_9G));});return new T1(0,function(_9I){return E(_9H);});};return _9F;};switch(E(_9s)){case 8:if(48>_9A){var _9J=new T(function(){return B(A1(_9w,__Z));});return function(_9K){return C > 19 ? new F(function(){return A1(_9K,_9J);}) : (++C,A1(_9K,_9J));};}else{if(_9A>55){var _9L=new T(function(){return B(A1(_9w,__Z));});return function(_9M){return C > 19 ? new F(function(){return A1(_9M,_9L);}) : (++C,A1(_9M,_9L));};}else{return _9B(_9A-48|0);}}break;case 10:if(48>_9A){var _9N=new T(function(){return B(A1(_9w,__Z));});return function(_9O){return C > 19 ? new F(function(){return A1(_9O,_9N);}) : (++C,A1(_9O,_9N));};}else{if(_9A>57){var _9P=new T(function(){return B(A1(_9w,__Z));});return function(_9Q){return C > 19 ? new F(function(){return A1(_9Q,_9P);}) : (++C,A1(_9Q,_9P));};}else{return _9B(_9A-48|0);}}break;case 16:if(48>_9A){if(97>_9A){if(65>_9A){var _9R=new T(function(){return B(A1(_9w,__Z));});return function(_9S){return C > 19 ? new F(function(){return A1(_9S,_9R);}) : (++C,A1(_9S,_9R));};}else{if(_9A>70){var _9T=new T(function(){return B(A1(_9w,__Z));});return function(_9U){return C > 19 ? new F(function(){return A1(_9U,_9T);}) : (++C,A1(_9U,_9T));};}else{return _9B((_9A-65|0)+10|0);}}}else{if(_9A>102){if(65>_9A){var _9V=new T(function(){return B(A1(_9w,__Z));});return function(_9W){return C > 19 ? new F(function(){return A1(_9W,_9V);}) : (++C,A1(_9W,_9V));};}else{if(_9A>70){var _9X=new T(function(){return B(A1(_9w,__Z));});return function(_9Y){return C > 19 ? new F(function(){return A1(_9Y,_9X);}) : (++C,A1(_9Y,_9X));};}else{return _9B((_9A-65|0)+10|0);}}}else{return _9B((_9A-97|0)+10|0);}}}else{if(_9A>57){if(97>_9A){if(65>_9A){var _9Z=new T(function(){return B(A1(_9w,__Z));});return function(_a0){return C > 19 ? new F(function(){return A1(_a0,_9Z);}) : (++C,A1(_a0,_9Z));};}else{if(_9A>70){var _a1=new T(function(){return B(A1(_9w,__Z));});return function(_a2){return C > 19 ? new F(function(){return A1(_a2,_a1);}) : (++C,A1(_a2,_a1));};}else{return _9B((_9A-65|0)+10|0);}}}else{if(_9A>102){if(65>_9A){var _a3=new T(function(){return B(A1(_9w,__Z));});return function(_a4){return C > 19 ? new F(function(){return A1(_a4,_a3);}) : (++C,A1(_a4,_a3));};}else{if(_9A>70){var _a5=new T(function(){return B(A1(_9w,__Z));});return function(_a6){return C > 19 ? new F(function(){return A1(_a6,_a5);}) : (++C,A1(_a6,_a5));};}else{return _9B((_9A-65|0)+10|0);}}}else{return _9B((_9A-97|0)+10|0);}}}else{return _9B(_9A-48|0);}}break;default:return E(_9q);}}},_a7=function(_a8){var _a9=E(_a8);if(!_a9._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_9t,_a9);}) : (++C,A1(_9t,_a9));}};return function(_aa){return C > 19 ? new F(function(){return A3(_9u,_aa,_n,_a7);}) : (++C,A3(_9u,_aa,_n,_a7));};},_ab=function(_ac){var _ad=function(_ae){return C > 19 ? new F(function(){return A1(_ac,new T1(5,new T2(0,8,_ae)));}) : (++C,A1(_ac,new T1(5,new T2(0,8,_ae))));},_af=function(_ag){return C > 19 ? new F(function(){return A1(_ac,new T1(5,new T2(0,16,_ag)));}) : (++C,A1(_ac,new T1(5,new T2(0,16,_ag))));},_ah=function(_ai){switch(E(_ai)){case 79:return new T1(1,_9r(8,_ad));case 88:return new T1(1,_9r(16,_af));case 111:return new T1(1,_9r(8,_ad));case 120:return new T1(1,_9r(16,_af));default:return new T0(2);}};return function(_aj){return (E(_aj)==48)?E(new T1(0,_ah)):new T0(2);};},_ak=function(_al){return new T1(0,_ab(_al));},_am=function(_an){return C > 19 ? new F(function(){return A1(_an,__Z);}) : (++C,A1(_an,__Z));},_ao=function(_ap){return C > 19 ? new F(function(){return A1(_ap,__Z);}) : (++C,A1(_ap,__Z));},_aq=function(_ar,_as){while(1){var _at=E(_ar);if(!_at._){var _au=_at.a,_av=E(_as);if(!_av._){var _aw=_av.a,_ax=addC(_au,_aw);if(!E(_ax.b)){return new T1(0,_ax.a);}else{_ar=new T1(1,I_fromInt(_au));_as=new T1(1,I_fromInt(_aw));continue;}}else{_ar=new T1(1,I_fromInt(_au));_as=_av;continue;}}else{var _ay=E(_as);if(!_ay._){_ar=_at;_as=new T1(1,I_fromInt(_ay.a));continue;}else{return new T1(1,I_add(_at.a,_ay.a));}}}},_az=new T(function(){return _aq(new T1(0,2147483647),new T1(0,1));}),_aA=function(_aB){var _aC=E(_aB);if(!_aC._){var _aD=E(_aC.a);return (_aD==( -2147483648))?E(_az):new T1(0, -_aD);}else{return new T1(1,I_negate(_aC.a));}},_aE=new T1(0,10),_aF=function(_aG,_aH){while(1){var _aI=E(_aG);if(!_aI._){return E(_aH);}else{var _aJ=_aH+1|0;_aG=_aI.b;_aH=_aJ;continue;}}},_aK=function(_aL,_aM){var _aN=E(_aM);return (_aN._==0)?__Z:new T2(1,new T(function(){return B(A1(_aL,_aN.a));}),new T(function(){return _aK(_aL,_aN.b);}));},_aO=function(_aP){return new T1(0,_aP);},_aQ=function(_aR){return _aO(E(_aR));},_aS=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_aT=function(_aU,_aV){while(1){var _aW=E(_aU);if(!_aW._){var _aX=_aW.a,_aY=E(_aV);if(!_aY._){var _aZ=_aY.a;if(!(imul(_aX,_aZ)|0)){return new T1(0,imul(_aX,_aZ)|0);}else{_aU=new T1(1,I_fromInt(_aX));_aV=new T1(1,I_fromInt(_aZ));continue;}}else{_aU=new T1(1,I_fromInt(_aX));_aV=_aY;continue;}}else{var _b0=E(_aV);if(!_b0._){_aU=_aW;_aV=new T1(1,I_fromInt(_b0.a));continue;}else{return new T1(1,I_mul(_aW.a,_b0.a));}}}},_b1=function(_b2,_b3){var _b4=E(_b3);if(!_b4._){return __Z;}else{var _b5=E(_b4.b);return (_b5._==0)?E(_aS):new T2(1,_aq(_aT(_b4.a,_b2),_b5.a),new T(function(){return _b1(_b2,_b5.b);}));}},_b6=new T1(0,0),_b7=function(_b8,_b9,_ba){while(1){var _bb=(function(_bc,_bd,_be){var _bf=E(_be);if(!_bf._){return E(_b6);}else{if(!E(_bf.b)._){return E(_bf.a);}else{var _bg=E(_bd);if(_bg<=40){var _bh=function(_bi,_bj){while(1){var _bk=E(_bj);if(!_bk._){return E(_bi);}else{var _bl=_aq(_aT(_bi,_bc),_bk.a);_bi=_bl;_bj=_bk.b;continue;}}};return _bh(_b6,_bf);}else{var _bm=_aT(_bc,_bc);if(!(_bg%2)){var _bn=_b1(_bc,_bf);_b8=_bm;_b9=quot(_bg+1|0,2);_ba=_bn;return __continue;}else{var _bn=_b1(_bc,new T2(1,_b6,_bf));_b8=_bm;_b9=quot(_bg+1|0,2);_ba=_bn;return __continue;}}}}})(_b8,_b9,_ba);if(_bb!=__continue){return _bb;}}},_bo=function(_bp,_bq){return _b7(_bp,new T(function(){return _aF(_bq,0);},1),_aK(_aQ,_bq));},_br=function(_bs){var _bt=new T(function(){var _bu=new T(function(){var _bv=function(_bw){return C > 19 ? new F(function(){return A1(_bs,new T1(1,new T(function(){return _bo(_aE,_bw);})));}) : (++C,A1(_bs,new T1(1,new T(function(){return _bo(_aE,_bw);}))));};return new T1(1,_9r(10,_bv));}),_bx=function(_by){if(E(_by)==43){var _bz=function(_bA){return C > 19 ? new F(function(){return A1(_bs,new T1(1,new T(function(){return _bo(_aE,_bA);})));}) : (++C,A1(_bs,new T1(1,new T(function(){return _bo(_aE,_bA);}))));};return new T1(1,_9r(10,_bz));}else{return new T0(2);}},_bB=function(_bC){if(E(_bC)==45){var _bD=function(_bE){return C > 19 ? new F(function(){return A1(_bs,new T1(1,new T(function(){return _aA(_bo(_aE,_bE));})));}) : (++C,A1(_bs,new T1(1,new T(function(){return _aA(_bo(_aE,_bE));}))));};return new T1(1,_9r(10,_bD));}else{return new T0(2);}};return _7L(_7L(new T1(0,_bB),new T1(0,_bx)),_bu);});return _7L(new T1(0,function(_bF){return (E(_bF)==101)?E(_bt):new T0(2);}),new T1(0,function(_bG){return (E(_bG)==69)?E(_bt):new T0(2);}));},_bH=function(_bI){var _bJ=function(_bK){return C > 19 ? new F(function(){return A1(_bI,new T1(1,_bK));}) : (++C,A1(_bI,new T1(1,_bK)));};return function(_bL){return (E(_bL)==46)?new T1(1,_9r(10,_bJ)):new T0(2);};},_bM=function(_bN){return new T1(0,_bH(_bN));},_bO=function(_bP){var _bQ=function(_bR){var _bS=function(_bT){return new T1(1,_8M(_br,_am,function(_bU){return C > 19 ? new F(function(){return A1(_bP,new T1(5,new T3(1,_bR,_bT,_bU)));}) : (++C,A1(_bP,new T1(5,new T3(1,_bR,_bT,_bU))));}));};return new T1(1,_8M(_bM,_ao,_bS));};return _9r(10,_bQ);},_bV=function(_bW){return new T1(1,_bO(_bW));},_bX=function(_bY){return E(E(_bY).a);},_bZ=function(_c0,_c1,_c2){while(1){var _c3=E(_c2);if(!_c3._){return false;}else{if(!B(A3(_bX,_c0,_c1,_c3.a))){_c2=_c3.b;continue;}else{return true;}}}},_c4=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_c5=function(_c6){return _bZ(_8p,_c6,_c4);},_c7=function(_c8){var _c9=new T(function(){return B(A1(_c8,8));}),_ca=new T(function(){return B(A1(_c8,16));});return function(_cb){switch(E(_cb)){case 79:return E(_c9);case 88:return E(_ca);case 111:return E(_c9);case 120:return E(_ca);default:return new T0(2);}};},_cc=function(_cd){return new T1(0,_c7(_cd));},_ce=function(_cf){return C > 19 ? new F(function(){return A1(_cf,10);}) : (++C,A1(_cf,10));},_cg=function(_ch,_ci){var _cj=jsShowI(_ch);return _0(fromJSStr(_cj),_ci);},_ck=function(_cl,_cm,_cn){if(_cm>=0){return _cg(_cm,_cn);}else{if(_cl<=6){return _cg(_cm,_cn);}else{return new T2(1,40,new T(function(){var _co=jsShowI(_cm);return _0(fromJSStr(_co),new T2(1,41,_cn));}));}}},_cp=function(_cq){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _ck(9,_cq,__Z);})));},_cr=function(_cs){var _ct=E(_cs);if(!_ct._){return E(_ct.a);}else{return I_toInt(_ct.a);}},_cu=function(_cv,_cw){var _cx=E(_cv);if(!_cx._){var _cy=_cx.a,_cz=E(_cw);return (_cz._==0)?_cy<=_cz.a:I_compareInt(_cz.a,_cy)>=0;}else{var _cA=_cx.a,_cB=E(_cw);return (_cB._==0)?I_compareInt(_cA,_cB.a)<=0:I_compare(_cA,_cB.a)<=0;}},_cC=function(_cD){return new T0(2);},_cE=function(_cF){var _cG=E(_cF);if(!_cG._){return _cC;}else{var _cH=_cG.a,_cI=E(_cG.b);if(!_cI._){return E(_cH);}else{var _cJ=new T(function(){return _cE(_cI);}),_cK=function(_cL){return _7L(B(A1(_cH,_cL)),new T(function(){return B(A1(_cJ,_cL));}));};return _cK;}}},_cM=function(_cN,_cO){var _cP=function(_cQ,_cR,_cS){var _cT=E(_cQ);if(!_cT._){return C > 19 ? new F(function(){return A1(_cS,_cN);}) : (++C,A1(_cS,_cN));}else{var _cU=E(_cR);if(!_cU._){return new T0(2);}else{if(E(_cT.a)!=E(_cU.a)){return new T0(2);}else{var _cV=new T(function(){return B(_cP(_cT.b,_cU.b,_cS));});return new T1(0,function(_cW){return E(_cV);});}}}};return function(_cX){return C > 19 ? new F(function(){return _cP(_cN,_cX,_cO);}) : (++C,_cP(_cN,_cX,_cO));};},_cY=new T(function(){return unCStr("SO");}),_cZ=function(_d0){var _d1=new T(function(){return B(A1(_d0,14));});return new T1(1,_cM(_cY,function(_d2){return E(_d1);}));},_d3=new T(function(){return unCStr("SOH");}),_d4=function(_d5){var _d6=new T(function(){return B(A1(_d5,1));});return new T1(1,_cM(_d3,function(_d7){return E(_d6);}));},_d8=new T(function(){return unCStr("NUL");}),_d9=function(_da){var _db=new T(function(){return B(A1(_da,0));});return new T1(1,_cM(_d8,function(_dc){return E(_db);}));},_dd=new T(function(){return unCStr("STX");}),_de=function(_df){var _dg=new T(function(){return B(A1(_df,2));});return new T1(1,_cM(_dd,function(_dh){return E(_dg);}));},_di=new T(function(){return unCStr("ETX");}),_dj=function(_dk){var _dl=new T(function(){return B(A1(_dk,3));});return new T1(1,_cM(_di,function(_dm){return E(_dl);}));},_dn=new T(function(){return unCStr("EOT");}),_do=function(_dp){var _dq=new T(function(){return B(A1(_dp,4));});return new T1(1,_cM(_dn,function(_dr){return E(_dq);}));},_ds=new T(function(){return unCStr("ENQ");}),_dt=function(_du){var _dv=new T(function(){return B(A1(_du,5));});return new T1(1,_cM(_ds,function(_dw){return E(_dv);}));},_dx=new T(function(){return unCStr("ACK");}),_dy=function(_dz){var _dA=new T(function(){return B(A1(_dz,6));});return new T1(1,_cM(_dx,function(_dB){return E(_dA);}));},_dC=new T(function(){return unCStr("BEL");}),_dD=function(_dE){var _dF=new T(function(){return B(A1(_dE,7));});return new T1(1,_cM(_dC,function(_dG){return E(_dF);}));},_dH=new T(function(){return unCStr("BS");}),_dI=function(_dJ){var _dK=new T(function(){return B(A1(_dJ,8));});return new T1(1,_cM(_dH,function(_dL){return E(_dK);}));},_dM=new T(function(){return unCStr("HT");}),_dN=function(_dO){var _dP=new T(function(){return B(A1(_dO,9));});return new T1(1,_cM(_dM,function(_dQ){return E(_dP);}));},_dR=new T(function(){return unCStr("LF");}),_dS=function(_dT){var _dU=new T(function(){return B(A1(_dT,10));});return new T1(1,_cM(_dR,function(_dV){return E(_dU);}));},_dW=new T(function(){return unCStr("VT");}),_dX=function(_dY){var _dZ=new T(function(){return B(A1(_dY,11));});return new T1(1,_cM(_dW,function(_e0){return E(_dZ);}));},_e1=new T(function(){return unCStr("FF");}),_e2=function(_e3){var _e4=new T(function(){return B(A1(_e3,12));});return new T1(1,_cM(_e1,function(_e5){return E(_e4);}));},_e6=new T(function(){return unCStr("CR");}),_e7=function(_e8){var _e9=new T(function(){return B(A1(_e8,13));});return new T1(1,_cM(_e6,function(_ea){return E(_e9);}));},_eb=new T(function(){return unCStr("SI");}),_ec=function(_ed){var _ee=new T(function(){return B(A1(_ed,15));});return new T1(1,_cM(_eb,function(_ef){return E(_ee);}));},_eg=new T(function(){return unCStr("DLE");}),_eh=function(_ei){var _ej=new T(function(){return B(A1(_ei,16));});return new T1(1,_cM(_eg,function(_ek){return E(_ej);}));},_el=new T(function(){return unCStr("DC1");}),_em=function(_en){var _eo=new T(function(){return B(A1(_en,17));});return new T1(1,_cM(_el,function(_ep){return E(_eo);}));},_eq=new T(function(){return unCStr("DC2");}),_er=function(_es){var _et=new T(function(){return B(A1(_es,18));});return new T1(1,_cM(_eq,function(_eu){return E(_et);}));},_ev=new T(function(){return unCStr("DC3");}),_ew=function(_ex){var _ey=new T(function(){return B(A1(_ex,19));});return new T1(1,_cM(_ev,function(_ez){return E(_ey);}));},_eA=new T(function(){return unCStr("DC4");}),_eB=function(_eC){var _eD=new T(function(){return B(A1(_eC,20));});return new T1(1,_cM(_eA,function(_eE){return E(_eD);}));},_eF=new T(function(){return unCStr("NAK");}),_eG=function(_eH){var _eI=new T(function(){return B(A1(_eH,21));});return new T1(1,_cM(_eF,function(_eJ){return E(_eI);}));},_eK=new T(function(){return unCStr("SYN");}),_eL=function(_eM){var _eN=new T(function(){return B(A1(_eM,22));});return new T1(1,_cM(_eK,function(_eO){return E(_eN);}));},_eP=new T(function(){return unCStr("ETB");}),_eQ=function(_eR){var _eS=new T(function(){return B(A1(_eR,23));});return new T1(1,_cM(_eP,function(_eT){return E(_eS);}));},_eU=new T(function(){return unCStr("CAN");}),_eV=function(_eW){var _eX=new T(function(){return B(A1(_eW,24));});return new T1(1,_cM(_eU,function(_eY){return E(_eX);}));},_eZ=new T(function(){return unCStr("EM");}),_f0=function(_f1){var _f2=new T(function(){return B(A1(_f1,25));});return new T1(1,_cM(_eZ,function(_f3){return E(_f2);}));},_f4=new T(function(){return unCStr("SUB");}),_f5=function(_f6){var _f7=new T(function(){return B(A1(_f6,26));});return new T1(1,_cM(_f4,function(_f8){return E(_f7);}));},_f9=new T(function(){return unCStr("ESC");}),_fa=function(_fb){var _fc=new T(function(){return B(A1(_fb,27));});return new T1(1,_cM(_f9,function(_fd){return E(_fc);}));},_fe=new T(function(){return unCStr("FS");}),_ff=function(_fg){var _fh=new T(function(){return B(A1(_fg,28));});return new T1(1,_cM(_fe,function(_fi){return E(_fh);}));},_fj=new T(function(){return unCStr("GS");}),_fk=function(_fl){var _fm=new T(function(){return B(A1(_fl,29));});return new T1(1,_cM(_fj,function(_fn){return E(_fm);}));},_fo=new T(function(){return unCStr("RS");}),_fp=function(_fq){var _fr=new T(function(){return B(A1(_fq,30));});return new T1(1,_cM(_fo,function(_fs){return E(_fr);}));},_ft=new T(function(){return unCStr("US");}),_fu=function(_fv){var _fw=new T(function(){return B(A1(_fv,31));});return new T1(1,_cM(_ft,function(_fx){return E(_fw);}));},_fy=new T(function(){return unCStr("SP");}),_fz=function(_fA){var _fB=new T(function(){return B(A1(_fA,32));});return new T1(1,_cM(_fy,function(_fC){return E(_fB);}));},_fD=new T(function(){return unCStr("DEL");}),_fE=function(_fF){var _fG=new T(function(){return B(A1(_fF,127));});return new T1(1,_cM(_fD,function(_fH){return E(_fG);}));},_fI=new T(function(){return _cE(new T2(1,function(_fJ){return new T1(1,_8M(_d4,_cZ,_fJ));},new T2(1,_d9,new T2(1,_de,new T2(1,_dj,new T2(1,_do,new T2(1,_dt,new T2(1,_dy,new T2(1,_dD,new T2(1,_dI,new T2(1,_dN,new T2(1,_dS,new T2(1,_dX,new T2(1,_e2,new T2(1,_e7,new T2(1,_ec,new T2(1,_eh,new T2(1,_em,new T2(1,_er,new T2(1,_ew,new T2(1,_eB,new T2(1,_eG,new T2(1,_eL,new T2(1,_eQ,new T2(1,_eV,new T2(1,_f0,new T2(1,_f5,new T2(1,_fa,new T2(1,_ff,new T2(1,_fk,new T2(1,_fp,new T2(1,_fu,new T2(1,_fz,new T2(1,_fE,__Z))))))))))))))))))))))))))))))))));}),_fK=function(_fL){var _fM=new T(function(){return B(A1(_fL,7));}),_fN=new T(function(){return B(A1(_fL,8));}),_fO=new T(function(){return B(A1(_fL,9));}),_fP=new T(function(){return B(A1(_fL,10));}),_fQ=new T(function(){return B(A1(_fL,11));}),_fR=new T(function(){return B(A1(_fL,12));}),_fS=new T(function(){return B(A1(_fL,13));}),_fT=new T(function(){return B(A1(_fL,92));}),_fU=new T(function(){return B(A1(_fL,39));}),_fV=new T(function(){return B(A1(_fL,34));}),_fW=new T(function(){var _fX=function(_fY){var _fZ=new T(function(){return _aO(E(_fY));}),_g0=function(_g1){var _g2=_bo(_fZ,_g1);if(!_cu(_g2,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_fL,new T(function(){var _g3=_cr(_g2);if(_g3>>>0>1114111){return _cp(_g3);}else{return _g3;}}));}) : (++C,A1(_fL,new T(function(){var _g3=_cr(_g2);if(_g3>>>0>1114111){return _cp(_g3);}else{return _g3;}})));}};return new T1(1,_9r(_fY,_g0));},_g4=new T(function(){var _g5=new T(function(){return B(A1(_fL,31));}),_g6=new T(function(){return B(A1(_fL,30));}),_g7=new T(function(){return B(A1(_fL,29));}),_g8=new T(function(){return B(A1(_fL,28));}),_g9=new T(function(){return B(A1(_fL,27));}),_ga=new T(function(){return B(A1(_fL,26));}),_gb=new T(function(){return B(A1(_fL,25));}),_gc=new T(function(){return B(A1(_fL,24));}),_gd=new T(function(){return B(A1(_fL,23));}),_ge=new T(function(){return B(A1(_fL,22));}),_gf=new T(function(){return B(A1(_fL,21));}),_gg=new T(function(){return B(A1(_fL,20));}),_gh=new T(function(){return B(A1(_fL,19));}),_gi=new T(function(){return B(A1(_fL,18));}),_gj=new T(function(){return B(A1(_fL,17));}),_gk=new T(function(){return B(A1(_fL,16));}),_gl=new T(function(){return B(A1(_fL,15));}),_gm=new T(function(){return B(A1(_fL,14));}),_gn=new T(function(){return B(A1(_fL,6));}),_go=new T(function(){return B(A1(_fL,5));}),_gp=new T(function(){return B(A1(_fL,4));}),_gq=new T(function(){return B(A1(_fL,3));}),_gr=new T(function(){return B(A1(_fL,2));}),_gs=new T(function(){return B(A1(_fL,1));}),_gt=new T(function(){return B(A1(_fL,0));}),_gu=function(_gv){switch(E(_gv)){case 64:return E(_gt);case 65:return E(_gs);case 66:return E(_gr);case 67:return E(_gq);case 68:return E(_gp);case 69:return E(_go);case 70:return E(_gn);case 71:return E(_fM);case 72:return E(_fN);case 73:return E(_fO);case 74:return E(_fP);case 75:return E(_fQ);case 76:return E(_fR);case 77:return E(_fS);case 78:return E(_gm);case 79:return E(_gl);case 80:return E(_gk);case 81:return E(_gj);case 82:return E(_gi);case 83:return E(_gh);case 84:return E(_gg);case 85:return E(_gf);case 86:return E(_ge);case 87:return E(_gd);case 88:return E(_gc);case 89:return E(_gb);case 90:return E(_ga);case 91:return E(_g9);case 92:return E(_g8);case 93:return E(_g7);case 94:return E(_g6);case 95:return E(_g5);default:return new T0(2);}};return _7L(new T1(0,function(_gw){return (E(_gw)==94)?E(new T1(0,_gu)):new T0(2);}),new T(function(){return B(A1(_fI,_fL));}));});return _7L(new T1(1,_8M(_cc,_ce,_fX)),_g4);});return _7L(new T1(0,function(_gx){switch(E(_gx)){case 34:return E(_fV);case 39:return E(_fU);case 92:return E(_fT);case 97:return E(_fM);case 98:return E(_fN);case 102:return E(_fR);case 110:return E(_fP);case 114:return E(_fS);case 116:return E(_fO);case 118:return E(_fQ);default:return new T0(2);}}),_fW);},_gy=function(_gz){return C > 19 ? new F(function(){return A1(_gz,0);}) : (++C,A1(_gz,0));},_gA=function(_gB){var _gC=E(_gB);if(!_gC._){return _gy;}else{var _gD=E(_gC.a),_gE=_gD>>>0,_gF=new T(function(){return _gA(_gC.b);});if(_gE>887){var _gG=u_iswspace(_gD);if(!E(_gG)){return _gy;}else{var _gH=function(_gI){var _gJ=new T(function(){return B(A1(_gF,_gI));});return new T1(0,function(_gK){return E(_gJ);});};return _gH;}}else{if(_gE==32){var _gL=function(_gM){var _gN=new T(function(){return B(A1(_gF,_gM));});return new T1(0,function(_gO){return E(_gN);});};return _gL;}else{if(_gE-9>>>0>4){if(_gE==160){var _gP=function(_gQ){var _gR=new T(function(){return B(A1(_gF,_gQ));});return new T1(0,function(_gS){return E(_gR);});};return _gP;}else{return _gy;}}else{var _gT=function(_gU){var _gV=new T(function(){return B(A1(_gF,_gU));});return new T1(0,function(_gW){return E(_gV);});};return _gT;}}}}},_gX=function(_gY){var _gZ=new T(function(){return B(_gX(_gY));}),_h0=function(_h1){return (E(_h1)==92)?E(_gZ):new T0(2);},_h2=function(_h3){return E(new T1(0,_h0));},_h4=new T1(1,function(_h5){return C > 19 ? new F(function(){return A2(_gA,_h5,_h2);}) : (++C,A2(_gA,_h5,_h2));}),_h6=new T(function(){return B(_fK(function(_h7){return C > 19 ? new F(function(){return A1(_gY,new T2(0,_h7,true));}) : (++C,A1(_gY,new T2(0,_h7,true)));}));}),_h8=function(_h9){var _ha=E(_h9);if(_ha==38){return E(_gZ);}else{var _hb=_ha>>>0;if(_hb>887){var _hc=u_iswspace(_ha);return (E(_hc)==0)?new T0(2):E(_h4);}else{return (_hb==32)?E(_h4):(_hb-9>>>0>4)?(_hb==160)?E(_h4):new T0(2):E(_h4);}}};return _7L(new T1(0,function(_hd){return (E(_hd)==92)?E(new T1(0,_h8)):new T0(2);}),new T1(0,function(_he){var _hf=E(_he);if(_hf==92){return E(_h6);}else{return C > 19 ? new F(function(){return A1(_gY,new T2(0,_hf,false));}) : (++C,A1(_gY,new T2(0,_hf,false)));}}));},_hg=function(_hh,_hi){var _hj=new T(function(){return B(A1(_hi,new T1(1,new T(function(){return B(A1(_hh,__Z));}))));}),_hk=function(_hl){var _hm=E(_hl),_hn=E(_hm.a);if(_hn==34){if(!E(_hm.b)){return E(_hj);}else{return C > 19 ? new F(function(){return _hg(function(_ho){return C > 19 ? new F(function(){return A1(_hh,new T2(1,_hn,_ho));}) : (++C,A1(_hh,new T2(1,_hn,_ho)));},_hi);}) : (++C,_hg(function(_ho){return C > 19 ? new F(function(){return A1(_hh,new T2(1,_hn,_ho));}) : (++C,A1(_hh,new T2(1,_hn,_ho)));},_hi));}}else{return C > 19 ? new F(function(){return _hg(function(_hp){return C > 19 ? new F(function(){return A1(_hh,new T2(1,_hn,_hp));}) : (++C,A1(_hh,new T2(1,_hn,_hp)));},_hi);}) : (++C,_hg(function(_hp){return C > 19 ? new F(function(){return A1(_hh,new T2(1,_hn,_hp));}) : (++C,A1(_hh,new T2(1,_hn,_hp)));},_hi));}};return C > 19 ? new F(function(){return _gX(_hk);}) : (++C,_gX(_hk));},_hq=new T(function(){return unCStr("_\'");}),_hr=function(_hs){var _ht=u_iswalnum(_hs);if(!E(_ht)){return _bZ(_8p,_hs,_hq);}else{return true;}},_hu=function(_hv){return _hr(E(_hv));},_hw=new T(function(){return unCStr(",;()[]{}`");}),_hx=new T(function(){return unCStr("=>");}),_hy=new T(function(){return unCStr("~");}),_hz=new T(function(){return unCStr("@");}),_hA=new T(function(){return unCStr("->");}),_hB=new T(function(){return unCStr("<-");}),_hC=new T(function(){return unCStr("|");}),_hD=new T(function(){return unCStr("\\");}),_hE=new T(function(){return unCStr("=");}),_hF=new T(function(){return unCStr("::");}),_hG=new T(function(){return unCStr("..");}),_hH=function(_hI){var _hJ=new T(function(){return B(A1(_hI,new T0(6)));}),_hK=new T(function(){var _hL=new T(function(){var _hM=function(_hN){var _hO=new T(function(){return B(A1(_hI,new T1(0,_hN)));});return new T1(0,function(_hP){return (E(_hP)==39)?E(_hO):new T0(2);});};return B(_fK(_hM));}),_hQ=function(_hR){var _hS=E(_hR);switch(_hS){case 39:return new T0(2);case 92:return E(_hL);default:var _hT=new T(function(){return B(A1(_hI,new T1(0,_hS)));});return new T1(0,function(_hU){return (E(_hU)==39)?E(_hT):new T0(2);});}},_hV=new T(function(){var _hW=new T(function(){return B(_hg(_n,_hI));}),_hX=new T(function(){var _hY=new T(function(){var _hZ=new T(function(){var _i0=function(_i1){var _i2=E(_i1),_i3=u_iswalpha(_i2);return (E(_i3)==0)?(_i2==95)?new T1(1,_9c(_hu,function(_i4){return C > 19 ? new F(function(){return A1(_hI,new T1(3,new T2(1,_i2,_i4)));}) : (++C,A1(_hI,new T1(3,new T2(1,_i2,_i4))));})):new T0(2):new T1(1,_9c(_hu,function(_i5){return C > 19 ? new F(function(){return A1(_hI,new T1(3,new T2(1,_i2,_i5)));}) : (++C,A1(_hI,new T1(3,new T2(1,_i2,_i5))));}));};return _7L(new T1(0,_i0),new T(function(){return new T1(1,_8M(_ak,_bV,_hI));}));}),_i6=function(_i7){return (!_bZ(_8p,_i7,_c4))?new T0(2):new T1(1,_9c(_c5,function(_i8){var _i9=new T2(1,_i7,_i8);if(!_bZ(_6q,_i9,new T2(1,_hG,new T2(1,_hF,new T2(1,_hE,new T2(1,_hD,new T2(1,_hC,new T2(1,_hB,new T2(1,_hA,new T2(1,_hz,new T2(1,_hy,new T2(1,_hx,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_hI,new T1(4,_i9));}) : (++C,A1(_hI,new T1(4,_i9)));}else{return C > 19 ? new F(function(){return A1(_hI,new T1(2,_i9));}) : (++C,A1(_hI,new T1(2,_i9)));}}));};return _7L(new T1(0,_i6),_hZ);});return _7L(new T1(0,function(_ia){if(!_bZ(_8p,_ia,_hw)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_hI,new T1(2,new T2(1,_ia,__Z)));}) : (++C,A1(_hI,new T1(2,new T2(1,_ia,__Z))));}}),_hY);});return _7L(new T1(0,function(_ib){return (E(_ib)==34)?E(_hW):new T0(2);}),_hX);});return _7L(new T1(0,function(_ic){return (E(_ic)==39)?E(new T1(0,_hQ)):new T0(2);}),_hV);});return _7L(new T1(1,function(_id){return (E(_id)._==0)?E(_hJ):new T0(2);}),_hK);},_ie=function(_if,_ig){var _ih=new T(function(){var _ii=new T(function(){var _ij=function(_ik){var _il=new T(function(){var _im=new T(function(){return B(A1(_ig,_ik));});return B(_hH(function(_in){var _io=E(_in);return (_io._==2)?(!_8h(_io.a,_8g))?new T0(2):E(_im):new T0(2);}));}),_ip=function(_iq){return E(_il);};return new T1(1,function(_ir){return C > 19 ? new F(function(){return A2(_gA,_ir,_ip);}) : (++C,A2(_gA,_ir,_ip));});};return B(A2(_if,0,_ij));});return B(_hH(function(_is){var _it=E(_is);return (_it._==2)?(!_8h(_it.a,_8f))?new T0(2):E(_ii):new T0(2);}));}),_iu=function(_iv){return E(_ih);};return function(_iw){return C > 19 ? new F(function(){return A2(_gA,_iw,_iu);}) : (++C,A2(_gA,_iw,_iu));};},_ix=function(_iy,_iz){var _iA=function(_iB){var _iC=new T(function(){return B(A1(_iy,_iB));}),_iD=function(_iE){return _7L(B(A1(_iC,_iE)),new T(function(){return new T1(1,_ie(_iA,_iE));}));};return _iD;},_iF=new T(function(){return B(A1(_iy,_iz));}),_iG=function(_iH){return _7L(B(A1(_iF,_iH)),new T(function(){return new T1(1,_ie(_iA,_iH));}));};return _iG;},_iI=function(_iJ,_iK){var _iL=function(_iM,_iN){var _iO=function(_iP){return C > 19 ? new F(function(){return A1(_iN,new T(function(){return  -E(_iP);}));}) : (++C,A1(_iN,new T(function(){return  -E(_iP);})));},_iQ=new T(function(){return B(_hH(function(_iR){return C > 19 ? new F(function(){return A3(_iJ,_iR,_iM,_iO);}) : (++C,A3(_iJ,_iR,_iM,_iO));}));}),_iS=function(_iT){return E(_iQ);},_iU=function(_iV){return C > 19 ? new F(function(){return A2(_gA,_iV,_iS);}) : (++C,A2(_gA,_iV,_iS));},_iW=new T(function(){return B(_hH(function(_iX){var _iY=E(_iX);if(_iY._==4){var _iZ=E(_iY.a);if(!_iZ._){return C > 19 ? new F(function(){return A3(_iJ,_iY,_iM,_iN);}) : (++C,A3(_iJ,_iY,_iM,_iN));}else{if(E(_iZ.a)==45){if(!E(_iZ.b)._){return E(new T1(1,_iU));}else{return C > 19 ? new F(function(){return A3(_iJ,_iY,_iM,_iN);}) : (++C,A3(_iJ,_iY,_iM,_iN));}}else{return C > 19 ? new F(function(){return A3(_iJ,_iY,_iM,_iN);}) : (++C,A3(_iJ,_iY,_iM,_iN));}}}else{return C > 19 ? new F(function(){return A3(_iJ,_iY,_iM,_iN);}) : (++C,A3(_iJ,_iY,_iM,_iN));}}));}),_j0=function(_j1){return E(_iW);};return new T1(1,function(_j2){return C > 19 ? new F(function(){return A2(_gA,_j2,_j0);}) : (++C,A2(_gA,_j2,_j0));});};return _ix(_iL,_iK);},_j3=function(_j4){var _j5=E(_j4);if(!_j5._){var _j6=_j5.b,_j7=new T(function(){return _b7(new T(function(){return _aO(E(_j5.a));}),new T(function(){return _aF(_j6,0);},1),_aK(_aQ,_j6));});return new T1(1,_j7);}else{return (E(_j5.b)._==0)?(E(_j5.c)._==0)?new T1(1,new T(function(){return _bo(_aE,_j5.a);})):__Z:__Z;}},_j8=function(_j9,_ja){return new T0(2);},_jb=function(_jc){var _jd=E(_jc);if(_jd._==5){var _je=_j3(_jd.a);if(!_je._){return _j8;}else{var _jf=new T(function(){return _cr(_je.a);});return function(_jg,_jh){return C > 19 ? new F(function(){return A1(_jh,_jf);}) : (++C,A1(_jh,_jf));};}}else{return _j8;}},_ji=function(_jj){return _iI(_jb,_jj);},_jk=new T(function(){return unCStr("[");}),_jl=function(_jm,_jn){var _jo=function(_jp,_jq){var _jr=new T(function(){return B(A1(_jq,__Z));}),_js=new T(function(){var _jt=function(_ju){return _jo(true,function(_jv){return C > 19 ? new F(function(){return A1(_jq,new T2(1,_ju,_jv));}) : (++C,A1(_jq,new T2(1,_ju,_jv)));});};return B(A2(_jm,0,_jt));}),_jw=new T(function(){return B(_hH(function(_jx){var _jy=E(_jx);if(_jy._==2){var _jz=E(_jy.a);if(!_jz._){return new T0(2);}else{var _jA=_jz.b;switch(E(_jz.a)){case 44:return (E(_jA)._==0)?(!E(_jp))?new T0(2):E(_js):new T0(2);case 93:return (E(_jA)._==0)?E(_jr):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_jB=function(_jC){return E(_jw);};return new T1(1,function(_jD){return C > 19 ? new F(function(){return A2(_gA,_jD,_jB);}) : (++C,A2(_gA,_jD,_jB));});},_jE=function(_jF,_jG){return C > 19 ? new F(function(){return _jH(_jG);}) : (++C,_jH(_jG));},_jH=function(_jI){var _jJ=new T(function(){var _jK=new T(function(){var _jL=new T(function(){var _jM=function(_jN){return _jo(true,function(_jO){return C > 19 ? new F(function(){return A1(_jI,new T2(1,_jN,_jO));}) : (++C,A1(_jI,new T2(1,_jN,_jO)));});};return B(A2(_jm,0,_jM));});return _7L(_jo(false,_jI),_jL);});return B(_hH(function(_jP){var _jQ=E(_jP);return (_jQ._==2)?(!_8h(_jQ.a,_jk))?new T0(2):E(_jK):new T0(2);}));}),_jR=function(_jS){return E(_jJ);};return _7L(new T1(1,function(_jT){return C > 19 ? new F(function(){return A2(_gA,_jT,_jR);}) : (++C,A2(_gA,_jT,_jR));}),new T(function(){return new T1(1,_ie(_jE,_jI));}));};return C > 19 ? new F(function(){return _jH(_jn);}) : (++C,_jH(_jn));},_jU=new T(function(){return B(_jl(_ji,_8E));}),_jV=function(_jW){var _jX=new T(function(){return B(A3(_iI,_jb,_jW,_8E));});return function(_3v){return _7B(_jX,_3v);};},_jY=function(_jZ,_k0,_k1){return C > 19 ? new F(function(){return _3H(_k0,_jZ,_k1);}) : (++C,_3H(_k0,_jZ,_k1));},_k2=function(_k3,_k4,_k5){var _k6=E(_k5);return new T2(0,function(_k7){return C > 19 ? new F(function(){return _jY(_k3,_k6.a,_k7);}) : (++C,_jY(_k3,_k6.a,_k7));},function(_k7){return C > 19 ? new F(function(){return _3H(_k4,_k6.b,_k7);}) : (++C,_3H(_k4,_k6.b,_k7));});},_k8=new T2(0,_n,_3F),_k9=function(_ka,_kb,_kc){var _kd=function(_ke){return C > 19 ? new F(function(){return A1(_kc,new T(function(){return B(A1(_ka,_ke));}));}) : (++C,A1(_kc,new T(function(){return B(A1(_ka,_ke));})));};return C > 19 ? new F(function(){return A1(_kb,_kd);}) : (++C,A1(_kb,_kd));},_kf=function(_kg,_kh,_ki,_kj){var _kk=function(_kl){var _km=E(_kl);if(!_km._){return E(_kj);}else{var _kn=E(_km.a);return C > 19 ? new F(function(){return A2(_ki,_kn.a,new T(function(){return B(A2(_kn.b,_ki,_kj));}));}) : (++C,A2(_ki,_kn.a,new T(function(){return B(A2(_kn.b,_ki,_kj));})));}};return C > 19 ? new F(function(){return A3(_2X,_kg,_kh,_kk);}) : (++C,A3(_2X,_kg,_kh,_kk));},_ko=function(_kp,_kq){var _kr=new T(function(){return _2V(new T(function(){return _2P(_kp);}));}),_ks=function(_kt,_ku){return C > 19 ? new F(function(){return A1(_kr,new T1(1,new T2(0,_kt,function(_kv,_kw){return C > 19 ? new F(function(){return _kf(_kp,_ku,_kv,_kw);}) : (++C,_kf(_kp,_ku,_kv,_kw));})));}) : (++C,A1(_kr,new T1(1,new T2(0,_kt,function(_kv,_kw){return C > 19 ? new F(function(){return _kf(_kp,_ku,_kv,_kw);}) : (++C,_kf(_kp,_ku,_kv,_kw));}))));};return C > 19 ? new F(function(){return A2(_kq,_ks,new T(function(){return B(A1(_kr,__Z));}));}) : (++C,A2(_kq,_ks,new T(function(){return B(A1(_kr,__Z));})));},_kx=function(_ky){return new T3(0,_ky,function(_kw){return C > 19 ? new F(function(){return _ko(_ky,_kw);}) : (++C,_ko(_ky,_kw));},function(_kz,_kv,_kw){return C > 19 ? new F(function(){return _kf(_ky,_kz,_kv,_kw);}) : (++C,_kf(_ky,_kz,_kv,_kw));});},_kA=function(_kB){return E(E(_kB).a);},_kC=function(_kD){return E(E(_kD).b);},_kE=function(_kF,_kG){var _kH=_kA(_kF),_kI=new T(function(){return _2P(_kH);}),_kJ=new T(function(){return _2R(new T(function(){return _2T(_kI);}));}),_kK=new T(function(){return B(A2(_2V,_kI,__Z));}),_kL=function(_kM){var _kN=E(_kM);if(!_kN._){return E(_kK);}else{var _kO=E(_kN.a);return C > 19 ? new F(function(){return A2(_kJ,function(_kw){return new T2(1,_kO.a,_kw);},new T(function(){return B(_kE(_kF,_kO.b));}));}) : (++C,A2(_kJ,function(_kw){return new T2(1,_kO.a,_kw);},new T(function(){return B(_kE(_kF,_kO.b));})));}};return C > 19 ? new F(function(){return A3(_2X,_kH,new T(function(){return B(A2(_kC,_kF,_kG));}),_kL);}) : (++C,A3(_2X,_kH,new T(function(){return B(A2(_kC,_kF,_kG));}),_kL));},_kP=function(_kQ){return E(E(_kQ).c);},_kR=function(_kS,_kT,_kU,_kV){var _kW=new T(function(){return _2P(new T(function(){return _kA(_kS);}));}),_kX=new T(function(){return _2V(_kW);}),_kY=new T(function(){return _2R(new T(function(){return _2T(_kW);}));}),_kZ=new T(function(){return B(A1(_kU,function(_kw){return C > 19 ? new F(function(){return _kE(_kT,_kw);}) : (++C,_kE(_kT,_kw));}));}),_l0=function(_l1){var _l2=E(_l1);if(!_l2._){return __Z;}else{var _l3=new T(function(){return B(_l4(new T(function(){return B(A1(_kX,_l2.b));})));});return new T1(1,new T2(0,_l2.a,_l3));}},_l4=function(_l5){return C > 19 ? new F(function(){return A2(_kP,_kS,new T(function(){return B(A2(_kY,_l0,_l5));}));}) : (++C,A2(_kP,_kS,new T(function(){return B(A2(_kY,_l0,_l5));})));};return C > 19 ? new F(function(){return A2(_kV,_l4,_kZ);}) : (++C,A2(_kV,_l4,_kZ));},_l6=function(_l7){return E(_l7);},_l8=function(_l9){return E(_l9);},_la=function(_lb,_lc,_ld,_le){var _lf=new T(function(){var _lg=B(A(_kR,[new T(function(){return _kx(_lc);}),new T(function(){return _kx(_lb);}),_4P,_k2,_k8])),_lh=new T(function(){var _li=function(_lj){return C > 19 ? new F(function(){return A1(_lg.b,_lj);}) : (++C,A1(_lg.b,_lj));};return B(A1(_ld,function(_lk,_ll){return C > 19 ? new F(function(){return _3H(_li,_lk,_ll);}) : (++C,_3H(_li,_lk,_ll));}));});return B(A2(_le,function(_lk,_ll){return C > 19 ? new F(function(){return _3H(_lg.a,_lk,_ll);}) : (++C,_3H(_lg.a,_lk,_ll));},_lh));}),_lm=new T(function(){return _48(_k9,_k9,_ld,_le);}),_ln=new T(function(){return B(A2(_le,_l8,new T(function(){return B(A1(_ld,_l6));})));}),_lo=function(_lp){var _lq=new T(function(){return B(A1(_lm,new T(function(){return B(A1(_ln,_lp));})));});return C > 19 ? new F(function(){return A1(_lf,_lq);}) : (++C,A1(_lf,_lq));};return _lo;},_lr=function(_ls,_lt){var _lu=B(A(_la,[_4S,_ls,_4P,_k2,_k8])),_lv=new T(function(){return B(A1(_lu.b,_lt));}),_lw=new T(function(){return _2V(new T(function(){return _2P(_ls);}));}),_lx=function(_ly){return C > 19 ? new F(function(){return A1(_lw,new T(function(){return B(A1(_lv,_ly));}));}) : (++C,A1(_lw,new T(function(){return B(A1(_lv,_ly));})));};return C > 19 ? new F(function(){return A1(_lu.a,_lx);}) : (++C,A1(_lu.a,_lx));},_lz=function(_lA){var _lB=E(_lA);return new T2(0,_lB.b,_lB.a);},_lC=function(_lD){var _lE=E(_lD);return (_lE._==0)?__Z:new T2(1,new T(function(){return _lz(_lE.a);}),new T(function(){return _lC(_lE.b);}));},_lF=function(_lG,_lH,_lI){var _lJ=E(_lG);if(!_lJ._){return E(_lI);}else{var _lK=E(_lJ.a);return C > 19 ? new F(function(){return A2(_lH,_lK.a,new T(function(){return B(A2(_lK.b,_lH,_lI));}));}) : (++C,A2(_lH,_lK.a,new T(function(){return B(A2(_lK.b,_lH,_lI));})));}},_lL=new T3(0,_4S,function(_ll){return C > 19 ? new F(function(){return _ko(_4S,_ll);}) : (++C,_ko(_4S,_ll));},_lF),_lM=new T(function(){return B(A1(B(_kR(_lL,_lL,_4P,_k2)),_k8));}),_lN=function(_lO,_lP){var _lQ=new T(function(){var _lR=E(_lM),_lS=new T(function(){var _lT=function(_lU){return C > 19 ? new F(function(){return A1(_lR.b,_lU);}) : (++C,A1(_lR.b,_lU));};return B(A1(_lO,function(_lk,_ll){return C > 19 ? new F(function(){return _3H(_lT,_lk,_ll);}) : (++C,_3H(_lT,_lk,_ll));}));});return B(A2(_lP,function(_lk,_ll){return C > 19 ? new F(function(){return _3H(_lR.a,_lk,_ll);}) : (++C,_3H(_lR.a,_lk,_ll));},_lS));}),_lV=new T(function(){return _48(_k9,_k9,_lO,_lP);}),_lW=new T(function(){return B(A2(_lP,_l8,new T(function(){return B(A1(_lO,_l6));})));}),_lX=function(_lY){var _lZ=new T(function(){return B(A1(_lV,new T(function(){return B(A1(_lW,_lY));})));});return C > 19 ? new F(function(){return A1(_lQ,_lZ);}) : (++C,A1(_lQ,_lZ));};return _lX;},_m0=new T(function(){return _lN(_3C,_3w);}),_m1=function(_m2){return E(E(_m2).a);},_m3=function(_m4,_m5){var _m6=new T(function(){var _m7=new T(function(){return B(A2(_m1,_m5,0));});return B(A2(_m0,_3F,function(_m8){return _lC(B(A1(_m7,_m8)));}));});return C > 19 ? new F(function(){return _lr(_m4,_m6);}) : (++C,_lr(_m4,_m6));},_m9=new T(function(){return B(_m3(_4S,new T4(0,_jV,function(_jj){return _7B(_jU,_jj);},_ji,function(_ma,_mb){return C > 19 ? new F(function(){return _jl(_ji,_mb);}) : (++C,_jl(_ji,_mb));})));}),_mc=function(_md,_me){var _mf=E(_md);return (_mf._==0)?E(_me):_mf;},_mg=function(_mh){return new T1(1,_mh);},_mi=function(_mj,_mk){var _ml=E(_mk);return (_ml._==0)?__Z:new T2(1,_mj,new T(function(){return _mi(_ml.a,_ml.b);}));},_mm=new T(function(){return unCStr(": empty list");}),_mn=new T(function(){return unCStr("Prelude.");}),_mo=function(_mp){return err(_0(_mn,new T(function(){return _0(_mp,_mm);},1)));},_mq=new T(function(){return _mo(new T(function(){return unCStr("init");}));}),_mr=function(_ms){var _mt=E(_ms);if(!_mt._){return E(_mq);}else{return _mi(_mt.a,_mt.b);}},_mu=function(_mv,_mw,_mx,_my,_mz){var _mA=function(_mB){var _mC=E(_mB);if(!_mC._){return __Z;}else{var _mD=new T(function(){return B(A1(_mx,new T(function(){return _3W(_mC.a);})));});return new T2(1,_mD,new T(function(){return _mA(_mC.b);}));}};return C > 19 ? new F(function(){return A3(_2R,_2T(_2P(_mv)),function(_mE){return C > 19 ? new F(function(){return _2B(_mw,_mA(_mE));}) : (++C,_2B(_mw,_mA(_mE)));},new T(function(){return B(A2(B(A(_la,[_mv,_mv,_4P,_k2,_k8])).b,_my,_mz));}));}) : (++C,A3(_2R,_2T(_2P(_mv)),function(_mE){return C > 19 ? new F(function(){return _2B(_mw,_mA(_mE));}) : (++C,_2B(_mw,_mA(_mE)));},new T(function(){return B(A2(B(A(_la,[_mv,_mv,_4P,_k2,_k8])).b,_my,_mz));})));},_mF=function(_mG){var _mH=function(_mI){var _mJ=B(_mu(_4S,new T2(0,_mc,__Z),_mg,_m9,_mG));return (_mJ._==0)?new T1(5,_mG):new T1(2,_mJ.a);},_mK=E(_mG);if(!_mK._){return _mH(_);}else{var _mL=_mK.b;switch(E(_mK.a)){case 34:return new T1(3,new T(function(){return _mr(_mL);}));case 39:return new T1(3,_mL);case 58:return new T1(4,_mL);case 123:if(!E(_mL)._){return __Z;}else{return _mH(_);}break;case 125:if(!E(_mL)._){return new T0(1);}else{return _mH(_);}break;default:return _mH(_);}}},_mM=new T2(0,_6A,_mF),_mN=function(_mO,_mP,_mQ){return new T2(0,_mO,_mP);},_mR=function(_mS,_mT){while(1){var _mU=(function(_mV,_mW){var _mX=E(_mW);if(!_mX._){_mS=new T2(1,new T2(0,_mX.b,_mX.c),new T(function(){return _mR(_mV,_mX.e);}));_mT=_mX.d;return __continue;}else{return E(_mV);}})(_mS,_mT);if(_mU!=__continue){return _mU;}}},_mY=function(_mZ,_n0,_n1){var _n2=new T(function(){var _n3=function(_n4){var _n5=new T(function(){return B(A1(_n0,new T(function(){return E(E(_n4).a);})));});return new T3(0,_n5,new T(function(){return E(E(_n4).b);}),new T(function(){return E(E(_n4).c);}));};return B(A1(_mZ,_n3));}),_n6=function(_n7){return C > 19 ? new F(function(){return A1(_n2,new T(function(){return B(A1(_n1,_n7));}));}) : (++C,A1(_n2,new T(function(){return B(A1(_n1,_n7));})));};return _n6;},_n8=function(_n9,_na,_nb,_nc){var _nd=new T(function(){return B(A1(_nb,new T(function(){return E(E(_nc).b);})));});return C > 19 ? new F(function(){return A2(_2V,_2P(_na),new T3(0,0,_nd,_2L));}) : (++C,A2(_2V,_2P(_na),new T3(0,0,_nd,_2L)));},_ne=function(_nf,_ng,_nh,_ni){return C > 19 ? new F(function(){return A2(_2V,_2P(_ng),new T3(0,0,_nh,_2L));}) : (++C,A2(_2V,_2P(_ng),new T3(0,0,_nh,_2L)));},_nj=function(_nk,_nl,_nm){var _nn=new T(function(){return E(E(_nm).b);});return C > 19 ? new F(function(){return A2(_2V,_2P(_nl),new T3(0,_nn,_nn,_2L));}) : (++C,A2(_2V,_2P(_nl),new T3(0,_nn,_nn,_2L)));},_no=function(_np,_nq){return new T4(0,_np,function(_4j){return C > 19 ? new F(function(){return _nj(_np,_nq,_4j);}) : (++C,_nj(_np,_nq,_4j));},function(_4i,_4j){return C > 19 ? new F(function(){return _ne(_np,_nq,_4i,_4j);}) : (++C,_ne(_np,_nq,_4i,_4j));},function(_4i,_4j){return C > 19 ? new F(function(){return _n8(_np,_nq,_4i,_4j);}) : (++C,_n8(_np,_nq,_4i,_4j));});},_nr=function(_ns,_nt,_nu,_nv){var _nw=new T(function(){return B(A3(_2R,_2T(_ns),_nv,_nu));});return function(_3v){return C > 19 ? new F(function(){return _2Z(_2M,_nt,_nw,_3v);}) : (++C,_2Z(_2M,_nt,_nw,_3v));};},_nx=function(_ny,_nz){return new T3(0,_ny,function(_nA,_nB){return C > 19 ? new F(function(){return _2Z(_2M,_nz,_nA,_nB);}) : (++C,_2Z(_2M,_nz,_nA,_nB));},function(_4i,_4j){return _nr(_ny,_nz,_4i,_4j);});},_nC=function(_nD,_nE){return new T2(0,_nD,function(_nF,_nG){return _3f(_nE,_nF,_nG);});},_nH=function(_nI,_nJ){return _nK(_nI,_nJ);},_nK=function(_nL,_nM){var _nN=E(_nL);return (_nN._==0)?E(_nM):new T2(1,_nN.a,new T(function(){return _nH(_nN.b,_nM);}));},_nO=function(_nP){return E(E(_nP).a);},_nQ=function(_nR){var _nS=E(_nR);return (_nS._==0)?__Z:new T2(1,new T(function(){return _nO(_nS.a);}),new T(function(){return _nQ(_nS.b);}));},_nT=function(_nU,_nV,_nW){return C > 19 ? new F(function(){return A1(_nU,new T3(0,_nV,new T(function(){return E(E(_nW).b);}),_2L));}) : (++C,A1(_nU,new T3(0,_nV,new T(function(){return E(E(_nW).b);}),_2L)));},_nX=function(_nY){return E(E(_nY).a);},_nZ=function(_o0,_o1){if(_o0<=0){if(_o0>=0){return quot(_o0,_o1);}else{if(_o1<=0){return quot(_o0,_o1);}else{return quot(_o0+1|0,_o1)-1|0;}}}else{if(_o1>=0){if(_o0>=0){return quot(_o0,_o1);}else{if(_o1<=0){return quot(_o0,_o1);}else{return quot(_o0+1|0,_o1)-1|0;}}}else{return quot(_o0-1|0,_o1)-1|0;}}},_o2=new T(function(){return unCStr("base");}),_o3=new T(function(){return unCStr("GHC.Exception");}),_o4=new T(function(){return unCStr("ArithException");}),_o5=function(_o6){return E(new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_o2,_o3,_o4),__Z,__Z));},_o7=new T(function(){return unCStr("Ratio has zero denominator");}),_o8=new T(function(){return unCStr("denormal");}),_o9=new T(function(){return unCStr("divide by zero");}),_oa=new T(function(){return unCStr("loss of precision");}),_ob=new T(function(){return unCStr("arithmetic underflow");}),_oc=new T(function(){return unCStr("arithmetic overflow");}),_od=function(_oe,_of){switch(E(_oe)){case 0:return _0(_oc,_of);case 1:return _0(_ob,_of);case 2:return _0(_oa,_of);case 3:return _0(_o9,_of);case 4:return _0(_o8,_of);default:return _0(_o7,_of);}},_og=function(_oh){return _od(_oh,__Z);},_oi=new T(function(){return new T5(0,_o5,new T3(0,function(_oj,_ok,_ol){return _od(_ok,_ol);},_og,function(_om,_on){return _1R(_od,_om,_on);}),_oo,function(_op){var _oq=E(_op);return _O(_M(_oq.a),_o5,_oq.b);},_og);}),_oo=function(_7c){return new T2(0,_oi,_7c);},_or=new T(function(){return die(new T(function(){return _oo(3);}));}),_os=new T(function(){return die(new T(function(){return _oo(0);}));}),_ot=function(_ou,_ov){var _ow=E(_ov);switch(_ow){case  -1:var _ox=E(_ou);if(_ox==( -2147483648)){return E(_os);}else{return _nZ(_ox, -1);}break;case 0:return E(_or);default:return _nZ(_ou,_ow);}},_oy=function(_oz,_oA){var _oB=new T(function(){var _oC=E(_oz);if(!_oC){return new T2(0,__Z,_oA);}else{var _oD=E(_oA);if(!_oD._){return E(new T2(0,__Z,__Z));}else{var _oE=new T(function(){var _oF=_oy(_oC-1|0,_oD.b);return new T2(0,_oF.a,_oF.b);});return new T2(0,new T2(1,_oD.a,new T(function(){return E(E(_oE).a);})),new T(function(){return E(E(_oE).b);}));}}});return new T2(0,new T(function(){return E(E(_oB).a);}),new T(function(){return E(E(_oB).b);}));},_oG=new T0(1),_oH=new T(function(){return unCStr("Failure in Data.Map.balance");}),_oI=new T(function(){var _oJ=_;return err(_oH);}),_oK=new T(function(){var _oL=_;return err(_oH);}),_oM=function(_oN,_oO,_oP,_oQ){var _oR=E(_oP);if(!_oR._){var _oS=_oR.a,_oT=_oR.b,_oU=_oR.c,_oV=_oR.d,_oW=_oR.e,_oX=E(_oQ);if(!_oX._){var _oY=_oX.a,_oZ=_oX.b,_p0=_oX.c;if(_oY<=(imul(3,_oS)|0)){if(_oS<=(imul(3,_oY)|0)){return new T5(0,(1+_oS|0)+_oY|0,E(_oN),_oO,_oR,_oX);}else{var _p1=E(_oV);if(!_p1._){var _p2=_p1.a,_p3=E(_oW);if(!_p3._){var _p4=_p3.a,_p5=_p3.b,_p6=_p3.c,_p7=_p3.d;if(_p4>=(imul(2,_p2)|0)){var _p8=function(_p9){var _pa=E(_p3.e);return (_pa._==0)?new T5(0,(1+_oS|0)+_oY|0,E(_p5),_p6,E(new T5(0,(1+_p2|0)+_p9|0,E(_oT),_oU,_p1,E(_p7))),E(new T5(0,(1+_oY|0)+_pa.a|0,E(_oN),_oO,_pa,_oX))):new T5(0,(1+_oS|0)+_oY|0,E(_p5),_p6,E(new T5(0,(1+_p2|0)+_p9|0,E(_oT),_oU,_p1,E(_p7))),E(new T5(0,1+_oY|0,E(_oN),_oO,E(_oG),_oX)));},_pb=E(_p7);if(!_pb._){return _p8(_pb.a);}else{return _p8(0);}}else{return new T5(0,(1+_oS|0)+_oY|0,E(_oT),_oU,_p1,E(new T5(0,(1+_oY|0)+_p4|0,E(_oN),_oO,_p3,_oX)));}}else{return E(_oI);}}else{return E(_oI);}}}else{var _pc=E(_oX.d);if(!_pc._){var _pd=_pc.a,_pe=_pc.b,_pf=_pc.c,_pg=_pc.d,_ph=E(_oX.e);if(!_ph._){var _pi=_ph.a;if(_pd>=(imul(2,_pi)|0)){var _pj=function(_pk){var _pl=E(_oN),_pm=E(_pc.e);return (_pm._==0)?new T5(0,(1+_oS|0)+_oY|0,E(_pe),_pf,E(new T5(0,(1+_oS|0)+_pk|0,_pl,_oO,_oR,E(_pg))),E(new T5(0,(1+_pi|0)+_pm.a|0,E(_oZ),_p0,_pm,_ph))):new T5(0,(1+_oS|0)+_oY|0,E(_pe),_pf,E(new T5(0,(1+_oS|0)+_pk|0,_pl,_oO,_oR,E(_pg))),E(new T5(0,1+_pi|0,E(_oZ),_p0,E(_oG),_ph)));},_pn=E(_pg);if(!_pn._){return _pj(_pn.a);}else{return _pj(0);}}else{return new T5(0,(1+_oS|0)+_oY|0,E(_oZ),_p0,E(new T5(0,(1+_oS|0)+_pd|0,E(_oN),_oO,_oR,_pc)),_ph);}}else{return E(_oK);}}else{return E(_oK);}}}else{var _po=E(_oV);if(!_po._){var _pp=_po.a,_pq=E(_oW);if(!_pq._){var _pr=_pq.a,_ps=_pq.b,_pt=_pq.c,_pu=_pq.d;if(_pr>=(imul(2,_pp)|0)){var _pv=function(_pw){var _px=E(_pq.e);return (_px._==0)?new T5(0,1+_oS|0,E(_ps),_pt,E(new T5(0,(1+_pp|0)+_pw|0,E(_oT),_oU,_po,E(_pu))),E(new T5(0,1+_px.a|0,E(_oN),_oO,_px,E(_oG)))):new T5(0,1+_oS|0,E(_ps),_pt,E(new T5(0,(1+_pp|0)+_pw|0,E(_oT),_oU,_po,E(_pu))),E(new T5(0,1,E(_oN),_oO,E(_oG),E(_oG))));},_py=E(_pu);if(!_py._){return _pv(_py.a);}else{return _pv(0);}}else{return new T5(0,1+_oS|0,E(_oT),_oU,_po,E(new T5(0,1+_pr|0,E(_oN),_oO,_pq,E(_oG))));}}else{return new T5(0,3,E(_oT),_oU,_po,E(new T5(0,1,E(_oN),_oO,E(_oG),E(_oG))));}}else{var _pz=E(_oW);return (_pz._==0)?new T5(0,3,E(_pz.b),_pz.c,E(new T5(0,1,E(_oT),_oU,E(_oG),E(_oG))),E(new T5(0,1,E(_oN),_oO,E(_oG),E(_oG)))):new T5(0,2,E(_oN),_oO,_oR,E(_oG));}}}else{var _pA=E(_oQ);if(!_pA._){var _pB=_pA.a,_pC=_pA.b,_pD=_pA.c,_pE=_pA.e,_pF=E(_pA.d);if(!_pF._){var _pG=_pF.a,_pH=_pF.b,_pI=_pF.c,_pJ=_pF.d,_pK=E(_pE);if(!_pK._){var _pL=_pK.a;if(_pG>=(imul(2,_pL)|0)){var _pM=function(_pN){var _pO=E(_oN),_pP=E(_pF.e);return (_pP._==0)?new T5(0,1+_pB|0,E(_pH),_pI,E(new T5(0,1+_pN|0,_pO,_oO,E(_oG),E(_pJ))),E(new T5(0,(1+_pL|0)+_pP.a|0,E(_pC),_pD,_pP,_pK))):new T5(0,1+_pB|0,E(_pH),_pI,E(new T5(0,1+_pN|0,_pO,_oO,E(_oG),E(_pJ))),E(new T5(0,1+_pL|0,E(_pC),_pD,E(_oG),_pK)));},_pQ=E(_pJ);if(!_pQ._){return _pM(_pQ.a);}else{return _pM(0);}}else{return new T5(0,1+_pB|0,E(_pC),_pD,E(new T5(0,1+_pG|0,E(_oN),_oO,E(_oG),_pF)),_pK);}}else{return new T5(0,3,E(_pH),_pI,E(new T5(0,1,E(_oN),_oO,E(_oG),E(_oG))),E(new T5(0,1,E(_pC),_pD,E(_oG),E(_oG))));}}else{var _pR=E(_pE);return (_pR._==0)?new T5(0,3,E(_pC),_pD,E(new T5(0,1,E(_oN),_oO,E(_oG),E(_oG))),_pR):new T5(0,2,E(_oN),_oO,E(_oG),_pA);}}else{return new T5(0,1,E(_oN),_oO,E(_oG),E(_oG));}}},_pS=function(_pT){return E(E(_pT).b);},_pU=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_pV=new T(function(){var _pW=_;return err(_pU);}),_pX=function(_pY,_pZ,_q0,_q1){var _q2=E(_q1);if(!_q2._){var _q3=_q2.a,_q4=E(_q0);if(!_q4._){var _q5=_q4.a,_q6=_q4.b,_q7=_q4.c;if(_q5<=(imul(3,_q3)|0)){return new T5(0,(1+_q5|0)+_q3|0,E(_pY),_pZ,_q4,_q2);}else{var _q8=E(_q4.d);if(!_q8._){var _q9=_q8.a,_qa=E(_q4.e);if(!_qa._){var _qb=_qa.a,_qc=_qa.b,_qd=_qa.c,_qe=_qa.d;if(_qb>=(imul(2,_q9)|0)){var _qf=function(_qg){var _qh=E(_qa.e);return (_qh._==0)?new T5(0,(1+_q5|0)+_q3|0,E(_qc),_qd,E(new T5(0,(1+_q9|0)+_qg|0,E(_q6),_q7,_q8,E(_qe))),E(new T5(0,(1+_q3|0)+_qh.a|0,E(_pY),_pZ,_qh,_q2))):new T5(0,(1+_q5|0)+_q3|0,E(_qc),_qd,E(new T5(0,(1+_q9|0)+_qg|0,E(_q6),_q7,_q8,E(_qe))),E(new T5(0,1+_q3|0,E(_pY),_pZ,E(_oG),_q2)));},_qi=E(_qe);if(!_qi._){return _qf(_qi.a);}else{return _qf(0);}}else{return new T5(0,(1+_q5|0)+_q3|0,E(_q6),_q7,_q8,E(new T5(0,(1+_q3|0)+_qb|0,E(_pY),_pZ,_qa,_q2)));}}else{return E(_pV);}}else{return E(_pV);}}}else{return new T5(0,1+_q3|0,E(_pY),_pZ,E(_oG),_q2);}}else{var _qj=E(_q0);if(!_qj._){var _qk=_qj.a,_ql=_qj.b,_qm=_qj.c,_qn=_qj.e,_qo=E(_qj.d);if(!_qo._){var _qp=_qo.a,_qq=E(_qn);if(!_qq._){var _qr=_qq.a,_qs=_qq.b,_qt=_qq.c,_qu=_qq.d;if(_qr>=(imul(2,_qp)|0)){var _qv=function(_qw){var _qx=E(_qq.e);return (_qx._==0)?new T5(0,1+_qk|0,E(_qs),_qt,E(new T5(0,(1+_qp|0)+_qw|0,E(_ql),_qm,_qo,E(_qu))),E(new T5(0,1+_qx.a|0,E(_pY),_pZ,_qx,E(_oG)))):new T5(0,1+_qk|0,E(_qs),_qt,E(new T5(0,(1+_qp|0)+_qw|0,E(_ql),_qm,_qo,E(_qu))),E(new T5(0,1,E(_pY),_pZ,E(_oG),E(_oG))));},_qy=E(_qu);if(!_qy._){return _qv(_qy.a);}else{return _qv(0);}}else{return new T5(0,1+_qk|0,E(_ql),_qm,_qo,E(new T5(0,1+_qr|0,E(_pY),_pZ,_qq,E(_oG))));}}else{return new T5(0,3,E(_ql),_qm,_qo,E(new T5(0,1,E(_pY),_pZ,E(_oG),E(_oG))));}}else{var _qz=E(_qn);return (_qz._==0)?new T5(0,3,E(_qz.b),_qz.c,E(new T5(0,1,E(_ql),_qm,E(_oG),E(_oG))),E(new T5(0,1,E(_pY),_pZ,E(_oG),E(_oG)))):new T5(0,2,E(_pY),_pZ,_qj,E(_oG));}}else{return new T5(0,1,E(_pY),_pZ,E(_oG),E(_oG));}}},_qA=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_qB=new T(function(){var _qC=_;return err(_qA);}),_qD=function(_qE,_qF,_qG,_qH){var _qI=E(_qG);if(!_qI._){var _qJ=_qI.a,_qK=E(_qH);if(!_qK._){var _qL=_qK.a,_qM=_qK.b,_qN=_qK.c;if(_qL<=(imul(3,_qJ)|0)){return new T5(0,(1+_qJ|0)+_qL|0,E(_qE),_qF,_qI,_qK);}else{var _qO=E(_qK.d);if(!_qO._){var _qP=_qO.a,_qQ=_qO.b,_qR=_qO.c,_qS=_qO.d,_qT=E(_qK.e);if(!_qT._){var _qU=_qT.a;if(_qP>=(imul(2,_qU)|0)){var _qV=function(_qW){var _qX=E(_qE),_qY=E(_qO.e);return (_qY._==0)?new T5(0,(1+_qJ|0)+_qL|0,E(_qQ),_qR,E(new T5(0,(1+_qJ|0)+_qW|0,_qX,_qF,_qI,E(_qS))),E(new T5(0,(1+_qU|0)+_qY.a|0,E(_qM),_qN,_qY,_qT))):new T5(0,(1+_qJ|0)+_qL|0,E(_qQ),_qR,E(new T5(0,(1+_qJ|0)+_qW|0,_qX,_qF,_qI,E(_qS))),E(new T5(0,1+_qU|0,E(_qM),_qN,E(_oG),_qT)));},_qZ=E(_qS);if(!_qZ._){return _qV(_qZ.a);}else{return _qV(0);}}else{return new T5(0,(1+_qJ|0)+_qL|0,E(_qM),_qN,E(new T5(0,(1+_qJ|0)+_qP|0,E(_qE),_qF,_qI,_qO)),_qT);}}else{return E(_qB);}}else{return E(_qB);}}}else{return new T5(0,1+_qJ|0,E(_qE),_qF,_qI,E(_oG));}}else{var _r0=E(_qH);if(!_r0._){var _r1=_r0.a,_r2=_r0.b,_r3=_r0.c,_r4=_r0.e,_r5=E(_r0.d);if(!_r5._){var _r6=_r5.a,_r7=_r5.b,_r8=_r5.c,_r9=_r5.d,_ra=E(_r4);if(!_ra._){var _rb=_ra.a;if(_r6>=(imul(2,_rb)|0)){var _rc=function(_rd){var _re=E(_qE),_rf=E(_r5.e);return (_rf._==0)?new T5(0,1+_r1|0,E(_r7),_r8,E(new T5(0,1+_rd|0,_re,_qF,E(_oG),E(_r9))),E(new T5(0,(1+_rb|0)+_rf.a|0,E(_r2),_r3,_rf,_ra))):new T5(0,1+_r1|0,E(_r7),_r8,E(new T5(0,1+_rd|0,_re,_qF,E(_oG),E(_r9))),E(new T5(0,1+_rb|0,E(_r2),_r3,E(_oG),_ra)));},_rg=E(_r9);if(!_rg._){return _rc(_rg.a);}else{return _rc(0);}}else{return new T5(0,1+_r1|0,E(_r2),_r3,E(new T5(0,1+_r6|0,E(_qE),_qF,E(_oG),_r5)),_ra);}}else{return new T5(0,3,E(_r7),_r8,E(new T5(0,1,E(_qE),_qF,E(_oG),E(_oG))),E(new T5(0,1,E(_r2),_r3,E(_oG),E(_oG))));}}else{var _rh=E(_r4);return (_rh._==0)?new T5(0,3,E(_r2),_r3,E(new T5(0,1,E(_qE),_qF,E(_oG),E(_oG))),_rh):new T5(0,2,E(_qE),_qF,E(_oG),_r0);}}else{return new T5(0,1,E(_qE),_qF,E(_oG),E(_oG));}}},_ri=function(_rj,_rk,_rl,_rm,_rn){var _ro=E(_rn);if(!_ro._){var _rp=new T(function(){var _rq=_ri(_ro.a,_ro.b,_ro.c,_ro.d,_ro.e);return new T2(0,_rq.a,_rq.b);});return new T2(0,new T(function(){return E(E(_rp).a);}),new T(function(){return _pX(_rk,_rl,_rm,E(_rp).b);}));}else{return new T2(0,new T2(0,_rk,_rl),_rm);}},_rr=function(_rs,_rt,_ru,_rv,_rw){var _rx=E(_rv);if(!_rx._){var _ry=new T(function(){var _rz=_rr(_rx.a,_rx.b,_rx.c,_rx.d,_rx.e);return new T2(0,_rz.a,_rz.b);});return new T2(0,new T(function(){return E(E(_ry).a);}),new T(function(){return _qD(_rt,_ru,E(_ry).b,_rw);}));}else{return new T2(0,new T2(0,_rt,_ru),_rw);}},_rA=function(_rB,_rC){var _rD=E(_rB);if(!_rD._){var _rE=_rD.a,_rF=E(_rC);if(!_rF._){var _rG=_rF.a;if(_rE<=_rG){var _rH=_rr(_rG,_rF.b,_rF.c,_rF.d,_rF.e),_rI=E(_rH.a);return _pX(_rI.a,_rI.b,_rD,_rH.b);}else{var _rJ=_ri(_rE,_rD.b,_rD.c,_rD.d,_rD.e),_rK=E(_rJ.a);return _qD(_rK.a,_rK.b,_rJ.b,_rF);}}else{return _rD;}}else{return E(_rC);}},_rL=function(_rM,_rN,_rO,_rP){var _rQ=E(_rO),_rR=E(_rP);if(!_rR._){var _rS=_rR.b,_rT=_rR.c,_rU=_rR.d,_rV=_rR.e;switch(B(A3(_pS,_rM,_rQ,_rS))){case 0:return _oM(_rS,_rT,B(_rL(_rM,_rN,_rQ,_rU)),_rV);case 1:var _rW=B(A1(_rN,new T1(1,_rT)));if(!_rW._){return _rA(_rU,_rV);}else{return new T5(0,_rR.a,E(_rS),_rW.a,E(_rU),E(_rV));}break;default:return _oM(_rS,_rT,_rU,B(_rL(_rM,_rN,_rQ,_rV)));}}else{var _rX=B(A1(_rN,__Z));return (_rX._==0)?new T0(1):new T5(0,1,_rQ,_rX.a,E(_oG),E(_oG));}},_rY=function(_rZ,_s0,_s1,_s2){return C > 19 ? new F(function(){return _rL(_rZ,_s0,_s1,_s2);}) : (++C,_rL(_rZ,_s0,_s1,_s2));},_s3=function(_s4,_s5){return E(_s5);},_s6=function(_s7){return E(E(_s7).b);},_s8=function(_s9){return E(E(_s9).b);},_sa=function(_sb,_sc,_sd){var _se=function(_sf,_sg){while(1){var _sh=E(_sf),_si=E(_sg);if(!_si._){switch(B(A3(_pS,_sb,_sh,_si.b))){case 0:_sf=_sh;_sg=_si.d;continue;case 1:return new T1(1,_si.c);default:_sf=_sh;_sg=_si.e;continue;}}else{return __Z;}}};return _se(_sc,_sd);},_sj=function(_sk){var _sl=E(_sk);return new T5(0,_sl.a,_sl.b,new T(function(){return E(_sl.c)+1|0;}),_sl.d,_sl.e);},_sm=function(_sn){var _so=E(_sn);return new T5(0,_so.a,_so.b,new T(function(){return E(_so.c)-1|0;}),_so.d,_so.e);},_sp=function(_sq){var _sr=E(_sq);return new T5(0,_sr.a,__Z,_sr.c,_sr.d,_sr.e);},_ss=function(_st,_su){while(1){var _sv=E(_st);if(!_sv._){return E(_su);}else{var _sw=new T2(1,_sv.a,_su);_st=_sv.b;_su=_sw;continue;}}},_sx=function(_sy,_sz){return E(_sz);},_sA=function(_sB,_sC,_sD,_sE,_sF){var _sG=_5b(_sC),_sH=new T(function(){return _2P(_sG);}),_sI=new T(function(){return _2T(_sH);}),_sJ=new T(function(){return B(A2(_5k,_sC,function(_sK){var _sL=E(_sK);return new T5(0,_sL.a,new T2(1,_sF,_sL.b),_sL.c,_sL.d,_sL.e);}));}),_sM=new T(function(){return B(A2(_5k,_sC,function(_sN){var _sO=E(_sN);return new T5(0,new T2(1,new T1(2,_sF),_sO.a),_sO.b,_sO.c,_sO.d,_sO.e);}));}),_sP=new T(function(){return B(A3(_2R,_sI,_s3,new T(function(){return B(A2(_5k,_sC,_sj));})));}),_sQ=new T(function(){return B(A3(_2R,_sI,_s3,new T(function(){return B(A2(_5k,_sC,_sm));})));}),_sR=new T(function(){return B(A2(_5k,_sC,_sp));}),_sS=new T(function(){return B(A2(_s8,_sB,_sF));}),_sT=new T(function(){return _nX(_sB);}),_sU=new T(function(){return B(A2(_2V,_sH,0));}),_sV=new T(function(){return B(A2(_2V,_sH,0));}),_sW=new T(function(){return _s6(_sI);}),_sX=new T(function(){return B(A2(_2R,_sI,_sx));}),_sY=function(_sZ){var _t0=E(_sZ);if(!_t0._){return __Z;}else{var _t1=new T(function(){return B(A1(_sW,new T(function(){return B(A1(_sX,_t0.a));})));});return new T2(1,_t1,new T(function(){return _sY(_t0.b);}));}},_t2=function(_t3){var _t4=E(_t3);return (_t4._==0)?__Z:new T2(1,new T(function(){return B(_sA(_sB,_sC,_sD,_sE,_t4.a));}),new T(function(){return _t2(_t4.b);}));},_t5=function(_t6){var _t7=function(_t8){var _t9=E(_t6);if(!E(_t9.c)){var _ta=_sa(_sT,_sF,_t9.d);if(!_ta._){return E(_sM);}else{var _tb=E(_ta.a);switch(_tb._){case 0:return C > 19 ? new F(function(){return A1(_sD,_tb.a);}) : (++C,A1(_sD,_tb.a));break;case 5:return C > 19 ? new F(function(){return A3(_2B,_6h,_sY(_t2(_tb.a)),_sV);}) : (++C,A3(_2B,_6h,_sY(_t2(_tb.a)),_sV));break;default:return C > 19 ? new F(function(){return A2(_5k,_sC,function(_tc){var _td=E(_tc);return new T5(0,new T2(1,_tb,_td.a),_td.b,_td.c,_td.d,_td.e);});}) : (++C,A2(_5k,_sC,function(_tc){var _td=E(_tc);return new T5(0,new T2(1,_tb,_td.a),_td.b,_td.c,_td.d,_td.e);}));}}}else{return E(_sJ);}},_te=E(_sS);switch(_te._){case 0:return C > 19 ? new F(function(){return A3(_s6,_sI,_sP,new T(function(){if(E(E(_t6).c)<=0){return E(_sU);}else{return E(_sJ);}}));}) : (++C,A3(_s6,_sI,_sP,new T(function(){if(E(E(_t6).c)<=0){return E(_sU);}else{return E(_sJ);}})));break;case 1:var _tf=new T(function(){var _tg=E(_t6);if(E(_tg.c)==1){var _th=new T(function(){var _ti=new T(function(){var _tj=new T(function(){return _ss(_tg.b,__Z);});return B(A2(_5k,_sC,function(_tk){var _tl=E(_tk);return new T5(0,new T2(1,new T1(5,_tj),_tl.a),_tl.b,_tl.c,_tl.d,_tl.e);}));});return B(A3(_2R,_sI,_s3,_ti));});return B(A3(_s6,_sI,_th,_sR));}else{return E(_sJ);}});return C > 19 ? new F(function(){return A3(_s6,_sI,_sQ,_tf);}) : (++C,A3(_s6,_sI,_sQ,_tf));break;case 2:if(!E(E(_t6).c)){return C > 19 ? new F(function(){return A2(_5k,_sC,function(_tm){var _tn=E(_tm);return new T5(0,new T2(1,new T1(1,_te.a),_tn.a),_tn.b,_tn.c,_tn.d,_tn.e);});}) : (++C,A2(_5k,_sC,function(_tm){var _tn=E(_tm);return new T5(0,new T2(1,new T1(1,_te.a),_tn.a),_tn.b,_tn.c,_tn.d,_tn.e);}));}else{return C > 19 ? new F(function(){return _t7(_);}) : (++C,_t7(_));}break;case 3:if(!E(E(_t6).c)){return C > 19 ? new F(function(){return A2(_5k,_sC,function(_to){var _tp=E(_to);return new T5(0,new T2(1,new T1(2,_te.a),_tp.a),_tp.b,_tp.c,_tp.d,_tp.e);});}) : (++C,A2(_5k,_sC,function(_to){var _tp=E(_to);return new T5(0,new T2(1,new T1(2,_te.a),_tp.a),_tp.b,_tp.c,_tp.d,_tp.e);}));}else{return C > 19 ? new F(function(){return _t7(_);}) : (++C,_t7(_));}break;case 4:return C > 19 ? new F(function(){return A1(_sE,_te.a);}) : (++C,A1(_sE,_te.a));break;default:return C > 19 ? new F(function(){return _t7(_);}) : (++C,_t7(_));}};return C > 19 ? new F(function(){return A3(_2X,_sG,new T(function(){return _5d(_sC);}),_t5);}) : (++C,A3(_2X,_sG,new T(function(){return _5d(_sC);}),_t5));},_tq=function(_tr){return E(_tr);},_ts=function(_tt){return new T3(0,_tq,new T(function(){return E(E(_tt).b);}),new T(function(){return E(E(_tt).c);}));},_tu=new T(function(){return unCStr("Irrefutable pattern failed for pattern");}),_tv=function(_tw){return _7a(new T1(0,new T(function(){return _7n(_tw,_tu);})),_6X);},_tx=new T(function(){return B(_tv("src/Algebra/Monad/Concatenative.hs:(95,46)-(97,93)|(h, _ : t)"));}),_ty=function(_tz){return __Z;},_tA=function(_tB){return new T3(0,new T(function(){return E(E(E(_tB).a).d);}),new T(function(){return E(E(_tB).b);}),new T(function(){return E(E(_tB).c);}));},_tC=function(_tD,_tE){var _tF=_tD%_tE;if(_tD<=0){if(_tD>=0){return _tF;}else{if(_tE<=0){return _tF;}else{return (_tF==0)?0:_tF+_tE|0;}}}else{if(_tE>=0){if(_tD>=0){return _tF;}else{if(_tE<=0){return _tF;}else{return (_tF==0)?0:_tF+_tE|0;}}}else{return (_tF==0)?0:_tF+_tE|0;}}},_tG=function(_tH){var _tI=E(_tH);if(!_tI._){return new T2(0,__Z,__Z);}else{var _tJ=_tI.b,_tK=E(_tI.a);if(!_tK._){if(!E(_tK.a)._){return new T2(0,__Z,_tI);}else{var _tL=new T(function(){var _tM=_tG(_tJ);return new T2(0,_tM.a,_tM.b);});return new T2(0,new T2(1,_tK,new T(function(){return E(E(_tL).a);})),new T(function(){return E(E(_tL).b);}));}}else{var _tN=new T(function(){var _tO=_tG(_tJ);return new T2(0,_tO.a,_tO.b);});return new T2(0,new T2(1,_tK,new T(function(){return E(E(_tN).a);})),new T(function(){return E(E(_tN).b);}));}}},_tP=function(_tQ){var _tR=E(_tQ);return (_tR._==0)?__Z:new T2(1,new T1(2,_tR.a),new T(function(){return _tP(_tR.b);}));},_tS=function(_tT){while(1){var _tU=(function(_tV){var _tW=E(_tV);if(!_tW._){return __Z;}else{var _tX=_tW.b,_tY=E(_tW.a);if(_tY._==2){return new T2(1,_tY.a,new T(function(){return _tS(_tX);}));}else{_tT=_tX;return __continue;}}})(_tT);if(_tU!=__continue){return _tU;}}},_tZ=function(_u0,_u1,_u2){var _u3=new T(function(){return B(A1(_u1,new T(function(){return E(E(_u2).a);})));});return C > 19 ? new F(function(){return A2(_u0,function(_u4){var _u5=E(_u2);return new T5(0,_u4,_u5.b,_u5.c,_u5.d,_u5.e);},_u3);}) : (++C,A2(_u0,function(_u4){var _u5=E(_u2);return new T5(0,_u4,_u5.b,_u5.c,_u5.d,_u5.e);},_u3));},_u6=function(_u7,_u8){var _u9=new T(function(){return _2P(_u8);}),_ua=new T(function(){return _2V(_u9);}),_ub=function(_uc){return C > 19 ? new F(function(){return A1(_ua,new T3(0,0,new T(function(){return E(E(_uc).b);}),_2L));}) : (++C,A1(_ua,new T3(0,0,new T(function(){return E(E(_uc).b);}),_2L)));},_ud=new T(function(){return _2R(new T(function(){return _2T(_u9);}));}),_ue=new T(function(){return B(A1(_ud,_ts));}),_uf=new T(function(){return _no(new T(function(){return _nx(new T(function(){return _mN(function(_ug,_uh){return C > 19 ? new F(function(){return _nT(_ua,_ug,_uh);}) : (++C,_nT(_ua,_ug,_uh));},new T(function(){return _nC(function(_ug,_uh){return _mY(_ud,_ug,_uh);},_u8);}),_u8);}),_u8);}),_u8);}),_ui=function(_uj){return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,new T(function(){var _uk=E(E(_uj).b);return new T5(0,new T2(1,new T1(0,__Z),_uk.a),_uk.b,_uk.c,_uk.d,_uk.e);}),_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,new T(function(){var _uk=E(E(_uj).b);return new T5(0,new T2(1,new T1(0,__Z),_uk.a),_uk.b,_uk.c,_uk.d,_uk.e);}),_2L)));},_ul=function(_um){var _un=new T(function(){var _uo=E(E(_um).b),_up=new T(function(){var _uq=_tG(_uo.a),_ur=E(_uq.b);if(!_ur._){return E(_tx);}else{return new T2(0,_uq.a,_ur.b);}});return new T5(0,new T2(1,new T1(3,new T(function(){return _ss(E(_up).a,__Z);})),new T(function(){return E(E(_up).b);})),_uo.b,_uo.c,_uo.d,_uo.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_un,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_un,_2L)));},_us=function(_ut){return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,new T(function(){var _uu=E(E(_ut).b);return new T5(0,__Z,_uu.b,_uu.c,_uu.d,_uu.e);}),_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,new T(function(){var _uu=E(E(_ut).b);return new T5(0,__Z,_uu.b,_uu.c,_uu.d,_uu.e);}),_2L)));},_uv=function(_uw){return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,new T(function(){var _ux=E(E(_uw).b),_uy=_ux.a;return new T5(0,new T2(1,new T1(3,_uy),_uy),_ux.b,_ux.c,_ux.d,_ux.e);}),_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,new T(function(){var _ux=E(E(_uw).b),_uy=_ux.a;return new T5(0,new T2(1,new T1(3,_uy),_uy),_ux.b,_ux.c,_ux.d,_ux.e);}),_2L)));},_uz=function(_uA){var _uB=new T(function(){var _uC=E(E(_uA).b),_uD=new T(function(){var _uE=E(_uC.a);if(!_uE._){return __Z;}else{var _uF=E(_uE.a);if(_uF._==1){var _uG=E(_uE.b);if(!_uG._){return _uE;}else{var _uH=E(_uG.a);if(_uH._==1){var _uI=E(_uF.a),_uJ=E(_uH.a);if(_uI>=_uJ){return _uE;}else{var _uK=E(_oy(_uI,_uG.b).b);if(!_uK._){return _uE;}else{return new T2(1,_uK.a,new T(function(){return E(_oy((_uJ-_uI|0)-1|0,_uK.b).b);}));}}}else{return _uE;}}}else{return _uE;}}});return new T5(0,_uD,_uC.b,_uC.c,_uC.d,_uC.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_uB,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_uB,_2L)));},_uL=function(_uM){var _uN=new T(function(){var _uO=E(E(_uM).b);return new T5(0,new T(function(){return E(_oy(1,_uO.a).b);}),_uO.b,_uO.c,_uO.d,_uO.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_uN,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_uN,_2L)));},_uP=function(_uQ){var _uR=new T(function(){var _uS=E(E(_uQ).b);return new T5(0,new T(function(){var _uT=E(_uS.a);if(!_uT._){return __Z;}else{var _uU=E(_uT.a);if(_uU._==1){var _uV=_oy(_uU.a,_uT.b),_uW=E(_uV.b);if(!_uW._){return _uT;}else{return _nK(_uV.a,_uW.b);}}else{return _uT;}}}),_uS.b,_uS.c,_uS.d,_uS.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_uR,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_uR,_2L)));},_uX=function(_uY){var _uZ=new T(function(){var _v0=E(E(_uY).b);return new T5(0,new T(function(){var _v1=E(_v0.a);if(!_v1._){return __Z;}else{return new T2(1,_v1.a,_v1);}}),_v0.b,_v0.c,_v0.d,_v0.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_uZ,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_uZ,_2L)));},_v2=function(_v3){var _v4=new T(function(){var _v5=E(E(_v3).b);return new T5(0,new T(function(){var _v6=E(_v5.a);if(!_v6._){return __Z;}else{var _v7=_v6.b,_v8=E(_v6.a);if(_v8._==1){var _v9=E(_oy(_v8.a,_v7).b);if(!_v9._){return _v6;}else{return new T2(1,_v9.a,_v7);}}else{return _v6;}}}),_v5.b,_v5.c,_v5.d,_v5.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_v4,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_v4,_2L)));},_va=function(_vb){var _vc=new T(function(){var _vd=E(E(_vb).b);return new T5(0,new T(function(){var _ve=E(_vd.a);if(!_ve._){return __Z;}else{var _vf=E(_ve.b);if(!_vf._){return _ve;}else{return new T2(1,_vf.a,new T2(1,_ve.a,_vf.b));}}}),_vd.b,_vd.c,_vd.d,_vd.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_vc,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_vc,_2L)));},_vg=function(_vh){var _vi=new T(function(){var _vj=E(E(_vh).b),_vk=new T(function(){var _vl=E(_vj.a);if(!_vl._){return __Z;}else{var _vm=E(_vl.a);if(_vm._==1){var _vn=_oy(new T(function(){return E(_vm.a)+1|0;},1),_vl.b),_vo=E(_vn.a);if(!_vo._){return _vl;}else{var _vp=E(_vn.b);if(!_vp._){return _vl;}else{return new T2(1,_vp.a,new T(function(){return _nK(_vo.b,new T2(1,_vo.a,_vp.b));}));}}}else{return _vl;}}});return new T5(0,_vk,_vj.b,_vj.c,_vj.d,_vj.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_vi,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_vi,_2L)));},_vq=function(_vr){var _vs=new T(function(){var _vt=E(E(_vr).b),_vu=new T(function(){var _vv=E(_vt.a);if(!_vv._){return __Z;}else{var _vw=E(_vv.a);if(_vw._==1){var _vx=new T(function(){var _vy=E(_vw.a)-1|0;if(0<=_vy){var _vz=function(_vA){return new T2(1,new T1(1,_vA),new T(function(){if(_vA!=_vy){return _vz(_vA+1|0);}else{return __Z;}}));};return _vz(0);}else{return __Z;}});return new T2(1,new T1(3,_vx),_vv.b);}else{return _vv;}}});return new T5(0,_vu,_vt.b,_vt.c,_vt.d,_vt.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_vs,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_vs,_2L)));},_vB=function(_vC){var _vD=new T(function(){var _vE=E(E(_vC).b),_vF=new T(function(){var _vG=E(_vE.a);if(!_vG._){return __Z;}else{var _vH=E(_vG.a);if(_vH._==1){var _vI=E(_vG.b);if(!_vI._){return _vG;}else{var _vJ=E(_vI.a);if(_vJ._==1){return new T2(1,new T1(1,new T(function(){return E(_vJ.a)+E(_vH.a)|0;})),_vI.b);}else{return _vG;}}}else{return _vG;}}});return new T5(0,_vF,_vE.b,_vE.c,_vE.d,_vE.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_vD,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_vD,_2L)));},_vK=function(_vL){var _vM=new T(function(){var _vN=E(E(_vL).b),_vO=new T(function(){var _vP=E(_vN.a);if(!_vP._){return __Z;}else{var _vQ=E(_vP.a);if(_vQ._==1){var _vR=E(_vP.b);if(!_vR._){return _vP;}else{var _vS=E(_vR.a);if(_vS._==1){return new T2(1,new T1(1,new T(function(){return E(_vS.a)-E(_vQ.a)|0;})),_vR.b);}else{return _vP;}}}else{return _vP;}}});return new T5(0,_vO,_vN.b,_vN.c,_vN.d,_vN.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_vM,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_vM,_2L)));},_vT=function(_vU){var _vV=new T(function(){var _vW=E(E(_vU).b),_vX=new T(function(){var _vY=E(_vW.a);if(!_vY._){return __Z;}else{var _vZ=E(_vY.a);if(_vZ._==1){var _w0=E(_vY.b);if(!_w0._){return _vY;}else{var _w1=E(_w0.a);if(_w1._==1){return new T2(1,new T1(1,new T(function(){return imul(E(_w1.a),E(_vZ.a))|0;})),_w0.b);}else{return _vY;}}}else{return _vY;}}});return new T5(0,_vX,_vW.b,_vW.c,_vW.d,_vW.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_vV,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_vV,_2L)));},_w2=function(_w3){var _w4=new T(function(){var _w5=E(E(_w3).b),_w6=new T(function(){var _w7=E(_w5.a);if(!_w7._){return __Z;}else{var _w8=E(_w7.a);if(_w8._==1){var _w9=E(_w7.b);if(!_w9._){return _w7;}else{var _wa=E(_w9.a);if(_wa._==1){return new T2(1,new T1(1,new T(function(){return _ot(E(_wa.a),E(_w8.a));})),_w9.b);}else{return _w7;}}}else{return _w7;}}});return new T5(0,_w6,_w5.b,_w5.c,_w5.d,_w5.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_w4,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_w4,_2L)));},_wb=function(_wc){var _wd=new T(function(){var _we=E(E(_wc).b),_wf=new T(function(){var _wg=E(_we.a);if(!_wg._){return __Z;}else{var _wh=E(_wg.a);if(_wh._==1){var _wi=E(_wg.b);if(!_wi._){return _wg;}else{var _wj=E(_wi.a);if(_wj._==1){return new T2(1,new T1(1,new T(function(){var _wk=E(_wh.a);switch(_wk){case  -1:return 0;break;case 0:return E(_or);break;default:return _tC(E(_wj.a),_wk);}})),_wi.b);}else{return _wg;}}}else{return _wg;}}});return new T5(0,_wf,_we.b,_we.c,_we.d,_we.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_wd,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_wd,_2L)));},_wl=function(_wm){var _wn=new T(function(){var _wo=E(E(_wm).b),_wp=new T(function(){var _wq=E(_wo.a);if(!_wq._){return __Z;}else{var _wr=E(_wq.a);if(_wr._==1){return new T2(1,new T1(1,new T(function(){var _ws=E(_wr.a);if(_ws>=0){if(!_ws){return 0;}else{return 1;}}else{return  -1;}})),_wq.b);}else{return _wq;}}});return new T5(0,_wp,_wo.b,_wo.c,_wo.d,_wo.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_wn,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_wn,_2L)));},_wt=new T(function(){return _nX(_u7);}),_wu=new T(function(){var _wv=function(_ww){var _wx=function(_wy){var _wz=new T(function(){var _wA=E(E(_wy).b),_wB=new T(function(){var _wC=E(_wA.a);if(!_wC._){return __Z;}else{var _wD=E(_wC.a);if(_wD._==2){return new T2(1,new T(function(){var _wE=_sa(_wt,_wD.a,E(E(_ww).a).d);if(!_wE._){return _wD;}else{return E(_wE.a);}}),_wC.b);}else{return _wC;}}});return new T5(0,_wB,_wA.b,_wA.c,_wA.d,_wA.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_wz,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_wz,_2L)));};return new T3(0,_wx,new T(function(){return E(E(_ww).b);}),new T(function(){return E(E(_ww).c);}));};return B(A1(_ud,_wv));}),_wF=function(_wG){var _wH=new T(function(){var _wI=new T(function(){return E(E(_wG).b);});return B(A2(_2V,_u9,new T3(0,_wI,_wI,_2L)));});return C > 19 ? new F(function(){return A1(_wu,_wH);}) : (++C,A1(_wu,_wH));},_wJ=function(_wK){return C > 19 ? new F(function(){return _2Z(_2M,_u8,_wF,_wK);}) : (++C,_2Z(_2M,_u8,_wF,_wK));},_wL=new T(function(){var _wM=function(_wN){var _wO=new T(function(){var _wP=E(E(E(_wN).a).a);if(!_wP._){return _ub;}else{var _wQ=E(_wP.b);if(!_wQ._){return _ub;}else{var _wR=E(_wQ.a);if(_wR._==2){var _wS=function(_wT){return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,new T(function(){var _wU=E(E(_wT).b);return new T5(0,_wQ.b,_wU.b,_wU.c,_wU.d,_wU.e);}),_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,new T(function(){var _wU=E(E(_wT).b);return new T5(0,_wQ.b,_wU.b,_wU.c,_wU.d,_wU.e);}),_2L)));},_wV=function(_wW){return new T1(1,_wP.a);},_wX=function(_wY){var _wZ=new T(function(){var _x0=new T(function(){var _x1=E(E(_wY).b);return new T5(0,_x1.a,_x1.b,_x1.c,new T(function(){return B(_rY(_wt,_wV,_wR.a,_x1.d));}),_x1.e);});return B(A2(_2V,_u9,new T3(0,0,_x0,_2L)));});return C > 19 ? new F(function(){return A1(_ue,_wZ);}) : (++C,A1(_ue,_wZ));};return _3f(_u8,_wX,_wS);}else{return _ub;}}}});return new T3(0,_wO,new T(function(){return E(E(_wN).b);}),new T(function(){return E(E(_wN).c);}));};return B(A1(_ud,_wM));}),_x2=function(_x3){var _x4=new T(function(){var _x5=new T(function(){return E(E(_x3).b);});return B(A2(_2V,_u9,new T3(0,_x5,_x5,_2L)));});return C > 19 ? new F(function(){return A1(_wL,_x4);}) : (++C,A1(_wL,_x4));},_x6=function(_x7){return C > 19 ? new F(function(){return _2Z(_2M,_u8,_x2,_x7);}) : (++C,_2Z(_2M,_u8,_x2,_x7));},_x8=new T(function(){return B(A1(_ud,_tA));}),_x9=new T(function(){var _xa=function(_xb){var _xc=new T(function(){return E(E(_xb).a);}),_xd=function(_xe){return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,new T(function(){var _xf=E(E(_xe).b);return new T5(0,new T2(1,new T1(4,_xc),_xf.a),_xf.b,_xf.c,_xf.d,_xf.e);}),_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,new T(function(){var _xf=E(E(_xe).b);return new T5(0,new T2(1,new T1(4,_xc),_xf.a),_xf.b,_xf.c,_xf.d,_xf.e);}),_2L)));};return new T3(0,_xd,new T(function(){return E(E(_xb).b);}),new T(function(){return E(E(_xb).c);}));};return B(A1(_ud,_xa));}),_xg=function(_xh){var _xi=new T(function(){var _xj=new T(function(){var _xk=new T(function(){return E(E(_xh).b);});return B(A2(_2V,_u9,new T3(0,_xk,_xk,_2L)));});return B(A1(_x8,_xj));});return C > 19 ? new F(function(){return A1(_x9,_xi);}) : (++C,A1(_x9,_xi));},_xl=function(_xm){return C > 19 ? new F(function(){return _2Z(_2M,_u8,_xg,_xm);}) : (++C,_2Z(_2M,_u8,_xg,_xm));},_xn=function(_xo){var _xp=E(_xo);if(!_xp._){return __Z;}else{var _xq=function(_xr){return C > 19 ? new F(function(){return A1(_ue,new T(function(){return B(A1(_xp.a,_xr));}));}) : (++C,A1(_ue,new T(function(){return B(A1(_xp.a,_xr));})));};return new T2(1,function(_xs){return _3f(_u8,_xq,_xs);},new T(function(){return _xn(_xp.b);}));}},_xt=function(_xu){var _xv=E(_xu);if(!_xv._){return __Z;}else{var _xw=function(_xx){return C > 19 ? new F(function(){return A1(_ue,new T(function(){return B(A1(_xv.a,_xx));}));}) : (++C,A1(_ue,new T(function(){return B(A1(_xv.a,_xx));})));};return new T2(1,function(_xy){return _3f(_u8,_xw,_xy);},new T(function(){return _xt(_xv.b);}));}},_xz=function(_xA){return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,new T(function(){var _xB=E(E(_xA).b);return new T5(0,new T2(1,new T1(4,_oG),_xB.a),_xB.b,_xB.c,_xB.d,_xB.e);}),_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,new T(function(){var _xB=E(E(_xA).b);return new T5(0,new T2(1,new T1(4,_oG),_xB.a),_xB.b,_xB.c,_xB.d,_xB.e);}),_2L)));},_xC=function(_xD){var _xE=new T(function(){var _xF=E(E(_xD).b),_xG=new T(function(){var _xH=E(_xF.a);if(!_xH._){return __Z;}else{var _xI=E(_xH.b);if(!_xI._){return _xH;}else{var _xJ=E(_xI.a);if(_xJ._==2){var _xK=E(_xI.b);if(!_xK._){return _xH;}else{var _xL=E(_xK.a);if(_xL._==4){var _xM=new T(function(){return B(_rY(_wt,function(_xN){return new T1(1,_xH.a);},_xJ.a,_xL.a));});return new T2(1,new T1(4,_xM),_xK.b);}else{return _xH;}}}else{return _xH;}}}});return new T5(0,_xG,_xF.b,_xF.c,_xF.d,_xF.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_xE,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_xE,_2L)));},_xO=function(_xP){var _xQ=new T(function(){var _xR=E(E(_xP).b),_xS=new T(function(){var _xT=E(_xR.a);if(!_xT._){return __Z;}else{var _xU=E(_xT.a);if(_xU._==2){var _xV=E(_xT.b);if(!_xV._){return _xT;}else{var _xW=E(_xV.a);if(_xW._==4){return new T2(1,new T1(4,new T(function(){return B(_rY(_wt,_ty,_xU.a,_xW.a));})),_xV.b);}else{return _xT;}}}else{return _xT;}}});return new T5(0,_xS,_xR.b,_xR.c,_xR.d,_xR.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_xQ,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_xQ,_2L)));},_xX=function(_xY){var _xZ=new T(function(){var _y0=E(E(_xY).b),_y1=new T(function(){var _y2=E(_y0.a);if(!_y2._){return __Z;}else{var _y3=E(_y2.a);if(_y3._==4){return new T2(1,new T1(3,new T(function(){return _tP(_nQ(_mR(__Z,_y3.a)));})),_y2.b);}else{return _y2;}}});return new T5(0,_y1,_y0.b,_y0.c,_y0.d,_y0.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_xZ,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_xZ,_2L)));},_y4=function(_y5){var _y6=new T(function(){var _y7=E(E(_y5).b),_y8=new T(function(){var _y9=E(_y7.a);if(!_y9._){return __Z;}else{var _ya=E(_y9.a);if(_ya._==3){return new T2(1,new T1(5,new T(function(){return _tS(_ya.a);})),_y9.b);}else{return _y9;}}});return new T5(0,_y8,_y7.b,_y7.c,_y7.d,_y7.e);});return C > 19 ? new F(function(){return A2(_2V,_u9,new T3(0,0,_y6,_2L));}) : (++C,A2(_2V,_u9,new T3(0,0,_y6,_2L)));},_yb=function(_yc,_yd,_ye){var _yf=function(_yg){return C > 19 ? new F(function(){return A1(_yd,_yg);}) : (++C,A1(_yd,_yg));},_yh=new T(function(){var _yi=function(_yj){var _yk=new T(function(){var _yl=E(E(E(_yj).a).a);if(!_yl._){return _ub;}else{var _ym=E(_yl.b);if(!_ym._){return _ub;}else{var _yn=E(_ym.a);if(_yn._==3){var _yo=new T(function(){var _yp=new T(function(){return B(_yq(_yl.a));}),_yr=function(_ys){var _yt=E(_ys);if(!_yt._){return __Z;}else{var _yu=new T(function(){var _yv=function(_yw){var _yx=new T(function(){return B(A2(_2V,_u9,new T3(0,0,new T(function(){var _yy=E(E(_yw).b);return new T5(0,new T2(1,_yt.a,_yy.a),_yy.b,_yy.c,_yy.d,_yy.e);}),_2L)));});return C > 19 ? new F(function(){return A1(_ue,_yx);}) : (++C,A1(_ue,_yx));};return _3f(_u8,_yv,_yp);});return new T2(1,_yu,new T(function(){return _yr(_yt.b);}));}};return B(A3(_2B,_6h,_xt(_yr(_yn.a)),_ub));}),_yz=function(_yA){var _yB=new T(function(){return B(A2(_2V,_u9,new T3(0,0,new T(function(){var _yC=E(E(_yA).b);return new T5(0,_ym.b,_yC.b,_yC.c,_yC.d,_yC.e);}),_2L)));});return C > 19 ? new F(function(){return A1(_ue,_yB);}) : (++C,A1(_ue,_yB));};return _3f(_u8,_yz,_yo);}else{return _ub;}}}});return new T3(0,_yk,new T(function(){return E(E(_yj).b);}),new T(function(){return E(E(_yj).c);}));};return B(A1(_ud,_yi));}),_yD=function(_yE){var _yF=new T(function(){var _yG=new T(function(){return E(E(_yE).b);});return B(A2(_2V,_u9,new T3(0,_yG,_yG,_2L)));});return C > 19 ? new F(function(){return A1(_yh,_yF);}) : (++C,A1(_yh,_yF));},_yH=function(_yI){return C > 19 ? new F(function(){return _2Z(_2M,_u8,_yD,_yI);}) : (++C,_2Z(_2M,_u8,_yD,_yI));},_yJ=new T(function(){var _yK=function(_yL){var _yM=new T(function(){var _yN=E(E(E(_yL).a).a);if(!_yN._){return _ub;}else{var _yO=_yN.b,_yP=E(_yN.a);switch(_yP._){case 0:var _yQ=function(_yR){var _yS=new T(function(){return B(A2(_2V,_u9,new T3(0,0,new T(function(){var _yT=E(E(_yR).b);return new T5(0,_yO,_yT.b,_yT.c,_yT.d,_yT.e);}),_2L)));});return C > 19 ? new F(function(){return A1(_ue,_yS);}) : (++C,A1(_ue,_yS));};return _3f(_u8,_yQ,new T(function(){return B(_yq(_yP));}));break;case 5:var _yU=function(_yV){var _yW=new T(function(){return B(A2(_2V,_u9,new T3(0,0,new T(function(){var _yX=E(E(_yV).b);return new T5(0,_yO,_yX.b,_yX.c,_yX.d,_yX.e);}),_2L)));});return C > 19 ? new F(function(){return A1(_ue,_yW);}) : (++C,A1(_ue,_yW));};return _3f(_u8,_yU,new T(function(){return B(_yq(_yP));}));break;default:return _ub;}}});return new T3(0,_yM,new T(function(){return E(E(_yL).b);}),new T(function(){return E(E(_yL).c);}));};return B(A1(_ud,_yK));}),_yY=function(_yZ){var _z0=new T(function(){var _z1=new T(function(){return E(E(_yZ).b);});return B(A2(_2V,_u9,new T3(0,_z1,_z1,_2L)));});return C > 19 ? new F(function(){return A1(_yJ,_z0);}) : (++C,A1(_yJ,_z0));},_z2=function(_z3){return C > 19 ? new F(function(){return _2Z(_2M,_u8,_yY,_z3);}) : (++C,_2Z(_2M,_u8,_yY,_z3));},_z4=new T(function(){var _z5=function(_z6){var _z7=E(_z6);if(!_z7._){return E(new T2(0,__Z,_ub));}else{var _z8=E(_z7.b);if(!_z8._){return new T2(0,_z7,_ub);}else{var _z9=E(_z8.b);if(!_z9._){return new T2(0,_z7,_ub);}else{var _za=E(_z9.a);if(_za._==2){var _zb=E(_z9.b);if(!_zb._){return new T2(0,_z7,_ub);}else{var _zc=_zb.b,_zd=E(_zb.a);if(_zd._==4){var _ze=_sa(_wt,_za.a,_zd.a);return (_ze._==0)?new T2(0,_zc,new T(function(){return B(_yq(_z7.a));})):new T2(0,new T2(1,_ze.a,_zc),new T(function(){return B(_yq(_z8.a));}));}else{return new T2(0,_z7,_ub);}}}else{return new T2(0,_z7,_ub);}}}}};return B(_5m(_uf,_tZ,_z5));}),_zf=function(_zg){return C > 19 ? new F(function(){return _2Z(_2M,_u8,_z4,_zg);}) : (++C,_2Z(_2M,_u8,_z4,_zg));},_zh=function(_zi){var _zj=E(_zi);switch(_zj._){case 0:return _ui;case 1:return _ul;case 2:return _us;case 3:return _uv;case 4:return _uz;case 5:return _uL;case 6:return _uP;case 7:return _uX;case 8:return _v2;case 9:return _va;case 10:return _vg;case 11:return _vq;case 12:return _yH;case 13:return _vB;case 14:return _vK;case 15:return _vT;case 16:return _w2;case 17:return _wb;case 18:return _wl;case 19:return _wJ;case 20:return _x6;case 21:return _z2;case 22:return _xl;case 23:return _xz;case 24:return _xC;case 25:return _zf;case 26:return _xO;case 27:return _xX;case 28:return _y4;default:return C > 19 ? new F(function(){return A1(_yc,_zj.a);}) : (++C,A1(_yc,_zj.a));}},_zk=function(_zl){var _zm=E(_zl);return (_zm._==0)?__Z:new T2(1,new T(function(){return B(_sA(_u7,_uf,_zh,_yf,_zm.a));}),new T(function(){return _zk(_zm.b);}));},_yq=function(_zn){var _zo=E(_zn);switch(_zo._){case 0:return C > 19 ? new F(function(){return _zh(_zo.a);}) : (++C,_zh(_zo.a));break;case 5:return C > 19 ? new F(function(){return A3(_2B,_6h,_xn(_zk(_zo.a)),_ub);}) : (++C,A3(_2B,_6h,_xn(_zk(_zo.a)),_ub));break;default:return _ub;}};return C > 19 ? new F(function(){return _sA(_u7,_uf,_zh,function(_zp){return C > 19 ? new F(function(){return A1(_yd,_zp);}) : (++C,A1(_yd,_zp));},_ye);}) : (++C,_sA(_u7,_uf,_zh,function(_zp){return C > 19 ? new F(function(){return A1(_yd,_zp);}) : (++C,A1(_yd,_zp));},_ye));};return _yb;},_zq=new T(function(){return _u6(_mM,_2F);}),_zr=function(_zs){return E(_zs);},_zt=function(_zu){var _zv=new T(function(){return E(E(_zu).b);});return new T3(0,new T(function(){return E(E(_zv).a);}),_zv,_2L);},_zw=new T(function(){return B(_4u(_2F,_zt));}),_zx=new T2(0,_nK,__Z),_zy=new T(function(){return err(new T(function(){return _0(_mn,new T(function(){return unCStr("!!: negative index");}));}));}),_zz=new T(function(){return err(new T(function(){return _0(_mn,new T(function(){return unCStr("!!: index too large");}));}));}),_zA=function(_zB,_zC){while(1){var _zD=E(_zB);if(!_zD._){return E(_zz);}else{var _zE=E(_zC);if(!_zE){return E(_zD.a);}else{_zB=_zD.b;_zC=_zE-1|0;continue;}}}},_zF=function(_zG,_zH){if(_zH>=0){return _zA(_zG,_zH);}else{return E(_zy);}},_zI=new T(function(){return unCStr("ACK");}),_zJ=new T(function(){return unCStr("BEL");}),_zK=new T(function(){return unCStr("BS");}),_zL=new T(function(){return unCStr("SP");}),_zM=new T(function(){return unCStr("US");}),_zN=new T(function(){return unCStr("RS");}),_zO=new T(function(){return unCStr("GS");}),_zP=new T(function(){return unCStr("FS");}),_zQ=new T(function(){return unCStr("ESC");}),_zR=new T(function(){return unCStr("SUB");}),_zS=new T(function(){return unCStr("EM");}),_zT=new T(function(){return unCStr("CAN");}),_zU=new T(function(){return unCStr("ETB");}),_zV=new T(function(){return unCStr("SYN");}),_zW=new T(function(){return unCStr("NAK");}),_zX=new T(function(){return unCStr("DC4");}),_zY=new T(function(){return unCStr("DC3");}),_zZ=new T(function(){return unCStr("DC2");}),_A0=new T(function(){return unCStr("DC1");}),_A1=new T(function(){return unCStr("DLE");}),_A2=new T(function(){return unCStr("SI");}),_A3=new T(function(){return unCStr("SO");}),_A4=new T(function(){return unCStr("CR");}),_A5=new T(function(){return unCStr("FF");}),_A6=new T(function(){return unCStr("VT");}),_A7=new T(function(){return unCStr("LF");}),_A8=new T(function(){return unCStr("HT");}),_A9=new T(function(){return unCStr("ENQ");}),_Aa=new T(function(){return unCStr("EOT");}),_Ab=new T(function(){return unCStr("ETX");}),_Ac=new T(function(){return unCStr("STX");}),_Ad=new T(function(){return unCStr("SOH");}),_Ae=new T(function(){return unCStr("NUL");}),_Af=new T(function(){return unCStr("\\DEL");}),_Ag=new T(function(){return unCStr("\\a");}),_Ah=new T(function(){return unCStr("\\\\");}),_Ai=new T(function(){return unCStr("\\SO");}),_Aj=new T(function(){return unCStr("\\r");}),_Ak=new T(function(){return unCStr("\\f");}),_Al=new T(function(){return unCStr("\\v");}),_Am=new T(function(){return unCStr("\\n");}),_An=new T(function(){return unCStr("\\t");}),_Ao=new T(function(){return unCStr("\\b");}),_Ap=function(_Aq,_Ar){if(_Aq<=127){var _As=E(_Aq);switch(_As){case 92:return _0(_Ah,_Ar);case 127:return _0(_Af,_Ar);default:if(_As<32){switch(_As){case 7:return _0(_Ag,_Ar);case 8:return _0(_Ao,_Ar);case 9:return _0(_An,_Ar);case 10:return _0(_Am,_Ar);case 11:return _0(_Al,_Ar);case 12:return _0(_Ak,_Ar);case 13:return _0(_Aj,_Ar);case 14:return _0(_Ai,new T(function(){var _At=E(_Ar);if(!_At._){return __Z;}else{if(E(_At.a)==72){return unAppCStr("\\&",_At);}else{return _At;}}},1));default:return _0(new T2(1,92,new T(function(){return _zF(new T2(1,_Ae,new T2(1,_Ad,new T2(1,_Ac,new T2(1,_Ab,new T2(1,_Aa,new T2(1,_A9,new T2(1,_zI,new T2(1,_zJ,new T2(1,_zK,new T2(1,_A8,new T2(1,_A7,new T2(1,_A6,new T2(1,_A5,new T2(1,_A4,new T2(1,_A3,new T2(1,_A2,new T2(1,_A1,new T2(1,_A0,new T2(1,_zZ,new T2(1,_zY,new T2(1,_zX,new T2(1,_zW,new T2(1,_zV,new T2(1,_zU,new T2(1,_zT,new T2(1,_zS,new T2(1,_zR,new T2(1,_zQ,new T2(1,_zP,new T2(1,_zO,new T2(1,_zN,new T2(1,_zM,new T2(1,_zL,__Z))))))))))))))))))))))))))))))))),_As);})),_Ar);}}else{return new T2(1,_As,_Ar);}}}else{var _Au=new T(function(){var _Av=jsShowI(_Aq);return _0(fromJSStr(_Av),new T(function(){var _Aw=E(_Ar);if(!_Aw._){return __Z;}else{var _Ax=E(_Aw.a);if(_Ax<48){return _Aw;}else{if(_Ax>57){return _Aw;}else{return unAppCStr("\\&",_Aw);}}}},1));});return new T2(1,92,_Au);}},_Ay=new T(function(){return unCStr("\\\"");}),_Az=function(_AA,_AB){var _AC=E(_AA);if(!_AC._){return E(_AB);}else{var _AD=_AC.b,_AE=E(_AC.a);if(_AE==34){return _0(_Ay,new T(function(){return _Az(_AD,_AB);},1));}else{return _Ap(_AE,new T(function(){return _Az(_AD,_AB);}));}}},_AF=function(_AG){return new T2(1,34,new T(function(){return _Az(_AG,new T2(1,34,__Z));}));},_AH=function(_AI,_AJ){return new T2(1,34,new T(function(){return _Az(_AI,new T2(1,34,_AJ));}));},_AK=function(_AL,_AM,_){return new T3(0,_AL,new T(function(){return E(E(_AM).b);}),_2L);},_AN=function(_AO,_AP,_AQ){var _AR=function(_AS,_){var _AT=B(A2(_AO,_AS,_)),_AU=new T(function(){return B(A1(_AP,new T(function(){return E(E(_AT).a);})));});return new T3(0,_AU,new T(function(){return E(E(_AT).b);}),new T(function(){return E(E(_AT).c);}));};return C > 19 ? new F(function(){return _2Z(_2M,_2F,_AR,_AQ);}) : (++C,_2Z(_2M,_2F,_AR,_AQ));},_AV=new T3(0,new T2(0,_AK,new T2(0,function(_AW,_AX){return _mY(_x,_AW,_AX);},function(_AY,_AZ){return _3f(_2F,_AY,_AZ);})),function(_B0,_B1){return C > 19 ? new F(function(){return _2Z(_2M,_2F,_B0,_B1);}) : (++C,_2Z(_2M,_2F,_B0,_B1));},_AN),_B2=function(_B3,_B4,_){var _B5=B(A1(_B3,_));return new T3(0,_B5,new T(function(){return E(E(_B4).b);}),_2L);},_B6=function(_B7,_B8){var _B9=new T(function(){return _2P(_B7);}),_Ba=new T(function(){return _2R(new T(function(){return _2T(_B9);}));}),_Bb=new T(function(){return _2V(_B9);}),_Bc=function(_Bd){var _Be=new T(function(){var _Bf=B(A1(_B8,new T2(0,_2L,new T(function(){return E(E(_Bd).a);}))));return new T2(0,_Bf.a,_Bf.b);}),_Bg=new T(function(){var _Bh=E(_Bd);return new T5(0,new T(function(){return E(E(_Be).b);}),_Bh.b,_Bh.c,_Bh.d,_Bh.e);});return C > 19 ? new F(function(){return A1(_Bb,new T2(0,_Bg,new T(function(){return E(E(_Be).a);})));}) : (++C,A1(_Bb,new T2(0,_Bg,new T(function(){return E(E(_Be).a);}))));};return C > 19 ? new F(function(){return A(_48,[_Ba,_Ba,_3C,_3w,_3F,_Bc]);}) : (++C,A(_48,[_Ba,_Ba,_3C,_3w,_3F,_Bc]));},_Bi=function(_Bj,_Bk){var _Bl=new T(function(){return _2P(_Bj);}),_Bm=new T(function(){return _2R(new T(function(){return _2T(_Bl);}));}),_Bn=new T(function(){return _2V(_Bl);}),_Bo=function(_Bp){var _Bq=new T(function(){var _Br=B(A1(_Bk,new T2(0,_2L,new T(function(){return E(E(_Bp).d);}))));return new T2(0,_Br.a,_Br.b);}),_Bs=new T(function(){var _Bt=E(_Bp);return new T5(0,_Bt.a,_Bt.b,_Bt.c,new T(function(){return E(E(_Bq).b);}),_Bt.e);});return C > 19 ? new F(function(){return A1(_Bn,new T2(0,_Bs,new T(function(){return E(E(_Bq).a);})));}) : (++C,A1(_Bn,new T2(0,_Bs,new T(function(){return E(E(_Bq).a);}))));};return C > 19 ? new F(function(){return A(_48,[_Bm,_Bm,_3C,_3w,_3F,_Bo]);}) : (++C,A(_48,[_Bm,_Bm,_3C,_3w,_3F,_Bo]));},_Bu=new T2(0,_oG,_oG),_Bv=new T3(0,_oG,_Bu,_oG),_Bw={_:0,a:new T2(0,function(_Bx,_By){return (E(_Bx)==0)?(E(_By)==0)?true:false:(E(_By)==0)?false:true;},function(_Bz,_BA){return (E(_Bz)==0)?(E(_BA)==0)?false:true:(E(_BA)==0)?true:false;}),b:function(_BB,_BC){return (E(_BB)==0)?(E(_BC)==0)?1:0:(E(_BC)==0)?2:1;},c:function(_BD,_BE){if(!E(_BD)){return (E(_BE)==0)?false:true;}else{var _BF=E(_BE);return false;}},d:function(_BG,_BH){if(!E(_BG)){var _BI=E(_BH);return true;}else{return (E(_BH)==0)?false:true;}},e:function(_BJ,_BK){if(!E(_BJ)){var _BL=E(_BK);return false;}else{return (E(_BK)==0)?true:false;}},f:function(_BM,_BN){if(!E(_BM)){return (E(_BN)==0)?true:false;}else{var _BO=E(_BN);return true;}},g:function(_BP,_BQ){if(!E(_BP)){return E(_BQ);}else{var _BR=E(_BQ);return 1;}},h:function(_BS,_BT){if(!E(_BS)){var _BU=E(_BT);return 0;}else{return E(_BT);}}},_BV=function(_BW,_BX){var _BY=E(_BW),_BZ=E(_BX);return (_BY>_BZ)?_BY:_BZ;},_C0=function(_C1,_C2){return (_C1>=_C2)?(_C1!=_C2)?2:1:0;},_C3=function(_C4,_C5){return E(_C4)>E(_C5);},_C6={_:0,a:new T2(0,function(_C7,_C8){return E(_C7)==E(_C8);},function(_C9,_Ca){return E(_C9)!=E(_Ca);}),b:function(_Cb,_Cc){return _C0(E(_Cb),E(_Cc));},c:function(_Cd,_Ce){return E(_Cd)<E(_Ce);},d:function(_Cf,_Cg){return E(_Cf)<=E(_Cg);},e:_C3,f:function(_Ch,_Ci){return E(_Ch)>=E(_Ci);},g:_BV,h:function(_Cj,_Ck){var _Cl=E(_Cj),_Cm=E(_Ck);return (_Cl>_Cm)?_Cm:_Cl;}},_Cn=function(_Co){return E(E(_Co).b);},_Cp=function(_Cq,_Cr,_Cs,_Ct){var _Cu=E(_Cs);if(!_Cu._){var _Cv=function(_Cw,_Cx){var _Cy=new T(function(){return B(A1(_Cw,new T(function(){return E(E(_Cx).a);})));});return C > 19 ? new F(function(){return A2(_Ct,function(_Cz){return new T2(0,_Cz,E(_Cx).b);},_Cy);}) : (++C,A2(_Ct,function(_Cz){return new T2(0,_Cz,E(_Cx).b);},_Cy));};return _Cv;}else{var _CA=new T(function(){return B(A3(_Cn,_Cr,_Cu.a,_Ct));}),_CB=new T(function(){return _2z(_Cq);}),_CC=new T(function(){return _Cp(_Cq,_Cr,_Cu.b,_Ct);}),_CD=function(_CE){var _CF=new T(function(){var _CG=new T(function(){return B(A1(_CC,_CE));}),_CH=new T(function(){return B(A2(_Ct,_mg,new T(function(){return B(A1(_CG,_CB));})));}),_CI=function(_CJ){var _CK=E(_CJ);if(!_CK._){return E(_CH);}else{return C > 19 ? new F(function(){return A2(_Ct,_mg,new T(function(){return B(A1(_CG,_CK.a));}));}) : (++C,A2(_Ct,_mg,new T(function(){return B(A1(_CG,_CK.a));})));}};return B(A1(_CA,_CI));}),_CL=function(_CM){var _CN=new T(function(){return B(A1(_CF,new T(function(){return E(E(_CM).b);})));});return C > 19 ? new F(function(){return A2(_Ct,function(_CO){return new T2(0,E(_CM).a,_CO);},_CN);}) : (++C,A2(_Ct,function(_CO){return new T2(0,E(_CM).a,_CO);},_CN));};return _CL;};return _CD;}},_CP=function(_CQ){var _CR=E(_CQ);return new T2(0,_CR.a,_CR.b);},_CS=function(_CT){var _CU=E(_CT);return (_CU._==0)?__Z:new T2(1,1,new T(function(){return _CS(_CU.b);}));},_CV=function(_CW){var _CX=E(_CW);return (_CX._==0)?__Z:new T2(1,function(_CY){return E(_CY)+E(_CX.a)|0;},new T(function(){return _CV(_CX.b);}));},_CZ=function(_D0,_D1){var _D2=E(_D0);if(!_D2._){var _D3=_D2.a,_D4=new T(function(){return B(A1(_D1,_CP));}),_D5=function(_D6,_D7){var _D8=new T(function(){var _D9=new T(function(){var _Da=E(_D7);return new T2(0,_Da.a,_Da.b);}),_Db=new T(function(){var _Dc=new T(function(){return E(E(_D9).a);}),_Dd=new T(function(){return B(A1(_D6,new T(function(){return _sa(_C6,_D3,_Dc);})));}),_De=function(_Df){return C > 19 ? new F(function(){return _rY(_C6,function(_Dg){return E(_Df);},_D3,_Dc);}) : (++C,_rY(_C6,function(_Dg){return E(_Df);},_D3,_Dc));};return B(A2(_D1,_De,_Dd));});return B(A2(_D1,function(_Dh){return new T2(0,_Dh,E(_D9).b);},_Db));});return C > 19 ? new F(function(){return A1(_D4,_D8);}) : (++C,A1(_D4,_D8));};return _D5;}else{var _Di=new T(function(){return B(A1(_D1,_CP));}),_Dj=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_D2.a)),0));}),_Dk=new T(function(){var _Dl=E(_D2.c);return _Dm(_Dl.a,_Dl.b,_D1);}),_Dn=function(_Do){var _Dp=new T(function(){return B(A1(_Dk,_Do));}),_Dq=new T(function(){return B(A2(_D1,_mg,new T(function(){return B(A1(_Dp,_Bu));})));}),_Dr=function(_Ds){var _Dt=new T(function(){var _Du=new T(function(){var _Dv=E(_Ds);return new T2(0,_Dv.a,_Dv.b);}),_Dw=new T(function(){return E(E(_Du).a);}),_Dx=new T(function(){var _Dy=new T(function(){return E(E(_Du).b);}),_Dz=new T(function(){var _DA=_sa(_C6,_Dj,_Dy);if(!_DA._){return E(_Dq);}else{return B(A2(_D1,_mg,new T(function(){return B(A1(_Dp,_DA.a));})));}}),_DB=function(_DC){return C > 19 ? new F(function(){return _rY(_C6,function(_DD){return E(_DC);},_Dj,_Dy);}) : (++C,_rY(_C6,function(_DD){return E(_DC);},_Dj,_Dy));};return B(A2(_D1,_DB,_Dz));});return B(A2(_D1,function(_DE){return new T2(0,_Dw,_DE);},_Dx));});return C > 19 ? new F(function(){return A1(_Di,_Dt);}) : (++C,A1(_Di,_Dt));};return _Dr;};return _Dn;}},_DF=function(_DG,_DH,_DI){return new T2(0,new T(function(){return _2z(_DH);}),new T(function(){return _2z(_DI);}));},_DJ=function(_DK,_DL,_DM){return new T2(0,_DK,new T(function(){return _DF(_DK,_DL,_DM);}));},_DN=function(_DO,_DP){return new T5(0,1,E(_DO),_DP,E(_oG),E(_oG));},_DQ=function(_DR,_DS,_DT){var _DU=E(_DT);if(!_DU._){return _qD(_DU.b,_DU.c,_DU.d,_DQ(_DR,_DS,_DU.e));}else{return _DN(_DR,_DS);}},_DV=function(_DW,_DX,_DY){var _DZ=E(_DY);if(!_DZ._){return _pX(_DZ.b,_DZ.c,_DV(_DW,_DX,_DZ.d),_DZ.e);}else{return _DN(_DW,_DX);}},_E0=function(_E1,_E2,_E3,_E4,_E5,_E6,_E7){return _pX(_E4,_E5,_DV(_E1,_E2,_E6),_E7);},_E8=function(_E9,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef,_Eg){var _Eh=E(_Eb);if(!_Eh._){var _Ei=_Eh.a,_Ej=_Eh.b,_Ek=_Eh.c,_El=_Eh.d,_Em=_Eh.e;if((imul(3,_Ei)|0)>=_Ec){if((imul(3,_Ec)|0)>=_Ei){return new T5(0,(_Ei+_Ec|0)+1|0,E(_E9),_Ea,_Eh,E(new T5(0,_Ec,E(_Ed),_Ee,E(_Ef),E(_Eg))));}else{return _qD(_Ej,_Ek,_El,B(_E8(_E9,_Ea,_Em,_Ec,_Ed,_Ee,_Ef,_Eg)));}}else{return _pX(_Ed,_Ee,B(_En(_E9,_Ea,_Ei,_Ej,_Ek,_El,_Em,_Ef)),_Eg);}}else{return _E0(_E9,_Ea,_Ec,_Ed,_Ee,_Ef,_Eg);}},_En=function(_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev){var _Ew=E(_Ev);if(!_Ew._){var _Ex=_Ew.a,_Ey=_Ew.b,_Ez=_Ew.c,_EA=_Ew.d,_EB=_Ew.e;if((imul(3,_Eq)|0)>=_Ex){if((imul(3,_Ex)|0)>=_Eq){return new T5(0,(_Eq+_Ex|0)+1|0,E(_Eo),_Ep,E(new T5(0,_Eq,E(_Er),_Es,E(_Et),E(_Eu))),_Ew);}else{return _qD(_Er,_Es,_Et,B(_E8(_Eo,_Ep,_Eu,_Ex,_Ey,_Ez,_EA,_EB)));}}else{return _pX(_Ey,_Ez,B(_En(_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_EA)),_EB);}}else{return _DQ(_Eo,_Ep,new T5(0,_Eq,E(_Er),_Es,E(_Et),E(_Eu)));}},_EC=function(_ED,_EE,_EF,_EG){var _EH=E(_EF);if(!_EH._){var _EI=_EH.a,_EJ=_EH.b,_EK=_EH.c,_EL=_EH.d,_EM=_EH.e,_EN=E(_EG);if(!_EN._){var _EO=_EN.a,_EP=_EN.b,_EQ=_EN.c,_ER=_EN.d,_ES=_EN.e;if((imul(3,_EI)|0)>=_EO){if((imul(3,_EO)|0)>=_EI){return new T5(0,(_EI+_EO|0)+1|0,E(_ED),_EE,_EH,_EN);}else{return _qD(_EJ,_EK,_EL,B(_E8(_ED,_EE,_EM,_EO,_EP,_EQ,_ER,_ES)));}}else{return _pX(_EP,_EQ,B(_En(_ED,_EE,_EI,_EJ,_EK,_EL,_EM,_ER)),_ES);}}else{return _DQ(_ED,_EE,_EH);}}else{return _DV(_ED,_EE,_EG);}},_ET=function(_EU,_EV,_EW){var _EX=E(_EV);if(!_EX._){return E(_EW);}else{var _EY=function(_EZ,_F0){while(1){var _F1=E(_F0);if(!_F1._){var _F2=_F1.b,_F3=_F1.e;switch(B(A3(_pS,_EU,_EZ,_F2))){case 0:return C > 19 ? new F(function(){return _EC(_F2,_F1.c,B(_EY(_EZ,_F1.d)),_F3);}) : (++C,_EC(_F2,_F1.c,B(_EY(_EZ,_F1.d)),_F3));break;case 1:return E(_F3);default:_F0=_F3;continue;}}else{return new T0(1);}}};return C > 19 ? new F(function(){return _EY(_EX.a,_EW);}) : (++C,_EY(_EX.a,_EW));}},_F4=function(_F5,_F6,_F7){var _F8=E(_F6);if(!_F8._){return E(_F7);}else{var _F9=function(_Fa,_Fb){while(1){var _Fc=E(_Fb);if(!_Fc._){var _Fd=_Fc.b,_Fe=_Fc.d;switch(B(A3(_pS,_F5,_Fd,_Fa))){case 0:return C > 19 ? new F(function(){return _EC(_Fd,_Fc.c,_Fe,B(_F9(_Fa,_Fc.e)));}) : (++C,_EC(_Fd,_Fc.c,_Fe,B(_F9(_Fa,_Fc.e))));break;case 1:return E(_Fe);default:_Fb=_Fe;continue;}}else{return new T0(1);}}};return C > 19 ? new F(function(){return _F9(_F8.a,_F7);}) : (++C,_F9(_F8.a,_F7));}},_Ff=function(_Fg,_Fh,_Fi,_Fj){var _Fk=E(_Fh),_Fl=E(_Fj);if(!_Fl._){var _Fm=_Fl.b,_Fn=_Fl.c,_Fo=_Fl.d,_Fp=_Fl.e;switch(B(A3(_pS,_Fg,_Fk,_Fm))){case 0:return _pX(_Fm,_Fn,_Ff(_Fg,_Fk,_Fi,_Fo),_Fp);case 1:return _Fl;default:return _qD(_Fm,_Fn,_Fo,_Ff(_Fg,_Fk,_Fi,_Fp));}}else{return new T5(0,1,_Fk,_Fi,E(_oG),E(_oG));}},_Fq=function(_Fr,_Fs,_Ft,_Fu){return _Ff(_Fr,_Fs,_Ft,_Fu);},_Fv=function(_Fw){return E(E(_Fw).d);},_Fx=function(_Fy){return E(E(_Fy).f);},_Fz=function(_FA,_FB,_FC,_FD){var _FE=E(_FB);if(!_FE._){var _FF=E(_FC);if(!_FF._){return E(_FD);}else{var _FG=function(_FH,_FI){while(1){var _FJ=E(_FI);if(!_FJ._){if(!B(A3(_Fx,_FA,_FJ.b,_FH))){return _FJ;}else{_FI=_FJ.d;continue;}}else{return new T0(1);}}};return _FG(_FF.a,_FD);}}else{var _FK=_FE.a,_FL=E(_FC);if(!_FL._){var _FM=function(_FN,_FO){while(1){var _FP=E(_FO);if(!_FP._){if(!B(A3(_Fv,_FA,_FP.b,_FN))){return _FP;}else{_FO=_FP.e;continue;}}else{return new T0(1);}}};return _FM(_FK,_FD);}else{var _FQ=function(_FR,_FS,_FT){while(1){var _FU=E(_FT);if(!_FU._){var _FV=_FU.b;if(!B(A3(_Fv,_FA,_FV,_FR))){if(!B(A3(_Fx,_FA,_FV,_FS))){return _FU;}else{_FT=_FU.d;continue;}}else{_FT=_FU.e;continue;}}else{return new T0(1);}}};return _FQ(_FK,_FL.a,_FD);}}},_FW=function(_FX,_FY,_FZ,_G0,_G1){var _G2=E(_G1);if(!_G2._){var _G3=_G2.b,_G4=_G2.c,_G5=_G2.d,_G6=_G2.e,_G7=E(_G0);if(!_G7._){var _G8=_G7.b,_G9=function(_Ga){var _Gb=new T1(1,E(_G8));return C > 19 ? new F(function(){return _EC(_G8,_G7.c,B(_FW(_FX,_FY,_Gb,_G7.d,_Fz(_FX,_FY,_Gb,_G2))),B(_FW(_FX,_Gb,_FZ,_G7.e,_Fz(_FX,_Gb,_FZ,_G2))));}) : (++C,_EC(_G8,_G7.c,B(_FW(_FX,_FY,_Gb,_G7.d,_Fz(_FX,_FY,_Gb,_G2))),B(_FW(_FX,_Gb,_FZ,_G7.e,_Fz(_FX,_Gb,_FZ,_G2)))));};if(!E(_G5)._){return C > 19 ? new F(function(){return _G9(_);}) : (++C,_G9(_));}else{if(!E(_G6)._){return C > 19 ? new F(function(){return _G9(_);}) : (++C,_G9(_));}else{return C > 19 ? new F(function(){return _Fq(_FX,_G3,_G4,_G7);}) : (++C,_Fq(_FX,_G3,_G4,_G7));}}}else{return C > 19 ? new F(function(){return _EC(_G3,_G4,B(_ET(_FX,_FY,_G5)),B(_F4(_FX,_FZ,_G6)));}) : (++C,_EC(_G3,_G4,B(_ET(_FX,_FY,_G5)),B(_F4(_FX,_FZ,_G6))));}}else{return E(_G0);}},_Gc=function(_Gd,_Ge,_Gf,_Gg,_Gh,_Gi,_Gj,_Gk,_Gl,_Gm,_Gn,_Go,_Gp){var _Gq=function(_Gr){var _Gs=new T1(1,E(_Gh));return C > 19 ? new F(function(){return _EC(_Gh,_Gi,B(_FW(_Gd,_Ge,_Gs,_Gj,_Fz(_Gd,_Ge,_Gs,new T5(0,_Gl,E(_Gm),_Gn,E(_Go),E(_Gp))))),B(_FW(_Gd,_Gs,_Gf,_Gk,_Fz(_Gd,_Gs,_Gf,new T5(0,_Gl,E(_Gm),_Gn,E(_Go),E(_Gp))))));}) : (++C,_EC(_Gh,_Gi,B(_FW(_Gd,_Ge,_Gs,_Gj,_Fz(_Gd,_Ge,_Gs,new T5(0,_Gl,E(_Gm),_Gn,E(_Go),E(_Gp))))),B(_FW(_Gd,_Gs,_Gf,_Gk,_Fz(_Gd,_Gs,_Gf,new T5(0,_Gl,E(_Gm),_Gn,E(_Go),E(_Gp)))))));};if(!E(_Go)._){return C > 19 ? new F(function(){return _Gq(_);}) : (++C,_Gq(_));}else{if(!E(_Gp)._){return C > 19 ? new F(function(){return _Gq(_);}) : (++C,_Gq(_));}else{return C > 19 ? new F(function(){return _Fq(_Gd,_Gm,_Gn,new T5(0,_Gg,E(_Gh),_Gi,E(_Gj),E(_Gk)));}) : (++C,_Fq(_Gd,_Gm,_Gn,new T5(0,_Gg,E(_Gh),_Gi,E(_Gj),E(_Gk))));}}},_Gt=function(_Gu,_Gv,_Gw){var _Gx=E(_Gw),_Gy=_Gx.a,_Gz=_Gx.b;return new T2(0,new T(function(){var _GA=E(_Gu);if(!_GA._){var _GB=E(_Gy);if(!_GB._){return B(_Gc(_C6,__Z,__Z,_GA.a,_GA.b,_GA.c,_GA.d,_GA.e,_GB.a,_GB.b,_GB.c,_GB.d,_GB.e));}else{return _GA;}}else{return E(_Gy);}}),new T(function(){var _GC=E(_Gv);if(!_GC._){var _GD=E(_Gz);if(!_GD._){return B(_Gc(_C6,__Z,__Z,_GC.a,_GC.b,_GC.c,_GC.d,_GC.e,_GD.a,_GD.b,_GD.c,_GD.d,_GD.e));}else{return _GC;}}else{return E(_Gz);}}));},_GE=function(_GF,_GG){var _GH=E(_GF),_GI=_Gt(_GH.a,_GH.b,_GG);return new T2(0,_GI.a,_GI.b);},_GJ=function(_GK,_GL,_GM,_GN){var _GO=E(_GN),_GP=_GO.a,_GQ=_GO.c;return new T3(0,new T(function(){var _GR=E(_GK);if(!_GR._){var _GS=E(_GP);if(!_GS._){return B(_Gc(_Bw,__Z,__Z,_GR.a,_GR.b,_GR.c,_GR.d,_GR.e,_GS.a,_GS.b,_GS.c,_GS.d,_GS.e));}else{return _GR;}}else{return E(_GP);}}),new T(function(){return _GE(_GL,_GO.b);}),new T(function(){var _GT=E(_GM);if(!_GT._){var _GU=E(_GQ);if(!_GU._){return B(_Gc(_C6,__Z,__Z,_GT.a,_GT.b,_GT.c,_GT.d,_GT.e,_GU.a,_GU.b,_GU.c,_GU.d,_GU.e));}else{return _GT;}}else{return E(_GQ);}}));},_GV=function(_GW,_GX){var _GY=E(_GW),_GZ=_GJ(_GY.a,_GY.b,_GY.c,_GX);return new T3(0,_GZ.a,_GZ.b,_GZ.c);},_H0=function(_H1,_H2){var _H3=E(_H1),_H4=E(_H2);return new T2(0,new T(function(){return _mc(_H3.a,_H4.a);}),new T(function(){return _GV(_H3.b,_H4.b);}));},_H5=function(_H6){return new T2(0,_H6,__Z);},_H7=function(_H8){return new T2(0,_H8,_Bv);},_H9=new T(function(){return _H7(_GV);}),_Ha=new T(function(){return _DJ(_H0,new T(function(){return _H5(_mc);}),_H9);}),_Hb=function(_Hc){return new T2(0,_Hc,function(_Hd,_He){return _Hf(_Hc,_Hd,_He);});},_Hg=new T(function(){return _Hb(_H9);}),_Dm=function(_Hh,_Hi,_Hj){var _Hk=new T(function(){return _CZ(_Hh,_Hj);}),_Hl=new T(function(){return _Cp(_Ha,_Hg,_Hi,_Hj);}),_Hm=function(_Hn){var _Ho=new T(function(){return B(A1(_Hl,_Hn));}),_Hp=new T(function(){return B(A2(_Hj,_mg,new T(function(){return B(A1(_Ho,new T2(0,__Z,_Bv)));})));}),_Hq=function(_Hr){var _Hs=E(_Hr);if(!_Hs._){return E(_Hp);}else{return C > 19 ? new F(function(){return A2(_Hj,_mg,new T(function(){return B(A1(_Ho,_Hs.a));}));}) : (++C,A2(_Hj,_mg,new T(function(){return B(A1(_Ho,_Hs.a));})));}};return C > 19 ? new F(function(){return A1(_Hk,_Hq);}) : (++C,A1(_Hk,_Hq));};return _Hm;},_Ht=function(_Hu){var _Hv=E(_Hu);return new T3(0,_Hv.a,_Hv.b,_Hv.c);},_Hw=new T(function(){return _H7(_GV);}),_Hf=function(_Hx,_Hy,_Hz){var _HA=E(_Hy);switch(_HA._){case 0:var _HB=_HA.a,_HC=new T(function(){return B(A1(_Hz,_Ht));}),_HD=new T(function(){return _Hf(_Hw,_HA.c,_Hz);}),_HE=new T(function(){return _2z(_Hx);}),_HF=new T(function(){return _Hf(_Hx,_HA.d,_Hz);}),_HG=function(_HH){var _HI=new T(function(){var _HJ=new T(function(){return B(A1(_HF,_HH));}),_HK=new T(function(){return B(A2(_Hz,_mg,new T(function(){return B(A1(_HJ,_HE));})));}),_HL=function(_HM){var _HN=E(_HM);if(!_HN._){return E(_HK);}else{return C > 19 ? new F(function(){return A2(_Hz,_mg,new T(function(){return B(A1(_HJ,_HN.a));}));}) : (++C,A2(_Hz,_mg,new T(function(){return B(A1(_HJ,_HN.a));})));}};return B(A1(_HD,_HL));}),_HO=new T(function(){return B(A2(_Hz,_mg,new T(function(){return B(A1(_HI,_Bv));})));}),_HP=function(_HQ){var _HR=new T(function(){var _HS=new T(function(){var _HT=E(_HQ);return new T3(0,_HT.a,_HT.b,_HT.c);}),_HU=new T(function(){var _HV=new T(function(){return E(E(_HS).a);}),_HW=new T(function(){var _HX=_sa(_Bw,_HB,_HV);if(!_HX._){return E(_HO);}else{return B(A2(_Hz,_mg,new T(function(){return B(A1(_HI,_HX.a));})));}}),_HY=function(_HZ){return C > 19 ? new F(function(){return _rY(_Bw,function(_I0){return E(_HZ);},_HB,_HV);}) : (++C,_rY(_Bw,function(_I0){return E(_HZ);},_HB,_HV));};return B(A2(_Hz,_HY,_HW));});return B(A2(_Hz,function(_I1){var _I2=E(_HS);return new T3(0,_I1,_I2.b,_I2.c);},_HU));});return C > 19 ? new F(function(){return A1(_HC,_HR);}) : (++C,A1(_HC,_HR));};return _HP;};return _HG;case 1:var _I3=new T(function(){return B(A1(_Hz,_Ht));}),_I4=new T(function(){var _I5=E(_HA.a);return _Dm(_I5.a,_I5.b,_Hz);}),_I6=function(_I7){var _I8=new T(function(){return B(A1(_I4,_I7));}),_I9=function(_Ia){var _Ib=new T(function(){var _Ic=new T(function(){var _Id=E(_Ia);return new T3(0,_Id.a,_Id.b,_Id.c);}),_Ie=new T(function(){return E(E(_Ic).c);}),_If=new T(function(){return E(E(_Ic).a);}),_Ig=new T(function(){return B(A1(_I8,new T(function(){return E(E(_Ic).b);})));});return B(A2(_Hz,function(_Ih){return new T3(0,_If,_Ih,_Ie);},_Ig));});return C > 19 ? new F(function(){return A1(_I3,_Ib);}) : (++C,A1(_I3,_Ib));};return _I9;};return _I6;default:var _Ii=_HA.a,_Ij=new T(function(){return B(A1(_Hz,_Ht));}),_Ik=function(_Il,_Im){var _In=new T(function(){var _Io=new T(function(){var _Ip=E(_Im);return new T3(0,_Ip.a,_Ip.b,_Ip.c);}),_Iq=new T(function(){return E(E(_Io).b);}),_Ir=new T(function(){return E(E(_Io).a);}),_Is=new T(function(){var _It=new T(function(){return E(E(_Io).c);}),_Iu=new T(function(){return B(A1(_Il,new T(function(){return _sa(_C6,_Ii,_It);})));}),_Iv=function(_Iw){return C > 19 ? new F(function(){return _rY(_C6,function(_Ix){return E(_Iw);},_Ii,_It);}) : (++C,_rY(_C6,function(_Ix){return E(_Iw);},_Ii,_It));};return B(A2(_Hz,_Iv,_Iu));});return B(A2(_Hz,function(_Iy){return new T3(0,_Ir,_Iq,_Iy);},_Is));});return C > 19 ? new F(function(){return A1(_Ij,_In);}) : (++C,A1(_Ij,_In));};return _Ik;}},_Iz=function(_IA,_IB){var _IC=function(_ID){var _IE=E(_ID);return (_IE._==0)?__Z:new T2(1,new T(function(){return B(A1(_IA,_IE.a));}),new T(function(){return _IC(_IE.b);}));};return _IC(_IB);},_IF=function(_IG,_IH){var _II=E(_IG);if(!_II._){return __Z;}else{var _IJ=E(_IH);return (_IJ._==0)?__Z:new T2(1,new T(function(){return B(A1(_II.a,_IJ.a));}),new T(function(){return _IF(_II.b,_IJ.b);}));}},_IK=function(_IL){return new T2(1,_IL,__Z);},_IM=function(_IN){return E(E(_IN).a);},_IO=function(_IP){return E(E(_IP).a);},_IQ=function(_IR){return E(E(_IR).a);},_IS=function(_IT){return E(E(_IT).b);},_IU=function(_IV){return E(E(_IV).d);},_IW=function(_IX){return E(E(_IX).e);},_IY=new T(function(){return _H5(_mc);}),_IZ=function(_J0){return E(E(_J0).b);},_J1=function(_J2,_J3,_J4,_J5,_J6){var _J7=new T(function(){var _J8=function(_J9){while(1){var _Ja=(function(_Jb){var _Jc=E(_Jb);if(!_Jc._){return __Z;}else{var _Jd=_Jc.b,_Je=E(_Jc.a);if(!B(A3(_IZ,_J2,_Je.a,_J3))){_J9=_Jd;return __continue;}else{return new T2(1,_Je,new T(function(){return _J8(_Jd);}));}}})(_J9);if(_Ja!=__continue){return _Ja;}}};return _J8(_J6);}),_Jf=new T(function(){var _Jg=new T(function(){var _Jh=function(_Ji){var _Jj=E(_Ji);return (_Jj._==0)?__Z:new T2(1,new T(function(){var _Jk=E(_Jj.a);if(!B(A3(_bX,_J2,_J3,_Jk.a))){return __Z;}else{return new T1(1,_Jk.b);}}),new T(function(){return _Jh(_Jj.b);}));};return B(_2B(_IY,_Jh(_J6)));});return B(A1(_J5,_Jg));});return C > 19 ? new F(function(){return A2(_J4,function(_Jl){var _Jm=E(_Jl);return (_Jm._==0)?E(_J7):new T2(1,new T2(0,_J3,_Jm.a),_J6);},_Jf);}) : (++C,A2(_J4,function(_Jl){var _Jm=E(_Jl);return (_Jm._==0)?E(_J7):new T2(1,new T2(0,_J3,_Jm.a),_J6);},_Jf));},_Jn=function(_Jo,_Jp){var _Jq=E(_Jp);return (_Jq._==0)?__Z:new T1(1,new T(function(){return B(A1(_Jo,_Jq.a));}));},_Jr=function(_Js,_Jt){var _Ju=E(_Jt),_Jv=_Jw(_Js,_Ju.a,_Ju.b,_Ju.c);return new T3(0,_Jv.a,_Jv.b,_Jv.c);},_Jx=function(_Jy,_Jz,_JA){var _JB=E(_JA),_JC=_JD(_Jy,_Jz,_JB.a,_JB.b);return new T2(0,_JC.a,_JC.b);},_JD=function(_JE,_JF,_JG,_JH){var _JI=new T(function(){return B(A2(_JE,function(_JJ){return _Jx(_JE,_JF,_JJ);},_JH));});return new T2(0,new T(function(){return B(A1(_JF,_JG));}),_JI);},_JK=function(_JL,_JM){var _JN=E(_JM);return (_JN._==0)?new T5(0,_JN.a,E(_JN.b),new T(function(){return B(A1(_JL,_JN.c));}),E(_JK(_JL,_JN.d)),E(_JK(_JL,_JN.e))):new T0(1);},_JO=function(_JP,_JQ,_JR){var _JS=new T(function(){var _JT=function(_He){return _Jn(_JP,_He);},_JU=function(_JV){var _JW=E(_JV),_JX=_JD(_Jr,_JT,_JW.a,_JW.b);return new T2(0,_JX.a,_JX.b);};return _JK(function(_JY){var _JZ=E(_JY),_K0=_JO(_JU,_JZ.a,_JZ.b);return new T2(0,_K0.a,_K0.b);},_JR);});return new T2(0,new T(function(){return _JK(_JP,_JQ);}),_JS);},_Jw=function(_K1,_K2,_K3,_K4){var _K5=new T(function(){var _K6=E(_K3),_K7=function(_He){return _Jn(_K1,_He);},_K8=_JO(function(_K9){var _Ka=E(_K9),_Kb=_JD(_Jr,_K7,_Ka.a,_Ka.b);return new T2(0,_Kb.a,_Kb.b);},_K6.a,_K6.b);return new T2(0,_K8.a,_K8.b);}),_Kc=new T(function(){var _Kd=function(_He){return _Jr(_K1,_He);};return _JK(function(_Ke){var _Kf=E(_Ke),_Kg=_Jw(_Kd,_Kf.a,_Kf.b,_Kf.c);return new T3(0,_Kg.a,_Kg.b,_Kg.c);},_K2);});return new T3(0,_Kc,_K5,new T(function(){return _JK(_K1,_K4);}));},_Kh=function(_Ki,_Kj){return new T2(1,_Ki,_Kj);},_Kk=function(_Kl,_Km){var _Kn=E(_Km);if(!_Kn._){return C > 19 ? new F(function(){return A2(_2V,_Kl,__Z);}) : (++C,A2(_2V,_Kl,__Z));}else{var _Ko=_2T(_Kl);return C > 19 ? new F(function(){return A3(_s6,_Ko,new T(function(){return B(A3(_2R,_Ko,_Kh,_Kn.a));}),new T(function(){return B(_Kk(_Kl,_Kn.b));}));}) : (++C,A3(_s6,_Ko,new T(function(){return B(A3(_2R,_Ko,_Kh,_Kn.a));}),new T(function(){return B(_Kk(_Kl,_Kn.b));})));}},_Kp=function(_Kq,_Kr){return E(_Kq)+E(_Kr)|0;},_Ks=function(_Kt){return E(E(_Kt).a);},_Ku=function(_Kv){return E(E(_Kv).b);},_Kw=new T0(1),_Kx=new T(function(){return unCStr("Failure in Data.Map.balanceL");}),_Ky=new T(function(){var _Kz=_;return err(_Kx);}),_KA=function(_KB,_KC,_KD){var _KE=E(_KD);if(!_KE._){var _KF=_KE.a,_KG=E(_KC);if(!_KG._){var _KH=_KG.a,_KI=_KG.b;if(_KH<=(imul(3,_KF)|0)){return new T4(0,(1+_KH|0)+_KF|0,E(_KB),_KG,_KE);}else{var _KJ=E(_KG.c);if(!_KJ._){var _KK=_KJ.a,_KL=E(_KG.d);if(!_KL._){var _KM=_KL.a,_KN=_KL.b,_KO=_KL.c;if(_KM>=(imul(2,_KK)|0)){var _KP=function(_KQ){var _KR=E(_KL.d);return (_KR._==0)?new T4(0,(1+_KH|0)+_KF|0,E(_KN),E(new T4(0,(1+_KK|0)+_KQ|0,E(_KI),_KJ,E(_KO))),E(new T4(0,(1+_KF|0)+_KR.a|0,E(_KB),_KR,_KE))):new T4(0,(1+_KH|0)+_KF|0,E(_KN),E(new T4(0,(1+_KK|0)+_KQ|0,E(_KI),_KJ,E(_KO))),E(new T4(0,1+_KF|0,E(_KB),E(_Kw),_KE)));},_KS=E(_KO);if(!_KS._){return _KP(_KS.a);}else{return _KP(0);}}else{return new T4(0,(1+_KH|0)+_KF|0,E(_KI),_KJ,E(new T4(0,(1+_KF|0)+_KM|0,E(_KB),_KL,_KE)));}}else{return E(_Ky);}}else{return E(_Ky);}}}else{return new T4(0,1+_KF|0,E(_KB),E(_Kw),_KE);}}else{var _KT=E(_KC);if(!_KT._){var _KU=_KT.a,_KV=_KT.b,_KW=_KT.d,_KX=E(_KT.c);if(!_KX._){var _KY=_KX.a,_KZ=E(_KW);if(!_KZ._){var _L0=_KZ.a,_L1=_KZ.b,_L2=_KZ.c;if(_L0>=(imul(2,_KY)|0)){var _L3=function(_L4){var _L5=E(_KZ.d);return (_L5._==0)?new T4(0,1+_KU|0,E(_L1),E(new T4(0,(1+_KY|0)+_L4|0,E(_KV),_KX,E(_L2))),E(new T4(0,1+_L5.a|0,E(_KB),_L5,E(_Kw)))):new T4(0,1+_KU|0,E(_L1),E(new T4(0,(1+_KY|0)+_L4|0,E(_KV),_KX,E(_L2))),E(new T4(0,1,E(_KB),E(_Kw),E(_Kw))));},_L6=E(_L2);if(!_L6._){return _L3(_L6.a);}else{return _L3(0);}}else{return new T4(0,1+_KU|0,E(_KV),_KX,E(new T4(0,1+_L0|0,E(_KB),_KZ,E(_Kw))));}}else{return new T4(0,3,E(_KV),_KX,E(new T4(0,1,E(_KB),E(_Kw),E(_Kw))));}}else{var _L7=E(_KW);return (_L7._==0)?new T4(0,3,E(_L7.b),E(new T4(0,1,E(_KV),E(_Kw),E(_Kw))),E(new T4(0,1,E(_KB),E(_Kw),E(_Kw)))):new T4(0,2,E(_KB),_KT,E(_Kw));}}else{return new T4(0,1,E(_KB),E(_Kw),E(_Kw));}}},_L8=new T(function(){return unCStr("Failure in Data.Map.balanceR");}),_L9=new T(function(){var _La=_;return err(_L8);}),_Lb=function(_Lc,_Ld,_Le){var _Lf=E(_Ld);if(!_Lf._){var _Lg=_Lf.a,_Lh=E(_Le);if(!_Lh._){var _Li=_Lh.a,_Lj=_Lh.b;if(_Li<=(imul(3,_Lg)|0)){return new T4(0,(1+_Lg|0)+_Li|0,E(_Lc),_Lf,_Lh);}else{var _Lk=E(_Lh.c);if(!_Lk._){var _Ll=_Lk.a,_Lm=_Lk.b,_Ln=_Lk.c,_Lo=E(_Lh.d);if(!_Lo._){var _Lp=_Lo.a;if(_Ll>=(imul(2,_Lp)|0)){var _Lq=function(_Lr){var _Ls=E(_Lc),_Lt=E(_Lk.d);return (_Lt._==0)?new T4(0,(1+_Lg|0)+_Li|0,E(_Lm),E(new T4(0,(1+_Lg|0)+_Lr|0,_Ls,_Lf,E(_Ln))),E(new T4(0,(1+_Lp|0)+_Lt.a|0,E(_Lj),_Lt,_Lo))):new T4(0,(1+_Lg|0)+_Li|0,E(_Lm),E(new T4(0,(1+_Lg|0)+_Lr|0,_Ls,_Lf,E(_Ln))),E(new T4(0,1+_Lp|0,E(_Lj),E(_Kw),_Lo)));},_Lu=E(_Ln);if(!_Lu._){return _Lq(_Lu.a);}else{return _Lq(0);}}else{return new T4(0,(1+_Lg|0)+_Li|0,E(_Lj),E(new T4(0,(1+_Lg|0)+_Ll|0,E(_Lc),_Lf,_Lk)),_Lo);}}else{return E(_L9);}}else{return E(_L9);}}}else{return new T4(0,1+_Lg|0,E(_Lc),_Lf,E(_Kw));}}else{var _Lv=E(_Le);if(!_Lv._){var _Lw=_Lv.a,_Lx=_Lv.b,_Ly=_Lv.d,_Lz=E(_Lv.c);if(!_Lz._){var _LA=_Lz.a,_LB=_Lz.b,_LC=_Lz.c,_LD=E(_Ly);if(!_LD._){var _LE=_LD.a;if(_LA>=(imul(2,_LE)|0)){var _LF=function(_LG){var _LH=E(_Lc),_LI=E(_Lz.d);return (_LI._==0)?new T4(0,1+_Lw|0,E(_LB),E(new T4(0,1+_LG|0,_LH,E(_Kw),E(_LC))),E(new T4(0,(1+_LE|0)+_LI.a|0,E(_Lx),_LI,_LD))):new T4(0,1+_Lw|0,E(_LB),E(new T4(0,1+_LG|0,_LH,E(_Kw),E(_LC))),E(new T4(0,1+_LE|0,E(_Lx),E(_Kw),_LD)));},_LJ=E(_LC);if(!_LJ._){return _LF(_LJ.a);}else{return _LF(0);}}else{return new T4(0,1+_Lw|0,E(_Lx),E(new T4(0,1+_LA|0,E(_Lc),E(_Kw),_Lz)),_LD);}}else{return new T4(0,3,E(_LB),E(new T4(0,1,E(_Lc),E(_Kw),E(_Kw))),E(new T4(0,1,E(_Lx),E(_Kw),E(_Kw))));}}else{var _LK=E(_Ly);return (_LK._==0)?new T4(0,3,E(_Lx),E(new T4(0,1,E(_Lc),E(_Kw),E(_Kw))),_LK):new T4(0,2,E(_Lc),E(_Kw),_Lv);}}else{return new T4(0,1,E(_Lc),E(_Kw),E(_Kw));}}},_LL=function(_LM){return new T4(0,1,E(_LM),E(_Kw),E(_Kw));},_LN=function(_LO,_LP){var _LQ=E(_LP);if(!_LQ._){return _KA(_LQ.b,_LN(_LO,_LQ.c),_LQ.d);}else{return _LL(_LO);}},_LR=function(_LS,_LT){var _LU=E(_LT);if(!_LU._){return _Lb(_LU.b,_LU.c,_LR(_LS,_LU.d));}else{return _LL(_LS);}},_LV=function(_LW,_LX,_LY,_LZ,_M0){return _Lb(_LY,_LZ,_LR(_LW,_M0));},_M1=function(_M2,_M3,_M4,_M5,_M6){return _KA(_M4,_LN(_M2,_M5),_M6);},_M7=function(_M8,_M9,_Ma,_Mb,_Mc,_Md){var _Me=E(_M9);if(!_Me._){var _Mf=_Me.a,_Mg=_Me.b,_Mh=_Me.c,_Mi=_Me.d;if((imul(3,_Mf)|0)>=_Ma){if((imul(3,_Ma)|0)>=_Mf){return new T4(0,(_Mf+_Ma|0)+1|0,E(_M8),_Me,E(new T4(0,_Ma,E(_Mb),E(_Mc),E(_Md))));}else{return _Lb(_Mg,_Mh,B(_M7(_M8,_Mi,_Ma,_Mb,_Mc,_Md)));}}else{return _KA(_Mb,B(_Mj(_M8,_Mf,_Mg,_Mh,_Mi,_Mc)),_Md);}}else{return _M1(_M8,_Ma,_Mb,_Mc,_Md);}},_Mj=function(_Mk,_Ml,_Mm,_Mn,_Mo,_Mp){var _Mq=E(_Mp);if(!_Mq._){var _Mr=_Mq.a,_Ms=_Mq.b,_Mt=_Mq.c,_Mu=_Mq.d;if((imul(3,_Ml)|0)>=_Mr){if((imul(3,_Mr)|0)>=_Ml){return new T4(0,(_Ml+_Mr|0)+1|0,E(_Mk),E(new T4(0,_Ml,E(_Mm),E(_Mn),E(_Mo))),_Mq);}else{return _Lb(_Mm,_Mn,B(_M7(_Mk,_Mo,_Mr,_Ms,_Mt,_Mu)));}}else{return _KA(_Ms,B(_Mj(_Mk,_Ml,_Mm,_Mn,_Mo,_Mt)),_Mu);}}else{return _LV(_Mk,_Ml,_Mm,_Mn,_Mo);}},_Mv=function(_Mw,_Mx,_My){var _Mz=E(_Mx);if(!_Mz._){var _MA=_Mz.a,_MB=_Mz.b,_MC=_Mz.c,_MD=_Mz.d,_ME=E(_My);if(!_ME._){var _MF=_ME.a,_MG=_ME.b,_MH=_ME.c,_MI=_ME.d;if((imul(3,_MA)|0)>=_MF){if((imul(3,_MF)|0)>=_MA){return new T4(0,(_MA+_MF|0)+1|0,E(_Mw),_Mz,_ME);}else{return _Lb(_MB,_MC,B(_M7(_Mw,_MD,_MF,_MG,_MH,_MI)));}}else{return _KA(_MG,B(_Mj(_Mw,_MA,_MB,_MC,_MD,_MH)),_MI);}}else{return _LV(_Mw,_MA,_MB,_MC,_MD);}}else{return _LN(_Mw,_My);}},_MJ=function(_MK,_ML,_MM){var _MN=E(_ML);if(!_MN._){return E(_MM);}else{var _MO=function(_MP,_MQ){while(1){var _MR=E(_MQ);if(!_MR._){var _MS=_MR.b,_MT=_MR.d;switch(B(A3(_pS,_MK,_MP,_MS))){case 0:return C > 19 ? new F(function(){return _Mv(_MS,B(_MO(_MP,_MR.c)),_MT);}) : (++C,_Mv(_MS,B(_MO(_MP,_MR.c)),_MT));break;case 1:return E(_MT);default:_MQ=_MT;continue;}}else{return new T0(1);}}};return C > 19 ? new F(function(){return _MO(_MN.a,_MM);}) : (++C,_MO(_MN.a,_MM));}},_MU=function(_MV,_MW,_MX){var _MY=E(_MW);if(!_MY._){return E(_MX);}else{var _MZ=function(_N0,_N1){while(1){var _N2=E(_N1);if(!_N2._){var _N3=_N2.b,_N4=_N2.c;switch(B(A3(_pS,_MV,_N3,_N0))){case 0:return C > 19 ? new F(function(){return _Mv(_N3,_N4,B(_MZ(_N0,_N2.d)));}) : (++C,_Mv(_N3,_N4,B(_MZ(_N0,_N2.d))));break;case 1:return E(_N4);default:_N1=_N4;continue;}}else{return new T0(1);}}};return C > 19 ? new F(function(){return _MZ(_MY.a,_MX);}) : (++C,_MZ(_MY.a,_MX));}},_N5=function(_N6,_N7,_N8){var _N9=E(_N7),_Na=E(_N8);if(!_Na._){var _Nb=_Na.b,_Nc=_Na.c,_Nd=_Na.d;switch(B(A3(_pS,_N6,_N9,_Nb))){case 0:return _KA(_Nb,_N5(_N6,_N9,_Nc),_Nd);case 1:return _Na;default:return _Lb(_Nb,_Nc,_N5(_N6,_N9,_Nd));}}else{return new T4(0,1,_N9,E(_Kw),E(_Kw));}},_Ne=function(_Nf,_Ng,_Nh){return _N5(_Nf,_Ng,_Nh);},_Ni=function(_Nj,_Nk,_Nl,_Nm){var _Nn=E(_Nk);if(!_Nn._){var _No=E(_Nl);if(!_No._){return E(_Nm);}else{var _Np=function(_Nq,_Nr){while(1){var _Ns=E(_Nr);if(!_Ns._){if(!B(A3(_Fx,_Nj,_Ns.b,_Nq))){return _Ns;}else{_Nr=_Ns.c;continue;}}else{return new T0(1);}}};return _Np(_No.a,_Nm);}}else{var _Nt=_Nn.a,_Nu=E(_Nl);if(!_Nu._){var _Nv=function(_Nw,_Nx){while(1){var _Ny=E(_Nx);if(!_Ny._){if(!B(A3(_Fv,_Nj,_Ny.b,_Nw))){return _Ny;}else{_Nx=_Ny.d;continue;}}else{return new T0(1);}}};return _Nv(_Nt,_Nm);}else{var _Nz=function(_NA,_NB,_NC){while(1){var _ND=E(_NC);if(!_ND._){var _NE=_ND.b;if(!B(A3(_Fv,_Nj,_NE,_NA))){if(!B(A3(_Fx,_Nj,_NE,_NB))){return _ND;}else{_NC=_ND.c;continue;}}else{_NC=_ND.d;continue;}}else{return new T0(1);}}};return _Nz(_Nt,_Nu.a,_Nm);}}},_NF=function(_NG,_NH,_NI,_NJ,_NK){var _NL=E(_NK);if(!_NL._){var _NM=_NL.b,_NN=_NL.c,_NO=_NL.d,_NP=E(_NJ);if(!_NP._){var _NQ=_NP.b,_NR=function(_NS){var _NT=new T1(1,E(_NQ));return C > 19 ? new F(function(){return _Mv(_NQ,B(_NF(_NG,_NH,_NT,_NP.c,_Ni(_NG,_NH,_NT,_NL))),B(_NF(_NG,_NT,_NI,_NP.d,_Ni(_NG,_NT,_NI,_NL))));}) : (++C,_Mv(_NQ,B(_NF(_NG,_NH,_NT,_NP.c,_Ni(_NG,_NH,_NT,_NL))),B(_NF(_NG,_NT,_NI,_NP.d,_Ni(_NG,_NT,_NI,_NL)))));};if(!E(_NN)._){return C > 19 ? new F(function(){return _NR(_);}) : (++C,_NR(_));}else{if(!E(_NO)._){return C > 19 ? new F(function(){return _NR(_);}) : (++C,_NR(_));}else{return C > 19 ? new F(function(){return _Ne(_NG,_NM,_NP);}) : (++C,_Ne(_NG,_NM,_NP));}}}else{return C > 19 ? new F(function(){return _Mv(_NM,B(_MJ(_NG,_NH,_NN)),B(_MU(_NG,_NI,_NO)));}) : (++C,_Mv(_NM,B(_MJ(_NG,_NH,_NN)),B(_MU(_NG,_NI,_NO))));}}else{return E(_NJ);}},_NU=function(_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5){var _O6=function(_O7){var _O8=new T1(1,E(_NZ));return C > 19 ? new F(function(){return _Mv(_NZ,B(_NF(_NV,_NW,_O8,_O0,_Ni(_NV,_NW,_O8,new T4(0,_O2,E(_O3),E(_O4),E(_O5))))),B(_NF(_NV,_O8,_NX,_O1,_Ni(_NV,_O8,_NX,new T4(0,_O2,E(_O3),E(_O4),E(_O5))))));}) : (++C,_Mv(_NZ,B(_NF(_NV,_NW,_O8,_O0,_Ni(_NV,_NW,_O8,new T4(0,_O2,E(_O3),E(_O4),E(_O5))))),B(_NF(_NV,_O8,_NX,_O1,_Ni(_NV,_O8,_NX,new T4(0,_O2,E(_O3),E(_O4),E(_O5)))))));};if(!E(_O4)._){return C > 19 ? new F(function(){return _O6(_);}) : (++C,_O6(_));}else{if(!E(_O5)._){return C > 19 ? new F(function(){return _O6(_);}) : (++C,_O6(_));}else{return C > 19 ? new F(function(){return _Ne(_NV,_O3,new T4(0,_NY,E(_NZ),E(_O0),E(_O1)));}) : (++C,_Ne(_NV,_O3,new T4(0,_NY,E(_NZ),E(_O0),E(_O1))));}}},_O9=function(_Oa,_Ob){var _Oc=E(_Oa);if(!_Oc._){var _Od=E(_Ob);if(!_Od._){return C > 19 ? new F(function(){return _NU(_C6,__Z,__Z,_Oc.a,_Oc.b,_Oc.c,_Oc.d,_Od.a,_Od.b,_Od.c,_Od.d);}) : (++C,_NU(_C6,__Z,__Z,_Oc.a,_Oc.b,_Oc.c,_Oc.d,_Od.a,_Od.b,_Od.c,_Od.d));}else{return _Oc;}}else{return E(_Ob);}},_Oe=new T2(0,_O9,_Kw),_Of=function(_Og){return (E(_Og)._==0)?false:true;},_Oh=function(_Oi,_Oj,_Ok,_Ol){var _Om=E(_Ol);if(!_Om._){var _On=new T(function(){var _Oo=_Oh(_Om.a,_Om.b,_Om.c,_Om.d);return new T2(0,_Oo.a,_Oo.b);});return new T2(0,new T(function(){return E(E(_On).a);}),new T(function(){return _KA(_Oj,_Ok,E(_On).b);}));}else{return new T2(0,_Oj,_Ok);}},_Op=function(_Oq,_Or,_Os,_Ot){var _Ou=E(_Os);if(!_Ou._){var _Ov=new T(function(){var _Ow=_Op(_Ou.a,_Ou.b,_Ou.c,_Ou.d);return new T2(0,_Ow.a,_Ow.b);});return new T2(0,new T(function(){return E(E(_Ov).a);}),new T(function(){return _Lb(_Or,E(_Ov).b,_Ot);}));}else{return new T2(0,_Or,_Ot);}},_Ox=function(_Oy,_Oz){var _OA=E(_Oy);if(!_OA._){var _OB=_OA.a,_OC=E(_Oz);if(!_OC._){var _OD=_OC.a;if(_OB<=_OD){var _OE=_Op(_OD,_OC.b,_OC.c,_OC.d);return _KA(_OE.a,_OA,_OE.b);}else{var _OF=_Oh(_OB,_OA.b,_OA.c,_OA.d);return _Lb(_OF.a,_OF.b,_OC);}}else{return _OA;}}else{return E(_Oz);}},_OG=function(_OH,_OI,_OJ){var _OK=E(_OI),_OL=E(_OJ);if(!_OL._){var _OM=_OL.b,_ON=_OL.c,_OO=_OL.d;switch(B(A3(_pS,_OH,_OK,_OM))){case 0:return _Lb(_OM,B(_OG(_OH,_OK,_ON)),_OO);case 1:return _Ox(_ON,_OO);default:return _KA(_OM,_ON,B(_OG(_OH,_OK,_OO)));}}else{return new T0(1);}},_OP=function(_OQ,_OR,_OS){return C > 19 ? new F(function(){return _OG(_OQ,_OR,_OS);}) : (++C,_OG(_OQ,_OR,_OS));},_OT=function(_OU,_OV,_OW){var _OX=E(_OV),_OY=E(_OW);if(!_OY._){var _OZ=_OY.b,_P0=_OY.c,_P1=_OY.d;switch(B(A3(_pS,_OU,_OX,_OZ))){case 0:return _KA(_OZ,_OT(_OU,_OX,_P0),_P1);case 1:return new T4(0,_OY.a,_OX,E(_P0),E(_P1));default:return _Lb(_OZ,_P0,_OT(_OU,_OX,_P1));}}else{return new T4(0,1,_OX,E(_Kw),E(_Kw));}},_P2=function(_P3,_P4,_P5){return _OT(_P3,_P4,_P5);},_P6=function(_P7,_P8,_P9){var _Pa=function(_Pb,_Pc){while(1){var _Pd=E(_Pb),_Pe=E(_Pc);if(!_Pe._){switch(B(A3(_pS,_P7,_Pd,_Pe.b))){case 0:_Pb=_Pd;_Pc=_Pe.c;continue;case 1:return true;default:_Pb=_Pd;_Pc=_Pe.d;continue;}}else{return false;}}};return _Pa(_P8,_P9);},_Pf=function(_Pg,_Ph,_Pi){var _Pj=new T(function(){return B(A1(_Pi,_Of));}),_Pk=function(_Pl,_Pm){var _Pn=new T(function(){return B(_P2(_Pg,_Ph,_Pm));}),_Po=new T(function(){return B(_OP(_Pg,_Ph,_Pm));}),_Pp=new T(function(){var _Pq=new T(function(){return B(A1(_Pl,new T(function(){if(!_P6(_Pg,_Ph,_Pm)){return __Z;}else{return E(new T1(1,_2L));}})));});return B(A1(_Pj,_Pq));});return C > 19 ? new F(function(){return A2(_Pi,function(_Pr){return (!E(_Pr))?E(_Po):E(_Pn);},_Pp);}) : (++C,A2(_Pi,function(_Pr){return (!E(_Pr))?E(_Po):E(_Pn);},_Pp));};return _Pk;},_Ps=new T2(0,_Oe,function(_Pt,_Pu){return _Pf(_C6,_Pt,_Pu);}),_Pv=function(_Pw,_Px){if(_Pw<=_Px){var _Py=function(_Pz){return new T2(1,_Pz,new T(function(){if(_Pz!=_Px){return _Py(_Pz+1|0);}else{return __Z;}}));};return _Py(_Pw);}else{return __Z;}},_PA=new T(function(){return _Pv(0,2147483647);}),_PB=function(_PC,_PD){var _PE=function(_PF,_PG,_PH){var _PI=E(_PG);if(!_PI._){var _PJ=E(_PI.a),_PK=E(_PF);if(_PJ>=_PK){var _PL=new T(function(){var _PM=function(_PN){var _PO=E(_PN);return (_PO._==0)?__Z:new T2(1,new T(function(){return _PP(_PK,_PO.a);}),new T(function(){return _PM(_PO.b);}));};return _PM(_PH);});return new T2(0,new T1(0,new T(function(){return _PK+B(A1(_PC,_PJ-_PK|0))|0;})),_PL);}else{var _PQ=new T(function(){var _PR=function(_PS){var _PT=E(_PS);return (_PT._==0)?__Z:new T2(1,new T(function(){return _PP(_PK,_PT.a);}),new T(function(){return _PR(_PT.b);}));};return _PR(_PH);});return new T2(0,_PI,_PQ);}}else{var _PU=_PI.a,_PV=new T(function(){var _PW=function(_PX){var _PY=E(_PX);return (_PY._==0)?__Z:new T2(1,new T(function(){return _PP(_PF,_PY.a);}),new T(function(){return _PW(_PY.b);}));};return _PW(_PH);}),_PZ=new T(function(){var _Q0=E(_PI.c),_Q1=_PE(new T(function(){return E(_PF)+B(A3(_2B,_6g,_CV(_CS(_PU)),0))|0;}),_Q0.a,_Q0.b);return new T2(0,_Q1.a,_Q1.b);}),_Q2=new T(function(){var _Q3=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_PU)),0));}),_Q4=function(_Q5){var _Q6=E(_Q5);if(!_Q6._){return __Z;}else{var _Q7=new T(function(){return E(_PF)+(E(_Q3)+E(_Q6.a)|0)|0;});return new T2(1,function(_Q8){return _PP(_Q7,_Q8);},new T(function(){return _Q4(_Q6.b);}));}};return _IF(_Q4(_PA),_PI.b);}),_Q9=new T(function(){var _Qa=function(_Qb){var _Qc=E(_Qb);if(!_Qc._){return __Z;}else{var _Qd=new T(function(){return E(_PF)+E(_Qc.a)|0;}),_Qe=function(_Qf){var _Qg=E(_Qf);return new T3(0,_Qg.a,new T(function(){return _PP(_Qd,_Qg.b);}),new T(function(){return _PP(_Qd,_Qg.c);}));};return new T2(1,_Qe,new T(function(){return _Qa(_Qc.b);}));}};return _ss(_IF(_Qa(_PA),new T(function(){return _ss(_PU,__Z);},1)),__Z);});return new T2(0,new T3(1,_Q9,_Q2,_PZ),_PV);}},_PP=function(_Qh,_Qi){var _Qj=E(_Qi);switch(_Qj._){case 0:var _Qk=new T(function(){return _PP(new T(function(){return E(_Qh)+1|0;}),_Qj.d);});return new T4(0,_Qj.a,_Qj.b,new T(function(){return _PP(_Qh,_Qj.c);}),_Qk);case 1:return new T1(1,new T(function(){var _Ql=E(_Qj.a),_Qm=_PE(_Qh,_Ql.a,_Ql.b);return new T2(0,_Qm.a,_Qm.b);}));default:return _Qj;}};return _PP(0,_PD);},_Qn=function(_Qo,_Qp,_Qq,_Qr,_Qs){var _Qt=E(_Qo);if(!_Qt._){var _Qu=_Qt.a,_Qv=_Qt.b,_Qw=_Qt.c,_Qx=_Qt.d;if((imul(3,_Qu)|0)>=_Qp){if((imul(3,_Qp)|0)>=_Qu){return _Ox(_Qt,new T4(0,_Qp,E(_Qq),E(_Qr),E(_Qs)));}else{return _Lb(_Qv,_Qw,B(_Qn(_Qx,_Qp,_Qq,_Qr,_Qs)));}}else{return _KA(_Qq,B(_Qy(_Qu,_Qv,_Qw,_Qx,_Qr)),_Qs);}}else{return new T4(0,_Qp,E(_Qq),E(_Qr),E(_Qs));}},_Qy=function(_Qz,_QA,_QB,_QC,_QD){var _QE=E(_QD);if(!_QE._){var _QF=_QE.a,_QG=_QE.b,_QH=_QE.c,_QI=_QE.d;if((imul(3,_Qz)|0)>=_QF){if((imul(3,_QF)|0)>=_Qz){return _Ox(new T4(0,_Qz,E(_QA),E(_QB),E(_QC)),_QE);}else{return _Lb(_QA,_QB,B(_Qn(_QC,_QF,_QG,_QH,_QI)));}}else{return _KA(_QG,B(_Qy(_Qz,_QA,_QB,_QC,_QH)),_QI);}}else{return new T4(0,_Qz,E(_QA),E(_QB),E(_QC));}},_QJ=function(_QK,_QL){var _QM=E(_QK);if(!_QM._){var _QN=_QM.a,_QO=_QM.b,_QP=_QM.c,_QQ=_QM.d,_QR=E(_QL);if(!_QR._){var _QS=_QR.a,_QT=_QR.b,_QU=_QR.c,_QV=_QR.d;if((imul(3,_QN)|0)>=_QS){if((imul(3,_QS)|0)>=_QN){return _Ox(_QM,_QR);}else{return _Lb(_QO,_QP,B(_Qn(_QQ,_QS,_QT,_QU,_QV)));}}else{return _KA(_QT,B(_Qy(_QN,_QO,_QP,_QQ,_QU)),_QV);}}else{return _QM;}}else{return E(_QL);}},_QW=function(_QX,_QY,_QZ,_R0,_R1){var _R2=E(_R0);if(!_R2._){var _R3=E(_R1);if(!_R3._){var _R4=new T1(1,E(_R3.b));return C > 19 ? new F(function(){return _QJ(B(_QW(_QX,_QY,_R4,_Ni(_QX,_QY,_R4,_R2),_R3.c)),B(_QW(_QX,_R4,_QZ,_Ni(_QX,_R4,_QZ,_R2),_R3.d)));}) : (++C,_QJ(B(_QW(_QX,_QY,_R4,_Ni(_QX,_QY,_R4,_R2),_R3.c)),B(_QW(_QX,_R4,_QZ,_Ni(_QX,_R4,_QZ,_R2),_R3.d))));}else{return C > 19 ? new F(function(){return _Mv(_R2.b,B(_MJ(_QX,_QY,_R2.c)),B(_MU(_QX,_QZ,_R2.d)));}) : (++C,_Mv(_R2.b,B(_MJ(_QX,_QY,_R2.c)),B(_MU(_QX,_QZ,_R2.d))));}}else{return new T0(1);}},_R5=function(_R6,_R7,_R8,_R9,_Ra,_Rb,_Rc,_Rd,_Re,_Rf,_Rg){var _Rh=new T1(1,E(_Re));return C > 19 ? new F(function(){return _QJ(B(_QW(_R6,_R7,_Rh,_Ni(_R6,_R7,_Rh,new T4(0,_R9,E(_Ra),E(_Rb),E(_Rc))),_Rf)),B(_QW(_R6,_Rh,_R8,_Ni(_R6,_Rh,_R8,new T4(0,_R9,E(_Ra),E(_Rb),E(_Rc))),_Rg)));}) : (++C,_QJ(B(_QW(_R6,_R7,_Rh,_Ni(_R6,_R7,_Rh,new T4(0,_R9,E(_Ra),E(_Rb),E(_Rc))),_Rf)),B(_QW(_R6,_Rh,_R8,_Ni(_R6,_Rh,_R8,new T4(0,_R9,E(_Ra),E(_Rb),E(_Rc))),_Rg))));},_Ri=function(_Rj){return __Z;},_Rk=function(_Rl,_Rm){return E(_Rl)-E(_Rm)|0;},_Rn=function(_Ro,_Rp){return _Rk(_Rp,_Ro);},_Rq=function(_He){return _Rn(1,_He);},_Rr=new T(function(){return _Pf(_C6, -1,_4P);}),_Rs=function(_Rt,_Ru){var _Rv=E(_Ru);return (_Rv._==0)?new T4(0,_Rv.a,E(B(A1(_Rt,_Rv.b))),E(_Rs(_Rt,_Rv.c)),E(_Rs(_Rt,_Rv.d))):new T0(1);},_Rw=new T(function(){return _69(function(_Rx,_Ry,_Rz){return C > 19 ? new F(function(){return _3H(_Ry,_Rx,_Rz);}) : (++C,_3H(_Ry,_Rx,_Rz));},_66);}),_RA=function(_RB){return E(E(_RB).a);},_RC=function(_RD){var _RE=E(_RD);return (_RE._==0)?__Z:new T2(1,_RE.a,new T(function(){return _RC(_RE.b);}));},_RF=function(_RG,_RH,_RI){var _RJ=new T(function(){var _RK=new T(function(){return _2z(_RG);}),_RL=function(_RM){return new T1(1,new T(function(){var _RN=E(_RM);if(!_RN._){return E(_RK);}else{return E(_RN.a);}}));};return B(A(_Cn,[_RH,_RI,_4P,_RL]));});return function(_RO){return C > 19 ? new F(function(){return A1(_RJ,_RO);}) : (++C,A1(_RJ,_RO));};},_RP=function(_RQ,_RR,_RS){var _RT=function(_RU){var _RV=E(_RU);return (_RV._==0)?__Z:new T2(1,new T(function(){return _RF(_RQ,_RR,_RV.a);}),new T(function(){return _RT(_RV.b);}));};return C > 19 ? new F(function(){return A3(_2B,_Rw,_RC(_RT(_RS)),new T(function(){return _2z(_RA(_RR));}));}) : (++C,A3(_2B,_Rw,_RC(_RT(_RS)),new T(function(){return _2z(_RA(_RR));})));},_RW=function(_RX){return new T1(1,new T(function(){var _RY=E(_RX);if(!_RY._){return E(_2L);}else{return E(_RY.a);}}));},_RZ=function(_S0){var _S1=E(_S0);return (_S1._==0)?__Z:new T2(1,new T(function(){return B(_S2(_S1.a));}),new T(function(){return _RZ(_S1.b);}));},_S3=function(_S4){var _S5=E(_S4);return (_S5._==0)?__Z:new T2(1,new T(function(){return B(_S2(_S5.a));}),new T(function(){return _S3(_S5.b);}));},_S6=function(_S7,_S8){var _S9=E(_S7);if(!_S9._){return C > 19 ? new F(function(){return _O9(B(A(_Pf,[_C6,_S9.a,_4P,_RW,_Kw])),B(_2B(_Oe,_RZ(_S8))));}) : (++C,_O9(B(A(_Pf,[_C6,_S9.a,_4P,_RW,_Kw])),B(_2B(_Oe,_RZ(_S8)))));}else{var _Sa=E(_S9.c),_Sb=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_S9.a)),0));}),_Sc=B(_S6(_Sa.a,_Sa.b));if(!_Sc._){var _Sd=E(_Sb),_Se=B(_RP(_2M,_Ps,_Pv(0,_Sd-1|0)));if(!_Se._){return C > 19 ? new F(function(){return _O9(B(_2B(_Oe,_S3(_S8))),_Rs(function(_He){return _Rn(_Sd,_He);},B(_R5(_C6,__Z,__Z,_Sc.a,_Sc.b,_Sc.c,_Sc.d,_Se.a,_Se.b,_Se.c,_Se.d))));}) : (++C,_O9(B(_2B(_Oe,_S3(_S8))),_Rs(function(_He){return _Rn(_Sd,_He);},B(_R5(_C6,__Z,__Z,_Sc.a,_Sc.b,_Sc.c,_Sc.d,_Se.a,_Se.b,_Se.c,_Se.d)))));}else{return C > 19 ? new F(function(){return _O9(B(_2B(_Oe,_S3(_S8))),_Rs(function(_He){return _Rn(_Sd,_He);},_Sc));}) : (++C,_O9(B(_2B(_Oe,_S3(_S8))),_Rs(function(_He){return _Rn(_Sd,_He);},_Sc)));}}else{return C > 19 ? new F(function(){return _O9(B(_2B(_Oe,_S3(_S8))),_Rs(function(_He){return _Rn(_Sb,_He);},_Kw));}) : (++C,_O9(B(_2B(_Oe,_S3(_S8))),_Rs(function(_He){return _Rn(_Sb,_He);},_Kw)));}}},_Sf=function(_Sg){var _Sh=E(_Sg);return C > 19 ? new F(function(){return _S6(_Sh.a,_Sh.b);}) : (++C,_S6(_Sh.a,_Sh.b));},_S2=function(_Si){var _Sj=E(_Si);switch(_Sj._){case 0:return C > 19 ? new F(function(){return _O9(B(_S2(_Sj.c)),B(A2(_Rr,_Ri,new T(function(){return _Rs(_Rq,B(_S2(_Sj.d)));}))));}) : (++C,_O9(B(_S2(_Sj.c)),B(A2(_Rr,_Ri,new T(function(){return _Rs(_Rq,B(_S2(_Sj.d)));})))));break;case 1:return C > 19 ? new F(function(){return _Sf(_Sj.a);}) : (++C,_Sf(_Sj.a));break;default:return new T0(1);}},_Sk=function(_Sl,_Sm){while(1){var _Sn=(function(_So,_Sp){var _Sq=E(_Sp);if(!_Sq._){var _Sr=new T(function(){return _Sk(_So,_Sq.d);}),_Ss=function(_St){return C > 19 ? new F(function(){return A1(_Sq.b,new T(function(){return B(A1(_Sr,_St));}));}) : (++C,A1(_Sq.b,new T(function(){return B(A1(_Sr,_St));})));};_Sl=_Ss;_Sm=_Sq.c;return __continue;}else{return E(_So);}})(_Sl,_Sm);if(_Sn!=__continue){return _Sn;}}},_Su=function(_Sv){return E(E(_Sv).c);},_Sw=new T(function(){return err(new T(function(){return unCStr("\'subst\' should not be called with a negative index");}));}),_Sx=function(_Sy,_Sz){return false;},_SA=new T(function(){return B(A3(_Sk,_n,new T(function(){return _Rs(_Sx,_Kw);}),true));}),_SB=new T(function(){return unCStr("Prod");}),_SC=new T(function(){return unCStr("Lambda");}),_SD=new T(function(){return unCStr("Ap ");}),_SE=function(_SF,_SG,_SH){return C > 19 ? new F(function(){return A1(_SF,new T2(1,44,new T(function(){return B(A1(_SG,_SH));})));}) : (++C,A1(_SF,new T2(1,44,new T(function(){return B(A1(_SG,_SH));}))));},_SI=new T(function(){return _mo(new T(function(){return unCStr("foldr1");}));}),_SJ=function(_SK,_SL){var _SM=E(_SL);if(!_SM._){return E(_SI);}else{var _SN=_SM.a,_SO=E(_SM.b);if(!_SO._){return E(_SN);}else{return C > 19 ? new F(function(){return A2(_SK,_SN,new T(function(){return B(_SJ(_SK,_SO));}));}) : (++C,A2(_SK,_SN,new T(function(){return B(_SJ(_SK,_SO));})));}}},_SP=new T(function(){return unCStr("Mu ");}),_SQ=new T(function(){return unCStr("Sym ");}),_SR=function(_SS){return E(E(_SS).a);},_ST=function(_SU,_SV,_SW){var _SX=E(_SW);if(!_SX._){var _SY=_SX.a;if(_SV<11){var _SZ=function(_T0){return _0(_SQ,new T(function(){return _ck(11,E(_SY),_T0);},1));};return _SZ;}else{var _T1=function(_T2){var _T3=new T(function(){return _0(_SQ,new T(function(){return _ck(11,E(_SY),new T2(1,41,_T2));},1));});return new T2(1,40,_T3);};return _T1;}}else{var _T4=new T(function(){var _T5=E(_SX.c);return _T6(_SU,11,_T5.a,_T5.b);}),_T7=function(_T8){return _T9(_SU,0,_T8);},_Ta=function(_Tb,_Tc){var _Td=E(_Tb),_Te=new T(function(){return B(A3(_SJ,_SE,new T2(1,new T(function(){return B(A3(_SR,_SU,0,_Td.a));}),new T2(1,new T(function(){return _T9(_SU,0,_Td.b);}),new T2(1,new T(function(){return _T9(_SU,0,_Td.c);}),__Z))),new T2(1,41,_Tc)));});return new T2(1,40,_Te);},_Tf=function(_Tg){var _Th=new T(function(){var _Ti=new T(function(){return _1R(_T7,_SX.b,new T2(1,32,new T(function(){return B(A1(_T4,_Tg));})));});return _1R(_Ta,_SX.a,new T2(1,32,_Ti));},1);return _0(_SP,_Th);};if(_SV<11){return _Tf;}else{var _Tj=function(_Tk){return new T2(1,40,new T(function(){return _Tf(new T2(1,41,_Tk));}));};return _Tj;}}},_T6=function(_Tl,_Tm,_Tn,_To){var _Tp=new T(function(){return _ST(_Tl,11,_Tn);}),_Tq=function(_Tr){return _T9(_Tl,0,_Tr);},_Ts=function(_Tt){var _Tu=new T(function(){return B(A1(_Tp,new T2(1,32,new T(function(){return _1R(_Tq,_To,_Tt);}))));},1);return _0(_SD,_Tu);};if(_Tm<11){return _Ts;}else{var _Tv=function(_Tw){return new T2(1,40,new T(function(){return _Ts(new T2(1,41,_Tw));}));};return _Tv;}},_Tx=new T(function(){return unCStr("Cons ");}),_Ty=new T(function(){return unCStr("Bind ");}),_Tz=new T(function(){return unCStr("Universe ");}),_T9=function(_TA,_TB,_TC){var _TD=E(_TC);switch(_TD._){case 0:var _TE=new T(function(){return B(A3(_SR,_TA,11,_TD.b));}),_TF=new T(function(){return _T9(_TA,11,_TD.c);}),_TG=new T(function(){return _T9(_TA,11,_TD.d);}),_TH=function(_TI){var _TJ=new T(function(){var _TK=new T(function(){var _TL=new T(function(){return B(A1(_TF,new T2(1,32,new T(function(){return B(A1(_TG,_TI));}))));});return B(A1(_TE,new T2(1,32,_TL)));});if(!E(_TD.a)){return _0(_SC,new T2(1,32,_TK));}else{return _0(_SB,new T2(1,32,_TK));}},1);return _0(_Ty,_TJ);};if(_TB<11){return _TH;}else{var _TM=function(_TN){return new T2(1,40,new T(function(){return _TH(new T2(1,41,_TN));}));};return _TM;}break;case 1:var _TO=new T(function(){var _TP=E(_TD.a);return _T6(_TA,11,_TP.a,_TP.b);});if(_TB<11){var _TQ=function(_TR){return _0(_Tx,new T(function(){return B(A1(_TO,_TR));},1));};return _TQ;}else{var _TS=function(_TT){var _TU=new T(function(){return _0(_Tx,new T(function(){return B(A1(_TO,new T2(1,41,_TT)));},1));});return new T2(1,40,_TU);};return _TS;}break;default:var _TV=_TD.a;if(_TB<11){var _TW=function(_TX){return _0(_Tz,new T(function(){return _ck(11,E(_TV),_TX);},1));};return _TW;}else{var _TY=function(_TZ){var _U0=new T(function(){return _0(_Tz,new T(function(){return _ck(11,E(_TV),new T2(1,41,_TZ));},1));});return new T2(1,40,_U0);};return _TY;}}},_U1=new T(function(){return unCStr("Cannot produce an induction principle for a term : ");}),_U2=function(_U3,_U4){return err(_nK(_U1,new T(function(){return B(A(_T9,[_U3,0,_U4,__Z]));},1)));},_U5=new T2(0,new T1(0,0),__Z),_U6=function(_U7){return new T2(0,_U7,__Z);},_U8=new T(function(){return _U6(_nK);}),_U9=function(_Ua){var _Ub=E(_Ua);return (_Ub._==0)?__Z:new T2(1,function(_Uc){var _Ud=E(_Ub.a);return new T4(0,0,_Ud.a,_Ud.c,E(_Uc));},new T(function(){return _U9(_Ub.b);}));},_Ue=function(_Uf){var _Ug=E(_Uf);return (_Ug._==0)?__Z:new T2(1,function(_Uh){var _Ui=E(_Ug.a);return new T4(0,0,_Ui.a,_Ui.b,E(_Uh));},new T(function(){return _Ue(_Ug.b);}));},_Uj=function(_Uk){var _Ul=E(_Uk);return (_Ul._==0)?__Z:new T2(1,new T(function(){return E(E(_Ul.a).c);}),new T(function(){return _Uj(_Ul.b);}));},_Um=function(_Un){var _Uo=E(_Un);return (_Uo._==0)?__Z:new T2(1,new T1(1,new T2(0,new T1(0,_Uo.a),__Z)),new T(function(){return _Um(_Uo.b);}));},_Up=new T(function(){return unCStr("Invalid substitution of non-lambda expression : ");}),_Uq=function(_Ur,_Us){return err(_nK(_Up,new T(function(){return B(A(_T9,[_Us,0,_Ur,__Z]));},1)));},_Ut=function(_Uu,_Uv,_Uw,_Ux){var _Uy=new T(function(){return _Ku(_Uv);}),_Uz=_Ks(_Uu),_UA=new T(function(){return _2V(new T(function(){return _2P(_Uz);}));}),_UB=function(_UC,_UD){var _UE=function(_UF){var _UG=E(_UD);if(_UG._==1){var _UH=E(_UG.a);return C > 19 ? new F(function(){return A1(_UA,new T1(1,new T2(0,_UH.a,new T(function(){return _nK(_UH.b,_UC);}))));}) : (++C,A1(_UA,new T1(1,new T2(0,_UH.a,new T(function(){return _nK(_UH.b,_UC);})))));}else{if(!E(_UC)._){return C > 19 ? new F(function(){return A1(_UA,_UG);}) : (++C,A1(_UA,_UG));}else{return _Uq(_UG,_Uy);}}},_UI=E(_UC);if(!_UI._){return C > 19 ? new F(function(){return _UE(_);}) : (++C,_UE(_));}else{var _UJ=E(_UD);if(!_UJ._){if(!E(_UJ.a)){return C > 19 ? new F(function(){return A3(_2X,_Uz,new T(function(){return B(_UK(_Uv,_Uu,_UI.a,0,_UJ.d));}),function(_He){return C > 19 ? new F(function(){return _UB(_UI.b,_He);}) : (++C,_UB(_UI.b,_He));});}) : (++C,A3(_2X,_Uz,new T(function(){return B(_UK(_Uv,_Uu,_UI.a,0,_UJ.d));}),function(_He){return C > 19 ? new F(function(){return _UB(_UI.b,_He);}) : (++C,_UB(_UI.b,_He));}));}else{return C > 19 ? new F(function(){return _UE(_);}) : (++C,_UE(_));}}else{return C > 19 ? new F(function(){return _UE(_);}) : (++C,_UE(_));}}};return C > 19 ? new F(function(){return _UB(_Uw,_Ux);}) : (++C,_UB(_Uw,_Ux));},_UK=function(_UL,_UM,_UN,_UO,_UP){if(_UO<0){return E(_Sw);}else{var _UQ=_Ks(_UM),_UR=new T(function(){return _2P(_UQ);}),_US=new T(function(){return _2T(_UR);}),_UT=new T(function(){return _2R(_US);}),_UU=new T(function(){return _2V(_UR);}),_UV=new T(function(){return _Ku(_UL);}),_UW=function(_UX,_UY,_UZ){while(1){var _V0=B((function(_V1,_V2,_V3){var _V4=new T(function(){return _Ue(_V1);}),_V5=function(_V6){var _V7=E(_V3);if(_V7._==1){var _V8=E(_V7.a),_V9=E(_V8.a);if(!_V9._){var _Va=B(A3(_2B,_6g,_CV(_CS(_V1)),0));if(E(_V9.a)>=_Va){return C > 19 ? new F(function(){return A1(_UU,new T1(1,new T2(0,new T3(1,_V1,_V2,_V8),__Z)));}) : (++C,A1(_UU,new T1(1,new T2(0,new T3(1,_V1,_V2,_V8),__Z))));}else{var _Vb=new T(function(){return _U9(_V1);}),_Vc=function(_Vd){return C > 19 ? new F(function(){return A1(_UU,new T(function(){return B(A3(_2B,_6g,_Vb,_Vd));}));}) : (++C,A1(_UU,new T(function(){return B(A3(_2B,_6g,_Vb,_Vd));})));},_Ve=new T(function(){var _Vf=new T(function(){var _Vg=new T(function(){return B(_RP(_2M,_Ps,_Pv(0,_Va-1|0)));}),_Vh=new T(function(){return _ss(_Uj(_V1),__Z);}),_Vi=new T(function(){return _Um(_ss(_Pv(1,_Va),__Z));}),_Vj=function(_Vk){var _Vl=E(_Vk);if(!_Vl._){return __Z;}else{var _Vm=_Vl.a,_Vn=new T(function(){var _Vo=function(_Vp){var _Vq=new T(function(){var _Vr=new T(function(){var _Vs=E(_Va);if(!_Vs){return B(A3(_2B,_6g,_V4,_Vm));}else{return _PB(function(_Vt){return E(_Vt)+_Vs|0;},B(A3(_2B,_6g,_V4,_Vm)));}});return B(A1(_UU,_Vr));});return new T2(1,_Vq,new T2(1,new T(function(){return B(_UK(_UL,_UM,_Vm,0,new T1(1,new T2(0,new T3(1,__Z,_Vh,_U5),_Vi))));}),__Z));},_Vu=B(_S2(_Vm));if(!_Vu._){var _Vv=E(_Vg);if(!_Vv._){if(!B(A3(_Sk,_n,_Rs(_Sx,B(_R5(_C6,__Z,__Z,_Vu.a,_Vu.b,_Vu.c,_Vu.d,_Vv.a,_Vv.b,_Vv.c,_Vv.d))),true))){return _Vo(_);}else{return new T2(1,new T(function(){return B(A1(_UU,_Vm));}),__Z);}}else{if(!B(A3(_Sk,_n,_Rs(_Sx,_Vu),true))){return _Vo(_);}else{return new T2(1,new T(function(){return B(A1(_UU,_Vm));}),__Z);}}}else{if(!E(_SA)){return _Vo(_);}else{return new T2(1,new T(function(){return B(A1(_UU,_Vm));}),__Z);}}});return new T2(1,_Vn,new T(function(){return _Vj(_Vl.b);}));}};return B(_Kk(_UR,B(_2B(_U8,_Vj(_V8.b)))));});return B(A2(_UT,function(_Vw){return new T1(1,new T2(0,_V9,_Vw));},_Vf));});return C > 19 ? new F(function(){return A3(_2X,_UQ,_Ve,_Vc);}) : (++C,A3(_2X,_UQ,_Ve,_Vc));}}else{return C > 19 ? new F(function(){return A1(_UU,new T1(1,new T2(0,new T3(1,_V1,_V2,_V8),__Z)));}) : (++C,A1(_UU,new T1(1,new T2(0,new T3(1,_V1,_V2,_V8),__Z))));}}else{return _U2(_UV,_V7);}},_Vx=E(_V2);if(!_Vx._){return C > 19 ? new F(function(){return _V5(_);}) : (++C,_V5(_));}else{var _Vy=E(_V3);if(!_Vy._){if(!E(_Vy.a)){var _Vz=new T2(1,new T3(0,_Vy.b,_Vy.c,_Vx.a),_V1);_UX=_Vz;_UY=_Vx.b;_UZ=_Vy.d;return __continue;}else{return C > 19 ? new F(function(){return _V5(_);}) : (++C,_V5(_));}}else{return C > 19 ? new F(function(){return _V5(_);}) : (++C,_V5(_));}}})(_UX,_UY,_UZ));if(_V0!=__continue){return _V0;}}},_VA=function(_VB,_VC,_VD){var _VE=E(_VC);if(!_VE._){var _VF=_VE.a,_VG=new T(function(){var _VH=E(_VB);if(!_VH){return E(_UN);}else{return _PB(function(_VI){return E(_VI)+_VH|0;},_UN);}}),_VJ=new T(function(){return E(_VF)-1|0;}),_VK=new T(function(){var _VL=E(_VF),_VM=E(_VB);if(_VL>=_VM){if(_VL!=_VM){return 2;}else{return 1;}}else{return 0;}}),_VN=new T(function(){var _VO=function(_VP){var _VQ=E(_VP);return (_VQ._==0)?__Z:new T2(1,new T(function(){return B(_VR(_VB,_VQ.a));}),new T(function(){return _VO(_VQ.b);}));};return B(_Kk(_UR,_VO(_VD)));});return C > 19 ? new F(function(){return A3(_2X,_UQ,_VN,function(_VS){switch(E(_VK)){case 0:return C > 19 ? new F(function(){return A1(_UU,new T1(1,new T2(0,_VE,_VS)));}) : (++C,A1(_UU,new T1(1,new T2(0,_VE,_VS))));break;case 1:return C > 19 ? new F(function(){return _Ut(_UM,_UL,_VS,_VG);}) : (++C,_Ut(_UM,_UL,_VS,_VG));break;default:return C > 19 ? new F(function(){return A1(_UU,new T1(1,new T2(0,new T1(0,_VJ),_VS)));}) : (++C,A1(_UU,new T1(1,new T2(0,new T1(0,_VJ),_VS))));}});}) : (++C,A3(_2X,_UQ,_VN,function(_VS){switch(E(_VK)){case 0:return C > 19 ? new F(function(){return A1(_UU,new T1(1,new T2(0,_VE,_VS)));}) : (++C,A1(_UU,new T1(1,new T2(0,_VE,_VS))));break;case 1:return C > 19 ? new F(function(){return _Ut(_UM,_UL,_VS,_VG);}) : (++C,_Ut(_UM,_UL,_VS,_VG));break;default:return C > 19 ? new F(function(){return A1(_UU,new T1(1,new T2(0,new T1(0,_VJ),_VS)));}) : (++C,A1(_UU,new T1(1,new T2(0,new T1(0,_VJ),_VS))));}}));}else{var _VT=_VE.a,_VU=new T(function(){var _VV=function(_VW){var _VX=E(_VW);return (_VX._==0)?__Z:new T2(1,new T(function(){return B(_VR(_VB,_VX.a));}),new T(function(){return _VV(_VX.b);}));};return B(_Kk(_UR,_VV(_VD)));}),_VY=new T(function(){var _VZ=function(_W0){var _W1=E(_W0);if(!_W1._){return __Z;}else{var _W2=new T(function(){return E(_VB)+E(_W1.a)|0;}),_W3=function(_W4){var _W5=E(_W4),_W6=new T(function(){return B(A3(_2R,_US,function(_W7,_W8){return new T3(0,_W5.a,_W7,_W8);},new T(function(){return B(_VR(_W2,_W5.b));})));});return C > 19 ? new F(function(){return A3(_s6,_US,_W6,new T(function(){return B(_VR(_W2,_W5.c));}));}) : (++C,A3(_s6,_US,_W6,new T(function(){return B(_VR(_W2,_W5.c));})));};return new T2(1,_W3,new T(function(){return _VZ(_W1.b);}));}};return B(_Kk(_UR,_ss(_IF(_VZ(_PA),new T(function(){return _ss(_VT,__Z);},1)),__Z)));}),_W9=new T(function(){var _Wa=function(_Wb){var _Wc=E(_Wb);if(!_Wc._){return __Z;}else{var _Wd=new T(function(){return _Kp(_VB,_Wc.a);});return new T2(1,function(_He){return C > 19 ? new F(function(){return _VR(_Wd,_He);}) : (++C,_VR(_Wd,_He));},new T(function(){return _Wa(_Wc.b);}));}};return B(_Kk(_UR,_IF(_Wa(_Pv(B(A3(_2B,_6g,_CV(_CS(_VT)),0)),2147483647)),_VE.b)));}),_We=function(_Wf){var _Wg=function(_Wh){var _Wi=function(_He){return C > 19 ? new F(function(){return _Ut(_UM,_UL,_Wh,_He);}) : (++C,_Ut(_UM,_UL,_Wh,_He));},_Wj=function(_Wk){var _Wl=function(_Wm){var _Wn=E(_Wf);if(_Wn._==1){return C > 19 ? new F(function(){return A1(_UU,new T1(1,new T2(0,new T3(1,_Wk,_Wm,_Wn.a),_Wh)));}) : (++C,A1(_UU,new T1(1,new T2(0,new T3(1,_Wk,_Wm,_Wn.a),_Wh))));}else{return C > 19 ? new F(function(){return A3(_2X,_UQ,new T(function(){return _UW(_Wk,_Wm,_Wn);}),_Wi);}) : (++C,A3(_2X,_UQ,new T(function(){return _UW(_Wk,_Wm,_Wn);}),_Wi));}};return C > 19 ? new F(function(){return A3(_2X,_UQ,_W9,_Wl);}) : (++C,A3(_2X,_UQ,_W9,_Wl));};return C > 19 ? new F(function(){return A3(_2X,_UQ,_VY,_Wj);}) : (++C,A3(_2X,_UQ,_VY,_Wj));};return C > 19 ? new F(function(){return A3(_2X,_UQ,_VU,_Wg);}) : (++C,A3(_2X,_UQ,_VU,_Wg));},_Wo=new T(function(){var _Wp=E(_VE.c);return B(_VA(new T(function(){return E(_VB)+B(A3(_2B,_6g,_CV(_CS(_VT)),0))|0;}),_Wp.a,_Wp.b));});return C > 19 ? new F(function(){return A3(_2X,_UQ,_Wo,_We);}) : (++C,A3(_2X,_UQ,_Wo,_We));}},_VR=function(_Wq,_Wr){var _Ws=E(_Wr);switch(_Ws._){case 0:var _Wt=new T(function(){return B(_VR(new T(function(){return E(_Wq)+1|0;}),_Ws.d));}),_Wu=function(_Wv){var _Ww=new T(function(){return B(A3(_Su,_UM,function(_He){return new T2(1,_Wv,_He);},_Wt));});return C > 19 ? new F(function(){return A2(_UT,function(_He){return new T4(0,_Ws.a,_Ws.b,_Wv,_He);},_Ww);}) : (++C,A2(_UT,function(_He){return new T4(0,_Ws.a,_Ws.b,_Wv,_He);},_Ww));};return C > 19 ? new F(function(){return A3(_2X,_UQ,new T(function(){return B(_VR(_Wq,_Ws.c));}),_Wu);}) : (++C,A3(_2X,_UQ,new T(function(){return B(_VR(_Wq,_Ws.c));}),_Wu));break;case 1:var _Wx=E(_Ws.a);return C > 19 ? new F(function(){return _VA(_Wq,_Wx.a,_Wx.b);}) : (++C,_VA(_Wq,_Wx.a,_Wx.b));break;default:return C > 19 ? new F(function(){return A1(_UU,_Ws);}) : (++C,A1(_UU,_Ws));}};return C > 19 ? new F(function(){return _VR(_UO,_UP);}) : (++C,_VR(_UO,_UP));}},_Wy=function(_Wz){return new T3(0,0,new T(function(){var _WA=E(E(_Wz).b);return new T4(0,true,_WA.b,_WA.c,_WA.d);}),_2L);},_WB=function(_WC){var _WD=new T(function(){return E(E(_WC).b);});return new T3(0,_WD,_WD,_2L);},_WE=function(_WF){var _WG=new T(function(){return E(E(_WF).b);});return new T3(0,_WG,_WG,_2L);},_WH=function(_WI){var _WJ=new T(function(){return E(E(_WI).b);});return new T3(0,new T(function(){return E(E(_WJ).b);}),_WJ,_2L);},_WK=function(_WL){return new T3(0,0,new T(function(){return E(E(_WL).b);}),_2L);},_WM=function(_WN){var _WO=new T(function(){return E(E(_WN).b);});return new T3(0,new T(function(){return E(E(_WO).c);}),_WO,_2L);},_WP=function(_WQ){var _WR=new T(function(){return E(E(_WQ).b);});return new T3(0,new T(function(){return E(E(_WR).b);}),_WR,_2L);},_WS=function(_WT){var _WU=new T(function(){return E(E(_WT).b);});return new T3(0,new T(function(){return E(E(_WU).b);}),_WU,_2L);},_WV=function(_WW){var _WX=new T(function(){return E(E(_WW).b);});return new T3(0,new T(function(){return E(E(_WX).b);}),_WX,_2L);},_WY=function(_WZ){var _X0=new T(function(){return E(E(_WZ).b);});return new T3(0,new T(function(){return E(E(_X0).b);}),_X0,_2L);},_X1=function(_X2){var _X3=new T(function(){return E(E(_X2).b);});return new T3(0,new T(function(){return E(E(_X3).b);}),_X3,_2L);},_X4=function(_X5){var _X6=new T(function(){return E(E(_X5).b);});return new T3(0,new T(function(){return E(E(_X6).b);}),_X6,_2L);},_X7=function(_X8){var _X9=new T(function(){return E(E(_X8).b);});return new T3(0,new T(function(){return E(E(_X9).b);}),_X9,_2L);},_Xa=function(_Xb){var _Xc=new T(function(){return E(E(_Xb).b);});return new T3(0,new T(function(){return E(E(_Xc).b);}),_Xc,_2L);},_Xd=function(_Xe){var _Xf=new T(function(){return E(E(_Xe).b);});return new T3(0,new T(function(){return E(E(_Xf).b);}),_Xf,_2L);},_Xg=function(_Xh){var _Xi=new T(function(){return E(E(_Xh).b);});return new T3(0,new T(function(){return E(E(_Xi).b);}),_Xi,_2L);},_Xj=function(_Xk){var _Xl=new T(function(){return E(E(_Xk).b);});return new T3(0,_Xl,_Xl,_2L);},_Xm=function(_Xn){var _Xo=new T(function(){return E(E(_Xn).b);});return new T3(0,_Xo,_Xo,_2L);},_Xp=function(_Xq){var _Xr=new T(function(){return E(E(_Xq).b);});return new T3(0,_Xr,_Xr,_2L);},_Xs=function(_Xt){var _Xu=new T(function(){return E(E(_Xt).b);});return new T3(0,_Xu,_Xu,_2L);},_Xv=function(_Xw){return E(_Xw);},_Xx=function(_Xy){return 4;},_Xz={_:0,a:_Xx,b:_Xx,c:function(_XA,_XB,_){return readOffAddr("w32",4,E(_XA),E(_XB));},d:function(_XC,_XD,_XE,_){var _=writeOffAddr("w32",4,E(_XC),E(_XD),E(_XE));return 0;},e:function(_XF,_XG,_){return readOffAddr("w32",4,plusAddr(E(_XF),E(_XG)),0);},f:function(_XH,_XI,_XJ,_){var _=writeOffAddr("w32",4,plusAddr(E(_XH),E(_XI)),0,E(_XJ));return 0;},g:function(_XK,_){return readOffAddr("w32",4,E(_XK),0);},h:function(_XL,_XM,_){var _=writeOffAddr("w32",4,E(_XL),0,E(_XM));return 0;}},_XN=function(_XO,_XP,_XQ,_XR,_XS,_XT,_){var _XU=nMV(__Z),_XV=function(_XW,_XX,_){while(1){var _XY=(function(_XZ,_Y0,_){var _Y1=E(_XO),_Y2=B(A3(_Y1.a,_XZ,_Y0,_)),_Y3=E(_Y2),_Y4=_Y3.c,_Y5=E(_Y3.b);if(_Y5.e!=_Y5.f){if(E(_Y3.a)==1){return __Z;}else{var _Y6=B(A3(_Y1.b,_Y5,_Y4,_)),_Y7=E(_Y6);_XW=_Y7.a;_XX=_Y7.b;return __continue;}}else{var _Y8=function(_Y9){var _Ya=E(_Y4),_Yb=_Ya.a,_Yc=_Ya.b,_Yd=_Ya.e,_Ye=_Ya.f;if(!E(_XP)){var _Yf=B(A2(_XT,new T2(0,_Yb,_Ye-_Yd|0),_));return new T1(1,_Yf);}else{var _=writeOffAddr("w8",1,_Yb,_Ye,0),_Yg=B(A2(_XT,new T2(0,_Yb,_Ye-_Yd|0),_));return new T1(1,_Yg);}};if(!E(_XP)){return _Y8(_);}else{var _Yh=E(_Y4);if(!(_Yh.d-_Yh.f|0)){return __Z;}else{return _Y8(_);}}}})(_XW,_XX,_);if(_XY!=__continue){return _XY;}}};return _XV(_XQ,new T(function(){return new T6(0,_XR,new T1(0,_XU),1,E(_XS),0,0);}),_);},_Yi=function(_Yj,_Yk,_Yl,_){switch(0){case 0:var _Ym=function(_){var _Yn=B(A1(_Yj,_)),_Yo=_Yn,_Yp=new T(function(){return B(A1(_Yl,_Yo));}),_Yq=jsCatch(function(_){return C > 19 ? new F(function(){return _Yp();}) : (++C,_Yp());},function(_Yr,_){var _Ys=B(A2(_Yk,_Yo,_));return die(_Yr);}),_Yt=B(A2(_Yk,_Yo,_));return _Yq;};return _Ym();case 1:var _Yu=B(A1(_Yj,_)),_Yv=_Yu,_Yw=jsCatch(new T(function(){return B(A1(_Yl,_Yv));}),function(_Yx,_){var _Yy=B(A2(_Yk,_Yv,_));return die(_Yx);}),_Yz=B(A2(_Yk,_Yv,_));return _Yw;default:var _YA=B(A1(_Yj,_)),_YB=_YA,_YC=jsCatch(new T(function(){return B(A1(_Yl,_YB));}),function(_YD,_){var _YE=B(A2(_Yk,_YB,_));return die(_YD);}),_YF=B(A2(_Yk,_YB,_));return _YC;}},_YG=function(_YH){return E(E(_YH).c);},_YI=function(_YJ){return E(E(_YJ).d);},_YK=function(_YL,_YM,_YN,_){var _YO=function(_YP,_YQ,_){while(1){var _YR=E(_YP);if(!_YR._){return 0;}else{var _YS=B(A(_YI,[_YL,_YM,_YQ,_YR.a,_])),_YT=_YQ+1|0;_YP=_YR.b;_YQ=_YT;continue;}}};return _YO(_YN,0,_);},_YU=function(_YV,_YW,_YX,_){var _YY=function(_YZ){return C > 19 ? new F(function(){return A1(_YX,E(_YZ).a);}) : (++C,A1(_YX,E(_YZ).a));},_Z0=function(_Z1,_){var _Z2=_aF(_YW,0),_Z3=newByteArr(imul(_Z2,4)|0),_Z4=_Z3,_Z5=_YK(_Xz,_Z4,_YW,_),_Z6=nMV(__Z),_Z7=_Z6,_Z8=function(_Z9,_){var _Za=newByteArr(_Z9),_Zb=_XN(_Z1,true,new T6(0,_Z4,new T1(0,_Z7),0,_Z2,0,_Z2),_Za,_Z9,_YY,_),_Zc=E(_Zb);if(!_Zc._){var _Zd=_Z8(imul(_Z9,2)|0,_);return _Zd;}else{return _Zc.a;}},_Ze=_Z8(_Z2+1|0,_);return _Ze;};return _Yi(E(_YV).c,_YG,_Z0,_);},_Zf=function(_Zg){return E(E(_Zg).c);},_Zh=new T2(0,_Iz,_2B),_Zi=new T2(0,function(_Zj,_Zk){return (!E(_Zj))?E(_Zk):true;},false),_Zl=function(_Zm){while(1){var _Zn=E(_Zm);if(!_Zn._){_Zm=new T1(1,I_fromInt(_Zn.a));continue;}else{return I_toString(_Zn.a);}}},_Zo=function(_Zp,_Zq){return _0(fromJSStr(_Zl(_Zp)),_Zq);},_Zr=function(_Zs,_Zt){var _Zu=E(_Zs);if(!_Zu._){var _Zv=_Zu.a,_Zw=E(_Zt);return (_Zw._==0)?_Zv<_Zw.a:I_compareInt(_Zw.a,_Zv)>0;}else{var _Zx=_Zu.a,_Zy=E(_Zt);return (_Zy._==0)?I_compareInt(_Zx,_Zy.a)<0:I_compare(_Zx,_Zy.a)<0;}},_Zz=function(_ZA,_ZB,_ZC){if(_ZA<=6){return _Zo(_ZB,_ZC);}else{if(!_Zr(_ZB,new T1(0,0))){return _Zo(_ZB,_ZC);}else{return new T2(1,40,new T(function(){return _0(fromJSStr(_Zl(_ZB)),new T2(1,41,_ZC));}));}}},_ZD=function(_ZE){return _Zz(0,_ZE,__Z);},_ZF=function(_ZG){return E(E(_ZG).a);},_ZH=function(_ZI){return E(E(_ZI).b);},_ZJ=function(_ZK,_ZL){var _ZM=E(_ZK);return new T2(0,_ZM,new T(function(){var _ZN=_ZJ(_aq(_ZM,_ZL),_ZL);return new T2(1,_ZN.a,_ZN.b);}));},_ZO=new T(function(){var _ZP=_ZJ(new T1(0,0),new T1(0,1));return new T2(1,_ZP.a,_ZP.b);}),_ZQ=new T(function(){return _U6(_nK);}),_ZR=function(_ZS,_ZT,_ZU){return new T2(0,new T(function(){return _2z(_ZT);}),new T(function(){return _2z(_ZU);}));},_ZV=function(_ZW,_ZX,_ZY){return new T2(0,_ZW,new T(function(){return _ZR(_ZW,_ZX,_ZY);}));},_ZZ=function(_100,_101,_102){var _103=new T(function(){return B(A2(_ZH,_101,_100));}),_104=new T(function(){return B(A2(_ZF,_101,_102));}),_105=function(_106){return C > 19 ? new F(function(){return A1(_103,new T(function(){return B(A1(_104,_106));}));}) : (++C,A1(_103,new T(function(){return B(A1(_104,_106));})));};return _105;},_107=function(_108,_109,_10a){var _10b=new T(function(){return _2z(_109);}),_10c=new T(function(){return _2z(_10a);}),_10d=new T(function(){var _10e=new T(function(){return _2x(_109);}),_10f=new T(function(){return _2x(_10a);}),_10g=function(_10h,_10i){var _10j=new T(function(){return B(A2(_10f,new T(function(){return E(E(_10h).b);}),new T(function(){return E(E(_10i).b);})));}),_10k=new T(function(){return B(A2(_10e,new T(function(){return E(E(_10h).a);}),new T(function(){return E(E(_10i).a);})));});return new T2(0,_10k,_10j);};return _ZV(_10g,_109,_10a);});return _ZZ(_10d,_108,function(_10l){var _10m=E(_10l);return (_10m._==0)?new T2(0,_10m.a,_10c):new T2(0,_10b,_10m.a);});},_10n=new T(function(){return _107(_Zh,_ZQ,_ZQ);}),_10o=new T(function(){return _mo(new T(function(){return unCStr("head");}));}),_10p=function(_10q){var _10r=E(_10q);return (_10r._==0)?E(_10o):E(_10r.a);},_10s=function(_10t,_10u,_10v,_10w,_10x,_10y){var _10z=new T(function(){var _10A=function(_10B){var _10C=E(_10B);if(!_10C._){return __Z;}else{var _10D=_10C.a,_10E=new T(function(){var _10F=new T(function(){return B(A3(_ZF,_10w,new T(function(){return B(A2(_bX,_10t,_10D));}),_10x));});if(!B(A3(_ZH,_10w,_Zi,_10F))){return new T1(0,new T(function(){return _IK(_10D);}));}else{return new T1(1,new T(function(){return _IK(_10D);}));}});return new T2(1,_10E,new T(function(){return _10A(_10C.b);}));}},_10G=new T(function(){var _10H=function(_10I){var _10J=E(_10I);if(!_10J._){return __Z;}else{var _10K=new T(function(){var _10L=new T(function(){return B(A1(_10u,new T(function(){return B(_ZD(_10J.a));})));});return B(A2(_10v,_10y,_10L));});return new T2(1,_10K,new T(function(){return _10H(_10J.b);}));}};return _10H(_ZO);});return _10A(new T2(1,_10y,_10G));});return _10p(B(A1(_10n,_10z)).a);},_10M=function(_10N,_10O,_10P,_10Q){var _10R=function(_10S,_10T){var _10U=E(_10T);if(!_10U._){return __Z;}else{var _10V=E(_10U.a),_10W=new T(function(){return _10s(_10N,_10O,_10P,_Zh,_10S,_10V.a);});return new T2(1,new T2(0,_10W,_10V),new T(function(){return _10R(new T2(1,_10W,_10S),_10U.b);}));}};return _10R(__Z,_10Q);},_10X=function(_10Y){return E(E(_10Y).c);},_10Z=function(_110,_111,_112,_){if(_111>0){var _113=function(_114,_115,_){while(1){var _116=E(_114);if(!_116){var _117=B(A(_10X,[_110,_112,0,_]));return new T2(1,_117,_115);}else{var _118=B(A(_10X,[_110,_112,_116,_])),_119=new T2(1,_118,_115);_114=_116-1|0;_115=_119;continue;}}};return _113(_111-1|0,__Z,_);}else{return __Z;}},_11a=new T(function(){return err(new T(function(){return unCStr("mallocForeignPtrBytes: size must be >= 0");}));}),_11b=function(_11c,_11d,_){var _11e=function(_11f,_){while(1){var _11g=readOffAddr("i8",1,_11d,_11f);if(!E(_11g)){return _11f;}else{var _11h=_11f+1|0;_11f=_11h;continue;}}},_11i=_11e(0,_),_11j=_11i,_11k=function(_11l,_){var _11m=nMV(__Z),_11n=_11m,_11o=E(_11j),_11p=function(_11q){var _11r=imul(_11q,4)|0;if(_11r>=0){var _11s=nMV(__Z),_11t=_11s,_11u=newByteArr(_11r),_11v=_11u,_11w=function(_11x,_){var _11y=E(_11l),_11z=B(A3(_11y.a,_11x,new T6(0,_11v,new T2(1,_11v,_11t),1,_11q,0,0),_)),_11A=E(_11z),_11B=_11A.c,_11C=E(_11A.b);if(_11C.e!=_11C.f){if(E(_11A.a)==1){var _11D=E(_11B),_11E=_11D.b,_11F=_10Z(_Xz,_11D.f-_11D.e|0,_11D.a,_),_11G=_11w(_11C,0);return new T(function(){return _0(_11F,_11G);});}else{var _11H=B(A3(_11y.b,_11C,_11B,_)),_11I=E(_11H),_11J=E(_11I.b),_11K=_11J.b,_11L=_10Z(_Xz,_11J.f-_11J.e|0,_11J.a,_),_11M=_11w(_11I.a,0);return new T(function(){return _0(_11L,_11M);});}}else{var _11N=E(_11B),_11O=_11N.b,_11P=_10Z(_Xz,_11N.f-_11N.e|0,_11N.a,_);return _11P;}};return _11w(new T6(0,_11d,new T1(0,_11n),0,_11o,0,_11o),_);}else{return E(_11a);}};if(_11o>1){return _11p(_11o);}else{return _11p(1);}};return _Yi(E(_11c).b,_YG,_11k,_);},_11Q=new T(function(){return unCStr("UTF16LE");}),_11R=new T(function(){return unCStr("UTF16BE");}),_11S=new T(function(){return unCStr("UTF16");}),_11T=new T(function(){return unCStr("UTF8");}),_11U=new T(function(){return unCStr("UTF32LE");}),_11V=new T(function(){return unCStr("UTF32BE");}),_11W=new T(function(){return unCStr("UTF32");}),_11X=function(_11Y){while(1){var _11Z=(function(_120){var _121=E(_120);if(!_121._){return __Z;}else{var _122=_121.b,_123=E(_121.a);if(_123==45){_11Y=_122;return __continue;}else{return new T2(1,new T(function(){var _124=u_towupper(_123);if(_124>>>0>1114111){return _cp(_124);}else{return _124;}}),new T(function(){return _11X(_122);}));}}})(_11Y);if(_11Z!=__continue){return _11Z;}}},_125=new T(function(){return unCStr("UTF-32LE");}),_126=function(_127){return (E(_127)==47)?false:true;},_128=new T(function(){return unCStr("iconvRecoder");}),_129=function(_12a,_){var _12b=function(_12c,_){while(1){var _12d=readOffAddr("i8",1,_12a,_12c);if(!E(_12d)){return _12c;}else{var _12e=_12c+1|0;_12c=_12e;continue;}}},_12f=_12b(0,_),_12g=E(_12f);if(_12g>0){var _12h=function(_12i,_12j,_){while(1){var _12k=readOffAddr("i8",1,_12a,_12j);if(_12j>0){var _12l=new T2(1,_12k>>>0&255&4294967295,_12i),_12m=_12j-1|0;_12i=_12l;_12j=_12m;continue;}else{return new T2(1,_12k>>>0&255&4294967295,_12i);}}};return _12h(__Z,_12g-1|0,_);}else{return __Z;}},_12n=function(_12o){var _12p=B(A1(_12o,_));return E(_12p);},_12q=new T(function(){return _12n(function(_){var _12r=localeEncoding();return _129(_12r,0);});}),_12s=new T(function(){return _12n(function(_){return _12t(1,_12q,0);});}),_12u=function(_){var _12v=nMV(_12s),_12w=_12v;return new T2(0,function(_){return rMV(_12w);},function(_12x,_){var _=wMV(_12w,_12x);return 0;});},_12y=new T(function(){return _12n(_12u);}),_12z=new T(function(){return E(E(_12y).a);}),_12A=function(_12B,_12C,_12D,_12E){var _12F=function(_){var _12G=E(_12C),_12H=strerror(_12G),_12I=B(A1(_12z,0)),_12J=_11b(_12I,_12H,0);return new T6(0,_12D,new T(function(){switch(_12G){case 1:return 6;break;case 2:return 1;break;case 3:return 1;break;case 4:return 18;break;case 5:return 14;break;case 6:return 1;break;case 7:return 3;break;case 8:return 12;break;case 9:return 12;break;case 10:return 1;break;case 11:return 3;break;case 12:return 3;break;case 13:return 6;break;case 15:return 12;break;case 16:return 2;break;case 17:return 0;break;case 18:return 15;break;case 19:return 15;break;case 20:return 13;break;case 21:return 13;break;case 22:return 12;break;case 23:return 3;break;case 24:return 3;break;case 25:return 5;break;case 26:return 2;break;case 27:return 6;break;case 28:return 3;break;case 29:return 15;break;case 30:return 6;break;case 31:return 3;break;case 32:return 17;break;case 33:return 12;break;case 34:return 15;break;case 35:return 2;break;case 36:return 12;break;case 37:return 3;break;case 38:return 15;break;case 39:return 8;break;case 40:return 12;break;case 42:return 1;break;case 43:return 17;break;case 60:return 12;break;case 61:return 1;break;case 62:return 16;break;case 63:return 3;break;case 64:return 1;break;case 66:return 5;break;case 67:return 17;break;case 69:return 8;break;case 70:return 17;break;case 71:return 10;break;case 72:return 15;break;case 74:return 13;break;case 78:return 17;break;case 84:return 12;break;case 87:return 3;break;case 88:return 12;break;case 89:return 12;break;case 90:return 3;break;case 91:return 10;break;case 92:return 15;break;case 93:return 10;break;case 94:return 15;break;case 95:return 15;break;case 96:return 15;break;case 97:return 15;break;case 98:return 2;break;case 99:return 15;break;case 100:return 17;break;case 101:return 1;break;case 102:return 17;break;case 104:return 17;break;case 105:return 3;break;case 106:return 0;break;case 107:return 12;break;case 108:return 5;break;case 109:return 3;break;case 110:return 16;break;case 111:return 1;break;case 112:return 1;break;case 113:return 1;break;case 114:return 0;break;case 115:return 0;break;case 116:return 17;break;case 122:return 6;break;default:return 11;}}),_12B,_12J,new T1(1,_12G),_12E);};return _12n(_12F);},_12K=function(_12L,_){var _12M=__hscore_get_errno(),_12N=new T(function(){return _1K(new T(function(){return _12A(_12L,_12M,__Z,__Z);}));});return die(_12N);},_12O=function(_12P,_12Q,_12R,_12S,_12T,_12U,_12V,_12W,_12X,_12Y,_12Z,_130,_131,_132,_133,_){var _134=newByteArr(4),_135=_134,_136=E(_12W),_137=function(_138){var _139=plusAddr(_12Q,_138),_=die("Unsupported PrimOp: writeAddrOffAddr#"),_13a=newByteArr(4),_13b=_13a,_13c=E(_133),_13d=function(_13e){var _13f=plusAddr(_12X,_13e),_=die("Unsupported PrimOp: writeAddrOffAddr#"),_13g=newByteArr(4),_13h=_13g,_13i=function(_13j){var _=writeOffAddr("w32",4,_13h,0,_13j),_13k=newByteArr(4),_13l=_13k,_13m=function(_13n){var _=writeOffAddr("w32",4,_13l,0,_13n),_13o=hs_iconv(E(_12P),_135,_13h,_13b,_13l),_13p=readOffAddr("w32",4,_13h,0),_13q=readOffAddr("w32",4,_13l,0),_13r=new T(function(){if(_13c<32){return (_13q&4294967295)>>_13c;}else{if((_13q&4294967295)>=0){return 0;}else{return  -1;}}}),_13s=new T(function(){var _13t=E(_13p);if(!_13t){return new T6(0,_12Q,_12R,_12S,_12T,0,0);}else{if(_136<32){return new T6(0,_12Q,_12R,_12S,_12T,_12V-((_13t&4294967295)>>_136)|0,_12V);}else{if((_13t&4294967295)>=0){return new T6(0,_12Q,_12R,_12S,_12T,_12V,_12V);}else{return new T6(0,_12Q,_12R,_12S,_12T,_12V+1|0,_12V);}}}});if(E(_13o)==4294967295){var _13u=__hscore_get_errno();switch(E(_13u)){case  -1:var _13v=_12K(_128,_);return _13v;case 7:return new T3(0,1,_13s,new T(function(){return new T6(0,_12X,_12Y,_12Z,_130,_131,_130-E(_13r)|0);}));case 22:return new T3(0,0,_13s,new T(function(){return new T6(0,_12X,_12Y,_12Z,_130,_131,_130-E(_13r)|0);}));case 84:return new T3(0,new T(function(){if(!E(_13r)){return 1;}else{return 2;}}),_13s,new T(function(){return new T6(0,_12X,_12Y,_12Z,_130,_131,_130-E(_13r)|0);}));default:var _13w=_12K(_128,_);return _13w;}}else{return new T3(0,0,_13s,new T(function(){return new T6(0,_12X,_12Y,_12Z,_130,_131,_130-E(_13r)|0);}));}};if(_13c<32){return _13m((_130-_132|0)<<_13c>>>0);}else{return _13m(0);}};if(_136<32){return _13i((_12V-_12U|0)<<_136>>>0);}else{return _13i(0);}};if(_13c<32){return _13d(_132<<_13c);}else{return _13d(0);}};if(_136<32){return C > 19 ? new F(function(){return _137(_12U<<_136);}) : (++C,_137(_12U<<_136));}else{return C > 19 ? new F(function(){return _137(0);}) : (++C,_137(0));}},_13x=function(_13y,_13z,_13A,_){var _13B=E(_13z),_13C=E(_13A);return C > 19 ? new F(function(){return _12O(_13y,_13B.a,_13B.b,_13B.c,_13B.d,_13B.e,_13B.f,2,_13C.a,_13C.b,_13C.c,_13C.d,_13C.e,_13C.f,0,_);}) : (++C,_12O(_13y,_13B.a,_13B.b,_13B.c,_13B.d,_13B.e,_13B.f,2,_13C.a,_13C.b,_13C.c,_13C.d,_13C.e,_13C.f,0,_));},_13D=function(_13E,_13F,_13G,_){var _13H=E(_13F),_13I=E(_13G);return C > 19 ? new F(function(){return _12O(_13E,_13H.a,_13H.b,_13H.c,_13H.d,_13H.e,_13H.f,0,_13I.a,_13I.b,_13I.c,_13I.d,_13I.e,_13I.f,2,_);}) : (++C,_12O(_13E,_13H.a,_13H.b,_13H.c,_13H.d,_13H.e,_13H.f,0,_13I.a,_13I.b,_13I.c,_13I.d,_13I.e,_13I.f,2,_));},_13J=function(_){return 0;},_13K=function(_13L,_){return _13J(_);},_13M=new T(function(){return unCStr("mkTextEncoding");}),_13N=new T(function(){return unCStr("Iconv.close");}),_13O=function(_13P,_13Q,_){var _13R=newByteArr(_aF(_13P,0)+1|0),_13S=_13R,_13T=function(_13U,_13V,_){while(1){var _13W=E(_13U);if(!_13W._){var _=writeOffAddr("i8",1,_13S,_13V,0);return 0;}else{var _=writeOffAddr("i8",1,_13S,_13V,E(_13W.a)&255),_13X=_13V+1|0;_13U=_13W.b;_13V=_13X;continue;}}},_13Y=_13T(_13P,0,_),_13Z=B(A2(_13Q,_13S,_));return _13Z;},_140=function(_141,_142,_143,_144,_){var _145=function(_146,_){var _147=function(_148,_){var _149=hs_iconv_open(E(_148),E(_146)),_14a=E(_149);if(_14a==( -1)){var _14b=_12K(_13M,_),_14c=_14b;return new T5(0,new T(function(){return B(A1(_144,_14c));}),_143,function(_){var _14d=hs_iconv_close(E(_14c));if(E(_14d)==( -1)){var _14e=_12K(_13N,_);return 0;}else{return 0;}},_13J,_13K);}else{return new T5(0,new T(function(){return B(A1(_144,_14a));}),_143,function(_){var _14f=hs_iconv_close(_14a);if(E(_14f)==( -1)){var _14g=_12K(_13N,_);return 0;}else{return 0;}},_13J,_13K);}};return _13O(_142,_147,_);};return _13O(_141,_145,_);},_14h=new T(function(){return _1K(new T6(0,__Z,12,new T(function(){return unCStr("recoverDecode");}),new T(function(){return unCStr("invalid byte sequence");}),__Z,__Z));}),_14i=function(_14j,_14k,_14l,_14m,_14n,_14o,_14p,_14q,_14r,_14s,_14t,_14u,_14v,_){switch(E(_14j)){case 0:return die(_14h);case 1:return new T2(0,new T6(0,_14k,_14l,_14m,_14n,_14o+1|0,_14p),new T6(0,_14q,_14r,_14s,_14t,_14u,_14v));case 2:var _=writeOffAddr("w32",4,_14q,_14v,65533);return new T2(0,new T6(0,_14k,_14l,_14m,_14n,_14o+1|0,_14p),new T6(0,_14q,_14r,_14s,_14t,_14u,_14v+1|0));default:var _14w=readOffAddr("w8",1,plusAddr(_14k,_14o),0);if(_14w>=128){var _14x=56320+(_14w&4294967295)|0;if(_14x>>>0>1114111){return _cp(_14x);}else{var _=writeOffAddr("w32",4,_14q,_14v,_14x);return new T2(0,new T6(0,_14k,_14l,_14m,_14n,_14o+1|0,_14p),new T6(0,_14q,_14r,_14s,_14t,_14u,_14v+1|0));}}else{var _14y=_14w&4294967295;if(_14y>>>0>1114111){return _cp(_14y);}else{var _=writeOffAddr("w32",4,_14q,_14v,_14y);return new T2(0,new T6(0,_14k,_14l,_14m,_14n,_14o+1|0,_14p),new T6(0,_14q,_14r,_14s,_14t,_14u,_14v+1|0));}}}},_14z=function(_14A,_14B,_14C,_){var _14D=E(_14B),_14E=E(_14C);return _14i(_14A,_14D.a,_14D.b,_14D.c,_14D.d,_14D.e,_14D.f,_14E.a,_14E.b,_14E.c,_14E.d,_14E.e,_14E.f,_);},_14F=new T(function(){return _1K(new T6(0,__Z,12,new T(function(){return unCStr("recoverEncode");}),new T(function(){return unCStr("invalid character");}),__Z,__Z));}),_14G=function(_){return die(_14F);},_14H=function(_14I,_14J,_14K,_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_){var _14V=readOffAddr("w32",4,_14J,_14N);switch(E(_14I)){case 0:return _14G(0);case 1:return new T2(0,new T6(0,_14J,_14K,_14L,_14M,_14N+1|0,_14O),new T6(0,_14P,_14Q,_14R,_14S,_14T,_14U));case 2:if(E(_14V)==63){return new T2(0,new T6(0,_14J,_14K,_14L,_14M,_14N+1|0,_14O),new T6(0,_14P,_14Q,_14R,_14S,_14T,_14U));}else{var _=writeOffAddr("w32",4,_14J,_14N,63);return new T2(0,new T6(0,_14J,_14K,_14L,_14M,_14N,_14O),new T6(0,_14P,_14Q,_14R,_14S,_14T,_14U));}break;default:if(56448>_14V){return _14G(0);}else{if(_14V>=56576){return _14G(0);}else{var _=writeOffAddr("w8",1,plusAddr(_14P,_14U),0,_14V>>>0&255);return new T2(0,new T6(0,_14J,_14K,_14L,_14M,_14N+1|0,_14O),new T6(0,_14P,_14Q,_14R,_14S,_14T,_14U+1|0));}}}},_14W=function(_14X,_14Y,_14Z,_){var _150=E(_14Y),_151=E(_14Z);return _14H(_14X,_150.a,_150.b,_150.c,_150.d,_150.e,_150.f,_151.a,_151.b,_151.c,_151.d,_151.e,_151.f,_);},_152=function(_153,_154,_){var _155=function(_156,_157,_){return C > 19 ? new F(function(){return _14W(_153,_156,_157,_);}) : (++C,_14W(_153,_156,_157,_));},_158=new T(function(){var _159=_7d(_126,_154);return new T2(0,_159.a,_159.b);}),_15a=function(_156,_157,_){return C > 19 ? new F(function(){return _14z(_153,_156,_157,_);}) : (++C,_14z(_153,_156,_157,_));},_15b=new T(function(){return _0(_125,new T(function(){return E(E(_158).b);},1));}),_15c=new T(function(){return E(E(_158).a);});return new T3(0,_154,function(_){return _140(_15c,_15b,_15a,_13D,_);},function(_){return _140(_125,_154,_155,_13x,_);});},_15d=function(_15e,_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p,_){var _15q=new T6(0,_15e,_15f,_15g,_15h,0,0),_15r=function(_15s,_15t,_){while(1){var _15u=(function(_15v,_15w,_){if(_15v<_15j){if((_15n-_15w|0)>=2){var _15x=readOffAddr("w32",4,_15e,_15v),_15y=_15x;if(_15y>=65536){if((_15n-_15w|0)>=4){var _15z=_15y-65536|0,_=writeOffAddr("w8",1,plusAddr(_15k,_15w),0,((_15z>>18)+216|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_15k,_15w+1|0),0,_15z>>10>>>0&255),_15A=_15z&1023,_=writeOffAddr("w8",1,plusAddr(_15k,_15w+2|0),0,((_15A>>8)+220|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_15k,_15w+3|0),0,_15A>>>0&255),_15B=_15v+1|0,_15C=_15w+4|0;_15s=_15B;_15t=_15C;_=0;return __continue;}else{return new T3(0,1,new T(function(){if(_15v!=_15j){return new T6(0,_15e,_15f,_15g,_15h,_15v,_15j);}else{return E(_15q);}}),new T6(0,_15k,_15l,_15m,_15n,_15o,_15w));}}else{var _15D=function(_15E){if(56320>_15y){var _=writeOffAddr("w8",1,plusAddr(_15k,_15w),0,_15y>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_15k,_15w+1|0),0,_15y>>>0&255);return _15r(_15v+1|0,_15w+2|0,0);}else{if(_15y>57343){var _=writeOffAddr("w8",1,plusAddr(_15k,_15w),0,_15y>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_15k,_15w+1|0),0,_15y>>>0&255);return _15r(_15v+1|0,_15w+2|0,0);}else{return new T3(0,2,new T(function(){if(_15v!=_15j){return new T6(0,_15e,_15f,_15g,_15h,_15v,_15j);}else{return E(_15q);}}),new T6(0,_15k,_15l,_15m,_15n,_15o,_15w));}}};if(55296>_15y){return _15D(0);}else{if(_15y>56319){return _15D(0);}else{return new T3(0,2,new T(function(){if(_15v!=_15j){return new T6(0,_15e,_15f,_15g,_15h,_15v,_15j);}else{return E(_15q);}}),new T6(0,_15k,_15l,_15m,_15n,_15o,_15w));}}}}else{return new T3(0,1,new T(function(){if(_15v!=_15j){return new T6(0,_15e,_15f,_15g,_15h,_15v,_15j);}else{return E(_15q);}}),new T6(0,_15k,_15l,_15m,_15n,_15o,_15w));}}else{return new T3(0,0,new T(function(){if(_15v!=_15j){return new T6(0,_15e,_15f,_15g,_15h,_15v,_15j);}else{return E(_15q);}}),new T6(0,_15k,_15l,_15m,_15n,_15o,_15w));}})(_15s,_15t,_);if(_15u!=__continue){return _15u;}}};return _15r(_15i,_15p,_);},_15F=function(_15G,_15H,_15I,_15J,_15K,_15L,_15M,_15N,_){var _15O=rMV(_15G);if(!E(_15O)){if((_15L-_15N|0)>=2){var _=wMV(_15G,true),_=writeOffAddr("w8",1,plusAddr(_15I,_15N),0,254),_=writeOffAddr("w8",1,plusAddr(_15I,_15N+1|0),0,255),_15P=E(_15H);return _15d(_15P.a,_15P.b,_15P.c,_15P.d,_15P.e,_15P.f,_15I,_15J,_15K,_15L,_15M,_15N+2|0,0);}else{return new T3(0,1,_15H,new T6(0,_15I,_15J,_15K,_15L,_15M,_15N));}}else{var _15Q=E(_15H);return _15d(_15Q.a,_15Q.b,_15Q.c,_15Q.d,_15Q.e,_15Q.f,_15I,_15J,_15K,_15L,_15M,_15N,_);}},_15R=function(_15S,_15T,_15U,_15V,_15W,_15X,_15Y,_15Z,_160,_161,_162,_163,_){var _164=new T6(0,_15S,_15T,_15U,_15V,0,0),_165=function(_166,_167,_){while(1){var _168=(function(_169,_16a,_){if(_16a<_161){if(_169<_15X){if((_169+1|0)!=_15X){var _16b=readOffAddr("w8",1,plusAddr(_15S,_169),0),_16c=readOffAddr("w8",1,plusAddr(_15S,_169+1|0),0),_16d=(_16b<<8>>>0&65535)+_16c>>>0&65535;if(_16d>=55296){if(_16d<=57343){if((_15X-_169|0)>=4){var _16e=readOffAddr("w8",1,plusAddr(_15S,_169+2|0),0),_16f=readOffAddr("w8",1,plusAddr(_15S,_169+3|0),0);if(_16d<55296){return new T3(0,2,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}else{if(_16d>56319){return new T3(0,2,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}else{var _16g=(_16e<<8>>>0&65535)+_16f>>>0&65535;if(_16g<56320){return new T3(0,2,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}else{if(_16g>57343){return new T3(0,2,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}else{var _=writeOffAddr("w32",4,_15Y,_16a,((((_16d&4294967295)-55296|0)<<10)+((_16g&4294967295)-56320|0)|0)+65536|0),_16h=_169+4|0,_16i=_16a+1|0;_166=_16h;_167=_16i;_=0;return __continue;}}}}}else{return new T3(0,0,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}}else{var _=writeOffAddr("w32",4,_15Y,_16a,_16d&4294967295),_16h=_169+2|0,_16i=_16a+1|0;_166=_16h;_167=_16i;_=0;return __continue;}}else{var _=writeOffAddr("w32",4,_15Y,_16a,_16d&4294967295),_16h=_169+2|0,_16i=_16a+1|0;_166=_16h;_167=_16i;_=0;return __continue;}}else{return new T3(0,0,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}}else{return new T3(0,0,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}}else{return new T3(0,1,new T(function(){if(_169!=_15X){return new T6(0,_15S,_15T,_15U,_15V,_169,_15X);}else{return E(_164);}}),new T6(0,_15Y,_15Z,_160,_161,_162,_16a));}})(_166,_167,_);if(_168!=__continue){return _168;}}};return _165(_15W,_163,_);},_16j=function(_16k,_16l,_16m,_16n,_16o,_16p,_16q,_16r,_16s,_16t,_16u,_16v,_){var _16w=new T6(0,_16k,_16l,_16m,_16n,0,0),_16x=function(_16y,_16z,_){while(1){var _16A=(function(_16B,_16C,_){if(_16C<_16t){if(_16B<_16p){if((_16B+1|0)!=_16p){var _16D=readOffAddr("w8",1,plusAddr(_16k,_16B),0),_16E=readOffAddr("w8",1,plusAddr(_16k,_16B+1|0),0),_16F=(_16E<<8>>>0&65535)+_16D>>>0&65535;if(_16F>=55296){if(_16F<=57343){if((_16p-_16B|0)>=4){var _16G=readOffAddr("w8",1,plusAddr(_16k,_16B+2|0),0),_16H=readOffAddr("w8",1,plusAddr(_16k,_16B+3|0),0);if(_16F<55296){return new T3(0,2,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}else{if(_16F>56319){return new T3(0,2,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}else{var _16I=(_16H<<8>>>0&65535)+_16G>>>0&65535;if(_16I<56320){return new T3(0,2,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}else{if(_16I>57343){return new T3(0,2,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}else{var _=writeOffAddr("w32",4,_16q,_16C,((((_16F&4294967295)-55296|0)<<10)+((_16I&4294967295)-56320|0)|0)+65536|0),_16J=_16B+4|0,_16K=_16C+1|0;_16y=_16J;_16z=_16K;_=0;return __continue;}}}}}else{return new T3(0,0,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}}else{var _=writeOffAddr("w32",4,_16q,_16C,_16F&4294967295),_16J=_16B+2|0,_16K=_16C+1|0;_16y=_16J;_16z=_16K;_=0;return __continue;}}else{var _=writeOffAddr("w32",4,_16q,_16C,_16F&4294967295),_16J=_16B+2|0,_16K=_16C+1|0;_16y=_16J;_16z=_16K;_=0;return __continue;}}else{return new T3(0,0,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}}else{return new T3(0,0,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}}else{return new T3(0,1,new T(function(){if(_16B!=_16p){return new T6(0,_16k,_16l,_16m,_16n,_16B,_16p);}else{return E(_16w);}}),new T6(0,_16q,_16r,_16s,_16t,_16u,_16C));}})(_16y,_16z,_);if(_16A!=__continue){return _16A;}}};return _16x(_16o,_16v,_);},_16L=function(_16M,_16N,_){var _16O=E(_16M),_16P=E(_16N);return _15R(_16O.a,_16O.b,_16O.c,_16O.d,_16O.e,_16O.f,_16P.a,_16P.b,_16P.c,_16P.d,_16P.e,_16P.f,_);},_16Q=new T1(1,_16L),_16R=function(_16S,_16T,_){var _16U=E(_16S),_16V=E(_16T);return _16j(_16U.a,_16U.b,_16U.c,_16U.d,_16U.e,_16U.f,_16V.a,_16V.b,_16V.c,_16V.d,_16V.e,_16V.f,_);},_16W=function(_16X,_16Y,_16Z,_170,_171,_172,_173,_174,_){var _175=rMV(_16X),_176=E(_175);if(!_176._){if((_173-_172|0)>=2){var _177=readOffAddr("w8",1,plusAddr(_16Y,_172),0),_178=_177,_179=readOffAddr("w8",1,plusAddr(_16Y,_172+1|0),0),_17a=_179,_17b=function(_17c){if(E(_178)==255){if(E(_17a)==254){var _=wMV(_16X,new T1(1,_16R)),_17d=E(_174);return _16j(_16Y,_16Z,_170,_171,_172+2|0,_173,_17d.a,_17d.b,_17d.c,_17d.d,_17d.e,_17d.f,0);}else{var _=wMV(_16X,_16Q),_17e=E(_174);return _15R(_16Y,_16Z,_170,_171,_172,_173,_17e.a,_17e.b,_17e.c,_17e.d,_17e.e,_17e.f,0);}}else{var _=wMV(_16X,_16Q),_17f=E(_174);return _15R(_16Y,_16Z,_170,_171,_172,_173,_17f.a,_17f.b,_17f.c,_17f.d,_17f.e,_17f.f,0);}};if(E(_178)==254){if(E(_17a)==255){var _=wMV(_16X,_16Q),_17g=E(_174);return _15R(_16Y,_16Z,_170,_171,_172+2|0,_173,_17g.a,_17g.b,_17g.c,_17g.d,_17g.e,_17g.f,0);}else{return _17b(0);}}else{return _17b(0);}}else{return new T3(0,0,new T6(0,_16Y,_16Z,_170,_171,_172,_173),_174);}}else{return C > 19 ? new F(function(){return A3(_176.a,new T6(0,_16Y,_16Z,_170,_171,_172,_173),_174,_);}) : (++C,A3(_176.a,new T6(0,_16Y,_16Z,_170,_171,_172,_173),_174,_));}},_17h=function(_){return 0;},_17i=new T(function(){return unCStr("UTF-16");}),_17j=function(_17k){var _17l=function(_){var _17m=nMV(false),_17n=_17m;return new T5(0,function(_17o,_17p,_){var _17q=E(_17p);return _15F(_17n,_17o,_17q.a,_17q.b,_17q.c,_17q.d,_17q.e,_17q.f,_);},function(_17r,_17s,_){return C > 19 ? new F(function(){return _14W(_17k,_17r,_17s,_);}) : (++C,_14W(_17k,_17r,_17s,_));},_17h,function(_){return rMV(_17n);},function(_17t,_){var _=wMV(_17n,_17t);return 0;});},_17u=function(_){var _17v=nMV(__Z),_17w=_17v;return new T5(0,function(_17x,_17y,_){var _17z=E(_17x);return C > 19 ? new F(function(){return _16W(_17w,_17z.a,_17z.b,_17z.c,_17z.d,_17z.e,_17z.f,_17y,_);}) : (++C,_16W(_17w,_17z.a,_17z.b,_17z.c,_17z.d,_17z.e,_17z.f,_17y,_));},function(_17r,_17s,_){return C > 19 ? new F(function(){return _14z(_17k,_17r,_17s,_);}) : (++C,_14z(_17k,_17r,_17s,_));},_17h,function(_){return rMV(_17w);},function(_17A,_){var _=wMV(_17w,_17A);return 0;});};return new T3(0,_17i,_17u,_17l);},_17B=function(_17C,_17D,_){var _17E=E(_17C),_17F=E(_17D);return _15d(_17E.a,_17E.b,_17E.c,_17E.d,_17E.e,_17E.f,_17F.a,_17F.b,_17F.c,_17F.d,_17F.e,_17F.f,_);},_17G=function(_17H,_){return _17h(_);},_17I=new T(function(){return unCStr("UTF-16BE");}),_17J=function(_17K){var _17L=function(_){return new T5(0,_17B,function(_17r,_17s,_){return C > 19 ? new F(function(){return _14W(_17K,_17r,_17s,_);}) : (++C,_14W(_17K,_17r,_17s,_));},_17h,_17h,_17G);},_17M=function(_){return new T5(0,_16L,function(_17r,_17s,_){return C > 19 ? new F(function(){return _14z(_17K,_17r,_17s,_);}) : (++C,_14z(_17K,_17r,_17s,_));},_17h,_17h,_17G);};return new T3(0,_17I,_17M,_17L);},_17N=function(_17O,_17P,_17Q,_17R,_17S,_17T,_17U,_17V,_17W,_17X,_17Y,_17Z,_){var _180=new T6(0,_17O,_17P,_17Q,_17R,0,0),_181=function(_182,_183,_){while(1){var _184=(function(_185,_186,_){if(_185<_17T){if((_17X-_186|0)>=2){var _187=readOffAddr("w32",4,_17O,_185),_188=_187;if(_188>=65536){if((_17X-_186|0)>=4){var _189=_188-65536|0,_=writeOffAddr("w8",1,plusAddr(_17U,_186),0,_189>>10>>>0&255),_=writeOffAddr("w8",1,plusAddr(_17U,_186+1|0),0,((_189>>18)+216|0)>>>0&255),_18a=_189&1023,_=writeOffAddr("w8",1,plusAddr(_17U,_186+2|0),0,_18a>>>0&255),_=writeOffAddr("w8",1,plusAddr(_17U,_186+3|0),0,((_18a>>8)+220|0)>>>0&255),_18b=_185+1|0,_18c=_186+4|0;_182=_18b;_183=_18c;_=0;return __continue;}else{return new T3(0,1,new T(function(){if(_185!=_17T){return new T6(0,_17O,_17P,_17Q,_17R,_185,_17T);}else{return E(_180);}}),new T6(0,_17U,_17V,_17W,_17X,_17Y,_186));}}else{var _18d=function(_18e){if(56320>_188){var _=writeOffAddr("w8",1,plusAddr(_17U,_186),0,_188>>>0&255),_=writeOffAddr("w8",1,plusAddr(_17U,_186+1|0),0,_188>>8>>>0&255);return _181(_185+1|0,_186+2|0,0);}else{if(_188>57343){var _=writeOffAddr("w8",1,plusAddr(_17U,_186),0,_188>>>0&255),_=writeOffAddr("w8",1,plusAddr(_17U,_186+1|0),0,_188>>8>>>0&255);return _181(_185+1|0,_186+2|0,0);}else{return new T3(0,2,new T(function(){if(_185!=_17T){return new T6(0,_17O,_17P,_17Q,_17R,_185,_17T);}else{return E(_180);}}),new T6(0,_17U,_17V,_17W,_17X,_17Y,_186));}}};if(55296>_188){return _18d(0);}else{if(_188>56319){return _18d(0);}else{return new T3(0,2,new T(function(){if(_185!=_17T){return new T6(0,_17O,_17P,_17Q,_17R,_185,_17T);}else{return E(_180);}}),new T6(0,_17U,_17V,_17W,_17X,_17Y,_186));}}}}else{return new T3(0,1,new T(function(){if(_185!=_17T){return new T6(0,_17O,_17P,_17Q,_17R,_185,_17T);}else{return E(_180);}}),new T6(0,_17U,_17V,_17W,_17X,_17Y,_186));}}else{return new T3(0,0,new T(function(){if(_185!=_17T){return new T6(0,_17O,_17P,_17Q,_17R,_185,_17T);}else{return E(_180);}}),new T6(0,_17U,_17V,_17W,_17X,_17Y,_186));}})(_182,_183,_);if(_184!=__continue){return _184;}}};return _181(_17S,_17Z,_);},_18f=function(_18g,_18h,_){var _18i=E(_18g),_18j=E(_18h);return _17N(_18i.a,_18i.b,_18i.c,_18i.d,_18i.e,_18i.f,_18j.a,_18j.b,_18j.c,_18j.d,_18j.e,_18j.f,_);},_18k=new T(function(){return unCStr("UTF16-LE");}),_18l=function(_18m){var _18n=function(_){return new T5(0,_18f,function(_17r,_17s,_){return C > 19 ? new F(function(){return _14W(_18m,_17r,_17s,_);}) : (++C,_14W(_18m,_17r,_17s,_));},_17h,_17h,_17G);},_18o=function(_){return new T5(0,_16R,function(_17r,_17s,_){return C > 19 ? new F(function(){return _14z(_18m,_17r,_17s,_);}) : (++C,_14z(_18m,_17r,_17s,_));},_17h,_17h,_17G);};return new T3(0,_18k,_18o,_18n);},_18p=function(_18q,_18r,_18s,_18t,_18u,_18v,_18w,_18x,_18y,_18z,_18A,_18B,_){var _18C=new T6(0,_18q,_18r,_18s,_18t,0,0),_18D=function(_18E,_18F,_){if(_18E<_18v){if((_18z-_18F|0)>=4){var _18G=readOffAddr("w32",4,_18q,_18E),_18H=_18G,_18I=function(_18J){if(56320>_18H){var _=writeOffAddr("w8",1,plusAddr(_18w,_18F),0,_18H>>24>>>0&255),_=writeOffAddr("w8",1,plusAddr(_18w,_18F+1|0),0,_18H>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_18w,_18F+2|0),0,_18H>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_18w,_18F+3|0),0,_18H>>>0&255);return C > 19 ? new F(function(){return _18D(_18E+1|0,_18F+4|0,0);}) : (++C,_18D(_18E+1|0,_18F+4|0,0));}else{if(_18H>57343){var _=writeOffAddr("w8",1,plusAddr(_18w,_18F),0,_18H>>24>>>0&255),_=writeOffAddr("w8",1,plusAddr(_18w,_18F+1|0),0,_18H>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_18w,_18F+2|0),0,_18H>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_18w,_18F+3|0),0,_18H>>>0&255);return C > 19 ? new F(function(){return _18D(_18E+1|0,_18F+4|0,0);}) : (++C,_18D(_18E+1|0,_18F+4|0,0));}else{return new T3(0,2,new T(function(){if(_18E!=_18v){return new T6(0,_18q,_18r,_18s,_18t,_18E,_18v);}else{return E(_18C);}}),new T6(0,_18w,_18x,_18y,_18z,_18A,_18F));}}};if(55296>_18H){return C > 19 ? new F(function(){return _18I(0);}) : (++C,_18I(0));}else{if(_18H>56319){return C > 19 ? new F(function(){return _18I(0);}) : (++C,_18I(0));}else{return new T3(0,2,new T(function(){if(_18E!=_18v){return new T6(0,_18q,_18r,_18s,_18t,_18E,_18v);}else{return E(_18C);}}),new T6(0,_18w,_18x,_18y,_18z,_18A,_18F));}}}else{return new T3(0,1,new T(function(){if(_18E!=_18v){return new T6(0,_18q,_18r,_18s,_18t,_18E,_18v);}else{return E(_18C);}}),new T6(0,_18w,_18x,_18y,_18z,_18A,_18F));}}else{return new T3(0,0,new T(function(){if(_18E!=_18v){return new T6(0,_18q,_18r,_18s,_18t,_18E,_18v);}else{return E(_18C);}}),new T6(0,_18w,_18x,_18y,_18z,_18A,_18F));}};return C > 19 ? new F(function(){return _18D(_18u,_18B,_);}) : (++C,_18D(_18u,_18B,_));},_18K=function(_18L,_18M,_18N,_18O,_18P,_18Q,_18R,_18S,_){var _18T=rMV(_18L);if(!E(_18T)){if((_18Q-_18S|0)>=4){var _=wMV(_18L,true),_=writeOffAddr("w8",1,plusAddr(_18N,_18S),0,0),_=writeOffAddr("w8",1,plusAddr(_18N,_18S+1|0),0,0),_=writeOffAddr("w8",1,plusAddr(_18N,_18S+2|0),0,254),_=writeOffAddr("w8",1,plusAddr(_18N,_18S+3|0),0,255),_18U=E(_18M);return C > 19 ? new F(function(){return _18p(_18U.a,_18U.b,_18U.c,_18U.d,_18U.e,_18U.f,_18N,_18O,_18P,_18Q,_18R,_18S+4|0,0);}) : (++C,_18p(_18U.a,_18U.b,_18U.c,_18U.d,_18U.e,_18U.f,_18N,_18O,_18P,_18Q,_18R,_18S+4|0,0));}else{return new T3(0,1,_18M,new T6(0,_18N,_18O,_18P,_18Q,_18R,_18S));}}else{var _18V=E(_18M);return C > 19 ? new F(function(){return _18p(_18V.a,_18V.b,_18V.c,_18V.d,_18V.e,_18V.f,_18N,_18O,_18P,_18Q,_18R,_18S,_);}) : (++C,_18p(_18V.a,_18V.b,_18V.c,_18V.d,_18V.e,_18V.f,_18N,_18O,_18P,_18Q,_18R,_18S,_));}},_18W=function(_18X,_18Y,_18Z,_190,_191,_192,_193,_194,_195,_196,_197,_198,_){var _199=new T6(0,_18X,_18Y,_18Z,_190,0,0),_19a=function(_19b,_19c,_){while(1){var _19d=(function(_19e,_19f,_){if(_19f<_196){if((_192-_19e|0)>=4){var _19g=readOffAddr("w8",1,plusAddr(_18X,_19e),0),_19h=readOffAddr("w8",1,plusAddr(_18X,_19e+1|0),0),_19i=readOffAddr("w8",1,plusAddr(_18X,_19e+2|0),0),_19j=readOffAddr("w8",1,plusAddr(_18X,_19e+3|0),0),_19k=((((_19g&4294967295)<<24)+((_19h&4294967295)<<16)|0)+((_19i&4294967295)<<8)|0)+(_19j&4294967295)|0,_19l=function(_19m){if(_19k<=57343){return new T3(0,2,new T(function(){if(_19e!=_192){return new T6(0,_18X,_18Y,_18Z,_190,_19e,_192);}else{return E(_199);}}),new T6(0,_193,_194,_195,_196,_197,_19f));}else{if(_19k>1114111){return new T3(0,2,new T(function(){if(_19e!=_192){return new T6(0,_18X,_18Y,_18Z,_190,_19e,_192);}else{return E(_199);}}),new T6(0,_193,_194,_195,_196,_197,_19f));}else{var _=writeOffAddr("w32",4,_193,_19f,_19k);return _19a(_19e+4|0,_19f+1|0,0);}}};if(_19k<0){return _19l(0);}else{if(_19k>=55296){return _19l(0);}else{var _=writeOffAddr("w32",4,_193,_19f,_19k),_19n=_19e+4|0,_19o=_19f+1|0;_19b=_19n;_19c=_19o;_=0;return __continue;}}}else{return new T3(0,0,new T(function(){if(_19e!=_192){return new T6(0,_18X,_18Y,_18Z,_190,_19e,_192);}else{return E(_199);}}),new T6(0,_193,_194,_195,_196,_197,_19f));}}else{return new T3(0,1,new T(function(){if(_19e!=_192){return new T6(0,_18X,_18Y,_18Z,_190,_19e,_192);}else{return E(_199);}}),new T6(0,_193,_194,_195,_196,_197,_19f));}})(_19b,_19c,_);if(_19d!=__continue){return _19d;}}};return _19a(_191,_198,_);},_19p=function(_19q,_19r,_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B,_){var _19C=new T6(0,_19q,_19r,_19s,_19t,0,0),_19D=function(_19E,_19F,_){while(1){var _19G=(function(_19H,_19I,_){if(_19I<_19z){if((_19v-_19H|0)>=4){var _19J=readOffAddr("w8",1,plusAddr(_19q,_19H),0),_19K=readOffAddr("w8",1,plusAddr(_19q,_19H+1|0),0),_19L=readOffAddr("w8",1,plusAddr(_19q,_19H+2|0),0),_19M=readOffAddr("w8",1,plusAddr(_19q,_19H+3|0),0),_19N=((((_19M&4294967295)<<24)+((_19L&4294967295)<<16)|0)+((_19K&4294967295)<<8)|0)+(_19J&4294967295)|0,_19O=function(_19P){if(_19N<=57343){return new T3(0,2,new T(function(){if(_19H!=_19v){return new T6(0,_19q,_19r,_19s,_19t,_19H,_19v);}else{return E(_19C);}}),new T6(0,_19w,_19x,_19y,_19z,_19A,_19I));}else{if(_19N>1114111){return new T3(0,2,new T(function(){if(_19H!=_19v){return new T6(0,_19q,_19r,_19s,_19t,_19H,_19v);}else{return E(_19C);}}),new T6(0,_19w,_19x,_19y,_19z,_19A,_19I));}else{var _=writeOffAddr("w32",4,_19w,_19I,_19N);return _19D(_19H+4|0,_19I+1|0,0);}}};if(_19N<0){return _19O(0);}else{if(_19N>=55296){return _19O(0);}else{var _=writeOffAddr("w32",4,_19w,_19I,_19N),_19Q=_19H+4|0,_19R=_19I+1|0;_19E=_19Q;_19F=_19R;_=0;return __continue;}}}else{return new T3(0,0,new T(function(){if(_19H!=_19v){return new T6(0,_19q,_19r,_19s,_19t,_19H,_19v);}else{return E(_19C);}}),new T6(0,_19w,_19x,_19y,_19z,_19A,_19I));}}else{return new T3(0,1,new T(function(){if(_19H!=_19v){return new T6(0,_19q,_19r,_19s,_19t,_19H,_19v);}else{return E(_19C);}}),new T6(0,_19w,_19x,_19y,_19z,_19A,_19I));}})(_19E,_19F,_);if(_19G!=__continue){return _19G;}}};return _19D(_19u,_19B,_);},_19S=function(_19T,_19U,_){var _19V=E(_19T),_19W=E(_19U);return _18W(_19V.a,_19V.b,_19V.c,_19V.d,_19V.e,_19V.f,_19W.a,_19W.b,_19W.c,_19W.d,_19W.e,_19W.f,_);},_19X=new T1(1,_19S),_19Y=function(_19Z,_1a0,_){var _1a1=E(_19Z),_1a2=E(_1a0);return _19p(_1a1.a,_1a1.b,_1a1.c,_1a1.d,_1a1.e,_1a1.f,_1a2.a,_1a2.b,_1a2.c,_1a2.d,_1a2.e,_1a2.f,_);},_1a3=function(_1a4,_1a5,_1a6,_1a7,_1a8,_1a9,_1aa,_1ab,_){var _1ac=rMV(_1a4),_1ad=E(_1ac);if(!_1ad._){if((_1aa-_1a9|0)>=4){var _1ae=readOffAddr("w8",1,plusAddr(_1a5,_1a9),0),_1af=_1ae,_1ag=readOffAddr("w8",1,plusAddr(_1a5,_1a9+1|0),0),_1ah=_1ag,_1ai=readOffAddr("w8",1,plusAddr(_1a5,_1a9+2|0),0),_1aj=_1ai,_1ak=readOffAddr("w8",1,plusAddr(_1a5,_1a9+3|0),0),_1al=_1ak,_1am=function(_1an){if(E(_1af)==255){if(E(_1ah)==254){if(!E(_1aj)){if(!E(_1al)){var _=wMV(_1a4,new T1(1,_19Y)),_1ao=E(_1ab);return _19p(_1a5,_1a6,_1a7,_1a8,_1a9+4|0,_1aa,_1ao.a,_1ao.b,_1ao.c,_1ao.d,_1ao.e,_1ao.f,0);}else{var _=wMV(_1a4,_19X),_1ap=E(_1ab);return _18W(_1a5,_1a6,_1a7,_1a8,_1a9,_1aa,_1ap.a,_1ap.b,_1ap.c,_1ap.d,_1ap.e,_1ap.f,0);}}else{var _=wMV(_1a4,_19X),_1aq=E(_1ab);return _18W(_1a5,_1a6,_1a7,_1a8,_1a9,_1aa,_1aq.a,_1aq.b,_1aq.c,_1aq.d,_1aq.e,_1aq.f,0);}}else{var _=wMV(_1a4,_19X),_1ar=E(_1ab);return _18W(_1a5,_1a6,_1a7,_1a8,_1a9,_1aa,_1ar.a,_1ar.b,_1ar.c,_1ar.d,_1ar.e,_1ar.f,0);}}else{var _=wMV(_1a4,_19X),_1as=E(_1ab);return _18W(_1a5,_1a6,_1a7,_1a8,_1a9,_1aa,_1as.a,_1as.b,_1as.c,_1as.d,_1as.e,_1as.f,0);}};if(!E(_1af)){if(!E(_1ah)){if(E(_1aj)==254){if(E(_1al)==255){var _=wMV(_1a4,_19X),_1at=E(_1ab);return _18W(_1a5,_1a6,_1a7,_1a8,_1a9+4|0,_1aa,_1at.a,_1at.b,_1at.c,_1at.d,_1at.e,_1at.f,0);}else{return _1am(0);}}else{return _1am(0);}}else{return _1am(0);}}else{return _1am(0);}}else{return new T3(0,0,new T6(0,_1a5,_1a6,_1a7,_1a8,_1a9,_1aa),_1ab);}}else{return C > 19 ? new F(function(){return A3(_1ad.a,new T6(0,_1a5,_1a6,_1a7,_1a8,_1a9,_1aa),_1ab,_);}) : (++C,A3(_1ad.a,new T6(0,_1a5,_1a6,_1a7,_1a8,_1a9,_1aa),_1ab,_));}},_1au=function(_){return 0;},_1av=new T(function(){return unCStr("UTF-32");}),_1aw=function(_1ax){var _1ay=function(_){var _1az=nMV(false),_1aA=_1az;return new T5(0,function(_1aB,_1aC,_){var _1aD=E(_1aC);return C > 19 ? new F(function(){return _18K(_1aA,_1aB,_1aD.a,_1aD.b,_1aD.c,_1aD.d,_1aD.e,_1aD.f,_);}) : (++C,_18K(_1aA,_1aB,_1aD.a,_1aD.b,_1aD.c,_1aD.d,_1aD.e,_1aD.f,_));},function(_1aE,_1aF,_){return C > 19 ? new F(function(){return _14W(_1ax,_1aE,_1aF,_);}) : (++C,_14W(_1ax,_1aE,_1aF,_));},_1au,function(_){return rMV(_1aA);},function(_1aG,_){var _=wMV(_1aA,_1aG);return 0;});},_1aH=function(_){var _1aI=nMV(__Z),_1aJ=_1aI;return new T5(0,function(_1aK,_1aL,_){var _1aM=E(_1aK);return C > 19 ? new F(function(){return _1a3(_1aJ,_1aM.a,_1aM.b,_1aM.c,_1aM.d,_1aM.e,_1aM.f,_1aL,_);}) : (++C,_1a3(_1aJ,_1aM.a,_1aM.b,_1aM.c,_1aM.d,_1aM.e,_1aM.f,_1aL,_));},function(_1aE,_1aF,_){return C > 19 ? new F(function(){return _14z(_1ax,_1aE,_1aF,_);}) : (++C,_14z(_1ax,_1aE,_1aF,_));},_1au,function(_){return rMV(_1aJ);},function(_1aN,_){var _=wMV(_1aJ,_1aN);return 0;});};return new T3(0,_1av,_1aH,_1ay);},_1aO=function(_1aP,_1aQ,_){var _1aR=E(_1aP),_1aS=E(_1aQ);return C > 19 ? new F(function(){return _18p(_1aR.a,_1aR.b,_1aR.c,_1aR.d,_1aR.e,_1aR.f,_1aS.a,_1aS.b,_1aS.c,_1aS.d,_1aS.e,_1aS.f,_);}) : (++C,_18p(_1aR.a,_1aR.b,_1aR.c,_1aR.d,_1aR.e,_1aR.f,_1aS.a,_1aS.b,_1aS.c,_1aS.d,_1aS.e,_1aS.f,_));},_1aT=function(_1aU,_){return _1au(_);},_1aV=new T(function(){return unCStr("UTF-32BE");}),_1aW=function(_1aX){var _1aY=function(_){return new T5(0,_1aO,function(_1aE,_1aF,_){return C > 19 ? new F(function(){return _14W(_1aX,_1aE,_1aF,_);}) : (++C,_14W(_1aX,_1aE,_1aF,_));},_1au,_1au,_1aT);},_1aZ=function(_){return new T5(0,_19S,function(_1aE,_1aF,_){return C > 19 ? new F(function(){return _14z(_1aX,_1aE,_1aF,_);}) : (++C,_14z(_1aX,_1aE,_1aF,_));},_1au,_1au,_1aT);};return new T3(0,_1aV,_1aZ,_1aY);},_1b0=function(_1b1,_1b2,_1b3,_1b4,_1b5,_1b6,_1b7,_1b8,_1b9,_1ba,_1bb,_1bc,_){var _1bd=new T6(0,_1b1,_1b2,_1b3,_1b4,0,0),_1be=function(_1bf,_1bg,_){if(_1bf<_1b6){if((_1ba-_1bg|0)>=4){var _1bh=readOffAddr("w32",4,_1b1,_1bf),_1bi=_1bh,_1bj=function(_1bk){if(56320>_1bi){var _=writeOffAddr("w8",1,plusAddr(_1b7,_1bg),0,_1bi>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1b7,_1bg+1|0),0,_1bi>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1b7,_1bg+2|0),0,_1bi>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1b7,_1bg+3|0),0,_1bi>>24>>>0&255);return C > 19 ? new F(function(){return _1be(_1bf+1|0,_1bg+4|0,0);}) : (++C,_1be(_1bf+1|0,_1bg+4|0,0));}else{if(_1bi>57343){var _=writeOffAddr("w8",1,plusAddr(_1b7,_1bg),0,_1bi>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1b7,_1bg+1|0),0,_1bi>>8>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1b7,_1bg+2|0),0,_1bi>>16>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1b7,_1bg+3|0),0,_1bi>>24>>>0&255);return C > 19 ? new F(function(){return _1be(_1bf+1|0,_1bg+4|0,0);}) : (++C,_1be(_1bf+1|0,_1bg+4|0,0));}else{return new T3(0,2,new T(function(){if(_1bf!=_1b6){return new T6(0,_1b1,_1b2,_1b3,_1b4,_1bf,_1b6);}else{return E(_1bd);}}),new T6(0,_1b7,_1b8,_1b9,_1ba,_1bb,_1bg));}}};if(55296>_1bi){return C > 19 ? new F(function(){return _1bj(0);}) : (++C,_1bj(0));}else{if(_1bi>56319){return C > 19 ? new F(function(){return _1bj(0);}) : (++C,_1bj(0));}else{return new T3(0,2,new T(function(){if(_1bf!=_1b6){return new T6(0,_1b1,_1b2,_1b3,_1b4,_1bf,_1b6);}else{return E(_1bd);}}),new T6(0,_1b7,_1b8,_1b9,_1ba,_1bb,_1bg));}}}else{return new T3(0,1,new T(function(){if(_1bf!=_1b6){return new T6(0,_1b1,_1b2,_1b3,_1b4,_1bf,_1b6);}else{return E(_1bd);}}),new T6(0,_1b7,_1b8,_1b9,_1ba,_1bb,_1bg));}}else{return new T3(0,0,new T(function(){if(_1bf!=_1b6){return new T6(0,_1b1,_1b2,_1b3,_1b4,_1bf,_1b6);}else{return E(_1bd);}}),new T6(0,_1b7,_1b8,_1b9,_1ba,_1bb,_1bg));}};return C > 19 ? new F(function(){return _1be(_1b5,_1bc,_);}) : (++C,_1be(_1b5,_1bc,_));},_1bl=function(_1bm,_1bn,_){var _1bo=E(_1bm),_1bp=E(_1bn);return C > 19 ? new F(function(){return _1b0(_1bo.a,_1bo.b,_1bo.c,_1bo.d,_1bo.e,_1bo.f,_1bp.a,_1bp.b,_1bp.c,_1bp.d,_1bp.e,_1bp.f,_);}) : (++C,_1b0(_1bo.a,_1bo.b,_1bo.c,_1bo.d,_1bo.e,_1bo.f,_1bp.a,_1bp.b,_1bp.c,_1bp.d,_1bp.e,_1bp.f,_));},_1bq=new T(function(){return unCStr("UTF-32LE");}),_1br=function(_1bs){var _1bt=function(_){return new T5(0,_1bl,function(_1aE,_1aF,_){return C > 19 ? new F(function(){return _14W(_1bs,_1aE,_1aF,_);}) : (++C,_14W(_1bs,_1aE,_1aF,_));},_1au,_1au,_1aT);},_1bu=function(_){return new T5(0,_19Y,function(_1aE,_1aF,_){return C > 19 ? new F(function(){return _14z(_1bs,_1aE,_1aF,_);}) : (++C,_14z(_1bs,_1aE,_1aF,_));},_1au,_1au,_1aT);};return new T3(0,_1bq,_1bu,_1bt);},_1bv=function(_1bw,_1bx,_1by,_1bz,_1bA,_1bB,_1bC,_1bD,_1bE,_1bF,_1bG,_1bH,_){var _1bI=new T6(0,_1bw,_1bx,_1by,_1bz,0,0),_1bJ=function(_1bK,_1bL,_){while(1){var _1bM=(function(_1bN,_1bO,_){if(_1bO<_1bF){if(_1bN<_1bB){var _1bP=readOffAddr("w32",4,_1bw,_1bN),_1bQ=_1bP;if(_1bQ>127){if(_1bQ>2047){if(_1bQ>65535){if((_1bF-_1bO|0)>=4){var _=writeOffAddr("w8",1,plusAddr(_1bC,_1bO),0,((_1bQ>>18)+240|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1bC,_1bO+1|0),0,((_1bQ>>12&63)+128|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1bC,_1bO+2|0),0,((_1bQ>>6&63)+128|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1bC,_1bO+3|0),0,((_1bQ&63)+128|0)>>>0&255),_1bR=_1bN+1|0,_1bS=_1bO+4|0;_1bK=_1bR;_1bL=_1bS;_=0;return __continue;}else{return new T3(0,1,new T(function(){if(_1bN!=_1bB){return new T6(0,_1bw,_1bx,_1by,_1bz,_1bN,_1bB);}else{return E(_1bI);}}),new T6(0,_1bC,_1bD,_1bE,_1bF,_1bG,_1bO));}}else{var _1bT=function(_1bU){var _1bV=function(_1bW){if((_1bF-_1bO|0)>=3){var _=writeOffAddr("w8",1,plusAddr(_1bC,_1bO),0,((_1bQ>>12)+224|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1bC,_1bO+1|0),0,((_1bQ>>6&63)+128|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1bC,_1bO+2|0),0,((_1bQ&63)+128|0)>>>0&255);return _1bJ(_1bN+1|0,_1bO+3|0,0);}else{return new T3(0,1,new T(function(){if(_1bN!=_1bB){return new T6(0,_1bw,_1bx,_1by,_1bz,_1bN,_1bB);}else{return E(_1bI);}}),new T6(0,_1bC,_1bD,_1bE,_1bF,_1bG,_1bO));}};if(56320>_1bQ){return _1bV(0);}else{if(_1bQ>57343){return _1bV(0);}else{return new T3(0,2,new T(function(){if(_1bN!=_1bB){return new T6(0,_1bw,_1bx,_1by,_1bz,_1bN,_1bB);}else{return E(_1bI);}}),new T6(0,_1bC,_1bD,_1bE,_1bF,_1bG,_1bO));}}};if(55296>_1bQ){return _1bT(0);}else{if(_1bQ>56319){return _1bT(0);}else{return new T3(0,2,new T(function(){if(_1bN!=_1bB){return new T6(0,_1bw,_1bx,_1by,_1bz,_1bN,_1bB);}else{return E(_1bI);}}),new T6(0,_1bC,_1bD,_1bE,_1bF,_1bG,_1bO));}}}}else{if((_1bF-_1bO|0)>=2){var _=writeOffAddr("w8",1,plusAddr(_1bC,_1bO),0,((_1bQ>>6)+192|0)>>>0&255),_=writeOffAddr("w8",1,plusAddr(_1bC,_1bO+1|0),0,((_1bQ&63)+128|0)>>>0&255),_1bR=_1bN+1|0,_1bS=_1bO+2|0;_1bK=_1bR;_1bL=_1bS;_=0;return __continue;}else{return new T3(0,1,new T(function(){if(_1bN!=_1bB){return new T6(0,_1bw,_1bx,_1by,_1bz,_1bN,_1bB);}else{return E(_1bI);}}),new T6(0,_1bC,_1bD,_1bE,_1bF,_1bG,_1bO));}}}else{var _=writeOffAddr("w8",1,plusAddr(_1bC,_1bO),0,_1bQ>>>0&255),_1bR=_1bN+1|0,_1bS=_1bO+1|0;_1bK=_1bR;_1bL=_1bS;_=0;return __continue;}}else{return new T3(0,0,new T(function(){if(_1bN!=_1bB){return new T6(0,_1bw,_1bx,_1by,_1bz,_1bN,_1bB);}else{return E(_1bI);}}),new T6(0,_1bC,_1bD,_1bE,_1bF,_1bG,_1bO));}}else{return new T3(0,1,new T(function(){if(_1bN!=_1bB){return new T6(0,_1bw,_1bx,_1by,_1bz,_1bN,_1bB);}else{return E(_1bI);}}),new T6(0,_1bC,_1bD,_1bE,_1bF,_1bG,_1bO));}})(_1bK,_1bL,_);if(_1bM!=__continue){return _1bM;}}};return _1bJ(_1bA,_1bH,_);},_1bX=function(_1bY,_1bZ,_){var _1c0=E(_1bY),_1c1=E(_1bZ);return _1bv(_1c0.a,_1c0.b,_1c0.c,_1c0.d,_1c0.e,_1c0.f,_1c1.a,_1c1.b,_1c1.c,_1c1.d,_1c1.e,_1c1.f,_);},_1c2=function(_){return 0;},_1c3=function(_1c4,_){return _1c2(_);},_1c5=function(_1c6,_1c7,_1c8,_1c9,_1ca,_1cb,_1cc,_1cd,_1ce,_1cf,_1cg,_1ch,_){var _1ci=new T6(0,_1c6,_1c7,_1c8,_1c9,0,0),_1cj=function(_1ck,_1cl,_){while(1){var _1cm=B((function(_1cn,_1co,_){if(_1co<_1cf){if(_1cn<_1cb){var _1cp=readOffAddr("w8",1,plusAddr(_1c6,_1cn),0),_1cq=_1cp;if(_1cq>127){var _1cr=function(_1cs){var _1ct=function(_1cu){var _1cv=function(_1cw){if(_1cq<240){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{switch(_1cb-_1cn|0){case 1:return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));case 2:var _1cx=readOffAddr("w8",1,plusAddr(_1c6,_1cn+1|0),0),_1cy=_1cx,_1cz=function(_1cA){var _1cB=function(_1cC){return (E(_1cq)==244)?(_1cy<128)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):(_1cy>143)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));};if(_1cq<241){return _1cB(0);}else{if(_1cq>243){return _1cB(0);}else{if(_1cy<128){return _1cB(0);}else{if(_1cy>191){return _1cB(0);}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}}};if(E(_1cq)==240){if(_1cy<144){return _1cz(0);}else{if(_1cy>191){return _1cz(0);}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}else{return _1cz(0);}break;case 3:var _1cD=readOffAddr("w8",1,plusAddr(_1c6,_1cn+1|0),0),_1cE=_1cD,_1cF=readOffAddr("w8",1,plusAddr(_1c6,_1cn+2|0),0),_1cG=_1cF,_1cH=function(_1cI){var _1cJ=function(_1cK){return (E(_1cq)==244)?(_1cE<128)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):(_1cE>143)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):(_1cG<128)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):(_1cG>191)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));};if(_1cq<241){return _1cJ(0);}else{if(_1cq>243){return _1cJ(0);}else{if(_1cE<128){return _1cJ(0);}else{if(_1cE>191){return _1cJ(0);}else{if(_1cG<128){return _1cJ(0);}else{if(_1cG>191){return _1cJ(0);}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}}}}};if(E(_1cq)==240){if(_1cE<144){return _1cH(0);}else{if(_1cE>191){return _1cH(0);}else{if(_1cG<128){return _1cH(0);}else{if(_1cG>191){return _1cH(0);}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}}}else{return _1cH(0);}break;default:var _1cL=readOffAddr("w8",1,plusAddr(_1c6,_1cn+1|0),0),_1cM=_1cL,_1cN=readOffAddr("w8",1,plusAddr(_1c6,_1cn+2|0),0),_1cO=_1cN,_1cP=readOffAddr("w8",1,plusAddr(_1c6,_1cn+3|0),0),_1cQ=_1cP,_1cR=function(_1cS){var _1cT=function(_1cU){if(E(_1cq)==244){if(_1cM<128){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1cM>143){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1cO<128){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1cO>191){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1cQ<128){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1cQ>191){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{var _=writeOffAddr("w32",4,_1cc,_1co,((1048576+(((_1cM&4294967295)-128|0)<<12)|0)+(((_1cO&4294967295)-128|0)<<6)|0)+((_1cQ&4294967295)-128|0)|0);return _1cj(_1cn+4|0,_1co+1|0,0);}}}}}}}else{return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}};if(_1cq<241){return _1cT(0);}else{if(_1cq>243){return _1cT(0);}else{if(_1cM<128){return _1cT(0);}else{if(_1cM>191){return _1cT(0);}else{if(_1cO<128){return _1cT(0);}else{if(_1cO>191){return _1cT(0);}else{if(_1cQ<128){return _1cT(0);}else{if(_1cQ>191){return _1cT(0);}else{var _=writeOffAddr("w32",4,_1cc,_1co,(((((_1cq&4294967295)-240|0)<<18)+(((_1cM&4294967295)-128|0)<<12)|0)+(((_1cO&4294967295)-128|0)<<6)|0)+((_1cQ&4294967295)-128|0)|0);return _1cj(_1cn+4|0,_1co+1|0,0);}}}}}}}}};if(E(_1cq)==240){if(_1cM<144){return _1cR(0);}else{if(_1cM>191){return _1cR(0);}else{if(_1cO<128){return _1cR(0);}else{if(_1cO>191){return _1cR(0);}else{if(_1cQ<128){return _1cR(0);}else{if(_1cQ>191){return _1cR(0);}else{var _=writeOffAddr("w32",4,_1cc,_1co,((((_1cM&4294967295)-128|0)<<12)+(((_1cO&4294967295)-128|0)<<6)|0)+((_1cQ&4294967295)-128|0)|0);return _1cj(_1cn+4|0,_1co+1|0,0);}}}}}}}else{return _1cR(0);}}}};if(_1cq<224){return C > 19 ? new F(function(){return _1cv(0);}) : (++C,_1cv(0));}else{if(_1cq>239){return C > 19 ? new F(function(){return _1cv(0);}) : (++C,_1cv(0));}else{switch(_1cb-_1cn|0){case 1:return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));case 2:var _1cV=readOffAddr("w8",1,plusAddr(_1c6,_1cn+1|0),0),_1cW=_1cV,_1cX=function(_1cY){var _1cZ=function(_1d0){var _1d1=function(_1d2){return (_1cq<238)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):(_1cW<128)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):(_1cW>191)?new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co)):new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));};if(E(_1cq)==237){if(_1cW<128){return _1d1(0);}else{if(_1cW>159){return _1d1(0);}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}else{return _1d1(0);}};if(_1cq<225){return _1cZ(0);}else{if(_1cq>236){return _1cZ(0);}else{if(_1cW<128){return _1cZ(0);}else{if(_1cW>191){return _1cZ(0);}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}}};if(E(_1cq)==224){if(_1cW<160){return _1cX(0);}else{if(_1cW>191){return _1cX(0);}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}else{return _1cX(0);}break;default:var _1d3=readOffAddr("w8",1,plusAddr(_1c6,_1cn+1|0),0),_1d4=_1d3,_1d5=readOffAddr("w8",1,plusAddr(_1c6,_1cn+2|0),0),_1d6=_1d5,_1d7=function(_1d8){var _1d9=function(_1da){var _1db=function(_1dc){if(_1cq<238){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1d4<128){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1d4>191){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1d6<128){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{if(_1d6>191){return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}else{var _=writeOffAddr("w32",4,_1cc,_1co,((((_1cq&4294967295)-224|0)<<12)+(((_1d4&4294967295)-128|0)<<6)|0)+((_1d6&4294967295)-128|0)|0);return _1cj(_1cn+3|0,_1co+1|0,0);}}}}}};if(E(_1cq)==237){if(_1d4<128){return _1db(0);}else{if(_1d4>159){return _1db(0);}else{if(_1d6<128){return _1db(0);}else{if(_1d6>191){return _1db(0);}else{var _=writeOffAddr("w32",4,_1cc,_1co,(53248+(((_1d4&4294967295)-128|0)<<6)|0)+((_1d6&4294967295)-128|0)|0);return _1cj(_1cn+3|0,_1co+1|0,0);}}}}}else{return _1db(0);}};if(_1cq<225){return _1d9(0);}else{if(_1cq>236){return _1d9(0);}else{if(_1d4<128){return _1d9(0);}else{if(_1d4>191){return _1d9(0);}else{if(_1d6<128){return _1d9(0);}else{if(_1d6>191){return _1d9(0);}else{var _=writeOffAddr("w32",4,_1cc,_1co,((((_1cq&4294967295)-224|0)<<12)+(((_1d4&4294967295)-128|0)<<6)|0)+((_1d6&4294967295)-128|0)|0);return _1cj(_1cn+3|0,_1co+1|0,0);}}}}}}};if(E(_1cq)==224){if(_1d4<160){return C > 19 ? new F(function(){return _1d7(0);}) : (++C,_1d7(0));}else{if(_1d4>191){return C > 19 ? new F(function(){return _1d7(0);}) : (++C,_1d7(0));}else{if(_1d6<128){return C > 19 ? new F(function(){return _1d7(0);}) : (++C,_1d7(0));}else{if(_1d6>191){return C > 19 ? new F(function(){return _1d7(0);}) : (++C,_1d7(0));}else{var _=writeOffAddr("w32",4,_1cc,_1co,(((_1d4&4294967295)-128|0)<<6)+((_1d6&4294967295)-128|0)|0);return _1cj(_1cn+3|0,_1co+1|0,0);}}}}}else{return C > 19 ? new F(function(){return _1d7(0);}) : (++C,_1d7(0));}}}}};if(_1cq<194){return C > 19 ? new F(function(){return _1ct(0);}) : (++C,_1ct(0));}else{if(_1cq>223){return C > 19 ? new F(function(){return _1ct(0);}) : (++C,_1ct(0));}else{if((_1cb-_1cn|0)>=2){var _1dd=readOffAddr("w8",1,plusAddr(_1c6,_1cn+1|0),0);if(_1dd>=128){if(_1dd<192){var _=writeOffAddr("w32",4,_1cc,_1co,(((_1cq&4294967295)-192|0)<<6)+((_1dd&4294967295)-128|0)|0);return _1cj(_1cn+2|0,_1co+1|0,0);}else{return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}else{return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}};if(_1cq<192){return C > 19 ? new F(function(){return _1cr(0);}) : (++C,_1cr(0));}else{if(_1cq>193){return C > 19 ? new F(function(){return _1cr(0);}) : (++C,_1cr(0));}else{return new T3(0,2,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}}else{var _=writeOffAddr("w32",4,_1cc,_1co,_1cq&4294967295),_1de=_1cn+1|0,_1df=_1co+1|0;_1ck=_1de;_1cl=_1df;_=0;return __continue;}}else{return new T3(0,0,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}}else{return new T3(0,1,new T(function(){if(_1cn!=_1cb){return new T6(0,_1c6,_1c7,_1c8,_1c9,_1cn,_1cb);}else{return E(_1ci);}}),new T6(0,_1cc,_1cd,_1ce,_1cf,_1cg,_1co));}})(_1ck,_1cl,_));if(_1cm!=__continue){return _1cm;}}};return _1cj(_1ca,_1ch,_);},_1dg=function(_1dh,_1di,_){var _1dj=E(_1dh),_1dk=E(_1di);return _1c5(_1dj.a,_1dj.b,_1dj.c,_1dj.d,_1dj.e,_1dj.f,_1dk.a,_1dk.b,_1dk.c,_1dk.d,_1dk.e,_1dk.f,_);},_1dl=new T(function(){return unCStr("UTF-8");}),_1dm=function(_1dn){var _1do=function(_){return new T5(0,_1bX,function(_1dp,_1dq,_){return C > 19 ? new F(function(){return _14W(_1dn,_1dp,_1dq,_);}) : (++C,_14W(_1dn,_1dp,_1dq,_));},_1c2,_1c2,_1c3);},_1dr=function(_){return new T5(0,_1dg,function(_1dp,_1dq,_){return C > 19 ? new F(function(){return _14z(_1dn,_1dp,_1dq,_);}) : (++C,_14z(_1dn,_1dp,_1dq,_));},_1c2,_1c2,_1c3);};return new T3(0,_1dl,_1dr,_1do);},_12t=function(_1ds,_1dt,_){var _1du=_11X(_1dt);if(!_8h(_1du,_11S)){if(!_8h(_1du,_11R)){if(!_8h(_1du,_11Q)){if(!_8h(_1du,_11W)){if(!_8h(_1du,_11V)){if(!_8h(_1du,_11U)){if(!_8h(_1du,_11T)){return _152(_1ds,_1dt,_);}else{return new T(function(){return _1dm(_1ds);});}}else{return new T(function(){return _1br(_1ds);});}}else{return new T(function(){return _1aW(_1ds);});}}else{return new T(function(){return _1aw(_1ds);});}}else{return new T(function(){return _18l(_1ds);});}}else{return new T(function(){return _17J(_1ds);});}}else{return new T(function(){return _17j(_1ds);});}},_1dv=new T(function(){return _12n(function(_){return _12t(3,_12q,0);});}),_1dw=function(_){var _1dx=nMV(_1dv),_1dy=_1dx;return new T2(0,function(_){return rMV(_1dy);},function(_1dz,_){var _=wMV(_1dy,_1dz);return 0;});},_1dA=new T(function(){return _12n(_1dw);}),_1dB=function(_1dC,_){var _1dD=getenv(_1dC);if(!addrEq(_1dD,0)){var _1dE=B(A1(E(_1dA).a,_)),_1dF=_11b(_1dE,_1dD,_);return new T1(1,_1dF);}else{return __Z;}},_1dG=function(_1dH,_){return _1dB(E(_1dH),_);},_1dI=function(_1dJ,_1dK){while(1){var _1dL=(function(_1dM,_1dN){var _1dO=E(_1dN);if(!_1dO._){_1dJ=new T(function(){if(!E(_1dO.b)){return false;}else{return _1dI(_1dM,_1dO.d);}},1);_1dK=_1dO.c;return __continue;}else{return E(_1dM);}})(_1dJ,_1dK);if(_1dL!=__continue){return _1dL;}}},_1dP=function(_1dQ,_1dR){while(1){var _1dS=(function(_1dT,_1dU){var _1dV=E(_1dU);if(!_1dV._){_1dQ=new T(function(){if(!E(_1dV.b)){return false;}else{return _1dP(_1dT,_1dV.d);}},1);_1dR=_1dV.c;return __continue;}else{return E(_1dT);}})(_1dQ,_1dR);if(_1dS!=__continue){return _1dS;}}},_1dW=function(_1dX,_1dY,_1dZ){var _1e0=E(_1dX);return new T6(0,new T1(1,_1dZ),_1e0.b,_1dY,_1e0.d,_1e0.e,new T(function(){var _1e1=E(_1e0.f);if(!_1e1._){var _1e2=E(_1dZ);if(!_1e2._){return new T1(1,_1e2.a);}else{return new T1(1,_1e2.a);}}else{return _1e1;}}));},_1e3=function(_1e4,_1e5,_1e6,_1e7,_){var _1e8=takeMVar(_1e7),_1e9=_1e8,_1ea=function(_1eb,_){var _=putMVar(_1e7,_1e9),_1ec=E(_1eb),_1ed=B(A2(_M,_1ec.a,_)),_1ee=_1ed.a,_1ef=_1ed.b,_1eg=hs_eqWord64(_1ee,new Long(4053623282,1685460941,true)),_1eh=function(_1ei){var _1ej=hs_eqWord64(_1ee,new Long(2677205718,3649059819,true));if(!_1ej){return die(_1ec);}else{var _1ek=hs_eqWord64(_1ef,new Long(3454527707,3314552285,true));if(!_1ek){return die(_1ec);}else{var _=die("Unsupported PrimOp: killThread#");return _1e3(_1e4,_1e5,_1e6,_1e7,_);}}};if(!_1eg){return _1eh(_);}else{var _1el=hs_eqWord64(_1ef,new Long(3693590983,2507416641,true));if(!_1el){return _1eh(_);}else{var _1em=new T(function(){return _1K(new T(function(){return _1dW(_1ec.b,_1e4,_1e5);}));});return die(_1em);}}};return jsCatch(new T(function(){return B(A1(_1e6,_1e9));}),_1ea);},_1en=function(_1eo){return E(E(_1eo).b);},_1ep=function(_1eq){return E(E(_1eq).e);},_1er=function(_1es,_){return new T1(1,_1es);},_1et=new T(function(){return _12n(function(_){var _1eu=nMV(__Z),_1ev=newByteArr(1);return new T6(0,_1ev,new T2(1,_1ev,_1eu),0,1,0,0);});}),_1ew=new T(function(){return _12n(function(_){var _1ex=nMV(__Z),_1ey=newByteArr(4);return new T6(0,_1ey,new T2(1,_1ey,_1ex),0,1,0,0);});}),_1ez=function(_1eA,_){var _1eB=E(_1eA),_1eC=_1eB.a,_1eD=_1eB.b,_1eE=_1eB.c,_1eF=_1eB.d,_1eG=_1eB.f,_1eH=_1eB.g,_1eI=_1eB.h,_1eJ=_1eB.i,_1eK=_1eB.j,_1eL=_1eB.k,_1eM=_1eB.m,_1eN=_1eB.n,_1eO=_1eB.o,_1eP=_1eB.p;if(!E(_1eB.e)){return new T2(0,_1eB,__Z);}else{var _1eQ=jsCatch(function(_){var _1eR=rMV(_1eG);if(!E(E(_1eR).c)){return __Z;}else{var _1eS=rMV(_1eG),_1eT=E(_1eS);if(_1eT.e!=_1eT.f){var _1eU=B(A(_1ep,[_1eD,_1eF,_1eT,_])),_=wMV(_1eG,_1eU);return __Z;}else{return __Z;}}},_1er),_1eV=_1eQ,_1eW=function(_,_1eX){var _=wMV(_1eK,__Z),_=wMV(_1eJ,_1ew),_=wMV(_1eG,_1et),_1eY=E(_1eB.l);if(!_1eY._){var _1eZ=E(_1eL);if(!_1eZ._){return new T2(0,{_:0,a:_1eC,b:_1eD,c:_1eE,d:E(_1eF),e:0,f:_1eG,g:_1eH,h:_1eI,i:_1eJ,j:_1eK,k:__Z,l:__Z,m:_1eM,n:_1eN,o:_1eO,p:_1eP},new T(function(){var _1f0=E(_1eV);if(!_1f0._){return E(_1eX);}else{return _1f0;}}));}else{var _1f1=B(A1(E(_1eZ.a).c,_));return new T2(0,{_:0,a:_1eC,b:_1eD,c:_1eE,d:E(_1eF),e:0,f:_1eG,g:_1eH,h:_1eI,i:_1eJ,j:_1eK,k:_1eZ,l:__Z,m:_1eM,n:_1eN,o:_1eO,p:_1eP},new T(function(){var _1f2=E(_1eV);if(!_1f2._){return E(_1eX);}else{return _1f2;}}));}}else{var _1f3=B(A1(E(_1eY.a).c,_)),_1f4=E(_1eL);if(!_1f4._){return new T2(0,{_:0,a:_1eC,b:_1eD,c:_1eE,d:E(_1eF),e:0,f:_1eG,g:_1eH,h:_1eI,i:_1eJ,j:_1eK,k:__Z,l:_1eY,m:_1eM,n:_1eN,o:_1eO,p:_1eP},new T(function(){var _1f5=E(_1eV);if(!_1f5._){return E(_1eX);}else{return _1f5;}}));}else{var _1f6=B(A1(E(_1f4.a).c,_));return new T2(0,{_:0,a:_1eC,b:_1eD,c:_1eE,d:E(_1eF),e:0,f:_1eG,g:_1eH,h:_1eI,i:_1eJ,j:_1eK,k:_1f4,l:_1eY,m:_1eM,n:_1eN,o:_1eO,p:_1eP},new T(function(){var _1f7=E(_1eV);if(!_1f7._){return E(_1eX);}else{return _1f7;}}));}}};if(!E(_1eP)._){var _1f8=jsCatch(function(_){var _1f9=B(A3(_1en,_1eC,_1eF,_));return __Z;},_1er);return _1eW(_,_1f8);}else{return _1eW(_,__Z);}}},_1fa=new T(function(){return unCStr("hGetContents");}),_1fb=function(_1fc,_1fd,_1fe,_1ff,_){var _1fg=function(_1fh,_1fi,_){while(1){var _1fj=B(A3(_1fc,_1fh,_1fi,_)),_1fk=E(_1fj),_1fl=_1fk.c;if(E(_1fk.a)==2){var _1fm=E(_1fk.b);if(E(_1fh).e!=_1fm.e){return new T3(0,2,_1fm,_1fl);}else{var _1fn=B(A3(_1fd,_1fm,_1fl,_)),_1fo=E(_1fn);_1fh=_1fo.a;_1fi=_1fo.b;continue;}}else{return _1fj;}}},_1fp=_1fg(_1fe,_1ff,_);return new T(function(){var _1fq=E(_1fp);return new T2(0,_1fq.b,_1fq.c);});},_1fr=function(_1fs,_1ft,_1fu,_1fv,_1fw,_1fx,_1fy,_1fz,_1fA,_1fB,_1fC,_1fD,_){var _1fE=new T6(0,_1fs,_1ft,_1fu,_1fv,0,0),_1fF=function(_1fG,_1fH,_){while(1){var _1fI=(function(_1fJ,_1fK,_){if(_1fK<_1fB){if(_1fJ<_1fx){var _1fL=readOffAddr("w8",1,plusAddr(_1fs,_1fJ),0),_=writeOffAddr("w32",4,_1fy,_1fK,_1fL&4294967295),_1fM=_1fJ+1|0,_1fN=_1fK+1|0;_1fG=_1fM;_1fH=_1fN;_=0;return __continue;}else{return new T3(0,0,new T(function(){if(_1fJ!=_1fx){return new T6(0,_1fs,_1ft,_1fu,_1fv,_1fJ,_1fx);}else{return E(_1fE);}}),new T6(0,_1fy,_1fz,_1fA,_1fB,_1fC,_1fK));}}else{return new T3(0,1,new T(function(){if(_1fJ!=_1fx){return new T6(0,_1fs,_1ft,_1fu,_1fv,_1fJ,_1fx);}else{return E(_1fE);}}),new T6(0,_1fy,_1fz,_1fA,_1fB,_1fC,_1fK));}})(_1fG,_1fH,_);if(_1fI!=__continue){return _1fI;}}};return _1fF(_1fw,_1fD,_);},_1fO=function(_1fP){return E(E(_1fP).b);},_1fQ=new T(function(){return _1K(new T6(0,__Z,4,__Z,__Z,__Z,__Z));}),_1fR=function(_){return die(_1fQ);},_1fS=new T(function(){return B(_tv("GHC/IO/Handle/Internals.hs:873:7-30|Just decoder"));}),_1fT=function(_1fU,_1fV,_1fW,_1fX,_1fY,_1fZ,_1g0,_1g1,_){while(1){var _1g2=E(_1fU),_1g3=_1g2.f,_1g4=_1g2.l,_1g5=_1g0-_1fZ|0,_1g6=memmove(_1fV,plusAddr(_1fV,_1fZ),_1g5>>>0),_1g7=B(A(_1fO,[_1g2.b,_1g2.d,new T6(0,_1fV,_1fW,_1fX,_1fY,0,_1g5),0])),_1g8=E(_1g7),_1g9=_1g8.b;if(!E(_1g8.a)){var _1ga=E(_1g9);if(_1ga.e!=_1ga.f){var _1gb=E(_1g4);if(!_1gb._){return E(_1fS);}else{var _1gc=B(A3(E(_1gb.a).b,_1ga,_1g1,0)),_1gd=E(_1gc),_=wMV(_1g3,_1gd.a),_1ge=E(_1gd.b);if(_1ge.f!=E(_1g1).f){return _1ge;}else{return C > 19 ? new F(function(){return _1gf(_1g2,_1ge,0);}) : (++C,_1gf(_1g2,_1ge,0));}}}else{return _1fR(0);}}else{var _1gg=E(_1g4);if(!_1gg._){return E(_1fS);}else{var _1gh=E(_1gg.a),_1gi=B(A1(_1gh.d,0)),_=wMV(_1g2.h,new T2(0,_1gi,_1g9)),_1gj=_1fb(_1gh.a,_1gh.b,_1g9,_1g1,0),_1gk=E(_1gj),_1gl=_1gk.a,_=wMV(_1g3,_1gl),_1gm=E(_1gk.b);if(E(_1g1).f!=_1gm.f){return _1gm;}else{var _1gn=E(_1gl);_1fU=_1g2;_1fV=_1gn.a;_1fW=_1gn.b;_1fX=_1gn.c;_1fY=_1gn.d;_1fZ=_1gn.e;_1g0=_1gn.f;_1g1=_1gm;_=0;continue;}}}}},_1go=new T(function(){return err(new T(function(){return unCStr("codec_state");}));}),_1gf=function(_1gp,_1gq,_){var _1gr=E(_1gp),_1gs=_1gr.f,_1gt=_1gr.h,_1gu=rMV(_1gs),_1gv=E(_1gu),_1gw=function(_,_1gx){var _1gy=E(_1gr.l);if(!_1gy._){var _=wMV(_1gt,new T2(0,_1go,_1gx)),_1gz=E(_1gx),_1gA=E(_1gq),_1gB=_1gA.f,_1gC=_1fr(_1gz.a,_1gz.b,_1gz.c,_1gz.d,_1gz.e,_1gz.f,_1gA.a,_1gA.b,_1gA.c,_1gA.d,_1gA.e,_1gB,_),_1gD=E(_1gC),_1gE=_1gD.b,_=wMV(_1gs,_1gE),_1gF=E(_1gD.c);if(_1gF.f!=_1gB){return _1gF;}else{var _1gG=E(_1gE);return C > 19 ? new F(function(){return _1fT(_1gr,_1gG.a,_1gG.b,_1gG.c,_1gG.d,_1gG.e,_1gG.f,_1gA,_);}) : (++C,_1fT(_1gr,_1gG.a,_1gG.b,_1gG.c,_1gG.d,_1gG.e,_1gG.f,_1gA,_));}}else{var _1gH=E(_1gy.a),_1gI=B(A1(_1gH.d,_)),_=wMV(_1gt,new T2(0,_1gI,_1gx)),_1gJ=_1fb(_1gH.a,_1gH.b,_1gx,_1gq,_),_1gK=E(_1gJ),_1gL=_1gK.a,_=wMV(_1gs,_1gL),_1gM=E(_1gK.b),_1gN=E(_1gq);if(_1gM.f!=_1gN.f){return _1gM;}else{var _1gO=E(_1gL);return C > 19 ? new F(function(){return _1fT(_1gr,_1gO.a,_1gO.b,_1gO.c,_1gO.d,_1gO.e,_1gO.f,_1gN,_);}) : (++C,_1fT(_1gr,_1gO.a,_1gO.b,_1gO.c,_1gO.d,_1gO.e,_1gO.f,_1gN,_));}}};if(_1gv.e!=_1gv.f){return C > 19 ? new F(function(){return _1gw(_,_1gv);}) : (++C,_1gw(_,_1gv));}else{var _1gP=B(A(_1fO,[_1gr.b,_1gr.d,_1gv,_])),_1gQ=E(_1gP);if(!E(_1gQ.a)){return die(_1fQ);}else{return C > 19 ? new F(function(){return _1gw(_,_1gQ.b);}) : (++C,_1gw(_,_1gQ.b));}}},_1gR=new T(function(){return unCStr("illegal handle type");}),_1gS=new T(function(){return unCStr("\r");}),_1gT=function(_1gU,_1gV,_1gW,_1gX,_1gY){return _7a(new T6(0,new T1(1,_1gU),_1gV,_1fa,_1gW,_1gX,new T(function(){var _1gZ=E(_1gY);if(!_1gZ._){var _1h0=E(_1gU);if(!_1h0._){return new T1(1,_1h0.a);}else{return new T1(1,_1h0.a);}}else{return _1gZ;}})),_1M);},_1h1=new T(function(){return unCStr("delayed read on closed handle");}),_1h2=function(_1h3,_){return new T(function(){var _1h4=B(A1(_1h3,_));return E(_1h4);});},_1h5=function(_2j,_){return _1h2(_2j,_);},_1h6=function(_1h7,_){var _1h8=new T1(1,_1h7),_1h9=new T(function(){return _1K(new T6(0,_1h8,5,_1fa,_1gR,__Z,__Z));}),_1ha=new T(function(){return _1K(new T6(0,_1h8,5,_1fa,_1h1,__Z,__Z));}),_1hb=function(_){var _1hc=function(_1hd,_){var _1he=E(_1hd),_1hf=_1he.i,_1hg=_1he.n;switch(E(_1he.e)){case 0:return die(_1ha);case 1:var _1hh=rMV(_1hf),_1hi=_1hh,_1hj=function(_1hk,_){var _1hl=E(_1hk),_1hm=B(A2(_M,_1hl.a,0)),_1hn=hs_eqWord64(_1hm.a,new Long(4053623282,1685460941,true));if(!_1hn){return die(_1hl);}else{var _1ho=hs_eqWord64(_1hm.b,new Long(3693590983,2507416641,true));if(!_1ho){return die(_1hl);}else{var _1hp=_1ez(_1he,0);return new T2(0,E(_1hp).a,new T(function(){var _1hq=E(_1hl.b),_1hr=E(_1hq.b);if(_1hr==4){var _1hs=E(_1hi);if(_1hs.e!=_1hs.f){return E(_1gS);}else{return __Z;}}else{return B(_1gT(_1h7,_1hr,_1hq.d,_1hq.e,_1hq.f));}}));}}},_1ht=function(_){var _1hu=E(_1hi),_1hv=_1hu.a,_1hw=_1hu.b,_1hx=_1hu.c,_1hy=_1hu.d,_1hz=_1hu.e,_1hA=_1hu.f,_1hB=function(_,_1hC,_1hD,_1hE,_1hF,_1hG,_1hH){var _1hI=_1h6(_1h7,0);if(!E(_1hg)){if(_1hG!=_1hH){var _1hJ=function(_1hK,_1hL,_){while(1){if(_1hL>=_1hG){var _1hM=readOffAddr("w32",4,_1hC,_1hL),_1hN=new T2(1,_1hM,_1hK),_1hO=_1hL-1|0;_1hK=_1hN;_1hL=_1hO;_=0;continue;}else{return _1hK;}}},_1hP=_1hJ(_1hI,_1hH-1|0,0),_=wMV(_1hf,new T6(0,_1hC,_1hD,_1hE,_1hF,0,0));return new T2(0,_1he,_1hP);}else{var _=wMV(_1hf,new T6(0,_1hC,_1hD,_1hE,_1hF,0,0));return new T2(0,_1he,_1hI);}}else{if(_1hG!=_1hH){var _1hQ=readOffAddr("w32",4,_1hC,_1hH-1|0),_1hR=function(_1hS,_1hT,_){while(1){if(_1hT>=_1hG){var _1hU=readOffAddr("w32",4,_1hC,_1hT),_1hV=E(_1hU);if(_1hV==10){if(_1hT<=_1hG){var _1hW=new T2(1,10,_1hS),_1hX=_1hT-1|0;_1hS=_1hW;_1hT=_1hX;_=0;continue;}else{var _1hY=readOffAddr("w32",4,_1hC,_1hT-1|0);if(E(_1hY)==13){var _1hW=new T2(1,10,_1hS),_1hX=_1hT-2|0;_1hS=_1hW;_1hT=_1hX;_=0;continue;}else{var _1hW=new T2(1,10,_1hS),_1hX=_1hT-1|0;_1hS=_1hW;_1hT=_1hX;_=0;continue;}}}else{var _1hW=new T2(1,_1hV,_1hS),_1hX=_1hT-1|0;_1hS=_1hW;_1hT=_1hX;_=0;continue;}}else{return _1hS;}}};if(E(_1hQ)==13){var _1hZ=_1hR(_1hI,_1hH-2|0,0),_1i0=_1hH-1|0,_=wMV(_1hf,new T(function(){if(_1i0!=_1hH){return new T6(0,_1hC,_1hD,_1hE,_1hF,_1i0,_1hH);}else{return new T6(0,_1hC,_1hD,_1hE,_1hF,0,0);}}));return new T2(0,_1he,_1hZ);}else{var _1i1=_1hR(_1hI,_1hH-1|0,0),_=wMV(_1hf,new T6(0,_1hC,_1hD,_1hE,_1hF,0,0));return new T2(0,_1he,_1i1);}}else{var _=wMV(_1hf,new T(function(){var _1i2=E(_1hH);if(!_1i2){return new T6(0,_1hC,_1hD,_1hE,_1hF,0,0);}else{return new T6(0,_1hC,_1hD,_1hE,_1hF,0,_1i2);}}));return new T2(0,_1he,_1hI);}}};switch(_1hA-_1hz|0){case 0:var _1i3=B(_1gf(_1he,_1hu,0)),_1i4=E(_1i3);return _1hB(0,_1i4.a,_1i4.b,_1i4.c,_1i4.d,_1i4.e,_1i4.f);case 1:if(!E(_1hg)){return _1hB(0,_1hv,_1hw,_1hx,_1hy,_1hz,_1hA);}else{var _1i5=readOffAddr("w32",4,_1hv,_1hz);if(E(_1i5)==13){var _=writeOffAddr("w32",4,_1hv,0,13),_1i6=B(_1gf(_1he,new T6(0,_1hv,_1hw,_1hx,_1hy,0,1),0)),_1i7=E(_1i6);return _1hB(0,_1i7.a,_1i7.b,_1i7.c,_1i7.d,_1i7.e,_1i7.f);}else{return _1hB(0,_1hv,_1hw,_1hx,_1hy,_1hz,_1hA);}}break;default:return _1hB(0,_1hv,_1hw,_1hx,_1hy,_1hz,_1hA);}};return jsCatch(_1ht,_1hj);default:return die(_1h9);}},_1i8=E(_1h7);if(!_1i8._){var _1i9=_1i8.b,_1ia=function(_){var _1ib=_1e3(_1fa,_1i8,_1hc,_1i9,0),_1ic=E(_1ib),_=putMVar(_1i9,_1ic.a);return _1ic.b;};if(!0){return _1ia();}else{return _1ia(0);}}else{var _1id=_1i8.b,_1ie=function(_){var _1if=_1e3(_1fa,_1i8,_1hc,_1id,0),_1ig=E(_1if),_=putMVar(_1id,_1ig.a);return _1ig.b;};if(!0){return _1ie();}else{return _1ie(0);}}};return _1h5(_1hb,_);},_1ih=new T(function(){return _1K(new T6(0,__Z,5,__Z,new T(function(){return unCStr("handle is closed");}),__Z,__Z));}),_1ii=function(_){return die(_1ih);},_1ij=new T(function(){return _1K(new T6(0,__Z,5,__Z,new T(function(){return unCStr("handle is not open for reading");}),__Z,__Z));}),_1ik=function(_){return die(_1ij);},_1il=function(_1im,_1in,_){var _1io=E(_1in),_1ip=_1io.f,_1iq=_1io.i;switch(E(_1io.e)){case 2:return C > 19 ? new F(function(){return A2(_1im,_1io,_);}) : (++C,A2(_1im,_1io,_));break;case 3:return _1ik(_);case 4:return _1ik(_);case 5:var _1ir=rMV(_1ip),_1is=E(_1ir);if(!E(_1is.c)){return C > 19 ? new F(function(){return A2(_1im,_1io,_);}) : (++C,A2(_1im,_1io,_));}else{if(_1is.e!=_1is.f){var _1it=rMV(_1ip),_1iu=E(_1it);if(_1iu.e!=_1iu.f){var _1iv=B(A(_1ep,[_1io.b,_1io.d,_1iu,_])),_=wMV(_1ip,_1iv),_1iw=rMV(_1iq),_=wMV(_1iq,new T(function(){var _1ix=E(_1iw);return new T6(0,_1ix.a,_1ix.b,0,_1ix.d,_1ix.e,_1ix.f);})),_1iy=rMV(_1ip),_=wMV(_1ip,new T(function(){var _1iz=E(_1iy);return new T6(0,_1iz.a,_1iz.b,0,_1iz.d,_1iz.e,_1iz.f);}));return C > 19 ? new F(function(){return A2(_1im,_1io,_);}) : (++C,A2(_1im,_1io,_));}else{var _1iA=rMV(_1iq),_=wMV(_1iq,new T(function(){var _1iB=E(_1iA);return new T6(0,_1iB.a,_1iB.b,0,_1iB.d,_1iB.e,_1iB.f);})),_1iC=rMV(_1ip),_=wMV(_1ip,new T(function(){var _1iD=E(_1iC);return new T6(0,_1iD.a,_1iD.b,0,_1iD.d,_1iD.e,_1iD.f);}));return C > 19 ? new F(function(){return A2(_1im,_1io,_);}) : (++C,A2(_1im,_1io,_));}}else{var _1iE=rMV(_1iq),_=wMV(_1iq,new T(function(){var _1iF=E(_1iE);return new T6(0,_1iF.a,_1iF.b,0,_1iF.d,_1iF.e,_1iF.f);})),_1iG=rMV(_1ip),_=wMV(_1ip,new T(function(){var _1iH=E(_1iG);return new T6(0,_1iH.a,_1iH.b,0,_1iH.d,_1iH.e,_1iH.f);}));return C > 19 ? new F(function(){return A2(_1im,_1io,_);}) : (++C,A2(_1im,_1io,_));}}break;default:return _1ii(_);}},_1iI=function(_1iJ,_1iK,_1iL,_){var _1iM=E(_1iK);if(!_1iM._){var _1iN=_1iM.b,_1iO=function(_){var _1iP=_1e3(_1iJ,_1iM,function(_1iQ,_){return C > 19 ? new F(function(){return _1il(_1iL,_1iQ,_);}) : (++C,_1il(_1iL,_1iQ,_));},_1iN,_),_1iR=E(_1iP),_=putMVar(_1iN,_1iR.a);return _1iR.b;};if(!0){return _1iO();}else{return _1iO(_);}}else{var _1iS=_1iM.b,_1iT=function(_){var _1iU=_1e3(_1iJ,_1iM,function(_1iQ,_){return C > 19 ? new F(function(){return _1il(_1iL,_1iQ,_);}) : (++C,_1il(_1iL,_1iQ,_));},_1iS,_),_1iV=E(_1iU),_=putMVar(_1iS,_1iV.a);return _1iV.b;};if(!0){return _1iT();}else{return _1iT(_);}}},_1iW=function(_1iX,_){var _1iY=function(_1iZ,_){var _1j0=_1h6(_1iX,_);return new T2(0,new T(function(){var _1j1=E(_1iZ);return {_:0,a:_1j1.a,b:_1j1.b,c:_1j1.c,d:E(_1j1.d),e:1,f:_1j1.f,g:_1j1.g,h:_1j1.h,i:_1j1.i,j:_1j1.j,k:_1j1.k,l:_1j1.l,m:_1j1.m,n:_1j1.n,o:_1j1.o,p:_1j1.p};}),_1j0);};return _1iI(_1fa,_1iX,_1iY,_);},_1j2=function(_1j3){return E(E(_1j3).b);},_1j4=function(_1j5,_1j6,_1j7){var _1j8=new T(function(){return B(A2(_1j5,function(_1j9){return C > 19 ? new F(function(){return A2(_1j5,_1j9,_1j7);}) : (++C,A2(_1j5,_1j9,_1j7));},_1j6));}),_1ja=function(_1jb){return C > 19 ? new F(function(){return A1(_1j8,function(_1jc){return C > 19 ? new F(function(){return A1(_1jc,_1jb);}) : (++C,A1(_1jc,_1jb));});}) : (++C,A1(_1j8,function(_1jc){return C > 19 ? new F(function(){return A1(_1jc,_1jb);}) : (++C,A1(_1jc,_1jb));}));};return _1ja;},_1jd=function(_1je){return new T2(0,_1je,function(_kv,_kw){return _1j4(_1je,_kv,_kw);});},_1jf=function(_1jg,_1jh,_1ji){var _1jj=new T(function(){return B(A3(_2R,_2T(_1jg),_1ji,_1jh));}),_1jk=function(_1jl){return C > 19 ? new F(function(){return A1(_1jj,function(_1jm){return C > 19 ? new F(function(){return A1(_1jm,_1jl);}) : (++C,A1(_1jm,_1jl));});}) : (++C,A1(_1jj,function(_1jm){return C > 19 ? new F(function(){return A1(_1jm,_1jl);}) : (++C,A1(_1jm,_1jl));}));};return _1jk;},_1jn=function(_1jo,_1jp){return C > 19 ? new F(function(){return A1(_1jo,function(_1jq){return C > 19 ? new F(function(){return A1(_1jq,_1jp);}) : (++C,A1(_1jq,_1jp));});}) : (++C,A1(_1jo,function(_1jq){return C > 19 ? new F(function(){return A1(_1jq,_1jp);}) : (++C,A1(_1jq,_1jp));}));},_1jr=function(_1js){return new T3(0,_1js,_1jn,function(_kv,_kw){return _1jf(_1js,_kv,_kw);});},_1jt=new T(function(){return _1jr(new T(function(){var _1ju=function(_1jv,_1jw){return C > 19 ? new F(function(){return A1(_1jw,_1jv);}) : (++C,A1(_1jw,_1jv));},_1jx=new T(function(){return _1jd(_k9);});return new T2(0,_1ju,_1jx);}));}),_1jy=function(_1jz){var _1jA=E(_1jz);return (_1jA._==0)?E(_1jA.a):E(_1jA.a);},_1jB=function(_1jC,_1jD,_1jE){var _1jF=new T(function(){return B(A1(_1jC,_1jE));}),_1jG=new T(function(){return B(A1(_1jD,_1jE));}),_1jH=function(_1jI){var _1jJ=new T(function(){return B(A1(_1jG,_1jI));}),_1jK=new T(function(){return B(A1(_1jF,_1jI));}),_1jL=function(_1jM){return C > 19 ? new F(function(){return A1(_1jK,new T(function(){return B(A1(_1jJ,_1jM));}));}) : (++C,A1(_1jK,new T(function(){return B(A1(_1jJ,_1jM));})));};return _1jL;};return _1jH;},_1jN=function(_1jO,_1jP){var _1jQ=new T(function(){return B(A1(_1jO,_1jP));});return function(_1jR){return C > 19 ? new F(function(){return A1(_1jR,_1jQ);}) : (++C,A1(_1jR,_1jQ));};},_1jS=function(_1jT,_1jU){return new T3(0,_1jT,new T(function(){return E(E(_1jU).b);}),_2L);},_1jV=function(_1jW,_1jX,_1jY){var _1jZ=new T(function(){return B(A1(_1jX,_1jY));}),_1k0=new T(function(){return B(A1(_1jW,new T(function(){return E(E(_1jZ).a);})));});return new T3(0,_1k0,new T(function(){return E(E(_1jZ).b);}),new T(function(){return E(E(_1jZ).c);}));},_1k1=function(_1k2,_1k3,_1k4){return C > 19 ? new F(function(){return _2Z(_2M,_4S,function(_1k5){return _1jV(_1k3,_1k2,_1k5);},_1k4);}) : (++C,_2Z(_2M,_4S,function(_1k5){return _1jV(_1k3,_1k2,_1k5);},_1k4));},_1k6=new T3(0,new T2(0,_1jS,new T2(0,_1jV,function(_1k7,_1k8){return _3f(_4S,_1k7,_1k8);})),function(_1k9,_1ka){return C > 19 ? new F(function(){return _2Z(_2M,_4S,_1k9,_1ka);}) : (++C,_2Z(_2M,_4S,_1k9,_1ka));},_1k1),_1kb=function(_1kc,_1kd,_1ke){var _1kf=new T(function(){var _1kg=function(_1kh){var _1ki=E(_1kh),_1kj=E(_1ki.a);if(!_1kj._){return __Z;}else{var _1kk=E(_1kj.a);return new T1(1,new T2(0,new T3(0,_1kk.a,_1ki.b,_1ki.c),new T(function(){return B(A1(_1kk.b,_1ke));})));}};return B(A3(_2R,_2T(_2P(_kA(_1kc))),_1kg,new T(function(){return B(A1(_1kd,_1ke));})));});return C > 19 ? new F(function(){return A2(_kP,_1kc,_1kf);}) : (++C,A2(_kP,_1kc,_1kf));},_1kl=function(_1km,_1kn,_1ko,_1kp,_1kq){var _1kr=new T(function(){return _2z(_1km);}),_1ks=new T(function(){return B(A2(_kC,_1kn,new T(function(){return B(A1(_1ko,new T2(0,_1kp,_1kq)));})));}),_1kt=function(_1ku){var _1kv=E(_1ku);if(!_1kv._){return E(new T3(0,__Z,_1kq,_1kr));}else{var _1kw=E(_1kv.a),_1kx=E(_1kw.a);return new T3(0,new T1(1,new T2(0,_1kx.a,function(_1ky){return E(_1kw.b);})),_1kq,_1kx.c);}};return C > 19 ? new F(function(){return A3(_2R,_2T(_2P(_kA(_1kn))),_1kt,_1ks);}) : (++C,A3(_2R,_2T(_2P(_kA(_1kn))),_1kt,_1ks));},_1kz=new T3(0,_1k6,function(_1kA,_1kB){var _1kC=E(_1kB);return C > 19 ? new F(function(){return _1kl(_2M,_lL,_1kA,_1kC.a,_1kC.b);}) : (++C,_1kl(_2M,_lL,_1kA,_1kC.a,_1kC.b));},function(_1kD,_1kE){return C > 19 ? new F(function(){return _1kb(_lL,_1kD,_1kE);}) : (++C,_1kb(_lL,_1kD,_1kE));}),_1kF=function(_1kG,_1kH){return C > 19 ? new F(function(){return _2Z(_2M,_1jt,_1kG,_1kH);}) : (++C,_2Z(_2M,_1jt,_1kG,_1kH));},_1kI=function(_1kJ,_1kK,_1kL){return C > 19 ? new F(function(){return A1(_1kL,new T3(0,_1kJ,new T(function(){return E(E(_1kK).b);}),_2L));}) : (++C,A1(_1kL,new T3(0,_1kJ,new T(function(){return E(E(_1kK).b);}),_2L)));},_1kM=function(_1kN,_1kO,_1kP){var _1kQ=new T(function(){return B(A1(_1kO,_1kP));}),_1kR=function(_1kS){var _1kT=function(_1kU){var _1kV=new T(function(){return B(A1(_1kN,new T(function(){return E(E(_1kU).a);})));});return C > 19 ? new F(function(){return A1(_1kS,new T3(0,_1kV,new T(function(){return E(E(_1kU).b);}),new T(function(){return E(E(_1kU).c);})));}) : (++C,A1(_1kS,new T3(0,_1kV,new T(function(){return E(E(_1kU).b);}),new T(function(){return E(E(_1kU).c);}))));};return C > 19 ? new F(function(){return A1(_1kQ,_1kT);}) : (++C,A1(_1kQ,_1kT));};return _1kR;},_1kW=function(_1kX,_1kY){return _3f(_1jt,_1kX,_1kY);},_1kZ=function(_1l0,_1l1,_1l2){return C > 19 ? new F(function(){return _2Z(_2M,_1jt,function(_1k5){return _1kM(_1l1,_1l0,_1k5);},_1l2);}) : (++C,_2Z(_2M,_1jt,function(_1k5){return _1kM(_1l1,_1l0,_1k5);},_1l2));},_1l3=new T3(0,new T2(0,_1kI,new T2(0,_1kM,_1kW)),_1kF,_1kZ),_1l4=function(_1l5,_1l6,_1l7){var _1l8=new T(function(){return B(A1(_1l5,_1l7));}),_1l9=function(_1la,_1lb){var _1lc=function(_1ld,_1le){var _1lf=new T(function(){return B(A2(_1la,_1ld,new T(function(){return _1jy(_1le);})));});return new T1(1,_1lf);},_1lg=B(A2(_1l8,_1lc,new T1(0,_1lb)));if(!_1lg._){return C > 19 ? new F(function(){return A3(_1l6,_1l7,_1la,_1lg.a);}) : (++C,A3(_1l6,_1l7,_1la,_1lg.a));}else{return E(_1lg.a);}};return _1l9;},_1lh=function(_1li){return E(E(_1li).a);},_1lj=function(_1lk){return E(E(_1lk).b);},_1ll=function(_1lm,_1ln,_1lo){var _1lp=new T(function(){return _2P(_1lm);}),_1lq=new T(function(){return _2T(_1lp);}),_1lr=new T(function(){return _2V(_1lp);}),_1ls=function(_1lt){var _1lu=new T(function(){return B(A3(_2R,_1lq,_s3,new T(function(){return B(A1(_1lo,_1lt));})));});return C > 19 ? new F(function(){return A3(_s6,_1lq,_1lu,new T(function(){return B(A1(_1lr,_1lt));}));}) : (++C,A3(_s6,_1lq,_1lu,new T(function(){return B(A1(_1lr,_1lt));})));};return C > 19 ? new F(function(){return A3(_2X,_1lm,_1ln,_1ls);}) : (++C,A3(_2X,_1lm,_1ln,_1ls));},_1lv=function(_1lw){return new T3(0,new T2(0,__Z,_n),new T(function(){return E(E(_1lw).b);}),_2L);},_1lx=function(_1ly){return E(E(_1ly).c);},_1lz=function(_1lA,_1lB){return C > 19 ? new F(function(){return A(_kR,[_1lA,_1lA,_3C,_3w,_3F,new T(function(){return B(A2(_2V,_2P(_kA(_1lA)),_1lB));})]);}) : (++C,A(_kR,[_1lA,_1lA,_3C,_3w,_3F,new T(function(){return B(A2(_2V,_2P(_kA(_1lA)),_1lB));})]));},_1lC=function(_1lD){return E(_1lD);},_1lE=function(_1lF){return E(E(_1lF).b);},_1lG=function(_1lH){return E(E(_1lH).a);},_1lI=function(_1lJ,_1lK,_1lL,_1lM){var _1lN=new T(function(){return _1lx(_1lL);}),_1lO=function(_1lP){var _1lQ=new T(function(){return B(A1(_1lN,_1lP));}),_1lR=function(_1lS){var _1lT=new T(function(){return B(A1(_1lQ,new T(function(){return E(E(_1lS).b);})));});return function(_1lU){return C > 19 ? new F(function(){return A1(_1lU,new T3(0,0,_1lT,_2L));}) : (++C,A1(_1lU,new T3(0,0,_1lT,_2L)));};};return _1lR;},_1lV=function(_1lW){return C > 19 ? new F(function(){return _1ll(_1lK,_1lW,_1lO);}) : (++C,_1ll(_1lK,_1lW,_1lO));},_1lX=new T(function(){return _1lh(_1lL);}),_1lY=new T(function(){return _1lj(_1lL);}),_1lZ=function(_1m0){var _1m1=E(_1m0);return C > 19 ? new F(function(){return A1(_1m1.b,new T(function(){return B(_1lz(_1lJ,_1m1.a));}));}) : (++C,A1(_1m1.b,new T(function(){return B(_1lz(_1lJ,_1m1.a));})));},_1m2=function(_1m3){var _1m4=new T(function(){return E(E(_1m3).b);}),_1m5=new T(function(){var _1m6=B(A2(_1lG,_1lY,_1m4));if(!_1m6._){return _1lv;}else{var _1m7=E(_1m6.a),_1m8=_1m7.a,_1m9=B(A1(_1lM,_1m8));if(!_1m9._){var _1ma=function(_1mb){return new T3(0,new T2(0,_1m9.a,_1lV),new T(function(){return E(E(_1mb).b);}),_2L);};return _1ma;}else{var _1mc=new T(function(){if(!E(_1m9.a)){return __Z;}else{return new T2(1,new T(function(){return B(A2(_1lE,_1lX,_1m8));}),__Z);}}),_1md=function(_1me){return new T3(0,new T2(0,_1mc,_n),new T(function(){return E(E(_1me).b);}),_2L);};return _3f(_4S,function(_1mf){return E(new T3(0,_1lC,_1m7.b,_2L));},_1md);}}});return new T3(0,_1m5,_1m4,_2L);},_1mg=function(_1mh){var _1mi=_1m2(_1mh);return new T3(0,_1mi.a,_1mi.b,_1mi.c);},_1mj=function(_1mk){var _1ml=new T(function(){return B(_2Z(_2M,_4S,_1mg,_1mk));});return function(_1mm){return C > 19 ? new F(function(){return A1(_1mm,_1ml);}) : (++C,A1(_1mm,_1ml));};};return C > 19 ? new F(function(){return A3(_2X,_1lK,_1mj,_1lZ);}) : (++C,A3(_2X,_1lK,_1mj,_1lZ));},_1mn={_:0,a:_1kz,b:new T2(0,_1jB,function(_1mo,_1mp,_1mq){return E(_1mq);}),c:_1l3,d:_1k6,e:_1jN,f:function(_1mr,_1ms){return C > 19 ? new F(function(){return _1lI(_1kz,_1l3,_1mr,_1ms);}) : (++C,_1lI(_1kz,_1l3,_1mr,_1ms));},g:function(_1mt,_1mu,_1mv){return E(_1mv);},h:_1l4,i:_1jB},_1mw=new T3(0,new T2(0,function(_1mx){return false;},function(_1my){return E(_1my);}),new T2(0,function(_1mz){var _1mA=E(_1mz);return (_1mA._==0)?__Z:new T1(1,new T2(0,_1mA.a,_1mA.b));},_Kh),function(_1mB,_1mC){return E(_1mC);}),_1mD=new T2(1,10,__Z),_1mE=function(_1mF){var _1mG=new T(function(){var _1mH=function(_1mI){var _1mJ=E(_1mI);return (_1mJ._==0)?__Z:new T2(1,new T(function(){return _8m(_1mF,_1mJ.a);}),new T(function(){return _1mH(_1mJ.b);}));};if(!B(_2B(_Zi,_1mH(_1mD)))){return true;}else{return false;}});return new T1(1,_1mG);},_1mK=function(_1mL){return E(E(_1mL).c);},_1mM=function(_1mN){return E(E(_1mN).h);},_1mO=function(_1mP,_1mQ){return C > 19 ? new F(function(){return A3(_1mM,_1mP,new T(function(){return B(_1mR(_1mP,_1mQ));}),new T(function(){return B(A2(_2V,_2P(_1mK(_1mP)),__Z));}));}) : (++C,A3(_1mM,_1mP,new T(function(){return B(_1mR(_1mP,_1mQ));}),new T(function(){return B(A2(_2V,_2P(_1mK(_1mP)),__Z));})));},_1mR=function(_1mS,_1mT){var _1mU=_2T(_2P(_1mK(_1mS)));return C > 19 ? new F(function(){return A3(_s6,_1mU,new T(function(){return B(A3(_2R,_1mU,_Kh,_1mT));}),new T(function(){return B(_1mO(_1mS,_1mT));}));}) : (++C,A3(_s6,_1mU,new T(function(){return B(A3(_2R,_1mU,_Kh,_1mT));}),new T(function(){return B(_1mO(_1mS,_1mT));})));},_1mV=new T(function(){return B(_1mR(_1mn,new T(function(){return B(_1lI(_1kz,_1l3,_1mw,_1mE));})));}),_1mW=function(_1mX,_1mY){return E(_1mX);},_1mZ=function(_1n0){var _1n1=new T(function(){return E(E(_1n0).b);});return new T3(0,_1n1,_1n1,_2L);},_1n2=function(_1n3){return E(E(_1n3).e);},_1n4=function(_1n5){var _1n6=new T(function(){return B(A2(_1n2,_1n5,_1mZ));}),_1n7=new T(function(){return _1mK(_1n5);}),_1n8=new T(function(){return _2T(new T(function(){return _2P(_1n7);}));}),_1n9=function(_1na){var _1nb=new T(function(){return B(A3(_2R,_1n8,_1mW,_1na));}),_1nc=function(_1nd){var _1ne=new T(function(){return B(A2(_1n2,_1n5,function(_1nf){return E(new T3(0,0,_1nd,_2L));}));});return C > 19 ? new F(function(){return A3(_s6,_1n8,_1nb,_1ne);}) : (++C,A3(_s6,_1n8,_1nb,_1ne));};return C > 19 ? new F(function(){return A3(_2X,_1n7,_1n6,_1nc);}) : (++C,A3(_2X,_1n7,_1n6,_1nc));};return _1n9;},_1ng=function(_1nh){return E(E(_1nh).a);},_1ni=function(_1nj){return 0;},_1nk=function(_1nl){return E(E(_1nl).f);},_1nm=function(_1nn,_1no,_1np,_1nq){var _1nr=new T(function(){var _1ns=new T(function(){return _1lh(_1np);}),_1nt=function(_1nu){return (!B(A3(_bX,_1no,_1nq,new T(function(){return B(A2(_1lE,_1ns,_1nu));}))))?(!B(A2(_1ng,_1ns,_1nu)))?E(new T1(1,false)):E(new T1(0,new T2(1,_1nq,__Z))):E(new T1(1,true));};return B(A3(_1nk,_1nn,_1np,_1nt));});return C > 19 ? new F(function(){return A3(_2R,_2T(_2P(_1mK(_1nn))),_1ni,_1nr);}) : (++C,A3(_2R,_2T(_2P(_1mK(_1nn))),_1ni,_1nr));},_1nv=new T(function(){return B(A1(_1n4(_1mn),new T(function(){return B(_1nm(_1mn,_8p,_1mw,10));})));}),_1nw=function(_1nx){var _1ny=E(_1nx);return (_1ny._==0)?__Z:new T2(1,_1ny.a,new T(function(){return _1nw(_1ny.b);}));},_1nz=new T(function(){return unCStr("&gt;");}),_1nA=new T(function(){return unCStr("&lt;");}),_1nB=new T(function(){return unCStr("&amp;");}),_1nC=function(_1nD){var _1nE=E(_1nD);return (_1nE._==0)?__Z:new T2(1,new T(function(){var _1nF=E(_1nE.a);switch(_1nF){case 38:return E(_1nB);break;case 60:return E(_1nA);break;case 62:return E(_1nz);break;default:return new T2(1,_1nF,__Z);}}),new T(function(){return _1nC(_1nE.b);}));},_1nG=function(_1nH){return E(E(_1nH).f);},_1nI=function(_1nJ,_1nK){return C > 19 ? new F(function(){return A2(_IW,_1nJ,new T(function(){return B(_2B(_zx,_1nC(B(A2(_1nG,_1nJ,_1nK)))));}));}) : (++C,A2(_IW,_1nJ,new T(function(){return B(_2B(_zx,_1nC(B(A2(_1nG,_1nJ,_1nK)))));})));},_1nL=function(_1nM,_1nN){return E(_1nM);},_1nO=function(_1nP,_1nQ){return C > 19 ? new F(function(){return A1(_1nQ,new T3(0,0,new T(function(){return E(E(_1nP).b);}),_2L));}) : (++C,A1(_1nQ,new T3(0,0,new T(function(){return E(E(_1nP).b);}),_2L)));},_1nR=function(_1nS){return E(_1nS);},_1nT=function(_1nU){var _1nV=E(_1nU);if(!_1nV._){return __Z;}else{var _1nW=function(_1nX){var _1nY=new T(function(){return B(A1(_1nV.a,_1nX));}),_1nZ=function(_1o0){var _1o1=function(_1o2){return C > 19 ? new F(function(){return A1(_1o0,new T3(0,_1nR,new T(function(){return E(E(_1o2).b);}),new T(function(){return E(E(_1o2).c);})));}) : (++C,A1(_1o0,new T3(0,_1nR,new T(function(){return E(E(_1o2).b);}),new T(function(){return E(E(_1o2).c);}))));};return C > 19 ? new F(function(){return A1(_1nY,_1o1);}) : (++C,A1(_1nY,_1o1));};return _1nZ;};return new T2(1,function(_1o3){return _3f(_1jt,_1nW,_1o3);},new T(function(){return _1nT(_1nV.b);}));}},_1o4=function(_1o5,_1o6,_1o7){var _1o8=new T(function(){return B(A3(_2R,_2T(_1o5),_1o7,_1o6));});return function(_3v){return C > 19 ? new F(function(){return _2Z(_2M,_1jt,_1o8,_3v);}) : (++C,_2Z(_2M,_1jt,_1o8,_3v));};},_1o9=function(_1oa){return new T3(0,_1oa,_1kF,function(_lk,_ll){return _1o4(_1oa,_lk,_ll);});},_1ob=new T(function(){return _1o9(new T(function(){var _1oc=_1kI,_1od=new T(function(){var _1oe=_1kM;return new T2(0,_1oe,_1kW);});return new T2(0,_1oc,_1od);}));}),_1of=function(_1og,_1oh,_1oi){return E(_1oi);},_1oj=new T(function(){var _1ok=_1jB;return new T2(0,_1ok,_1of);}),_1ol=function(_1om,_1on){var _1oo=new T(function(){return _kx(_1on);});return function(_1op,_1oq){return C > 19 ? new F(function(){return _1kb(_1oo,_1op,_1oq);}) : (++C,_1kb(_1oo,_1op,_1oq));};},_1or=function(_1os){var _1ot=new T(function(){return _kx(_1os);});return function(_1ou,_1ov){var _1ow=E(_1ov);return C > 19 ? new F(function(){return _1kl(_2M,_1ot,_1ou,_1ow.a,_1ow.b);}) : (++C,_1kl(_2M,_1ot,_1ou,_1ow.a,_1ow.b));};},_1ox=function(_1oy,_1oz){return new T3(0,_1oy,new T(function(){return _1or(_1oz);}),new T(function(){return _1ol(_1oy,_1oz);}));},_1oA=function(_1oB){return new T1(0,_1oB);},_1oC=function(_1oB){return new T1(1,_1oB);},_1oD=function(_1oE,_1oF,_1oG,_1oH,_1oI){var _1oJ=new T(function(){return _2P(_1oE);}),_1oK=new T(function(){return B(A1(_1oF,_2L));}),_1oL=new T(function(){return _2V(_1oJ);}),_1oM=function(_1oN){var _1oO=E(_1oN);if(!_1oO._){return C > 19 ? new F(function(){return A2(_1oK,_1oH,new T(function(){return B(A1(_1oL,_1oO.a));}));}) : (++C,A2(_1oK,_1oH,new T(function(){return B(A1(_1oL,_1oO.a));})));}else{return C > 19 ? new F(function(){return A1(_1oL,_1oO.a);}) : (++C,A1(_1oL,_1oO.a));}},_1oP=new T(function(){var _1oQ=new T(function(){return _2R(new T(function(){return _2T(_1oJ);}));}),_1oR=function(_1oS,_1oT){var _1oU=new T(function(){return B(A2(_1oH,_1oS,new T(function(){return B(A2(_1oQ,_1jy,_1oT));})));});return C > 19 ? new F(function(){return A2(_1oQ,_1oC,_1oU);}) : (++C,A2(_1oQ,_1oC,_1oU));};return B(A2(_1oG,_1oR,new T(function(){return B(A2(_1oQ,_1oA,_1oI));})));});return C > 19 ? new F(function(){return A3(_2X,_1oE,_1oP,_1oM);}) : (++C,A3(_2X,_1oE,_1oP,_1oM));},_1oV=function(_1oW,_1oX,_1oY,_1oZ,_1p0){var _1p1=function(_1p2,_1p3,_1p4){var _1p5=function(_1p6){return C > 19 ? new F(function(){return A1(_1p3,_1p4);}) : (++C,A1(_1p3,_1p4));},_1p7=new T(function(){return B(A1(_1p2,_1p4));});return function(_1p8,_1p9){return C > 19 ? new F(function(){return _1oD(_1p0,_1p5,_1p7,_1p8,_1p9);}) : (++C,_1oD(_1p0,_1p5,_1p7,_1p8,_1p9));};};return {_:0,a:_1oW,b:_1oX,c:_1oY,d:_1oZ,e:_1jN,f:function(_1pa,_1pb){return C > 19 ? new F(function(){return _1lI(_1oW,_1oY,_1pa,_1pb);}) : (++C,_1lI(_1oW,_1oY,_1pa,_1pb));},g:_1of,h:_1p1,i:_1jB};},_1pc=function(_1pd,_1pe,_1pf){var _1pg=new T(function(){var _1ph=E(_1pf);return E(_8p);}),_1pi=new T(function(){return _2P(_1pd);}),_1pj=new T(function(){return _2V(_1pi);}),_1pk=new T(function(){return _2R(new T(function(){return _2T(_1pi);}));}),_1pl=new T(function(){return _nx(new T(function(){return _mN(function(_lk,_ll){return C > 19 ? new F(function(){return _nT(_1pj,_lk,_ll);}) : (++C,_nT(_1pj,_lk,_ll));},new T(function(){return _nC(function(_lk,_ll){return _mY(_1pk,_lk,_ll);},_1pd);}),_1pd);}),_1pd);}),_1pm=new T(function(){return _1oV(new T(function(){return _1ox(_1pl,_1pd);}),_1oj,_1ob,_1pl,_1pd);}),_1pn=function(_1po){var _1pp=E(_1po);return (_1pp._==0)?__Z:new T2(1,new T(function(){return B(_1nm(_1pm,_1pg,_1pe,_1pp.a));}),new T(function(){return _1pn(_1pp.b);}));},_1pq=function(_1pr){var _1ps=new T(function(){var _1pt=E(_1pf);return B(A3(_2B,_6h,_1nT(_1pn(_1pr)),_1nO));}),_1pu=function(_1pv){var _1pw=new T(function(){return B(A1(_1ps,_1pv));}),_1px=function(_1py){var _1pz=function(_1pA){return C > 19 ? new F(function(){return A1(_1py,new T3(0,_2L,new T(function(){return E(E(_1pA).b);}),new T(function(){return E(E(_1pA).c);})));}) : (++C,A1(_1py,new T3(0,_2L,new T(function(){return E(E(_1pA).b);}),new T(function(){return E(E(_1pA).c);}))));};return C > 19 ? new F(function(){return A1(_1pw,_1pz);}) : (++C,A1(_1pw,_1pz));};return _1px;};return _1pu;};return _1pq;},_1pB=new T(function(){return _1pc(_4S,_1mw,_);}),_1pC=new T(function(){return B(A1(_1pB,new T(function(){return unCStr("{{");})));}),_1pD=function(_1pE){var _1pF=new T(function(){return B(A1(_1pC,_1pE));}),_1pG=function(_1pH){var _1pI=function(_1pJ){return C > 19 ? new F(function(){return A1(_1pH,new T3(0,_1nL,new T(function(){return E(E(_1pJ).b);}),new T(function(){return E(E(_1pJ).c);})));}) : (++C,A1(_1pH,new T3(0,_1nL,new T(function(){return E(E(_1pJ).b);}),new T(function(){return E(E(_1pJ).c);}))));};return C > 19 ? new F(function(){return A1(_1pF,_1pI);}) : (++C,A1(_1pF,_1pI));};return _1pG;},_1pK=function(_1pL){return __Z;},_1pM=function(_1pN){return E(_1pN);},_1pO=new T2(0,true,__Z),_1pP=new T(function(){return unCStr("span");}),_1pQ=new T(function(){return unCStr("</code>");}),_1pR=new T(function(){return unCStr("<code class=\"capricon\">");}),_1pS=new T(function(){return unCStr("hidestache");}),_1pT=new T(function(){return unCStr(":");}),_1pU=new T(function(){return unCStr(":\n");}),_1pV=new T(function(){return unCStr("paragraph");}),_1pW=new T(function(){return unCStr("div");}),_1pX=new T(function(){return unCStr("</div>");}),_1pY=new T(function(){return unCStr("<div class=\"user-input\"><input type=\"text\" class=\"capricon-input\" /><button class=\"capricon-submit\">Run</button><pre class=\"capricon-output\"></pre></div>");}),_1pZ=new T(function(){return unCStr("</pre>");}),_1q0=new T(function(){return unCStr("\n");}),_1q1=new T(function(){return unCStr("<div class=\"capricon-steps\"><pre class=\"capricon capricon-paragraph capricon-context\">");}),_1q2=new T(function(){return unCStr("hideparagraph");}),_1q3=new T(function(){return unCStr("</span></label>");}),_1q4=new T(function(){return unCStr("\"></span><span class=\"capricon-reveal\">");}),_1q5=new T(function(){return unCStr("<label class=\"hide-label\"><input type=\"checkbox\" class=\"capricon-hide\" checked=\"checked\"/><span class=\"capricon-");}),_1q6=new T(function(){return unCStr(">");}),_1q7=new T(function(){return unCStr(":</");}),_1q8=new T(function(){return unCStr("result\">");}),_1q9=new T(function(){return unCStr(" class=\"capricon-");}),_1qa=new T(function(){return unCStr(":<");}),_1qb=new T(function(){return B(A1(_1pB,new T(function(){return unCStr("}}");})));}),_1qc=new T(function(){return _1pc(_4S,_1mw,_);}),_1qd=new T(function(){return B(A1(_1qc,new T(function(){return unCStr("> ");})));}),_1qe=new T(function(){return B(A1(_1qc,new T(function(){return unCStr("$> ");})));}),_1qf=new T(function(){return B(_1nm(_1mn,_8p,_1mw,10));}),_1qg=function(_1qh){var _1qi=new T(function(){var _1qj=function(_1qk){var _1ql=E(_1qk);return (_1ql._==0)?__Z:new T2(1,new T(function(){return _8m(_1qh,_1ql.a);}),new T(function(){return _1qj(_1ql.b);}));};if(!B(_2B(_Zi,_1qj(new T2(1,123,_1mD))))){return true;}else{return false;}});return new T1(1,_1qi);},_1qm=new T(function(){return B(_1lI(_1kz,_1l3,_1mw,_1qg));}),_1qn=new T(function(){return B(_1nm(_1mn,_8p,_1mw,123));}),_1qo=function(_1qp){var _1qq=new T(function(){return B(A1(_1qn,_1qp));}),_1qr=function(_1qs){var _1qt=function(_1qu){var _1qv=new T(function(){return E(E(_1qu).a);});return C > 19 ? new F(function(){return A1(_1qs,new T3(0,function(_1qw){return E(_1qv);},new T(function(){return E(E(_1qu).b);}),new T(function(){return E(E(_1qu).c);})));}) : (++C,A1(_1qs,new T3(0,function(_1qw){return E(_1qv);},new T(function(){return E(E(_1qu).b);}),new T(function(){return E(E(_1qu).c);}))));};return C > 19 ? new F(function(){return A1(_1qq,_1qt);}) : (++C,A1(_1qq,_1qt));};return _1qr;},_1qx=function(_1qy){var _1qz=new T(function(){var _1qA=function(_1qB){var _1qC=E(_1qB);return (_1qC._==0)?__Z:new T2(1,new T(function(){return _8m(_1qy,_1qC.a);}),new T(function(){return _1qA(_1qC.b);}));};if(!B(_2B(_Zi,_1qA(new T2(1,123,__Z))))){return true;}else{return false;}});return new T1(1,_1qz);},_1qD=new T(function(){return _1n4(_1mn);}),_1qE=new T(function(){return _3f(_1jt,_1qo,new T(function(){return B(A1(_1qD,new T(function(){return B(_1lI(_1kz,_1l3,_1mw,_1qx));})));}));}),_1qF=function(_1qG){var _1qH=new T(function(){return B(A1(_1qm,_1qG));}),_1qI=function(_1qJ,_1qK){var _1qL=function(_1qM,_1qN){var _1qO=new T(function(){return B(A2(_1qJ,_1qM,new T(function(){return _1jy(_1qN);})));});return new T1(1,_1qO);},_1qP=B(A2(_1qH,_1qL,new T1(0,_1qK)));if(!_1qP._){var _1qQ=function(_1qR){return C > 19 ? new F(function(){return A1(_1qJ,new T3(0,123,new T(function(){return E(E(_1qR).b);}),new T(function(){return E(E(_1qR).c);})));}) : (++C,A1(_1qJ,new T3(0,123,new T(function(){return E(E(_1qR).b);}),new T(function(){return E(E(_1qR).c);}))));};return C > 19 ? new F(function(){return A3(_1qE,_1qG,_1qQ,_1qP.a);}) : (++C,A3(_1qE,_1qG,_1qQ,_1qP.a));}else{return E(_1qP.a);}};return _1qI;},_1qS=new T(function(){return B(_1mR(_1mn,_1qF));}),_1qT=function(_1qU){var _1qV=new T(function(){var _1qW=function(_1qX){var _1qY=E(_1qX);return (_1qY._==0)?__Z:new T2(1,new T(function(){return _8m(_1qU,_1qY.a);}),new T(function(){return _1qW(_1qY.b);}));};if(!B(_2B(_Zi,_1qW(new T2(1,125,__Z))))){return true;}else{return false;}});return new T1(1,_1qV);},_1qZ=new T(function(){return B(_1lI(_1kz,_1l3,_1mw,_1qT));}),_1r0=new T(function(){return B(_1nm(_1mn,_8p,_1mw,125));}),_1r1=function(_1r2){var _1r3=new T(function(){return B(A1(_1r0,_1r2));}),_1r4=function(_1r5){var _1r6=function(_1r7){var _1r8=new T(function(){return E(E(_1r7).a);});return C > 19 ? new F(function(){return A1(_1r5,new T3(0,function(_1r9){return E(_1r8);},new T(function(){return E(E(_1r7).b);}),new T(function(){return E(E(_1r7).c);})));}) : (++C,A1(_1r5,new T3(0,function(_1r9){return E(_1r8);},new T(function(){return E(E(_1r7).b);}),new T(function(){return E(E(_1r7).c);}))));};return C > 19 ? new F(function(){return A1(_1r3,_1r6);}) : (++C,A1(_1r3,_1r6));};return _1r4;},_1ra=new T(function(){return _3f(_1jt,_1r1,new T(function(){return B(A1(_1qD,new T(function(){return B(_1lI(_1kz,_1l3,_1mw,_1qT));})));}));}),_1rb=function(_1rc){var _1rd=new T(function(){return B(A1(_1qZ,_1rc));}),_1re=function(_1rf,_1rg){var _1rh=function(_1ri,_1rj){var _1rk=new T(function(){return B(A2(_1rf,_1ri,new T(function(){return _1jy(_1rj);})));});return new T1(1,_1rk);},_1rl=B(A2(_1rd,_1rh,new T1(0,_1rg)));if(!_1rl._){var _1rm=function(_1rn){return C > 19 ? new F(function(){return A1(_1rf,new T3(0,125,new T(function(){return E(E(_1rn).b);}),new T(function(){return E(E(_1rn).c);})));}) : (++C,A1(_1rf,new T3(0,125,new T(function(){return E(E(_1rn).b);}),new T(function(){return E(E(_1rn).c);}))));};return C > 19 ? new F(function(){return A3(_1ra,_1rc,_1rm,_1rl.a);}) : (++C,A3(_1ra,_1rc,_1rm,_1rl.a));}else{return E(_1rl.a);}};return _1re;},_1ro=new T(function(){return B(_1mR(_1mn,_1rb));}),_1rp=new T(function(){return _U6(_nK);}),_1rq=function(_1rr){var _1rs=E(_1rr);return (_1rs._==0)?__Z:new T2(1,new T(function(){return _nO(_1rs.a);}),new T(function(){return _1rq(_1rs.b);}));},_1rt=function(_1ru){var _1rv=E(_1ru);return (_1rv._==0)?__Z:new T2(1,new T(function(){return _3W(_1rv.a);}),new T(function(){return _1rt(_1rv.b);}));},_1rw=function(_1rx,_1ry,_1rz){var _1rA=_2T(_2P(_1mK(_1rx))),_1rB=new T(function(){var _1rC=new T(function(){return B(A3(_s6,_1rA,new T(function(){return B(A3(_2R,_1rA,_s3,_1rz));}),_1ry));});return B(_1mO(_1rx,_1rC));});return C > 19 ? new F(function(){return A3(_s6,_1rA,new T(function(){return B(A3(_2R,_1rA,_Kh,_1ry));}),_1rB);}) : (++C,A3(_s6,_1rA,new T(function(){return B(A3(_2R,_1rA,_Kh,_1ry));}),_1rB));},_1rD=new T(function(){return unCStr("\"");}),_1rE=function(_1rF,_1rG){while(1){var _1rH=(function(_1rI,_1rJ){var _1rK=E(_1rJ);if(!_1rK._){return new T2(0,new T2(1,34,new T(function(){return B(A1(_1rI,_1rD));})),__Z);}else{var _1rL=_1rK.b,_1rM=E(_1rK.a);switch(_1rM){case 34:return new T2(0,new T2(1,34,new T(function(){return B(A1(_1rI,_1rD));})),new T(function(){return _1rN(_1rL);}));case 92:var _1rO=E(_1rL);if(!_1rO._){_1rF=function(_1rP){return C > 19 ? new F(function(){return A1(_1rI,new T2(1,_1rM,_1rP));}) : (++C,A1(_1rI,new T2(1,_1rM,_1rP)));};_1rG=__Z;return __continue;}else{var _1rQ=function(_1rR){return C > 19 ? new F(function(){return A1(_1rI,new T2(1,new T(function(){var _1rS=E(_1rO.a);switch(_1rS){case 110:return 10;break;case 116:return 9;break;default:return _1rS;}}),_1rR));}) : (++C,A1(_1rI,new T2(1,new T(function(){var _1rS=E(_1rO.a);switch(_1rS){case 110:return 10;break;case 116:return 9;break;default:return _1rS;}}),_1rR)));};_1rF=_1rQ;_1rG=_1rO.b;return __continue;}break;default:_1rF=function(_1rT){return C > 19 ? new F(function(){return A1(_1rI,new T2(1,_1rM,_1rT));}) : (++C,A1(_1rI,new T2(1,_1rM,_1rT)));};_1rG=_1rL;return __continue;}}})(_1rF,_1rG);if(_1rH!=__continue){return _1rH;}}},_1rU=new T2(1,32,new T2(1,9,new T2(1,13,_1mD))),_1rV=function(_1rW,_1rX){while(1){var _1rY=(function(_1rZ,_1s0){var _1s1=E(_1s0);if(!_1s1._){return new T2(0,new T(function(){return B(A1(_1rZ,__Z));}),__Z);}else{var _1s2=_1s1.a,_1s3=_1s1.b,_1s4=function(_1s5){var _1s6=E(_1s5);return (_1s6._==0)?__Z:new T2(1,new T(function(){return _8m(_1s2,_1s6.a);}),new T(function(){return _1s4(_1s6.b);}));};if(!B(_2B(_Zi,_1s4(_1rU)))){_1rW=function(_1s7){return C > 19 ? new F(function(){return A1(_1rZ,new T2(1,_1s2,_1s7));}) : (++C,A1(_1rZ,new T2(1,_1s2,_1s7)));};_1rX=_1s3;return __continue;}else{return new T2(0,new T(function(){return B(A1(_1rZ,__Z));}),new T(function(){return _1rN(_1s3);}));}}})(_1rW,_1rX);if(_1rY!=__continue){return _1rY;}}},_1rN=function(_1s8){while(1){var _1s9=(function(_1sa){var _1sb=E(_1sa);if(!_1sb._){return __Z;}else{var _1sc=_1sb.a,_1sd=_1sb.b,_1se=function(_1sf){var _1sg=E(_1sf);return (_1sg._==0)?__Z:new T2(1,new T(function(){return _8m(_1sc,_1sg.a);}),new T(function(){return _1se(_1sg.b);}));};if(!B(_2B(_Zi,_1se(_1rU)))){var _1sh=E(_1sc);if(_1sh==34){var _1si=_1rE(_n,_1sd);return new T2(1,_1si.a,_1si.b);}else{var _1sj=_1rV(function(_1k5){return new T2(1,_1sh,_1k5);},_1sd);return new T2(1,_1sj.a,_1sj.b);}}else{_1s8=_1sd;return __continue;}}})(_1s8);if(_1s9!=__continue){return _1s9;}}},_1sk=function(_1sl,_1sm){var _1sn=new T(function(){return _IW(_1sl);}),_1so=function(_1sp){var _1sq=E(_1sp);return (_1sq._==0)?__Z:new T2(1,new T(function(){return B(A1(_1sn,_1sq.a));}),new T(function(){return _1so(_1sq.b);}));};return _1so(_1rN(B(A2(_1nG,_1sl,_1sm))));},_1sr=function(_1ss){var _1st=new T(function(){return _IW(_1ss);}),_1su=new T(function(){return B(A1(_1st,_1pU));}),_1sv=function(_1sw){var _1sx=E(_1sw);if(!_1sx._){return __Z;}else{var _1sy=_1sx.a,_1sz=function(_1sA){var _1sB=new T(function(){var _1sC=E(_1sA);if(!E(_1sC.a)){return _nK(_1sy,new T(function(){return _nK(new T2(1,_1su,__Z),_1sC.b);},1));}else{return E(_1sy);}});return new T2(0,false,_1sB);};return new T2(1,_1sz,new T(function(){return _1sv(_1sx.b);}));}},_1sD=new T(function(){var _1sE=new T(function(){return _IQ(new T(function(){return _IU(_1ss);}));}),_1sF=new T(function(){return _2x(_1sE);}),_1sG=new T(function(){return B(A1(_1st,_1pT));}),_1sH=new T(function(){return B(A1(_1st,_1q5));}),_1sI=new T(function(){return B(A1(_1st,_1q4));}),_1sJ=new T(function(){return B(A1(_1st,_1q3));}),_1sK=new T(function(){return B(A1(_1st,_1q2));}),_1sL=new T(function(){return B(A1(_1st,_1q1));}),_1sM=new T(function(){return B(A1(_1st,_1q0));}),_1sN=function(_1sO){var _1sP=E(_1sO);if(!_1sP._){return __Z;}else{var _1sQ=_1sP.a,_1sR=function(_1sS){var _1sT=new T(function(){var _1sU=E(_1sS);if(!E(_1sU.a)){return B(A2(_1sF,_1sQ,new T(function(){return B(A2(_1sF,_1sM,_1sU.b));})));}else{return E(_1sQ);}});return new T2(0,false,_1sT);};return new T2(1,_1sR,new T(function(){return _1sN(_1sP.b);}));}},_1sV=new T(function(){var _1sW=new T(function(){return B(A2(_1sF,new T(function(){return B(A1(_1st,_1pY));}),new T(function(){return B(A1(_1st,_1pX));})));});return B(A2(_1sF,new T(function(){return B(A1(_1st,_1pZ));}),_1sW));}),_1sX=new T(function(){return B(A1(_1st,_1pW));}),_1sY=new T(function(){return B(A1(_1st,_1q7));}),_1sZ=new T(function(){return B(A1(_1st,_1q6));}),_1t0=new T(function(){return B(A2(_1sF,_1sY,new T(function(){return B(A2(_1sF,_1sX,_1sZ));})));}),_1t1=new T(function(){return B(A1(_1st,_1qa));}),_1t2=new T(function(){return B(A1(_1st,_1q9));}),_1t3=new T(function(){return B(A1(_1st,_1q8));}),_1t4=new T(function(){var _1t5=new T(function(){var _1t6=new T(function(){var _1t7=new T(function(){return B(A2(_1sF,new T(function(){return B(A1(_1st,_1pV));}),_1t3));});return B(A2(_1sF,_1t2,_1t7));});return B(A2(_1sF,_1sX,_1t6));});return B(A2(_1sF,_1t1,_1t5));}),_1t8=function(_1t9){var _1ta=new T(function(){return B(A1(_1mV,_1t9));}),_1tb=new T(function(){return E(E(_1t9).b);}),_1tc=function(_1td,_1te){var _1tf=function(_1tg,_1th){var _1ti=new T(function(){var _1tj=new T(function(){return E(E(_1tg).a);});return B(A2(_1td,new T3(0,new T2(0,new T(function(){return B(A1(_1st,_1tj));}),new T(function(){return _Iz(_1st,_1nw(_1rN(_1tj)));})),new T(function(){return E(E(_1tg).b);}),new T(function(){return E(E(_1tg).c);})),new T(function(){return _1jy(_1th);})));});return new T1(1,_1ti);},_1tk=B(A2(_1ta,_1tf,new T1(0,_1te)));if(!_1tk._){return C > 19 ? new F(function(){return A2(_1td,new T3(0,new T2(0,new T(function(){return B(A1(_1st,__Z));}),new T(function(){return _Iz(_1st,_1nw(_1rN(__Z)));})),_1tb,_2L),_1tk.a);}) : (++C,A2(_1td,new T3(0,new T2(0,new T(function(){return B(A1(_1st,__Z));}),new T(function(){return _Iz(_1st,_1nw(_1rN(__Z)));})),_1tb,_2L),_1tk.a));}else{return E(_1tk.a);}};return _1tc;},_1tl=new T(function(){return _2z(_1sE);}),_1tm=function(_1tn){var _1to=new T(function(){var _1tp=new T(function(){var _1tq=function(_1tr){var _1ts=new T(function(){return B(A1(_1tn,_1tr));}),_1tt=function(_1tu){var _1tv=function(_1tw){return C > 19 ? new F(function(){return A1(_1tu,new T3(0,_1pM,new T(function(){return E(E(_1tw).b);}),new T(function(){return E(E(_1tw).c);})));}) : (++C,A1(_1tu,new T3(0,_1pM,new T(function(){return E(E(_1tw).b);}),new T(function(){return E(E(_1tw).c);}))));};return C > 19 ? new F(function(){return A1(_1ts,_1tv);}) : (++C,A1(_1ts,_1tv));};return _1tt;};return _3f(_1jt,_1tq,_1t8);});return B(_1rw(_1mn,_1tp,_1qf));}),_1tx=function(_1ty){var _1tz=new T(function(){return B(A1(_1to,_1ty));}),_1tA=function(_1tB){var _1tC=function(_1tD){var _1tE=new T(function(){return E(E(_1tD).a);}),_1tF=new T(function(){var _1tG=new T(function(){var _1tH=new T(function(){var _1tI=new T(function(){var _1tJ=new T(function(){var _1tK=new T(function(){var _1tL=new T(function(){var _1tM=new T(function(){var _1tN=new T(function(){return B(_2B(_zx,_1nC(B(A2(_1nG,_1ss,new T(function(){return E(B(A3(_2B,_6h,_1sN(_1rq(_1tE)),new T2(0,true,_1tl))).b);}))))));});return B(A2(_IW,_1ss,_1tN));});return B(A2(_1sF,_1tM,_1sV));});return B(A2(_1sF,_1sL,_1tL));});return B(A2(_1sF,_1tK,_1sJ));});return B(A2(_1sF,_1sI,_1tJ));});return B(A2(_1sF,_1sK,_1tI));});return B(A2(_1sF,_1sH,_1tH));});return B(A2(_1sF,_1sG,_1tG));});return C > 19 ? new F(function(){return A1(_1tB,new T3(0,new T2(1,_1tF,new T2(1,_1t4,new T(function(){return _nK(B(_2B(_1rp,_1rt(_1tE))),new T2(1,_1t0,__Z));}))),new T(function(){return E(E(_1tD).b);}),new T(function(){return E(E(_1tD).c);})));}) : (++C,A1(_1tB,new T3(0,new T2(1,_1tF,new T2(1,_1t4,new T(function(){return _nK(B(_2B(_1rp,_1rt(_1tE))),new T2(1,_1t0,__Z));}))),new T(function(){return E(E(_1tD).b);}),new T(function(){return E(E(_1tD).c);}))));};return C > 19 ? new F(function(){return A1(_1tz,_1tC);}) : (++C,A1(_1tz,_1tC));};return _1tA;};return _1tx;},_1tO=new T(function(){return _1tm(_1qd);}),_1tP=new T(function(){return _1tm(_1qe);}),_1tQ=new T(function(){return B(A1(_1sF,_1sG));}),_1tR=new T(function(){return B(A1(_1st,_1pQ));}),_1tS=new T(function(){return B(A1(_1st,_1pR));}),_1tT=new T(function(){return B(A1(_1st,_1pS));}),_1tU=function(_1tV){var _1tW=E(_1tV);if(!_1tW._){return __Z;}else{var _1tX=new T(function(){var _1tY=E(_1tW.a);if(!_1tY._){return new T2(1,new T(function(){return B(A1(_1tQ,_1tY.a));}),__Z);}else{var _1tZ=E(_1tY.a),_1u0=new T(function(){var _1u1=new T(function(){var _1u2=new T(function(){var _1u3=new T(function(){var _1u4=new T(function(){var _1u5=new T(function(){var _1u6=new T(function(){return B(A2(_1sF,new T(function(){return B(_1nI(_1ss,_1tZ.a));}),_1tR));});return B(A2(_1sF,_1tS,_1u6));});return B(A2(_1sF,_1u5,_1sJ));});return B(A2(_1sF,_1sI,_1u4));});return B(A2(_1sF,_1tT,_1u3));});return B(A2(_1sF,_1sH,_1u2));});return B(A2(_1sF,_1sG,_1u1));});return _nK(_1tZ.b,new T2(1,_1u0,__Z));}});return new T2(1,_1tX,new T(function(){return _1tU(_1tW.b);}));}},_1u7=new T(function(){var _1u8=new T(function(){var _1u9=new T(function(){var _1ua=new T(function(){var _1ub=new T(function(){return B(A1(_1st,_1pP));}),_1uc=new T(function(){return B(A2(_1sF,_1sY,new T(function(){return B(A2(_1sF,_1ub,_1sZ));})));}),_1ud=new T(function(){var _1ue=new T(function(){var _1uf=new T(function(){var _1ug=new T(function(){return B(A2(_1sF,new T(function(){return B(A1(_1st,__Z));}),_1t3));});return B(A2(_1sF,_1t2,_1ug));});return B(A2(_1sF,_1ub,_1uf));});return B(A2(_1sF,_1t1,_1ue));}),_1uh=function(_1ui){var _1uj=new T(function(){return B(A1(_1ro,_1ui));}),_1uk=function(_1ul){var _1um=function(_1un){var _1uo=new T(function(){return E(E(_1un).a);}),_1up=new T(function(){return _nK(_1sk(_1ss,new T(function(){return B(A1(_1st,_1uo));})),new T2(1,_1uc,__Z));});return C > 19 ? new F(function(){return A1(_1ul,new T3(0,new T2(0,new T(function(){return B(A1(_1st,_1uo));}),new T2(1,_1ud,_1up)),new T(function(){return E(E(_1un).b);}),new T(function(){return E(E(_1un).c);})));}) : (++C,A1(_1ul,new T3(0,new T2(0,new T(function(){return B(A1(_1st,_1uo));}),new T2(1,_1ud,_1up)),new T(function(){return E(E(_1un).b);}),new T(function(){return E(E(_1un).c);}))));};return C > 19 ? new F(function(){return A1(_1uj,_1um);}) : (++C,A1(_1uj,_1um));};return _1uk;};return _3f(_1jt,_1pD,_1uh);});return _3f(_1jt,_1ua,_1qb);}),_1uq=function(_1ur){var _1us=new T(function(){return B(A1(_1qS,_1ur));}),_1ut=function(_1uu,_1uv){var _1uw=function(_1ux){var _1uy=new T(function(){return B(A1(_1st,new T(function(){return E(E(_1ux).a);})));}),_1uz=new T(function(){return E(E(_1ux).b);}),_1uA=new T(function(){return E(E(_1ux).c);}),_1uB=function(_1uC){var _1uD=new T(function(){return B(A2(_1uu,new T3(0,new T1(0,_1uy),_1uz,_1uA),new T(function(){return _1jy(_1uC);})));});return new T1(1,_1uD);};return _1uB;},_1uE=B(A2(_1us,_1uw,new T1(0,_1uv)));if(!_1uE._){var _1uF=function(_1uG){return C > 19 ? new F(function(){return A1(_1uu,new T3(0,new T1(1,new T(function(){return E(E(_1uG).a);})),new T(function(){return E(E(_1uG).b);}),new T(function(){return E(E(_1uG).c);})));}) : (++C,A1(_1uu,new T3(0,new T1(1,new T(function(){return E(E(_1uG).a);})),new T(function(){return E(E(_1uG).b);}),new T(function(){return E(E(_1uG).c);}))));};return C > 19 ? new F(function(){return A3(_1u9,_1ur,_1uF,_1uE.a);}) : (++C,A3(_1u9,_1ur,_1uF,_1uE.a));}else{return E(_1uE.a);}};return _1ut;};return B(_1mR(_1mn,_1uq));}),_1uH=function(_1uI){var _1uJ=new T(function(){return B(A1(_1u8,_1uI));}),_1uK=new T(function(){return E(E(_1uI).b);}),_1uL=function(_1uM,_1uN){var _1uO=function(_1uP,_1uQ){var _1uR=new T(function(){var _1uS=new T(function(){return E(E(_1uP).a);});return B(A2(_1uM,new T3(0,function(_1uT){return E(_1uS);},new T(function(){return E(E(_1uP).b);}),new T(function(){return E(E(_1uP).c);})),new T(function(){return _1jy(_1uQ);})));});return new T1(1,_1uR);},_1uU=B(A2(_1uJ,_1uO,new T1(0,_1uN)));if(!_1uU._){return C > 19 ? new F(function(){return A2(_1uM,new T3(0,_1pK,_1uK,_2L),_1uU.a);}) : (++C,A2(_1uM,new T3(0,_1pK,_1uK,_2L),_1uU.a));}else{return E(_1uU.a);}};return _1uL;};return _3f(_1jt,_1uH,_1nv);}),_1uV=function(_1uW){var _1uX=new T(function(){return B(A1(_1tO,_1uW));}),_1uY=function(_1uZ,_1v0){var _1v1=function(_1v2,_1v3){var _1v4=new T(function(){return B(A2(_1uZ,_1v2,new T(function(){return _1jy(_1v3);})));});return new T1(1,_1v4);},_1v5=B(A2(_1uX,_1v1,new T1(0,_1v0)));if(!_1v5._){var _1v6=function(_1v7,_1v8){var _1v9=new T(function(){return B(A2(_1uZ,_1v7,new T(function(){return _1jy(_1v8);})));});return new T1(1,_1v9);},_1va=B(A3(_1tP,_1uW,_1v6,new T1(0,_1v5.a)));if(!_1va._){var _1vb=function(_1vc){return C > 19 ? new F(function(){return A1(_1uZ,new T3(0,new T(function(){return B(_2B(_1rp,_1tU(E(_1vc).a)));}),new T(function(){return E(E(_1vc).b);}),new T(function(){return E(E(_1vc).c);})));}) : (++C,A1(_1uZ,new T3(0,new T(function(){return B(_2B(_1rp,_1tU(E(_1vc).a)));}),new T(function(){return E(E(_1vc).b);}),new T(function(){return E(E(_1vc).c);}))));};return C > 19 ? new F(function(){return A3(_1u7,_1uW,_1vb,_1va.a);}) : (++C,A3(_1u7,_1uW,_1vb,_1va.a));}else{return E(_1va.a);}}else{return E(_1v5.a);}};return _1uY;};return B(_1rw(_1mn,_1uV,_1qf));}),_1vd=function(_1ve){var _1vf=new T(function(){return B(A1(_1sD,_1ve));}),_1vg=new T(function(){return E(E(_1ve).b);}),_1vh=function(_1vi,_1vj){var _1vk=function(_1vl,_1vm){var _1vn=new T(function(){return B(A2(_1vi,new T3(0,new T(function(){return E(B(A3(_2B,_6h,_1sv(E(_1vl).a),_1pO)).b);}),new T(function(){return E(E(_1vl).b);}),new T(function(){return E(E(_1vl).c);})),new T(function(){return _1jy(_1vm);})));});return new T1(1,_1vn);},_1vo=B(A2(_1vf,_1vk,new T1(0,_1vj)));if(!_1vo._){return C > 19 ? new F(function(){return A2(_1vi,new T3(0,new T(function(){return E(B(A3(_2B,_6h,_1sv(__Z),_1pO)).b);}),_1vg,_2L),_1vo.a);}) : (++C,A2(_1vi,new T3(0,new T(function(){return E(B(A3(_2B,_6h,_1sv(__Z),_1pO)).b);}),_1vg,_2L),_1vo.a));}else{return E(_1vo.a);}};return _1vh;};return _1vd;},_1vp=new T1(6,new T0(1)),_1vq=function(_1vr,_1vs){return new T3(0,_1vr,new T(function(){return E(E(_1vs).b);}),_2L);},_1vt=function(_1vu,_1vv,_1vw){var _1vx=new T(function(){return B(A1(_1vv,_1vw));}),_1vy=new T(function(){return B(A1(_1vu,new T(function(){return E(E(_1vx).a);})));});return new T3(0,_1vy,new T(function(){return E(E(_1vx).b);}),new T(function(){return E(E(_1vx).c);}));},_1vz=new T(function(){return _no(new T(function(){return _nx(new T(function(){return _mN(_1vq,new T(function(){return _nC(_1vt,_4S);}),_4S);}),_4S);}),_4S);}),_1vA=new T(function(){return B(_5m(_1vz,_5C,function(_1vB){return new T2(0,_n,_1vB);}));}),_1vC=function(_1vD,_){return __Z;},_1vE=function(_1vF,_1vG){var _1vH=E(_1vF);if(!_1vH._){return __Z;}else{return _Jn(_1vH.a,_1vG);}},_1vI=new T3(0,new T2(0,_mg,new T2(0,_Jn,_1vE)),function(_1vJ){var _1vK=E(_1vJ);return (_1vK._==0)?__Z:E(_1vK.a);},function(_1vL,_1vM){var _1vN=E(_1vL);if(!_1vN._){return __Z;}else{return C > 19 ? new F(function(){return A1(_1vM,_1vN.a);}) : (++C,A1(_1vM,_1vN.a));}}),_1vO=new T2(0,_Jn,function(_1vP,_1vQ){var _1vR=E(_1vQ);if(!_1vR._){return C > 19 ? new F(function(){return A2(_2V,_1vP,__Z);}) : (++C,A2(_2V,_1vP,__Z));}else{return C > 19 ? new F(function(){return A3(_2R,_2T(_1vP),_mg,_1vR.a);}) : (++C,A3(_2R,_2T(_1vP),_mg,_1vR.a));}}),_1vS=function(_1vT,_1vU,_1vV,_1vW){return new T2(0,_1vT,_1vU);},_1vX=function(_1vY){return E(_1vY);},_1vZ=function(_1w0){return E(E(_1w0).b);},_1w1=function(_1w2){return E(E(_1w2).b);},_1w3=function(_1w4,_1w5,_1w6,_1w7){var _1w8=new T(function(){return _2P(_1w6);}),_1w9=new T(function(){return _2R(new T(function(){return _2T(_1w8);}));}),_1wa=new T(function(){return B(A1(_1w9,new T(function(){return _1vZ(_1w7);})));}),_1wb=new T(function(){return _1vZ(_1w6);}),_1wc=new T(function(){return B(A1(_1w9,new T(function(){return B(A2(_1w1,_1w5,_1w8));})));}),_1wd=new T(function(){return B(A2(_2R,_2T(_1w4),_1vX));}),_1we=function(_1wf){var _1wg=new T(function(){var _1wh=new T(function(){return B(A1(_1wc,new T(function(){return B(A1(_1wd,_1wf));})));});return B(A1(_1wb,_1wh));});return C > 19 ? new F(function(){return A1(_1wa,_1wg);}) : (++C,A1(_1wa,_1wg));};return _1we;},_1wi=function(_1wj,_1wk,_1wl,_1wm,_1wn){var _1wo=new T(function(){return B(A3(_2R,_1wk,new T(function(){return _s6(_1wl);}),_1wm));});return C > 19 ? new F(function(){return A3(_s6,_1wk,_1wo,_1wn);}) : (++C,A3(_s6,_1wk,_1wo,_1wn));},_1wp=function(_1wq,_1wr,_1ws){return new T2(0,_1wq,function(_1wt,_1wu){return C > 19 ? new F(function(){return _1wi(_1wq,_1wr,_1ws,_1wt,_1wu);}) : (++C,_1wi(_1wq,_1wr,_1ws,_1wt,_1wu));});},_1wv=function(_1ww){return E(E(_1ww).a);},_1wx=function(_1wy,_1wz,_1wA){var _1wB=new T(function(){return _2P(_1wy);}),_1wC=new T(function(){return _2P(_1wz);}),_1wD=new T(function(){return _2T(_1wC);}),_1wE=new T(function(){var _1wF=new T(function(){var _1wG=new T(function(){return _2R(_1wD);}),_1wH=new T(function(){return _1wv(_1wA);}),_1wI=function(_1wJ,_1wK){return C > 19 ? new F(function(){return A2(_1wG,new T(function(){return B(A1(_1wH,_1wJ));}),_1wK);}) : (++C,A2(_1wG,new T(function(){return B(A1(_1wH,_1wJ));}),_1wK));};return _1wp(_1wI,_1wD,new T(function(){return _2T(_1wB);}));}),_1wL=new T(function(){return _2V(_1wC);}),_1wM=new T(function(){return _2V(_1wB);}),_1wN=function(_1wO){return C > 19 ? new F(function(){return A1(_1wL,new T(function(){return B(A1(_1wM,_1wO));}));}) : (++C,A1(_1wL,new T(function(){return B(A1(_1wM,_1wO));})));};return _1vS(_1wN,_1wF,_1wC,_1wB);},1);return _1w3(_1wE,_1wA,_1wz,_1wy);},_1wP=new T2(0,_nK,__Z),_1wQ=new T(function(){return _107(_Zh,_1wP,_1wP);}),_1wR=function(_1wS){var _1wT=E(_1wS);return (_1wT==0)?_1wT:_1wT+1|0;},_1wU=function(_1wV){return E(_1wV)+2|0;},_1wW=function(_1wX){return E(_1wX)+1|0;},_1wY=new T(function(){return _Pf(_C6,1,_4P);}),_1wZ=function(_1x0){var _1x1=E(_1x0);return (_1x1._==0)?__Z:new T2(1,function(_1x2){var _1x3=E(_1x1.a);return new T4(0,1,_1x3.a,_1x3.b,_1x2);},new T(function(){return _1wZ(_1x1.b);}));},_1x4=function(_1x5){var _1x6=E(_1x5);return (_1x6._==0)?__Z:new T2(1,new T(function(){return _PB(_1wW,_1x6.a);}),new T(function(){return _1x4(_1x6.b);}));},_1x7=function(_1x8){var _1x9=E(_1x8);return (_1x9._==0)?__Z:new T2(1,function(_1xa){var _1xb=E(_1x9.a);return new T4(0,0,_1xb.a,_1xb.b,_1xa);},new T(function(){return _1x7(_1x9.b);}));},_1xc=function(_1xd){var _1xe=E(_1xd);return (_1xe._==0)?__Z:new T2(1,function(_1xf){var _1xg=E(_1xe.a);return new T4(0,1,_1xg.a,_1xg.b,_1xf);},new T(function(){return _1xc(_1xe.b);}));},_1xh=function(_1xi){var _1xj=E(_1xi);return (_1xj._==0)?__Z:new T2(1,new T1(1,new T2(0,new T1(0,_1xj.a),__Z)),new T(function(){return _1xh(_1xj.b);}));},_1xk=function(_1xl){var _1xm=E(_1xl);return (_1xm._==0)?(E(_1xm.a)==0)?__Z:new T2(1,new T2(0,_1xm.b,_1xm.c),new T(function(){return _1xk(_1xm.d);})):__Z;},_1xn=function(_1xo){var _1xp=new T(function(){return _Ks(_1xo);}),_1xq=new T(function(){return _1wx(_1vI,_1xp,_1vO);}),_1xr=new T(function(){return _2P(_1xp);}),_1xs=new T(function(){return B(A2(_2V,_1xr,__Z));}),_1xt=new T(function(){return _2V(_1xr);}),_1xu=new T(function(){return _2R(new T(function(){return _2T(_1xr);}));}),_1xv=function(_1xw){var _1xx=_PB(_1wW,_1xw),_1xy=new T(function(){return _1xk(_1xx);}),_1xz=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_1xy)),0));}),_1xA=new T(function(){return _1xh(_ss(_Pv(0,E(_1xz)-1|0),__Z));}),_1xB=function(_1xC){var _1xD=E(_1xC);return (_1xD._==0)?__Z:new T2(1,new T1(1,new T2(0,new T1(0,new T(function(){return _Kp(_1xD.a,_1xz);})),__Z)),new T(function(){return _1xB(_1xD.b);}));},_1xE=function(_1xF,_1xG){var _1xH=E(_1xG);switch(_1xH._){case 0:var _1xI=_1xH.b,_1xJ=_1xH.c;if(!E(_1xH.a)){return E(_1xs);}else{var _1xK=new T(function(){var _1xL=new T(function(){var _1xM=new T(function(){return B(_1xE(new T(function(){return E(_1xF)+1|0;}),_1xH.d));});return B(A3(_Su,_1xo,function(_He){return new T2(1,_1xJ,_He);},_1xM));}),_1xN=new T(function(){var _1xO=new T1(0,new T(function(){return (E(_1xz)-E(_1xF)|0)-1|0;})),_1xP=new T(function(){return E(_1xz)-E(_1xF)|0;}),_1xQ=function(_1xR,_1xS,_1xT){var _1xU=E(_1xT);switch(_1xU._){case 0:var _1xV=_1xU.b,_1xW=_1xU.c,_1xX=_1xU.d;if(!E(_1xU.a)){return E(_1xs);}else{var _1xY=function(_1xZ){var _1y0=new T(function(){var _1y1=new T(function(){return B(_1xQ(new T(function(){return E(_1xR)+1|0;}),new T(function(){return _Rs(_1wW,_1xS);}),_1xX));});return B(A3(_Su,_1xo,function(_He){return new T2(1,_1xW,_He);},_1y1));});return C > 19 ? new F(function(){return A2(_1xu,function(_1y2){var _1y3=E(_1y2);return (_1y3._==0)?__Z:new T1(1,new T4(0,1,_1xV,_1xW,_1y3.a));},_1y0);}) : (++C,A2(_1xu,function(_1y2){var _1y3=E(_1y2);return (_1y3._==0)?__Z:new T1(1,new T4(0,1,_1xV,_1xW,_1y3.a));},_1y0));},_1y4=E(_1xW);if(_1y4._==1){var _1y5=E(_1y4.a),_1y6=E(_1y5.a);if(!_1y6._){var _1y7=E(_1xR),_1y8=E(_1y6.a);if(_1y7>_1y8){return C > 19 ? new F(function(){return _1xY(_);}) : (++C,_1xY(_));}else{var _1y9=E(_1xF);if(_1y8>=(_1y9+_1y7|0)){return C > 19 ? new F(function(){return _1xY(_);}) : (++C,_1xY(_));}else{var _1ya=new T(function(){var _1yb=new T(function(){return _nK(_1x4(_1y5.b),new T2(1,new T1(1,_U5),__Z));}),_1yc=new T(function(){var _1yd=_1y9+_1y7|0,_1ye=function(_1yf){var _1yg=E(_1yf);if(!_1yg._){return __Z;}else{var _1yh=function(_1yi){var _1yj=E(_1yi),_1yk=E(_1yg.a);return (_1yj>=_1yk)?_1yk+((_1yj-_1yk|0)+_1yd|0)|0:_1yj;},_1yl=function(_1ym){return new T2(0,new T(function(){return E(E(_1ym).a);}),new T(function(){return _PB(_1yh,E(_1ym).b);}));};return new T2(1,_1yl,new T(function(){return _1ye(_1yg.b);}));}},_1yn=new T(function(){return _PB(function(_1yo){var _1yp=E(_1yo);return (_1y7>_1yp)?_1yp+E(_1xz)|0:(_1yp>=_1yd)?_1yp+E(_1xz)|0:(_1yp-_1y7|0)+E(_1xP)|0;},_1y4);});return B(A3(_2B,_6h,_1wZ(_IF(_1ye(_PA),_1xy)),_1yn));}),_1yq=new T(function(){var _1yr=new T(function(){var _1ys=new T(function(){return B(A2(_1wY,_RW,new T(function(){return _Rs(_1wU,_1xS);})));});return B(_1xQ(_1y7+2|0,_1ys,_PB(_1wR,_1xX)));});return B(A3(_Su,_1xo,function(_1yt){return new T2(1,_1y4,new T2(1,_2L,_1yt));},_1yr));}),_1yu=function(_1yv){var _1yw=E(_1yv);return (_1yw._==0)?__Z:new T1(1,new T(function(){return B(A1(_1xt,new T1(1,new T4(0,1,_1xV,_1yc,new T4(0,1,_1xV,new T1(1,new T2(0,new T1(0,_1y8+1|0),_1yb)),_1yw.a)))));}));};return B(A2(_1xu,_1yu,_1yq));});return C > 19 ? new F(function(){return A1(_1xq,_1ya);}) : (++C,A1(_1xq,_1ya));}}}else{return C > 19 ? new F(function(){return _1xY(_);}) : (++C,_1xY(_));}}else{return C > 19 ? new F(function(){return _1xY(_);}) : (++C,_1xY(_));}}break;case 1:var _1yx=E(_1xU.a),_1yy=E(_1yx.a);if(!_1yy._){var _1yz=E(_1xR),_1yA=E(_1yy.a);if(_1yz>_1yA){return E(_1xs);}else{var _1yB=E(_1xF);if(_1yA>=(_1yB+_1yz|0)){return E(_1xs);}else{var _1yC=new T(function(){var _1yD=new T(function(){var _1yE=function(_1yF){var _1yG=E(_1yF);if(!_1yG._){return __Z;}else{var _1yH=function(_1yI){var _1yJ=E(_1yI),_1yK=E(_1yG.a);return (_1yJ>=_1yK)?_1yK+((_1yJ-_1yK|0)+(_1yB+_1yz|0)|0)|0:_1yJ;},_1yL=function(_1yM){return new T2(0,new T(function(){return E(E(_1yM).a);}),new T(function(){return _PB(_1yH,E(_1yM).b);}));};return new T2(1,_1yL,new T(function(){return _1yE(_1yG.b);}));}},_1yN=new T(function(){var _1yO=new T(function(){var _1yP=function(_1yQ){var _1yR=E(_1yQ);if(!_1yR._){return __Z;}else{var _1yS=_1yR.a,_1yT=new T(function(){if(!B(A(_Pf,[_C6,_1yS,_3C,_3F,_1xS]))._){return new T1(0,new T(function(){return _IK(_1yS);}));}else{return new T1(1,new T(function(){return _IK(_1yS);}));}});return new T2(1,_1yT,new T(function(){return _1yP(_1yR.b);}));}};return _1yP(_Pv(0,_1yz-1|0));}),_1yU=function(_1yV){var _1yW=E(_1yV);if(!_1yW._){return __Z;}else{var _1yX=_1yW.a,_1yY=new T(function(){if(!B(A(_Pf,[_C6,new T(function(){return E(_1yX)+1|0;}),_3C,_3F,_1xS]))._){return new T2(0,_1yX,__Z);}else{return new T2(0,new T(function(){return E(_1yX)+1|0;}),_1xA);}});return new T2(1,new T1(1,new T2(0,new T1(0,new T(function(){return E(E(_1yY).a)+E(_1xz)|0;})),new T(function(){return E(E(_1yY).b);}))),new T(function(){return _1yU(_1yW.b);}));}};return _1yU(B(A1(_1wQ,_1yO)).a);});return B(A3(_2B,_6h,_1x7(_IF(_1yE(_PA),_1xy)),new T1(1,new T2(0,_1xO,_1yN))));});return _nK(_1yx.b,new T2(1,_1yD,__Z));});return C > 19 ? new F(function(){return A1(_1xt,new T1(1,new T1(1,new T2(0,_1yy,_1yC))));}) : (++C,A1(_1xt,new T1(1,new T1(1,new T2(0,_1yy,_1yC)))));}}}else{return E(_1xs);}break;default:var _1yZ=new T(function(){var _1z0=new T(function(){return E(_1xF)+E(_1xR)|0;}),_1z1=function(_1z2){var _1z3=E(_1z2);if(!_1z3._){return __Z;}else{var _1z4=function(_1z5){var _1z6=E(_1z5),_1z7=E(_1z3.a);return (_1z6>=_1z7)?_1z7+((_1z6-_1z7|0)+E(_1z0)|0)|0:_1z6;},_1z8=function(_1z9){return new T2(0,new T(function(){return E(E(_1z9).a);}),new T(function(){return _PB(_1z4,E(_1z9).b);}));};return new T2(1,_1z8,new T(function(){return _1z1(_1z3.b);}));}};return B(A3(_2B,_6h,_1xc(_IF(_1z1(_PA),_1xy)),new T1(1,new T2(0,_1xO,new T(function(){return _1xB(_ss(_Pv(0,E(_1xR)-1|0),__Z));})))));});return C > 19 ? new F(function(){return A1(_1xt,new T1(1,new T4(0,1,_1xI,_1yZ,new T1(2,new T(function(){return E(_1xU.a)+1|0;})))));}) : (++C,A1(_1xt,new T1(1,new T4(0,1,_1xI,_1yZ,new T1(2,new T(function(){return E(_1xU.a)+1|0;}))))));}};return B(_1xQ(0,_Kw,_1xJ));}),_1za=function(_1zb){var _1zc=E(_1zb);if(!_1zc._){return __Z;}else{var _1zd=new T(function(){var _1ze=new T(function(){var _1zf=function(_1zg){var _1zh=E(_1zg);return (_1zh._==0)?__Z:new T1(1,new T(function(){return B(A1(_1xt,new T1(1,new T4(0,1,_1xI,_1zc.a,_1zh.a))));}));};return B(A2(_1xu,_1zf,_1xL));});return B(A1(_1xq,_1ze));});return new T1(1,_1zd);}};return B(A2(_1xu,_1za,_1xN));});return C > 19 ? new F(function(){return A1(_1xq,_1xK);}) : (++C,A1(_1xq,_1xK));}break;case 1:var _1zi=E(_1xH.a),_1zj=E(_1zi.a);if(!_1zj._){return C > 19 ? new F(function(){return A1(_1xt,new T1(1,new T1(1,new T2(0,_1zj,new T(function(){return _nK(_1zi.b,new T2(1,new T1(1,new T2(0,new T1(0,_1xz),__Z)),__Z));})))));}) : (++C,A1(_1xt,new T1(1,new T1(1,new T2(0,_1zj,new T(function(){return _nK(_1zi.b,new T2(1,new T1(1,new T2(0,new T1(0,_1xz),__Z)),__Z));}))))));}else{return E(_1xs);}break;default:return E(_1xs);}};return C > 19 ? new F(function(){return _1xE(0,_1xx);}) : (++C,_1xE(0,_1xx));};return _1xv;},_1zk=function(_1zl,_1zm,_1zn){return C > 19 ? new F(function(){return _3H(_1zm,_1zl,_1zn);}) : (++C,_3H(_1zm,_1zl,_1zn));},_1zo=function(_1zp,_1zq,_1zr){var _1zs=new T(function(){return B(A3(_2R,_2T(_1zp),_1zr,_1zq));});return function(_1zt){return C > 19 ? new F(function(){return A2(_1zs,_1zt,_1zt);}) : (++C,A2(_1zs,_1zt,_1zt));};},_1zu=function(_1zv,_1zw){return C > 19 ? new F(function(){return A2(_1zv,_1zw,_1zw);}) : (++C,A2(_1zv,_1zw,_1zw));},_1zx=function(_1zy){return new T3(0,_1zy,_1zu,function(_1wt,_1wu){return _1zo(_1zy,_1wt,_1wu);});},_1zz=function(_1zA,_1zB,_1zC){var _1zD=new T(function(){return B(A2(_1zA,function(_1zE){return C > 19 ? new F(function(){return A2(_1zA,_1zE,_1zC);}) : (++C,A2(_1zA,_1zE,_1zC));},_1zB));});return function(_1zF){return C > 19 ? new F(function(){return A2(_1zD,_1zF,_1zF);}) : (++C,A2(_1zD,_1zF,_1zF));};},_1zG=function(_1zH){return new T2(0,_1zH,function(_1wt,_1wu){return _1zz(_1zH,_1wt,_1wu);});},_1zI=new T(function(){var _1zJ=new T(function(){return _1zx(new T(function(){var _1zK=_1mW,_1zL=new T(function(){return _1zG(_3H);});return new T2(0,_1zK,_1zL);}));});return new T3(0,_1zJ,_n,_1zk);}),_1zM=new T(function(){return _1xn(_1zI);}),_1zN=function(_1zO,_1zP){return E(_1zP);},_1zQ=new T(function(){return _Pv(0,2147483647);}),_1zR=function(_1zS){var _1zT=E(_1zS);if(!_1zT._){return __Z;}else{var _1zU=function(_1zV){return new T2(0,new T(function(){return E(E(_1zV).a);}),_1zT.a);};return new T2(1,_1zU,new T(function(){return _1zR(_1zT.b);}));}},_1zW=new T(function(){return _1zR(_1zQ);}),_1zX=new T(function(){return _U6(_nK);}),_1zY=new T(function(){return _107(_Zh,_1zX,_1zX);}),_1zZ=new T(function(){return _U6(_nK);}),_1A0=new T(function(){return _107(_Zh,_1zZ,_1zZ);}),_1A1=new T(function(){return unCStr(".md");}),_1A2=function(_1A3,_1A4){return E(_1A4);},_1A5=function(_1A6,_1A7){return new T3(0,_1A6,new T(function(){return E(E(_1A7).b);}),_2L);},_1A8=function(_1A9,_1Aa,_1Ab){var _1Ac=new T(function(){return B(A1(_1Aa,_1Ab));}),_1Ad=new T(function(){return B(A1(_1A9,new T(function(){return E(E(_1Ac).a);})));});return new T3(0,_1Ad,new T(function(){return E(E(_1Ac).b);}),new T(function(){return E(E(_1Ac).c);}));},_1Ae=new T(function(){return _no(new T(function(){return _nx(new T(function(){return _mN(_1A5,new T(function(){return _nC(_1A8,_4S);}),_4S);}),_4S);}),_4S);}),_1Af=new T(function(){return B(_5m(_1Ae,_1A2,function(_1Ag){var _1Ah=E(_1Ag);if(!_1Ah._){return E(new T2(0,__Z,__Z));}else{var _1Ai=E(_1Ah.a);if(_1Ai._==2){var _1Aj=E(_1Ah.b);if(!_1Aj._){return new T2(0,_1Ah,__Z);}else{var _1Ak=E(_1Aj.a);if(_1Ak._==6){var _1Al=E(_1Ak.a);return (_1Al._==0)?new T2(0,_1Aj.b,new T1(1,new T2(0,_1Al.a,new T2(0,_1Ai.a,_1Al.b)))):new T2(0,_1Ah,__Z);}else{return new T2(0,_1Ah,__Z);}}}else{return new T2(0,_1Ah,__Z);}}}));}),_1Am=new T(function(){return B(_7y("src/CaPriCon/Run.hs:(261,60)-(264,130)|lambda"));}),_1An=new T(function(){return unCStr(" ");}),_1Ao=function(_1Ap,_1Aq){return __Z;},_1Ar=function(_1As){return __Z;},_1At=new T(function(){return err(new T(function(){return unCStr("Prelude.read: no parse");}));}),_1Au=new T(function(){return err(new T(function(){return unCStr("Prelude.read: ambiguous parse");}));}),_1Av=function(_1Aw){var _1Ax=function(_1Ay){return E(new T2(3,_1Aw,_8D));};return new T1(1,function(_1Az){return C > 19 ? new F(function(){return A2(_gA,_1Az,_1Ax);}) : (++C,A2(_gA,_1Az,_1Ax));});},_1AA=new T(function(){return B(A3(_iI,_jb,0,_1Av));}),_1AB=new T1(0,0),_1AC=new T(function(){return unCStr("openFile");}),_1AD=function(_1AE){return (E(_1AE)==( -1))?true:false;},_1AF=new T(function(){return unCStr("GHC.IO.FD.close");}),_1AG=function(_1AH,_1AI,_1AJ,_){while(1){var _1AK=B(A1(_1AJ,_));if(!B(A1(_1AH,_1AK))){return _1AK;}else{var _1AL=__hscore_get_errno();if(E(_1AL)==4){continue;}else{return _12K(_1AI,_);}}}},_1AM=function(_1AN,_){var _1AO=_1AG(_1AD,_1AF,function(_){return close(_1AN);},_);return 0;},_1AP=function(_1AQ,_){return _1AM(E(_1AQ),_);},_1AR=function(_1AS){var _1AT=E(_1AS);return (_1AT._==0)?0:E(_1AT.a)|_1AR(_1AT.b);},_1AU=function(_1AV){return E(_1AV).c;},_1AW=new T(function(){return _aK(_1AU,__Z);}),_1AX=function(_1AY){var _1AZ=E(_1AY);if(!_1AZ._){return _1AR(_1AW);}else{if(!E(_1AZ.b)._){return E(E(_1AZ.a).c);}else{return _1AR(_aK(_1AU,_1AZ));}}},_1B0=function(_1B1,_){while(1){var _1B2=E(_1B1);if(!_1B2._){return 0;}else{var _1B3=E(_1B2.a),_1B4=B(A3(_1B3.d,new T2(0,_1B3.a,_1B3.b),_1B3.c&7|4,_));_1B1=_1B2.b;continue;}}},_1B5=function(_){return 0;},_1B6=new T(function(){return unCStr("sendWakeup");}),_1B7=function(_1B8,_1B9,_1Ba,_){var _1Bb=rMV(_1B9),_1Bc=E(_1Bb),_1Bd=_1Bc.a,_1Be=_1Bc.b,_1Bf=_1Bc.c,_1Bg=E(_1Ba),_1Bh=_1Bg&(_1Bd["length"]-1|0),_1Bi=_1Bd[_1Bh],_1Bj=function(_1Bk){var _1Bl=E(_1Bk);if(!_1Bl._){return new T3(0,__Z,__Z,__Z);}else{var _1Bm=_1Bl.a,_1Bn=_1Bl.b,_1Bo=_1Bl.c;if(_1Bm!=_1Bg){var _1Bp=_1Bj(_1Bo);return new T3(0,_1Bp.a,_1Bp.b,new T3(1,_1Bm,_1Bn,_1Bp.c));}else{return new T3(0,__Z,new T1(1,_1Bn),E(_1Bo));}}},_1Bq=_1Bj(_1Bi),_1Br=function(_,_1Bs){var _1Bt=E(_1Bs);if(!_1Bt._){return _1B5;}else{var _1Bu=_1Bt.a,_1Bv=_1AX(_1Bu);if(!_1Bv){return function(_){return _1B0(_1Bu,_);};}else{var _1Bw=E(_1B8),_1Bx=E(_1Bw.a),_1By=B(A(_1Bx.c,[_1Bx.a,_1Bg,_1Bv&7,0,_])),_1Bz=eventfd_write(_1Bw.j,new Long(1,0,true));if(E(_1Bz)==( -1)){var _1BA=_12K(_1B6,_);return function(_){return _1B0(_1Bu,_);};}else{return function(_){return _1B0(_1Bu,_);};}}}},_1BB=E(_1Bq.b);if(!_1BB._){return _1Br(_,__Z);}else{var _=_1Bd[_1Bh]=_1Bq.c;if(!E(_1Bq.a)._){var _1BC=readOffAddr("i32",4,_1Be,0),_=writeOffAddr("i32",4,_1Be,0,_1BC-1|0);return _1Br(0,_1BB);}else{return _1Br(_,_1BB);}}},_1BD=function(_1BE,_){while(1){var _1BF=E(_1BE);if(!_1BF._){return 0;}else{var _1BG=B(A1(_1BF.a,_));_1BE=_1BF.b;continue;}}},_1BH=new T(function(){return err(new T(function(){return unCStr("Negative range size");}));}),_1BI=function(_){var _1BJ=readOffAddr("i32",4,":(",0),_1BK=_1BJ-1|0,_1BL=function(_1BM){if(_1BM>=0){var _1BN=newArr(_1BM,__Z),_1BO=nMV(new T4(0,0,_1BK,_1BM,_1BN)),_1BP=_1BO,_1BQ=function(_){var _1BR=getOrSetSystemEventThreadEventManagerStore(_1BP);if(!addrEq(_1BP,_1BR)){var _1BS=hs_free_stable_ptr(_1BP);return _1BR;}else{return _1BP;}};if(!0){return _1BQ();}else{return _1BQ(0);}}else{return E(_1BH);}};if(0>_1BK){return _1BL(0);}else{return _1BL(_1BK+1|0);}},_1BT=new T(function(){return _12n(_1BI);}),_1BU=function(_1BV,_1BW,_){if(!0){var _1BX=function(_){var _1BY=jsCatch(function(_){return C > 19 ? new F(function(){return _1BV();}) : (++C,_1BV());},function(_1BZ,_){var _1C0=B(A1(_1BW,_));return die(_1BZ);}),_1C1=B(A1(_1BW,_));return _1BY;};return _1BX();}else{var _1C2=jsCatch(_1BV,function(_1C3,_){var _1C4=B(A1(_1BW,_));return die(_1C3);}),_1C5=B(A1(_1BW,_));return _1C2;}},_1C6=function(_1C7){return _ck(0,E(_1C7),__Z);},_1C8=function(_1C9,_1Ca){return _ck(0,E(_1C9),_1Ca);},_1Cb=new T3(0,function(_1Cc,_1Cd,_1Ce){return _ck(E(_1Cc),E(_1Cd),_1Ce);},_1C6,function(_1Cf,_1Cg){return _1R(_1C8,_1Cf,_1Cg);}),_1Ch=new T(function(){return unCStr("Int");}),_1Ci=new T(function(){return unCStr(" out of range ");}),_1Cj=new T(function(){return unCStr("}.index: Index ");}),_1Ck=new T(function(){return unCStr("Ix{");}),_1Cl=function(_1Cm,_1Cn,_1Co,_1Cp,_1Cq){var _1Cr=new T(function(){var _1Cs=new T(function(){var _1Ct=new T(function(){var _1Cu=new T(function(){var _1Cv=new T(function(){return B(A3(_SJ,_SE,new T2(1,new T(function(){return B(A3(_SR,_1Co,0,_1Cp));}),new T2(1,new T(function(){return B(A3(_SR,_1Co,0,_1Cq));}),__Z)),new T2(1,41,new T2(1,41,__Z))));});return _0(_1Ci,new T2(1,40,new T2(1,40,_1Cv)));});return B(A(_SR,[_1Co,0,_1Cn,new T2(1,41,_1Cu)]));});return _0(_1Cj,new T2(1,40,_1Ct));},1);return _0(_1Cm,_1Cs);},1);return err(_0(_1Ck,_1Cr));},_1Cw=function(_1Cx,_1Cy,_1Cz,_1CA,_1CB){return _1Cl(_1Cx,_1Cy,_1CB,_1Cz,_1CA);},_1CC=function(_1CD,_1CE,_1CF,_1CG){var _1CH=E(_1CF);return _1Cw(_1CD,_1CE,_1CH.a,_1CH.b,_1CG);},_1CI=function(_1CJ,_1CK,_1CL,_1CM){return C > 19 ? new F(function(){return _1CC(_1CM,_1CL,_1CK,_1CJ);}) : (++C,_1CC(_1CM,_1CL,_1CK,_1CJ));},_1CN=function(_1CO,_1CP,_1CQ){return C > 19 ? new F(function(){return _1CI(_1Cb,new T2(0,_1CP,_1CQ),_1CO,_1Ch);}) : (++C,_1CI(_1Cb,new T2(0,_1CP,_1CQ),_1CO,_1Ch));},_1CR=new T(function(){return B(A2(_2b,_2a,new T(function(){return B(A1(_2d,new T(function(){return unCStr("Pattern match failure in do expression at GHC/Event/Thread.hs:104:5-17");})));})));}),_1CS=function(_1CT,_1CU,_1CV,_1CW){var _1CX=E(_1CU);if(!_1CX._){return __Z;}else{var _1CY=E(_1CV);if(!_1CY._){return __Z;}else{var _1CZ=E(_1CW);return (_1CZ._==0)?__Z:new T2(1,new T(function(){return B(A3(_1CT,_1CX.a,_1CY.a,_1CZ.a));}),new T(function(){return _1CS(_1CT,_1CX.b,_1CY.b,_1CZ.b);}));}}},_1D0=function(_1D1,_1D2,_){var _1D3=rMV(E(_1BT)),_1D4=E(_1D3),_1D5=E(_1D4.a),_1D6=E(_1D4.b),_1D7=function(_,_1D8){var _1D9=function(_){var _1Da=function(_1Db,_){var _1Dc=E(_1Db);if(!_1Dc._){return __Z;}else{var _1Dd=E(_1Dc.a),_1De=E(_1Dd.b),_1Df=E(_1Dd.c),_1Dg=E(_1D2)&31;if(_1De>_1Dg){return C > 19 ? new F(function(){return _1CN(_1Dg,_1De,_1Df);}) : (++C,_1CN(_1Dg,_1De,_1Df));}else{if(_1Dg>_1Df){return C > 19 ? new F(function(){return _1CN(_1Dg,_1De,_1Df);}) : (++C,_1CN(_1Dg,_1De,_1Df));}else{var _1Dh=takeMVar(E(_1Dd.e[_1Dg-_1De|0])),_1Di=B(_1Da(_1Dc.b,_));return new T2(1,_1Dh,_1Di);}}}},_1Dj=B(_1Da(_1D8,_)),_1Dk=function(_1Dl,_1Dm,_){var _1Dn=E(_1Dl);if(!_1Dn._){return __Z;}else{var _1Do=E(_1Dm);if(!_1Do._){return __Z;}else{var _1Dp=_1B7(_1Dn.a,E(_1Do.a),_1D2,_),_1Dq=_1Dk(_1Dn.b,_1Do.b,_);return new T2(1,_1Dp,_1Dq);}}},_1Dr=_1Dk(_1D8,_1Dj,_),_1Ds=new T(function(){return _1CS(function(_1Dt,_1Du,_1Dv,_){var _1Dw=E(_1Dt),_1Dx=E(_1Dw.b),_1Dy=E(_1Dw.c),_1Dz=E(_1D2)&31;if(_1Dx>_1Dz){return C > 19 ? new F(function(){return _1CN(_1Dz,_1Dx,_1Dy);}) : (++C,_1CN(_1Dz,_1Dx,_1Dy));}else{if(_1Dz>_1Dy){return C > 19 ? new F(function(){return _1CN(_1Dz,_1Dx,_1Dy);}) : (++C,_1CN(_1Dz,_1Dx,_1Dy));}else{var _=putMVar(E(_1Dw.e[_1Dz-_1Dx|0]),_1Du);return C > 19 ? new F(function(){return A1(_1Dv,_);}) : (++C,A1(_1Dv,_));}}},_1D8,_1Dj,_1Dr);});return _1BU(new T(function(){return B(A1(_1D1,_1D2));}),function(_){return _1BD(_1Ds,_);},_);};if(!0){return _1D9();}else{return _1D9(_);}};if(_1D5<=_1D6){var _1DA=function(_1DB,_){if(_1D5>_1DB){return C > 19 ? new F(function(){return _1CN(_1DB,_1D5,_1D6);}) : (++C,_1CN(_1DB,_1D5,_1D6));}else{if(_1DB>_1D6){return C > 19 ? new F(function(){return _1CN(_1DB,_1D5,_1D6);}) : (++C,_1CN(_1DB,_1D5,_1D6));}else{var _1DC=_1D4.d[_1DB-_1D5|0],_1DD=E(_1DC);if(!_1DD._){return die(_1CR);}else{var _1DE=E(E(_1DD.a).b);if(_1DB!=_1D6){var _1DF=B(_1DA(_1DB+1|0,_));return new T2(1,_1DE,_1DF);}else{return new T2(1,_1DE,__Z);}}}}},_1DG=B(_1DA(_1D5,_));return C > 19 ? new F(function(){return _1D7(_,_1DG);}) : (++C,_1D7(_,_1DG));}else{return C > 19 ? new F(function(){return _1D7(_,__Z);}) : (++C,_1D7(_,__Z));}},_1DH=function(_1DI,_){var _1DJ=unlockFile(_1DI),_1DK=rtsSupportsBoundThreads();if(!E(_1DK)){var _1DL=_1AG(_1AD,_1AF,function(_){return close(_1DI);},_);return 0;}else{return C > 19 ? new F(function(){return _1D0(_1AP,_1DI,_);}) : (++C,_1D0(_1AP,_1DI,_));}},_1DM=function(_){return  -1;},_1DN=function(_1DO,_1DP,_1DQ,_){while(1){var _1DR=B(A1(_1DP,_)),_1DS=E(_1DR);if(_1DS==( -1)){var _1DT=__hscore_get_errno();switch(E(_1DT)){case 4:continue;case 11:return C > 19 ? new F(function(){return A1(_1DQ,_);}) : (++C,A1(_1DQ,_));break;default:return _12K(_1DO,_);}}else{return _1DS;}}},_1DU=new T(function(){return unCStr("GHC.IO.FD.fdWriteNonBlocking");}),_1DV=function(_1DW,_1DX,_1DY,_1DZ,_){if(!E(_1DX)){var _1E0=fdReady(_1DW,1,0,0);if(!E(_1E0)){return 0;}else{var _1E1=rtsSupportsBoundThreads();if(!E(_1E1)){var _1E2=B(_1DN(_1DU,function(_){return ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite(_1DW,E(_1DY),E(_1DZ)>>>0);},_1DM,_)),_1E3=E(_1E2);return (_1E3==( -1))?0:_1E3;}else{var _1E4=B(_1DN(_1DU,function(_){return ghczuwrapperZC19ZCbaseZCSystemziPosixziInternalsZCwrite(_1DW,E(_1DY),E(_1DZ)>>>0);},_1DM,_)),_1E5=E(_1E4);return (_1E5==( -1))?0:_1E5;}}}else{var _1E6=B(_1DN(_1DU,function(_){return ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite(_1DW,E(_1DY),E(_1DZ)>>>0);},_1DM,_)),_1E7=E(_1E6);return (_1E7==( -1))?0:_1E7;}},_1E8=function(_1E9,_1Ea,_1Eb,_1Ec,_1Ed,_1Ee,_1Ef,_1Eg,_){var _1Eh=_1DV(_1E9,_1Ea,plusAddr(_1Eb,_1Ef),_1Eg-_1Ef|0,_);return new T2(0,_1Eh,new T(function(){var _1Ei=_1Ef+E(_1Eh)|0;if(_1Ei!=_1Eg){return new T6(0,_1Eb,_1Ec,_1Ed,_1Ee,_1Ei,_1Eg);}else{return new T6(0,_1Eb,_1Ec,_1Ed,_1Ee,0,0);}}));},_1Ej=new T(function(){return unCStr("GHC.IO.FD.fdRead");}),_1Ek=function(_1El,_1Em,_){var _1En=rMV(_1Em),_1Eo=E(_1En).a,_1Ep=E(_1El),_1Eq=_1Eo[_1Ep&(_1Eo["length"]-1|0)],_1Er=function(_1Es,_){while(1){var _1Et=E(_1Es);if(!_1Et._){return __Z;}else{if(_1Et.a!=_1Ep){_1Es=_1Et.c;continue;}else{return new T1(1,_1Et.b);}}}};return _1Er(_1Eq,_);},_1Eu=function(_1Ev,_1Ew){while(1){var _1Ex=(function(_1Ey,_1Ez){var _1EA=E(_1Ez);if(!_1EA._){return __Z;}else{var _1EB=_1EA.a,_1EC=_1EA.b;if(!B(A1(_1Ey,_1EB))){var _1ED=_1Ey;_1Ev=_1ED;_1Ew=_1EC;return __continue;}else{return new T2(1,_1EB,new T(function(){return _1Eu(_1Ey,_1EC);}));}}})(_1Ev,_1Ew);if(_1Ex!=__continue){return _1Ex;}}},_1EE=new T(function(){return unCStr("Int");}),_1EF=function(_1EG,_1EH,_1EI){return C > 19 ? new F(function(){return _1CI(_1Cb,new T2(0,_1EH,_1EI),_1EG,_1EE);}) : (++C,_1CI(_1Cb,new T2(0,_1EH,_1EI),_1EG,_1EE));},_1EJ=new T(function(){return unCStr("unregisterFd_");}),_1EK=function(_1EL,_1EM){var _1EN=new T(function(){return _0(_ck(0,_1EM,__Z),new T(function(){return unAppCStr(" at location ",_1EL);},1));});return err(unAppCStr("Failed while attempting to modify registration of file ",_1EN));},_1EO=function(_1EP){return _1EK(_1EJ,_1EP);},_1EQ=function(_1ER,_1ES,_1ET,_1EU,_1EV,_1EW,_1EX,_1EY,_1EZ,_1F0,_){var _1F1=new T(function(){var _1F2=_1EZ&31;if(_1ES>_1F2){return B(_1EF(_1F2,_1ES,_1ET));}else{if(_1F2>_1ET){return B(_1EF(_1F2,_1ES,_1ET));}else{return E(_1EU[_1F2-_1ES|0]);}}}),_1F3=function(_1F4,_){var _1F5=rMV(_1F4),_1F6=E(_1F5),_1F7=_1F6.a,_1F8=_1F6.b,_1F9=_1F6.c,_1Fa=_1EZ&(_1F7["length"]-1|0),_1Fb=_1F7[_1Fa],_1Fc=function(_1Fd){return hs_neInt64(E(_1Fd).b,_1F0);},_1Fe=function(_1Ff){var _1Fg=E(_1Ff);if(!_1Fg._){return new T3(0,__Z,__Z,__Z);}else{var _1Fh=_1Fg.a,_1Fi=_1Fg.b,_1Fj=_1Fg.c;if(_1Fh!=_1EZ){var _1Fk=_1Fe(_1Fj);return new T3(0,_1Fk.a,_1Fk.b,new T3(1,_1Fh,_1Fi,_1Fk.c));}else{var _1Fl=_1Eu(_1Fc,_1Fi);if(!_1Fl._){var _1Fm=__Z;}else{var _1Fm=new T1(1,_1Fl);}var _1Fn=E(_1Fm);if(!_1Fn._){var _1Fo=E(_1Fj);}else{var _1Fo=new T3(1,_1Fh,_1Fn.a,_1Fj);}return new T3(0,_1Fm,new T1(1,_1Fi),_1Fo);}}},_1Fp=_1Fe(_1Fb),_1Fq=function(_,_1Fr){var _1Fs=function(_1Ft,_1Fu,_){if(_1Ft==_1Fu){return false;}else{if(!(_1Fu&8)){var _1Fv=E(_1ER),_1Fw=B(A(_1Fv.c,[_1Fv.a,_1EZ,_1Ft&7,_1Fu&7,_]));if(!E(_1Fw)){return _1EO(_1EZ);}else{return true;}}else{var _1Fx=E(_1ER),_1Fy=B(A(_1Fx.c,[_1Fx.a,_1EZ,_1Ft&7,_1Fu&7,_]));if(!E(_1Fy)){return _1EO(_1EZ);}else{return true;}}}},_1Fz=E(_1Fr);if(!_1Fz._){return C > 19 ? new F(function(){return _1Fs(0,0,_);}) : (++C,_1Fs(0,0,_));}else{var _1FA=_1Ek(_1EZ,_1F4,_),_1FB=_1AX(_1Fz.a),_1FC=E(_1FA);if(!_1FC._){return C > 19 ? new F(function(){return _1Fs(_1FB,0,_);}) : (++C,_1Fs(_1FB,0,_));}else{return C > 19 ? new F(function(){return _1Fs(_1FB,_1AX(_1FC.a),_);}) : (++C,_1Fs(_1FB,_1AX(_1FC.a),_));}}},_1FD=E(_1Fp.b);if(!_1FD._){return C > 19 ? new F(function(){return _1Fq(_,__Z);}) : (++C,_1Fq(_,__Z));}else{var _=_1F7[_1Fa]=_1Fp.c;if(!E(_1Fp.a)._){var _1FE=readOffAddr("i32",4,_1F8,0),_=writeOffAddr("i32",4,_1F8,0,_1FE-1|0);return C > 19 ? new F(function(){return _1Fq(0,_1FD);}) : (++C,_1Fq(0,_1FD));}else{return C > 19 ? new F(function(){return _1Fq(_,_1FD);}) : (++C,_1Fq(_,_1FD));}}},_1FF=function(_1FG,_){return C > 19 ? new F(function(){return _1F3(E(_1FG),_);}) : (++C,_1F3(E(_1FG),_));};if(!0){var _1FH=function(_){var _1FI=E(_1F1),_1FJ=takeMVar(_1FI),_1FK=_1FJ,_1FL=function(_){return C > 19 ? new F(function(){return _1FF(_1FK,_);}) : (++C,_1FF(_1FK,_));},_1FM=jsCatch(function(_){return C > 19 ? new F(function(){return _1FL();}) : (++C,_1FL());},function(_1FN,_){var _=putMVar(_1FI,_1FK);return die(_1FN);}),_=putMVar(_1FI,_1FK);return _1FM;};return _1FH();}else{var _1FO=E(_1F1),_1FP=takeMVar(_1FO),_1FQ=_1FP,_1FR=jsCatch(function(_){return C > 19 ? new F(function(){return _1FF(_1FQ,_);}) : (++C,_1FF(_1FQ,_));},function(_1FS,_){var _=putMVar(_1FO,_1FQ);return die(_1FS);}),_=putMVar(_1FO,_1FQ);return _1FR;}},_1FT=function(_1FU,_1FV,_1FW,_){var _1FX=newArr(_1FU["length"]<<1,__Z),_1FY=_1FX,_1FZ=nMV(__Z),_1G0=newByteArr(4),_=writeOffAddr("i32",4,_1G0,0,0),_1G1=function(_1G2,_1G3,_){if(_1G2!=E(_1FW)){var _1G4=_1FU[_1G3],_1G5=function(_1G6,_1G7,_){while(1){var _1G8=E(_1G7);if(!_1G8._){return C > 19 ? new F(function(){return _1G1(_1G6,_1G3+1|0,0);}) : (++C,_1G1(_1G6,_1G3+1|0,0));}else{var _1G9=_1G8.a,_1Ga=_1G9&(_1FY["length"]-1|0),_1Gb=_1FY[_1Ga],_=_1FY[_1Ga]=new T3(1,_1G9,_1G8.b,_1Gb),_1Gc=_1G6+1|0;_1G6=_1Gc;_1G7=_1G8.c;_=0;continue;}}};return C > 19 ? new F(function(){return _1G5(_1G2,_1G4,0);}) : (++C,_1G5(_1G2,_1G4,0));}else{return 0;}},_1Gd=B(_1G1(0,0,0)),_=writeOffAddr("i32",4,_1G0,0,E(_1FW)),_=wMV(E(_1FV),new T3(0,_1FY,_1G0,new T2(1,_1G0,_1FZ)));return 0;},_1Ge=function(_1Gf,_1Gg){var _1Gh=E(_1Gf);return (_1Gh._==0)?E(_1Gg):new T3(1,_1Gh.a,_1Gh.b,new T(function(){return _1Ge(_1Gh.c,_1Gg);}));},_1Gi=function(_1Gj,_1Gk,_1Gl,_1Gm,_){var _1Gn=rMV(_1Gm),_1Go=E(_1Gn),_1Gp=_1Go.a,_1Gq=_1Go.b,_1Gr=_1Go.c,_1Gs=E(_1Gk),_1Gt=_1Gs&(_1Gp["length"]-1|0),_1Gu=_1Gp[_1Gt],_1Gv=function(_1Gw,_1Gx,_){while(1){var _1Gy=E(_1Gx);if(!_1Gy._){var _1Gz=readOffAddr("i32",4,_1Gq,0);if((_1Gz+1|0)<(_1Gp["length"]-(_1Gp["length"]>>2)|0)){var _=_1Gp[_1Gt]=new T3(1,_1Gs,E(_1Gl),_1Gw),_=writeOffAddr("i32",4,_1Gq,0,_1Gz+1|0);return __Z;}else{var _1GA=_1FT(_1Gp,_1Gm,_1Gz,_),_1GB=B(_1GC(_1Gj,_1Gs,_1Gl,_1Gm,_));return _1GB;}}else{var _1GD=_1Gy.a,_1GE=_1Gy.b,_1GF=_1Gy.c;if(_1GD!=_1Gs){var _1GG=new T3(1,_1GD,_1GE,_1Gw);_1Gw=_1GG;_1Gx=_1GF;continue;}else{var _=_1Gp[_1Gt]=new T3(1,_1Gs,B(A2(_1Gj,_1Gl,_1GE)),_1Ge(_1Gw,_1GF));return new T1(1,_1GE);}}}};return _1Gv(__Z,_1Gu,_);},_1GH=function(_1GI,_1GJ,_1GK,_1GL,_){return _1Gi(_1GI,_1GJ,_1GK,E(_1GL),_);},_1GC=function(_1GM,_1GN,_1GO,_1GP,_){return _1GH(_1GM,_1GN,_1GO,_1GP,_);},_1GQ=function(_){var _1GR=die("Unsupported PrimOp: threadStatus#"),_1GS=_1GR.b,_1GT=rMV(E(_1BT)),_1GU=E(_1GT),_1GV=E(_1GU.a),_1GW=E(_1GU.b);if(_1GV>_1GS){return C > 19 ? new F(function(){return _1CI(_1Cb,new T2(0,_1GV,_1GW),_1GS,_1Ch);}) : (++C,_1CI(_1Cb,new T2(0,_1GV,_1GW),_1GS,_1Ch));}else{if(_1GS>_1GW){return C > 19 ? new F(function(){return _1CI(_1Cb,new T2(0,_1GV,_1GW),_1GS,_1Ch);}) : (++C,_1CI(_1Cb,new T2(0,_1GV,_1GW),_1GS,_1Ch));}else{var _1GX=_1GU.d[_1GS-_1GV|0];return new T(function(){var _1GY=E(_1GX);if(!_1GY._){return __Z;}else{return new T1(1,new T(function(){return _3W(_1GY.a);}));}});}}},_1GZ=new T(function(){return B(A2(_2b,_2a,new T(function(){return B(A1(_2d,new T(function(){return unCStr("Pattern match failure in do expression at GHC/Event/Thread.hs:183:3-10");})));})));}),_1H0=new T2(0,false,false),_1H1=function(_1H2,_){return die(new T(function(){return _1K(_1H2);}));},_1H3=new T(function(){return _12A(new T(function(){return unCStr("threadWait");}),9,__Z,__Z);}),_1H4=function(_1H5,_){if(!(E(_1H5)&4)){return 0;}else{return _1H1(_1H3,_);}},_1H6=function(_1H7,_1H8,_){var _1H9=function(_){var _1Ha=newMVar(),_1Hb=_1Ha,_1Hc=B(_1GQ(_)),_1Hd=E(_1Hc);if(!_1Hd._){return die(_1GZ);}else{var _1He=E(_1Hd.a),_1Hf=_1He.e,_1Hg=_1He.f,_1Hh=_1He.g,_1Hi=_1He.k,_1Hj=_1He.l,_1Hk=E(_1He.b),_1Hl=E(_1He.c),_1Hm=E(_1He.a),_1Hn=(function(_){var _1Ho=rMV(_1Hh),_1Hp=hs_plusInt64(E(_1Ho),new Long(1,0)),_=wMV(_1Hh,_1Hp);return _1Hp;})(),_1Hq=E(_1H8),_1Hr=E(_1Hn),_1Hs=E(_1H7),_1Ht=new T(function(){var _1Hu=_1Hq&31;if(_1Hk>_1Hu){return B(_1CN(_1Hu,_1Hk,_1Hl));}else{if(_1Hu>_1Hl){return B(_1CN(_1Hu,_1Hk,_1Hl));}else{return E(_1Hf[_1Hu-_1Hk|0]);}}}),_1Hv=function(_1Hw,_){var _1Hx=B(_1GC(_0,_1Hq,new T2(1,new T4(0,_1Hq,_1Hr,_1Hs,function(_1Hy,_1Hz,_){var _=putMVar(_1Hb,_1Hz);return 0;}),__Z),_1Hw,_)),_1HA=_1Hx,_1HB=function(_1HC){var _1HD=_1HC|_1Hs;if(_1HC==_1HD){return new T2(0,false,true);}else{var _1HE=B(A(_1Hm.c,[_1Hm.a,_1Hq,_1HC&7,_1HD&7,_]));if(!E(_1HE)){var _1HF=E(_1HA);if(!_1HF._){var _1HG=rMV(_1Hw),_1HH=E(_1HG),_1HI=_1HH.a,_1HJ=_1HH.b,_1HK=_1HH.c,_1HL=_1Hq&(_1HI["length"]-1|0),_1HM=_1HI[_1HL],_1HN=function(_1HO){var _1HP=E(_1HO);if(!_1HP._){return new T3(0,__Z,__Z,__Z);}else{var _1HQ=_1HP.a,_1HR=_1HP.b,_1HS=_1HP.c;if(_1HQ!=_1Hq){var _1HT=_1HN(_1HS);return new T3(0,_1HT.a,_1HT.b,new T3(1,_1HQ,_1HR,_1HT.c));}else{return new T3(0,__Z,new T1(1,_1HR),E(_1HS));}}},_1HU=_1HN(_1HM);if(!E(_1HU.b)._){return _1H0;}else{var _=_1HI[_1HL]=_1HU.c;if(!E(_1HU.a)._){var _1HV=readOffAddr("i32",4,_1HJ,0),_=writeOffAddr("i32",4,_1HJ,0,_1HV-1|0);return _1H0;}else{return _1H0;}}}else{var _1HW=B(_1GC(_1mW,_1Hq,_1HF.a,_1Hw,_));return _1H0;}}else{return new T2(0,true,true);}}},_1HX=E(_1HA);if(!_1HX._){return _1HB(0);}else{return _1HB(_1AX(_1HX.a));}},_1HY=function(_1HZ,_){return _1Hv(E(_1HZ),_);},_1I0=function(_,_1I1,_1I2){if(!E(_1I2)){var _1I3=jsCatch(function(_){return takeMVar(_1Hb);},function(_1I4,_){var _1I5=E(_1I1),_1I6=_1EQ(_1Hm,_1Hk,_1Hl,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1I5.a,_1I5.b,_);return die(_1I4);});return _1H4(_1I3,_);}else{var _1I7=eventfd_write(_1He.j,new Long(1,0,true)),_1I8=function(_){var _1I9=jsCatch(function(_){return takeMVar(_1Hb);},function(_1Ia,_){var _1Ib=E(_1I1),_1Ic=_1EQ(_1Hm,_1Hk,_1Hl,_1Hf,_1Hg,_1Hh,_1Hi,_1Hj,_1Ib.a,_1Ib.b,_);return die(_1Ia);});return _1H4(_1I9,_);};if(E(_1I7)==( -1)){var _1Id=_12K(_1B6,_);return C > 19 ? new F(function(){return _1I8(_);}) : (++C,_1I8(_));}else{return C > 19 ? new F(function(){return _1I8(_);}) : (++C,_1I8(_));}}};if(!0){var _1Ie=function(_){var _1If=E(_1Ht),_1Ig=takeMVar(_1If),_1Ih=_1Ig,_1Ii=function(_){return _1HY(_1Ih,_);},_1Ij=jsCatch(function(_){return C > 19 ? new F(function(){return _1Ii();}) : (++C,_1Ii());},function(_1Ik,_){var _=putMVar(_1If,_1Ih);return die(_1Ik);}),_=putMVar(_1If,_1Ih);return _1Ij;},_1Il=_1Ie(),_1Im=E(_1Il),_1In=_1Im.a;if(!E(_1Im.b)){var _=putMVar(_1Hb,_1Hs);return C > 19 ? new F(function(){return _1I0(_,new T2(0,_1Hq,_1Hr),_1In);}) : (++C,_1I0(_,new T2(0,_1Hq,_1Hr),_1In));}else{return C > 19 ? new F(function(){return _1I0(_,new T2(0,_1Hq,_1Hr),_1In);}) : (++C,_1I0(_,new T2(0,_1Hq,_1Hr),_1In));}}else{var _1Io=E(_1Ht),_1Ip=takeMVar(_1Io),_1Iq=_1Ip,_1Ir=jsCatch(function(_){return _1HY(_1Iq,_);},function(_1Is,_){var _=putMVar(_1Io,_1Iq);return die(_1Is);}),_=putMVar(_1Io,_1Iq),_1It=E(_1Ir),_1Iu=_1It.a;if(!E(_1It.b)){var _=putMVar(_1Hb,_1Hs);return C > 19 ? new F(function(){return _1I0(_,new T2(0,_1Hq,_1Hr),_1Iu);}) : (++C,_1I0(_,new T2(0,_1Hq,_1Hr),_1Iu));}else{return C > 19 ? new F(function(){return _1I0(_,new T2(0,_1Hq,_1Hr),_1Iu);}) : (++C,_1I0(_,new T2(0,_1Hq,_1Hr),_1Iu));}}}};if(!0){return C > 19 ? new F(function(){return _1H9();}) : (++C,_1H9());}else{return C > 19 ? new F(function(){return _1H9(_);}) : (++C,_1H9(_));}},_1Iv=function(_1Iw,_1Ix,_1Iy,_1Iz,_){while(1){var _1IA=B(A1(_1Iy,_));if(!B(A1(_1Iw,_1IA))){return _1IA;}else{var _1IB=__hscore_get_errno();switch(E(_1IB)){case 4:continue;case 11:var _1IC=B(A1(_1Iz,_));continue;default:return _12K(_1Ix,_);}}}},_1ID=function(_1IE){return (E(_1IE)==( -1))?true:false;},_1IF=function(_1IG,_1IH,_1II,_1IJ,_1IK,_1IL,_){var _1IM=function(_1IN,_){var _1IO=_1Iv(_1ID,_1IG,_1IN,function(_){var _1IP=rtsSupportsBoundThreads();if(!E(_1IP)){var _=die("Unsupported PrimOp: waitRead#");return 0;}else{return C > 19 ? new F(function(){return _1H6(1,_1IH,_);}) : (++C,_1H6(1,_1IH,_));}},_);return new T(function(){return E(_1IO);});},_1IQ=function(_){return ghczuwrapperZC22ZCbaseZCSystemziPosixziInternalsZCread(_1IH,plusAddr(E(_1IJ),E(_1IK)),E(_1IL));};if(!E(_1II)){var _1IR=fdReady(_1IH,0,0,0),_1IS=function(_,_1IT){var _1IU=function(_){var _1IV=rtsSupportsBoundThreads();if(!E(_1IV)){return _1IM(_1IQ,_);}else{return _1IM(function(_){return ghczuwrapperZC21ZCbaseZCSystemziPosixziInternalsZCread(_1IH,plusAddr(E(_1IJ),E(_1IK)),E(_1IL));},_);}};if(!E(_1IT)){var _1IW=rtsSupportsBoundThreads();if(!E(_1IW)){var _=die("Unsupported PrimOp: waitRead#");return _1IU(_);}else{var _1IX=B(_1H6(1,_1IH,_));return _1IU(_);}}else{return _1IU(_);}},_1IY=E(_1IR);if(_1IY==( -1)){var _1IZ=_12K(_1IG,_);return _1IS(_,E(_1IZ));}else{return _1IS(_,_1IY);}}else{return _1IM(_1IQ,_);}},_1J0=function(_1J1,_1J2,_1J3,_1J4,_1J5,_1J6,_1J7,_1J8,_){var _1J9=B(_1IF(_1Ej,_1J1,_1J2,plusAddr(_1J3,_1J8),0,(_1J6-_1J8|0)>>>0,_));return new T2(0,_1J9,new T(function(){return new T6(0,_1J3,_1J4,_1J5,_1J6,_1J7,_1J8+E(_1J9)|0);}));},_1Ja=function(_1Jb,_1Jc,_1Jd,_1Je,_1Jf,_1Jg,_){var _1Jh=function(_1Ji,_){return _1Iv(_1ID,_1Jb,_1Ji,function(_){var _1Jj=rtsSupportsBoundThreads();if(!E(_1Jj)){var _=die("Unsupported PrimOp: waitWrite#");return 0;}else{return C > 19 ? new F(function(){return _1H6(2,_1Jc,_);}) : (++C,_1H6(2,_1Jc,_));}},_);},_1Jk=function(_){return ghczuwrapperZC20ZCbaseZCSystemziPosixziInternalsZCwrite(_1Jc,plusAddr(E(_1Je),E(_1Jf)),E(_1Jg));};if(!E(_1Jd)){var _1Jl=fdReady(_1Jc,1,0,0),_1Jm=function(_){var _1Jn=rtsSupportsBoundThreads();if(!E(_1Jn)){return C > 19 ? new F(function(){return _1Jh(_1Jk,_);}) : (++C,_1Jh(_1Jk,_));}else{return C > 19 ? new F(function(){return _1Jh(function(_){return ghczuwrapperZC19ZCbaseZCSystemziPosixziInternalsZCwrite(_1Jc,plusAddr(E(_1Je),E(_1Jf)),E(_1Jg));},_);}) : (++C,_1Jh(function(_){return ghczuwrapperZC19ZCbaseZCSystemziPosixziInternalsZCwrite(_1Jc,plusAddr(E(_1Je),E(_1Jf)),E(_1Jg));},_));}};if(!E(_1Jl)){var _1Jo=rtsSupportsBoundThreads();if(!E(_1Jo)){var _=die("Unsupported PrimOp: waitWrite#");return C > 19 ? new F(function(){return _1Jm(_);}) : (++C,_1Jm(_));}else{var _1Jp=B(_1H6(2,_1Jc,_));return C > 19 ? new F(function(){return _1Jm(_);}) : (++C,_1Jm(_));}}else{return C > 19 ? new F(function(){return _1Jm(_);}) : (++C,_1Jm(_));}}else{return C > 19 ? new F(function(){return _1Jh(_1Jk,_);}) : (++C,_1Jh(_1Jk,_));}},_1Jq=new T(function(){return unCStr("GHC.IO.FD.fdWrite");}),_1Jr=function(_1Js,_1Jt,_1Ju,_1Jv,_){while(1){var _1Jw=(function(_1Jx,_1Jy,_1Jz,_1JA,_){var _1JB=B(_1Ja(_1Jq,_1Jx,_1Jy,_1Jz,0,new T(function(){return E(_1JA)>>>0;}),_)),_1JC=E(_1JB),_1JD=E(_1JA);if(_1JC>=_1JD){return 0;}else{var _1JE=_1Jx,_1JF=_1Jy;_1Js=_1JE;_1Jt=_1JF;_1Ju=new T(function(){return plusAddr(E(_1Jz),_1JC);});_1Jv=_1JD-_1JC|0;return __continue;}})(_1Js,_1Jt,_1Ju,_1Jv,_);if(_1Jw!=__continue){return _1Jw;}}},_1JG=function(_1JH,_1JI,_){return new T(function(){var _1JJ=E(_1JI);return new T6(0,_1JJ.a,_1JJ.b,1,_1JJ.d,0,0);});},_1JK=new T(function(){return unCStr("GHC.IO.FD.fdReadNonBlocking");}),_1JL=new T1(1,0),_1JM=function(_1JN,_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU,_){if(!E(_1JO)){var _1JV=fdReady(_1JN,0,0,0);if(!E(_1JV)){return new T2(0,_1JL,new T6(0,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU));}else{var _1JW=B(_1DN(_1JK,function(_){return ghczuwrapperZC21ZCbaseZCSystemziPosixziInternalsZCread(_1JN,plusAddr(_1JP,_1JU),(_1JS-_1JU|0)>>>0);},_1DM,_)),_1JX=E(_1JW);switch(_1JX){case  -1:return new T2(0,_1JL,new T6(0,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU));case 0:return new T2(0,__Z,new T6(0,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU));default:return new T2(0,new T1(1,_1JX),new T6(0,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU+_1JX|0));}}}else{var _1JY=B(_1DN(_1JK,function(_){return ghczuwrapperZC22ZCbaseZCSystemziPosixziInternalsZCread(_1JN,plusAddr(_1JP,_1JU),(_1JS-_1JU|0)>>>0);},_1DM,_)),_1JZ=E(_1JY);switch(_1JZ){case  -1:return new T2(0,_1JL,new T6(0,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU));case 0:return new T2(0,__Z,new T6(0,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU));default:return new T2(0,new T1(1,_1JZ),new T6(0,_1JP,_1JQ,_1JR,_1JS,_1JT,_1JU+_1JZ|0));}}},_1K0=new T6(0,function(_1K1,_1K2,_){var _1K3=nMV(__Z),_1K4=newByteArr(8096);return new T6(0,_1K4,new T2(1,_1K4,_1K3),_1K2,8096,0,0);},function(_1K5,_1K6,_){var _1K7=E(_1K5),_1K8=E(_1K6);return _1J0(_1K7.a,_1K7.b,_1K8.a,_1K8.b,_1K8.c,_1K8.d,_1K8.e,_1K8.f,_);},function(_1K9,_1Ka,_){var _1Kb=E(_1K9),_1Kc=E(_1Ka);return _1JM(_1Kb.a,_1Kb.b,_1Kc.a,_1Kc.b,_1Kc.c,_1Kc.d,_1Kc.e,_1Kc.f,_);},_1JG,function(_1Kd,_1Ke,_){var _1Kf=E(_1Ke),_1Kg=_1Kf.a,_1Kh=_1Kf.e,_1Ki=E(_1Kd),_1Kj=_1Jr(_1Ki.a,_1Ki.b,plusAddr(_1Kg,_1Kh),_1Kf.f-_1Kh|0,_);return new T6(0,_1Kg,_1Kf.b,_1Kf.c,_1Kf.d,0,0);},function(_1Kk,_1Kl,_){var _1Km=E(_1Kk),_1Kn=E(_1Kl);return _1E8(_1Km.a,_1Km.b,_1Kn.a,_1Kn.b,_1Kn.c,_1Kn.d,_1Kn.e,_1Kn.f,_);}),_1Ko=new T(function(){return unCStr("GHC.IO.FD.dup2");}),_1Kp=function(_1Kq,_1Kr,_1Ks,_){var _1Kt=dup2(_1Kq,_1Ks);if(E(_1Kt)==( -1)){var _1Ku=_12K(_1Ko,_);return new T2(0,_1Ks,_1Kr);}else{return new T2(0,_1Ks,_1Kr);}},_1Kv=new T(function(){return unCStr("hGetPosn");}),_1Kw=function(_1Kx){return (E(_1Kx)==( -1))?true:false;},_1Ky=function(_1Kz,_){var _1KA=_1AG(_1Kw,_1Kv,function(_){var _1KB=ghczuwrapperZC2ZCbaseZCSystemziPosixziInternalsZCSEEKzuCUR();return ghczuwrapperZC23ZCbaseZCSystemziPosixziInternalsZClseek(_1Kz,0,_1KB);},_);return new T(function(){return _aO(E(_1KA));});},_1KC=new T(function(){return unCStr("seek");}),_1KD=function(_1KE,_1KF,_1KG,_){var _1KH=_1AG(_1Kw,_1KC,function(_){var _1KI=_cr(_1KG);switch(E(_1KF)){case 0:var _1KJ=ghczuwrapperZC1ZCbaseZCSystemziPosixziInternalsZCSEEKzuSET();return ghczuwrapperZC23ZCbaseZCSystemziPosixziInternalsZClseek(_1KE,_1KI,_1KJ);case 1:var _1KK=ghczuwrapperZC2ZCbaseZCSystemziPosixziInternalsZCSEEKzuCUR();return ghczuwrapperZC23ZCbaseZCSystemziPosixziInternalsZClseek(_1KE,_1KI,_1KK);default:var _1KL=ghczuwrapperZC0ZCbaseZCSystemziPosixziInternalsZCSEEKzuEND();return ghczuwrapperZC23ZCbaseZCSystemziPosixziInternalsZClseek(_1KE,_1KI,_1KL);}},_);return 0;},_1KM=function(_1KN){return (E(_1KN)==( -1))?true:false;},_1KO=new T(function(){return unCStr("fdType");}),_1KP=new T(function(){return _1K(new T6(0,__Z,15,_1KO,new T(function(){return unCStr("unknown file type");}),__Z,__Z));}),_1KQ=function(_1KR,_){var _1KS=__hscore_sizeof_stat(),_1KT=newByteArr(_1KS),_1KU=_1KT,_1KV=_1AG(_1KM,_1KO,function(_){return __hscore_fstat(E(_1KR),_1KU);},_),_1KW=__hscore_st_mode(_1KU),_1KX=ghczuwrapperZC5ZCbaseZCSystemziPosixziInternalsZCSzuISDIR(_1KW);if(!E(_1KX)){var _1KY=ghczuwrapperZC4ZCbaseZCSystemziPosixziInternalsZCSzuISFIFO(_1KW);if(!E(_1KY)){var _1KZ=ghczuwrapperZC3ZCbaseZCSystemziPosixziInternalsZCSzuISSOCK(_1KW);if(!E(_1KZ)){var _1L0=ghczuwrapperZC7ZCbaseZCSystemziPosixziInternalsZCSzuISCHR(_1KW);if(!E(_1L0)){var _1L1=ghczuwrapperZC8ZCbaseZCSystemziPosixziInternalsZCSzuISREG(_1KW);if(!E(_1L1)){var _1L2=ghczuwrapperZC6ZCbaseZCSystemziPosixziInternalsZCSzuISBLK(_1KW);if(!E(_1L2)){return die(_1KP);}else{var _1L3=__hscore_st_dev(_1KU),_1L4=__hscore_st_ino(_1KU);return new T3(0,3,_1L3,_1L4);}}else{var _1L5=__hscore_st_dev(_1KU),_1L6=__hscore_st_ino(_1KU);return new T3(0,2,_1L5,_1L6);}}else{var _1L7=__hscore_st_dev(_1KU),_1L8=__hscore_st_ino(_1KU);return new T3(0,1,_1L7,_1L8);}}else{var _1L9=__hscore_st_dev(_1KU),_1La=__hscore_st_ino(_1KU);return new T3(0,1,_1L9,_1La);}}else{var _1Lb=__hscore_st_dev(_1KU),_1Lc=__hscore_st_ino(_1KU);return new T3(0,1,_1Lb,_1Lc);}}else{var _1Ld=__hscore_st_dev(_1KU),_1Le=__hscore_st_ino(_1KU);return new T3(0,0,_1Ld,_1Le);}},_1Lf=function(_1Lg,_){var _1Lh=_1KQ(new T(function(){return E(_1Lg).a;}),_);return new T(function(){switch(E(E(_1Lh).a)){case 2:return true;break;case 3:return true;break;default:return false;}});},_1Li=function(_1Lj,_){var _1Lk=isatty(E(_1Lj).a);return new T(function(){if(!E(_1Lk)){return false;}else{return true;}});},_1Ll=new T(function(){return err(new T(function(){return unCStr("Prelude.Enum.Bool.toEnum: bad argument");}));}),_1Lm=new T(function(){return unCStr("GHC.IO.FD.ready");}),_1Ln=function(_1Lo,_1Lp,_1Lq,_){var _1Lr=_1AG(_1AD,_1Lm,function(_){if(!E(_1Lp)){return fdReady(_1Lo,0,_1Lq,0);}else{return fdReady(_1Lo,1,_1Lq,0);}},_);return new T(function(){switch(E(_1Lr)){case 0:return false;break;case 1:return true;break;default:return E(_1Ll);}});},_1Ls=new T(function(){return unCStr("GHC.IO.FD.dup");}),_1Lt=function(_1Lu,_1Lv,_){var _1Lw=dup(_1Lu),_1Lx=E(_1Lw);if(_1Lx==( -1)){var _1Ly=_12K(_1Ls,_);return new T(function(){return new T2(0,E(_1Ly),_1Lv);});}else{return new T2(0,_1Lx,_1Lv);}},_1Lz=function(_1LA,_){var _1LB=_1KQ(new T(function(){return E(_1LA).a;}),_);return E(_1LB).a;},_1LC=new T(function(){return unCStr("sigemptyset");}),_1LD=new T(function(){return unCStr("sigaddset");}),_1LE=new T(function(){return unCStr("sigprocmask");}),_1LF=new T(function(){return unCStr("tcSetAttr");}),_1LG=new T(function(){return _1K(new T6(0,__Z,3,new T(function(){return unCStr("malloc");}),new T(function(){return unCStr("out of memory");}),__Z,__Z));}),_1LH=function(_1LI,_1LJ,_){var _1LK=__hscore_sizeof_termios(),_1LL=newByteArr(_1LK),_1LM=_1LL,_1LN=_1AG(_1KM,_1LF,function(_){return ghczuwrapperZC11ZCbaseZCSystemziPosixziInternalsZCtcgetattr(E(_1LI),_1LM);},_),_1LO=E(_1LI),_1LP=function(_){var _1LQ=__hscore_sizeof_sigset_t(),_1LR=newByteArr(_1LQ),_1LS=_1LR,_1LT=newByteArr(_1LQ),_1LU=_1LT,_1LV=ghczuwrapperZC14ZCbaseZCSystemziPosixziInternalsZCsigemptyset(_1LS),_1LW=function(_){var _1LX=__hscore_sigttou(),_1LY=ghczuwrapperZC13ZCbaseZCSystemziPosixziInternalsZCsigaddset(_1LS,_1LX),_1LZ=function(_){var _1M0=__hscore_sig_block(),_1M1=ghczuwrapperZC12ZCbaseZCSystemziPosixziInternalsZCsigprocmask(_1M0,_1LS,_1LU),_1M2=function(_){var _1M3=B(A2(_1LJ,_1LM,_)),_1M4=_1AG(_1KM,_1LF,function(_){var _1M5=__hscore_tcsanow();return ghczuwrapperZC10ZCbaseZCSystemziPosixziInternalsZCtcsetattr(_1LO,_1M5,_1LM);},_),_1M6=__hscore_sig_setmask(),_1M7=ghczuwrapperZC12ZCbaseZCSystemziPosixziInternalsZCsigprocmask(_1M6,_1LU,0);if(E(_1M7)==( -1)){var _1M8=_12K(_1LE,_);return _1M3;}else{return _1M3;}};if(E(_1M1)==( -1)){var _1M9=_12K(_1LE,_);return _1M2(_);}else{return _1M2(_);}};if(E(_1LY)==( -1)){var _1Ma=_12K(_1LD,_);return _1LZ(_);}else{return _1LZ(_);}};if(E(_1LV)==( -1)){var _1Mb=_12K(_1LC,_);return _1LW(_);}else{return _1LW(_);}};if(_1LO>2){return C > 19 ? new F(function(){return _1LP(_);}) : (++C,_1LP(_));}else{var _1Mc=__hscore_get_saved_termios(_1LO);if(!addrEq(_1Mc,0)){return C > 19 ? new F(function(){return _1LP(_);}) : (++C,_1LP(_));}else{var _1Md=malloc(_1LK>>>0);if(!addrEq(_1Md,0)){var _1Me=memcpy(_1Md,_1LM,_1LK>>>0),_1Mf=__hscore_set_saved_termios(_1LO,_1Md);return C > 19 ? new F(function(){return _1LP(_);}) : (++C,_1LP(_));}else{return die(_1LG);}}}},_1Mg=new T(function(){var _1Mh=__hscore_icanon();return _1Mh>>>0;}),_1Mi=new T(function(){var _1Mj=__hscore_icanon();return (_1Mj>>>0^4294967295)>>>0;}),_1Mk=new T(function(){return __hscore_vtime();}),_1Ml=new T(function(){return __hscore_vmin();}),_1Mm=function(_1Mn,_1Mo,_){var _1Mp=function(_1Mq,_){var _1Mr=E(_1Mq),_1Ms=__hscore_lflag(_1Mr),_1Mt=function(_1Mu){var _1Mv=__hscore_poke_lflag(_1Mr,_1Mu);if(!E(_1Mo)){var _1Mw=__hscore_ptr_c_cc(_1Mr),_=writeOffAddr("w8",1,plusAddr(_1Mw,E(_1Ml)),0,1),_=writeOffAddr("w8",1,plusAddr(_1Mw,E(_1Mk)),0,0);return 0;}else{return 0;}};if(!E(_1Mo)){return _1Mt((_1Ms&E(_1Mi))>>>0);}else{return _1Mt((_1Ms|E(_1Mg))>>>0);}};return C > 19 ? new F(function(){return _1LH(_1Mn,_1Mp,_);}) : (++C,_1LH(_1Mn,_1Mp,_));},_1Mx=function(_1My,_1Mz,_){return C > 19 ? new F(function(){return _1Mm(new T(function(){return E(_1My).a;}),new T(function(){if(!E(_1Mz)){return true;}else{return false;}}),_);}) : (++C,_1Mm(new T(function(){return E(_1My).a;}),new T(function(){if(!E(_1Mz)){return true;}else{return false;}}),_));},_1MA=new T(function(){var _1MB=__hscore_echo();return _1MB>>>0;}),_1MC=function(_1MD,_){var _1ME=__hscore_lflag(E(_1MD));return new T(function(){if(!((_1ME&E(_1MA))>>>0)){return false;}else{return true;}});},_1MF=function(_1MG,_){return C > 19 ? new F(function(){return _1LH(new T(function(){return E(_1MG).a;}),_1MC,_);}) : (++C,_1LH(new T(function(){return E(_1MG).a;}),_1MC,_));},_1MH=new T(function(){var _1MI=__hscore_echo();return (_1MI>>>0^4294967295)>>>0;}),_1MJ=function(_1MK,_1ML,_){return C > 19 ? new F(function(){return _1LH(_1MK,function(_1MM,_){var _1MN=E(_1MM),_1MO=__hscore_lflag(_1MN);if(!E(_1ML)){var _1MP=__hscore_poke_lflag(_1MN,(_1MO&E(_1MH))>>>0);return 0;}else{var _1MQ=__hscore_poke_lflag(_1MN,(_1MO|E(_1MA))>>>0);return 0;}},_);}) : (++C,_1LH(_1MK,function(_1MM,_){var _1MN=E(_1MM),_1MO=__hscore_lflag(_1MN);if(!E(_1ML)){var _1MP=__hscore_poke_lflag(_1MN,(_1MO&E(_1MH))>>>0);return 0;}else{var _1MQ=__hscore_poke_lflag(_1MN,(_1MO|E(_1MA))>>>0);return 0;}},_));},_1MR=function(_1MS,_1MT,_){return C > 19 ? new F(function(){return _1MJ(new T(function(){return E(_1MS).a;}),_1MT,_);}) : (++C,_1MJ(new T(function(){return E(_1MS).a;}),_1MT,_));},_1MU=new T(function(){return unCStr("GHC.IO.FD.setSize");}),_1MV=function(_1MW,_1MX,_){var _1MY=__hscore_ftruncate(_1MW,_cr(_1MX));if(!E(_1MY)){return 0;}else{var _1MZ=_12K(_1MU,_);return 0;}},_1N0=new T(function(){return unCStr("fileSize");}),_1N1=function(_1N2,_){var _1N3=__hscore_sizeof_stat(),_1N4=newByteArr(_1N3),_1N5=_1N4,_1N6=_1AG(_1KM,_1N0,function(_){return __hscore_fstat(E(_1N2),_1N5);},_),_1N7=__hscore_st_mode(_1N5),_1N8=ghczuwrapperZC8ZCbaseZCSystemziPosixziInternalsZCSzuISREG(_1N7);if(!E(_1N8)){return new T1(0, -1);}else{var _1N9=__hscore_st_size(_1N5);return new T(function(){return _aO(_1N9);});}},_1Na=function(_1Nb,_){return _1N1(new T(function(){return E(_1Nb).a;}),_);},_1Nc={_:0,a:function(_1Nd,_1Ne,_1Nf,_){return _1Ln(E(_1Nd).a,_1Ne,E(_1Nf),_);},b:function(_1Ng,_){return C > 19 ? new F(function(){return _1DH(E(_1Ng).a,_);}) : (++C,_1DH(E(_1Ng).a,_));},c:_1Li,d:_1Lf,e:function(_1Nh,_1Ni,_1Nj,_){return _1KD(E(_1Nh).a,_1Ni,_1Nj,_);},f:function(_1Nk,_){return _1Ky(E(_1Nk).a,_);},g:_1Na,h:function(_1Nl,_1Nm,_){return _1MV(E(_1Nl).a,_1Nm,_);},i:_1MR,j:_1MF,k:_1Mx,l:_1Lz,m:function(_1Nn,_){var _1No=E(_1Nn);return _1Lt(_1No.a,_1No.b,_);},n:function(_1Np,_1Nq,_){var _1Nr=E(_1Np);return _1Kp(_1Nr.a,_1Nr.b,E(_1Nq).a,_);}},_1Ns=new T(function(){return _1K(new T6(0,__Z,13,_1AC,new T(function(){return unCStr("is a directory");}),__Z,__Z));}),_1Nt=new T(function(){return unCStr("base");}),_1Nu=new T(function(){return unCStr("GHC.IO.FD");}),_1Nv=new T(function(){return unCStr("FD");}),_1Nw=function(_1Nx){return E(new T5(0,new Long(2302221327,4000630249,true),new Long(2077833458,4112603226,true),new T5(0,new Long(2302221327,4000630249,true),new Long(2077833458,4112603226,true),_1Nt,_1Nu,_1Nv),__Z,__Z));},_1Ny=new T(function(){return B(A2(_2b,_2a,new T(function(){return B(A1(_2d,new T(function(){return unCStr("Pattern match failure in do expression at GHC/IO/Handle/Internals.hs:672:3-35");})));})));}),_1Nz=new T(function(){return unCStr("Pattern match failure in do expression at GHC/IO/Handle/Internals.hs:678:3-33");}),_1NA=new T1(1,function(_1NB,_1NC,_){var _1ND=E(_1NC),_1NE=takeMVar(_1ND),_1NF=_1ez(_1NE,_),_=putMVar(_1ND,E(_1NF).a);return 0;}),_1NG=function(_1NH){return E(E(_1NH).c);},_1NI=function(_1NJ){return E(E(_1NJ).a);},_1NK=function(_1NL,_1NM,_1NN,_1NO,_1NP,_1NQ,_1NR,_1NS,_1NT,_1NU,_1NV,_){var _1NW=function(_1NX,_1NY,_){var _1NZ=new T(function(){if(E(_1NQ)==2){return 0;}else{return 1;}}),_1O0=B(A(_1NI,[_1NM,_1NO,_1NZ,_])),_1O1=nMV(_1O0),_1O2=_1O1,_1O3=nMV(new T2(0,_1go,_1O0)),_1O4=_1O3,_1O5=function(_,_1O6,_1O7){var _1O8=nMV(__Z),_1O9=newMVar(),_1Oa=new T(function(){return {_:0,a:_1NL,b:_1NM,c:_1NN,d:E(_1NO),e:_1NQ,f:_1O2,g:_1O7,h:_1O4,i:E(_1O6),j:_1O8,k:_1NX,l:_1NY,m:_1NS,n:new T(function(){return E(E(_1NT).a);}),o:new T(function(){return E(E(_1NT).b);}),p:_1NV};}),_=putMVar(_1O9,_1Oa),_1Ob=E(_1NU);if(!_1Ob._){return new T2(0,_1NP,_1O9);}else{var _1Oc=mkWeak(_1O9,0,new T(function(){return B(A2(_1Ob.a,_1NP,_1O9));}));return new T2(0,_1NP,_1O9);}};if(!E(_1NR)){var _1Od=nMV(__Z),_1Oe=newByteArr(8192),_1Of=nMV(new T6(0,_1Oe,new T2(1,_1Oe,_1Od),_1NZ,2048,0,0));return _1O5(_,_1Of,__Z);}else{var _1Og=nMV(__Z),_1Oh=newByteArr(8192),_1Oi=nMV(new T6(0,_1Oh,new T2(1,_1Oh,_1Og),_1NZ,2048,0,0)),_1Oj=B(A3(_1NG,_1NL,_1NO,_));return _1O5(_,_1Oi,new T(function(){if(!E(_1Oj)){return E(new T1(2,__Z));}else{return new T0(1);}}));}},_1Ok=E(_1NS);if(!_1Ok._){return _1NW(__Z,__Z,_);}else{var _1Ol=E(_1Ok.a),_1Om=_1Ol.b,_1On=_1Ol.c,_1Oo=function(_,_1Op){switch(E(_1NQ)){case 3:var _1Oq=B(A1(_1On,_));return _1NW(new T1(1,_1Oq),_1Op,_);case 4:var _1Or=B(A1(_1On,_));return _1NW(new T1(1,_1Or),_1Op,_);case 5:var _1Os=B(A1(_1On,_));return _1NW(new T1(1,_1Os),_1Op,_);default:return _1NW(__Z,_1Op,_);}};switch(E(_1NQ)){case 2:var _1Ot=B(A1(_1Om,_));return _1Oo(_,new T1(1,_1Ot));case 5:var _1Ou=B(A1(_1Om,_));return _1Oo(_,new T1(1,_1Ou));default:return _1Oo(_,__Z);}}},_1Ov=function(_1Ow,_1Ox,_1Oy,_1Oz,_1OA,_1OB,_1OC,_){var _1OD=B(_1NK(_1Ow,_1Ox,_1Oy,_1Oz,_1OA,3,true,_1OB,_1OC,_1NA,__Z,_)),_1OE=E(_1OD);if(!_1OE._){var _1OF=_1OE.b,_1OG=B(_1NK(_1Ow,_1Ox,_1Oy,_1Oz,_1OA,2,true,_1OB,_1OC,__Z,new T1(1,_1OF),_)),_1OH=E(_1OG);if(!_1OH._){return new T3(1,_1OA,_1OH.b,_1OF);}else{return _2f(_1Nz,_);}}else{return die(_1Ny);}},_1OI=new T(function(){return unCStr("setNonBlockingFD");}),_1OJ=function(_1OK,_1OL,_1OM,_1ON,_1OO,_1OP,_){var _1OQ=function(_,_1OR){var _1OS=new T(function(){var _1OT=E(_1OP);return E(new T2(0,0,0));}),_1OU=function(_){return C > 19 ? new F(function(){return _1NK(_1Nc,_1K0,_1Nw,_1OR,_1OM,new T(function(){switch(E(_1ON)){case 0:return 2;break;case 1:return 3;break;case 2:return 4;break;default:return 5;}}),true,_1OP,_1OS,_1NA,__Z,_);}) : (++C,_1NK(_1Nc,_1K0,_1Nw,_1OR,_1OM,new T(function(){switch(E(_1ON)){case 0:return 2;break;case 1:return 3;break;case 2:return 4;break;default:return 5;}}),true,_1OP,_1OS,_1NA,__Z,_));};switch(E(_1OL)){case 0:return die(_1Ns);case 1:if(E(_1ON)==3){return _1Ov(_1Nc,_1K0,_1Nw,_1OR,_1OM,_1OP,_1OS,_);}else{return C > 19 ? new F(function(){return _1OU(_);}) : (++C,_1OU(_));}break;default:return C > 19 ? new F(function(){return _1OU(_);}) : (++C,_1OU(_));}};if(!E(_1OO)){return C > 19 ? new F(function(){return _1OQ(_,_1OK);}) : (++C,_1OQ(_,_1OK));}else{var _1OV=E(_1OK).a,_1OW=_1AG(_1KM,_1OI,function(_){var _1OX=__hscore_f_getfl();return ghczuwrapperZC18ZCbaseZCSystemziPosixziInternalsZCfcntl(_1OV,_1OX);},_),_1OY=E(_1OW),_1OZ=__hscore_o_nonblock(),_1P0=(_1OY>>>0|_1OZ>>>0)>>>0&4294967295;if(_1OY!=_1P0){var _1P1=__hscore_f_setfl(),_1P2=ghczuwrapperZC17ZCbaseZCSystemziPosixziInternalsZCfcntl(_1OV,_1P1,_1P0);return C > 19 ? new F(function(){return _1OQ(_,new T2(0,_1OV,1));}) : (++C,_1OQ(_,new T2(0,_1OV,1)));}else{return C > 19 ? new F(function(){return _1OQ(_,new T2(0,_1OV,1));}) : (++C,_1OQ(_,new T2(0,_1OV,1)));}}},_1P3=new T(function(){return _12n(function(_){return _12t(0,_12q,0);});}),_1P4=function(_){var _1P5=nMV(_1P3),_1P6=_1P5;return new T2(0,function(_){return rMV(_1P6);},function(_1P7,_){var _=wMV(_1P6,_1P7);return 0;});},_1P8=new T(function(){return _12n(_1P4);}),_1P9=function(_1Pa){var _1Pb=hs_int64ToWord64(_1Pa);return E(_1Pb);},_1Pc=function(_1Pd){var _1Pe=E(_1Pd);if(!_1Pe._){var _1Pf=hs_intToInt64(_1Pe.a);return _1P9(_1Pf);}else{return I_toWord64(_1Pe.a);}},_1Pg=new T(function(){return unCStr("openFile");}),_1Ph=new T(function(){return _1K(new T6(0,__Z,13,_1Pg,new T(function(){return unCStr("is a directory");}),__Z,__Z));}),_1Pi=new T(function(){return _1K(new T6(0,__Z,2,_1Pg,new T(function(){return unCStr("file is locked");}),__Z,__Z));}),_1Pj=function(_1Pk){return new T1(1,I_fromInt(_1Pk));},_1Pl=function(_1Pm,_1Pn,_1Po,_1Pp,_){var _1Pq=function(_,_1Pr,_1Ps,_1Pt){var _1Pu=E(_1Pr);switch(_1Pu){case 0:return die(_1Ph);case 2:var _1Pv=E(_1Pm),_1Pw=E(_1Ps),_1Px=_1Pw&4294967295,_1Py=function(_1Pz){var _1PA=E(_1Pt),_1PB=_1PA&4294967295,_1PC=function(_1PD){if(!E(_1Pn)){var _1PE=lockFile(_1Pv,_1Pz,_1PD,0);if(E(_1PE)==( -1)){return die(_1Pi);}else{return new T2(0,new T(function(){if(!E(_1Pp)){return new T2(0,_1Pv,0);}else{return new T2(0,_1Pv,1);}}),2);}}else{var _1PF=lockFile(_1Pv,_1Pz,_1PD,1);if(E(_1PF)==( -1)){return die(_1Pi);}else{return new T2(0,new T(function(){if(!E(_1Pp)){return new T2(0,_1Pv,0);}else{return new T2(0,_1Pv,1);}}),2);}}};if(_1PB<0){return _1PC(_1Pc(_1Pj(_1PA)));}else{return _1PC(_1Pc(_aO(_1PB)));}};if(_1Px<0){return _1Py(_1Pc(_1Pj(_1Pw)));}else{return _1Py(_1Pc(_aO(_1Px)));}break;default:return new T2(0,new T(function(){var _1PG=E(_1Pm);if(!E(_1Pp)){return new T2(0,_1PG,0);}else{return new T2(0,_1PG,1);}}),_1Pu);}},_1PH=E(_1Po);if(!_1PH._){var _1PI=_1KQ(_1Pm,_),_1PJ=E(_1PI);return C > 19 ? new F(function(){return _1Pq(_,_1PJ.a,_1PJ.b,_1PJ.c);}) : (++C,_1Pq(_,_1PJ.a,_1PJ.b,_1PJ.c));}else{var _1PK=E(_1PH.a);return C > 19 ? new F(function(){return _1Pq(_,_1PK.a,_1PK.b,_1PK.c);}) : (++C,_1Pq(_,_1PK.a,_1PK.b,_1PK.c));}},_1PL=new T(function(){var _1PM=__hscore_o_noctty(),_1PN=__hscore_o_creat();return (_1PM>>>0|_1PN>>>0)>>>0&4294967295;}),_1PO=new T(function(){var _1PP=__hscore_o_wronly();return (E(_1PL)>>>0|_1PP>>>0)>>>0&4294967295;}),_1PQ=new T(function(){var _1PR=__hscore_o_append();return (E(_1PO)>>>0|_1PR>>>0)>>>0&4294967295;}),_1PS=new T(function(){var _1PT=__hscore_o_noctty(),_1PU=__hscore_o_rdonly();return (_1PT>>>0|_1PU>>>0)>>>0&4294967295;}),_1PV=new T(function(){var _1PW=__hscore_o_rdwr();return (E(_1PL)>>>0|_1PW>>>0)>>>0&4294967295;}),_1PX=function(_1PY,_1PZ,_){return die(new T(function(){return B(A2(_2b,_1PY,_1PZ));}));},_1Q0=function(_1Q1,_1Q2,_1Q3,_){var _1Q4=B(A1(E(_1dA).a,_)),_1Q5=new T(function(){switch(E(_1Q2)){case 0:var _1Q6=__hscore_o_nonblock();return (E(_1PS)>>>0|_1Q6>>>0)>>>0&4294967295;break;case 1:var _1Q7=__hscore_o_nonblock();return (E(_1PO)>>>0|_1Q7>>>0)>>>0&4294967295;break;case 2:var _1Q8=__hscore_o_nonblock();return (E(_1PQ)>>>0|_1Q8>>>0)>>>0&4294967295;break;default:var _1Q9=__hscore_o_nonblock();return (E(_1PV)>>>0|_1Q9>>>0)>>>0&4294967295;}}),_1Qa=function(_1Qb,_){var _1Qc=function(_1Qd){var _1Qe=E(_1Qd);return function(_){var _1Qf=close(E(_1Qb));return _1PX(_1Qe.a,_1Qe.b,_);};},_1Qg=jsCatch(function(_){return C > 19 ? new F(function(){return _1Pl(_1Qb,_1Q2,__Z,_1Q3,_);}) : (++C,_1Pl(_1Qb,_1Q2,__Z,_1Q3,_));},_1Qc),_1Qh=E(_1Qg),_1Qi=_1Qh.a;if(E(_1Q2)==1){switch(E(_1Qh.b)){case 0:return new T2(0,_1Qi,0);case 1:return new T2(0,_1Qi,1);case 2:var _1Qj=E(_1Qi),_1Qk=__hscore_ftruncate(_1Qj.a,0);if(!E(_1Qk)){return new T2(0,_1Qj,2);}else{var _1Ql=_12K(_1MU,_);return new T2(0,_1Qj,2);}break;default:return new T2(0,_1Qi,3);}}else{return _1Qg;}},_1Qm=function(_1Qn,_){if(!E(_1Q3)){var _1Qo=_1AG(_1AD,_1Pg,function(_){var _1Qp=E(_1Qn);switch(E(_1Q2)){case 0:return __hscore_open(_1Qp,E(_1PS),438);case 1:return __hscore_open(_1Qp,E(_1PO),438);case 2:return __hscore_open(_1Qp,E(_1PQ),438);default:return __hscore_open(_1Qp,E(_1PV),438);}},_);return _1Qa(_1Qo,_);}else{var _1Qq=_1AG(_1AD,_1Pg,function(_){return __hscore_open(E(_1Qn),E(_1Q5),438);},_);return _1Qa(_1Qq,_);}};return _YU(_1Q4,_1Q1,_1Qm,_);},_1Qr=function(_1Qs,_1Qt,_1Qu,_1Qv,_){var _1Qw=B(_1Q0(_1Qs,_1Qt,_1Qv,_)),_1Qx=E(_1Qw),_1Qy=_1Qx.a,_1Qz=function(_,_1QA){return jsCatch(function(_){return C > 19 ? new F(function(){return _1OJ(_1Qy,_1Qx.b,_1Qs,_1Qt,false,_1QA,_);}) : (++C,_1OJ(_1Qy,_1Qx.b,_1Qs,_1Qt,false,_1QA,_));},function(_1QB,_){var _1QC=B(_1DH(E(_1Qy).a,_));return die(_1QB);});};if(!E(_1Qu)){var _1QD=B(A1(E(_1P8).a,_));return _1Qz(_,new T1(1,_1QD));}else{return _1Qz(_,__Z);}},_1QE=function(_1QF,_1QG,_){var _1QH=function(_1QI,_){var _1QJ=E(_1QI),_1QK=B(A2(_M,_1QJ.a,_)),_1QL=hs_eqWord64(_1QK.a,new Long(4053623282,1685460941,true));if(!_1QL){return die(_1QJ);}else{var _1QM=hs_eqWord64(_1QK.b,new Long(3693590983,2507416641,true));if(!_1QM){return die(_1QJ);}else{var _1QN=new T(function(){return _1K(new T(function(){var _1QO=E(_1QJ.b);return new T6(0,_1QO.a,_1QO.b,_1AC,_1QO.d,_1QO.e,new T1(1,_1QF));}));});return die(_1QN);}}};return jsCatch(function(_){return _1Qr(_1QF,_1QG,false,true,_);},_1QH);},_1QP=function(_1QQ){return E(E(_1QQ).e);},_1QR=function(_1QS,_1QT,_1QU){var _1QV=function(_1QW){var _1QX=new T(function(){var _1QY=E(E(_1QW).b),_1QZ=function(_1R0){return C > 19 ? new F(function(){return A1(_1QY.d,new T(function(){return B(A2(_1QS,_1QU,_1R0));}));}) : (++C,A1(_1QY.d,new T(function(){return B(A2(_1QS,_1QU,_1R0));})));};return new T4(0,_1QY.a,_1QY.b,_1QY.c,_1QZ);});return new T3(0,0,_1QX,_2L);};return C > 19 ? new F(function(){return A2(_1QP,_1QT,_1QV);}) : (++C,A2(_1QP,_1QT,_1QV));},_1R1=function(_1R2,_1R3){return new T3(0,_1R2,new T(function(){return E(E(_1R3).b);}),_2L);},_1R4=function(_1R5,_1R6,_1R7){var _1R8=new T(function(){return B(A1(_1R6,_1R7));}),_1R9=new T(function(){return B(A1(_1R5,new T(function(){return E(E(_1R8).a);})));});return new T3(0,_1R9,new T(function(){return E(E(_1R8).b);}),new T(function(){return E(E(_1R8).c);}));},_1Ra=new T(function(){return _no(new T(function(){return _nx(new T(function(){return _mN(_1R1,new T(function(){return _nC(_1R4,_4S);}),_4S);}),_4S);}),_4S);}),_1Rb=new T(function(){return _H7(_GV);}),_1Rc=new T(function(){return _H5(_mc);}),_1Rd=function(_1Re){var _1Rf=E(_1Re);return (_1Rf._==0)?(E(_1Rf.a)==0)?__Z:new T2(1,_1Rf.c,new T(function(){return _1Rd(_1Rf.d);})):__Z;},_1Rg=function(_1Rh){var _1Ri=E(_1Rh);return (_1Ri._==0)?__Z:new T2(1,new T1(2,new T(function(){return _nO(_1Ri.a);})),new T(function(){return _1Rg(_1Ri.b);}));},_1Rj=function(_1Rk){return false;},_1Rl=function(_1Rm){var _1Rn=E(_1Rm);return (_1Rn._==0)?__Z:new T2(1,_1Rj,new T(function(){return _1Rl(_1Rn.b);}));},_1Ro=function(_1Rp){var _1Rq=E(_1Rp);return (_1Rq._==0)?__Z:new T2(1,new T(function(){return _3W(_1Rq.a);}),new T(function(){return _1Ro(_1Rq.b);}));},_1Rr=function(_1Rs){var _1Rt=E(_1Rs);return (_1Rt._==0)?__Z:new T2(1,new T(function(){return _3W(_1Rt.a);}),new T(function(){return _1Rr(_1Rt.b);}));},_1Ru=function(_1Rv){var _1Rw=E(_1Rv);return (_1Rw._==0)?__Z:new T2(1,new T(function(){return _3W(_1Rw.a);}),new T(function(){return _1Ru(_1Rw.b);}));},_1Rx=function(_1Ry){var _1Rz=E(_1Ry);return (_1Rz._==0)?__Z:new T2(1,new T(function(){return _nO(_1Rz.a);}),new T(function(){return _1Rx(_1Rz.b);}));},_1RA=function(_1RB){var _1RC=E(_1RB);return (_1RC._==0)?__Z:new T2(1,new T(function(){return _3W(_1RC.a);}),new T(function(){return _1RA(_1RC.b);}));},_1RD=function(_1RE){var _1RF=E(_1RE);return (_1RF._==0)?__Z:new T2(1,new T(function(){return _3W(_1RF.a);}),new T(function(){return _1RD(_1RF.b);}));},_1RG=function(_1RH){while(1){var _1RI=(function(_1RJ){var _1RK=E(_1RJ);if(!_1RK._){return __Z;}else{var _1RL=_1RK.b,_1RM=E(_1RK.a);if(!E(_1RM.b)._){return new T2(1,_1RM.a,new T(function(){return _1RG(_1RL);}));}else{_1RH=_1RL;return __continue;}}})(_1RH);if(_1RI!=__continue){return _1RI;}}},_1RN=function(_1RO){return E(E(_1RO).f);},_1RP=function(_1RQ){return E(E(_1RQ).d);},_1RR=new T(function(){return _mo(new T(function(){return unCStr("tail");}));}),_1RS=function(_1RT,_1RU,_1RV){var _1RW=E(_1RV),_1RX=new T(function(){return B(A3(_SJ,_SE,new T2(1,new T(function(){return B(A3(_SR,_1RT,0,_1RW.a));}),new T2(1,new T(function(){return B(A3(_SR,_1RU,0,_1RW.b));}),__Z)),new T2(1,41,__Z)));});return new T2(1,40,_1RX);},_1RY=function(_1RZ,_1S0,_1S1,_1S2){var _1S3=function(_1S4,_1S5){var _1S6=E(_1S4),_1S7=new T(function(){return B(A3(_SJ,_SE,new T2(1,new T(function(){return B(A3(_SR,_1RZ,0,_1S6.a));}),new T2(1,new T(function(){return B(A3(_SR,_1S0,0,_1S6.b));}),__Z)),new T2(1,41,_1S5)));});return new T2(1,40,_1S7);};return _1R(_1S3,_1S1,_1S2);},_1S8=function(_1S9,_1Sa,_1Sb,_1Sc,_1Sd){var _1Se=E(_1Sc),_1Sf=new T(function(){return B(A3(_SJ,_SE,new T2(1,new T(function(){return B(A3(_SR,_1S9,0,_1Se.a));}),new T2(1,new T(function(){return B(A3(_SR,_1Sa,0,_1Se.b));}),__Z)),new T2(1,41,_1Sd)));});return new T2(1,40,_1Sf);},_1Sg=function(_1Sh,_1Si){return new T3(0,function(_1Sj,_1Sk,_1Sl){return _1S8(_1Sh,_1Si,_1Sj,_1Sk,_1Sl);},function(_1Sl){return _1RS(_1Sh,_1Si,_1Sl);},function(_1Sk,_1Sl){return _1RY(_1Sh,_1Si,_1Sk,_1Sl);});},_1Sm=new T(function(){return unCStr("COCB_Format");}),_1Sn=new T(function(){return unCStr("COCB_InsertNodeDir");}),_1So=new T(function(){return unCStr("COCB_SetShowDir");}),_1Sp=new T(function(){return unCStr("COCB_GetShowDir");}),_1Sq=new T(function(){return unCStr("COCB_ContextVars");}),_1Sr=new T(function(){return unCStr("COCB_Rename");}),_1Ss=new T(function(){return unCStr("COCB_Subst");}),_1St=new T(function(){return unCStr("COCB_HypBefore");}),_1Su=new T(function(){return unCStr("COCB_Mu");}),_1Sv=new T(function(){return unCStr("COCB_TypeOf");}),_1Sw=new T(function(){return unCStr("COCB_Bind ");}),_1Sx=new T(function(){return unCStr("COCB_Ap");}),_1Sy=new T(function(){return unCStr("COCB_Var");}),_1Sz=new T(function(){return unCStr("COCB_Quit");}),_1SA=new T(function(){return unCStr("COCB_Hyp");}),_1SB=new T(function(){return unCStr("COCB_Uni");}),_1SC=new T(function(){return unCStr("COCB_Concat");}),_1SD=new T(function(){return unCStr("COCB_ToInt");}),_1SE=new T(function(){return unCStr("COCB_GetEnv");}),_1SF=new T(function(){return unCStr("COCB_ExecModule");}),_1SG=new T(function(){return unCStr("COCB_Open");}),_1SH=new T(function(){return unCStr("COCB_Print");}),_1SI=new T(function(){return unCStr("True");}),_1SJ=new T(function(){return unCStr("False");}),_1SK=function(_1SL,_1SM,_1SN){var _1SO=E(_1SM);switch(_1SO._){case 0:return _0(_1SH,_1SN);case 1:return _0(_1SG,_1SN);case 2:return _0(_1SF,_1SN);case 3:return _0(_1SE,_1SN);case 4:return _0(_1SD,_1SN);case 5:return _0(_1SC,_1SN);case 6:return _0(_1SB,_1SN);case 7:return _0(_1SA,_1SN);case 8:return _0(_1Sz,_1SN);case 9:return _0(_1Sy,_1SN);case 10:return _0(_1Sx,_1SN);case 11:var _1SP=function(_1SQ){var _1SR=new T(function(){var _1SS=new T(function(){if(!E(_1SO.b)){return _0(_SC,_1SQ);}else{return _0(_SB,_1SQ);}});if(!E(_1SO.a)){return _0(_1SJ,new T2(1,32,_1SS));}else{return _0(_1SI,new T2(1,32,_1SS));}},1);return _0(_1Sw,_1SR);};if(E(_1SL)<11){return _1SP(_1SN);}else{return new T2(1,40,new T(function(){return _1SP(new T2(1,41,_1SN));}));}break;case 12:return _0(_1Sv,_1SN);case 13:return _0(_1Su,_1SN);case 14:return _0(_1St,_1SN);case 15:return _0(_1Ss,_1SN);case 16:return _0(_1Sr,_1SN);case 17:return _0(_1Sq,_1SN);case 18:return _0(_1Sp,_1SN);case 19:return _0(_1So,_1SN);case 20:return _0(_1Sn,_1SN);default:return _0(_1Sm,_1SN);}},_1ST=function(_1SU,_1k5){return _1SK(0,_1SU,_1k5);},_1SV=new T3(0,_1SK,function(_1SW){return _1SK(0,_1SW,__Z);},function(_1SU,_1k5){return _1R(_1ST,_1SU,_1k5);}),_1SX=function(_1SY,_1SZ){return C > 19 ? new F(function(){return A(_1T0,[_1SY,0,_1SZ,__Z]);}) : (++C,A(_1T0,[_1SY,0,_1SZ,__Z]));},_1T1=function(_1T2){var _1T3=new T(function(){return B(A2(_1T0,_1T2,0));});return function(_3v,_1T4){return _1R(_1T3,_3v,_1T4);};},_1T5=function(_1T6){return new T3(0,new T(function(){return _1T0(_1T6);}),function(_He){return C > 19 ? new F(function(){return _1SX(_1T6,_He);}) : (++C,_1SX(_1T6,_He));},new T(function(){return _1T1(_1T6);}));},_1T7=new T(function(){return unCStr("Step ");}),_1T8=function(_1T9,_1Ta,_1Tb,_1Tc,_1Td){var _1Te=new T(function(){return B(A3(_SR,_1T9,11,_1Tc));}),_1Tf=new T(function(){return B(A3(_SR,_1Ta,11,_1Td));});if(_1Tb<11){var _1Tg=function(_1Th){var _1Ti=new T(function(){return B(A1(_1Te,new T2(1,32,new T(function(){return B(A1(_1Tf,_1Th));}))));},1);return _0(_1T7,_1Ti);};return _1Tg;}else{var _1Tj=function(_1Tk){var _1Tl=new T(function(){var _1Tm=new T(function(){return B(A1(_1Te,new T2(1,32,new T(function(){return B(A1(_1Tf,new T2(1,41,_1Tk)));}))));},1);return _0(_1T7,_1Tm);});return new T2(1,40,_1Tl);};return _1Tj;}},_1Tn=function(_1To,_1Tp,_1Tq){var _1Tr=E(_1Tq);return C > 19 ? new F(function(){return A(_1T8,[_1To,_1Tp,0,_1Tr.a,_1Tr.b,__Z]);}) : (++C,A(_1T8,[_1To,_1Tp,0,_1Tr.a,_1Tr.b,__Z]));},_1Ts=function(_1Tt,_1Tu,_1Tv,_1Tw){return _1R(function(_1Tx){var _1Ty=E(_1Tx);return _1T8(_1Tt,_1Tu,0,_1Ty.a,_1Ty.b);},_1Tv,_1Tw);},_1Tz=function(_1TA,_1TB,_1TC,_1TD){var _1TE=E(_1TD);return _1T8(_1TA,_1TB,E(_1TC),_1TE.a,_1TE.b);},_1TF=function(_1TG,_1TH){return new T3(0,function(_1TI,_JJ){return _1Tz(_1TG,_1TH,_1TI,_JJ);},function(_JJ){return C > 19 ? new F(function(){return _1Tn(_1TG,_1TH,_JJ);}) : (++C,_1Tn(_1TG,_1TH,_JJ));},function(_1TI,_JJ){return _1Ts(_1TG,_1TH,_1TI,_JJ);});},_1TJ=new T(function(){return unCStr("Just ");}),_1TK=new T(function(){return unCStr("Nothing");}),_1TL=function(_1TM,_1TN){var _1TO=E(_1TN);if(!_1TO._){return E(_1TK);}else{return _0(_1TJ,new T(function(){return B(A(_SR,[_1TM,11,_1TO.a,__Z]));},1));}},_1TP=function(_1Sl){return _0(_1TK,_1Sl);},_1TQ=function(_1TR,_1TS,_1TT){var _1TU=E(_1TT);if(!_1TU._){return _1TP;}else{var _1TV=new T(function(){return B(A3(_SR,_1TR,11,_1TU.a));});if(E(_1TS)<11){var _1TW=function(_1TX){return _0(_1TJ,new T(function(){return B(A1(_1TV,_1TX));},1));};return _1TW;}else{var _1TY=function(_1TZ){var _1U0=new T(function(){return _0(_1TJ,new T(function(){return B(A1(_1TV,new T2(1,41,_1TZ)));},1));});return new T2(1,40,_1U0);};return _1TY;}}},_1U1=function(_1U2,_1U3,_1U4){return _1R(function(_1Sl){return _1TQ(_1U2,0,_1Sl);},_1U3,_1U4);},_1U5=function(_1U6){return new T3(0,function(_1Sk,_1Sl){return _1TQ(_1U6,_1Sk,_1Sl);},function(_1Sl){return _1TL(_1U6,_1Sl);},function(_1Sk,_1Sl){return _1U1(_1U6,_1Sk,_1Sl);});},_1U7=function(_1U8,_1U9){return C > 19 ? new F(function(){return A(_1Ua,[_1U8,0,_1U9,__Z]);}) : (++C,A(_1Ua,[_1U8,0,_1U9,__Z]));},_1Ub=function(_1Uc){var _1Ud=new T(function(){return B(A2(_1Ua,_1Uc,0));});return function(_3v,_1T4){return _1R(_1Ud,_3v,_1T4);};},_1Ue=function(_1Uf){return new T3(0,new T(function(){return _1Ua(_1Uf);}),function(_He){return C > 19 ? new F(function(){return _1U7(_1Uf,_He);}) : (++C,_1U7(_1Uf,_He));},new T(function(){return _1Ub(_1Uf);}));},_1Ug=new T(function(){return unCStr("fromList ");}),_1Uh=function(_1Ui,_1Uj,_1Uk,_1Ul){var _1Um=new T(function(){return _mR(__Z,_1Ul);}),_1Un=function(_1Uo,_1Up){var _1Uq=E(_1Uo),_1Ur=new T(function(){return B(A3(_SJ,_SE,new T2(1,new T(function(){return B(A3(_SR,_1Ui,0,_1Uq.a));}),new T2(1,new T(function(){return B(A3(_SR,_1Uj,0,_1Uq.b));}),__Z)),new T2(1,41,_1Up)));});return new T2(1,40,_1Ur);};if(_1Uk<=10){var _1Us=function(_1Ut){return _0(_1Ug,new T(function(){return _1R(_1Un,_1Um,_1Ut);},1));};return _1Us;}else{var _1Uu=function(_1Uv){var _1Uw=new T(function(){return _0(_1Ug,new T(function(){return _1R(_1Un,_1Um,new T2(1,41,_1Uv));},1));});return new T2(1,40,_1Uw);};return _1Uu;}},_1Ux=new T(function(){return unCStr("AHDir ");}),_1T0=function(_1Uy){var _1Uz=new T(function(){return _1Ue(_1UA);}),_1UA=new T(function(){return _1TF(new T(function(){return _1U5(_1Uy);}),_1Uz);}),_1UB=new T(function(){return _1T5(_1UA);}),_1UC=function(_1UD,_1UE){var _1UF=E(_1UE),_1UG=new T(function(){return _1Uh(_1Cb,_1Uy,11,_1UF.a);}),_1UH=new T(function(){return _1Uh(_1Cb,_1UB,11,_1UF.b);});if(E(_1UD)<11){var _1UI=function(_1UJ){var _1UK=new T(function(){return B(A1(_1UG,new T2(1,32,new T(function(){return B(A1(_1UH,_1UJ));}))));},1);return _0(_1Ux,_1UK);};return _1UI;}else{var _1UL=function(_1UM){var _1UN=new T(function(){var _1UO=new T(function(){return B(A1(_1UG,new T2(1,32,new T(function(){return B(A1(_1UH,new T2(1,41,_1UM)));}))));},1);return _0(_1Ux,_1UO);});return new T2(1,40,_1UN);};return _1UL;}};return _1UC;},_1UP=function(_1UQ){return (E(_1UQ)==0)?E(_SC):E(_SB);},_1UR=function(_1US,_1UT){if(!E(_1US)){return _0(_SC,_1UT);}else{return _0(_SB,_1UT);}},_1UU=function(_Hd,_He){return _1R(_1UR,_Hd,_He);},_1UV=function(_1UW,_1UX,_1UY){if(!E(_1UX)){return _0(_SC,_1UY);}else{return _0(_SB,_1UY);}},_1UZ=new T(function(){return unCStr("NodeDir ");}),_1Ua=function(_1V0){var _1V1=new T(function(){return _1Ue(new T(function(){return _1Ue(_1V0);}));}),_1V2=new T(function(){return _1Ue(_1V3);}),_1V3=new T(function(){return _1TF(new T(function(){return _1U5(_1V0);}),_1V2);}),_1V4=new T(function(){return _1T0(_1V3);}),_1V5=function(_1V6,_1V7){var _1V8=E(_1V7),_1V9=new T(function(){return _1Uh(new T3(0,_1UV,_1UP,_1UU),_1V1,11,_1V8.a);}),_1Va=new T(function(){return B(A2(_1V4,11,_1V8.b));}),_1Vb=new T(function(){return _1Uh(_1Cb,_1V0,11,_1V8.c);}),_1Vc=function(_1Vd){var _1Ve=new T(function(){var _1Vf=new T(function(){return B(A1(_1Va,new T2(1,32,new T(function(){return B(A1(_1Vb,_1Vd));}))));});return B(A1(_1V9,new T2(1,32,_1Vf)));},1);return _0(_1UZ,_1Ve);};if(E(_1V6)<11){return _1Vc;}else{var _1Vg=function(_1Vh){return new T2(1,40,new T(function(){return _1Vc(new T2(1,41,_1Vh));}));};return _1Vg;}};return _1V5;},_1Vi=new T(function(){return unCStr("Builtin_Lookup");}),_1Vj=function(_uh){return _0(_1Vi,_uh);},_1Vk=new T(function(){return unCStr("Builtin_Insert");}),_1Vl=function(_uh){return _0(_1Vk,_uh);},_1Vm=new T(function(){return unCStr("Builtin_Empty");}),_1Vn=function(_uh){return _0(_1Vm,_uh);},_1Vo=new T(function(){return unCStr("Builtin_CurrentDict");}),_1Vp=function(_uh){return _0(_1Vo,_uh);},_1Vq=new T(function(){return unCStr("Builtin_Exec");}),_1Vr=function(_uh){return _0(_1Vq,_uh);},_1Vs=new T(function(){return unCStr("Builtin_Extra ");}),_1Vt=new T(function(){return unCStr("Builtin_Def");}),_1Vu=function(_uh){return _0(_1Vt,_uh);},_1Vv=new T(function(){return unCStr("Builtin_DeRef");}),_1Vw=function(_uh){return _0(_1Vv,_uh);},_1Vx=new T(function(){return unCStr("Builtin_Sign");}),_1Vy=function(_uh){return _0(_1Vx,_uh);},_1Vz=new T(function(){return unCStr("Builtin_Mod");}),_1VA=function(_uh){return _0(_1Vz,_uh);},_1VB=new T(function(){return unCStr("Builtin_Div");}),_1VC=function(_uh){return _0(_1VB,_uh);},_1VD=new T(function(){return unCStr("Builtin_Mul");}),_1VE=function(_uh){return _0(_1VD,_uh);},_1VF=new T(function(){return unCStr("Builtin_Sub");}),_1VG=function(_uh){return _0(_1VF,_uh);},_1VH=new T(function(){return unCStr("Builtin_Add");}),_1VI=function(_uh){return _0(_1VH,_uh);},_1VJ=new T(function(){return unCStr("Builtin_Each");}),_1VK=function(_uh){return _0(_1VJ,_uh);},_1VL=new T(function(){return unCStr("Builtin_Range");}),_1VM=function(_uh){return _0(_1VL,_uh);},_1VN=new T(function(){return unCStr("Builtin_Quote");}),_1VO=function(_uh){return _0(_1VN,_uh);},_1VP=new T(function(){return unCStr("Builtin_SwapN");}),_1VQ=function(_uh){return _0(_1VP,_uh);},_1VR=new T(function(){return unCStr("Builtin_Swap");}),_1VS=function(_uh){return _0(_1VR,_uh);},_1VT=new T(function(){return unCStr("Builtin_DupN");}),_1VU=function(_uh){return _0(_1VT,_uh);},_1VV=new T(function(){return unCStr("Builtin_Dup");}),_1VW=function(_uh){return _0(_1VV,_uh);},_1VX=new T(function(){return unCStr("Builtin_PopN");}),_1VY=function(_uh){return _0(_1VX,_uh);},_1VZ=new T(function(){return unCStr("Builtin_Pop");}),_1W0=function(_uh){return _0(_1VZ,_uh);},_1W1=new T(function(){return unCStr("Builtin_Pick");}),_1W2=function(_uh){return _0(_1W1,_uh);},_1W3=new T(function(){return unCStr("Builtin_Stack");}),_1W4=function(_uh){return _0(_1W3,_uh);},_1W5=new T(function(){return unCStr("Builtin_Clear");}),_1W6=function(_uh){return _0(_1W5,_uh);},_1W7=new T(function(){return unCStr("Builtin_ListEnd");}),_1W8=function(_uh){return _0(_1W7,_uh);},_1W9=new T(function(){return unCStr("Builtin_Keys");}),_1Wa=function(_uh){return _0(_1W9,_uh);},_1Wb=new T(function(){return unCStr("Builtin_ListBegin");}),_1Wc=function(_uh){return _0(_1Wb,_uh);},_1Wd=new T(function(){return unCStr("Builtin_Delete");}),_1We=function(_uh){return _0(_1Wd,_uh);},_1Wf=function(_1Wg,_1Wh,_1Wi){var _1Wj=E(_1Wi);switch(_1Wj._){case 0:return _1Wc;case 1:return _1W8;case 2:return _1W6;case 3:return _1W4;case 4:return _1W2;case 5:return _1W0;case 6:return _1VY;case 7:return _1VW;case 8:return _1VU;case 9:return _1VS;case 10:return _1VQ;case 11:return _1VM;case 12:return _1VK;case 13:return _1VI;case 14:return _1VG;case 15:return _1VE;case 16:return _1VC;case 17:return _1VA;case 18:return _1Vy;case 19:return _1Vw;case 20:return _1Vu;case 21:return _1Vr;case 22:return _1Vp;case 23:return _1Vn;case 24:return _1Vl;case 25:return _1Vj;case 26:return _1We;case 27:return _1Wa;case 28:return _1VO;default:var _1Wk=new T(function(){return B(A3(_SR,_1Wg,11,_1Wj.a));});if(E(_1Wh)<11){var _1Wl=function(_1Wm){return _0(_1Vs,new T(function(){return B(A1(_1Wk,_1Wm));},1));};return _1Wl;}else{var _1Wn=function(_1Wo){var _1Wp=new T(function(){return _0(_1Vs,new T(function(){return B(A1(_1Wk,new T2(1,41,_1Wo)));},1));});return new T2(1,40,_1Wp);};return _1Wn;}}},_1Wq=new T(function(){return unCStr("StackProg ");}),_1Wr=new T(function(){return unCStr("StackDict ");}),_1Ws=new T(function(){return unCStr("StackList ");}),_1Wt=new T(function(){return unCStr("StackSymbol ");}),_1Wu=new T(function(){return unCStr("StackInt ");}),_1Wv=new T(function(){return unCStr("StackBuiltin ");}),_1Ww=new T(function(){return unCStr("#<opaque>");}),_1Wx=new T(function(){return unCStr("StackExtra ");}),_1Wy=function(_1Wz){var _1WA=new T(function(){return _0(_1Wx,new T(function(){return _0(_1Ww,new T2(1,41,_1Wz));},1));});return new T2(1,40,_1WA);},_1WB=function(_1WC){return _0(_1Wx,new T(function(){return _0(_1Ww,_1WC);},1));},_1WD=function(_1WE){return E(E(_1WE).c);},_1WF=function(_1WG,_1WH){var _1WI=new T(function(){return _1WJ(_1WG,_1WH);}),_1WK=new T(function(){return B(A3(_1WF,_1WG,_1WH,0));}),_1WL=function(_1WM,_1WN){var _1WO=E(_1WN);switch(_1WO._){case 0:var _1WP=new T(function(){return _1Wf(_1WH,11,_1WO.a);});if(E(_1WM)<11){var _1WQ=function(_1WR){return _0(_1Wv,new T(function(){return B(A1(_1WP,_1WR));},1));};return _1WQ;}else{var _1WS=function(_1WT){var _1WU=new T(function(){return _0(_1Wv,new T(function(){return B(A1(_1WP,new T2(1,41,_1WT)));},1));});return new T2(1,40,_1WU);};return _1WS;}break;case 1:var _1WV=_1WO.a;if(E(_1WM)<11){var _1WW=function(_1WX){return _0(_1Wu,new T(function(){return _ck(11,E(_1WV),_1WX);},1));};return _1WW;}else{var _1WY=function(_1WZ){var _1X0=new T(function(){return _0(_1Wu,new T(function(){return _ck(11,E(_1WV),new T2(1,41,_1WZ));},1));});return new T2(1,40,_1X0);};return _1WY;}break;case 2:var _1X1=new T(function(){return B(A3(_SR,_1WG,11,_1WO.a));});if(E(_1WM)<11){var _1X2=function(_1X3){return _0(_1Wt,new T(function(){return B(A1(_1X1,_1X3));},1));};return _1X2;}else{var _1X4=function(_1X5){var _1X6=new T(function(){return _0(_1Wt,new T(function(){return B(A1(_1X1,new T2(1,41,_1X5)));},1));});return new T2(1,40,_1X6);};return _1X4;}break;case 3:var _1X7=_1WO.a;if(E(_1WM)<11){var _1X8=function(_1X9){return _0(_1Ws,new T(function(){return _1R(_1WK,_1X7,_1X9);},1));};return _1X8;}else{var _1Xa=function(_1Xb){var _1Xc=new T(function(){return _0(_1Ws,new T(function(){return _1R(_1WK,_1X7,new T2(1,41,_1Xb));},1));});return new T2(1,40,_1Xc);};return _1Xa;}break;case 4:var _1Xd=new T(function(){return _1Uh(_1WG,_1WI,11,_1WO.a);});if(E(_1WM)<11){var _1Xe=function(_1Xf){return _0(_1Wr,new T(function(){return B(A1(_1Xd,_1Xf));},1));};return _1Xe;}else{var _1Xg=function(_1Xh){var _1Xi=new T(function(){return _0(_1Wr,new T(function(){return B(A1(_1Xd,new T2(1,41,_1Xh)));},1));});return new T2(1,40,_1Xi);};return _1Xg;}break;case 5:var _1Xj=new T(function(){return B(A2(_1WD,_1WG,_1WO.a));});if(E(_1WM)<11){var _1Xk=function(_1Xl){return _0(_1Wq,new T(function(){return B(A1(_1Xj,_1Xl));},1));};return _1Xk;}else{var _1Xm=function(_1Xn){var _1Xo=new T(function(){return _0(_1Wq,new T(function(){return B(A1(_1Xj,new T2(1,41,_1Xn)));},1));});return new T2(1,40,_1Xo);};return _1Xm;}break;default:return (E(_1WM)<11)?_1WB:_1Wy;}};return _1WL;},_1Xp=function(_1Xq,_1Xr,_1Xs){return C > 19 ? new F(function(){return A(_1WF,[_1Xq,_1Xr,0,_1Xs,__Z]);}) : (++C,A(_1WF,[_1Xq,_1Xr,0,_1Xs,__Z]));},_1Xt=function(_1Xu,_1Xv){var _1Xw=new T(function(){return B(A3(_1WF,_1Xu,_1Xv,0));});return function(_3v,_1T4){return _1R(_1Xw,_3v,_1T4);};},_1WJ=function(_1Xx,_1Xy){return new T3(0,new T(function(){return _1WF(_1Xx,_1Xy);}),function(_uh){return C > 19 ? new F(function(){return _1Xp(_1Xx,_1Xy,_uh);}) : (++C,_1Xp(_1Xx,_1Xy,_uh));},new T(function(){return _1Xt(_1Xx,_1Xy);}));},_1Xz=function(_1XA,_1XB){return C > 19 ? new F(function(){return A3(_1WD,_1XA,_1XB,__Z);}) : (++C,A3(_1WD,_1XA,_1XB,__Z));},_1XC=function(_1XD,_1XE,_1XF){return _1R(new T(function(){return _1WD(_1XD);}),_1XE,_1XF);},_1XG=function(_1XH){var _1XI=new T(function(){return _1WD(_1XH);});return new T3(0,function(_1XJ){return E(_1XI);},function(_1Sl){return C > 19 ? new F(function(){return _1Xz(_1XH,_1Sl);}) : (++C,_1Xz(_1XH,_1Sl));},function(_1Sk,_1Sl){return _1XC(_1XH,_1Sk,_1Sl);});},_1XK=function(_1XL){return E(E(_1XL).a);},_1XM=function(_1XN){return E(E(_1XN).b);},_1XO=new T(function(){return _U6(_nK);}),_1XP=new T(function(){return _U6(_nK);}),_1XQ=function(_1XR,_1XS){var _1XT=function(_1XU){var _1XV=E(_1XU);return (_1XV._==0)?__Z:new T2(1,new T(function(){return _Iz(_1XV.a,_1XS);}),new T(function(){return _1XT(_1XV.b);}));};return C > 19 ? new F(function(){return _2B(_1XP,_1XT(_1XR));}) : (++C,_2B(_1XP,_1XT(_1XR)));},_1XW=new T3(0,new T2(0,_IK,new T2(0,_Iz,_1XQ)),function(_1XX){return C > 19 ? new F(function(){return _2B(_1XP,_1XX);}) : (++C,_2B(_1XP,_1XX));},function(_1XY,_1XZ){return C > 19 ? new F(function(){return _2B(_1XP,_Iz(_1XZ,_1XY));}) : (++C,_2B(_1XP,_Iz(_1XZ,_1XY)));}),_1Y0=function(_1Y1){return new T3(0,new T(function(){return E(E(_1Y1).b);}),_2L,new T(function(){return E(E(_1Y1).a);}));},_1Y2=function(_1Y3){var _1Y4=E(_1Y3);return (_1Y4._==0)?__Z:new T2(1,new T(function(){return _1Y0(_1Y4.a);}),new T(function(){return _1Y2(_1Y4.b);}));},_1Y5=new T(function(){return _1Y2(__Z);}),_1Y6=function(_1Y7){return E(_1Y5);},_1Y8=function(_1Y9,_1Ya){var _1Yb=E(E(_1Y9).a);return (_1Yb._==0)?__Z:new T2(1,new T3(0,_1Yb.a,new T(function(){return E(E(_1Ya).b);}),__Z),__Z);},_1Yc=function(_1Yd){return __Z;},_1Ye=function(_1Yf){return __Z;},_1Yg=function(_1Yh,_1Yi,_1Yj,_1Yk){var _1Yl=new T(function(){var _1Ym=E(_1Yj);if(!_1Ym._){var _1Yn=E(_1Ym.a);if(_1Yn>=B(A3(_2B,_6g,_CV(_CS(_1Yh)),0))){return _1Y6;}else{var _1Yo=_sa(_C6,_1Yn,E(_1Yi).a);if(!_1Yo._){return _1Ye;}else{var _1Yp=function(_1Yq){return new T2(1,new T3(0,_1Yo.a,new T(function(){return E(E(_1Yq).b);}),__Z),__Z);};return _1Yp;}}}else{var _1Yr=new T(function(){var _1Ys=_sa(_C6,B(A3(_2B,_6g,_CV(_CS(_1Ym.a)),0)),E(_1Yi).b);if(!_1Ys._){return _1Yc;}else{var _1Yt=function(_1Yu){return new T2(1,new T3(0,_1Ys.a,new T(function(){return E(E(_1Yu).b);}),__Z),__Z);};return _1Yt;}}),_1Yv=function(_1Yw){var _1Yx=E(_1Yw);if(!_1Yx._){return __Z;}else{var _1Yy=_1Yx.a,_1Yz=new T(function(){var _1YA=E(_1Ym.c);return _1Yg(_1Yh,new T(function(){return E(E(_1Yy).a);},1),_1YA.a,_1YA.b);});return new T2(1,new T3(0,_1Yz,new T(function(){return E(E(_1Yy).b);}),new T(function(){return E(E(_1Yy).c);})),new T(function(){return _1Yv(_1Yx.b);}));}},_1YB=function(_1YC){return _1Yv(B(A1(_1Yr,_1YC)));};return function(_3v){return C > 19 ? new F(function(){return _2Z(_1XO,_1XW,_1YB,_3v);}) : (++C,_2Z(_1XO,_1XW,_1YB,_3v));};}}),_1YD=function(_1YE){var _1YF=E(_1YE);if(!_1YF._){return __Z;}else{var _1YG=function(_1YH,_1YI){var _1YJ=new T(function(){var _1YK=E(E(_1YI).b),_1YL=E(_1YK.b);return B(_1YM(_1Yh,_1YK.a,_1YL.a,_1YL.b,_1YK.c,_1YF.a));}),_1YN=function(_1YO){var _1YP=E(_1YO);if(!_1YP._){return __Z;}else{var _1YQ=_1YP.a,_1YR=new T(function(){return B(A1(_1YH,new T(function(){return E(E(_1YQ).a);})));});return new T2(1,new T3(0,_1YR,new T(function(){return E(E(_1YQ).b);}),new T(function(){return E(E(_1YQ).c);})),new T(function(){return _1YN(_1YP.b);}));}},_1YS=function(_1YT){return _1YN(B(A1(_1YJ,_1YT)));};return function(_3v){return C > 19 ? new F(function(){return _2Z(_1XO,_1XW,_1YS,_3v);}) : (++C,_2Z(_1XO,_1XW,_1YS,_3v));};};return new T2(1,_1YG,new T(function(){return _1YD(_1YF.b);}));}},_1YU=new T(function(){return _1YD(_1Yk);}),_1YV=function(_1YW){var _1YX=E(_1YW);if(!_1YX._){return __Z;}else{var _1YY=_1YX.a,_1YZ=new T(function(){return B(A(_2B,[_6h,_1YU,_1Y8,new T(function(){return E(E(_1YY).a);})]));});return new T2(1,new T3(0,_1YZ,new T(function(){return E(E(_1YY).b);}),new T(function(){return E(E(_1YY).c);})),new T(function(){return _1YV(_1YX.b);}));}},_1Z0=function(_1Z1){return _1YV(B(A1(_1Yl,_1Z1)));};return function(_3v){return C > 19 ? new F(function(){return _2Z(_1XO,_1XW,_1Z0,_3v);}) : (++C,_2Z(_1XO,_1XW,_1Z0,_3v));};},_1Z2=new T(function(){return _U6(_nK);}),_1Z3=function(_1Z4,_1Z5){var _1Z6=new T(function(){return B(A1(_1Z4,new T(function(){return E(E(_1Z5).b);})));});return new T2(0,new T(function(){return E(E(_1Z5).a);}),_1Z6);},_1Z7=function(_1Z8,_1Z9,_1Za,_1Zb){var _1Zc=new T(function(){var _1Zd=B(A2(_1Z8,function(_1Ze){return C > 19 ? new F(function(){return A2(_1Z8,_1Ze,_1Zb);}) : (++C,A2(_1Z8,_1Ze,_1Zb));},_1Za)),_1Zf=_1Zd.b;return new T3(0,_1Zd.a,new T(function(){return E(E(_1Zf).a);}),new T(function(){return E(E(_1Zf).b);}));}),_1Zg=new T(function(){return B(A3(_2x,_1Z9,new T(function(){return E(E(_1Zc).a);}),new T(function(){return E(E(_1Zc).b);})));});return new T2(0,_1Zg,new T(function(){return E(E(_1Zc).c);}));},_1Zh=function(_1Zi,_1Zj){return new T2(0,_1Zi,function(_1wt,_1wu){return _1Z7(_1Zi,_1Zj,_1wt,_1wu);});},_1Zk=new T(function(){var _1Zl=function(_1Zm){return new T2(0,__Z,_1Zm);},_1Zn=new T(function(){return _1Zh(_1Z3,_1Z2);}),_1Zo=_1Z2;return new T2(0,_1Zl,_1Zn);}),_1Zp=new T(function(){return _U6(_nK);}),_1Zq=function(_1Zr,_1Zs,_1Zt,_1Zu){var _1Zv=new T(function(){var _1Zw=new T(function(){return B(A3(_ZF,_1Zr,function(_1Zx){var _1Zy=E(_1Zx);return C > 19 ? new F(function(){return _1Zq(_1Zr,_1Zs,_1Zy.a,_1Zy.b);}) : (++C,_1Zq(_1Zr,_1Zs,_1Zy.a,_1Zy.b));},_1Zu));});return B(A3(_ZH,_1Zr,_1Zs,_1Zw));});return C > 19 ? new F(function(){return A3(_2x,_1Zs,_1Zt,_1Zv);}) : (++C,A3(_2x,_1Zs,_1Zt,_1Zv));},_1Zz=function(_1ZA,_1ZB,_1ZC,_1ZD){var _1ZE=new T(function(){var _1ZF=_2R(_2T(_2P(_1ZB))),_1ZG=function(_1ZH){var _1ZI=new T(function(){var _1ZJ=function(_1ZK){var _1ZL=new T(function(){return B(A1(E(_1ZH).a,new T(function(){return E(E(_1ZK).a);})));});return new T3(0,_1ZL,new T(function(){return E(E(_1ZK).b);}),new T(function(){return E(E(_1ZK).c);}));};return B(A1(_1ZF,_1ZJ));}),_1ZM=function(_1ZN){return C > 19 ? new F(function(){return A1(_1ZI,new T(function(){return B(A1(_1ZD,_1ZN));}));}) : (++C,A1(_1ZI,new T(function(){return B(A1(_1ZD,_1ZN));})));};return new T3(0,_1ZM,new T(function(){return E(E(_1ZH).b);}),new T(function(){return E(E(_1ZH).c);}));};return B(A1(_1ZF,_1ZG));}),_1ZO=function(_1ZP){return C > 19 ? new F(function(){return A1(_1ZE,new T(function(){return B(A1(_1ZC,_1ZP));}));}) : (++C,A1(_1ZE,new T(function(){return B(A1(_1ZC,_1ZP));})));};return function(_3v){return C > 19 ? new F(function(){return _2Z(_1ZA,_1ZB,_1ZO,_3v);}) : (++C,_2Z(_1ZA,_1ZB,_1ZO,_3v));};},_1ZQ=function(_1ZR){return new T2(0,new T(function(){return E(E(_1ZR).c);}),new T(function(){return E(E(_1ZR).a);}));},_1ZS=function(_1ZT){var _1ZU=E(_1ZT);return (_1ZU._==0)?__Z:new T2(1,new T(function(){return _1ZQ(_1ZU.a);}),new T(function(){return _1ZS(_1ZU.b);}));},_1ZV=function(_1ZW){var _1ZX=E(_1ZW);return (_1ZX._==0)?__Z:new T2(1,new T(function(){return _1ZQ(_1ZX.a);}),new T(function(){return _1ZV(_1ZX.b);}));},_1ZY=function(_1ZZ){var _200=E(_1ZZ);return (_200._==0)?__Z:new T2(1,new T(function(){return _1Y0(_200.a);}),new T(function(){return _1ZY(_200.b);}));},_201=new T2(0,_2L,_2L),_202=function(_203,_204){var _205=new T(function(){return _1ZY(_nK(_1ZV(B(A1(_203,_201))),new T(function(){return _1ZS(B(A1(_204,_201)));},1)));});return function(_206){return E(_205);};},_207=function(_208){return __Z;},_209=function(_20a,_20b){var _20c=E(_20b);if(!_20c._){return _2z(_20a);}else{return E(_20c.a);}},_20d=function(_20e,_20f){var _20g=new T(function(){return _2x(_20e);}),_20h=function(_20i,_20j){while(1){var _20k=(function(_20l,_20m){var _20n=E(_20m);if(!_20n._){var _20o=new T(function(){return B(A2(_20g,_20n.c,new T(function(){return _20h(_20l,_20n.e);})));},1);_20i=_20o;_20j=_20n.d;return __continue;}else{return E(_20l);}})(_20i,_20j);if(_20k!=__continue){return _20k;}}};return _20h(new T(function(){return _2z(_20e);},1),_20f);},_20p=function(_20q,_20r){var _20s=new T(function(){return _20p(_20q,_20r);}),_20t=new T(function(){return B(A1(_20q,function(_20u){var _20v=E(_20u);return C > 19 ? new F(function(){return _1Zq(_20w,_20r,_20v.a,_20v.b);}) : (++C,_1Zq(_20w,_20r,_20v.a,_20v.b));}));}),_20x=new T(function(){var _20y=function(_He){return _209(_20r,_He);};return B(A1(_20q,function(_20z){var _20A=E(_20z),_20B=_JD(_Jr,_20y,_20A.a,_20A.b);return new T2(0,_20B.a,_20B.b);}));}),_20C=function(_20D){var _20E=new T(function(){return B(A1(_20t,new T(function(){return B(A1(_20x,_20D));})));});return C > 19 ? new F(function(){return A1(_20s,_20E);}) : (++C,A1(_20s,_20E));},_20F=new T(function(){return _2x(_20r);}),_20G=function(_20H){var _20I=E(_20H);return C > 19 ? new F(function(){return A2(_20F,new T(function(){return _20d(_20r,_20I.a);}),new T(function(){return _20d(_20r,_JK(_20C,_20I.b));}));}) : (++C,A2(_20F,new T(function(){return _20d(_20r,_20I.a);}),new T(function(){return _20d(_20r,_JK(_20C,_20I.b));})));};return _20G;},_20J=function(_20K,_20L){var _20M=E(_20L),_20N=_JO(_20K,_20M.a,_20M.b);return new T2(0,_20N.a,_20N.b);},_20O=function(_20P,_20Q){var _20R=new T(function(){return _20O(_20P,_20Q);}),_20S=new T(function(){return B(A1(_20P,new T(function(){return _20O(_20P,_20Q);})));}),_20T=function(_20U){return C > 19 ? new F(function(){return A1(_20R,new T(function(){return B(A1(_20S,_20U));}));}) : (++C,A1(_20R,new T(function(){return B(A1(_20S,_20U));})));},_20V=new T(function(){return _20p(_20J,_20Q);}),_20W=new T(function(){return _2x(_20Q);}),_20X=new T(function(){return _20Y(_20P);}),_20Z=function(_210){var _211=E(_210);return C > 19 ? new F(function(){return _1Zq(_20X,_20Q,_211.a,_211.b);}) : (++C,_1Zq(_20X,_20Q,_211.a,_211.b));},_212=function(_He){return _209(_20Q,_He);},_213=function(_214){var _215=E(_214),_216=_JD(_20P,_212,_215.a,_215.b);return new T2(0,_216.a,_216.b);},_217=function(_218){var _219=E(_218),_21a=new T(function(){var _21b=new T(function(){return B(A1(_20V,new T(function(){var _21c=E(_219.b),_21d=_JO(_213,_21c.a,_21c.b),_21e=_JO(_20Z,_21d.a,_21d.b);return new T2(0,_21e.a,_21e.b);})));});return B(A2(_20W,_21b,new T(function(){return _20d(_20Q,_219.c);})));});return C > 19 ? new F(function(){return A2(_20W,new T(function(){return _20d(_20Q,_JK(_20T,_219.a));}),_21a);}) : (++C,A2(_20W,new T(function(){return _20d(_20Q,_JK(_20T,_219.a));}),_21a));};return _217;},_20Y=function(_21f){return new T2(0,_21f,function(_He){return _20O(_21f,_He);});},_20w=new T(function(){return _20Y(_Jr);}),_21g=function(_21h){return E(_21h);},_21i=function(_21j){var _21k=E(_21j);if(!_21k._){return __Z;}else{var _21l=_21k.a;return new T2(1,new T3(0,_21g,new T(function(){return E(E(_21l).b);}),new T(function(){return E(E(_21l).c);})),new T(function(){return _21i(_21k.b);}));}},_21m=function(_21n){return _mR(__Z,_21n);},_21o=function(_21p,_21q,_21r,_21s){var _21t=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_21p)),0));}),_21u=function(_21v){var _21w=E(_21v);return (_21w._==0)?__Z:new T2(1,new T(function(){var _21x=E(_21w.a);if(E(_21x.a)<E(_21t)){return new T2(0,__Z,_21x);}else{return new T2(0,new T2(1,_21x,__Z),_21x);}}),new T(function(){return _21u(_21w.b);}));},_21y=function(_21z){var _21A=E(_21z);if(!_21A._){return __Z;}else{var _21B=function(_21C){var _21D=E(_21A.a),_21E=new T(function(){var _21F=E(_21D.b),_21G=new T(function(){return E(_21D.a)-E(_21t)|0;}),_21H=function(_21I){return _21i(new T2(1,new T3(0,0,new T(function(){return E(E(_21I).b);}),new T2(1,new T3(0,_21p,_21G,_21r),__Z)),__Z));},_21J=function(_21K,_21L){var _21M=E(_21L),_21N=E(_21K);if(!_21N._){return _21M;}else{var _21O=new T(function(){var _21P=function(_21Q){return new T2(1,new T3(0,_21N.a,new T(function(){return E(E(_21Q).b);}),__Z),__Z);};return _1Zz(_1Zp,_1XW,_21H,_21P);},1);return _202(_21O,_21M);}},_21R=_JD(_Jr,_21J,_21F.a,_21F.b);return B(A(_1Zq,[_20w,_6g,_21R.a,_21R.b,_207]));},1);return _202(_21C,_21E);};return new T2(1,_21B,new T(function(){return _21y(_21A.b);}));}};return C > 19 ? new F(function(){return A3(_2B,_6h,_21y(B(_Kk(_1Zk,_21u(_21m(_21q)))).a),_21s);}) : (++C,A3(_2B,_6h,_21y(B(_Kk(_1Zk,_21u(_21m(_21q)))).a),_21s));},_21S=function(_21T){return __Z;},_21U=function(_21V){return __Z;},_1YM=function(_21W,_21X,_21Y,_21Z,_220,_221){var _222=E(_221);switch(_222._){case 0:var _223=_222.c,_224=function(_225){var _226=E(_225);if(!_226._){return __Z;}else{var _227=_226.a;return new T2(1,new T3(0,new T(function(){var _228=E(E(_227).a),_229=E(_228.b);return B(_1YM(new T2(1,new T2(0,_222.b,_223),_21W),_228.a,_229.a,_229.b,_228.c,_222.d));}),new T(function(){return E(E(_227).b);}),new T(function(){return E(E(_227).c);})),new T(function(){return _224(_226.b);}));}},_22a=function(_22b){var _22c=E(_22b);if(!_22c._){return __Z;}else{var _22d=_22c.a,_22e=new T(function(){var _22f=E(E(_22d).a),_22g=E(_22f.b);return B(_1YM(_21W,_22f.a,_22g.a,_22g.b,_22f.c,_223));}),_22h=function(_22i){return _224(B(A1(_22e,_22i)));};return new T2(1,new T3(0,function(_22j){return C > 19 ? new F(function(){return _2Z(_1XO,_1XW,_22h,_22j);}) : (++C,_2Z(_1XO,_1XW,_22h,_22j));},new T(function(){return E(E(_22d).b);}),new T(function(){return E(E(_22d).c);})),new T(function(){return _22a(_22c.b);}));}},_22k=new T(function(){var _22l=_sa(_Bw,_222.a,_21X);if(!_22l._){return _21U;}else{var _22m=function(_22n){return new T2(1,new T3(0,_22l.a,new T(function(){return E(E(_22n).b);}),__Z),__Z);};return _22m;}}),_22o=function(_22p){return _22a(B(A1(_22k,_22p)));};return C > 19 ? new F(function(){return _21o(_21W,_21Y,_222,function(_22q){return C > 19 ? new F(function(){return _2Z(_1XO,_1XW,_22o,_22q);}) : (++C,_2Z(_1XO,_1XW,_22o,_22q));});}) : (++C,_21o(_21W,_21Y,_222,function(_22q){return C > 19 ? new F(function(){return _2Z(_1XO,_1XW,_22o,_22q);}) : (++C,_2Z(_1XO,_1XW,_22o,_22q));}));break;case 1:return C > 19 ? new F(function(){return _21o(_21W,_21Y,_222,new T(function(){var _22r=E(_222.a);return _1Yg(_21W,new T2(0,_21Y,_21Z),_22r.a,_22r.b);}));}) : (++C,_21o(_21W,_21Y,_222,new T(function(){var _22r=E(_222.a);return _1Yg(_21W,new T2(0,_21Y,_21Z),_22r.a,_22r.b);})));break;default:var _22s=new T(function(){var _22t=_sa(_C6,_222.a,_220);if(!_22t._){return _21S;}else{var _22u=function(_22v){return new T2(1,new T3(0,_22t.a,new T(function(){return E(E(_22v).b);}),__Z),__Z);};return _22u;}});return C > 19 ? new F(function(){return _21o(_21W,_21Y,_222,_22s);}) : (++C,_21o(_21W,_21Y,_222,_22s));}},_22w=function(_22x){var _22y=E(_22x);return (_22y._==0)?__Z:new T2(1,new T(function(){return _1ZQ(_22y.a);}),new T(function(){return _22w(_22y.b);}));},_22z=function(_22A){var _22B=E(_22A);return (_22B._==0)?__Z:new T2(1,_22B.a,new T(function(){return _22z(_22B.b);}));},_22C=function(_22D,_22E,_22F){var _22G=new T(function(){return B(A(_Cn,[_22D,_22E,_4P,function(_22H){return E(new T1(1,_22F));}]));});return function(_22I){return C > 19 ? new F(function(){return A1(_22G,_22I);}) : (++C,A1(_22G,_22I));};},_22J=function(_22K,_22L){var _22M=function(_22N){var _22O=E(_22N);return (_22O._==0)?__Z:new T2(1,new T(function(){var _22P=E(_22O.a);return _22C(_22K,_22P.a,_22P.b);}),new T(function(){return _22M(_22O.b);}));};return C > 19 ? new F(function(){return A3(_2B,_Rw,_22z(_22M(_22L)),new T(function(){return _2z(_RA(_22K));}));}) : (++C,A3(_2B,_Rw,_22z(_22M(_22L)),new T(function(){return _2z(_RA(_22K));})));},_22Q=new T(function(){return unCStr(" ");}),_22R=new T(function(){return unCStr("Set");}),_22S=new T(function(){return unCStr("\u03bc(");}),_22T=new T(function(){return unCStr("#");}),_22U=new T(function(){return unCStr("\u2200");}),_22V=new T(function(){return unCStr("\u03bb");}),_22W=new T(function(){return unCStr(" -> ");}),_22X=new T(function(){return unCStr(":");}),_22Y=new T(function(){return unCStr(" (");}),_22Z=new T(function(){return unCStr(", ");}),_230=new T(function(){return _Pf(_C6,0,_3C);}),_231=new T(function(){return unCStr(")");}),_232=new T(function(){return unCStr("(");}),_233=function(_234,_235,_236,_237,_238){var _239=new T(function(){return B(A1(_237,new T(function(){return _sa(_234,_235,_238);})));}),_23a=function(_23b){return C > 19 ? new F(function(){return _rY(_234,function(_23c){return E(_23b);},_235,_238);}) : (++C,_rY(_234,function(_23c){return E(_23b);},_235,_238));};return C > 19 ? new F(function(){return A2(_236,_23a,_239);}) : (++C,A2(_236,_23a,_239));},_23d=function(_23e,_23f){return new T2(0,_23e,function(_23g,_23h,_23i,_23j){return C > 19 ? new F(function(){return _233(_23f,_23g,_23h,_23i,_23j);}) : (++C,_233(_23f,_23g,_23h,_23i,_23j));});},_23k=new T(function(){return _23d(new T(function(){var _23l=function(_23m,_23n){var _23o=E(_23m);if(!_23o._){var _23p=E(_23n);if(!_23p._){return C > 19 ? new F(function(){return _Gc(_C6,__Z,__Z,_23o.a,_23o.b,_23o.c,_23o.d,_23o.e,_23p.a,_23p.b,_23p.c,_23p.d,_23p.e);}) : (++C,_Gc(_C6,__Z,__Z,_23o.a,_23o.b,_23o.c,_23o.d,_23o.e,_23p.a,_23p.b,_23p.c,_23p.d,_23p.e));}else{return _23o;}}else{return E(_23n);}},_23q=_C6;return new T2(0,_23l,_oG);}),_C6);}),_23r=function(_23s){var _23t=E(_23s);return (_23t._==0)?__Z:new T2(1,new T(function(){return _nO(_23t.a);}),new T(function(){return _23r(_23t.b);}));},_23u=function(_23v){return false;},_23w=function(_23x){var _23y=E(_23x);return (_23y._==0)?__Z:new T2(1,_23u,new T(function(){return _23w(_23y.b);}));},_23z=function(_23A){var _23B=E(_23A);return (_23B._==0)?__Z:new T2(1,_23u,new T(function(){return _23z(_23B.b);}));},_23C=function(_23D){var _23E=E(_23D);if(!_23E._){return __Z;}else{var _23F=E(_23E.a);return new T2(1,new T2(0,_23F.b,new T2(0,_23F.a,_23F.c)),new T(function(){return _23C(_23E.b);}));}},_23G=function(_23H){return E(E(_23H).b);},_23I=function(_23J){var _23K=new T(function(){return _IW(_23J);}),_23L=new T(function(){return B(A1(_23K,_232));}),_23M=new T(function(){return B(A1(_23K,_231));}),_23N=new T(function(){return _IU(_23J);}),_23O=new T(function(){return _IQ(_23N);}),_23P=new T(function(){return _2x(_23O);}),_23Q=new T(function(){return _IO(new T(function(){return _1XK(_23J);}));}),_23R=new T(function(){return _2z(_23O);}),_23S=new T(function(){return B(A1(_23K,_22Z));}),_23T=new T(function(){return B(A1(_23K,_22Y));}),_23U=new T(function(){return B(A1(_23K,_22X));}),_23V=new T(function(){return B(A1(_23K,_22W));}),_23W=new T(function(){return B(A1(_23K,_22V));}),_23X=new T(function(){return B(A1(_23K,_22U));}),_23Y=new T(function(){return B(A1(_23K,_22T));}),_23Z=new T(function(){return B(A1(_23K,_22S));}),_240=new T(function(){return B(A1(_23K,_22Q));}),_241=new T(function(){return B(A1(_23P,_240));}),_242=new T(function(){return _2z(_23O);}),_243=function(_244){var _245=E(_244);if(!_245._){return __Z;}else{var _246=_245.a,_247=function(_248){var _249=new T(function(){var _24a=E(_248);if(!E(_24a.a)){return B(A2(_23P,_246,new T(function(){return B(A2(_23P,_240,_24a.b));})));}else{return E(_246);}});return new T2(0,false,_249);};return new T2(1,_247,new T(function(){return _243(_245.b);}));}},_24b=new T(function(){return B(A1(_23K,_22R));}),_24c=function(_24d,_24e,_24f){var _24g=function(_24h,_24i,_24j){var _24k=E(_24d),_24l=E(_24k.b),_24m=_22w(B(A(_1YM,[__Z,_24k.a,_24l.a,_24l.b,_24k.c,_24j,_201])));if(!_24m._){var _24n=E(_24j);switch(_24n._){case 0:var _24o=_24n.a,_24p=_24n.c,_24q=_24n.d,_24r=function(_24s){var _24t=new T(function(){var _24u=new T(function(){var _24v=new T(function(){var _24w=function(_24x,_24y){var _24z=E(_24y);if(!_24z._){var _24A=_24z.a,_24B=_24z.c,_24C=_24z.d,_24D=function(_24E){var _24F=function(_24G){var _24H=new T(function(){var _24I=new T(function(){return _10s(_23Q,_23K,_23P,_Zh,new T(function(){return _23r(_24x);}),_24z.b);}),_24J=new T(function(){var _24K=new T(function(){var _24L=new T(function(){return B(A2(_23P,_23M,new T(function(){return B(_24w(new T2(1,new T2(0,_24I,_24B),_24x),_24C));})));});return B(A2(_23P,new T(function(){return B(_24g(0,_24x,_24B));}),_24L));});return B(A2(_23P,_23U,_24K));});return B(A2(_23P,_24I,_24J));});return C > 19 ? new F(function(){return A2(_23P,_23T,_24H);}) : (++C,A2(_23P,_23T,_24H));};if(!E(_24o)){return C > 19 ? new F(function(){return _24F(_);}) : (++C,_24F(_));}else{if(!B(A2(_230,_3F,new T(function(){return B(_S2(_24C));})))._){return C > 19 ? new F(function(){return A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));}));}) : (++C,A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));})));}else{return C > 19 ? new F(function(){return _24F(_);}) : (++C,_24F(_));}}};if(!E(_24o)){if(!E(_24A)){return C > 19 ? new F(function(){return _24D(_);}) : (++C,_24D(_));}else{return C > 19 ? new F(function(){return A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));}));}) : (++C,A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));})));}}else{if(!E(_24A)){return C > 19 ? new F(function(){return A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));}));}) : (++C,A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));})));}else{return C > 19 ? new F(function(){return _24D(_);}) : (++C,_24D(_));}}}else{return C > 19 ? new F(function(){return A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));}));}) : (++C,A2(_23P,_23S,new T(function(){return B(_24g(0,_24x,_24z));})));}};return B(_24w(_24i,_24n));});return E(B(A3(_23G,_23N,1,_24v)).b);});return B(A2(_23P,new T(function(){if(!E(_24o)){return E(_23W);}else{return E(_23X);}}),_24u));});if(E(_24h)<=0){return E(_24t);}else{return C > 19 ? new F(function(){return A2(_23P,_23L,new T(function(){return B(A2(_23P,_24t,_23M));}));}) : (++C,A2(_23P,_23L,new T(function(){return B(A2(_23P,_24t,_23M));})));}};if(!E(_24o)){return C > 19 ? new F(function(){return _24r(_);}) : (++C,_24r(_));}else{if(!B(A2(_230,_3F,new T(function(){return B(_S2(_24q));})))._){var _24M=new T(function(){var _24N=new T(function(){return B(A2(_23P,_23V,new T(function(){return B(_24g(0,new T2(1,new T2(0,_24n.b,_24p),_24i),_24q));})));});return B(A2(_23P,new T(function(){return B(_24g(1,_24i,_24p));}),_24N));});if(E(_24h)<=0){return E(_24M);}else{return C > 19 ? new F(function(){return A2(_23P,_23L,new T(function(){return B(A2(_23P,_24M,_23M));}));}) : (++C,A2(_23P,_23L,new T(function(){return B(A2(_23P,_24M,_23M));})));}}else{return C > 19 ? new F(function(){return _24r(_);}) : (++C,_24r(_));}}break;case 1:var _24O=E(_24n.a),_24P=function(_24Q){var _24R=E(_24Q);if(!_24R._){return __Z;}else{var _24S=new T(function(){return B(A1(_241,new T(function(){return B(_24g(2,_24i,_24R.a));})));});return new T2(1,_24S,new T(function(){return _24P(_24R.b);}));}},_24T=function(_24U,_24V){var _24W=E(_24h),_24X=new T(function(){var _24Y=new T(function(){var _24Z=E(_24U);if(!_24Z._){var _250=_24Z.a,_251=E(_oy(_250,_24i).b);if(!_251._){var _252=new T(function(){return B(A1(_23K,new T(function(){return B(_1C6(_250));})));});return B(A2(_23P,_23Y,_252));}else{return E(E(_251.a).a);}}else{var _253=new T(function(){return B(A2(_23P,new T(function(){var _254=E(_24Z.c);return B(_24T(_254.a,_254.b));}),_23M));});return B(A2(_23P,_23Z,_253));}});return B(A2(_23P,_24Y,new T(function(){return B(_2B(_23O,_24P(_24V)));})));});if(!B(A3(_2B,_6h,_23w(_24V),true))){if(_24W<=1){return E(_24X);}else{return C > 19 ? new F(function(){return A2(_23P,_23L,new T(function(){return B(A2(_23P,_24X,_23M));}));}) : (++C,A2(_23P,_23L,new T(function(){return B(A2(_23P,_24X,_23M));})));}}else{if(_24W<=1000){return E(_24X);}else{return C > 19 ? new F(function(){return A2(_23P,_23L,new T(function(){return B(A2(_23P,_24X,_23M));}));}) : (++C,A2(_23P,_23L,new T(function(){return B(A2(_23P,_24X,_23M));})));}}};return C > 19 ? new F(function(){return _24T(_24O.a,_24O.b);}) : (++C,_24T(_24O.a,_24O.b));break;default:var _255=new T(function(){return B(A1(_23K,new T(function(){return B(_1C6(_24n.a));})));});return C > 19 ? new F(function(){return A2(_23P,_24b,_255);}) : (++C,A2(_23P,_24b,_255));}}else{var _256=E(_24m.a),_257=_256.a,_258=E(_24h),_259=new T(function(){var _25a=new T(function(){return B(_22J(_23k,_23C(_257)));}),_25b=function(_25c){var _25d=E(_25c);if(!_25d._){return __Z;}else{var _25e=new T(function(){var _25f=E(_25d.a);if(!_25f._){return E(_25f.a);}else{var _25g=_sa(_C6,_25f.a,_25a);if(!_25g._){return E(_23R);}else{var _25h=E(_25g.a);return B(_24g(2,new T(function(){return _nK(_25h.a,_24i);}),_25h.b));}}});return new T2(1,_25e,new T(function(){return _25b(_25d.b);}));}};return E(B(A3(_2B,_6h,_243(_25b(E(_256.b).b)),new T2(0,true,_242))).b);});if(!B(A3(_2B,_6h,_23z(_257),true))){if(_258<=1){return E(_259);}else{return C > 19 ? new F(function(){return A2(_23P,_23L,new T(function(){return B(A2(_23P,_259,_23M));}));}) : (++C,A2(_23P,_23L,new T(function(){return B(A2(_23P,_259,_23M));})));}}else{if(_258<=1000){return E(_259);}else{return C > 19 ? new F(function(){return A2(_23P,_23L,new T(function(){return B(A2(_23P,_259,_23M));}));}) : (++C,A2(_23P,_23L,new T(function(){return B(A2(_23P,_259,_23M));})));}}}};return C > 19 ? new F(function(){return _24g(0,_24e,_24f);}) : (++C,_24g(0,_24e,_24f));};return _24c;},_25i=function(_25j){var _25k=E(_25j);if(!_25k._){return __Z;}else{var _25l=_25k.a;return new T2(1,new T2(0,new T(function(){return E(E(_25l).a);}),new T(function(){return E(E(E(_25l).b).b);})),new T(function(){return _25i(_25k.b);}));}},_25m=new T(function(){return unCStr("(null)");}),_25n=function(_25o,_25p){return E(_oy(new T(function(){return B(A3(_2B,_6g,_CV(_CS(_25p)),0))-E(_25o)|0;},1),_25p).b);},_25q=function(_25r){var _25s=new T(function(){return _IO(new T(function(){return _1XK(_25r);}));}),_25t=new T(function(){return _2x(new T(function(){return _IQ(new T(function(){return _IU(_25r);}));}));}),_25u=new T(function(){return _Ku(_25r);}),_25v=new T(function(){return _1Ua(new T(function(){return _1Sg(new T(function(){return _1XG(_25u);}),new T(function(){return _1WJ(_25u,_1SV);}));}));}),_25w=new T(function(){return _1WF(_25u,_1SV);}),_25x=new T(function(){return _IW(_25r);}),_25y=new T(function(){return B(A1(_25x,_25m));}),_25z=new T(function(){return _23I(_25r);}),_25A=function(_25B,_25C,_25D){var _25E=E(_25D);switch(_25E._){case 1:return C > 19 ? new F(function(){return A1(_25x,new T(function(){return B(_1C6(_25E.a));}));}) : (++C,A1(_25x,new T(function(){return B(_1C6(_25E.a));})));break;case 2:return C > 19 ? new F(function(){return A1(_25x,new T(function(){return B(A2(_1XM,_25u,_25E.a));}));}) : (++C,A1(_25x,new T(function(){return B(A2(_1XM,_25u,_25E.a));})));break;case 6:var _25F=E(_25E.a);switch(_25F._){case 0:var _25G=new T(function(){return _25i(_25n(_25F.a,new T(function(){return _10M(_25s,_25x,_25t,_25C);})));});return C > 19 ? new F(function(){return A3(_25z,_25B,_25G,_25F.b);}) : (++C,A3(_25z,_25B,_25G,_25F.b));break;case 1:return E(_25y);default:return C > 19 ? new F(function(){return A1(_25x,new T(function(){return B(A3(_25v,0,_25F.a,__Z));}));}) : (++C,A1(_25x,new T(function(){return B(A3(_25v,0,_25F.a,__Z));})));}break;default:return C > 19 ? new F(function(){return A1(_25x,new T(function(){return B(A3(_25w,0,_25E,__Z));}));}) : (++C,A1(_25x,new T(function(){return B(A3(_25w,0,_25E,__Z));})));}};return _25A;},_25H=function(_25I){var _25J=E(_25I);return (_25J._==0)?E(_1RR):E(_25J.b);},_25K=function(_25L,_25M,_25N){return new T2(0,_25L,_25M);},_25O=function(_25P,_25Q,_25R){return C > 19 ? new F(function(){return A2(_25P,function(_25S){return _Jn(_25Q,_25S);},_25R);}) : (++C,A2(_25P,function(_25S){return _Jn(_25Q,_25S);},_25R));},_25T=function(_25U,_25V,_25W,_25X){return C > 19 ? new F(function(){return A(_1wx,[_1vI,_25V,_1vO,new T(function(){return B(A3(_2R,_2T(_25U),_25X,_25W));})]);}) : (++C,A(_1wx,[_1vI,_25V,_1vO,new T(function(){return B(A3(_2R,_2T(_25U),_25X,_25W));})]));},_25Y=function(_25Z,_260){return new T3(0,_25Z,new T(function(){return _1wx(_1vI,_260,_1vO);}),function(_261,_25S){return C > 19 ? new F(function(){return _25T(_25Z,_260,_261,_25S);}) : (++C,_25T(_25Z,_260,_261,_25S));});},_262=function(_263){return E(E(_263).b);},_264=function(_265,_266){return C > 19 ? new F(function(){return A3(_2R,_2T(_2P(_Ks(_266))),new T(function(){return _2V(_2P(_265));}),new T(function(){return _262(_266);}));}) : (++C,A3(_2R,_2T(_2P(_Ks(_266))),new T(function(){return _2V(_2P(_265));}),new T(function(){return _262(_266);})));},_267=function(_268,_269){return new T3(0,_268,new T(function(){return B(_264(_1vI,_269));}),function(_26a,_26b){return C > 19 ? new F(function(){return A3(_Su,_269,_26a,_26b);}) : (++C,A3(_Su,_269,_26a,_26b));});},_26c=function(_26d,_26e,_26f,_26g){return C > 19 ? new F(function(){return A3(_s6,_26e,new T(function(){return B(A3(_2R,_26e,_1vE,_26f));}),_26g);}) : (++C,A3(_s6,_26e,new T(function(){return B(A3(_2R,_26e,_1vE,_26f));}),_26g));},_26h=function(_26i,_26j){return new T2(0,_26i,function(_261,_25S){return C > 19 ? new F(function(){return _26c(_26i,_26j,_261,_25S);}) : (++C,_26c(_26i,_26j,_261,_25S));});},_26k=function(_26l,_26m){return C > 19 ? new F(function(){return A1(_26l,new T1(1,_26m));}) : (++C,A1(_26l,new T1(1,_26m)));},_26n=function(_26o,_26p){var _26q=E(_26o);if(!_26q){return E(_26p);}else{return _PB(function(_26r){return E(_26r)+_26q|0;},_26p);}},_26s=function(_26t,_26u){return _26n(E(_26t),_26u);},_26v=function(_26w){var _26x=E(_26w);return (_26x._==0)?__Z:new T2(1,function(_26y){var _26z=E(_26x.a);return new T4(0,1,_26z.a,_26z.b,E(_26y));},new T(function(){return _26v(_26x.b);}));},_26A=function(_26B){var _26C=E(_26B);return (_26C._==0)?__Z:new T2(1,new T(function(){return E(E(_26C.a).b);}),new T(function(){return _26A(_26C.b);}));},_26D=function(_26E,_26F){var _26G=new T(function(){return _Ks(_26F);}),_26H=new T(function(){return _1wx(_1vI,_26G,_1vO);}),_26I=new T(function(){return _2P(_26G);}),_26J=new T(function(){return B(A2(_2V,_26I,__Z));}),_26K=new T(function(){return _2T(_26I);}),_26L=new T(function(){return _2R(_26K);}),_26M=new T(function(){return _2V(_26I);}),_26N=new T(function(){return _1xn(_26F);}),_26O=new T(function(){return B(_264(_1vI,_26F));}),_26P=new T(function(){return _267(new T(function(){return _25Y(new T(function(){return _25K(function(_He){return C > 19 ? new F(function(){return _26k(_26M,_He);}) : (++C,_26k(_26M,_He));},new T(function(){return _26h(function(_Hd,_He){return C > 19 ? new F(function(){return _25O(_26L,_Hd,_He);}) : (++C,_25O(_26L,_Hd,_He));},_26K);}),_26I);}),_26G);}),_26F);}),_26Q=function(_26R,_26S){var _26T=E(_26R);if(!_26T._){return C > 19 ? new F(function(){return _26k(_26M,_26S);}) : (++C,_26k(_26M,_26S));}else{var _26U=E(_26S);if(!_26U._){if(!E(_26U.a)){return E(_26J);}else{var _26V=new T(function(){var _26W=function(_26X){var _26Y=E(_26X);return (_26Y._==0)?__Z:new T1(1,new T(function(){return B(_26Q(_26T.b,_26Y.a));}));};return B(A2(_26L,_26W,new T(function(){return B(_UK(_26E,_26P,_26T.a,0,_26U.d));})));});return C > 19 ? new F(function(){return A1(_26H,_26V);}) : (++C,A1(_26H,_26V));}}else{return E(_26J);}}},_26Z=function(_270,_271){var _272=E(_270);if(!_272._){var _273=_272.a,_274=new T(function(){var _275=new T(function(){return E(_273)+1|0;}),_276=function(_277){var _278=E(_277);if(!_278._){return __Z;}else{var _279=new T(function(){var _27a=E(_oy(_273,_278.a).b);if(!_27a._){return E(_26J);}else{return B(_26Q(_271,new T(function(){return B(_26s(_275,_27a.a));})));}});return new T1(1,_279);}};return B(A2(_26L,_276,_26O));});return C > 19 ? new F(function(){return A1(_26H,_274);}) : (++C,A1(_26H,_274));}else{var _27b=_272.a,_27c=_272.c,_27d=new T(function(){var _27e=function(_27f){var _27g=E(_27f);return (_27g._==0)?__Z:new T1(1,new T(function(){return B(_26Q(_271,_27g.a));}));},_27h=function(_27i){var _27j=E(_27i);if(!_27j._){return __Z;}else{var _27k=new T(function(){var _27l=new T(function(){return B(A2(_26L,_27e,new T(function(){return B(_UK(_26E,_26P,new T1(1,_27c),0,_27j.a));})));});return B(A1(_26H,_27l));});return new T1(1,_27k);}},_27m=new T(function(){return _26v(_27b);}),_27n=new T(function(){var _27o=new T(function(){return _26A(_27b);});return B(A3(_Su,_26F,function(_He){return _nK(_27o,_He);},new T(function(){var _27p=E(_27c);return B(_26Z(_27p.a,_27p.b));})));}),_27q=function(_27r){var _27s=E(_27r);if(!_27s._){return __Z;}else{var _27t=new T(function(){var _27u=new T(function(){var _27v=new T(function(){return B(A1(_26N,new T(function(){return B(A3(_2B,_6g,_27m,_27s.a));})));});return B(A2(_26L,_27h,_27v));});return B(A1(_26H,_27u));});return new T1(1,_27t);}};return B(A2(_26L,_27q,_27n));});return C > 19 ? new F(function(){return A1(_26H,_27d);}) : (++C,A1(_26H,_27d));}},_27w=function(_27x){var _27y=E(_27x);switch(_27y._){case 0:var _27z=_27y.c,_27A=_27y.d;if(!E(_27y.a)){var _27B=new T(function(){return B(A3(_Su,_26F,function(_He){return new T2(1,_27z,_He);},new T(function(){return B(_27w(_27A));})));});return C > 19 ? new F(function(){return A2(_26L,function(_27C){var _27D=E(_27C);return (_27D._==0)?__Z:new T1(1,new T4(0,1,_27y.b,_27z,_27D.a));},_27B);}) : (++C,A2(_26L,function(_27C){var _27D=E(_27C);return (_27D._==0)?__Z:new T1(1,new T4(0,1,_27y.b,_27z,_27D.a));},_27B));}else{var _27E=new T(function(){var _27F=new T(function(){return B(A3(_Su,_26F,function(_He){return new T2(1,_27z,_He);},new T(function(){return B(_27w(_27A));})));}),_27G=function(_27H){var _27I=E(_27H);if(!_27I._){return __Z;}else{var _27J=new T(function(){var _27K=new T(function(){var _27L=function(_27M){var _27N=E(_27M);if(!_27N._){return __Z;}else{var _27O=new T(function(){var _27P=E(_27I.a);if(_27P._==2){var _27Q=E(_27N.a);if(_27Q._==2){return B(A1(_26M,new T1(1,new T1(2,new T(function(){return _BV(_27P.a,_27Q.a);})))));}else{return E(_26J);}}else{return E(_26J);}});return new T1(1,_27O);}};return B(A2(_26L,_27L,_27F));});return B(A1(_26H,_27K));});return new T1(1,_27J);}};return B(A2(_26L,_27G,new T(function(){return B(_27w(_27z));})));});return C > 19 ? new F(function(){return A1(_26H,_27E);}) : (++C,A1(_26H,_27E));}break;case 1:var _27R=E(_27y.a);return C > 19 ? new F(function(){return _26Z(_27R.a,_27R.b);}) : (++C,_26Z(_27R.a,_27R.b));break;default:return C > 19 ? new F(function(){return A1(_26M,new T1(1,new T1(2,new T(function(){return E(_27y.a)+1|0;}))));}) : (++C,A1(_26M,new T1(1,new T1(2,new T(function(){return E(_27y.a)+1|0;})))));}};return _27w;},_27S=function(_27T,_27U){var _27V=E(_27U);if(!_27V._){return new T2(0,__Z,__Z);}else{var _27W=_27V.a;if(!B(A1(_27T,_27W))){var _27X=new T(function(){var _27Y=_27S(_27T,_27V.b);return new T2(0,_27Y.a,_27Y.b);});return new T2(0,new T2(1,_27W,new T(function(){return E(E(_27X).a);})),new T(function(){return E(E(_27X).b);}));}else{return new T2(0,__Z,_27V);}}},_27Z=function(_280,_281){while(1){var _282=E(_281);if(!_282._){return __Z;}else{if(!B(A1(_280,_282.a))){return _282;}else{_281=_282.b;continue;}}}},_283=function(_284){var _285=_284>>>0;if(_285>887){var _286=u_iswspace(_284);return (E(_286)==0)?false:true;}else{return (_285==32)?true:(_285-9>>>0>4)?(_285==160)?true:false:true;}},_287=function(_288){return _283(E(_288));},_289=function(_28a){var _28b=_27Z(_287,_28a);if(!_28b._){return __Z;}else{var _28c=new T(function(){var _28d=_27S(_287,_28b);return new T2(0,_28d.a,_28d.b);});return new T2(1,new T(function(){return E(E(_28c).a);}),new T(function(){return _289(E(_28c).b);}));}},_28e=new T(function(){return unCStr("hClose");}),_28f=function(_28g,_28h,_){var _28i=E(_28g);if(!_28i._){return 0;}else{var _28j=E(_28i.a),_28k=B(A2(_M,_28j.a,_)),_28l=hs_eqWord64(_28k.a,new Long(4053623282,1685460941,true));if(!_28l){return die(_28j);}else{var _28m=hs_eqWord64(_28k.b,new Long(3693590983,2507416641,true));if(!_28m){return die(_28j);}else{var _28n=new T(function(){return _1K(new T(function(){return _1dW(_28j.b,_28e,_28h);}));});return die(_28n);}}}},_28o=function(_28p){while(1){var _28q=(function(_28r){var _28s=E(_28r);if(!_28s._){return __Z;}else{var _28t=_28s.b,_28u=E(_28s.a);if(!_28u._){_28p=_28t;return __continue;}else{return new T2(1,_28u.a,new T(function(){return _28o(_28t);}));}}})(_28p);if(_28q!=__continue){return _28q;}}},_28v=function(_28w,_){var _28x=E(_28w);if(!_28x._){var _28y=_28x.b;if(!0){var _28z=(function(_){var _28A=_1e3(_28e,_28x,_1ez,_28y,_),_28B=E(_28A),_=putMVar(_28y,_28B.a);return _28B.b;})();return _28f(_28z,_28x,_);}else{var _28C=_1e3(_28e,_28x,_1ez,_28y,_),_28D=E(_28C),_=putMVar(_28y,_28D.a);return _28f(_28D.b,_28x,_);}}else{var _28E=_28x.b,_28F=_28x.c,_28G=function(_,_28H){var _28I=function(_,_28J){var _28K=_28o(new T2(1,_28H,new T2(1,_28J,__Z)));if(!_28K._){return _28f(__Z,_28x,_);}else{return _28f(new T1(1,_28K.a),_28x,_);}};if(!0){var _28L=(function(_){var _28M=_1e3(_28e,_28x,_1ez,_28F,_),_28N=E(_28M),_=putMVar(_28F,_28N.a);return _28N.b;})();return _28I(_,_28L);}else{var _28O=_1e3(_28e,_28x,_1ez,_28F,_),_28P=E(_28O),_=putMVar(_28F,_28P.a);return _28I(_,_28P.b);}};if(!0){var _28Q=(function(_){var _28R=_1e3(_28e,_28x,_1ez,_28E,_),_28S=E(_28R),_=putMVar(_28E,_28S.a);return _28S.b;})();return C > 19 ? new F(function(){return _28G(_,_28Q);}) : (++C,_28G(_,_28Q));}else{var _28T=_1e3(_28e,_28x,_1ez,_28E,_),_28U=E(_28T),_=putMVar(_28E,_28U.a);return C > 19 ? new F(function(){return _28G(_,_28U.b);}) : (++C,_28G(_,_28U.b));}}},_28V=function(_28W,_28X,_){var _28Y=jsWriteHandle(E(_28W),toJSStr(E(_28X)));return 0;},_28Z=function(_290,_291,_){if(!0){var _292=function(_){var _293=_1QE(_290,1,_),_294=_293,_295=function(_){return _28V(_294,_291,_);},_296=jsCatch(function(_){return _295();},function(_297,_){var _298=B(_28v(_294,_));return die(_297);}),_299=B(_28v(_294,_));return _296;};return _292();}else{var _29a=_1QE(_290,1,_),_29b=_29a,_29c=jsCatch(function(_){return _28V(_29b,_291,_);},function(_29d,_){var _29e=B(_28v(_29b,_));return die(_29d);}),_29f=B(_28v(_29b,_));return _29c;}},_29g=function(_29h,_29i){var _29j=E(_29h);if(!_29j._){return __Z;}else{var _29k=E(_29i);return (_29k._==0)?__Z:new T2(1,new T2(0,_29j.a,_29k.a),new T(function(){return _29g(_29j.b,_29k.b);}));}},_29l=function(_29m,_29n,_29o){var _29p=new T(function(){return _26D(_29m,_1zI);}),_29q=new T(function(){return _IQ(new T(function(){return _IU(_29m);}));}),_29r=new T(function(){return _2x(_29q);}),_29s=new T(function(){return _IS(_29o);}),_29t=new T(function(){return _2P(_29s);}),_29u=new T(function(){return _2T(_29t);}),_29v=new T(function(){return B(A2(_2R,_29u,_sx));}),_29w=new T(function(){return _s6(_29u);}),_29x=new T(function(){return B(A2(_2V,_29t,0));}),_29y=new T(function(){var _29z=function(_29A){var _29B=new T(function(){var _29C=E(E(_29A).b);if(!_29C._){return __Z;}else{var _29D=E(_29C.a);if(_29D._==2){var _29E=new T(function(){var _29F=_1RG(_7B(_1AA,new T(function(){return B(A2(_1nG,_29m,_29D.a));})));if(!_29F._){return E(_1At);}else{if(!E(_29F.b)._){return E(_29F.a);}else{return E(_1Au);}}});return new T2(1,new T1(1,_29E),_29C.b);}else{return _29C;}}});return new T3(0,0,_29B,_2L);};return B(A2(_1RP,_29o,_29z));}),_29G=new T(function(){return B(A2(_1QP,_29o,_Wy));}),_29H=new T(function(){return B(A2(_1QP,_29o,_X7));}),_29I=new T(function(){return _1RP(_29o);}),_29J=new T(function(){return _1RN(_29o);}),_29K=new T(function(){var _29L=function(_29M){var _29N=new T(function(){var _29O=E(E(_29M).b);if(!_29O._){return __Z;}else{var _29P=E(_29O.a);if(_29P._==2){var _29Q=E(_29O.b);if(!_29Q._){return _29O;}else{var _29R=E(_29Q.a);if(_29R._==2){return new T2(1,new T1(2,new T(function(){return B(A2(_29r,_29R.a,_29P.a));})),_29Q.b);}else{return _29O;}}}else{return _29O;}}});return new T3(0,0,_29N,_2L);};return B(A2(_1RP,_29o,_29L));}),_29S=new T(function(){return _2V(_29t);}),_29T=new T(function(){var _29U=new T(function(){return B(A1(_29S,0));}),_29V=function(_29W){var _29X=E(_29W);if(!_29X._){return __Z;}else{var _29Y=new T(function(){var _29Z=E(_29X.a);if(_29Z._==2){var _2a0=function(_2a1){var _2a2=new T(function(){var _2a3=E(E(_2a1).b),_2a4=function(_2a5){return C > 19 ? new F(function(){return A1(_2a3.d,new T(function(){return B(A2(_29r,_29Z.a,_2a5));}));}) : (++C,A1(_2a3.d,new T(function(){return B(A2(_29r,_29Z.a,_2a5));})));};return new T4(0,_2a3.a,_2a3.b,_2a3.c,_2a4);});return new T3(0,0,_2a2,_2L);};return B(A2(_1QP,_29o,_2a0));}else{return E(_29U);}});return new T2(1,_29Y,new T(function(){return _29V(_29X.b);}));}},_2a6=function(_2a7){var _2a8=E(_2a7);if(!_2a8._){return __Z;}else{var _2a9=new T(function(){return B(A1(_29w,new T(function(){return B(A1(_29v,_2a8.a));})));});return new T2(1,_2a9,new T(function(){return _2a6(_2a8.b);}));}};return B(A3(_2X,_29s,new T(function(){return B(A2(_1RP,_29o,_WE));}),function(_2aa){return C > 19 ? new F(function(){return A3(_2B,_6h,_2a6(_29V(_oy(1,_2aa).a)),_29x);}) : (++C,A3(_2B,_6h,_2a6(_29V(_oy(1,_2aa).a)),_29x));}));}),_2ab=new T(function(){var _2ac=new T(function(){return B(A1(_29S,0));}),_2ad=new T(function(){return _1sr(_29m);}),_2ae=function(_2af){var _2ag=E(_2af);if(!_2ag._){return E(_2ac);}else{var _2ah=E(_2ag.a);if(_2ah._==2){var _2ai=_2ah.a,_2aj=function(_2ak){return C > 19 ? new F(function(){return A2(_1RP,_29o,function(_2al){return E(new T3(0,0,new T2(1,new T1(5,_2ak),_2ag.b),_2L));});}) : (++C,A2(_1RP,_29o,function(_2al){return E(new T3(0,0,new T2(1,new T1(5,_2ak),_2ag.b),_2L));}));},_2am=new T(function(){var _2an=function(_){var _2ao=function(_){var _2ap=function(_2aq,_){var _2ar=_1QE(new T(function(){return B(A2(_1nG,_29m,_2ai));}),0,_);return _1iW(_2ar,_);},_2as=function(_){var _2at=_1QE(new T(function(){return _nK(B(A2(_1nG,_29m,_2ai)),_1A1);}),0,_);return _1iW(_2at,_);},_2au=jsCatch(_2as,_2ap),_2av=B(_mu(_4S,_1Rc,_mg,_2ad,_2au));return (_2av._==0)?E(_2L):_2av.a;};return jsCatch(_2ao,_1vC);};return B(A2(_1j2,_29n,_2an));});return C > 19 ? new F(function(){return A3(_2X,_29s,_2am,_2aj);}) : (++C,A3(_2X,_29s,_2am,_2aj));}else{return E(_2ac);}}};return B(A3(_2X,_29s,new T(function(){return B(A2(_1RP,_29o,_Xs));}),_2ae));}),_2aw=new T(function(){return _IW(_29m);}),_2ax=new T(function(){var _2ay=new T(function(){return B(A1(_29S,0));}),_2az=new T(function(){return B(A2(_1RN,_29o,_Xj));}),_2aA=new T(function(){return B(A2(_1QP,_29o,_1vA));}),_2aB=new T(function(){return _1j2(_29n);}),_2aC=new T(function(){return _1nG(_29m);}),_2aD=new T(function(){return _1RP(_29o);}),_2aE=new T(function(){return B(A3(_Zf,_29o,new T(function(){return _29l(_29m,_29n,_29o);}),function(_1k5){return C > 19 ? new F(function(){return _1QR(_29r,_29o,_1k5);}) : (++C,_1QR(_29r,_29o,_1k5));}));}),_2aF=new T(function(){return B(A1(_2aw,__Z));}),_2aG=function(_2aH){var _2aI=E(_2aH);if(!_2aI._){return __Z;}else{var _2aJ=new T(function(){return B(A1(_29w,new T(function(){return B(A1(_29v,_2aI.a));})));});return new T2(1,_2aJ,new T(function(){return _2aG(_2aI.b);}));}},_2aK=function(_2aL){var _2aM=E(_2aL);if(!_2aM._){return E(_2ay);}else{var _2aN=E(_2aM.a);if(_2aN._==2){var _2aO=E(_2aM.b);if(!_2aO._){return E(_2ay);}else{var _2aP=E(_2aO.a);if(_2aP._==5){var _2aQ=new T(function(){return B(A2(_1nG,_29m,_2aN.a));}),_2aR=new T(function(){return B(A3(_2R,_29u,_s3,new T(function(){return B(A3(_2B,_6h,_2aG(_Iz(_2aE,_2aP.a)),_29x));})));}),_2aS=function(_2aT){var _2aU=new T(function(){var _2aV=new T(function(){return B(_5m(_1Ra,_1zN,function(_2aW){return new T2(0,_2aT,_2aW);}));});return B(A2(_1RN,_29o,_2aV));}),_2aX=function(_2aY){var _2aZ=new T(function(){var _2b0=new T(function(){var _2b1=new T(function(){return B(_5m(_1vz,_5C,function(_2b2){return new T2(0,_2aY,_2b2);}));});return B(A2(_1QP,_29o,_2b1));}),_2b3=function(_2b4){var _2b5=new T(function(){return B(A1(_2aD,function(_2b6){return E(new T3(0,0,new T2(1,new T1(4,_2b4),_2aO.b),_2L));}));}),_2b7=function(_2b8){var _2b9=new T(function(){var _2ba=new T(function(){var _2bb=new T(function(){return B(A1(_2aC,new T(function(){return B(A1(_2b8,_2aF));})));});return B(A1(_2aB,function(_){return _28Z(_2aQ,_2bb,_);}));});return B(A3(_2R,_29u,_s3,_2ba));});return C > 19 ? new F(function(){return A3(_s6,_29u,_2b9,_2b5);}) : (++C,A3(_s6,_29u,_2b9,_2b5));};return C > 19 ? new F(function(){return A3(_2X,_29s,_2b0,_2b7);}) : (++C,A3(_2X,_29s,_2b0,_2b7));};return B(A3(_2X,_29s,_2aU,_2b3));});return C > 19 ? new F(function(){return A3(_s6,_29u,_2aR,_2aZ);}) : (++C,A3(_s6,_29u,_2aR,_2aZ));};return C > 19 ? new F(function(){return A3(_2X,_29s,_2aA,_2aX);}) : (++C,A3(_2X,_29s,_2aA,_2aX));};return C > 19 ? new F(function(){return A3(_2X,_29s,_2az,_2aS);}) : (++C,A3(_2X,_29s,_2az,_2aS));}else{return E(_2ay);}}}else{return E(_2ay);}}};return B(A3(_2X,_29s,new T(function(){return B(A2(_1RP,_29o,_Xp));}),_2aK));}),_2bc=new T(function(){var _2bd=new T(function(){return B(A1(_29S,0));}),_2be=new T(function(){return _1j2(_29n);}),_2bf=function(_2bg){var _2bh=E(_2bg);if(!_2bh._){return E(_2bd);}else{var _2bi=E(_2bh.a);if(_2bi._==2){var _2bj=function(_2bk){var _2bl=new T(function(){return B(A1(_2aw,new T(function(){var _2bm=E(_2bk);if(!_2bm._){return __Z;}else{return E(_2bm.a);}})));});return C > 19 ? new F(function(){return A2(_1RP,_29o,function(_2bn){return E(new T3(0,0,new T2(1,new T1(2,_2bl),_2bh.b),_2L));});}) : (++C,A2(_1RP,_29o,function(_2bn){return E(new T3(0,0,new T2(1,new T1(2,_2bl),_2bh.b),_2L));}));},_2bo=new T(function(){var _2bp=function(_){var _2bq=B(A1(E(_12y).a,_));return _YU(_2bq,new T(function(){return B(A2(_1nG,_29m,_2bi.a));}),_1dG,_);};return B(A1(_2be,_2bp));});return C > 19 ? new F(function(){return A3(_2X,_29s,_2bo,_2bj);}) : (++C,A3(_2X,_29s,_2bo,_2bj));}else{return E(_2bd);}}};return B(A3(_2X,_29s,new T(function(){return B(A2(_1RP,_29o,_Xm));}),_2bf));}),_2br=new T(function(){var _2bs=new T(function(){return _1RP(_29o);}),_2bt=function(_2bu){var _2bv=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_2bu)),0));}),_2bw=function(_2bx){return new T3(0,0,new T(function(){var _2by=E(E(_2bx).b);if(!_2by._){return __Z;}else{var _2bz=E(_2by.a);if(_2bz._==1){return new T2(1,new T1(6,new T2(0,_2bv,new T1(2,_2bz.a))),_2by.b);}else{return _2by;}}}),_2L);};return C > 19 ? new F(function(){return A1(_2bs,_2bw);}) : (++C,A1(_2bs,_2bw));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_Xg));}),_2bt));}),_2bA=new T(function(){var _2bB=new T(function(){return _1QP(_29o);}),_2bC=new T(function(){return B(A1(_29S,0));}),_2bD=function(_2bE){var _2bF=E(_2bE);if(!_2bF._){return E(_2bC);}else{var _2bG=E(_2bF.a),_2bH=_2bG.b,_2bI=new T(function(){return E(E(_2bH).a);}),_2bJ=function(_2bK){var _2bL=new T(function(){var _2bM=E(E(_2bK).b),_2bN=_2bM.b,_2bO=new T(function(){var _2bP=E(_2bH).b,_2bQ=B(A3(_2B,_6g,_CV(_CS(_2bN)),0))-E(_2bG.a)|0;if(!_2bQ){return E(_2bP);}else{return _PB(function(_2bR){return E(_2bR)+_2bQ|0;},_2bP);}});return new T4(0,_2bM.a,new T2(1,new T2(0,_2bI,_2bO),_2bN),_2bM.c,_2bM.d);});return new T3(0,0,_2bL,_2L);};return C > 19 ? new F(function(){return A1(_2bB,_2bJ);}) : (++C,A1(_2bB,_2bJ));}};return B(A3(_2X,_29s,new T(function(){return B(A2(_1RP,_29o,_1Af));}),_2bD));}),_2bS=new T(function(){var _2bT=new T(function(){return _1RP(_29o);}),_2bU=function(_2bV){var _2bW=new T(function(){return _1Ro(_2bV);}),_2bX=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_2bV)),0));}),_2bY=function(_2bZ){var _2c0=new T(function(){var _2c1=E(E(_2bZ).b);if(!_2c1._){return __Z;}else{var _2c2=E(_2c1.a);if(_2c2._==6){var _2c3=E(_2c2.a);if(!_2c3._){var _2c4=_2c3.b,_2c5=E(_2c1.b);if(!_2c5._){return _2c1;}else{var _2c6=E(_2c5.a);if(_2c6._==6){var _2c7=E(_2c6.a);if(!_2c7._){var _2c8=_2c7.b,_2c9=new T(function(){var _2ca=new T(function(){var _2cb=(1+E(_2bX)|0)-E(_2c7.a)|0;if(!_2cb){return E(_2c8);}else{return _PB(function(_2cc){return E(_2cc)+_2cb|0;},_2c8);}}),_2cd=new T(function(){var _2ce=E(_2bX)-E(_2c3.a)|0;if(!_2ce){return E(_2c4);}else{return _PB(function(_2cf){return E(_2cf)+_2ce|0;},_2c4);}});return B(A(_UK,[_29m,_1zI,_2cd,0,new T1(1,new T2(0,_1AB,new T2(1,_2ca,__Z))),_2bW]));});return new T2(1,new T1(6,new T2(0,_2bX,_2c9)),_2c5.b);}else{return _2c1;}}else{return _2c1;}}}else{return _2c1;}}else{return _2c1;}}});return new T3(0,0,_2c0,_2L);};return C > 19 ? new F(function(){return A1(_2bT,_2bY);}) : (++C,A1(_2bT,_2bY));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_Xa));}),_2bU));}),_2cg=new T(function(){var _2ch=new T(function(){return _1RP(_29o);}),_2ci=function(_2cj){var _2ck=new T(function(){return _1Rr(_2cj);}),_2cl=function(_2cm){var _2cn=new T(function(){var _2co=E(E(_2cm).b);if(!_2co._){return __Z;}else{var _2cp=_2co.b,_2cq=E(_2co.a);if(_2cq._==6){var _2cr=E(_2cq.a);if(!_2cr._){var _2cs=_2cr.a,_2ct=_2cr.b,_2cu=function(_2cv){var _2cw=new T(function(){var _2cx=B(A2(_29p,_2ct,new T(function(){return _25n(_2cs,_2ck);})));if(!_2cx._){return new T0(1);}else{return new T2(0,_2cs,_2cx.a);}});return new T2(1,new T1(6,_2cw),_2cp);},_2cy=E(_2ct);if(_2cy._==1){var _2cz=E(_2cy.a),_2cA=E(_2cz.a);if(!_2cA._){var _2cB=_2cA.a;if(!E(_2cz.b)._){var _2cC=E(_oy(_2cB,_2cj).b);if(!_2cC._){return _2cu(_);}else{return new T2(1,new T1(6,new T2(0,new T(function(){return (E(_2cs)-E(_2cB)|0)-1|0;}),E(_2cC.a).b)),_2cp);}}else{return _2cu(_);}}else{return _2cu(_);}}else{return _2cu(_);}}else{return _2co;}}else{return _2co;}}});return new T3(0,0,_2cn,_2L);};return C > 19 ? new F(function(){return A1(_2ch,_2cl);}) : (++C,A1(_2ch,_2cl));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_X4));}),_2ci));}),_2cD=new T(function(){var _2cE=new T(function(){return _1RP(_29o);}),_2cF=function(_2cG){var _2cH=function(_2cI){var _2cJ=new T(function(){var _2cK=E(E(_2cI).b);if(!_2cK._){return __Z;}else{var _2cL=_2cK.b,_2cM=E(_2cK.a);if(_2cM._==6){var _2cN=E(_2cM.a);if(!_2cN._){var _2cO=_2cN.a,_2cP=_2cN.b,_2cQ=B(A2(_29p,_2cP,new T(function(){return _1Ru(_25n(_2cO,_2cG));})));if(!_2cQ._){return new T2(1,_1vp,_2cL);}else{var _2cR=B(A2(_1zM,_2cQ.a,new T(function(){return _1Ru(_25n(_2cO,_2cG));})));if(!_2cR._){return new T2(1,_1vp,_2cL);}else{var _2cS=new T(function(){return B(A(_UK,[_29m,_1zI,_2cP,0,new T1(1,new T2(0,new T3(1,__Z,new T(function(){return _1Rd(_2cR.a);}),new T2(0,_1AB,__Z)),__Z)),new T(function(){return _1Ru(_25n(_2cO,_2cG));})]));});return new T2(1,new T1(6,new T2(0,_2cO,_2cS)),_2cL);}}}else{return _2cK;}}else{return _2cK;}}});return new T3(0,0,_2cJ,_2L);};return C > 19 ? new F(function(){return A1(_2cE,_2cH);}) : (++C,A1(_2cE,_2cH));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_X1));}),_2cF));}),_2cT=new T(function(){var _2cU=new T(function(){return _1RP(_29o);}),_2cV=new T(function(){return B(A1(_2aw,_1An));}),_2cW=function(_2cX){var _2cY=E(_2cX);if(!_2cY._){return __Z;}else{var _2cZ=_2cY.a,_2d0=function(_2d1){var _2d2=new T(function(){var _2d3=E(_2d1);if(!E(_2d3.a)){return B(A2(_29r,_2cZ,new T(function(){return B(A2(_29r,_2cV,_2d3.b));})));}else{return E(_2cZ);}});return new T2(0,false,_2d2);};return new T2(1,_2d0,new T(function(){return _2cW(_2cY.b);}));}},_2d4=new T(function(){return _2z(_29q);}),_2d5=function(_2d6,_2d7){var _2d8=new T(function(){var _2d9=function(_2da){var _2db=E(_2da);return (_2db._==0)?__Z:new T2(1,new T(function(){var _2dc=E(_2db.a);if(!_2dc._){return E(_2dc.a);}else{return _10p(_oy(_2dc.a,_2d6).b);}}),new T(function(){return _2d9(_2db.b);}));};return E(B(A3(_2B,_6h,_2cW(_2d9(_2d7)),new T2(0,true,_2d4))).b);});return new T2(0,_2d6,new T1(2,_2d8));},_2dd=function(_2de){var _2df=E(_2de),_2dg=_2d5(_2df.a,_2df.b);return new T2(0,_2dg.a,_2dg.b);},_2dh=function(_2di){var _2dj=new T(function(){var _2dk=E(_2di),_2dl=_Jw(_2dd,_2dk.a,_2dk.b,_2dk.c);return new T3(0,_2dl.a,_2dl.b,_2dl.c);}),_2dm=function(_2dn){return new T3(0,0,new T2(1,new T1(6,new T1(2,_2dj)),new T(function(){return E(E(_2dn).b);})),_2L);};return C > 19 ? new F(function(){return A1(_2cU,_2dm);}) : (++C,A1(_2cU,_2dm));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_WM));}),_2dh));}),_2do=new T(function(){var _2dp=new T(function(){return _1RP(_29o);}),_2dq=function(_2dr){var _2ds=function(_2dt){var _2du=new T(function(){var _2dv=E(E(_2dt).b);if(!_2dv._){return __Z;}else{var _2dw=E(_2dv.b);if(!_2dw._){return _2dv;}else{var _2dx=E(_2dw.a);if(_2dx._==6){var _2dy=E(_2dx.a);if(!_2dy._){var _2dz=E(_2dw.b);if(!_2dz._){return _2dv;}else{var _2dA=E(_2dz.a);if(_2dA._==6){var _2dB=E(_2dA.a);if(_2dB._==2){var _2dC=new T(function(){var _2dD=new T(function(){return _1Rx(_25n(_2dy.a,_2dr));});return B(A(_Hf,[_1Rb,_2dy.b,_4P,function(_2dE){return E(new T1(1,new T2(0,_2dD,_2dv.a)));},_2dB.a]));});return new T2(1,new T1(6,new T1(2,_2dC)),_2dz.b);}else{return _2dv;}}else{return _2dv;}}}else{return _2dv;}}else{return _2dv;}}}});return new T3(0,0,_2du,_2L);};return C > 19 ? new F(function(){return A1(_2dp,_2ds);}) : (++C,A1(_2dp,_2ds));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_WH));}),_2dq));}),_2dF=new T(function(){var _2dG=new T(function(){return _1RP(_29o);}),_2dH=new T(function(){return B(A1(_2aw,__Z));}),_2dI=new T(function(){return _25q(_29m);}),_2dJ=function(_2dK){var _2dL=new T(function(){return E(E(_2dK).c);}),_2dM=new T(function(){return E(E(_2dK).b);}),_2dN=function(_2dO,_2dP){var _2dQ=E(_2dO);if(!_2dQ._){return new T2(0,_2dH,_2dP);}else{var _2dR=_2dQ.b,_2dS=E(_2dQ.a);if(_2dS==37){var _2dT=E(_2dR);if(!_2dT._){var _2dU=new T(function(){var _2dV=_2dN(__Z,_2dP);return new T2(0,_2dV.a,_2dV.b);}),_2dW=new T(function(){return B(A2(_29r,new T(function(){return B(A1(_2aw,new T2(1,_2dS,__Z)));}),new T(function(){return E(E(_2dU).a);})));});return new T2(0,_2dW,new T(function(){return E(E(_2dU).b);}));}else{var _2dX=_2dT.b;switch(E(_2dT.a)){case 115:var _2dY=E(_2dP);if(!_2dY._){var _2dZ=new T(function(){var _2e0=_2dN(_2dT,__Z);return new T2(0,_2e0.a,_2e0.b);}),_2e1=new T(function(){return B(A2(_29r,new T(function(){return B(A1(_2aw,new T2(1,_2dS,__Z)));}),new T(function(){return E(E(_2dZ).a);})));});return new T2(0,_2e1,new T(function(){return E(E(_2dZ).b);}));}else{var _2e2=E(_2dY.a);if(_2e2._==2){var _2e3=new T(function(){var _2e4=_2dN(_2dX,_2dY.b);return new T2(0,_2e4.a,_2e4.b);}),_2e5=new T(function(){return B(A2(_29r,_2e2.a,new T(function(){return E(E(_2e3).a);})));});return new T2(0,_2e5,new T(function(){return E(E(_2e3).b);}));}else{var _2e6=new T(function(){var _2e7=_2dN(_2dT,_2dY);return new T2(0,_2e7.a,_2e7.b);}),_2e8=new T(function(){return B(A2(_29r,new T(function(){return B(A1(_2aw,new T2(1,_2dS,__Z)));}),new T(function(){return E(E(_2e6).a);})));});return new T2(0,_2e8,new T(function(){return E(E(_2e6).b);}));}}break;case 118:var _2e9=E(_2dP);if(!_2e9._){var _2ea=new T(function(){var _2eb=_2dN(_2dT,__Z);return new T2(0,_2eb.a,_2eb.b);}),_2ec=new T(function(){return B(A2(_29r,new T(function(){return B(A1(_2aw,new T2(1,_2dS,__Z)));}),new T(function(){return E(E(_2ea).a);})));});return new T2(0,_2ec,new T(function(){return E(E(_2ea).b);}));}else{var _2ed=new T(function(){var _2ee=_2dN(_2dX,_2e9.b);return new T2(0,_2ee.a,_2ee.b);}),_2ef=new T(function(){return B(A2(_29r,new T(function(){return B(A3(_2dI,_2dL,_2dM,_2e9.a));}),new T(function(){return E(E(_2ed).a);})));});return new T2(0,_2ef,new T(function(){return E(E(_2ed).b);}));}break;default:var _2eg=new T(function(){var _2eh=_2dN(_2dT,_2dP);return new T2(0,_2eh.a,_2eh.b);}),_2ei=new T(function(){return B(A2(_29r,new T(function(){return B(A1(_2aw,new T2(1,_2dS,__Z)));}),new T(function(){return E(E(_2eg).a);})));});return new T2(0,_2ei,new T(function(){return E(E(_2eg).b);}));}}}else{var _2ej=new T(function(){var _2ek=_2dN(_2dR,_2dP);return new T2(0,_2ek.a,_2ek.b);}),_2el=new T(function(){return B(A2(_29r,new T(function(){return B(A1(_2aw,new T2(1,_2dS,__Z)));}),new T(function(){return E(E(_2ej).a);})));});return new T2(0,_2el,new T(function(){return E(E(_2ej).b);}));}}},_2em=function(_2en){return new T3(0,0,new T(function(){var _2eo=E(E(_2en).b);if(!_2eo._){return __Z;}else{var _2ep=E(_2eo.a);if(_2ep._==2){var _2eq=_2dN(B(A2(_1nG,_29m,_2ep.a)),_2eo.b);return new T2(1,new T1(2,_2eq.a),_2eq.b);}else{return _2eo;}}}),_2L);};return C > 19 ? new F(function(){return A1(_2dG,_2em);}) : (++C,A1(_2dG,_2em));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_WB));}),_2dJ));}),_2er=new T(function(){return _IO(new T(function(){return _nX(new T(function(){return _IM(_29o);}));}));}),_2es=new T(function(){var _2et=new T(function(){return _1RP(_29o);}),_2eu=function(_2ev){var _2ew=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_2ev)),0));}),_2ex=new T(function(){return _IF(_1zW,new T(function(){return _10M(_2er,_2aw,_29r,_2ev);},1));}),_2ey=function(_2ez){return new T3(0,0,new T(function(){var _2eA=E(E(_2ez).b);if(!_2eA._){return __Z;}else{var _2eB=E(_2eA.a);if(_2eB._==2){var _2eC=B(_J1(_2er,_2eB.a,_3C,_3F,_2ex));if(!_2eC._){return _2eA;}else{return new T2(1,new T1(6,new T2(0,_2ew,new T1(1,new T2(0,new T1(0,_2eC.a),__Z)))),_2eA.b);}}else{return _2eA;}}}),_2L);};return C > 19 ? new F(function(){return A1(_2et,_2ey);}) : (++C,A1(_2et,_2ey));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_Xd));}),_2eu));}),_2eD=new T(function(){var _2eE=new T(function(){return _1RP(_29o);}),_2eF=function(_2eG){var _2eH=function(_2eI){return new T3(0,0,new T(function(){var _2eJ=E(E(_2eI).b);return new T4(0,_2eJ.a,_2eG,_2eJ.c,_2eJ.d);}),_2L);};return C > 19 ? new F(function(){return A2(_1QP,_29o,_2eH);}) : (++C,A2(_1QP,_29o,_2eH));},_2eK=function(_2eL){var _2eM=new T(function(){var _2eN=new T(function(){var _2eO=new T(function(){return _29g(_1zQ,_2eL);}),_2eP=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_2eL)),0));}),_2eQ=function(_2eR){var _2eS=E(_2eR);if(!_2eS._){return E(new T2(0,__Z,_2eL));}else{var _2eT=E(_2eS.a);if(_2eT._==2){var _2eU=E(_2eS.b);if(!_2eU._){return new T2(0,_2eS,_2eL);}else{var _2eV=E(_2eU.a);if(_2eV._==2){var _2eW=E(_2eU.b);if(!_2eW._){return new T2(0,_2eS,_2eL);}else{var _2eX=E(_2eW.a);if(_2eX._==6){var _2eY=E(_2eX.a);if(!_2eY._){var _2eZ=_2eY.a,_2f0=_2eY.b,_2f1=new T(function(){var _2f2=function(_2f3){var _2f4=E(_2f3);if(!_2f4._){return __Z;}else{var _2f5=_2f4.a,_2f6=new T(function(){if(!B(A3(_bX,_2er,new T(function(){return E(E(E(_2f5).b).a);}),_2eT.a))){return new T1(1,new T(function(){return _IK(_2f5);}));}else{return new T1(0,new T(function(){return _IK(_2f5);}));}});return new T2(1,_2f6,new T(function(){return _2f2(_2f4.b);}));}};return _2f2(_2eO);}),_2f7=E(B(A1(_1zY,_2f1)).a);if(!_2f7._){return new T2(0,_2eS,_2eL);}else{var _2f8=E(_2f7.a).a,_2f9=new T(function(){return (E(_2f8)+E(_2eZ)|0)-E(_2eP)|0;});if(!_1dP(true,_Rs(_Xv,_Rs(function(_2fa){return _C3(_2fa,_2f9);},B(_S2(_2f0)))))){return new T2(0,_2eS,_2eL);}else{var _2fb=new T(function(){var _2fc=new T(function(){var _2fd=E(_2eP)-(E(_2eZ)+(E(_2f8)+1|0)|0)|0;if(!_2fd){return E(_2f0);}else{return _PB(function(_2fe){return E(_2fe)+_2fd|0;},_2f0);}}),_2ff=function(_2fg){var _2fh=E(_2fg);if(!_2fh._){return __Z;}else{var _2fi=_2fh.a,_2fj=new T(function(){return E(E(_2fi).a);}),_2fk=function(_2fl,_2fm){var _2fn=E(_2f8),_2fo=E(_2fm);if(_2fn>=_2fo){if(_2fn!=_2fo){var _2fp=new T(function(){return _PB(function(_2fq){var _2fr=E(_2fq);return ((_2fo+_2fr|0)<_2fn)?_2fr:_2fr+1|0;},E(_2fi).b);});return new T2(1,new T2(0,_2fj,_2fp),new T(function(){return B(A1(_2fl,_2fo+1|0));}));}else{var _2fs=new T(function(){return _PB(function(_2ft){var _2fu=E(_2ft);return ((_2fo+_2fu|0)<_2fn)?_2fu:_2fu+1|0;},E(_2fi).b);});return new T2(1,new T2(0,_2fj,_2fs),new T2(1,new T2(0,_2eV.a,_2fc),new T(function(){return B(A1(_2fl,_2fo+1|0));})));}}else{return new T2(1,_2fi,new T(function(){return B(A1(_2fl,_2fo+1|0));}));}};return new T2(1,_2fk,new T(function(){return _2ff(_2fh.b);}));}};return B(A(_2B,[_6h,_2ff(_2eL),_1Ar,0]));}),_2fv=new T(function(){var _2fw=new T(function(){return E(_2eZ)+1|0;}),_2fx=new T(function(){return E(_2f8)+1|0;}),_2fy=function(_2fz){var _2fA=E(_2fz);if(!_2fA._){return __Z;}else{var _2fB=new T(function(){var _2fC=E(_2fA.a);if(_2fC._==6){var _2fD=E(_2fC.a);if(!_2fD._){var _2fE=E(_2eP)-E(_2fD.a)|0;if(_2fE>E(_2f8)){return _2fC;}else{var _2fF=new T(function(){return _PB(function(_2fG){var _2fH=E(_2fG);return ((_2fE+_2fH|0)<E(_2fx))?_2fH:_2fH+1|0;},_2fD.b);});return new T1(6,new T2(0,_2fw,_2fF));}}else{return _2fC;}}else{return _2fC;}});return new T2(1,_2fB,new T(function(){return _2fy(_2fA.b);}));}};return _2fy(_2eW.b);});return new T2(0,_2fv,_2fb);}}}else{return new T2(0,_2eS,_2eL);}}else{return new T2(0,_2eS,_2eL);}}}else{return new T2(0,_2eS,_2eL);}}}else{return new T2(0,_2eS,_2eL);}}};return B(_5m(_1Ae,_1A2,_2eQ));});return B(A1(_2eE,_2eN));});return C > 19 ? new F(function(){return A3(_2X,_29s,_2eM,_2eF);}) : (++C,A3(_2X,_29s,_2eM,_2eF));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_WY));}),_2eK));}),_2fI=new T(function(){var _2fJ=new T(function(){return _1RP(_29o);}),_2fK=function(_2fL){var _2fM=function(_2fN){return new T3(0,0,new T(function(){var _2fO=E(E(_2fN).b);return new T4(0,_2fO.a,_2fL,_2fO.c,_2fO.d);}),_2L);};return C > 19 ? new F(function(){return A2(_1QP,_29o,_2fM);}) : (++C,A2(_1QP,_29o,_2fM));},_2fP=function(_2fQ){var _2fR=new T(function(){var _2fS=new T(function(){var _2fT=new T(function(){return _1RD(_2fQ);}),_2fU=new T(function(){return _29g(_1zQ,_2fQ);}),_2fV=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_2fQ)),0));}),_2fW=function(_2fX){var _2fY=E(_2fX);if(!_2fY._){return E(new T2(0,__Z,_2fQ));}else{var _2fZ=E(_2fY.a);if(_2fZ._==2){var _2g0=E(_2fY.b);if(!_2g0._){return new T2(0,_2fY,_2fQ);}else{var _2g1=E(_2g0.a);if(_2g1._==6){var _2g2=E(_2g1.a);if(!_2g2._){var _2g3=_2g2.a,_2g4=_2g2.b,_2g5=new T(function(){var _2g6=function(_2g7){var _2g8=E(_2g7);if(!_2g8._){return __Z;}else{var _2g9=_2g8.a,_2ga=new T(function(){if(!B(A3(_bX,_2er,new T(function(){return E(E(E(_2g9).b).a);}),_2fZ.a))){return new T1(1,new T(function(){return _IK(_2g9);}));}else{return new T1(0,new T(function(){return _IK(_2g9);}));}});return new T2(1,_2ga,new T(function(){return _2g6(_2g8.b);}));}};return _2g6(_2fU);}),_2gb=E(B(A1(_1zY,_2g5)).a);if(!_2gb._){return new T2(0,_2fY,_2fQ);}else{var _2gc=E(_2gb.a).a,_2gd=new T(function(){return (E(_2gc)+E(_2g3)|0)-E(_2fV)|0;});if(!_1dI(true,_Rs(_Xv,_Rs(function(_2ge){return _C3(_2ge,_2gd);},B(_S2(_2g4)))))){return new T2(0,_2fY,_2fQ);}else{var _2gf=new T(function(){var _2gg=function(_2gh){var _2gi=E(_2gh);if(!_2gi._){return __Z;}else{var _2gj=_2gi.a,_2gk=new T(function(){return E(E(_2gj).a);}),_2gl=function(_2gm,_2gn,_2go){var _2gp=E(_2gn),_2gq=E(_2gc);if(_2gp>=_2gq){if(_2gp!=_2gq){var _2gr=new T(function(){return B(A2(_2gm,_2gp+1|0,new T(function(){return _25H(_2go);})));});return new T2(1,_2gj,_2gr);}else{return C > 19 ? new F(function(){return A2(_2gm,_2gp+1|0,new T(function(){return _25H(_2go);}));}) : (++C,A2(_2gm,_2gp+1|0,new T(function(){return _25H(_2go);})));}}else{var _2gs=new T(function(){return B(A2(_2gm,_2gp+1|0,new T(function(){return _25H(_2go);})));});return new T2(1,new T2(0,_2gk,new T(function(){return B(A(_UK,[_29m,_1zI,_2g4,_2gq-_2gp|0,E(_2gj).b,_2go]));})),_2gs);}};return new T2(1,_2gl,new T(function(){return _2gg(_2gi.b);}));}};return B(A(_2B,[_6h,_2gg(_2fQ),_1Ao,0,_2fT]));}),_2gt=new T(function(){var _2gu=new T(function(){return E(_2g3)-1|0;}),_2gv=function(_2gw){var _2gx=E(_2gw);if(!_2gx._){return __Z;}else{var _2gy=new T(function(){var _2gz=E(_2gx.a);if(_2gz._==6){var _2gA=E(_2gz.a);if(!_2gA._){var _2gB=E(_2gc),_2gC=E(_2fV)-E(_2gA.a)|0;if(_2gC>_2gB){return _2gz;}else{var _2gD=new T(function(){return B(A(_UK,[_29m,_1zI,_2g4,_2gB-_2gC|0,_2gA.b,new T(function(){return _1RA(_oy(_2gC,_2fQ).b);})]));});return new T1(6,new T2(0,_2gu,_2gD));}}else{return _2gz;}}else{return _2gz;}});return new T2(1,_2gy,new T(function(){return _2gv(_2gx.b);}));}};return _2gv(_2g0.b);});return new T2(0,_2gt,_2gf);}}}else{return new T2(0,_2fY,_2fQ);}}else{return new T2(0,_2fY,_2fQ);}}}else{return new T2(0,_2fY,_2fQ);}}};return B(_5m(_1Ae,_1A2,_2fW));});return B(A1(_2fJ,_2fS));});return C > 19 ? new F(function(){return A3(_2X,_29s,_2fR,_2fK);}) : (++C,A3(_2X,_29s,_2fR,_2fK));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_WV));}),_2fP));}),_2gE=new T(function(){var _2gF=new T(function(){return _1RP(_29o);}),_2gG=function(_2gH){var _2gI=function(_2gJ){return new T3(0,0,new T(function(){var _2gK=E(E(_2gJ).b);return new T4(0,_2gK.a,_2gH,_2gK.c,_2gK.d);}),_2L);};return C > 19 ? new F(function(){return A2(_1QP,_29o,_2gI);}) : (++C,A2(_1QP,_29o,_2gI));},_2gL=function(_2gM){var _2gN=new T(function(){var _2gO=new T(function(){var _2gP=function(_2gQ){var _2gR=E(_2gQ);if(!_2gR._){return E(new T2(0,__Z,_2gM));}else{var _2gS=E(_2gR.a);if(_2gS._==2){var _2gT=E(_2gR.b);if(!_2gT._){return new T2(0,_2gR,_2gM);}else{var _2gU=E(_2gT.a);if(_2gU._==2){var _2gV=new T(function(){var _2gW=function(_2gX){var _2gY=E(_2gX);if(!_2gY._){return __Z;}else{var _2gZ=new T(function(){var _2h0=E(_2gY.a),_2h1=_2h0.a;return new T2(0,new T(function(){if(!B(A3(_bX,_2er,_2h1,_2gS.a))){return E(_2h1);}else{return E(_2gU.a);}}),_2h0.b);});return new T2(1,_2gZ,new T(function(){return _2gW(_2gY.b);}));}};return _2gW(_2gM);});return new T2(0,_2gT.b,_2gV);}else{return new T2(0,_2gR,_2gM);}}}else{return new T2(0,_2gR,_2gM);}}};return B(_5m(_1Ae,_1A2,_2gP));});return B(A1(_2gF,_2gO));});return C > 19 ? new F(function(){return A3(_2X,_29s,_2gN,_2gG);}) : (++C,A3(_2X,_29s,_2gN,_2gG));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_WS));}),_2gL));}),_2h2=new T(function(){var _2h3=new T(function(){return _1RP(_29o);}),_2h4=function(_2h5){var _2h6=new T(function(){return _1Rg(_10M(_2er,_2aw,_29r,_2h5));}),_2h7=function(_2h8){return new T3(0,0,new T2(1,new T1(3,_2h6),new T(function(){return E(E(_2h8).b);})),_2L);};return C > 19 ? new F(function(){return A1(_2h3,_2h7);}) : (++C,A1(_2h3,_2h7));};return B(A3(_2X,_29s,new T(function(){return B(A2(_1QP,_29o,_WP));}),_2h4));}),_2h9=new T(function(){var _2ha=new T(function(){var _2hb=new T(function(){var _2hc=function(_2hd,_2he){var _2hf=E(_2he);if(_2hf._==2){var _2hg=new T(function(){var _2hh=new T(function(){return _29g(_2hd,_1zQ);}),_2hi=function(_2hj){var _2hk=E(_2hj);if(!_2hk._){return __Z;}else{var _2hl=_2hk.a,_2hm=new T(function(){var _2hn=new T(function(){var _2ho=function(_2hp){var _2hq=E(_2hp);if(!_2hq._){return __Z;}else{var _2hr=_2hq.a,_2hs=new T(function(){if(!B(A3(_bX,_2er,new T(function(){return E(E(_2hr).a);}),_2hl))){return new T1(1,new T(function(){return _IK(_2hr);}));}else{return new T1(0,new T(function(){return _IK(_2hr);}));}});return new T2(1,_2hs,new T(function(){return _2ho(_2hq.b);}));}};return _2ho(_2hh);}),_2ht=E(B(A1(_1A0,_2hn)).a);if(!_2ht._){return new T1(0,_2hl);}else{return new T1(1,E(_2ht.a).b);}});return new T2(1,_2hm,new T(function(){return _2hi(_2hk.b);}));}};return _2hi(_Iz(_2aw,_289(B(A2(_1nG,_29m,_2hf.a)))));});return new T2(0,_2hd,_2hg);}else{return E(_1Am);}},_2hu=function(_2hv){var _2hw=E(_2hv),_2hx=_2hc(_2hw.a,_2hw.b);return new T2(0,_2hx.a,_2hx.b);},_2hy=function(_2hz){var _2hA=E(_2hz);if(!_2hA._){return E(new T2(0,__Z,_WK));}else{var _2hB=E(_2hA.a);if(_2hB._==6){var _2hC=E(_2hB.a);if(_2hC._==2){var _2hD=new T(function(){var _2hE=E(_2hC.a),_2hF=_Jw(_2hu,_2hE.a,_2hE.b,_2hE.c);return new T3(0,_2hF.a,_2hF.b,_2hF.c);}),_2hG=function(_2hH){return new T3(0,0,new T(function(){var _2hI=E(E(_2hH).b);return new T4(0,_2hI.a,_2hI.b,_2hD,_2hI.d);}),_2L);};return new T2(0,_2hA.b,_2hG);}else{return new T2(0,_2hA,_WK);}}else{return new T2(0,_2hA,_WK);}}};return B(_5m(_1Ae,_1A2,_2hy));});return B(A2(_1RP,_29o,_2hb));});return B(A3(_2X,_29s,_2ha,function(_2hJ){return C > 19 ? new F(function(){return A2(_1QP,_29o,_2hJ);}) : (++C,A2(_1QP,_29o,_2hJ));}));}),_2hK=function(_2hL){var _2hM=E(_2hL);switch(_2hM._){case 0:return E(_29T);case 1:return E(_2ab);case 2:return E(_2ax);case 3:return E(_2bc);case 4:return E(_29y);case 5:return E(_29K);case 6:return E(_2br);case 7:return E(_2bA);case 8:return E(_29G);case 9:return E(_2es);case 10:return E(_2bS);case 11:var _2hN=_2hM.a,_2hO=function(_2hP){var _2hQ=new T(function(){return B(A3(_2B,_6g,_CV(_CS(_2hP)),0));}),_2hR=function(_2hS){var _2hT=E(_2hS);switch(_2hT._){case 3:return new T1(3,new T(function(){return _2hU(_2hT.a);}));case 4:return new T1(4,new T(function(){return _JK(_2hR,_2hT.a);}));case 6:var _2hV=E(_2hT.a);if(!_2hV._){var _2hW=E(_2hQ),_2hX=E(_2hV.a),_2hY=function(_2hZ){var _2i0=E(_oy(_2hW-_2hX|0,_2hP).b);if(!_2i0._){return _2hT;}else{var _2i1=E(_2i0.a);return new T1(6,new T2(0,_2hX-1|0,new T4(0,_2hM.b,_2i1.a,_2i1.b,_2hV.b)));}};if(_2hW!=_2hX){if(!E(_2hN)){return _2hY(_);}else{return _2hT;}}else{return _2hY(_);}}else{return _2hT;}break;default:return _2hT;}},_2hU=function(_2i2){var _2i3=E(_2i2);return (_2i3._==0)?__Z:new T2(1,new T(function(){return _2hR(_2i3.a);}),new T(function(){return _2hU(_2i3.b);}));},_2i4=new T(function(){var _2i5=new T(function(){var _2i6=function(_2i7){return new T3(0,0,new T(function(){return _JK(_2hR,E(_2i7).b);}),_2L);};return B(A1(_29J,_2i6));});return B(A3(_2R,_29u,_s3,_2i5));}),_2i8=function(_2i9){var _2ia=new T(function(){var _2ib=function(_2ic){return new T3(0,0,new T(function(){var _2id=E(E(_2ic).b);return new T4(0,_2id.a,_2i9,_2id.c,_2id.d);}),_2L);};return B(A2(_1QP,_29o,_2ib));});return C > 19 ? new F(function(){return A3(_s6,_29u,_2i4,_2ia);}) : (++C,A3(_s6,_29u,_2i4,_2ia));},_2ie=new T(function(){var _2if=new T(function(){var _2ig=new T(function(){if(!E(_2hN)){return E(_2hP);}else{if(!B(A3(_2B,_6h,_1Rl(_2hP),true))){var _2ih=E(_2hP);if(!_2ih._){return E(_1RR);}else{return E(_2ih.b);}}else{return E(_2hP);}}}),_2ii=function(_2ij){var _2ik=E(_2ij);if(!_2ik._){return __Z;}else{var _2il=_2ik.b;return new T2(1,new T(function(){return _2hR(_2ik.a);}),new T(function(){if(!E(_2hN)){return E(_2il);}else{return _2ii(_2il);}}));}},_2im=function(_2in){return new T2(0,new T(function(){return _2ii(_2in);}),_2ig);};return B(_5m(_1Ae,_1A2,_2im));});return B(A1(_29I,_2if));});return C > 19 ? new F(function(){return A3(_2X,_29s,_2ie,_2i8);}) : (++C,A3(_2X,_29s,_2ie,_2i8));};return C > 19 ? new F(function(){return A3(_2X,_29s,_29H,_2hO);}) : (++C,A3(_2X,_29s,_29H,_2hO));break;case 12:return E(_2cg);case 13:return E(_2cD);case 14:return E(_2eD);case 15:return E(_2fI);case 16:return E(_2gE);case 17:return E(_2h2);case 18:return E(_2cT);case 19:return E(_2h9);case 20:return E(_2do);default:return E(_2dF);}};return _2hK;},_2io=new T(function(){return _29l(new T6(0,_6A,new T3(0,function(_2ip,_1Sk,_1Sl){return _AH(_1Sk,_1Sl);},_AF,function(_2iq,_2ir){return _1R(_AH,_2iq,_2ir);}),_zx,new T2(0,_zx,function(_2is,_2it){var _2iu=_oy(_2is,_2it);return new T2(0,_2iu.a,_2iu.b);}),function(_2iv){return E(_2iv);},_n),new T2(0,_AV,_B2),new T6(0,_mM,_AV,_zq,function(_2iw){return C > 19 ? new F(function(){return _B6(_2F,_2iw);}) : (++C,_B6(_2F,_2iw));},function(_2ix){return C > 19 ? new F(function(){return _4u(_2F,_2ix);}) : (++C,_4u(_2F,_2ix));},function(_2iy){return C > 19 ? new F(function(){return _Bi(_2F,_2iy);}) : (++C,_Bi(_2F,_2iy));}));}),_2iz=function(_2iA,_){return new T3(0,0,new T(function(){return E(E(_2iA).b);}),_2L);},_2iB=function(_2iC){var _2iD=E(_2iC);if(!_2iD._){return __Z;}else{var _2iE=new T(function(){return B(A3(_zq,_2io,_6i,_2iD.a));}),_2iF=function(_2iG,_){var _2iH=B(A2(_2iE,_2iG,_));return new T3(0,_zr,new T(function(){return E(E(_2iH).b);}),new T(function(){return E(E(_2iH).c);}));},_2iI=function(_2iJ){var _2iK=new T(function(){return _3f(_2F,_2iF,_2iJ);}),_2iL=function(_2iM,_){var _2iN=B(A2(_zw,_2iM,_));return new T3(0,new T(function(){if(!E(E(_2iN).a)){return E(_2iK);}else{return _2iz;}}),new T(function(){return E(E(_2iN).b);}),new T(function(){return E(E(_2iN).c);}));};return function(_3v){return C > 19 ? new F(function(){return _2Z(_2M,_2F,_2iL,_3v);}) : (++C,_2Z(_2M,_2F,_2iL,_3v));};};return new T2(1,_2iI,new T(function(){return _2iB(_2iD.b);}));}},_2iO=function(_2iP){return E(_2iP);},_2iQ=new T(function(){return B(A1(_48(_x,_x,_4P,_k2),new T2(0,function(_2iR){return E(_2iR);},function(_2iS){return E(_2iS);})));}),_2iT=function(_2iU,_2iV,_){var _2iW=new T(function(){var _2iX=new T(function(){return B(A3(_2B,_6h,_2iB(_2iU),_2iz));}),_2iY=function(_2iZ,_){var _2j0=B(A2(_2iX,_2iZ,_));return new T3(0,_2iO,new T(function(){return E(E(_2j0).b);}),new T(function(){return E(E(_2j0).c);}));};return _3f(_2F,_2iY,_5X);});return C > 19 ? new F(function(){return A3(E(_2iQ).b,_2iW,_2iV,_);}) : (++C,A3(E(_2iQ).b,_2iW,_2iV,_));},_2j1=(function(id){return document.getElementById(id);}),_2j2=(function(c){return document.getElementsByClassName(c);}),_2j3=new T(function(){return unAppCStr(") is outside of enumeration\'s range (0,",new T(function(){return _ck(0,2,new T(function(){return unCStr(")");}));}));}),_2j4=function(_2j5){return err(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return _ck(0,_2j5,_2j3);})));},_2j6=function(_2j7,_){return new T(function(){var _2j8=Number(E(_2j7)),_2j9=jsTrunc(_2j8);if(_2j9<0){return _2j4(_2j9);}else{if(_2j9>2){return _2j4(_2j9);}else{return _2j9;}}});},_2ja=new T3(0,0,0,0),_2jb=new T(function(){return jsGetMouseCoords;}),_2jc=function(_2jd,_){var _2je=E(_2jd);if(!_2je._){return __Z;}else{var _2jf=_2jc(_2je.b,_);return new T2(1,new T(function(){var _2jg=Number(E(_2je.a));return jsTrunc(_2jg);}),_2jf);}},_2jh=function(_2ji,_){var _2jj=__arr2lst(0,_2ji);return _2jc(_2jj,_);},_2jk=function(_2jl,_){return new T(function(){var _2jm=Number(E(_2jl));return jsTrunc(_2jm);});},_2jn=new T2(0,_2jk,function(_2jo,_){return _2jh(E(_2jo),_);}),_2jp=function(_2jq,_){var _2jr=E(_2jq);if(!_2jr._){return __Z;}else{var _2js=_2jp(_2jr.b,_);return new T2(1,_2jr.a,_2js);}},_2jt=new T(function(){return _1K(new T6(0,__Z,7,__Z,new T(function(){return unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:268:5-9");}),__Z,__Z));}),_2ju=function(_){return die(_2jt);},_2jv=function(_2jw){return E(E(_2jw).a);},_2jx=function(_2jy,_2jz,_2jA,_){var _2jB=__arr2lst(0,_2jA),_2jC=_2jp(_2jB,_),_2jD=E(_2jC);if(!_2jD._){return _2ju(_);}else{var _2jE=E(_2jD.b);if(!_2jE._){return _2ju(_);}else{if(!E(_2jE.b)._){var _2jF=B(A3(_2jv,_2jy,_2jD.a,_)),_2jG=B(A3(_2jv,_2jz,_2jE.a,_));return new T2(0,_2jF,_2jG);}else{return _2ju(_);}}}},_2jH=new T(function(){return _12n(function(_){return __jsNull();});}),_2jI=function(_2jJ,_2jK,_){if(E(_2jJ)==7){var _2jL=E(_2jb)(_2jK),_2jM=_2jx(_2jn,_2jn,_2jL,_),_2jN=_2jK["deltaX"],_2jO=_2jK["deltaY"],_2jP=_2jK["deltaZ"];return new T(function(){return new T3(0,E(_2jM),E(__Z),E(new T3(0,_2jN,_2jO,_2jP)));});}else{var _2jQ=E(_2jb)(_2jK),_2jR=_2jx(_2jn,_2jn,_2jQ,_),_2jS=_2jK["button"],_2jT=__eq(_2jS,E(_2jH));if(!E(_2jT)){var _2jU=__isUndef(_2jS);if(!E(_2jU)){var _2jV=_2j6(_2jS,_);return new T(function(){return new T3(0,E(_2jR),E(new T1(1,_2jV)),E(_2ja));});}else{return new T(function(){return new T3(0,E(_2jR),E(__Z),E(_2ja));});}}else{return new T(function(){return new T3(0,E(_2jR),E(__Z),E(_2ja));});}}},_2jW=function(_2jX,_2jY,_){return _2jI(_2jX,E(_2jY),_);},_2jZ=function(_2k0){switch(E(_2k0)){case 0:return "click";case 1:return "dblclick";case 2:return "mousedown";case 3:return "mouseup";case 4:return "mousemove";case 5:return "mouseover";case 6:return "mouseout";default:return "wheel";}},_2k1=function(_2k2){return E(_2k2);},_2k3=function(_){return 0;},_2k4=function(_){return 0;},_2k5=(function(e,q){if(!e || typeof e.querySelectorAll !== 'function') {throw 'querySelectorAll not supported by this element';} else {return e.querySelectorAll(q);}}),_2k6=function(_2k7){var _2k8=E(_2k7);return (_2k8._==0)?__Z:new T2(1,function(_2k9,_){var _2ka=B(A1(_2k8.a,_));return C > 19 ? new F(function(){return A1(_2k9,_);}) : (++C,A1(_2k9,_));},new T(function(){return _2k6(_2k8.b);}));},_2kb=function(_2kc,_2kd,_2ke,_){var _2kf=E(_2kd);if(!_2kf._){return C > 19 ? new F(function(){return A2(_2ke,__Z,_);}) : (++C,A2(_2ke,__Z,_));}else{var _2kg=E(_2kc),_2kh=_2k5(_2kg,toJSStr(new T2(1,46,_2kf.a))),_2ki=__arr2lst(0,_2kh),_2kj=_f(_2ki,_),_2kk=function(_2kl){var _2km=E(_2kl);if(!_2km._){return __Z;}else{var _2kn=function(_){return C > 19 ? new F(function(){return _2kb(_2kg,_2kf.b,function(_2ko){return C > 19 ? new F(function(){return A1(_2ke,new T2(1,_2km.a,_2ko));}) : (++C,A1(_2ke,new T2(1,_2km.a,_2ko)));},_);}) : (++C,_2kb(_2kg,_2kf.b,function(_2ko){return C > 19 ? new F(function(){return A1(_2ke,new T2(1,_2km.a,_2ko));}) : (++C,A1(_2ke,new T2(1,_2km.a,_2ko)));},_));};return new T2(1,_2kn,new T(function(){return _2kk(_2km.b);}));}};return C > 19 ? new F(function(){return A(_2B,[_6h,_2k6(_2kk(_2kj)),_2k4,_]);}) : (++C,A(_2B,[_6h,_2k6(_2kk(_2kj)),_2k4,_]));}},_2kp=function(_2kq){var _2kr=E(_2kq);return (_2kr._==0)?__Z:new T2(1,_2kr.a,new T(function(){return _2kp(_2kr.b);}));},_2ks=function(_2kt){var _2ku=E(_2kt);return (_2ku._==0)?__Z:new T2(1,_2ku.a,new T(function(){return _2ks(_2ku.b);}));},_2kv=(function(e,p){var x = e[p];return typeof x === 'undefined' ? '' : x.toString();}),_2kw=function(_2kx){return E(E(_2kx).b);},_2ky=function(_2kz){return fromJSStr(E(_2kz));},_2kA=function(_2kB){return E(E(_2kB).a);},_2kC=function(_2kD){return E(E(_2kD).b);},_2kE=function(_2kF,_2kG,_2kH,_2kI){var _2kJ=new T(function(){var _2kK=function(_){var _2kL=_2kv(B(A2(_2kA,_2kF,_2kH)),E(_2kI));return new T(function(){return String(_2kL);});};return _2kK;});return C > 19 ? new F(function(){return A2(_2kC,_2kG,_2kJ);}) : (++C,A2(_2kC,_2kG,_2kJ));},_2kM=function(_2kN,_2kO,_2kP,_2kQ){var _2kR=_j(_2kO),_2kS=new T(function(){return _l(_2kR);}),_2kT=function(_2kU){return C > 19 ? new F(function(){return A1(_2kS,new T(function(){return _2ky(_2kU);}));}) : (++C,A1(_2kS,new T(function(){return _2ky(_2kU);})));},_2kV=new T(function(){return B(_2kE(_2kN,_2kO,_2kP,new T(function(){return toJSStr(E(_2kQ));},1)));});return C > 19 ? new F(function(){return A3(_2kw,_2kR,_2kV,_2kT);}) : (++C,A3(_2kw,_2kR,_2kV,_2kT));},_2kW=(function(e,p,v){e[p] = v;}),_2kX=new T(function(){return unCStr("capricon-input");}),_2kY=new T(function(){return unCStr("capricon-submit");}),_2kZ=new T(function(){return unCStr("capricon-output");}),_2l0=new T(function(){return B((function(_2l1){return C > 19 ? new F(function(){return _7y("exe/CaPriCon_haste.hs:(44,80)-(54,21)|lambda");}) : (++C,_7y("exe/CaPriCon_haste.hs:(44,80)-(54,21)|lambda"));})(_));}),_2l2=new T(function(){return unCStr(".capricon-context");}),_2l3=new T(function(){return B((function(_2l4){return C > 19 ? new F(function(){return _7y("exe/CaPriCon_haste.hs:(45,49)-(54,21)|case");}) : (++C,_7y("exe/CaPriCon_haste.hs:(45,49)-(54,21)|case"));})(_));}),_2l5=new T(function(){return unCStr("textContent");}),_2l6=function(_2l7){return E(E(_2l7).a);},_2l8=function(_2l9){return E(E(_2l9).b);},_2la=function(_2lb){return E(E(_2lb).a);},_2lc=new T(function(){return _12n(function(_){return nMV(__Z);});}),_2ld=function(_2le){return E(E(_2le).b);},_2lf=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_2lg=function(_2lh,_2li,_2lj,_2lk,_2ll,_2lm){var _2ln=_2l6(_2lh),_2lo=_j(_2ln),_2lp=new T(function(){return _2kC(_2ln);}),_2lq=new T(function(){return _l(_2lo);}),_2lr=new T(function(){return B(A1(_2li,_2lk));}),_2ls=new T(function(){return B(A2(_2la,_2lj,_2ll));}),_2lt=function(_2lu){return C > 19 ? new F(function(){return A1(_2lq,new T3(0,_2ls,_2lr,_2lu));}) : (++C,A1(_2lq,new T3(0,_2ls,_2lr,_2lu)));},_2lv=function(_2lw){var _2lx=new T(function(){var _2ly=new T(function(){var _2lz=__createJSFunc(2,function(_2lA,_){var _2lB=B(A2(E(_2lw),_2lA,_));return _2jH;}),_2lC=_2lz;return function(_){return _2lf(E(_2lr),E(_2ls),_2lC);};});return B(A1(_2lp,_2ly));});return C > 19 ? new F(function(){return A3(_2kw,_2lo,_2lx,_2lt);}) : (++C,A3(_2kw,_2lo,_2lx,_2lt));},_2lD=new T(function(){var _2lE=new T(function(){return _2kC(_2ln);}),_2lF=function(_2lG){var _2lH=new T(function(){return B(A1(_2lE,function(_){var _=wMV(E(_2lc),new T1(1,_2lG));return C > 19 ? new F(function(){return A(_2l8,[_2lj,_2ll,_2lG,_]);}) : (++C,A(_2l8,[_2lj,_2ll,_2lG,_]));}));});return C > 19 ? new F(function(){return A3(_2kw,_2lo,_2lH,_2lm);}) : (++C,A3(_2kw,_2lo,_2lH,_2lm));};return B(A2(_2ld,_2lh,_2lF));});return C > 19 ? new F(function(){return A3(_2kw,_2lo,_2lD,_2lv);}) : (++C,A3(_2kw,_2lo,_2lD,_2lv));},_2lI=function(_2lJ){var _2lK=E(_2lJ);if(!_2lK._){return __Z;}else{var _2lL=_2lK.a,_2lM=function(_2lN,_2lO,_){var _2lP=function(_2lQ,_){var _2lR=E(_2lQ);if(!_2lR._){return E(_2l0);}else{var _2lS=E(_2lR.b);if(!_2lS._){return E(_2l0);}else{var _2lT=E(_2lS.b);if(!_2lT._){return E(_2l0);}else{if(!E(_2lT.b)._){var _2lU=_2k5(E(_2lL),toJSStr(E(_2l2))),_2lV=__arr2lst(0,_2lU),_2lW=_f(_2lV,_),_2lX=E(_2lW);if(!_2lX._){return E(_2l3);}else{if(!E(_2lX.b)._){var _2lY=B(A(_2kM,[_p,_2o,_2lX.a,_2l5,_])),_2lZ=B(_2iT(new T(function(){return _2ks(_1rN(_2lY));},1),_2lO,_)),_2m0=E(_2lZ).a,_2m1=function(_2m2,_){var _2m3=_2kv(E(_2lR.a),"value"),_2m4=B(_2iT(new T(function(){var _2m5=String(_2m3);return _2kp(_1rN(fromJSStr(_2m5)));},1),_2m0,_)),_2m6=_2kW(E(_2lT.a),toJSStr(E(_2l5)),toJSStr(E(E(_2m4).b)));return _2k3(_);},_2m7=B(A(_2lg,[new T2(0,_2o,_B),_2k1,new T2(0,_2jZ,_2jW),_2lS.a,0,_2m1,_]));return C > 19 ? new F(function(){return A2(_2lN,_2m0,_);}) : (++C,A2(_2lN,_2m0,_));}else{return E(_2l3);}}}else{return E(_2l0);}}}}};return C > 19 ? new F(function(){return _2kb(_2lL,new T2(1,_2kX,new T2(1,_2kY,new T2(1,_2kZ,__Z))),_2lP,_);}) : (++C,_2kb(_2lL,new T2(1,_2kX,new T2(1,_2kY,new T2(1,_2kZ,__Z))),_2lP,_));};return new T2(1,_2lM,new T(function(){return _2lI(_2lK.b);}));}},_2m8=function(_2m9){var _2ma=E(_2m9);return (_2ma._==0)?__Z:new T2(1,_2ma.a,new T(function(){return _2m8(_2ma.b);}));},_2mb=function(_2mc,_){return 0;},_2md=function(_2me){var _2mf=E(_2me);if(!_2mf._){return new T2(0,__Z,__Z);}else{var _2mg=_2mf.b,_2mh=E(_2mf.a);if(_2mh==47){return new T2(0,__Z,new T(function(){var _2mi=_2md(_2mg);return new T2(1,_2mi.a,_2mi.b);}));}else{var _2mj=new T(function(){var _2mk=_2md(_2mg);return new T2(0,_2mk.a,_2mk.b);});return new T2(0,new T2(1,_2mh,new T(function(){return E(E(_2mj).a);})),new T(function(){return E(E(_2mj).b);}));}}},_2ml=function(_2mm,_2mn,_2mo,_2mp){var _2mq=E(_2mn);if(!_2mq._){return C > 19 ? new F(function(){return _233(_6A,_2mm,_4P,_2mo,_2mp);}) : (++C,_233(_6A,_2mm,_4P,_2mo,_2mp));}else{var _2mr=_2mq.a,_2ms=_2mq.b,_2mt=function(_2mu){var _2mv=_sa(_6A,_2mm,_2mp);if(!_2mv._){return new T1(1,new T1(4,new T(function(){return B(_2ml(_2mr,_2ms,_2mo,_oG));})));}else{var _2mw=new T(function(){var _2mx=E(_2mv.a);if(_2mx._==4){return new T1(4,new T(function(){return B(_2ml(_2mr,_2ms,_2mo,_2mx.a));}));}else{return _2mx;}});return new T1(1,_2mw);}};return C > 19 ? new F(function(){return _rY(_6A,_2mt,_2mm,_2mp);}) : (++C,_rY(_6A,_2mt,_2mm,_2mp));}},_2my=function(_2mz){var _2mA=E(_2mz);if(!_2mA._){return __Z;}else{var _2mB=new T(function(){var _2mC=E(_2mA.a),_2mD=new T(function(){var _2mE=_2md(_2mC.a);return new T2(0,_2mE.a,_2mE.b);}),_2mF=function(_2mG){return E(new T1(1,_2mC.b));};return function(_2mH){var _2mI=E(_2mD);return C > 19 ? new F(function(){return _2ml(_2mI.a,_2mI.b,_2mF,_2mH);}) : (++C,_2ml(_2mI.a,_2mI.b,_2mF,_2mH));};});return new T2(1,_2mB,new T(function(){return _2my(_2mA.b);}));}},_2mJ=function(_2mK){var _2mL=E(_2mK);if(!_2mL._){return __Z;}else{var _2mM=E(_2mL.a);return new T2(1,new T2(0,_2mM.a,new T1(0,_2mM.b)),new T(function(){return _2mJ(_2mL.b);}));}},_2mN=new T(function(){return B(A3(_2B,_6h,new T(function(){return _2my(new T2(1,new T2(0,new T(function(){return unCStr(".");}),new T1(5,__Z)),new T2(1,new T2(0,new T(function(){return unCStr("version");}),new T1(2,new T(function(){return unCStr("0.7.1");}))),new T(function(){return _2mJ(new T2(1,new T2(0,new T(function(){return unCStr("def");}),new T0(20)),new T2(1,new T2(0,new T(function(){return unCStr("$");}),new T0(19)),new T2(1,new T2(0,new T(function(){return unCStr("lookup");}),new T0(25)),new T2(1,new T2(0,new T(function(){return unCStr("exec");}),new T0(21)),new T2(1,new T2(0,new T(function(){return unCStr("quote");}),new T0(28)),new T2(1,new T2(0,new T(function(){return unCStr("stack");}),new T0(3)),new T2(1,new T2(0,new T(function(){return unCStr("clear");}),new T0(2)),new T2(1,new T2(0,new T(function(){return unCStr("pop");}),new T0(5)),new T2(1,new T2(0,new T(function(){return unCStr("popn");}),new T0(6)),new T2(1,new T2(0,new T(function(){return unCStr("dup");}),new T0(7)),new T2(1,new T2(0,new T(function(){return unCStr("dupn");}),new T0(8)),new T2(1,new T2(0,new T(function(){return unCStr("swap");}),new T0(9)),new T2(1,new T2(0,new T(function(){return unCStr("swapn");}),new T0(10)),new T2(1,new T2(0,new T(function(){return unCStr("pick");}),new T0(4)),new T2(1,new T2(0,new T(function(){return unCStr("[");}),__Z),new T2(1,new T2(0,new T(function(){return unCStr("]");}),new T0(1)),new T2(1,new T2(0,new T(function(){return unCStr("io/exit");}),new T1(29,new T0(8))),new T2(1,new T2(0,new T(function(){return unCStr("io/print");}),new T1(29,__Z)),new T2(1,new T2(0,new T(function(){return unCStr("io/open");}),new T1(29,new T0(1))),new T2(1,new T2(0,new T(function(){return unCStr("io/get-env");}),new T1(29,new T0(3))),new T2(1,new T2(0,new T(function(){return unCStr("string/format");}),new T1(29,new T0(21))),new T2(1,new T2(0,new T(function(){return unCStr("string/to-int");}),new T1(29,new T0(4))),new T2(1,new T2(0,new T(function(){return unCStr("arith/+");}),new T0(13)),new T2(1,new T2(0,new T(function(){return unCStr("arith/-");}),new T0(14)),new T2(1,new T2(0,new T(function(){return unCStr("arith/*");}),new T0(15)),new T2(1,new T2(0,new T(function(){return unCStr("arith/div");}),new T0(16)),new T2(1,new T2(0,new T(function(){return unCStr("arith/mod");}),new T0(17)),new T2(1,new T2(0,new T(function(){return unCStr("arith/sign");}),new T0(18)),new T2(1,new T2(0,new T(function(){return unCStr("list/each");}),new T0(12)),new T2(1,new T2(0,new T(function(){return unCStr("list/range");}),new T0(11)),new T2(1,new T2(0,new T(function(){return unCStr("dict/vocabulary");}),new T0(22)),new T2(1,new T2(0,new T(function(){return unCStr("dict/empty");}),new T0(23)),new T2(1,new T2(0,new T(function(){return unCStr("dict/insert");}),new T0(24)),new T2(1,new T2(0,new T(function(){return unCStr("dict/delete");}),new T0(26)),new T2(1,new T2(0,new T(function(){return unCStr("dict/keys");}),new T0(27)),new T2(1,new T2(0,new T(function(){return unCStr("dict/module");}),new T1(29,new T0(2))),new T2(1,new T2(0,new T(function(){return unCStr("term-index/pattern-index");}),new T1(29,new T0(18))),new T2(1,new T2(0,new T(function(){return unCStr("term-index/set-pattern-index");}),new T1(29,new T0(19))),new T2(1,new T2(0,new T(function(){return unCStr("term-index/index-insert");}),new T1(29,new T0(20))),new T2(1,new T2(0,new T(function(){return unCStr("term/universe");}),new T1(29,new T0(6))),new T2(1,new T2(0,new T(function(){return unCStr("term/variable");}),new T1(29,new T0(9))),new T2(1,new T2(0,new T(function(){return unCStr("term/apply");}),new T1(29,new T0(10))),new T2(1,new T2(0,new T(function(){return unCStr("term/lambda");}),new T1(29,new T2(11,false,0))),new T2(1,new T2(0,new T(function(){return unCStr("term/forall");}),new T1(29,new T2(11,false,1))),new T2(1,new T2(0,new T(function(){return unCStr("term/mu");}),new T1(29,new T0(13))),new T2(1,new T2(0,new T(function(){return unCStr("context/intro");}),new T1(29,new T0(7))),new T2(1,new T2(0,new T(function(){return unCStr("context/intro-before");}),new T1(29,new T0(14))),new T2(1,new T2(0,new T(function(){return unCStr("context/extro-lambda");}),new T1(29,new T2(11,true,0))),new T2(1,new T2(0,new T(function(){return unCStr("context/extro-forall");}),new T1(29,new T2(11,true,1))),new T2(1,new T2(0,new T(function(){return unCStr("context/rename");}),new T1(29,new T0(16))),new T2(1,new T2(0,new T(function(){return unCStr("context/substitute");}),new T1(29,new T0(15))),new T2(1,new T2(0,new T(function(){return unCStr("context/type");}),new T1(29,new T0(12))),new T2(1,new T2(0,new T(function(){return unCStr("context/hypotheses");}),new T1(29,new T0(17))),__Z))))))))))))))))))))))))))))))))))))))))))))))))))))));}))));}),_oG));}),_2mO=new T(function(){return unCStr(" found!");}),_2mP=function(_2mQ){return err(unAppCStr("No element with ID ",new T(function(){return _0(fromJSStr(E(_2mQ)),_2mO);})));},_2mR=function(_){var _2mS=_2j1("capricon-prelude"),_2mT=__eq(_2mS,E(_2jH)),_2mU=function(_,_2mV){var _2mW=E(_2mV);if(!_2mW._){return _2mP("capricon-prelude");}else{var _2mX=B(A(_2kM,[_p,_2o,_2mW.a,_2l5,_])),_2mY=B(_2iT(new T(function(){return _2m8(_1rN(_2mX));},1),new T5(0,__Z,__Z,0,_2mN,new T4(0,false,__Z,_Bv,_n)),_)),_2mZ=_2j2("capricon-steps"),_2n0=__arr2lst(0,_2mZ),_2n1=_f(_2n0,_),_2n2=B(A(_2B,[_6h,_2lI(_2n1),_2mb,E(_2mY).a,_]));return new T0(2);}};if(!E(_2mT)){var _2n3=__isUndef(_2mS);if(!E(_2n3)){return _2mU(_,new T1(1,_2mS));}else{return _2mU(_,__Z);}}else{return _2mU(_,__Z);}},_2n4=function(_){return _a(new T1(0,_2mR),__Z,_);},_2n5=function(_){return _2n4(_);};
var hasteMain = function() {B(A(_2n5, [0]));};window.onload = hasteMain;