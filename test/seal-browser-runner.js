/*
 * seal-browser-runner.js -- headless QUnit driver for the jQuery test suite.
 *
 * The sealed-package build (see .travis.yml) uses this to execute
 * test/index.html in headless Chrome, because "npm test" (the grunt default
 * task) only lints and builds and therefore produces no test-runner output.
 *
 * Usage:
 *     PHP_CLI_SERVER_WORKERS=10 php -S 127.0.0.1:8000 -t . &
 *     NODE_PATH=/tmp/driver/node_modules node test/seal-browser-runner.js
 *
 * PHP is required because the ajax module requests test/data/*.php, and the
 * worker count is load-bearing: a single-process "php -S" serializes requests
 * and starves the fixture iframes.
 *
 * Environment:
 *     SEAL_TEST_URL    page to load. Default
 *                      http://127.0.0.1:8000/test/index.html?dev -- the "?dev"
 *                      parameter is required, since test/jquery.js loads
 *                      dist/jquery.min.js without it.
 *     SEAL_SKIP_TESTS  "|"-separated QUnit test names to de-register before
 *                      they run. Each entry matches either the bare test name
 *                      or "<module>: <name>".
 *     SEAL_TIMEOUT_MS  global watchdog in milliseconds (default 20 minutes).
 *     CHROME_PATH      Chrome/Chromium executable override.
 *
 * Exit status: 0 only when QUnit reported done with zero failed assertions and
 * a non-zero test count; 1 on test failures, 2 on runner errors, 3 on timeout.
 *
 * This file is ES5 only and must lint under test/.jshintrc ("es3": true,
 * "onevar": true), because the grunt default task runs jshint over the test
 * directory. It never ships in the npm tarball -- .npmignore excludes /test.
 */

/*global process: false, Promise: false */

var fs = require( "fs" ),
	puppeteer = require( "puppeteer-core" ),

	// Marker prefix for the in-page -> Node console bridge.
	MARKER = "@@SEAL_QUNIT@@",

	// "url" is deliberately avoided as a name: the QUnit suite exposes a
	// global url() helper and test/.jshintrc declares it.
	pageUrl = process.env.SEAL_TEST_URL ||
		"http://127.0.0.1:8000/test/index.html?dev",

	skipList = parseSkipList( process.env.SEAL_SKIP_TESTS ),

	timeoutMs = Number( process.env.SEAL_TIMEOUT_MS ) || 20 * 60 * 1000,

	// Resolved once the promise created in main() is built.
	pendingResolve = null,

	state = {
		moduleOrder: [],
		modules: {},
		failures: [],
		skipped: [],

		// moduleStarts counts QUnit module transitions, which exceeds the
		// number of distinct modules: test/unit/ready.js declares
		// module( "event" ) and is loaded (via document.write in
		// test/jquery.js) before unit/event.js re-enters the same module.
		moduleStarts: 0,
		started: 0,
		tests: 0,
		assertions: 0,
		summary: null
	};

function parseSkipList( raw ) {
	var parts = String( raw == null ? "" : raw ).split( "|" ),
		out = [],
		i,
		entry;

	for ( i = 0; i < parts.length; i++ ) {
		entry = parts[ i ].replace( /^\s+|\s+$/g, "" );
		if ( entry ) {
			out.push( entry );
		}
	}
	return out;
}

/*
 * Installed with page.evaluateOnNewDocument, so it runs in every frame before
 * any page script. It traps the "window.QUnit = QUnit" assignment made at the
 * bottom of test/libs/qunit/qunit.js and, in the top frame only, registers the
 * real logging callbacks. The suite spawns many QUnit-loading iframes;
 * registering in those produces garbage.
 */
function browserHook( options ) {
	var nativeStringify = window.JSON && window.JSON.stringify,
		nativeConsole = window.console,
		nativeLog = nativeConsole && nativeConsole.log,
		qunitRef,
		installed = false;

	// Snapshot-based serialization. The test
	// "ajax: jQuery.getJSON() - Using Native JSON" replaces window.JSON with a
	// parse-only stub; a reporter that reached for JSON.stringify there would
	// throw, the throw would propagate into jQuery's converter and the whole
	// suite would wedge (QUnit.config.testTimeout does not rescue it).
	function encode( value ) {
		var text;

		try {
			text = nativeStringify( value );
		} catch ( e ) {
			text = null;
		}
		if ( typeof text !== "string" ) {
			try {
				text = String( value );
			} catch ( e2 ) {
				text = "<unserializable>";
			}
		}
		if ( text.length > 400 ) {
			text = text.slice( 0, 400 ) + " ...(truncated)";
		}
		return text;
	}

	// Every emit is wrapped: nothing this reporter does may ever throw into
	// the code under test.
	function emit( kind, payload ) {
		var text;

		try {
			text = nativeStringify( { kind: kind, data: payload } );
			nativeLog.call( nativeConsole, options.marker + text );
		} catch ( e ) {}
	}

	function isTopFrame() {
		var result;

		try {
			result = window === window.top || window.parent === window;
		} catch ( e ) {
			result = false;
		}
		return result;
	}

	function currentModuleName() {
		var name;

		try {
			name = qunitRef && qunitRef.config && qunitRef.config.currentModule;
		} catch ( e ) {
			name = null;
		}
		return typeof name === "string" ? name : "";
	}

	function shouldSkip( moduleName, testName ) {
		var i,
			entry;

		for ( i = 0; i < options.skips.length; i++ ) {
			entry = options.skips[ i ];
			if ( entry === testName ) {
				return true;
			}
			if ( moduleName && entry === moduleName + ": " + testName ) {
				return true;
			}
		}
		return false;
	}

	// SEAL_SKIP_TESTS is implemented at declaration time so an excluded test is
	// never registered and never runs, which keeps the test/unit sources
	// pristine and keeps the exclusions in the build command.
	function wrapDeclarator( globalName ) {
		var original = window[ globalName ];

		if ( typeof original !== "function" ) {
			return;
		}
		window[ globalName ] = function( testName ) {
			var moduleName = currentModuleName();

			if ( typeof testName === "string" && shouldSkip( moduleName, testName ) ) {
				emit( "skip", { module: moduleName, name: testName } );
				return undefined;
			}
			return original.apply( window, arguments );
		};
	}

	function install( qunit ) {
		try {
			qunit.config.reorder = false;
		} catch ( e ) {}

		// window.test / window.asyncTest already exist at this point: qunit.js
		// runs extend( window, QUnit.constructor.prototype ) immediately
		// before assigning window.QUnit. QUnit.asyncTest calls QUnit.test
		// internally rather than the global, so wrapping both globals skips
		// each excluded test exactly once.
		wrapDeclarator( "test" );
		wrapDeclarator( "asyncTest" );

		qunit.moduleStart( function( details ) {
			emit( "moduleStart", { name: details.name || "" } );
		} );

		qunit.testStart( function( details ) {
			emit( "testStart", {
				name: details.name || "",
				module: details.module || ""
			} );
		} );

		qunit.log( function( details ) {
			if ( details.result ) {
				return;
			}
			emit( "fail", {
				module: details.module || "",
				name: details.name || "",
				message: encode( details.message == null ? "" : details.message ),
				expected: encode( details.expected ),
				actual: encode( details.actual ),
				source: details.source ? encode( details.source ) : ""
			} );
		} );

		qunit.testDone( function( details ) {
			emit( "testDone", {
				module: details.module || "",
				name: details.name || "",
				passed: details.passed || 0,
				failed: details.failed || 0,
				total: details.total || 0,
				runtime: details.runtime || 0
			} );
		} );

		qunit.done( function( details ) {
			emit( "done", {
				passed: details.passed || 0,
				failed: details.failed || 0,
				total: details.total || 0,
				runtime: details.runtime || 0
			} );
		} );
	}

	try {
		Object.defineProperty( window, "QUnit", {
			configurable: true,
			enumerable: true,
			get: function() {
				return qunitRef;
			},
			set: function( value ) {
				qunitRef = value;
				if ( !value || installed || !isTopFrame() ) {
					return;
				}
				installed = true;
				try {
					install( value );
				} catch ( inner ) {
					emit( "hookError", { message: encode( inner && inner.message ) } );
				}
			}
		} );
	} catch ( e ) {
		emit( "hookError", { message: "Object.defineProperty( window, 'QUnit' ) failed" } );
	}
}

function findChrome() {
	var candidates = [
			process.env.CHROME_PATH,
			"/usr/bin/google-chrome-stable",
			"/usr/bin/google-chrome",
			"/opt/google/chrome/chrome",
			"/usr/bin/chromium-browser",
			"/usr/bin/chromium"
		],
		i;

	for ( i = 0; i < candidates.length; i++ ) {
		if ( candidates[ i ] ) {
			try {
				if ( fs.existsSync( candidates[ i ] ) ) {
					return candidates[ i ];
				}
			} catch ( e ) {}
		}
	}

	// Last resort: let the OS resolve it through PATH.
	return "google-chrome";
}

function padRight( value, width ) {
	var out = String( value );

	while ( out.length < width ) {
		out += " ";
	}
	return out;
}

function padLeft( value, width ) {
	var out = String( value );

	while ( out.length < width ) {
		out = " " + out;
	}
	return out;
}

// Module names are namespaced so they cannot collide with Object.prototype
// members such as "constructor".
function moduleRecord( name ) {
	var label = name || "(no module)",
		key = "module:" + label;

	if ( !state.modules[ key ] ) {
		state.modules[ key ] = {
			name: label,
			tests: 0,
			assertions: 0,
			failed: 0
		};
		state.moduleOrder.push( key );
	}
	return state.modules[ key ];
}

function reportFailure( data ) {
	console.log( "  FAIL " + ( data.module || "(no module)" ) + ": " + data.name );
	console.log( "       message:  " + data.message );
	console.log( "       expected: " + data.expected );
	console.log( "       actual:   " + data.actual );
	if ( data.source ) {
		console.log( "       source:   " + data.source );
	}
}

function handleEvent( kind, data ) {
	var record;

	if ( kind === "moduleStart" ) {
		moduleRecord( data.name );
		state.moduleStarts++;
		console.log( "" );
		console.log( "== module " + ( data.name || "(no module)" ) );

	} else if ( kind === "testStart" ) {
		state.started++;
		console.log( "  [" + padLeft( state.started, 4 ) + "] " +
			( data.module || "(no module)" ) + ": " + data.name );

	} else if ( kind === "fail" ) {
		state.failures.push( data );
		reportFailure( data );

	} else if ( kind === "testDone" ) {
		record = moduleRecord( data.module );
		record.tests++;
		record.assertions += data.total;
		record.failed += data.failed;
		state.tests++;
		state.assertions += data.total;

	} else if ( kind === "skip" ) {
		state.skipped.push( ( data.module ? data.module + ": " : "" ) + data.name );
		console.log( "  SKIP (SEAL_SKIP_TESTS) " +
			( data.module ? data.module + ": " : "" ) + data.name );

	} else if ( kind === "done" ) {
		state.summary = data;
		if ( pendingResolve ) {
			// Small grace period so trailing console messages are delivered
			// before the browser is torn down.
			setTimeout( function() {
				pendingResolve();
			}, 500 );
		}

	} else if ( kind === "hookError" ) {
		console.log( "  HOOK ERROR: " + data.message );
	}
}

function messageText( message ) {
	var text;

	try {
		text = typeof message.text === "function" ? message.text() : message.text;
	} catch ( e ) {
		text = null;
	}
	return typeof text === "string" ? text : null;
}

function onConsoleMessage( message ) {
	var text = messageText( message ),
		payload;

	if ( !text || text.indexOf( MARKER ) !== 0 ) {
		return;
	}
	try {
		payload = JSON.parse( text.slice( MARKER.length ) );
	} catch ( e ) {
		return;
	}
	if ( payload && payload.kind ) {
		handleEvent( payload.kind, payload.data || {} );
	}
}

function report() {
	var i,
		record,
		summary;

	console.log( "" );
	console.log( "==================== per-module results ====================" );
	console.log( padRight( "module", 24 ) + padLeft( "tests", 8 ) +
		padLeft( "assertions", 13 ) + padLeft( "failed", 9 ) );
	console.log( "------------------------------------------------------------" );
	for ( i = 0; i < state.moduleOrder.length; i++ ) {
		record = state.modules[ state.moduleOrder[ i ] ];
		console.log( padRight( record.name, 24 ) + padLeft( record.tests, 8 ) +
			padLeft( record.assertions, 13 ) + padLeft( record.failed, 9 ) );
	}
	console.log( "------------------------------------------------------------" );

	if ( state.skipped.length ) {
		console.log( "" );
		console.log( "skipped via SEAL_SKIP_TESTS (" + state.skipped.length + "):" );
		for ( i = 0; i < state.skipped.length; i++ ) {
			console.log( "  - " + state.skipped[ i ] );
		}
	}

	if ( state.failures.length ) {
		console.log( "" );
		console.log( "failed assertions (" + state.failures.length + "):" );
		for ( i = 0; i < state.failures.length; i++ ) {
			reportFailure( state.failures[ i ] );
		}
	}

	summary = state.summary || {
		passed: state.assertions - state.failures.length,
		failed: state.failures.length,
		total: state.assertions
	};

	console.log( "" );
	console.log( summary.passed + " assertions of " + summary.total +
		" passed, " + summary.failed + " failed" );
	console.log( state.tests + " tests, " + summary.failed + " failures" );
	console.log( state.moduleStarts + " module transitions over " +
		state.moduleOrder.length + " distinct modules" );
}

// Returns a description of the problem, or null when the run is a clean pass.
function verdict() {
	if ( !state.summary ) {
		return "QUnit never reported done";
	}
	if ( state.summary.failed > 0 || state.failures.length > 0 ) {
		return state.summary.failed + " failed assertions (" +
			state.failures.length + " reported)";
	}
	if ( state.tests === 0 || state.summary.total === 0 ) {
		return "no tests executed";
	}
	return null;
}

function main() {
	var executablePath = findChrome(),
		browser = null,
		watchdog,
		finished;

	finished = new Promise( function( resolve ) {
		pendingResolve = resolve;
	} );

	watchdog = setTimeout( function() {
		console.log( "" );
		console.log( "TIMEOUT: QUnit did not finish within " +
			Math.round( timeoutMs / 1000 ) + "s" );
		report();
		process.exit( 3 );
	}, timeoutMs );

	console.log( "chrome: " + executablePath );
	console.log( "url:    " + pageUrl );
	console.log( "skips:  " + ( skipList.length ? skipList.join( " | " ) : "(none)" ) );

	puppeteer.launch( {
		executablePath: executablePath,
		headless: true,
		args: [
			"--no-sandbox",
			"--disable-setuid-sandbox",
			"--force-device-scale-factor=1"
		]
	} ).then( function( launched ) {
		browser = launched;
		return browser.newPage();
	} ).then( function( page ) {
		page.on( "console", onConsoleMessage );
		page.on( "pageerror", function( error ) {
			console.log( "  page error: " + ( error && error.message ? error.message : error ) );
		} );
		return page.evaluateOnNewDocument( browserHook, {
			marker: MARKER,
			skips: skipList
		} ).then( function() {
			// page.goto in subscript form: "goto" is a reserved word in ES3
			// and test/.jshintrc sets "es3": true (with "sub": true).
			return page[ "goto" ]( pageUrl, {
				waitUntil: "domcontentloaded",
				timeout: 120000
			} );
		} );
	} ).then( function() {
		return finished;
	} ).then( function() {
		clearTimeout( watchdog );
		report();
		return browser.close();
	} ).then( function() {
		var problem = verdict();

		if ( problem ) {
			console.log( "RESULT: FAIL - " + problem );
			process.exit( 1 );
		}
		console.log( "RESULT: PASS" );
		process.exit( 0 );
	}, function( error ) {
		clearTimeout( watchdog );
		console.log( "RUNNER ERROR: " +
			( error && error.stack ? error.stack : error ) );
		report();
		process.exit( 2 );
	} );
}

main();
