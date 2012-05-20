// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Exports a {@code ses.logger} which logs to the
 * console if one exists.
 *
 * <p>This <code>logger.js</code> file both defines the logger API and
 * provides default implementations for its methods. Because
 * <code>logger.js</code> is normally packaged in
 * <code>initSES.js</code>, it is built to support being overridden by
 * a script run <i>earlier</i>. For example, for better diagnostics,
 * consider loading and initializing <code>useHTMLLogger.js</code> first.
 *
 * <p>The {@code ses.logger} API consists of
 * <dl>
 *   <dt>log, info, warn, and error methods</dt>
 *     <dd>each of which take a list of arguments which should be
 *         stringified and appended together. The logger should
 *         display this string associated with that severity level. If
 *         any of the arguments has an associated stack trace
 *         (presumably Error objects), then the logger <i>may</i> also
 *         show this stack trace. If no {@code ses.logger} already
 *         exists, the default provided here forwards to the
 *         pre-existing global {@code console} if one
 *         exists. Otherwise, all four of these do nothing. If we
 *         default to forwarding to the pre-existing {@code console} ,
 *         we prepend an empty string as first argument since we do
 *         not want to obligate all loggers to implement the console's
 *         "%" formatting. </dd>
 *   <dt>classify(postSeverity)</dt>
 *     <dd>where postSeverity is a severity
 *         record as defined by {@code ses.severities} in
 *         <code>repairES5.js</code>, and returns a helpful record
 *         consisting of a
 *         <dl>
 *           <dt>consoleLevel:</dt>
 *             <dd>which is one of 'log', 'info', 'warn', or
 *                 'error', which can be used to select one of the above
 *                 methods.</dd>
 *           <dt>note:</dt>
 *             <dd>containing some helpful text to display
 *                 explaining the impact of this severity on SES.</dd>
 *         </dl>
 *   <dt>reportRepairs(reports)</dt>
 *     <dd>where {@code reports} is the list of repair reports, each
 *         of which contains
 *       <dl>
 *         <dt>description:</dt>
 *           <dd>a string describing the problem</dd>
 *         <dt>preSeverity:</dt>
 *           <dd>a severity record (as defined by {@code
 *               ses.severities} in <code>repairES5.js</code>)
 *               indicating the level of severity of this problem if
 *               unrepaired. Or, if !canRepair, then the severity
 *               whether or not repaired.</dd>
 *         <dt>canRepair:</dt>
 *           <dd>a boolean indicating "if the repair exists and the test
 *               subsequently does not detect a problem, are we now ok?"</dd>
 *         <dt>urls:</dt>
 *           <dd>a list of URL strings, each of which points at a page
 *               relevant for documenting or tracking the bug in
 *               question. These are typically into bug-threads in issue
 *               trackers for the various browsers.</dd>
 *         <dt>sections:</dt>
 *           <dd>a list of strings, each of which is a relevant ES5.1
 *               section number.</dd>
 *         <dt>tests:</dt>
 *           <dd>a list of strings, each of which is the name of a
 *               relevant test262 or sputnik test case.</dd>
 *         <dt>postSeverity:</dt>
 *           <dd>a severity record (as defined by {@code
 *               ses.severities} in <code>repairES5.js</code>)
 *               indicating the level of severity of this problem
 *               after all repairs have been attempted.</dd>
 *         <dt>beforeFailure:</dt>
 *           <dd>The outcome of the test associated with this record
 *               as run before any attempted repairs. If {@code
 *               false}, it means there was no failure. If {@code
 *               true}, it means that the test fails in some way that
 *               the authors of <code>repairES5.js</code>
 *               expected. Otherwise it returns a string describing
 *               the symptoms of an unexpected form of failure. This
 *               is typically considered a more severe form of failure
 *               than {@code true}, since the authors have not
 *               anticipated the consequences and safety
 *               implications.</dd>
 *         <dt>afterFailure:</dt>
 *           <dd>The outcome of the test associated with this record
 *               as run after all attempted repairs.</dd>
 *       </dl>
 *       The default behavior here is to be silent.</dd>
 *   <dt>reportMax()</dt>
 *     <dd>Displays only a summary of the worst case
 *         severity seen so far, according to {@code ses.maxSeverity} as
 *         interpreted by {@code ses.logger.classify}.</dd>
 *   <dt>reportDiagnosis(severity, status, problemList)</dt>
 *     <dd>where {@code severity} is a severity record, {@code status}
 *         is a brief string description of a list of problems, and
 *         {@code problemList} is a list of strings, each of which is
 *         one occurrence of the described problem.
 *         The default behavior here should only the number of
 *         problems, not the individual problems.</dd>
 * </dl>
 *
 * <p>Assumes only ES3. Compatible with ES5, ES5-strict, or
 * anticipated ES6.
 *
 * //provides ses.logger
 * @author Mark S. Miller
 * @requires console
 * @overrides ses, loggerModule
 */
var ses;
if (!ses) { ses = {}; }

(function loggerModule() {
  "use strict";

  var logger;
  function logNowhere(str) {}

  var slice = [].slice;
  var apply = slice.apply;



  if (ses.logger) {
    logger = ses.logger;

  } else if (typeof console !== 'undefined' && 'log' in console) {
    // We no longer test (typeof console.log === 'function') since,
    // on IE9 and IE10preview, in violation of the ES5 spec, it
    // is callable but has typeof "object".
    // See https://connect.microsoft.com/IE/feedback/details/685962/
    //   console-log-and-others-are-callable-but-arent-typeof-function

    // We manually wrap each call to a console method because <ul>
    // <li>On some platforms, these methods depend on their
    //     this-binding being the console.
    // <li>All this has to work on platforms that might not have their
    //     own {@code Function.prototype.bind}, and has to work before
    //     we install an emulated bind.
    // </ul>

    var forward = function(level, args) {
      args = slice.call(args, 0);
      // We don't do "console.apply" because "console" is not a function
      // on IE 10 preview 2 and it has no apply method. But it is a
      // callable that Function.prototype.apply can successfully apply.
      // This code most work on ES3 where there's no bind. When we
      // decide support defensiveness in contexts (frames) with mutable
      // primordials, we will need to revisit the "call" below.
      apply.call(console[level], console, [''].concat(args));

      // See debug.js
      var getStack = ses.getStack;
      if (getStack) {
        for (var i = 0, len = args.length; i < len; i++) {
          var stack = getStack(args[i]);
          if (stack) {
            console[level]('', stack);
          }
        }
      }
    };

    logger = {
      log:   function log(var_args)   { forward('log', arguments); },
      info:  function info(var_args)  { forward('info', arguments); },
      warn:  function warn(var_args)  { forward('warn', arguments); },
      error: function error(var_args) { forward('error', arguments); }
    };
  } else {
    logger = {
      log:   logNowhere,
      info:  logNowhere,
      warn:  logNowhere,
      error: logNowhere
    };
  }

  /**
   * Returns a record that's helpful for displaying a severity.
   *
   * <p>The record contains {@code consoleLevel} and {@code note}
   * properties whose values are strings. The {@code consoleLevel} is
   * {@code "log", "info", "warn", or "error"}, which can be used as
   * method names for {@code logger}, or, in an html context, as a css
   * class name. The {@code note} is a string stating the severity
   * level and its consequences for SES.
   */
  function defaultClassify(postSeverity) {
    var MAX_SES_SAFE = ses.severities.SAFE_SPEC_VIOLATION;

    var consoleLevel = 'log';
    var note = '';
    if (postSeverity.level > ses.severities.SAFE.level) {
      consoleLevel = 'info';
      note = postSeverity.description + '(' + postSeverity.level + ')';
      if (postSeverity.level > ses.maxAcceptableSeverity.level) {
        consoleLevel = 'error';
        note += ' is not suitable for SES';
      } else if (postSeverity.level > MAX_SES_SAFE.level) {
        consoleLevel = 'warn';
        note += ' is not SES-safe';
      }
      note += '.';
    }
    return {
      consoleLevel: consoleLevel,
      note: note
    };
  }

  if (!logger.classify) {
    logger.classify = defaultClassify;
  }

  /**
   * By default is silent
   */
  function defaultReportRepairs(reports) {}

  if (!logger.reportRepairs) {
    logger.reportRepairs = defaultReportRepairs;
  }

  /**
   * By default, logs a report suitable for display on the console.
   */
  function defaultReportMax() {
    if (ses.maxSeverity.level > ses.severities.SAFE.level) {
      var maxClassification = ses.logger.classify(ses.maxSeverity);
      logger[maxClassification.consoleLevel](
        'Max Severity: ' + maxClassification.note);
    }
  }

  if (!logger.reportMax) {
    logger.reportMax = defaultReportMax;
  }

  function defaultReportDiagnosis(severity, status, problemList) {
    var classification = ses.logger.classify(severity);
    ses.logger[classification.consoleLevel](
      problemList.length + ' ' + status);
  }

  if (!logger.reportDiagnosis) {
    logger.reportDiagnosis = defaultReportDiagnosis;
  }

  ses.logger = logger;

})();
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Monkey patch almost ES5 platforms into a closer
 * emulation of full <a href=
 * "http://code.google.com/p/es-lab/wiki/SecureableES5">Secureable
 * ES5</a>.
 *
 * <p>Assumes only ES3, but only proceeds to do useful repairs when
 * the platform is close enough to ES5 to be worth attempting
 * repairs. Compatible with almost-ES5, ES5, ES5-strict, and
 * anticipated ES6.
 *
 * <p>Ignore the "...requires ___global_test_function___" below. We
 * create it, use it, and delete it all within this module. But we
 * need to lie to the linter since it can't tell.
 *
 * //provides ses.statuses, ses.ok, ses.is, ses.makeDelayedTamperProof
 * //provides ses.makeCallerHarmless, ses.makeArgumentsHarmless
 * //provides ses.severities, ses.maxSeverity, ses.updateMaxSeverity
 * //provides ses.maxAcceptableSeverityName, ses.maxAcceptableSeverity
 *
 * @author Mark S. Miller
 * @requires ___global_test_function___, ___global_valueOf_function___
 * @requires JSON, navigator, this, eval, document
 * @overrides ses, RegExp, WeakMap, Object, parseInt, repairES5Module
 */
var RegExp;
var ses;

/**
 * <p>Qualifying platforms generally include all JavaScript platforms
 * shown on <a href="http://kangax.github.com/es5-compat-table/"
 * >ECMAScript 5 compatibility table</a> that implement {@code
 * Object.getOwnPropertyNames}. At the time of this writing,
 * qualifying browsers already include the latest released versions of
 * Internet Explorer (9), Firefox (4), Chrome (11), and Safari
 * (5.0.5), their corresponding standalone (e.g., server-side) JavaScript
 * engines, Rhino 1.73, and BESEN.
 *
 * <p>On such not-quite-ES5 platforms, some elements of these
 * emulations may lose SES safety, as enumerated in the comment on
 * each kludge record in the {@code kludges} array below. The platform
 * must at least provide {@code Object.getOwnPropertyNames}, because
 * it cannot reasonably be emulated.
 *
 * <p>This file is useful by itself, as it has no dependencies on the
 * rest of SES. It creates no new global bindings, but merely repairs
 * standard globals or standard elements reachable from standard
 * globals. If the future-standard {@code WeakMap} global is present,
 * as it is currently on FF7.0a1, then it will repair it in place. The
 * one non-standard element that this file uses is {@code console} if
 * present, in order to report the repairs it found necessary, in
 * which case we use its {@code log, info, warn}, and {@code error}
 * methods. If {@code console.log} is absent, then this file performs
 * its repairs silently.
 *
 * <p>Generally, this file should be run as the first script in a
 * JavaScript context (i.e. a browser frame), as it relies on other
 * primordial objects and methods not yet being perturbed.
 *
 * <p>TODO(erights): This file tries to protect itself from some
 * post-initialization perturbation by stashing some of the
 * primordials it needs for later use, but this attempt is currently
 * incomplete. We need to revisit this when we support Confined-ES5,
 * as a variant of SES in which the primordials are not frozen. See
 * previous failed attempt at <a
 * href="http://codereview.appspot.com/5278046/" >Speeds up
 * WeakMap. Preparing to support unfrozen primordials.</a>. From
 * analysis of this failed attempt, it seems that the only practical
 * way to support CES is by use of two frames, where most of initSES
 * runs in a SES frame, and so can avoid worrying about most of these
 * perturbations.
 */
(function repairES5Module(global) {
  "use strict";

  /**
   * The severity levels.
   *
   * <dl>
   *   <dt>SAFE</dt><dd>no problem.
   *   <dt>SAFE_SPEC_VIOLATION</dt>
   *     <dd>safe (in an integrity sense) even if unrepaired. May
   *         still lead to inappropriate failures.</dd>
   *   <dt>UNSAFE_SPEC_VIOLATION</dt>
   *     <dd>a safety issue only indirectly, in that this spec
   *         violation may lead to the corruption of assumptions made
   *         by other security critical or defensive code.</dd>
   *   <dt>NOT_OCAP_SAFE</dt>
   *     <dd>a violation of object-capability rules among objects
   *         within a coarse-grained unit of isolation.</dd>
   *   <dt>NOT_ISOLATED</dt>
   *     <dd>an inability to reliably sandbox even coarse-grain units
   *         of isolation.</dd>
   *   <dt>NEW_SYMPTOM</dt>
   *     <dd>some test failed in a way we did not expect.</dd>
   *   <dt>NOT_SUPPORTED</dt>
   *     <dd>this platform cannot even support SES development in an
   *         unsafe manner.</dd>
   * </dl>
   */
  ses.severities = {
    SAFE:                  { level: 0, description: 'Safe' },
    SAFE_SPEC_VIOLATION:   { level: 1, description: 'Safe spec violation' },
    UNSAFE_SPEC_VIOLATION: { level: 2, description: 'Unsafe spec violation' },
    NOT_OCAP_SAFE:         { level: 3, description: 'Not ocap safe' },
    NOT_ISOLATED:          { level: 4, description: 'Not isolated' },
    NEW_SYMPTOM:           { level: 5, description: 'New symptom' },
    NOT_SUPPORTED:         { level: 6, description: 'Not supported' }
  };

  /**
   * Statuses.
   *
   * <dl>
   *   <dt>ALL_FINE</dt>
   *     <dd>test passed before and after.</dd>
   *   <dt>REPAIR_FAILED</dt>
   *     <dd>test failed before and after repair attempt.</dd>
   *   <dt>NOT_REPAIRED</dt>
   *     <dd>test failed before and after, with no repair to attempt.</dd>
   *   <dt>REPAIRED_UNSAFELY</dt>
   *     <dd>test failed before and passed after repair attempt, but
   *         the repair is known to be inadequate for security, so the
   *         real problem remains.</dd>
   *   <dt>REPAIRED</dt>
   *     <dd>test failed before and passed after repair attempt,
   *         repairing the problem (canRepair was true).</dd>
   *   <dt>ACCIDENTALLY_REPAIRED</dt>
   *      <dd>test failed before and passed after, despite no repair
   *          to attempt. (Must have been fixed by some other
   *          attempted repair.)</dd>
   *   <dt>BROKEN_BY_OTHER_ATTEMPTED_REPAIRS</dt>
   *      <dd>test passed before and failed after, indicating that
   *          some other attempted repair created the problem.</dd>
   * </dl>
   */
  ses.statuses = {
    ALL_FINE:                          'All fine',
    REPAIR_FAILED:                     'Repair failed',
    NOT_REPAIRED:                      'Not repaired',
    REPAIRED_UNSAFELY:                 'Repaired unsafely',
    REPAIRED:                          'Repaired',
    ACCIDENTALLY_REPAIRED:             'Accidentally repaired',
    BROKEN_BY_OTHER_ATTEMPTED_REPAIRS: 'Broken by other attempted repairs'
  };


  var logger = ses.logger;

  /**
   * As we start to repair, this will track the worst post-repair
   * severity seen so far.
   */
  ses.maxSeverity = ses.severities.SAFE;

  /**
   * {@code ses.maxAcceptableSeverity} is the max post-repair severity
   * that is considered acceptable for proceeding with the SES
   * verification-only strategy.
   *
   * <p>Although <code>repairES5.js</code> can be used standalone for
   * partial ES5 repairs, its primary purpose is to repair as a first
   * stage of <code>initSES.js</code> for purposes of supporting SES
   * security. In support of that purpose, we initialize
   * {@code ses.maxAcceptableSeverity} to the post-repair severity
   * level at which we should report that we are unable to adequately
   * support SES security. By default, this is set to
   * {@code ses.severities.SAFE_SPEC_VIOLATION}, which is the maximum
   * severity that we believe results in no loss of SES security.
   *
   * <p>If {@code ses.maxAcceptableSeverityName} is already set (to a
   * severity property name of a severity below {@code
   * ses.NOT_SUPPORTED}), then we use that setting to initialize
   * {@code ses.maxAcceptableSeverity} instead. For example, if we are
   * using SES only for isolation, then we could set it to
   * 'NOT_OCAP_SAFE', in which case repairs that are inadequate for
   * object-capability (ocap) safety would still be judged safe for
   * our purposes.
   *
   * <p>As repairs proceed, they update {@code ses.maxSeverity} to
   * track the worst case post-repair severity seen so far. When
   * {@code ses.ok()} is called, it return whether {@code
   * ses.maxSeverity} is still less than or equal to
   * {@code ses.maxAcceptableSeverity}, indicating that this platform
   * still seems adequate for supporting SES. In the Caja context, we
   * have the choice of using SES on those platforms which we judge to
   * be adequately repairable, or otherwise falling back to Caja's
   * ES5/3 translator.
   */
  if (ses.maxAcceptableSeverityName) {
    var maxSev = ses.severities[ses.maxAcceptableSeverityName];
    if (maxSev && typeof maxSev.level === 'number' &&
        maxSev.level >= ses.severities.SAFE.level &&
        maxSev.level < ses.severities.NOT_SUPPORTED.level) {
      // do nothing
    } else {
      logger.error('Ignoring bad maxAcceptableSeverityName: ' +
                   ses.maxAcceptableSeverityName + '.') ;
      ses.maxAcceptableSeverityName = 'SAFE_SPEC_VIOLATION';
    }
  } else {
    ses.maxAcceptableSeverityName = 'SAFE_SPEC_VIOLATION';
  }
  ses.maxAcceptableSeverity = ses.severities[ses.maxAcceptableSeverityName];

  /**
   * Once this returns false, we can give up on the SES
   * verification-only strategy and fall back to ES5/3 translation.
   */
  ses.ok = function ok() {
    return ses.maxSeverity.level <= ses.maxAcceptableSeverity.level;
  };

  /**
   * Update the max based on the provided severity.
   *
   * <p>If the provided severity exceeds the max so far, update the
   * max to match.
   */
  ses.updateMaxSeverity = function updateMaxSeverity(severity) {
    if (severity.level > ses.maxSeverity.level) {
      ses.maxSeverity = severity;
    }
  };

  //////// Prepare for "caller" and "argument" testing and repair /////////

  /**
   * Needs to work on ES3, since repairES5.js may be run on an ES3
   * platform.
   */
  function strictForEachFn(list, callback) {
    for (var i = 0, len = list.length; i < len; i++) {
      callback(list[i], i);
    }
  }

  /**
   * Needs to work on ES3, since repairES5.js may be run on an ES3
   * platform.
   *
   * <p>Also serves as our representative strict function, by contrast
   * to builtInMapMethod below, for testing what the "caller" and
   * "arguments" properties of a strict function reveals.
   */
  function strictMapFn(list, callback) {
    var result = [];
    for (var i = 0, len = list.length; i < len; i++) {
      result.push(callback(list[i], i));
    }
    return result;
  }

  var objToString = Object.prototype.toString;

  /**
   * Sample map early, to obtain a representative built-in for testing.
   *
   * <p>There is no reliable test for whether a function is a
   * built-in, and it is possible some of the tests below might
   * replace the built-in Array.prototype.map, though currently none
   * do. Since we <i>assume</i> (but with no reliable way to check)
   * that repairES5.js runs in its JavaScript context before anything
   * which might have replaced map, we sample it now. The map method
   * is a particularly nice one to sample, since it can easily be used
   * to test what the "caller" and "arguments" properties on a
   * in-progress built-in method reveals.
   */
  var builtInMapMethod = Array.prototype.map;

  var builtInForEach = Array.prototype.forEach;

  /**
   * http://wiki.ecmascript.org/doku.php?id=harmony:egal
   */
  var is = ses.is = Object.is || function(x, y) {
    if (x === y) {
      // 0 === -0, but they are not identical
      return x !== 0 || 1 / x === 1 / y;
    }

    // NaN !== NaN, but they are identical.
    // NaNs are the only non-reflexive value, i.e., if x !== x,
    // then x is a NaN.
    // isNaN is broken: it converts its argument to number, so
    // isNaN("foo") => true
    return x !== x && y !== y;
  };


  /**
   * By the time this module exits, either this is repaired to be a
   * function that is adequate to make the "caller" property of a
   * strict or built-in function harmess, or this module has reported
   * a failure to repair.
   *
   * <p>Start off with the optimistic assumption that nothing is
   * needed to make the "caller" property of a strict or built-in
   * function harmless. We are not concerned with the "caller"
   * property of non-strict functions. It is not the responsibility of
   * this module to actually make these "caller" properties
   * harmless. Rather, this module only provides this function so
   * clients such as startSES.js can use it to do so on the functions
   * they whitelist.
   *
   * <p>If the "caller" property of strict functions are not already
   * harmless, then this platform cannot be repaired to be
   * SES-safe. The only reason why {@code makeCallerHarmless} must
   * work on strict functions in addition to built-in is that some of
   * the other repairs below will replace some of the built-ins with
   * strict functions, so startSES.js will apply {@code
   * makeCallerHarmless} blindly to both strict and built-in
   * functions. {@code makeCallerHarmless} simply need not to complete
   * without breaking anything when given a strict function argument.
   */
  ses.makeCallerHarmless = function assumeCallerHarmless(func, path) {
    return 'Apparently fine';
  };

  /**
   * By the time this module exits, either this is repaired to be a
   * function that is adequate to make the "arguments" property of a
   * strict or built-in function harmess, or this module has reported
   * a failure to repair.
   *
   * Exactly analogous to {@code makeCallerHarmless}, but for
   * "arguments" rather than "caller".
   */
  ses.makeArgumentsHarmless = function assumeArgumentsHarmless(func, path) {
    return 'Apparently fine';
  };

  /**
   * "makeTamperProof()" returns a "tamperProof(obj)" function that
   * acts like "Object.freeze(obj)", except that, if obj is a
   * <i>prototypical</i> object (defined below), it ensures that the
   * effect of freezing properties of obj does not suppress the
   * ability to override these properties on derived objects by simple
   * assignment.
   *
   * <p>Because of lack of sufficient foresight at the time, ES5
   * unifortunately specified that a simple assignment to a
   * non-existent property must fail if it would override a
   * non-writable data property of the same name. (In retrospect, this
   * was a mistake, but it is now too late and we must live with the
   * consequences.) As a result, simply freezing an object to make it
   * tamper proof has the unfortunate side effect of breaking
   * previously correct code that is considered to have followed JS
   * best practices, of this previous code used assignment to
   * override.
   *
   * <p>To work around this mistake, tamperProof(obj) detects if obj
   * is <i>prototypical</i>, i.e., is an object whose own
   * "constructor" is a function whose "prototype" is this obj. If so,
   * then when tamper proofing it, prior to freezing, replace all its
   * configurable own data properties with accessor properties which
   * simulate what we should have specified -- that assignments to
   * derived objects succeed if otherwise possible.
   *
   * <p>Some platforms (Chrome and Safari as of this writing)
   * implement the assignment semantics ES5 should have specified
   * rather than what it did specify.
   * "test_ASSIGN_CAN_OVERRIDE_FROZEN()" below tests whether we are on
   * such a platform. If so, "repair_ASSIGN_CAN_OVERRIDE_FROZEN()"
   * replaces "makeTamperProof" with a function that simply returns
   * "Object.freeze", since the complex workaround here is not needed
   * on those platforms.
   *
   * <p>"makeTamperProof" should only be called after the trusted
   * initialization has done all the monkey patching that it is going
   * to do on the Object.* methods, but before any untrusted code runs
   * in this context.
   */
  var makeTamperProof = function defaultMakeTamperProof() {

    // Sample these after all trusted monkey patching initialization
    // but before any untrusted code runs in this frame.
    var gopd = Object.getOwnPropertyDescriptor;
    var gopn = Object.getOwnPropertyNames;
    var getProtoOf = Object.getPrototypeOf;
    var freeze = Object.freeze;
    var isFrozen = Object.isFrozen;
    var defProp = Object.defineProperty;

    function tamperProof(obj) {
      if (obj !== Object(obj)) { return obj; }
      var func;
      if (typeof obj === 'object' &&
          !!gopd(obj, 'constructor') &&
          typeof (func = obj.constructor) === 'function' &&
          func.prototype === obj &&
          !isFrozen(obj)) {
        strictForEachFn(gopn(obj), function(name) {
          var value;
          function getter() {
            if (obj === this) { return value; }
            if (this === void 0 || this === null) { return void 0; }
            var thisObj = Object(this);
            if (!!gopd(thisObj, name)) { return this[name]; }
            // TODO(erights): If we can reliably uncurryThis() in
            // repairES5.js, the next line should be:
            //   return callFn(getter, getProtoOf(thisObj));
            return getter.call(getProtoOf(thisObj));
          }
          function setter(newValue) {
            if (obj === this) {
              throw new TypeError('Cannot set virtually frozen property: ' +
                                  name);
            }
            if (!!gopd(this, name)) {
              this[name] = newValue;
            }
            // TODO(erights): Do all the inherited property checks
            defProp(this, name, {
              value: newValue,
              writable: true,
              enumerable: true,
              configurable: true
            });
          }
          var desc = gopd(obj, name);
          if (desc.configurable && 'value' in desc) {
            value = desc.value;
            getter.prototype = null;
            setter.prototype = null;
            defProp(obj, name, {
              get: getter,
              set: setter,
              // We should be able to omit the enumerable line, since it
              // should default to its existing setting.
              enumerable: desc.enumerable,
              configurable: false
            });
          }
        });
      }
      return freeze(obj);
    }
    return tamperProof;
  };


  var needToTamperProof = [];
  /**
   * Various repairs may expose non-standard objects that are not
   * reachable from startSES's root, and therefore not freezable by
   * startSES's normal whitelist traversal. However, freezing these
   * during repairES5.js may be too early, as it is before WeakMap.js
   * has had a chance to monkey patch Object.freeze if necessary, in
   * order to install hidden properties for its own use before the
   * object becomes non-extensible.
   */
  function rememberToTamperProof(obj) {
    needToTamperProof.push(obj);
  }

  /**
   * Makes and returns a tamperProof(obj) function, and uses it to
   * tamper proof all objects whose tamper proofing had been delayed.
   *
   * <p>"makeDelayedTamperProof()" must only be called once.
   */
  ses.makeDelayedTamperProof = function makeDelayedTamperProof() {
    var tamperProof = makeTamperProof();
    strictForEachFn(needToTamperProof, tamperProof);
    needToTamperProof = void 0;
    return tamperProof;
  };

  /**
   * Where the "that" parameter represents a "this" that should have
   * been bound to "undefined" but may be bound to a global or
   * globaloid object.
   *
   * <p>The "desc" parameter is a string to describe the "that" if it
   * is something unexpected.
   */
  function testGlobalLeak(desc, that) {
    if (that === void 0) { return false; }
    if (that === global) { return true; }
    if ({}.toString.call(that) === '[object Window]') { return true; }
    return desc + ' leaked as: ' + that;
  }

  ////////////////////// Tests /////////////////////
  //
  // Each test is a function of no arguments that should not leave any
  // significant side effects, which tests for the presence of a
  // problem. It returns either
  // <ul>
  // <li>false, meaning that the problem does not seem to be present.
  // <li>true, meaning that the problem is present in a form that we expect.
  // <li>a non-empty string, meaning that there seems to be a related
  //     problem, but we're seeing a symptom different than what we
  //     expect. The string should describe the new symptom. It must
  //     be non-empty so that it is truthy.
  // </ul>
  // All the tests are run first to determine which corresponding
  // repairs to attempt. Then these repairs are run. Then all the
  // tests are rerun to see how they were effected by these repair
  // attempts. Finally, we report what happened.

  /**
   * If {@code Object.getOwnPropertyNames} is missing, we consider
   * this to be an ES3 browser which is unsuitable for attempting to
   * run SES.
   *
   * <p>If {@code Object.getOwnPropertyNames} is missing, there is no
   * way to emulate it.
   */
  function test_MISSING_GETOWNPROPNAMES() {
    return !('getOwnPropertyNames' in Object);
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=64250
   *
   * <p>No workaround attempted. Just reporting that this platform is
   * not SES-safe.
   */
  function test_GLOBAL_LEAKS_FROM_GLOBAL_FUNCTION_CALLS() {
    global.___global_test_function___ = function() { return this; };
    var that = ___global_test_function___();
    delete global.___global_test_function___;
    return testGlobalLeak('Global func "this"', that);
  }

  /**
   * Detects whether the most painful ES3 leak is still with us.
   */
  function test_GLOBAL_LEAKS_FROM_ANON_FUNCTION_CALLS() {
    var that = (function(){ return this; })();
    return testGlobalLeak('Anon func "this"', that);
  }

  var strictThis = this;

  /**
   *
   */
  function test_GLOBAL_LEAKS_FROM_STRICT_THIS() {
    return testGlobalLeak('Strict "this"', strictThis);
  }

  /**
   * Detects
   * https://bugs.webkit.org/show_bug.cgi?id=51097
   * https://bugs.webkit.org/show_bug.cgi?id=58338
   * http://code.google.com/p/v8/issues/detail?id=1437
   *
   * <p>No workaround attempted. Just reporting that this platform is
   * not SES-safe.
   */
  function test_GLOBAL_LEAKS_FROM_BUILTINS() {
    var v = {}.valueOf;
    var that = 'dummy';
    try {
      that = v();
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'valueOf() threw: ' + err;
    }
    if (that === void 0) {
      // Should report as a safe spec violation
      return false;
    }
    return testGlobalLeak('valueOf()', that);
  }

  /**
   *
   */
  function test_GLOBAL_LEAKS_FROM_GLOBALLY_CALLED_BUILTINS() {
    global.___global_valueOf_function___ = {}.valueOf;
    var that = 'dummy';
    try {
      that = ___global_valueOf_function___();
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'valueOf() threw: ' + err;
    } finally {
      delete global.___global_valueOf_function___;
    }
    if (that === void 0) {
      // Should report as a safe spec violation
      return false;
    }
    return testGlobalLeak('Global valueOf()', that);
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=55736
   *
   * <p>As of this writing, the only major browser that does implement
   * Object.getOwnPropertyNames but not Object.freeze etc is the
   * released Safari 5 (JavaScriptCore). The Safari beta 5.0.4
   * (5533.20.27, r84622) already does implement freeze, which is why
   * this WebKit bug is listed as closed. When the released Safari has
   * this fix, we can retire this kludge.
   *
   * <p>This kludge is <b>not</b> safety preserving. The emulations it
   * installs if needed do not actually provide the safety that the
   * rest of SES relies on.
   */
  function test_MISSING_FREEZE_ETC() {
    return !('freeze' in Object);
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1530
   *
   * <p>Detects whether the value of a function's "prototype" property
   * as seen by normal object operations might deviate from the value
   * as seem by the reflective {@code Object.getOwnPropertyDescriptor}
   */
  function test_FUNCTION_PROTOTYPE_DESCRIPTOR_LIES() {
    function foo() {}
    Object.defineProperty(foo, 'prototype', { value: {} });
    return foo.prototype !==
      Object.getOwnPropertyDescriptor(foo, 'prototype').value;
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=55537
   *
   * This bug is fixed on the latest Safari beta 5.0.5 (5533.21.1,
   * r88603). When the released Safari has this fix, we can retire
   * this kludge.
   *
   * <p>This kludge is safety preserving.
   */
  function test_MISSING_CALLEE_DESCRIPTOR() {
    function foo(){}
    if (Object.getOwnPropertyNames(foo).indexOf('callee') < 0) { return false; }
    if (foo.hasOwnProperty('callee')) {
      return 'Empty strict function has own callee';
    }
    return true;
  }

  /**
   * A strict delete should either succeed, returning true, or it
   * should fail by throwing a TypeError. Under no circumstances
   * should a strict delete return false.
   *
   * <p>This case occurs on IE10preview2.
   */
  function test_STRICT_DELETE_RETURNS_FALSE() {
    if (!RegExp.hasOwnProperty('rightContext')) { return false; }
    var deleted;
    try {
      deleted = delete RegExp.rightContext;
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Deletion failed with: ' + err;
    }
    if (deleted) { return false; }
    return true;
  }

  /**
   * Detects https://bugzilla.mozilla.org/show_bug.cgi?id=591846
   * as applied to the RegExp constructor.
   *
   * <p>Note that Mozilla lists this bug as closed. But reading that
   * bug thread clarifies that is partially because the code in {@code
   * repair_REGEXP_CANT_BE_NEUTERED} enables us to work around the
   * non-configurability of the RegExp statics.
   */
  function test_REGEXP_CANT_BE_NEUTERED() {
    if (!RegExp.hasOwnProperty('leftContext')) { return false; }
    var deleted;
    try {
      deleted = delete RegExp.leftContext;
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return 'Deletion failed with: ' + err;
    }
    if (!RegExp.hasOwnProperty('leftContext')) { return false; }
    if (deleted) {
      return 'Deletion of RegExp.leftContext did not succeed.';
    } else {
      // This case happens on IE10preview2, as demonstrated by
      // test_STRICT_DELETE_RETURNS_FALSE.
      return true;
    }
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1393
   *
   * <p>This kludge is safety preserving.
   */
  function test_REGEXP_TEST_EXEC_UNSAFE() {
    (/foo/).test('xfoox');
    var match = new RegExp('(.|\r|\n)*','').exec()[0];
    if (match === 'undefined') { return false; }
    if (match === 'xfoox') { return true; }
    return 'regExp.exec() does not match against "undefined".';
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=26382
   *
   * <p>As of this writing, the only major browser that does implement
   * Object.getOwnPropertyNames but not Function.prototype.bind is
   * Safari 5 (JavaScriptCore), including the current Safari beta
   * 5.0.4 (5533.20.27, r84622).
   *
   * <p>This kludge is safety preserving. But see
   * https://bugs.webkit.org/show_bug.cgi?id=26382#c25 for why this
   * kludge cannot faithfully implement the specified semantics.
   *
   * <p>See also https://bugs.webkit.org/show_bug.cgi?id=42371
   */
  function test_MISSING_BIND() {
    return !('bind' in Function.prototype);
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=892
   *
   * <p>This tests whether the built-in bind method violates the spec
   * by calling the original using its current .apply method rather
   * than the internal [[Call]] method. The workaround is the same as
   * for test_MISSING_BIND -- to replace the built-in bind with one
   * written in JavaScript. This introduces a different bug though: As
   * https://bugs.webkit.org/show_bug.cgi?id=26382#c29 explains, a
   * bind written in JavaScript cannot emulate the specified currying
   * over the construct behavior, and so fails to enable a var-args
   * {@code new} operation.
   */
  function test_BIND_CALLS_APPLY() {
    if (!('bind' in Function.prototype)) { return false; }
    var applyCalled = false;
    function foo() { return [].slice.call(arguments,0).join(','); }
    foo.apply = function fakeApply(self, args) {
      applyCalled = true;
      return Function.prototype.apply.call(this, self, args);
    };
    var b = foo.bind(33,44);
    var answer = b(55,66);
    if (applyCalled) { return true; }
    if (answer === '44,55,66') { return false; }
    return 'Bind test returned "' + answer + '" instead of "44,55,66".';
  }

  /**
   * Demonstrates the point made by comment 29
   * https://bugs.webkit.org/show_bug.cgi?id=26382#c29
   *
   * <p>Tests whether Function.prototype.bind curries over
   * construction ({@code new}) behavior. A built-in bind should. A
   * bind emulation written in ES5 can't.
   */
  function test_BIND_CANT_CURRY_NEW() {
    function construct(f, args) {
      var bound = Function.prototype.bind.apply(f, [null].concat(args));
      return new bound();
    }
    var d;
    try {
      d = construct(Date, [1957, 4, 27]);
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return 'Curries construction failed with: ' + err;
    }
    if (typeof d === 'string') { return true; } // Opera
    var str = objToString.call(d);
    if (str === '[object Date]') { return false; }
    return 'Unexpected ' + str + ': ' + d;
  }

  /**
   * Detects http://code.google.com/p/google-caja/issues/detail?id=1362
   *
   * <p>This is an unfortunate oversight in the ES5 spec: Even if
   * Date.prototype is frozen, it is still defined to be a Date, and
   * so has mutable state in internal properties that can be mutated
   * by the primordial mutation methods on Date.prototype, such as
   * {@code Date.prototype.setFullYear}.
   *
   * <p>This kludge is safety preserving.
   */
  function test_MUTABLE_DATE_PROTO() {
    try {
      Date.prototype.setFullYear(1957);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Mutating Date.prototype failed with: ' + err;
    }
    var v = Date.prototype.getFullYear();
    Date.prototype.setFullYear(NaN); // hopefully undoes the damage
    if (v !== v && typeof v === 'number') {
      // NaN indicates we're probably ok.
      // TODO(erights) Should we report this as a symptom anyway, so
      // that we get the repair which gives us a reliable TypeError?
      return false;
    }
    if (v === 1957) { return true; }
    return 'Mutating Date.prototype did not throw';
  }

  /**
   * Detects https://bugzilla.mozilla.org/show_bug.cgi?id=656828
   *
   * <p>A bug in the current FF6.0a1 implementation: Even if
   * WeakMap.prototype is frozen, it is still defined to be a WeakMap,
   * and so has mutable state in internal properties that can be
   * mutated by the primordial mutation methods on WeakMap.prototype,
   * such as {@code WeakMap.prototype.set}.
   *
   * <p>This kludge is safety preserving.
   *
   * <p>TODO(erights): Update the ES spec page to reflect the current
   * agreement with Mozilla.
   */
  function test_MUTABLE_WEAKMAP_PROTO() {
    if (typeof WeakMap !== 'function') { return false; }
    var x = {};
    try {
      WeakMap.prototype.set(x, 86);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Mutating WeakMap.prototype failed with: ' + err;
    }
    var v = WeakMap.prototype.get(x);
    // Since x cannot escape, there's no observable damage to undo.
    if (v === 86) { return true; }
    return 'Mutating WeakMap.prototype did not throw';
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1447
   *
   * <p>This bug is fixed as of V8 r8258 bleeding-edge, but is not yet
   * available in the latest dev-channel Chrome (13.0.782.15 dev).
   *
   * <p>Unfortunately, an ES5 strict method wrapper cannot emulate
   * absence of a [[Construct]] behavior, as specified for the Chapter
   * 15 built-in methods. The installed wrapper relies on {@code
   * Function.prototype.apply}, as inherited by original, obeying its
   * contract.
   *
   * <p>This kludge is safety preserving but non-transparent, in that
   * the real forEach is frozen even in the success case, since we
   * have to freeze it in order to test for this failure. We could
   * repair this non-transparency by replacing it with a transparent
   * wrapper (as http://codereview.appspot.com/5278046/ does), but
   * since the SES use of this will freeze it anyway and the
   * indirection is costly, we choose not to for now.
   */
  function test_NEED_TO_WRAP_FOREACH() {
    if (!('freeze' in Object)) {
      // Object.freeze is still absent on released Android and would
      // cause a bogus bug detection in the following try/catch code.
      return false;
    }
    if (Array.prototype.forEach !== builtInForEach) {
      // If it is already wrapped, we are confident the problem does
      // not occur, and we need to skip the test to avoid freezing the
      // wrapper.
      return false;
    }
    try {
      ['z'].forEach(function(){ Object.freeze(Array.prototype.forEach); });
      return false;
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return 'freezing forEach failed with ' + err;
    }
  }

  /**
   * <p>Sometimes, when trying to freeze an object containing an
   * accessor property with a getter but no setter, Chrome <= 17 fails
   * with <blockquote>Uncaught TypeError: Cannot set property ident___
   * of #<Object> which has only a getter</blockquote>. So if
   * necessary, this kludge overrides {@code Object.defineProperty} to
   * always install a dummy setter in lieu of the absent one.
   *
   * <p>Since this problem seems to have gone away as of Chrome 18, it
   * is no longer as important to isolate and report it.
   *
   * <p>TODO(erights): We should also override {@code
   * Object.getOwnPropertyDescriptor} to hide the presence of the
   * dummy setter, and instead report an absent setter.
   */
  function test_NEEDS_DUMMY_SETTER() {
    if (NEEDS_DUMMY_SETTER_repaired) { return false; }
    if (typeof navigator === 'undefined') { return false; }
    var ChromeMajorVersionPattern = (/Chrome\/(\d*)\./);
    var match = ChromeMajorVersionPattern.exec(navigator.userAgent);
    if (!match) { return false; }
    var ver = +match[1];
    return ver <= 17;
  }
  /** we use this variable only because we haven't yet isolated a test
   * for the problem. */
  var NEEDS_DUMMY_SETTER_repaired = false;

  /**
   * Detects http://code.google.com/p/chromium/issues/detail?id=94666
   */
  function test_FORM_GETTERS_DISAPPEAR() {
    function getter() { return 'gotten'; }

    if (typeof document === 'undefined' ||
       typeof document.createElement !== 'function') {
      // likely not a browser environment
      return false;
    }
    var f = document.createElement("form");
    try {
      Object.defineProperty(f, 'foo', {
        get: getter,
        set: void 0
      });
    } catch (err) {
      // Happens on Safari 5.0.2 on IPad2.
      return 'defining accessor on form failed with: ' + err;
    }
    var desc = Object.getOwnPropertyDescriptor(f, 'foo');
    if (desc.get === getter) { return false; }
    if (desc.get === void 0) { return true; }
    return 'Getter became ' + desc.get;
  }

  /**
   * Detects https://bugzilla.mozilla.org/show_bug.cgi?id=637994
   *
   * <p>On Firefox 4 an inherited non-configurable accessor property
   * appears to be an own property of all objects which inherit this
   * accessor property. This is fixed as of Forefox Nightly 7.0a1
   * (2011-06-21).
   *
   * <p>Our workaround wraps hasOwnProperty, getOwnPropertyNames, and
   * getOwnPropertyDescriptor to heuristically decide when an accessor
   * property looks like it is apparently own because of this bug, and
   * suppress reporting its existence.
   *
   * <p>However, it is not feasible to likewise wrap JSON.stringify,
   * and this bug will cause JSON.stringify to be misled by inherited
   * enumerable non-configurable accessor properties. To prevent this,
   * we wrap defineProperty, freeze, and seal to prevent the creation
   * of <i>enumerable</i> non-configurable accessor properties on
   * those platforms with this bug.
   *
   * <p>A little known fact about JavaScript is that {@code
   * Object.prototype.propertyIsEnumerable} actually tests whether a
   * property is both own and enumerable. Assuming that our wrapping
   * of defineProperty, freeze, and seal prevents the occurrence of an
   * enumerable non-configurable accessor property, it should also
   * prevent the occurrence of this bug for any enumerable property,
   * and so we do not need to wrap propertyIsEnumerable.
   *
   * <p>This kludge seems to be safety preserving, but the issues are
   * delicate and not well understood.
   */
  function test_ACCESSORS_INHERIT_AS_OWN() {
    var base = {};
    var derived = Object.create(base);
    function getter() { return 'gotten'; }
    Object.defineProperty(base, 'foo', { get: getter });
    if (!derived.hasOwnProperty('foo') &&
        Object.getOwnPropertyDescriptor(derived, 'foo') === void 0 &&
        Object.getOwnPropertyNames(derived).indexOf('foo') < 0) {
      return false;
    }
    if (!derived.hasOwnProperty('foo') ||
        Object.getOwnPropertyDescriptor(derived, 'foo').get !== getter ||
        Object.getOwnPropertyNames(derived).indexOf('foo') < 0) {
      return 'Accessor properties partially inherit as own properties.';
    }
    Object.defineProperty(base, 'bar', { get: getter, configurable: true });
    if (!derived.hasOwnProperty('bar') &&
        Object.getOwnPropertyDescriptor(derived, 'bar') === void 0 &&
        Object.getOwnPropertyNames(derived).indexOf('bar') < 0) {
      return true;
    }
    return 'Accessor properties inherit as own even if configurable.';
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1360
   *
   * Our workaround wraps {@code sort} to wrap the comparefn.
   */
  function test_SORT_LEAKS_GLOBAL() {
    var that = 'dummy';
    [2,3].sort(function(x,y) { that = this; return x - y; });
    if (that === void 0) { return false; }
    if (that === global) { return true; }
    return 'sort called comparefn with "this" === ' + that;
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1360
   *
   * <p>Our workaround wraps {@code replace} to wrap the replaceValue
   * if it's a function.
   */
  function test_REPLACE_LEAKS_GLOBAL() {
    var that = 'dummy';
    function capture() { that = this; return 'y';}
    'x'.replace(/x/, capture);
    if (that === void 0) { return false; }
    if (that === capture) {
      // This case happens on IE10preview2. See
      // https://connect.microsoft.com/IE/feedback/details/685928/
      //   bad-this-binding-for-callback-in-string-prototype-replace
      // TODO(erights): When this happens, the kludge.description is
      // wrong.
      return true;
    }
    if (that === global) { return true; }
    return 'Replace called replaceValue function with "this" === ' + that;
  }

  /**
   * Detects
   * https://connect.microsoft.com/IE/feedback/details/
   *   685436/getownpropertydescriptor-on-strict-caller-throws
   *
   * <p>Object.getOwnPropertyDescriptor must work even on poisoned
   * "caller" properties.
   */
  function test_CANT_GOPD_CALLER() {
    var desc = null;
    try {
      desc = Object.getOwnPropertyDescriptor(function(){}, 'caller');
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return 'getOwnPropertyDescriptor failed with: ' + err;
    }
    if (desc &&
        typeof desc.get === 'function' &&
        typeof desc.set === 'function' &&
        !desc.configurable) {
      return false;
    }
    if (desc &&
        desc.value === null &&
        !desc.writable &&
        !desc.configurable) {
      // Seen in IE9. Harmless by itself
      return false;
    }
    return 'getOwnPropertyDesciptor returned unexpected caller descriptor';
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=63398
   *
   * <p>A strict function's caller should be poisoned only in a way
   * equivalent to an accessor property with a throwing getter and
   * setter.
   *
   * <p>Seen on Safari 5.0.6 through WebKit Nightly r93670
   */
  function test_CANT_HASOWNPROPERTY_CALLER() {
    var answer = void 0;
    try {
      answer = function(){}.hasOwnProperty('caller');
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return 'hasOwnProperty failed with: ' + err;
    }
    if (answer) { return false; }
    return 'strict_function.hasOwnProperty("caller") was false';
  }

  /**
   * Protect an 'in' with a try/catch to workaround a bug in Safari
   * WebKit Nightly Version 5.0.5 (5533.21.1, r89741).
   *
   * <p>See https://bugs.webkit.org/show_bug.cgi?id=63398
   *
   * <p>Notes: We're seeing exactly
   * <blockquote>
   *   New symptom (c): ('caller' in &lt;a bound function&gt;) threw:
   *   TypeError: Cannot access caller property of a strict mode
   *   function<br>
   *   New symptom (c): ('arguments' in &lt;a bound function&gt;)
   *   threw: TypeError: Can't access arguments object of a strict
   *   mode function
   * </blockquote>
   * which means we're skipping both the catch and the finally in
   * {@code has} while hitting the catch in {@code has2}. Further, if
   * we remove one of these finally clauses (forget which) and rerun
   * the example, if we're under the debugger the browser crashes. If
   * we're not, then the TypeError escapes both catches.
   */
  function has(base, name, baseDesc) {
    var result = void 0;
    var finallySkipped = true;
    try {
      result = name in base;
    } catch (err) {
      logger.error('New symptom (a): (\'' +
                   name + '\' in <' + baseDesc + '>) threw: ', err);
      // treat this as a safe absence
      result = false;
      return false;
    } finally {
      finallySkipped = false;
      if (result === void 0) {
        logger.error('New symptom (b): (\'' +
                     name + '\' in <' + baseDesc + '>) failed');
      }
    }
    if (finallySkipped) {
      logger.error('New symptom (e): (\'' +
                   name + '\' in <' + baseDesc +
                   '>) inner finally skipped');
    }
    return !!result;
  }

  function has2(base, name, baseDesc) {
    var result = void 0;
    var finallySkipped = true;
    try {
      result = has(base, name, baseDesc);
    } catch (err) {
      logger.error('New symptom (c): (\'' +
                   name + '\' in <' + baseDesc + '>) threw: ', err);
      // treat this as a safe absence
      result = false;
      return false;
    } finally {
      finallySkipped = false;
      if (result === void 0) {
        logger.error('New symptom (d): (\'' +
                     name + '\' in <' + baseDesc + '>) failed');
      }
    }
    if (finallySkipped) {
      logger.error('New symptom (f): (\'' +
                   name + '\' in <' + baseDesc +
                   '>) outer finally skipped');
    }
    return !!result;
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=63398
   *
   * <p>If this reports a problem in the absence of "New symptom (a)",
   * it means the error thrown by the "in" in {@code has} is skipping
   * past the first layer of "catch" surrounding that "in". This is in
   * fact what we're currently seeing on Safari WebKit Nightly Version
   * 5.0.5 (5533.21.1, r91108).
   */
  function test_CANT_IN_CALLER() {
    var answer = void 0;
    try {
      answer = has2(function(){}, 'caller', 'strict_function');
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return '("caller" in strict_func) failed with: ' + err;
    } finally {}
    if (answer) { return false; }
    return '("caller" in strict_func) was false.';
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=63398
   *
   * <p>If this reports a problem in the absence of "New symptom (a)",
   * it means the error thrown by the "in" in {@code has} is skipping
   * past the first layer of "catch" surrounding that "in". This is in
   * fact what we're currently seeing on Safari WebKit Nightly Version
   * 5.0.5 (5533.21.1, r91108).
   */
  function test_CANT_IN_ARGUMENTS() {
    var answer = void 0;
    try {
      answer = has2(function(){}, 'arguments', 'strict_function');
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return '("arguments" in strict_func) failed with: ' + err;
    } finally {}
    if (answer) { return false; }
    return '("arguments" in strict_func) was false.';
  }

  /**
   * Detects whether strict function violate caller anonymity.
   */
  function test_STRICT_CALLER_NOT_POISONED() {
    if (!has2(strictMapFn, 'caller', 'a strict function')) { return false; }
    function foo(m) { return m.caller; }
    // using Function so it'll be non-strict
    var testfn = Function('m', 'f', 'return m([m], f)[0];');
    var caller;
    try {
      caller = testfn(strictMapFn, foo);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Strict "caller" failed with: ' + err;
    }
    if (testfn === caller) {
      // Seen on IE 9
      return true;
    }
    return 'Unexpected "caller": ' + caller;
  }

  /**
   * Detects whether strict functions are encapsulated.
   */
  function test_STRICT_ARGUMENTS_NOT_POISONED() {
    if (!has2(strictMapFn, 'arguments', 'a strict function')) { return false; }
    function foo(m) { return m.arguments; }
    // using Function so it'll be non-strict
    var testfn = Function('m', 'f', 'return m([m], f)[0];');
    var args;
    try {
      args = testfn(strictMapFn, foo);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Strict "arguments" failed with: ' + err;
    }
    if (args[1] === foo) {
      // Seen on IE 9
      return true;
    }
    return 'Unexpected arguments: ' + arguments;
  }

  /**
   * Detects https://bugzilla.mozilla.org/show_bug.cgi?id=591846 as
   * applied to "caller"
   */
  function test_BUILTIN_LEAKS_CALLER() {
    if (!has2(builtInMapMethod, 'caller', 'a builtin')) { return false; }
    function foo(m) { return m.caller; }
    // using Function so it'll be non-strict
    var testfn = Function('a', 'f', 'return a.map(f)[0];');
    var a = [builtInMapMethod];
    a.map = builtInMapMethod;
    var caller;
    try {
      caller = testfn(a, foo);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Built-in "caller" failed with: ' + err;
    }
    if (null === caller || void 0 === caller) { return false; }
    if (testfn === caller) { return true; }
    return 'Unexpected "caller": ' + caller;
  }

  /**
   * Detects https://bugzilla.mozilla.org/show_bug.cgi?id=591846 as
   * applied to "arguments"
   */
  function test_BUILTIN_LEAKS_ARGUMENTS() {
    if (!has2(builtInMapMethod, 'arguments', 'a builtin')) { return false; }
    function foo(m) { return m.arguments; }
    // using Function so it'll be non-strict
    var testfn = Function('a', 'f', 'return a.map(f)[0];');
    var a = [builtInMapMethod];
    a.map = builtInMapMethod;
    var args;
    try {
      args = testfn(a, foo);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Built-in "arguments" failed with: ' + err;
    }
    if (args === void 0 || args === null) { return false; }
    return true;
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=893
   */
  function test_BOUND_FUNCTION_LEAKS_CALLER() {
    if (!('bind' in Function.prototype)) { return false; }
    function foo() { return bar.caller; }
    var bar = foo.bind({});
    if (!has2(bar, 'caller', 'a bound function')) { return false; }
    // using Function so it'll be non-strict
    var testfn = Function('b', 'return b();');
    var caller;
    try {
      caller = testfn(bar);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Bound function "caller" failed with: ' + err;
    }
    if (caller === void 0 || caller === null) { return false; }
    if (caller === testfn) { return true; }
    return 'Unexpected "caller": ' + caller;
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=893
   */
  function test_BOUND_FUNCTION_LEAKS_ARGUMENTS() {
    if (!('bind' in Function.prototype)) { return false; }
    function foo() { return bar.arguments; }
    var bar = foo.bind({});
    if (!has2(bar, 'arguments', 'a bound function')) { return false; }
    // using Function so it'll be non-strict
    var testfn = Function('b', 'return b();');
    var args;
    try {
      args = testfn(bar);
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Bound function "arguments" failed with: ' + err;
    }
    if (args === void 0 || args === null) { return false; }
    return true;
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=70207
   *
   * <p>After deleting a built-in, the problem is that
   * getOwnPropertyNames still lists the name as present, but it seems
   * absent in all other ways.
   */
  function test_DELETED_BUILTINS_IN_OWN_NAMES() {
    if (!('__defineSetter__' in Object.prototype)) { return false; }
    var desc = Object.getOwnPropertyDescriptor(Object.prototype,
                                               '__defineSetter__');
    try {
      try {
        delete Object.prototype.__defineSetter__;
      } catch (err1) {
        return false;
      }
      var names = Object.getOwnPropertyNames(Object.prototype);
      if (names.indexOf('__defineSetter__') === -1) { return false; }
      if ('__defineSetter__' in Object.prototype) {
        // If it's still there, it bounced back. Which is still a
        // problem, but not the problem we're testing for here.
        return false;
      }
      return true;
    } finally {
      Object.defineProperty(Object.prototype, '__defineSetter__', desc);
    }
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1769
   */
  function test_GETOWNPROPDESC_OF_ITS_OWN_CALLER_FAILS() {
    try {
      Object.getOwnPropertyDescriptor(Object.getOwnPropertyDescriptor,
                                      'caller');
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return 'getOwnPropertyDescriptor threw: ' + err;
    }
    return false;
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=621
   *
   */
  function test_JSON_PARSE_PROTO_CONFUSION() {
    var x;
    try {
      x = JSON.parse('{"__proto__":[]}');
    } catch (err) {
      if (err instanceof TypeError) {
        // We consider it acceptable to fail this case with a
        // TypeError, as our repair below will cause it to do.
        return false;
      }
      return 'JSON.parse failed with: ' + err;
    }
    if (Object.getPrototypeOf(x) !== Object.prototype) { return true; }
    if (Array.isArray(x.__proto__)) { return false; }
    return 'JSON.parse did not set "__proto__" as a regular property';
  }

  /**
   * Detects https://bugs.webkit.org/show_bug.cgi?id=65832
   *
   * <p>On a non-extensible object, it must not be possible to change
   * its internal [[Prototype]] property, i.e., which object it
   * inherits from.
   *
   * TODO(erights): investigate the following:
   * At http://goo.gl/ycCmo Mike Stay says
   * <blockquote>
   * Kevin notes in domado.js that on some versions of FF, event
   * objects switch prototypes when moving between frames. You should
   * probably check out their behavior around freezing and sealing.
   * </blockquote>
   * But I couldn't find it.
   */
  function test_PROTO_NOT_FROZEN() {
    if (!('freeze' in Object)) {
      // Object.freeze and its ilk (including preventExtensions) are
      // still absent on released Android and would
      // cause a bogus bug detection in the following try/catch code.
      return false;
    }
    var x = Object.preventExtensions({});
    if (x.__proto__ === void 0 && !('__proto__' in x)) { return false; }
    var y = {};
    try {
      x.__proto__ = y;
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Mutating __proto__ failed with: ' + err;
    }
    if (y.isPrototypeOf(x)) { return true; }
    return 'Mutating __proto__ neither failed nor succeeded';
  }

  /**
   * Like test_PROTO_NOT_FROZEN but using defineProperty rather than
   * assignment.
   */
  function test_PROTO_REDEFINABLE() {
    if (!('freeze' in Object)) {
      // Object.freeze and its ilk (including preventExtensions) are
      // still absent on released Android and would
      // cause a bogus bug detection in the following try/catch code.
      return false;
    }
    var x = Object.preventExtensions({});
    if (x.__proto__ === void 0 && !('__proto__' in x)) { return false; }
    var y = {};
    try {
      Object.defineProperty(x, '__proto__', { value: y });
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Defining __proto__ failed with: ' + err;
    }
    if (y.isPrototypeOf(x)) { return true; }
    return 'Defining __proto__ neither failed nor succeeded';
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1624
   *
   * <p>Both a direct strict eval operator and an indirect strict eval
   * function must not leak top level declarations in the string being
   * evaluated into their containing context.
   */
  function test_STRICT_EVAL_LEAKS_GLOBALS() {
    (1,eval)('"use strict"; var ___global_test_variable___ = 88;');
    if ('___global_test_variable___' in global) {
      delete global.___global_test_variable___;
      return true;
    }
    return false;
  }

  /**
   * Detects http://code.google.com/p/v8/issues/detail?id=1645
   */
  function test_PARSEINT_STILL_PARSING_OCTAL() {
    var n = parseInt('010');
    if (n === 10) { return false; }
    if (n === 8)  { return true; }
    return 'parseInt("010") returned ' + n;
  }

  /**
   * Detects https://bugzilla.mozilla.org/show_bug.cgi?id=695577
   *
   * <p>When E4X syntax is accepted in strict code, then without
   * parsing, we cannot prevent untrusted code from expressing E4X
   * literals and so obtaining access to shared E4X prototypes,
   * despite the absence of these prototypes from our whitelist. While
   * https://bugzilla.mozilla.org/show_bug.cgi?id=695579 is also
   * open, we cannot even repair the situation, leading to unpluggable
   * capability leaks. However, we do not test for this additional
   * problem, since E4X is such a can of worms that 695577 is adequate
   * by itself for us to judge this platform to be insecurable without
   * parsing.
   */
  function test_STRICT_E4X_LITERALS_ALLOWED() {
    var x;
    try {
      x = eval('"use strict";(<foo/>);');
    } catch (err) {
      if (err instanceof SyntaxError) { return false; }
      return 'E4X test failed with: ' + err;
    }
    if (x !== void 0) { return true; }
    return 'E4X literal expression had no value';
  }

  /**
   * Detects whether assignment can override an inherited
   * non-writable, non-configurable data property.
   *
   * <p>According to ES5.1, assignment should not be able to do so,
   * which is unfortunate for SES, as the tamperProof function must
   * kludge expensively to ensure that legacy assignments that don't
   * violate best practices continue to work. Ironically, on platforms
   * in which this bug is present, tamperProof can just be cheaply
   * equivalent to Object.freeze.
   */
  function test_ASSIGN_CAN_OVERRIDE_FROZEN() {
    var x = Object.freeze({foo: 88});
    var y = Object.create(x);
    try {
      y.foo = 99;
    } catch (err) {
      if (err instanceof TypeError) { return false; }
      return 'Override failed with: ' + err;
    }
    if (y.foo === 99) { return true; }
    if (y.foo === 88) { return 'Override failed silently'; }
    return 'Unexpected override outcome: ' + y.foo;
  }

  /**
   *
   */
  function test_CANT_REDEFINE_NAN_TO_ITSELF() {
    var descNaN = Object.getOwnPropertyDescriptor(global, 'NaN');
    try {
      Object.defineProperty(global, 'NaN', descNaN);
    } catch (err) {
      if (err instanceof TypeError) { return true; }
      return 'defineProperty of NaN failed with: ' + err;
    }
    return false;
  }

  /**
   * These are all the own properties that appear on Error instances
   * on various ES5 platforms as of this writing.
   *
   * <p>Due to browser bugs, some of these are absent from
   * getOwnPropertyNames (gopn). TODO(erights): File bugs with various
   * browser makers for any own properties that we know to be present
   * but not reported by gopn.
   *
   * <p>TODO(erights): do intelligence with the various browser
   * implementors to find out what other properties are provided by
   * their implementation but absent from gopn, whether on Errors or
   * anything else. Every one of these are potentially fatal to our
   * security until we can examine these.
   *
   * <p>The source form is a list rather than a map so that we can list a
   * name like "message" for each browser section we think it goes in.
   *
   * <p>We thank the following people, projects, and websites for
   * providing some useful intelligence of what property names we
   * should suspect:<ul>
   * <li><a href="http://stacktracejs.org">stacktracejs.org</a>
   * <li>TODO(erights): find message on es-discuss list re
   * "   stack". credit author.
   * </ul>
   */
  var errorInstanceWhitelist = [
    // at least Chrome 16
    'arguments',
    'message',
    'stack',
    'type',

    // at least FF 9
    'fileName',
    'lineNumber',
    'message',
    'stack',

    // at least Safari, WebKit 5.1
    'line',
    'message',
    'sourceId',
    'sourceURL',

    // at least IE 10 preview 2
    'description',
    'message',
    'number',

    // at least Opera 11.60
    'message',
    'stack',
    'stacktrace'
  ];

  var errorInstanceBlacklist = [
    // seen in a Firebug on FF
    'category',
    'context',
    'href',
    'lineNo',
    'msgId',
    'source',
    'trace',
    'correctSourcePoint',
    'correctWithStackTrace',
    'getSourceLine',
    'resetSource'
  ];

  /** Return a fresh one so client can mutate freely */
  function freshErrorInstanceWhiteMap() {
    var result = Object.create(null);
    strictForEachFn(errorInstanceWhitelist, function(name) {
      // We cannot yet use StringMap so do it manually
      // We do this naively here assuming we don't need to worry about
      // __proto__
      result[name] = true;
    });
    return result;
  }

  function freshHiddenPropertyCandidates() {
    var result = freshErrorInstanceWhiteMap();
    strictForEachFn(errorInstanceBlacklist, function(name) {
      result[name] = true;
    });
    return result;
  }

  /**
   * Do Error instances on thos platform carry own properties that we
   * haven't yet examined and determined to be SES-safe?
   *
   * <p>A new property should only be added to the
   * errorInstanceWhitelist after inspecting the consequences of that
   * property to determine that it does not compromise SES safety. If
   * some platform maker does add an Error own property that does
   * compromise SES safety, that might be a severe problem, if we
   * can't find a way to deny untrusted code access to that property.
   */
  function test_UNEXPECTED_ERROR_PROPERTIES() {
    var errs = [new Error('e1')];
    try { null.foo = 3; } catch (err) { errs.push(err); }
    var result = false;

    var approvedNames = freshErrorInstanceWhiteMap();

    strictForEachFn(errs, function(err) {
      strictForEachFn(Object.getOwnPropertyNames(err), function(name) {
         if (!(name in approvedNames)) {
           result = 'Unexpected error instance property: ' + name;
           // would be good to terminate early
         }
      });
    });
    return result;
  }

  /**
   *
   */
  function test_GET_OWN_PROPERTY_NAME_LIES() {
    var gopn = Object.getOwnPropertyNames;
    var gopd = Object.getOwnPropertyDescriptor;

    var suspects = [new Error('e1')];
    try { null.foo = 3; } catch (err) { suspects.push(err); }

    var unreported = Object.create(null);

    strictForEachFn(suspects, function(suspect) {
      var candidates = freshHiddenPropertyCandidates();
      strictForEachFn(gopn(suspect), function(name) {
        // Delete the candidates that are reported
        delete candidates[name];
      });
      strictForEachFn(gopn(candidates), function(name) {
        if (!gopd(suspect, name)) {
          // Delete the candidates that are not own properties
          delete candidates[name];
        }
      });
      strictForEachFn(gopn(candidates), function(name) {
        unreported[name] = true;
      });
    });

    var unreportedNames = gopn(unreported);
    if (unreportedNames.length === 0) { return false; }
    return 'Error own properties unreported by getOwnPropertyNames: ' +
      unreportedNames.sort().join(',');
  }


  ////////////////////// Repairs /////////////////////
  //
  // Each repair_NAME function exists primarily to repair the problem
  // indicated by the corresponding test_NAME function. But other test
  // failures can still trigger a given repair.


  var call = Function.prototype.call;
  var apply = Function.prototype.apply;

  var hop = Object.prototype.hasOwnProperty;
  var slice = Array.prototype.slice;
  var concat = Array.prototype.concat;
  var getPrototypeOf = Object.getPrototypeOf;

  function patchMissingProp(base, name, missingFunc) {
    if (!(name in base)) {
      Object.defineProperty(base, name, {
        value: missingFunc,
        writable: true,
        enumerable: false,
        configurable: true
      });
    }
  }

  function repair_MISSING_FREEZE_ETC() {
    patchMissingProp(Object, 'freeze',
                     function fakeFreeze(obj) { return obj; });
    patchMissingProp(Object, 'seal',
                     function fakeSeal(obj) { return obj; });
    patchMissingProp(Object, 'preventExtensions',
                     function fakePreventExtensions(obj) { return obj; });
    patchMissingProp(Object, 'isFrozen',
                     function fakeIsFrozen(obj) { return false; });
    patchMissingProp(Object, 'isSealed',
                     function fakeIsSealed(obj) { return false; });
    patchMissingProp(Object, 'isExtensible',
                     function fakeIsExtensible(obj) { return true; });
  }

  function repair_FUNCTION_PROTOTYPE_DESCRIPTOR_LIES() {
    var unsafeDefProp = Object.defineProperty;
    function repairedDefineProperty(base, name, desc) {
      if (typeof base === 'function' &&
          name === 'prototype' &&
          'value' in desc) {
        try {
          base.prototype = desc.value;
        } catch (err) {
          logger.warn('prototype fixup failed', err);
        }
      }
      return unsafeDefProp(base, name, desc);
    }
    Object.defineProperty(Object, 'defineProperty', {
      value: repairedDefineProperty
    });
  }

  function repair_MISSING_CALLEE_DESCRIPTOR() {
    var realGOPN = Object.getOwnPropertyNames;
    Object.defineProperty(Object, 'getOwnPropertyNames', {
      value: function calleeFix(base) {
        var result = realGOPN(base);
        if (typeof base === 'function') {
          var i = result.indexOf('callee');
          if (i >= 0 && !hop.call(base, 'callee')) {
            result.splice(i, 1);
          }
        }
        return result;
      }
    });
  }

  function repair_REGEXP_CANT_BE_NEUTERED() {
    var UnsafeRegExp = RegExp;
    var FakeRegExp = function RegExpWrapper(pattern, flags) {
      switch (arguments.length) {
        case 0: {
          return UnsafeRegExp();
        }
        case 1: {
          return UnsafeRegExp(pattern);
        }
        default: {
          return UnsafeRegExp(pattern, flags);
        }
      }
    };
    Object.defineProperty(FakeRegExp, 'prototype', {
      value: UnsafeRegExp.prototype
    });
    Object.defineProperty(FakeRegExp.prototype, 'constructor', {
      value: FakeRegExp
    });
    RegExp = FakeRegExp;
  }

  function repair_REGEXP_TEST_EXEC_UNSAFE() {
    var unsafeRegExpExec = RegExp.prototype.exec;
    var unsafeRegExpTest = RegExp.prototype.test;

    Object.defineProperty(RegExp.prototype, 'exec', {
      value: function fakeExec(specimen) {
        return unsafeRegExpExec.call(this, String(specimen));
      }
    });
    Object.defineProperty(RegExp.prototype, 'test', {
      value: function fakeTest(specimen) {
        return unsafeRegExpTest.call(this, String(specimen));
      }
    });
  }

  function repair_MISSING_BIND() {

    /**
     * Actual bound functions are not supposed to have a prototype, and
     * are supposed to curry over both the [[Call]] and [[Construct]]
     * behavior of their original function. However, in ES5,
     * functions written in JavaScript cannot avoid having a 'prototype'
     * property, and cannot reliably distinguish between being called as
     * a function vs as a constructor, i.e., by {@code new}.
     *
     * <p>Since the repair_MISSING_BIND emulation produces a bound
     * function written in JavaScript, it cannot faithfully emulate
     * either the lack of a 'prototype' property nor the currying of the
     * [[Construct]] behavior. So instead, we use BOGUS_BOUND_PROTOTYPE
     * to reliably give an error for attempts to {@code new} a bound
     * function. Since we cannot avoid exposing BOGUS_BOUND_PROTOTYPE
     * itself, it is possible to pass in a this-binding which inherits
     * from it without using {@code new}, which will also trigger our
     * error case. Whether this latter error is appropriate or not, it
     * still fails safe.
     *
     * <p>By making the 'prototype' of the bound function be the same as
     * the current {@code thisFunc.prototype}, we could have emulated
     * the [[HasInstance]] property of bound functions. But even this
     * would have been inaccurate, since we would be unable to track
     * changes to the original {@code thisFunc.prototype}. (We cannot
     * make 'prototype' into an accessor to do this tracking, since
     * 'prototype' on a function written in JavaScript is
     * non-configurable.) And this one partially faithful emulation
     * would have come at the cost of no longer being able to reasonably
     * detect construction, in order to safely reject it.
     */
    var BOGUS_BOUND_PROTOTYPE = {
      toString: function BBPToString() { return 'bogus bound prototype'; }
    };
    rememberToTamperProof(BOGUS_BOUND_PROTOTYPE);
    BOGUS_BOUND_PROTOTYPE.toString.prototype = null;
    rememberToTamperProof(BOGUS_BOUND_PROTOTYPE.toString);

    var defProp = Object.defineProperty;
    defProp(Function.prototype, 'bind', {
      value: function fakeBind(self, var_args) {
        var thisFunc = this;
        var leftArgs = slice.call(arguments, 1);
        function funcBound(var_args) {
          if (this === Object(this) &&
              getPrototypeOf(this) === BOGUS_BOUND_PROTOTYPE) {
            throw new TypeError(
              'Cannot emulate "new" on pseudo-bound function.');
          }
          var args = concat.call(leftArgs, slice.call(arguments, 0));
          return apply.call(thisFunc, self, args);
        }
        defProp(funcBound, 'prototype', {
          value: BOGUS_BOUND_PROTOTYPE,
          writable: false,
          configurable: false
        });
        return funcBound;
      },
      writable: true,
      enumerable: false,
      configurable: true
    });
  }

  /**
   * Return a function suitable for using as a forEach argument on a
   * list of method names, where that function will monkey patch each
   * of these names methods on {@code constr.prototype} so that they
   * can't be called on a {@code constr.prototype} itself even across
   * frames.
   *
   * <p>This only works when {@code constr} corresponds to an internal
   * [[Class]] property whose value is {@code classString}. To test
   * for {@code constr.prototype} cross-frame, we observe that for all
   * objects of this [[Class]], only the prototypes directly inherit
   * from an object that does not have this [[Class]].
   */
  function makeMutableProtoPatcher(constr, classString) {
    var proto = constr.prototype;
    var baseToString = objToString.call(proto);
    if (baseToString !== '[object ' + classString + ']') {
      throw new TypeError('unexpected: ' + baseToString);
    }
    var grandProto = getPrototypeOf(proto);
    var grandBaseToString = objToString.call(grandProto);
    if (grandBaseToString === '[object ' + classString + ']') {
      throw new TypeError('malformed inheritance: ' + classString);
    }
    if (grandProto !== Object.prototype) {
      logger.log('unexpected inheritance: ' + classString);
    }
    function mutableProtoPatcher(name) {
      if (!hop.call(proto, name)) { return; }
      var originalMethod = proto[name];
      function replacement(var_args) {
        var parent = getPrototypeOf(this);
        if (parent !== proto) {
          // In the typical case, parent === proto, so the above test
          // lets the typical case succeed quickly.
          // Note that, even if parent === proto, that does not
          // necessarily mean that the method application will
          // succeed, since, for example, a non-Date can still inherit
          // from Date.prototype. However, in such cases, the built-in
          // method application will fail on its own without our help.
          if (objToString.call(parent) !== baseToString) {
            // As above, === baseToString does not necessarily mean
            // success, but the built-in failure again would not need
            // our help.
            var thisToString = objToString.call(this);
            if (thisToString === baseToString) {
              throw new TypeError('May not mutate internal state of a ' +
                                  classString + '.prototype');
            } else {
              throw new TypeError('Unexpected: ' + thisToString);
            }
          }
        }
        return originalMethod.apply(this, arguments);
      }
      Object.defineProperty(proto, name, { value: replacement });
    }
    return mutableProtoPatcher;
  }


  function repair_MUTABLE_DATE_PROTO() {
    // Note: coordinate this list with maintenance of whitelist.js
    ['setYear',
     'setTime',
     'setFullYear',
     'setUTCFullYear',
     'setMonth',
     'setUTCMonth',
     'setDate',
     'setUTCDate',
     'setHours',
     'setUTCHours',
     'setMinutes',
     'setUTCMinutes',
     'setSeconds',
     'setUTCSeconds',
     'setMilliseconds',
     'setUTCMilliseconds'].forEach(makeMutableProtoPatcher(Date, 'Date'));
  }

  function repair_MUTABLE_WEAKMAP_PROTO() {
    // Note: coordinate this list with maintanence of whitelist.js
    ['set',
     'delete'].forEach(makeMutableProtoPatcher(WeakMap, 'WeakMap'));
  }

  function repair_NEED_TO_WRAP_FOREACH() {
    var forEach = Array.prototype.forEach;
    Object.defineProperty(Array.prototype, 'forEach', {
      value: function forEachWrapper(callbackfn, opt_thisArg) {
        return forEach.apply(this, arguments);
      }
    });
  }


  function repair_NEEDS_DUMMY_SETTER() {
    var defProp = Object.defineProperty;
    var gopd = Object.getOwnPropertyDescriptor;

    function dummySetter(newValue) {
      throw new TypeError('no setter for assigning: ' + newValue);
    }
    dummySetter.prototype = null;
    rememberToTamperProof(dummySetter);

    defProp(Object, 'defineProperty', {
      value: function setSetterDefProp(base, name, desc) {
        if (typeof desc.get === 'function' && desc.set === void 0) {
          var oldDesc = gopd(base, name);
          if (oldDesc) {
            var testBase = {};
            defProp(testBase, name, oldDesc);
            defProp(testBase, name, desc);
            desc = gopd(testBase, name);
            if (desc.set === void 0) { desc.set = dummySetter; }
          } else {
            if (objToString.call(base) === '[object HTMLFormElement]') {
              // This repair was triggering bug
              // http://code.google.com/p/chromium/issues/detail?id=94666
              // on Chrome, causing
              // http://code.google.com/p/google-caja/issues/detail?id=1401
              // so if base is an HTMLFormElement we skip this
              // fix. Since this repair and this situation are both
              // Chrome only, it is ok that we're conditioning this on
              // the unspecified [[Class]] value of base.
              //
              // To avoid the further bug identified at Comment 2
              // http://code.google.com/p/chromium/issues/detail?id=94666#c2
              // We also have to reconstruct the requested desc so that
              // the setter is absent. This is why we additionally
              // condition this special case on the absence of an own
              // name property on base.
              var desc2 = { get: desc.get };
              if ('enumerable' in desc) {
                desc2.enumerable = desc.enumerable;
              }
              if ('configurable' in desc) {
                desc2.configurable = desc.configurable;
              }
              var result = defProp(base, name, desc2);
              var newDesc = gopd(base, name);
              if (newDesc.get === desc.get) {
                return result;
              }
            }
            desc.set = dummySetter;
          }
        }
        return defProp(base, name, desc);
      }
    });
    NEEDS_DUMMY_SETTER_repaired = true;
  }


  function repair_ACCESSORS_INHERIT_AS_OWN() {
    // restrict these
    var defProp = Object.defineProperty;
    var freeze = Object.freeze;
    var seal = Object.seal;

    // preserve illusion
    var gopn = Object.getOwnPropertyNames;
    var gopd = Object.getOwnPropertyDescriptor;

    var complaint = 'Workaround for ' +
      'https://bugzilla.mozilla.org/show_bug.cgi?id=637994 ' +
      ' prohibits enumerable non-configurable accessor properties.';

    function isBadAccessor(derived, name) {
      var desc = gopd(derived, name);
      if (!desc || !('get' in desc)) { return false; }
      var base = getPrototypeOf(derived);
      if (!base) { return false; }
      var superDesc = gopd(base, name);
      if (!superDesc || !('get' in superDesc)) { return false; }
      return (desc.get &&
              !desc.configurable && !superDesc.configurable &&
              desc.get === superDesc.get &&
              desc.set === superDesc.set &&
              desc.enumerable === superDesc.enumerable);
    }

    defProp(Object, 'defineProperty', {
      value: function definePropertyWrapper(base, name, desc) {
        var oldDesc = gopd(base, name);
        var testBase = {};
        if (oldDesc && !isBadAccessor(base, name)) {
          defProp(testBase, name, oldDesc);
        }
        defProp(testBase, name, desc);
        var fullDesc = gopd(testBase, name);
         if ('get' in fullDesc &&
            fullDesc.enumerable &&
            !fullDesc.configurable) {
          logger.warn(complaint);
          throw new TypeError(complaint
              + " (Object: " + base + " Property: " + name + ")");
        }
        return defProp(base, name, fullDesc);
      }
    });

    function ensureSealable(base) {
      gopn(base).forEach(function(name) {
        var desc = gopd(base, name);
        if ('get' in desc && desc.enumerable) {
          if (!desc.configurable) {
            logger.error('New symptom: ' +
                         '"' + name + '" already non-configurable');
          }
          logger.warn(complaint);
          throw new TypeError(complaint + " (During sealing. Object: "
              + base + " Property: " + name + ")");
        }
      });
    }

    defProp(Object, 'freeze', {
      value: function freezeWrapper(base) {
        ensureSealable(base);
        return freeze(base);
      }
    });

    defProp(Object, 'seal', {
      value: function sealWrapper(base) {
        ensureSealable(base);
        return seal(base);
      }
    });

    defProp(Object.prototype, 'hasOwnProperty', {
      value: function hasOwnPropertyWrapper(name) {
        return hop.call(this, name) && !isBadAccessor(this, name);
      }
    });

    defProp(Object, 'getOwnPropertyDescriptor', {
      value: function getOwnPropertyDescriptorWrapper(base, name) {
        if (isBadAccessor(base, name)) { return void 0; }
        return gopd(base, name);
      }
    });

    defProp(Object, 'getOwnPropertyNames', {
      value: function getOwnPropertyNamesWrapper(base) {
        return gopn(base).filter(function(name) {
          return !isBadAccessor(base, name);
        });
      }
    });
  }

  function repair_SORT_LEAKS_GLOBAL() {
    var unsafeSort = Array.prototype.sort;
    function sortWrapper(opt_comparefn) {
      function comparefnWrapper(x, y) {
        return opt_comparefn(x, y);
      }
      if (arguments.length === 0) {
        return unsafeSort.call(this);
      } else {
        return unsafeSort.call(this, comparefnWrapper);
      }
    }
    Object.defineProperty(Array.prototype, 'sort', {
      value: sortWrapper
    });
  }

  function repair_REPLACE_LEAKS_GLOBAL() {
    var unsafeReplace = String.prototype.replace;
    function replaceWrapper(searchValue, replaceValue) {
      var safeReplaceValue = replaceValue;
      function replaceValueWrapper(m1, m2, m3) {
        return replaceValue(m1, m2, m3);
      }
      if (typeof replaceValue === 'function') {
        safeReplaceValue = replaceValueWrapper;
      }
      return unsafeReplace.call(this, searchValue, safeReplaceValue);
    }
    Object.defineProperty(String.prototype, 'replace', {
      value: replaceWrapper
    });
  }

  function repair_CANT_GOPD_CALLER() {
    var unsafeGOPD = Object.getOwnPropertyDescriptor;
    function gopdWrapper(base, name) {
      try {
        return unsafeGOPD(base, name);
      } catch (err) {
        if (err instanceof TypeError &&
            typeof base === 'function' &&
            (name === 'caller' || name === 'arguments')) {
          return (function(message) {
             function fakePoison() { throw new TypeError(message); }
             fakePoison.prototype = null;
             return {
               get: fakePoison,
               set: fakePoison,
               enumerable: false,
               configurable: false
             };
           })(err.message);
        }
        throw err;
      }
    }
    Object.defineProperty(Object, 'getOwnPropertyDescriptor', {
      value: gopdWrapper
    });
  }

  function repair_CANT_HASOWNPROPERTY_CALLER() {
    Object.defineProperty(Object.prototype, 'hasOwnProperty', {
      value: function hopWrapper(name) {
        return !!Object.getOwnPropertyDescriptor(this, name);
      }
    });
  }

  function makeHarmless(magicName, func, path) {
    function poison() {
      throw new TypeError('Cannot access property ' + path);
    }
    poison.prototype = null;
    var desc = Object.getOwnPropertyDescriptor(func, magicName);
    if ((!desc && Object.isExtensible(func)) || desc.configurable) {
      try {
        Object.defineProperty(func, magicName, {
          get: poison,
          set: poison,
          configurable: false
        });
      } catch (cantPoisonErr) {
        return 'Poisoning failed with ' + cantPoisonErr;
      }
      desc = Object.getOwnPropertyDescriptor(func, magicName);
      if (desc &&
          desc.get === poison &&
          desc.set === poison &&
          !desc.configurable) {
        return 'Apparently poisoned';
      }
      return 'Not poisoned';
    }
    if ('get' in desc || 'set' in desc) {
      return 'Apparently safe';
    }
    try {
      Object.defineProperty(func, magicName, {
        value: desc.value === null ? null : void 0,
        writable: false,
        configurable: false
      });
    } catch (cantFreezeHarmlessErr) {
      return 'Freezing harmless failed with ' + cantFreezeHarmlessErr;
    }
    desc = Object.getOwnPropertyDescriptor(func, magicName);
    if (desc &&
        (desc.value === null || desc.value === void 0) &&
        !desc.writable &&
        !desc.configurable) {
      return 'Apparently frozen harmless';
    }
    return 'Did not freeze harmless';
  }

  function repair_BUILTIN_LEAKS_CALLER() {
    // The call to .bind as a method here is fine since it happens
    // after all repairs which might fix .bind and before any
    // untrusted code runs.
    ses.makeCallerHarmless = makeHarmless.bind(void 0, 'caller');
    //logger.info(ses.makeCallerHarmless(builtInMapMethod));
  }

  function repair_BUILTIN_LEAKS_ARGUMENTS() {
    // The call to .bind as a method here is fine since it happens
    // after all repairs which might fix .bind and before any
    // untrusted code runs.
    ses.makeArgumentsHarmless = makeHarmless.bind(void 0, 'arguments');
    //logger.info(ses.makeArgumentsHarmless(builtInMapMethod));
  }

  function repair_DELETED_BUILTINS_IN_OWN_NAMES() {
    var realGOPN = Object.getOwnPropertyNames;
    var repairedHop = Object.prototype.hasOwnProperty;
    function getOnlyRealOwnPropertyNames(base) {
      return realGOPN(base).filter(function(name) {
        return repairedHop.call(base, name);
      });
    }
    Object.defineProperty(Object, 'getOwnPropertyNames', {
      value: getOnlyRealOwnPropertyNames
    });
  }

  function repair_GETOWNPROPDESC_OF_ITS_OWN_CALLER_FAILS() {
    var realGOPD = Object.getOwnPropertyDescriptor;
    function GOPDWrapper(base, name) {
      return realGOPD(base, name);
    }
    Object.defineProperty(Object, 'getOwnPropertyDescriptor', {
      value: GOPDWrapper
    });
  }

  function repair_JSON_PARSE_PROTO_CONFUSION() {
    var unsafeParse = JSON.parse;
    function validate(plainJSON) {
      if (plainJSON !== Object(plainJSON)) {
        // If we were trying to do a full validation, we would
        // validate that it is not NaN, Infinity, -Infinity, or
        // (if nested) undefined. However, we are currently only
        // trying to repair
        // http://code.google.com/p/v8/issues/detail?id=621
        // That's why this special case validate function is private
        // to this repair.
        return;
      }
      var proto = getPrototypeOf(plainJSON);
      if (proto !== Object.prototype && proto !== Array.prototype) {
        throw new TypeError(
          'Parse resulted in invalid JSON. ' +
            'See http://code.google.com/p/v8/issues/detail?id=621');
      }
      Object.keys(plainJSON).forEach(function(key) {
        validate(plainJSON[key]);
      });
    }
    Object.defineProperty(JSON, 'parse', {
      value: function parseWrapper(text, opt_reviver) {
        var result = unsafeParse(text);
        validate(result);
        if (opt_reviver) {
          return unsafeParse(text, opt_reviver);
        } else {
          return result;
        }
      },
      writable: true,
      enumerable: false,
      configurable: true
    });
  }

  function repair_PARSEINT_STILL_PARSING_OCTAL() {
    var badParseInt = parseInt;
    function goodParseInt(n, radix) {
      n = '' + n;
      // This turns an undefined radix into a NaN but is ok since NaN
      // is treated as undefined by badParseInt
      radix = +radix;
      var isHexOrOctal = /^\s*[+-]?\s*0(x?)/.exec(n);
      var isOct = isHexOrOctal ? isHexOrOctal[1] !== 'x' : false;

      if (isOct && (radix !== radix || 0 === radix)) {
        return badParseInt(n, 10);
      }
      return badParseInt(n, radix);
    }
    parseInt = goodParseInt;
  }

  function repair_ASSIGN_CAN_OVERRIDE_FROZEN() {
    makeTamperProof = function simpleMakeTamperProof() {
      return Object.freeze;
    };
  }

  function repair_CANT_REDEFINE_NAN_TO_ITSELF() {
    var defProp = Object.defineProperty;
    // 'value' handled separately
    var attrs = ['writable', 'get', 'set', 'enumerable', 'configurable'];

    defProp(Object, 'defineProperty', {
      value: function(base, name, desc) {
        try {
          return defProp(base, name, desc);
        } catch (err) {
          var oldDesc = Object.getOwnPropertyDescriptor(base, name);
          for (var i = 0, len = attrs.length; i < len; i++) {
            var attr = attrs[i];
            if (attr in desc && desc[attr] !== oldDesc[attr]) { throw err; }
          }
          if (!('value' in desc) || is(desc.value, oldDesc.value)) {
            return base;
          }
          throw err;
        }
      }
    });
  }


  ////////////////////// Kludge Records /////////////////////
  //
  // Each kludge record has a <dl>
  //   <dt>description:</dt>
  //     <dd>a string describing the problem</dd>
  //   <dt>test:</dt>
  //     <dd>a predicate testing for the presence of the problem</dd>
  //   <dt>repair:</dt>
  //     <dd>a function which attempts repair, or undefined if no
  //         repair is attempted for this problem</dd>
  //   <dt>preSeverity:</dt>
  //     <dd>an enum (see below) indicating the level of severity of
  //         this problem if unrepaired. Or, if !canRepair, then
  //         the severity whether or not repaired.</dd>
  //   <dt>canRepair:</dt>
  //     <dd>a boolean indicating "if the repair exists and the test
  //         subsequently does not detect a problem, are we now ok?"</dd>
  //   <dt>urls:</dt>
  //     <dd>a list of URL strings, each of which points at a page
  //         relevant for documenting or tracking the bug in
  //         question. These are typically into bug-threads in issue
  //         trackers for the various browsers.</dd>
  //   <dt>sections:</dt>
  //     <dd>a list of strings, each of which is a relevant ES5.1
  //         section number.</dd>
  //   <dt>tests:</dt>
  //     <dd>a list of strings, each of which is the name of a
  //         relevant test262 or sputnik test case.</dd>
  // </dl>
  // These kludge records are the meta-data driving the testing and
  // repairing.

  var severities = ses.severities;
  var statuses = ses.statuses;

  /**
   * First test whether the platform can even support our repair
   * attempts.
   */
  var baseKludges = [
    {
      description: 'Missing getOwnPropertyNames',
      test: test_MISSING_GETOWNPROPNAMES,
      repair: void 0,
      preSeverity: severities.NOT_SUPPORTED,
      canRepair: false,
      urls: [],
      sections: ['15.2.3.4'],
      tests: ['15.2.3.4-0-1']
    }
  ];

  /**
   * Run these only if baseKludges report success.
   */
  var supportedKludges = [
    {
      description: 'Global object leaks from global function calls',
      test: test_GLOBAL_LEAKS_FROM_GLOBAL_FUNCTION_CALLS,
      repair: void 0,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: false,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=64250'],
      sections: ['10.2.1.2', '10.2.1.2.6'],
      tests: ['10.4.3-1-8gs']
    },
    {
      description: 'Global object leaks from anonymous function calls',
      test: test_GLOBAL_LEAKS_FROM_ANON_FUNCTION_CALLS,
      repair: void 0,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: false,
      urls: [],
      sections: ['10.4.3'],
      tests: ['S10.4.3_A1']
    },
    {
      description: 'Global leaks through strict this',
      test: test_GLOBAL_LEAKS_FROM_STRICT_THIS,
      repair: void 0,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: false,
      urls: [],
      sections: ['10.4.3'],
      tests: ['10.4.3-1-8gs', '10.4.3-1-8-s']
    },
    {
      description: 'Global object leaks from built-in methods',
      test: test_GLOBAL_LEAKS_FROM_BUILTINS,
      repair: void 0,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: false,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=51097',
             'https://bugs.webkit.org/show_bug.cgi?id=58338',
             'http://code.google.com/p/v8/issues/detail?id=1437',
             'https://connect.microsoft.com/IE/feedback/details/' +
               '685430/global-object-leaks-from-built-in-methods'],
      sections: ['15.2.4.4'],
      tests: ['S15.2.4.4_A14']
    },
    {
      description: 'Global object leaks from globally called built-in methods',
      test: test_GLOBAL_LEAKS_FROM_GLOBALLY_CALLED_BUILTINS,
      repair: void 0,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: false,
      urls: [],
      sections: ['10.2.1.2', '10.2.1.2.6', '15.2.4.4'],
      tests: ['S15.2.4.4_A15']
    },
    {
      description: 'Object.freeze is missing',
      test: test_MISSING_FREEZE_ETC,
      repair: repair_MISSING_FREEZE_ETC,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: false,           // repair for development, not safety
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=55736'],
      sections: ['15.2.3.9'],
      tests: ['15.2.3.9-0-1']
    },
    {
      description: 'A function.prototype\'s descriptor lies',
      test: test_FUNCTION_PROTOTYPE_DESCRIPTOR_LIES,
      repair: repair_FUNCTION_PROTOTYPE_DESCRIPTOR_LIES,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1530',
             'http://code.google.com/p/v8/issues/detail?id=1570'],
      sections: ['15.2.3.3', '15.2.3.6', '15.3.5.2'],
      tests: ['S15.3.3.1_A4']
    },
    {
      description: 'Phantom callee on strict functions',
      test: test_MISSING_CALLEE_DESCRIPTOR,
      repair: repair_MISSING_CALLEE_DESCRIPTOR,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=55537'],
      sections: ['15.2.3.4'],
      tests: ['S15.2.3.4_A1_T1']
    },
    {
      description: 'Strict delete returned false rather than throwing',
      test: test_STRICT_DELETE_RETURNS_FALSE,
      repair: void 0,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: false,
      urls: ['https://connect.microsoft.com/IE/feedback/details/' +
               '685432/strict-delete-sometimes-returns-false-' +
               'rather-than-throwing'],
      sections: ['11.4.1'],
      tests: ['S11.4.1_A5']
    },
    {
      description: 'Non-deletable RegExp statics are a' +
        ' global communication channel',
      test: test_REGEXP_CANT_BE_NEUTERED,
      repair: repair_REGEXP_CANT_BE_NEUTERED,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['https://bugzilla.mozilla.org/show_bug.cgi?id=591846',
             'http://wiki.ecmascript.org/doku.php?id=' +
               'conventions:make_non-standard_properties_configurable',
             'https://connect.microsoft.com/IE/feedback/details/' +
               '685439/non-deletable-regexp-statics-are-a-global-' +
               'communication-channel'],
      sections: ['11.4.1'],
      tests: ['S11.4.1_A5']
    },
    {
      description: 'RegExp.exec leaks match globally',
      test: test_REGEXP_TEST_EXEC_UNSAFE,
      repair: repair_REGEXP_TEST_EXEC_UNSAFE,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1393',
             'http://code.google.com/p/chromium/issues/detail?id=75740',
             'https://bugzilla.mozilla.org/show_bug.cgi?id=635017',
             'http://code.google.com/p/google-caja/issues/detail?id=528'],
      sections: ['15.10.6.2'],
      tests: ['S15.10.6.2_A12']
    },
    {
      description: 'Function.prototype.bind is missing',
      test: test_MISSING_BIND,
      repair: repair_MISSING_BIND,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=26382',
             'https://bugs.webkit.org/show_bug.cgi?id=42371'],
      sections: ['15.3.4.5'],
      tests: ['S15.3.4.5_A3']
    },
    {
      description: 'Function.prototype.bind calls .apply rather than [[Call]]',
      test: test_BIND_CALLS_APPLY,
      repair: repair_MISSING_BIND,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=892',
             'http://code.google.com/p/v8/issues/detail?id=828'],
      sections: ['15.3.4.5.1'],
      tests: ['S15.3.4.5_A4']
    },
    {
      description: 'Function.prototype.bind does not curry construction',
      test: test_BIND_CANT_CURRY_NEW,
      repair: void 0, // JS-based repair essentially impossible
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: false,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=26382#c29'],
      sections: ['15.3.4.5.2'],
      tests: ['S15.3.4.5_A5']
    },
    {
      description: 'Date.prototype is a global communication channel',
      test: test_MUTABLE_DATE_PROTO,
      repair: repair_MUTABLE_DATE_PROTO,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['http://code.google.com/p/google-caja/issues/detail?id=1362'],
      sections: ['15.9.5'],
      tests: []
    },
    {
      description: 'WeakMap.prototype is a global communication channel',
      test: test_MUTABLE_WEAKMAP_PROTO,
      repair: repair_MUTABLE_WEAKMAP_PROTO,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['https://bugzilla.mozilla.org/show_bug.cgi?id=656828'],
      sections: [],
      tests: []
    },
    {
      description: 'Array forEach cannot be frozen while in progress',
      test: test_NEED_TO_WRAP_FOREACH,
      repair: repair_NEED_TO_WRAP_FOREACH,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1447'],
      sections: ['15.4.4.18'],
      tests: ['S15.4.4.18_A1', 'S15.4.4.18_A2']
    },
    {
      description: 'Workaround undiagnosed need for dummy setter',
      test: test_NEEDS_DUMMY_SETTER,
      repair: repair_NEEDS_DUMMY_SETTER,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: [],
      sections: [],
      tests: []
    },
    {
      description: 'Getter on HTMLFormElement disappears',
      test: test_FORM_GETTERS_DISAPPEAR,
      repair: repair_NEEDS_DUMMY_SETTER,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['http://code.google.com/p/chromium/issues/detail?id=94666',
             'http://code.google.com/p/v8/issues/detail?id=1651',
             'http://code.google.com/p/google-caja/issues/detail?id=1401'],
      sections: ['15.2.3.6'],
      tests: ['S15.2.3.6_A1']
    },
    {
      description: 'Accessor properties inherit as own properties',
      test: test_ACCESSORS_INHERIT_AS_OWN,
      repair: repair_ACCESSORS_INHERIT_AS_OWN,
      preSeverity: severities.UNSAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['https://bugzilla.mozilla.org/show_bug.cgi?id=637994'],
      sections: ['8.6.1', '15.2.3.6'],
      tests: ['S15.2.3.6_A2']
    },
    {
      description: 'Array sort leaks global',
      test: test_SORT_LEAKS_GLOBAL,
      repair: repair_SORT_LEAKS_GLOBAL,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1360'],
      sections: ['15.4.4.11'],
      tests: ['S15.4.4.11_A8']
    },
    {
      description: 'String replace leaks global',
      test: test_REPLACE_LEAKS_GLOBAL,
      repair: repair_REPLACE_LEAKS_GLOBAL,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1360',
             'https://connect.microsoft.com/IE/feedback/details/' +
               '685928/bad-this-binding-for-callback-in-string-' +
               'prototype-replace'],
      sections: ['15.5.4.11'],
      tests: ['S15.5.4.11_A12']
    },
    {
      description: 'getOwnPropertyDescriptor on strict "caller" throws',
      test: test_CANT_GOPD_CALLER,
      repair: repair_CANT_GOPD_CALLER,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['https://connect.microsoft.com/IE/feedback/details/' +
               '685436/getownpropertydescriptor-on-strict-caller-throws'],
      sections: ['15.2.3.3', '13.2', '13.2.3'],
      tests: ['S13.2_A6_T1']
    },
    {
      description: 'strict_function.hasOwnProperty("caller") throws',
      test: test_CANT_HASOWNPROPERTY_CALLER,
      repair: repair_CANT_HASOWNPROPERTY_CALLER,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=63398#c3'],
      sections: ['15.2.4.5', '13.2', '13.2.3'],
      tests: ['S13.2_A7_T1']
    },
    {
      description: 'Cannot "in" caller on strict function',
      test: test_CANT_IN_CALLER,
      repair: void 0,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: false,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=63398'],
      sections: ['11.8.7', '13.2', '13.2.3'],
      tests: ['S13.2_A8_T1']
    },
    {
      description: 'Cannot "in" arguments on strict function',
      test: test_CANT_IN_ARGUMENTS,
      repair: void 0,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: false,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=63398'],
      sections: ['11.8.7', '13.2', '13.2.3'],
      tests: ['S13.2_A8_T2']
    },
    {
      description: 'Strict "caller" not poisoned',
      test: test_STRICT_CALLER_NOT_POISONED,
      repair: void 0,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: false,
      urls: [],
      sections: ['13.2'],
      tests: ['S13.2.3_A1']
    },
    {
      description: 'Strict "arguments" not poisoned',
      test: test_STRICT_ARGUMENTS_NOT_POISONED,
      repair: void 0,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: false,
      urls: [],
      sections: ['13.2'],
      tests: ['S13.2.3_A1']
    },
    {
      description: 'Built in functions leak "caller"',
      test: test_BUILTIN_LEAKS_CALLER,
      repair: repair_BUILTIN_LEAKS_CALLER,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1643',
             'http://code.google.com/p/v8/issues/detail?id=1548',
             'https://bugzilla.mozilla.org/show_bug.cgi?id=591846',
             'http://wiki.ecmascript.org/doku.php?id=' +
               'conventions:make_non-standard_properties_configurable'],
      sections: [],
      tests: ['Sbp_A10_T1']
    },
    {
      description: 'Built in functions leak "arguments"',
      test: test_BUILTIN_LEAKS_ARGUMENTS,
      repair: repair_BUILTIN_LEAKS_ARGUMENTS,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1643',
             'http://code.google.com/p/v8/issues/detail?id=1548',
             'https://bugzilla.mozilla.org/show_bug.cgi?id=591846',
             'http://wiki.ecmascript.org/doku.php?id=' +
               'conventions:make_non-standard_properties_configurable'],
      sections: [],
      tests: ['Sbp_A10_T2']
    },
    {
      description: 'Bound functions leak "caller"',
      test: test_BOUND_FUNCTION_LEAKS_CALLER,
      repair: repair_MISSING_BIND,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=893',
             'https://bugs.webkit.org/show_bug.cgi?id=63398'],
      sections: ['15.3.4.5'],
      tests: ['S13.2.3_A1', 'S15.3.4.5_A1']
    },
    {
      description: 'Bound functions leak "arguments"',
      test: test_BOUND_FUNCTION_LEAKS_ARGUMENTS,
      repair: repair_MISSING_BIND,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=893',
             'https://bugs.webkit.org/show_bug.cgi?id=63398'],
      sections: ['15.3.4.5'],
      tests: ['S13.2.3_A1', 'S15.3.4.5_A2']
    },
    {
      description: 'Deleting built-in leaves phantom behind',
      test: test_DELETED_BUILTINS_IN_OWN_NAMES,
      repair: repair_DELETED_BUILTINS_IN_OWN_NAMES,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=70207'],
      sections: ['15.2.3.4'],
      tests: []
    },
    {
      description: 'getOwnPropertyDescriptor on its own "caller" fails',
      test: test_GETOWNPROPDESC_OF_ITS_OWN_CALLER_FAILS,
      repair: repair_GETOWNPROPDESC_OF_ITS_OWN_CALLER_FAILS,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1769'],
      sections: ['13.2', '15.2.3.3'],
      tests: []
    },
    {
      description: 'JSON.parse confused by "__proto__"',
      test: test_JSON_PARSE_PROTO_CONFUSION,
      repair: repair_JSON_PARSE_PROTO_CONFUSION,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=621',
             'http://code.google.com/p/v8/issues/detail?id=1310'],
      sections: ['15.12.2'],
      tests: ['S15.12.2_A1']
    },
    {
      description: 'Prototype still mutable on non-extensible object',
      test: test_PROTO_NOT_FROZEN,
      repair: void 0,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: false,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=65832',
             'https://bugs.webkit.org/show_bug.cgi?id=78438'],
      sections: ['8.6.2'],
      tests: ['S8.6.2_A8']
    },
    {
      description: 'Prototype still redefinable on non-extensible object',
      test: test_PROTO_REDEFINABLE,
      repair: void 0,
      preSeverity: severities.NOT_OCAP_SAFE,
      canRepair: false,
      urls: ['https://bugs.webkit.org/show_bug.cgi?id=65832'],
      sections: ['8.6.2'],
      tests: ['S8.6.2_A8']
    },
    {
      description: 'Strict eval function leaks variable definitions',
      test: test_STRICT_EVAL_LEAKS_GLOBALS,
      repair: void 0,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: false,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1624'],
      sections: ['10.4.2.1'],
      tests: ['S10.4.2.1_A1']
    },
    {
      description: 'parseInt still parsing octal',
      test: test_PARSEINT_STILL_PARSING_OCTAL,
      repair: repair_PARSEINT_STILL_PARSING_OCTAL,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1645'],
      sections: ['15.1.2.2'],
      tests: ['S15.1.2.2_A5.1_T1']
    },
    {
      description: 'E4X literals allowed in strict code',
      test: test_STRICT_E4X_LITERALS_ALLOWED,
      repair: void 0,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: false,
      urls: ['https://bugzilla.mozilla.org/show_bug.cgi?id=695577',
             'https://bugzilla.mozilla.org/show_bug.cgi?id=695579'],
      sections: [],
      tests: []
    },
    {
      description: 'Assignment can override frozen inherited property',
      test: test_ASSIGN_CAN_OVERRIDE_FROZEN,
      repair: repair_ASSIGN_CAN_OVERRIDE_FROZEN,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: false,
      urls: ['http://code.google.com/p/v8/issues/detail?id=1169',
             'https://mail.mozilla.org/pipermail/es-discuss/' +
               '2011-November/017997.html'],
      sections: ['8.12.4'],
      tests: ['15.2.3.6-4-405']
    },
    {
      description: 'Cannot redefine global NaN to itself',
      test: test_CANT_REDEFINE_NAN_TO_ITSELF,
      repair: repair_CANT_REDEFINE_NAN_TO_ITSELF,
      preSeverity: severities.SAFE_SPEC_VIOLATION,
      canRepair: true,
      urls: [], // Seen on WebKit Nightly. TODO(erights): report
      sections: ['8.12.9', '15.1.1.1'],
      tests: [] // TODO(erights): Add to test262
    },
    {
      description: 'Error instances have unexpected properties',
      test: test_UNEXPECTED_ERROR_PROPERTIES,
      repair: void 0,
      preSeverity: severities.NEW_SYMPTOM,
      canRepair: false,
      urls: [],
      sections: [],
      tests: []
    },
    {
      description: 'getOwnPropertyNames lies, hiding some own properties',
      test: test_GET_OWN_PROPERTY_NAME_LIES,
      repair: void 0,
      preSeverity: severities.NOT_ISOLATED,
      canRepair: false,
      urls: ['https://bugzilla.mozilla.org/show_bug.cgi?id=726477'],
      sections: [],
      tests: []
    }
  ];

  ////////////////////// Testing, Repairing, Reporting ///////////

  var aboutTo = void 0;

  /**
   * Run a set of tests & repairs, and report results.
   *
   * <p>First run all the tests before repairing anything.
   * Then repair all repairable failed tests.
   * Some repair might fix multiple problems, but run each repair at most once.
   * Then run all the tests again, in case some repairs break other tests.
   * And finally return a list of records of results.
   */
  function testRepairReport(kludges) {
    var beforeFailures = strictMapFn(kludges, function(kludge) {
      aboutTo = ['pre test: ', kludge.description];
      return kludge.test();
    });
    var repairs = [];
    strictForEachFn(kludges, function(kludge, i) {
      if (beforeFailures[i]) {
        var repair = kludge.repair;
        if (repair && repairs.lastIndexOf(repair) === -1) {
          aboutTo = ['repair: ', kludge.description];
          repair();
          repairs.push(repair);
        }
      }
    });
    var afterFailures = strictMapFn(kludges, function(kludge) {
      aboutTo = ['post test: ', kludge.description];
      return kludge.test();
    });

    if (Object.isFrozen && Object.isFrozen(Array.prototype.forEach)) {
      // Need to do it anyway, to repair the sacrificial freezing we
      // needed to do to test. Once we can permanently retire this
      // test, we can also retire the redundant repair.
      repair_NEED_TO_WRAP_FOREACH();
    }

    return strictMapFn(kludges, function(kludge, i) {
      var status = statuses.ALL_FINE;
      var postSeverity = severities.SAFE;
      var beforeFailure = beforeFailures[i];
      var afterFailure = afterFailures[i];
      if (beforeFailure) { // failed before
        if (afterFailure) { // failed after
          if (kludge.repair) {
            postSeverity = kludge.preSeverity;
            status = statuses.REPAIR_FAILED;
          } else {
            if (!kludge.canRepair) {
              postSeverity = kludge.preSeverity;
            } // else no repair + canRepair -> problem isn't safety issue
            status = statuses.NOT_REPAIRED;
          }
        } else { // succeeded after
          if (kludge.repair) {
            if (!kludge.canRepair) {
              // repair for development, not safety
              postSeverity = kludge.preSeverity;
              status = statuses.REPAIRED_UNSAFELY;
            } else {
              status = statuses.REPAIRED;
            }
          } else {
            status = statuses.ACCIDENTALLY_REPAIRED;
          }
        }
      } else { // succeeded before
        if (afterFailure) { // failed after
          if (kludge.repair || !kludge.canRepair) {
            postSeverity = kludge.preSeverity;
          } // else no repair + canRepair -> problem isn't safety issue
          status = statuses.BROKEN_BY_OTHER_ATTEMPTED_REPAIRS;
        } else { // succeeded after
          // nothing to see here, move along
        }
      }

      if (typeof beforeFailure === 'string' ||
          typeof afterFailure === 'string') {
        postSeverity = severities.NEW_SYMPTOM;
      }

      ses.updateMaxSeverity(postSeverity);

      return {
        description:   kludge.description,
        preSeverity:   kludge.preSeverity,
        canRepair:     kludge.canRepair,
        urls:          kludge.urls,
        sections:      kludge.sections,
        tests:         kludge.tests,
        status:        status,
        postSeverity:  postSeverity,
        beforeFailure: beforeFailure,
        afterFailure:  afterFailure
      };
    });
  }

  try {
    var reports = testRepairReport(baseKludges);
    if (ses.ok()) {
      reports.push.apply(reports, testRepairReport(supportedKludges));
    }
    logger.reportRepairs(reports);
  } catch (err) {
    ses.updateMaxSeverity(ses.severities.NOT_SUPPORTED);
    var during = aboutTo ? '(' + aboutTo.join('') + ') ' : '';
    logger.error('ES5 Repair ' + during + 'failed with: ', err);
  }

  logger.reportMax();

})(this);
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Install a leaky WeakMap emulation on platforms that
 * don't provide a built-in one.
 *
 * <p>Assumes that an ES5 platform where, if {@code WeakMap} is
 * already present, then it conforms to the anticipated ES6
 * specification. To run this file on an ES5 or almost ES5
 * implementation where the {@code WeakMap} specification does not
 * quite conform, run <code>repairES5.js</code> first.
 *
 * @author Mark S. Miller
 * @requires ses, crypto, ArrayBuffer, Uint8Array
 * @overrides WeakMap, WeakMapModule
 */

/**
 * This {@code WeakMap} emulation is observably equivalent to the
 * ES-Harmony WeakMap, but with leakier garbage collection properties.
 *
 * <p>As with true WeakMaps, in this emulation, a key does not
 * retain maps indexed by that key and (crucially) a map does not
 * retain the keys it indexes. A map by itself also does not retain
 * the values associated with that map.
 *
 * <p>However, the values associated with a key in some map are
 * retained so long as that key is retained and those associations are
 * not overridden. For example, when used to support membranes, all
 * values exported from a given membrane will live for the lifetime
 * they would have had in the absence of an interposed membrane. Even
 * when the membrane is revoked, all objects that would have been
 * reachable in the absence of revocation will still be reachable, as
 * far as the GC can tell, even though they will no longer be relevant
 * to ongoing computation.
 *
 * <p>The API implemented here is approximately the API as implemented
 * in FF6.0a1 and agreed to by MarkM, Andreas Gal, and Dave Herman,
 * rather than the offially approved proposal page. TODO(erights):
 * upgrade the ecmascript WeakMap proposal page to explain this API
 * change and present to EcmaScript committee for their approval.
 *
 * <p>The first difference between the emulation here and that in
 * FF6.0a1 is the presence of non enumerable {@code get___, has___,
 * set___, and delete___} methods on WeakMap instances to represent
 * what would be the hidden internal properties of a primitive
 * implementation. Whereas the FF6.0a1 WeakMap.prototype methods
 * require their {@code this} to be a genuine WeakMap instance (i.e.,
 * an object of {@code [[Class]]} "WeakMap}), since there is nothing
 * unforgeable about the pseudo-internal method names used here,
 * nothing prevents these emulated prototype methods from being
 * applied to non-WeakMaps with pseudo-internal methods of the same
 * names.
 *
 * <p>Another difference is that our emulated {@code
 * WeakMap.prototype} is not itself a WeakMap. A problem with the
 * current FF6.0a1 API is that WeakMap.prototype is itself a WeakMap
 * providing ambient mutability and an ambient communications
 * channel. Thus, if a WeakMap is already present and has this
 * problem, repairES5.js wraps it in a safe wrappper in order to
 * prevent access to this channel. (See
 * PATCH_MUTABLE_FROZEN_WEAKMAP_PROTO in repairES5.js).
 */
var WeakMap;

/**
 * If this is a full <a href=
 * "http://code.google.com/p/es-lab/wiki/SecureableES5"
 * >secureable ES5</a> platform and the ES-Harmony {@code WeakMap} is
 * absent, install an approximate emulation.
 *
 * <p>If this is almost a secureable ES5 platform, then WeakMap.js
 * should be run after repairES5.js.
 *
 * <p>See {@code WeakMap} for documentation of the garbage collection
 * properties of this WeakMap emulation.
 */
(function WeakMapModule() {
  "use strict";

  if (typeof ses !== 'undefined' && ses.ok && !ses.ok()) {
    // already too broken, so give up
    return;
  }

  if (typeof WeakMap === 'function') {
    // assumed fine, so we're done.
    return;
  }

  var hop = Object.prototype.hasOwnProperty;
  var gopn = Object.getOwnPropertyNames;
  var defProp = Object.defineProperty;

  /**
   * Holds the orginal static properties of the Object constructor,
   * after repairES5 fixes these if necessary to be a more complete
   * secureable ES5 environment, but before installing the following
   * WeakMap emulation overrides and before any untrusted code runs.
   */
  var originalProps = {};
  gopn(Object).forEach(function(name) {
    originalProps[name] = Object[name];
  });

  /**
   * Security depends on HIDDEN_NAME being both <i>unguessable</i> and
   * <i>undiscoverable</i> by untrusted code.
   *
   * <p>Given the known weaknesses of Math.random() on existing
   * browsers, it does not generate unguessability we can be confident
   * of.
   *
   * <p>It is the monkey patching logic in this file that is intended
   * to ensure undiscoverability. The basic idea is that there are
   * three fundamental means of discovering properties of an object:
   * The for/in loop, Object.keys(), and Object.getOwnPropertyNames(),
   * as well as some proposed ES6 extensions that appear on our
   * whitelist. The first two only discover enumerable properties, and
   * we only use HIDDEN_NAME to name a non-enumerable property, so the
   * only remaining threat should be getOwnPropertyNames and some
   * proposed ES6 extensions that appear on our whitelist. We monkey
   * patch them to remove HIDDEN_NAME from the list of properties they
   * returns.
   *
   * <p>TODO(erights): On a platform with built-in Proxies, proxies
   * could be used to trap and thereby discover the HIDDEN_NAME, so we
   * need to monkey patch Proxy.create, Proxy.createFunction, etc, in
   * order to wrap the provided handler with the real handler which
   * filters out all traps using HIDDEN_NAME.
   *
   * <p>TODO(erights): Revisit Mike Stay's suggestion that we use an
   * encapsulated function at a not-necessarily-secret name, which
   * uses the Stiegler shared-state rights amplification pattern to
   * reveal the associated value only to the WeakMap in which this key
   * is associated with that value. Since only the key retains the
   * function, the function can also remember the key without causing
   * leakage of the key, so this doesn't violate our general gc
   * goals. In addition, because the name need not be a guarded
   * secret, we could efficiently handle cross-frame frozen keys.
   */
  var HIDDEN_NAME = 'ident:' + Math.random() + '___';

  if (typeof crypto !== 'undefined' &&
      typeof crypto.getRandomValues === 'function' &&
      typeof ArrayBuffer === 'function' &&
      typeof Uint8Array === 'function') {
    var ab = new ArrayBuffer(25);
    var u8s = new Uint8Array(ab);
    crypto.getRandomValues(u8s);
    HIDDEN_NAME = 'rand:' +
      Array.prototype.map.call(u8s, function(u8) {
        return (u8 % 36).toString(36);
      }).join('') + '___';
  }

  /**
   * Monkey patch getOwnPropertyNames to avoid revealing the
   * HIDDEN_NAME.
   *
   * <p>The ES5.1 spec requires each name to appear only once, but as
   * of this writing, this requirement is controversial for ES6, so we
   * made this code robust against this case. If the resulting extra
   * search turns out to be expensive, we can probably relax this once
   * ES6 is adequately supported on all major browsers, iff no browser
   * versions we support at that time have relaxed this constraint
   * without providing built-in ES6 WeakMaps.
   */
  defProp(Object, 'getOwnPropertyNames', {
    value: function fakeGetOwnPropertyNames(obj) {
      return gopn(obj).filter(function(name) {
        return name !== HIDDEN_NAME;
      });
    }
  });

  /**
   * getPropertyNames is not in ES5 but it is proposed for ES6 and
   * does appear in our whitelist, so we need to clean it too.
   */
  if ('getPropertyNames' in Object) {
    defProp(Object, 'getPropertyNames', {
      value: function fakeGetPropertyNames(obj) {
        return originalProps.getPropertyNames(obj).filter(function(name) {
          return name !== HIDDEN_NAME;
        });
      }
    });
  }

  /**
   * <p>To treat objects as identity-keys with reasonable efficiency
   * on ES5 by itself (i.e., without any object-keyed collections), we
   * need to add a hidden property to such key objects when we
   * can. This raises several issues:
   * <ul>
   * <li>Arranging to add this property to objects before we lose the
   *     chance, and
   * <li>Hiding the existence of this new property from most
   *     JavaScript code.
   * <li>Preventing <i>certification theft</i>, where one object is
   *     created falsely claiming to be the key of an association
   *     actually keyed by another object.
   * <li>Preventing <i>value theft</i>, where untrusted code with
   *     access to a key object but not a weak map nevertheless
   *     obtains access to the value associated with that key in that
   *     weak map.
   * </ul>
   * We do so by
   * <ul>
   * <li>Making the name of the hidden property unguessable, so "[]"
   *     indexing, which we cannot intercept, cannot be used to access
   *     a property without knowing the name.
   * <li>Making the hidden property non-enumerable, so we need not
   *     worry about for-in loops or {@code Object.keys},
   * <li>monkey patching those reflective methods that would
   *     prevent extensions, to add this hidden property first,
   * <li>monkey patching those methods that would reveal this
   *     hidden property.
   * </ul>
   * Unfortunately, because of same-origin iframes, we cannot reliably
   * add this hidden property before an object becomes
   * non-extensible. Instead, if we encounter a non-extensible object
   * without a hidden record that we can detect (whether or not it has
   * a hidden record stored under a name secret to us), then we just
   * use the key object itself to represent its identity in a brute
   * force leaky map stored in the weak map, losing all the advantages
   * of weakness for these.
   */
  function getHiddenRecord(key) {
    if (key !== Object(key)) {
      throw new TypeError('Not an object: ' + key);
    }
    var hiddenRecord = key[HIDDEN_NAME];
    if (hiddenRecord && hiddenRecord.key === key) { return hiddenRecord; }
    if (!originalProps.isExtensible(key)) {
      // Weak map must brute force, as explained in doc-comment above.
      return void 0;
    }
    var gets = [];
    var vals = [];
    hiddenRecord = {
      key: key,   // self pointer for quick own check above.
      gets: gets, // get___ methods identifying weak maps
      vals: vals  // values associated with this key in each
                  // corresponding weak map.
    };
    defProp(key, HIDDEN_NAME, {
      value: hiddenRecord,
      writable: false,
      enumerable: false,
      configurable: false
    });
    return hiddenRecord;
  }


  /**
   * Monkey patch operations that would make their argument
   * non-extensible.
   *
   * <p>The monkey patched versions throw a TypeError if their
   * argument is not an object, so it should only be done to functions
   * that should throw a TypeError anyway if their argument is not an
   * object.
   */
  (function(){
    var oldFreeze = Object.freeze;
    defProp(Object, 'freeze', {
      value: function identifyingFreeze(obj) {
        getHiddenRecord(obj);
        return oldFreeze(obj);
      }
    });
    var oldSeal = Object.seal;
    defProp(Object, 'seal', {
      value: function identifyingSeal(obj) {
        getHiddenRecord(obj);
        return oldSeal(obj);
      }
    });
    var oldPreventExtensions = Object.preventExtensions;
    defProp(Object, 'preventExtensions', {
      value: function identifyingPreventExtensions(obj) {
        getHiddenRecord(obj);
        return oldPreventExtensions(obj);
      }
    });
  })();


  function constFunc(func) {
    func.prototype = null;
    return Object.freeze(func);
  }

  // Right now (12/25/2012) the histogram supports the current
  // representation. We should check this occasionally, as a true
  // constant time representation is easy.
  // var histogram = [];

  WeakMap = function() {
    // We are currently (12/25/2012) never encountering any prematurely
    // non-extensible keys.
    var keys = []; // brute force for prematurely non-extensible keys.
    var vals = []; // brute force for corresponding values.

    function get___(key, opt_default) {
      var hr = getHiddenRecord(key);
      var i, vs;
      if (hr) {
        i = hr.gets.indexOf(get___);
        vs = hr.vals;
      } else {
        i = keys.indexOf(key);
        vs = vals;
      }
      return (i >= 0) ? vs[i] : opt_default;
    }

    function has___(key) {
      var hr = getHiddenRecord(key);
      var i;
      if (hr) {
        i = hr.gets.indexOf(get___);
      } else {
        i = keys.indexOf(key);
      }
      return i >= 0;
    }

    function set___(key, value) {
      var hr = getHiddenRecord(key);
      var i;
      if (hr) {
        i = hr.gets.indexOf(get___);
        if (i >= 0) {
          hr.vals[i] = value;
        } else {
//          i = hr.gets.length;
//          histogram[i] = (histogram[i] || 0) + 1;
          hr.gets.push(get___);
          hr.vals.push(value);
        }
      } else {
        i = keys.indexOf(key);
        if (i >= 0) {
          vals[i] = value;
        } else {
          keys.push(key);
          vals.push(value);
        }
      }
    }

    function delete___(key) {
      var hr = getHiddenRecord(key);
      var i;
      if (hr) {
        i = hr.gets.indexOf(get___);
        if (i >= 0) {
          hr.gets.splice(i, 1);
          hr.vals.splice(i, 1);
        }
      } else {
        i = keys.indexOf(key);
        if (i >= 0) {
          keys.splice(i, 1);
          vals.splice(i, 1);
        }
      }
      return true;
    }

    return Object.create(WeakMap.prototype, {
      get___:    { value: constFunc(get___) },
      has___:    { value: constFunc(has___) },
      set___:    { value: constFunc(set___) },
      delete___: { value: constFunc(delete___) }
    });
  };
  WeakMap.prototype = Object.create(Object.prototype, {
    get: {
      /**
       * Return the value most recently associated with key, or
       * opt_default if none.
       */
      value: function get(key, opt_default) {
        return this.get___(key, opt_default);
      },
      writable: true,
      configurable: true
    },

    has: {
      /**
       * Is there a value associated with key in this WeakMap?
       */
      value: function has(key) {
        return this.has___(key);
      },
      writable: true,
      configurable: true
    },

    set: {
      /**
       * Associate value with key in this WeakMap, overwriting any
       * previous association if present.
       */
      value: function set(key, value) {
        this.set___(key, value);
      },
      writable: true,
      configurable: true
    },

    'delete': {
      /**
       * Remove any association for key in this WeakMap, returning
       * whether there was one.
       *
       * <p>Note that the boolean return here does not work like the
       * {@code delete} operator. The {@code delete} operator returns
       * whether the deletion succeeds at bringing about a state in
       * which the deleted property is absent. The {@code delete}
       * operator therefore returns true if the property was already
       * absent, whereas this {@code delete} method returns false if
       * the association was already absent.
       */
      value: function remove(key) {
        return this.delete___(key);
      },
      writable: true,
      configurable: true
    }
  });

})();
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview An optional part of the SES initialization process
 * that saves potentially valuable debugging aids on the side before
 * startSES.js would remove these, and adds a debugging API which uses
 * these without compromising SES security.
 *
 * <p>NOTE: The currently exposed debugging API is far from
 * settled. This module is currently in an exploratory phase.
 *
 * <p>Meant to be run sometime after repairs are done and a working
 * WeakMap is available, but before startSES.js. initSES.js includes
 * this. initSESPlus.js does not.
 *
 * //provides ses.UnsafeError,
 * //provides ses.getCWStack ses.stackString ses.getStack
 * @author Mark S. Miller
 * @requires WeakMap, this
 * @overrides Error, ses, debugModule
 */

var Error;
var ses;

(function debugModule(global) {
   "use strict";


   /**
    * Save away the original Error constructor as ses.UnsafeError and
    * make it otheriwse unreachable. Replace it with a reachable
    * wrapping constructor with the same standard behavior.
    *
    * <p>When followed by the rest of SES initialization, the
    * UnsafeError we save off here is exempt from whitelist-based
    * extra property removal and primordial freezing. Thus, we can
    * use any platform specific APIs defined on Error for privileged
    * debugging operations, unless explicitly turned off below.
    */
   var UnsafeError = Error;
   ses.UnsafeError = Error;
   function FakeError(message) {
     return UnsafeError(message);
   }
   FakeError.prototype = UnsafeError.prototype;
   FakeError.prototype.constructor = FakeError;

   Error = FakeError;

   /**
    * Should be a function of an argument object (normally an error
    * instance) that returns the stack trace associated with argument
    * in Causeway format.
    *
    * <p>See http://wiki.erights.org/wiki/Causeway_Platform_Developer
    *
    * <p>Currently, there is no one portable technique for doing
    * this. So instead, each platform specific branch of the if below
    * should assign something useful to getCWStack.
    */
   ses.getCWStack = function uselessGetCWStack(err) { return void 0; };

   if ('captureStackTrace' in UnsafeError) {
     (function() {
       // Assuming http://code.google.com/p/v8/wiki/JavaScriptStackTraceApi
       // So this section is v8 specific.

       UnsafeError.prepareStackTrace = function(err, sst) {
         ssts.set(err, sst);
         return void 0;
       };

       var unsafeCaptureStackTrace = UnsafeError.captureStackTrace;

       // TODO(erights): This seems to be write only. Can this be made
       // safe enough to expose to untrusted code?
       UnsafeError.captureStackTrace = function(obj, opt_MyError) {
         var wasFrozen = Object.isFrozen(obj);
         var stackDesc = Object.getOwnPropertyDescriptor(obj, 'stack');
         try {
           var result = unsafeCaptureStackTrace(obj, opt_MyError);
           var ignore = obj.stack;
           return result;
         } finally {
           if (wasFrozen && !Object.isFrozen(obj)) {
             if (stackDesc) {
               Object.defineProperty(obj, 'stack', stackDesc);
             } else {
               delete obj.stack;
             }
             Object.freeze(obj);
           }
         }
       };

       var ssts = WeakMap(); // error -> sst

       /**
        * Returns a stack in Causeway format.
        *
        * <p>Based on
        * http://code.google.com/p/causeway/source/browse/trunk/src/js/com/teleometry/causeway/purchase_example/workers/makeCausewayLogger.js
        */
       function getCWStack(err) {
         var sst = ssts.get(err);
         if (sst === void 0 && err instanceof Error) {
           // We hope it triggers prepareStackTrace
           var ignore = err.stack;
           sst = ssts.get(err);
         }
         if (sst === void 0) { return void 0; }

         return { calls: sst.map(function(frame) {
           return {
             name: '' + (frame.getFunctionName() ||
                         frame.getMethodName() || '?'),
             source: '' + (frame.getFileName() || '?'),
             span: [ [ frame.getLineNumber(), frame.getColumnNumber() ] ]
           };
         })};
       };
       ses.getCWStack = getCWStack;
     })();

   } else if (global.opera) {
     (function() {
       // Since pre-ES5 browsers are disqualified, we can assume a
       // minimum of Opera 11.60.
     })();


   } else if (new Error().stack) {
     (function() {
       var FFFramePattern = (/^([^@]*)@(.*?):?(\d*)$/);

       // stacktracejs.org suggests that this indicates FF. Really?
       function getCWStack(err) {
         var stack = err.stack;
         if (!stack) { return void 0; }
         var lines = stack.split('\n');
         var frames = lines.map(function(line) {
           var match = FFFramePattern.exec(line);
           if (match) {
             return {
               name: match[1].trim() || '?',
               source: match[2].trim() || '?',
               span: [[+match[3]]]
             };
           } else {
             return {
               name: line.trim() || '?',
               source: '?',
               span: []
             };
           }
         });
         return { calls: frames };
       }

       ses.getCWStack = getCWStack;
     })();

   } else {
     (function() {
       // Including Safari and IE10.
     })();

   }

   /**
    * Turn a Causeway stack into a v8-like stack traceback string.
    */
   function stackString(cwStack) {
     if (!cwStack) { return void 0; }
     var calls = cwStack.calls;

     var result = calls.map(function(call) {

       var spanString = call.span.map(function(subSpan) {
         return subSpan.join(':');
       }).join('::');
       if (spanString) { spanString = ':' + spanString; }

       return '  at ' + call.name + ' (' + call.source + spanString + ')';

     });
     return result.join('\n');
   };
   ses.stackString = stackString;

   /**
    * Return the v8-like stack traceback string associated with err.
    */
   function getStack(err) {
     if (err !== Object(err)) { return void 0; }
     var cwStack = ses.getCWStack(err);
     if (!cwStack) { return void 0; }
     var result = ses.stackString(cwStack);
     if (err instanceof Error) { result = err + '\n' + result; }
     return result;
   };
   ses.getStack = getStack;

 })(this);;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Implements StringMap - a map api for strings.
 *
 * @author Mark S. Miller
 * @author Jasvir Nagra
 * @overrides StringMap
 */

var StringMap;

(function() {
   "use strict";

   var create = Object.create;
   var freeze = Object.freeze;
   function constFunc(func) {
     func.prototype = null;
     return freeze(func);
   }

   function assertString(x) {
     if ('string' !== typeof(x)) {
       throw new TypeError('Not a string: ' + String(x));
     }
     return x;
   }

   StringMap = function StringMap() {

     var objAsMap = create(null);

     return freeze({
       get: constFunc(function(key) {
         return objAsMap[assertString(key) + '$'];
       }),
       set: constFunc(function(key, value) {
         objAsMap[assertString(key) + '$'] = value;
       }),
       has: constFunc(function(key) {
         return (assertString(key) + '$') in objAsMap;
       }),
       'delete': constFunc(function(key) {
         return delete objAsMap[assertString(key) + '$'];
       })
     });
   };

 })();
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Exports {@code ses.whitelist}, a recursively defined
 * JSON record enumerating all the naming paths in the ES5.1 spec,
 * those de-facto extensions that we judge to be safe, and SES and
 * Dr. SES extensions provided by the SES runtime.
 *
 * <p>Assumes only ES3. Compatible with ES5, ES5-strict, or
 * anticipated ES6.
 *
 * //provides ses.whitelist
 * @author Mark S. Miller,
 * @overrides ses, whitelistModule
 */
var ses;

/**
 * <p>Each JSON record enumerates the disposition of the properties on
 * some corresponding primordial object, with the root record
 * representing the global object. For each such record, the values
 * associated with its property names can be
 * <ul>
 * <li>Another record, in which case this property is simply
 *     whitelisted and that next record represents the disposition of
 *     the object which is its value. For example, {@code "Object"}
 *     leads to another record explaining what properties {@code
 *     "Object"} may have and how each such property, if present,
 *     and its value should be tamed.
 * <li>true, in which case this property is simply whitelisted. The
 *     value associated with that property is still traversed and
 *     tamed, but only according to the taming of the objects that
 *     object inherits from. For example, {@code "Object.freeze"} leads
 *     to true, meaning that the {@code "freeze"} property of {@code
 *     Object} should be whitelisted and the value of the property (a
 *     function) should be further tamed only according to the
 *     markings of the other objects it inherits from, like {@code
 *     "Function.prototype"} and {@code "Object.prototype").
 * <li>"*", in which case this property on this object is whitelisted,
 *     as is this property as inherited by all objects that inherit
 *     from this object. The values associated with all such properties
 *     are still traversed and tamed, but only according to the taming
 *     of the objects that object inherits from. For example, {@code
 *     "Object.prototype.constructor"} leads to "*", meaning that we
 *     whitelist the {@code "constructor"} property on {@code
 *     Object.prototype} and on every object that inherits from {@code
 *     Object.prototype} that does not have a conflicting mark. Each
 *     of these is tamed as if with true, so that the value of the
 *     property is further tamed according to what other objects it
 *     inherits from.
 * <li>"skip", in which case this property on this object is simply
 *     whitelisted, as is this property as inherited by all objects
 *     that inherit from this object, but we avoid taming the value
 *     associated with that property. For example, as of this writing
 *     {@code "Function.prototype.caller"} leads to "skip" because
 *     some current browser bugs prevent us from removing or even
 *     traversing this property on some platforms of interest.
 * </ul>
 *
 * The "skip" markings are workarounds for browser bugs or other
 * temporary problems. For each of these, there should be an
 * explanatory comment explaining why or a bug citation. Ideally, we
 * can retire all "skip" entries by the time SES is ready for secure
 * production use.
 *
 * The members of the whitelist are either
 * <ul>
 * <li>(uncommented) defined by the ES5.1 normative standard text,
 * <li>(questionable) provides a source of non-determinism, in
 *     violation of pure object-capability rules, but allowed anyway
 *     since we've given up on restricting JavaScript to a
 *     deterministic subset.
 * <li>(ES5 Appendix B) common elements of de facto JavaScript
 *     described by the non-normative Appendix B.
 * <li>(Harmless whatwg) extensions documented at
 *     <a href="http://wiki.whatwg.org/wiki/Web_ECMAScript"
 *     >http://wiki.whatwg.org/wiki/Web_ECMAScript</a> that seem to be
 *     harmless. Note that the RegExp constructor extensions on that
 *     page are <b>not harmless</b> and so must not be whitelisted.
 * <li>(ES-Harmony proposal) accepted as "proposal" status for
 *     EcmaScript-Harmony.
 * <li>(Marked as "skip") See above.
 * </ul>
 *
 * <p>With the above encoding, there are some sensible whitelists we
 * cannot express, such as marking a property both with "*" and a JSON
 * record. This is an expedient decision based only on not having
 * encountered such a need. Should we need this extra expressiveness,
 * we'll need to refactor to enable a different encoding.
 *
 * <p>We factor out {@code true} into the variable {@code t} just to
 * get a bit better compression from simple minifiers.
 */
(function whitelistModule() {
  "use strict";

  if (!ses) { ses = {}; }

  var t = true;
  ses.whitelist = {
    cajaVM: {                        // Caja support
      log: t,
      tamperProof: t,
      constFunc: t,
      def: t,
      is: t,

      compileExpr: t,
      compileModule: t,              // experimental
      compileProgram: t,             // Cannot be implemented in just ES5.1.
      eval: t,
      Function: t,

      sharedImports: t,
      makeImports: t,
      copyToImports: t,

      callWithEjector: t,
      eject: t,
      GuardT: {
        coerce: t
      },
      makeTableGuard: t,
      Trademark: {
        stamp: t
      },
      guard: t,
      passesGuard: t,
      stamp: t,
      makeSealerUnsealerPair: t,

      makeArrayLike: {}
    },
    WeakMap: {       // ES-Harmony proposal as currently implemented by FF6.0a1
      prototype: {
        // Note: coordinate this list with maintenance of repairES5.js
        get: t,
        set: t,
        has: t,
        'delete': t
      }
    },
    StringMap: {  // A specialized approximation of ES-Harmony's Map.
      prototype: {} // Technically, the methods should be on the prototype,
                    // but doing so while preserving encapsulation will be
                    // needlessly expensive for current usage.
    },
// As of this writing, the WeakMap emulation in WeakMap.js relies on
// the unguessability and undiscoverability of HIDDEN_NAME, a
// secret property name. However, on a platform with built-in
// Proxies, if whitelisted but not properly monkey patched, proxies
// could be used to trap and thereby discover HIDDEN_NAME. So until we
// (TODO(erights)) write the needed monkey patching of proxies, we
// omit them from our whitelist.
//    Proxy: {                         // ES-Harmony proposal
//      create: t,
//      createFunction: t
//    },
    escape: t,                       // ES5 Appendix B
    unescape: t,                     // ES5 Appendix B
    Object: {
      // If any new methods are added here that may reveal the
      // HIDDEN_NAME within WeakMap.js, such as the proposed
      // getOwnPropertyDescriptors or getPropertyDescriptors, then
      // extend WeakMap.js to monkey patch these to avoid revealing
      // HIDDEN_NAME.
      getPropertyDescriptor: t,      // ES-Harmony proposal
      getPropertyNames: t,           // ES-Harmony proposal
      is: t,                         // ES-Harmony proposal
      prototype: {

        // Whitelisted only to work around a Chrome debugger
        // stratification bug (TODO(erights): report). These are
        // redefined in startSES.js in terms of standard methods, so
        // that we can be confident they introduce no non-standard
        // possibilities.
        __defineGetter__: t,
        __defineSetter__: t,
        __lookupGetter__: t,
        __lookupSetter__: t,

        constructor: '*',
        toString: '*',
        toLocaleString: '*',
        valueOf: t,
        hasOwnProperty: t,
        isPrototypeOf: t,
        propertyIsEnumerable: t
      },
      getPrototypeOf: t,
      getOwnPropertyDescriptor: t,
      getOwnPropertyNames: t,
      create: t,
      defineProperty: t,
      defineProperties: t,
      seal: t,
      freeze: t,
      preventExtensions: t,
      isSealed: t,
      isFrozen: t,
      isExtensible: t,
      keys: t
    },
    NaN: t,
    Infinity: t,
    undefined: t,
    // eval: t,                      // Whitelisting under separate control
                                     // by TAME_GLOBAL_EVAL in startSES.js
    parseInt: t,
    parseFloat: t,
    isNaN: t,
    isFinite: t,
    decodeURI: t,
    decodeURIComponent: t,
    encodeURI: t,
    encodeURIComponent: t,
    Function: {
      prototype: {
        apply: t,
        call: t,
        bind: t,
        prototype: '*',
        length: '*',
        arity: '*',                  // non-std, deprecated in favor of length
        name: '*'                    // non-std
      }
    },
    Array: {
      prototype: {
        concat: t,
        join: t,
        pop: t,
        push: t,
        reverse: t,
        shift: t,
        slice: t,
        sort: t,
        splice: t,
        unshift: t,
        indexOf: t,
        lastIndexOf: t,
        every: t,
        some: t,
        forEach: t,
        map: t,
        filter: t,
        reduce: t,
        reduceRight: t,
        length: 'skip'               // can't be redefined on Mozilla
        // See https://bugzilla.mozilla.org/show_bug.cgi?id=591059
        // and https://bugzilla.mozilla.org/show_bug.cgi?id=598996
      },
      isArray: t
    },
    String: {
      prototype: {
        substr: t,                   // ES5 Appendix B
        anchor: t,                   // Harmless whatwg
        big: t,                      // Harmless whatwg
        blink: t,                    // Harmless whatwg
        bold: t,                     // Harmless whatwg
        fixed: t,                    // Harmless whatwg
        fontcolor: t,                // Harmless whatwg
        fontsize: t,                 // Harmless whatwg
        italics: t,                  // Harmless whatwg
        link: t,                     // Harmless whatwg
        small: t,                    // Harmless whatwg
        strike: t,                   // Harmless whatwg
        sub: t,                      // Harmless whatwg
        sup: t,                      // Harmless whatwg
        trimLeft: t,                 // non-standard
        trimRight: t,                // non-standard
        valueOf: t,
        charAt: t,
        charCodeAt: t,
        concat: t,
        indexOf: t,
        lastIndexOf: t,
        localeCompare: t,
        match: t,
        replace: t,
        search: t,
        slice: t,
        split: t,
        substring: t,
        toLowerCase: t,
        toLocaleLowerCase: t,
        toUpperCase: t,
        toLocaleUpperCase: t,
        trim: t,
        length: '*'
      },
      fromCharCode: t
    },
    Boolean: {
      prototype: {
        valueOf: t
      }
    },
    Number: {
      prototype: {
        valueOf: t,
        toFixed: t,
        toExponential: t,
        toPrecision: t
      },
      MAX_VALUE: t,
      MIN_VALUE: t,
      NaN: t,
      NEGATIVE_INFINITY: t,
      POSITIVE_INFINITY: t
    },
    Math: {
      E: t,
      LN10: t,
      LN2: t,
      LOG2E: t,
      LOG10E: t,
      PI: t,
      SQRT1_2: t,
      SQRT2: t,

      abs: t,
      acos: t,
      asin: t,
      atan: t,
      atan2: t,
      ceil: t,
      cos: t,
      exp: t,
      floor: t,
      log: t,
      max: t,
      min: t,
      pow: t,
      random: t,                     // questionable
      round: t,
      sin: t,
      sqrt: t,
      tan: t
    },
    Date: {                          // no-arg Date constructor is questionable
      prototype: {
        // Note: coordinate this list with maintanence of repairES5.js
        getYear: t,                  // ES5 Appendix B
        setYear: t,                  // ES5 Appendix B
        toGMTString: t,              // ES5 Appendix B
        toDateString: t,
        toTimeString: t,
        toLocaleString: t,
        toLocaleDateString: t,
        toLocaleTimeString: t,
        getTime: t,
        getFullYear: t,
        getUTCFullYear: t,
        getMonth: t,
        getUTCMonth: t,
        getDate: t,
        getUTCDate: t,
        getDay: t,
        getUTCDay: t,
        getHours: t,
        getUTCHours: t,
        getMinutes: t,
        getUTCMinutes: t,
        getSeconds: t,
        getUTCSeconds: t,
        getMilliseconds: t,
        getUTCMilliseconds: t,
        getTimezoneOffset: t,
        setTime: t,
        setFullYear: t,
        setUTCFullYear: t,
        setMonth: t,
        setUTCMonth: t,
        setDate: t,
        setUTCDate: t,
        setHours: t,
        setUTCHours: t,
        setMinutes: t,
        setUTCMinutes: t,
        setSeconds: t,
        setUTCSeconds: t,
        setMilliseconds: t,
        setUTCMilliseconds: t,
        toUTCString: t,
        toISOString: t,
        toJSON: t
      },
      parse: t,
      UTC: t,
      now: t                         // questionable
    },
    RegExp: {
      prototype: {
        exec: t,
        test: t,
        source: '*',
        global: '*',
        ignoreCase: '*',
        multiline: '*',
        lastIndex: '*',
        sticky: '*'                  // non-std
      }
    },
    Error: {
      prototype: {
        name: '*',
        message: '*'
      }
    },
    EvalError: {
      prototype: t
    },
    RangeError: {
      prototype: t
    },
    ReferenceError: {
      prototype: t
    },
    SyntaxError: {
      prototype: t
    },
    TypeError: {
      prototype: t
    },
    URIError: {
      prototype: t
    },
    JSON: {
      parse: t,
      stringify: t
    }
  };
})();
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Export a {@code ses.atLeastFreeVarNames} function for
 * internal use by the SES-on-ES5 implementation, which enumerates at
 * least the identifiers which occur freely in a source text string.
 *
 * <p>Assumes only ES3. Compatible with ES5, ES5-strict, or
 * anticipated ES6.
 *
 * // provides ses.atLeastFreeVarNames
 * @author Mark S. Miller
 * @requires StringMap
 * @overrides ses, atLeastFreeVarNamesModule
 */
var ses;

/**
 * Calling {@code ses.atLeastFreeVarNames} on a {@code programSrc}
 * string argument, the result should include at least all the free
 * variable names of {@code programSrc} as own properties. It is
 * harmless to include other strings as well.
 *
 * <p>Assuming a programSrc that parses as a strict Program,
 * atLeastFreeVarNames(programSrc) returns a Record whose enumerable
 * own property names must include the names of all the free variables
 * occuring in programSrc. It can include as many other strings as is
 * convenient so long as it includes these. The value of each of these
 * properties should be {@code true}.
 *
 * <p>TODO(erights): On platforms that support Proxies (currently only
 * FF4 and later), we should stop using atLeastFreeVarNames, since a
 * {@code with(aProxy) {...}} should reliably intercept all free
 * variable accesses without needing any prior scan.
 */
(function atLeastFreeVarNamesModule() {
  "use strict";

   if (!ses) { ses = {}; }

  /////////////// KLUDGE SWITCHES ///////////////

  /**
   * Currently we use this to limit the input text to ascii only
   * without backslash-u escapes, in order to simply our identifier
   * gathering.
   *
   * <p>This is only a temporary development hack. TODO(erights): fix.
   */
  function LIMIT_SRC(programSrc) {
    if ((/[^\u0000-\u007f]/).test(programSrc)) {
      throw new EvalError('Non-ascii text not yet supported');
    }
    if ((/\\u/).test(programSrc)) {
      throw new EvalError('Backslash-u escape encoded text not yet supported');
    }
  }

  /**
   * Return a regexp that can be used repeatedly to scan for the next
   * identifier.
   *
   * <p>The current implementation is safe only because of the above
   * LIMIT_SRC. To do this right takes quite a lot of unicode
   * machinery. See the "Identifier" production at
   * http://es-lab.googlecode.com/svn/trunk/src/parser/es5parser.ojs
   * which depends on
   * http://es-lab.googlecode.com/svn/trunk/src/parser/unicode.js
   *
   * <p>This is only a temporary development hack. TODO(erights): fix.
   */
  function SHOULD_MATCH_IDENTIFIER() { return (/(\w|\$)+/g); }


  //////////////// END KLUDGE SWITCHES ///////////

  ses.atLeastFreeVarNames = function atLeastFreeVarNames(programSrc) {
    programSrc = String(programSrc);
    LIMIT_SRC(programSrc);
    // Now that we've temporarily limited our attention to ascii...
    var regexp = SHOULD_MATCH_IDENTIFIER();
    // Once we decide this file can depends on ES5, the following line
    // should say "... = Object.create(null);" rather than "... = {};"
    var result = [];
    var found = StringMap();
    var a;
    while ((a = regexp.exec(programSrc))) {
      // Note that we could have avoided the while loop by doing
      // programSrc.match(regexp), except that then we'd need
      // temporary storage proportional to the total number of
      // apparent identifiers, rather than the total number of
      // apparently unique identifiers.
      var name = a[0];

      if (!found.has(name)) {
        result.push(name);
        found.set(name, true);
      }
    }
    return result;
  };

})();
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Make this frame SES-safe or die trying.
 *
 * <p>Assumes ES5 plus a WeakMap that conforms to the anticipated ES6
 * WeakMap spec. Compatible with ES5-strict or anticipated ES6.
 *
 * //provides ses.startSES
 * @author Mark S. Miller,
 * @requires WeakMap
 * @overrides ses, console, eval, Function, cajaVM
 */
var ses;


/**
 * The global {@code eval} function available to script code, which
 * may or not be made safe.
 *
 * <p>The original global binding of {@code eval} is not
 * SES-safe. {@code cajaVM.eval} is a safe wrapper around this
 * original eval, enforcing SES language restrictions.
 *
 * <p>If {@code TAME_GLOBAL_EVAL} is true, both the global {@code
 * eval} variable and {@code sharedImports.eval} are set to the safe
 * wrapper. If {@code TAME_GLOBAL_EVAL} is false, in order to work
 * around a bug in the Chrome debugger, then the global {@code eval}
 * is unaltered and no {@code "eval"} property is available on {@code
 * sharedImports}. In either case, SES-evaled-code and SES-script-code
 * can both access the safe eval wrapper as {@code cajaVM.eval}.
 *
 * <p>By making the safe eval available on {@code sharedImports} only
 * when we also make it be the genuine global eval, we preserve the
 * property that SES-evaled-code differs from SES-script-code only by
 * having a subset of the same variables in globalish scope. This is a
 * nice-to-have that makes explanation easier rather than a hard
 * requirement. With this property, any SES-evaled-code that does not
 * fail to access a global variable (or to test whether it could)
 * should operate the same way when run as SES-script-code.
 *
 * <p>See doc-comment on cajaVM for the restriction on this API needed
 * to operate under Caja translation on old browsers.
 */
var eval;

/**
 * The global {@code Function} constructor is always replaced with a
 * safe wrapper, which is also made available as
 * {@code sharedImports.Function}.
 *
 * <p>Both the original Function constructor and this safe wrapper
 * point at the original {@code Function.prototype}, so {@code
 * instanceof} works fine with the wrapper. {@code
 * Function.prototype.constructor} is set to point at the safe
 * wrapper, so that only it, and not the unsafe original, is
 * accessible.
 *
 * <p>See doc-comment on cajaVM for the restriction on this API needed
 * to operate under Caja translation on old browsers.
 */
var Function;

/**
 * A new global exported by SES, intended to become a mostly
 * compatible API between server-side Caja translation for older
 * browsers and client-side SES verification for newer browsers.
 *
 * <p>Under server-side Caja translation for old pre-ES5 browsers, the
 * synchronous interface of the evaluation APIs (currently {@code
 * eval, Function, cajaVM.{compileExpr, compileModule, eval, Function}})
 * cannot reasonably be provided. Instead, under translation we expect
 * <ul>
 * <li>Not to have a binding for {@code "eval"} on
 *     {@code sharedImports}, just as we would not if
 *     {@code TAME_GLOBAL_EVAL} is false.
 * <li>The global {@code eval} seen by scripts is either unaltered (to
 *     work around the Chrome debugger bug if {@code TAME_GLOBAL_EVAL}
 *     is false), or is replaced by a function that throws an
 *     appropriate EvalError diagnostic (if {@code TAME_GLOBAL_EVAL}
 *     is true).
 * <li>The global {@code Function} constructor, both as seen by script
 *     code and evaled code, to throw an appropriate diagnostic.
 * <li>The {@code Q} API to always be available, to handle
 *     asynchronous, promise, and remote requests.
 * <li>The evaluating methods on {@code cajaVM} -- currently {@code
 *     compileExpr, compileModule, eval, and Function} -- to be remote
 *     promises for their normal interfaces, which therefore must be
 *     invoked with {@code Q.post}.
 * <li>Since {@code Q.post} can be used for asynchronously invoking
 *     non-promises, invocations like
 *     {@code Q.post(cajaVM, 'eval', ['2+3'])}, for example,
 *     will return a promise for a 5. This should work both under Caja
 *     translation and (TODO(erights)) under SES verification when
 *     {@code Q} is also installed, and so is the only portable
 *     evaluating API that SES code should use during this transition
 *     period.
 * <li>TODO(erights): {@code Q.post(cajaVM, 'compileModule',
 *     [moduleSrc]} should eventually pre-load the transitive
 *     synchronous dependencies of moduleSrc before resolving the
 *     promise for its result. It currently would not, instead
 *     requiring its client to do so manually.
 * </ul>
 */
var cajaVM;

/**
 * <p>{@code ses.startSES} should be called before any other potentially
 * dangerous script is executed in this frame.
 *
 * <p>If {@code ses.startSES} succeeds, the evaluation operations on
 * {@code cajaVM}, the global {@code Function} contructor, and perhaps
 * the {@code eval} function (see doc-comment on {@code eval} and
 * {@code cajaVM}) will only load code according to the <i>loader
 * isolation</i> rules of the object-capability model, suitable for
 * loading untrusted code. If all other (trusted) code executed
 * directly in this frame (i.e., other than through these safe
 * evaluation operations) takes care to uphold object-capability
 * rules, then untrusted code loaded via these safe evaluation
 * operations will be constrained by those rules. TODO(erights):
 * explain concretely what the trusted code must do or avoid doing to
 * uphold object-capability rules.
 *
 * <p>On a pre-ES5 platform, this script will fail cleanly, leaving
 * the frame intact. Otherwise, if this script fails, it may leave
 * this frame in an unusable state. All following description assumes
 * this script succeeds and that the browser conforms to the ES5
 * spec. The ES5 spec allows browsers to implement more than is
 * specified as long as certain invariants are maintained. We further
 * assume that these extensions are not maliciously designed to obey
 * the letter of these invariants while subverting the intent of the
 * spec. In other words, even on an ES5 conformant browser, we do not
 * presume to defend ourselves from a browser that is out to get us.
 *
 * @param global ::Record(any) Assumed to be the real global object
 *        for some frame. Since {@code ses.startSES} will allow global
 *        variable references that appear at the top level of the
 *        whitelist, our safety depends on these variables being
 *        frozen as a side effect of freezing the corresponding
 *        properties of {@code global}. These properties are also
 *        duplicated onto the virtual global objects which are
 *        provided as the {@code this} binding for the safe
 *        evaluation calls -- emulating the safe subset of the normal
 *        global object.
 *        TODO(erights): Currently, the code has only been tested when
 *        {@code global} is the global object of <i>this</i>
 *        frame. The code should be made to work for cross-frame use.
 * @param whitelist ::Record(Permit) where Permit = true | "*" |
 *        "skip" | Record(Permit).  Describes the subset of naming
 *        paths starting from {@code sharedImports} that should be
 *        accessible. The <i>accessible primordials</i> are all values
 *        found by navigating these paths starting from {@code
 *        sharedImports}. All non-whitelisted properties of accessible
 *        primordials are deleted, and then {@code sharedImports}
 *        and all accessible primordials are frozen with the
 *        whitelisted properties frozen as data properties.
 *        TODO(erights): fix the code and documentation to also
 *        support confined-ES5, suitable for confining potentially
 *        offensive code but not supporting defensive code, where we
 *        skip this last freezing step. With confined-ES5, each frame
 *        is considered a separate protection domain rather that each
 *        individual object.
 * @param atLeastFreeVarNames ::F([string], Record(true))
 *        Given the sourceText for a strict Program,
 *        atLeastFreeVarNames(sourceText) returns a Record whose
 *        enumerable own property names must include the names of all the
 *        free variables occuring in sourceText. It can include as
 *        many other strings as is convenient so long as it includes
 *        these. The value of each of these properties should be
 *        {@code true}. TODO(erights): On platforms with Proxies
 *        (currently only Firefox 4 and after), use {@code
 *        with(aProxy) {...}} to intercept free variables rather than
 *        atLeastFreeVarNames.
 * @param extensions ::F([], Record(any)]) A function returning a
 *        record whose own properties will be copied onto cajaVM. This
 *        is used for the optional components which bring SES to
 *        feature parity with the ES5/3 runtime at the price of larger
 *        code size. At the time that {@code startSES} calls {@code
 *        extensions}, {@code cajaVM} exists but should not yet be
 *        used. In particular, {@code extensions} should not call
 *        {@code cajaVM.def} during this setup, because def would then
 *        freeze priordials before startSES cleans them (removes
 *        non-whitelisted properties). The methods that
 *        {@code extensions} contributes can, of course, use
 *        {@code cajaVM}, since those methods will only be called once
 *        {@code startSES} finishes.
 */
ses.startSES = function(global,
                        whitelist,
                        atLeastFreeVarNames,
                        extensions) {
  "use strict";

  /////////////// KLUDGE SWITCHES ///////////////

  /////////////////////////////////
  // The following are only the minimal kludges needed for the current
  // Firefox or the current Chrome Beta. At the time of
  // this writing, these are Firefox 4.0 and Chrome 12.0.742.5 dev
  // As these move forward, kludges can be removed until we simply
  // rely on ES5.

  /**
   * <p>TODO(erights): isolate and report this.
   *
   * <p>Workaround for Chrome debugger's own use of 'eval'
   *
   * <p>This kludge is safety preserving but not semantics
   * preserving. When {@code TAME_GLOBAL_EVAL} is false, no {@code
   * sharedImports.eval} is available, and the 'eval' available as a
   * global to trusted (script) code is the original 'eval', and so is
   * not safe.
   */
  //var TAME_GLOBAL_EVAL = true;
  var TAME_GLOBAL_EVAL = false;

  /**
   * If this is true, then we redefine these to work around a
   * stratification bug in the Chrome debugger. To allow this, we have
   * also whitelisted these four properties in whitelist.js
   */
  //var EMULATE_LEGACY_GETTERS_SETTERS = false;
  var EMULATE_LEGACY_GETTERS_SETTERS = true;

  //////////////// END KLUDGE SWITCHES ///////////


  var dirty = true;

  var hop = Object.prototype.hasOwnProperty;

  var getProto = Object.getPrototypeOf;
  var defProp = Object.defineProperty;
  var gopd = Object.getOwnPropertyDescriptor;
  var gopn = Object.getOwnPropertyNames;
  var keys = Object.keys;
  var freeze = Object.freeze;
  var create = Object.create;

  /**
   * Use to tamper proof a function which is not intended to ever be
   * used as a constructor, since it nulls out the function's
   * prototype first.
   */
  function constFunc(func) {
    func.prototype = null;
    return freeze(func);
  }


  function fail(str) {
// CHEATING(jpolitz)
//    debugger;
    throw new EvalError(str);
  }

  if (typeof WeakMap === 'undefined') {
    fail('No built-in WeakMaps, so WeakMap.js must be loaded first');
  }


  if (EMULATE_LEGACY_GETTERS_SETTERS) {
    (function(){
      function legacyDefineGetter(sprop, getter) {
        sprop = '' + sprop;
        if (hop.call(this, sprop)) {
          defProp(this, sprop, { get: getter });
        } else {
          defProp(this, sprop, {
            get: getter,
            set: undefined,
            enumerable: true,
            configurable: true
          });
        }
      }
      legacyDefineGetter.prototype = null;
      defProp(Object.prototype, '__defineGetter__', {
        value: legacyDefineGetter,
        writable: false,
        enumerable: false,
        configurable: false
      });

      function legacyDefineSetter(sprop, setter) {
        sprop = '' + sprop;
        if (hop.call(this, sprop)) {
          defProp(this, sprop, { set: setter });
        } else {
          defProp(this, sprop, {
            get: undefined,
            set: setter,
            enumerable: true,
            configurable: true
          });
        }
      }
      legacyDefineSetter.prototype = null;
      defProp(Object.prototype, '__defineSetter__', {
        value: legacyDefineSetter,
        writable: false,
        enumerable: false,
        configurable: false
      });

      function legacyLookupGetter(sprop) {
        sprop = '' + sprop;
        var base = this, desc = void 0;
        while (base && !(desc = gopd(base, sprop))) { base = getProto(base); }
        return desc && desc.get;
      }
      legacyLookupGetter.prototype = null;
      defProp(Object.prototype, '__lookupGetter__', {
        value: legacyLookupGetter,
        writable: false,
        enumerable: false,
        configurable: false
      });

      function legacyLookupSetter(sprop) {
        sprop = '' + sprop;
        var base = this, desc = void 0;
        while (base && !(desc = gopd(base, sprop))) { base = getProto(base); }
        return desc && desc.set;
      }
      legacyLookupSetter.prototype = null;
      defProp(Object.prototype, '__lookupSetter__', {
        value: legacyLookupSetter,
        writable: false,
        enumerable: false,
        configurable: false
      });
    })();
  } else {
    delete Object.prototype.__defineGetter__;
    delete Object.prototype.__defineSetter__;
    delete Object.prototype.__lookupGetter__;
    delete Object.prototype.__lookupSetter__;
  }


  /**
   * By this time, WeakMap has already monkey patched Object.freeze if
   * necessary, so we can do the tamperProofing delayed from
   * repairES5.js
   */
  var tamperProof = ses.makeDelayedTamperProof();

  /**
   * Code being eval'ed by {@code cajaVM.eval} sees {@code
   * sharedImports} as its top-level {@code this}, as if {@code
   * sharedImports} were the global object.
   *
   * <p>{@code sharedImports}'s properties are exactly the whitelisted
   * global variable references. These properties, both as they appear
   * on the global object and on this {@code sharedImports} object,
   * are frozen and so cannot diverge. This preserves the illusion.
   *
   * <p>For code being evaluated by {@code cajaVM.compileExpr} and its
   * ilk, the {@code imports} provided to the compiled function is bound
   * to the top-level {@code this} of the evaluated code. For sanity,
   * this {@code imports} should first be initialized with a copy of the
   * properties of {@code sharedImports}, but nothing enforces this.
   */
  var sharedImports = create(null);

  (function startSESPrelude() {

    /**
     * The unsafe* variables hold precious values that must not escape
     * to untrusted code. When {@code eval} is invoked via {@code
     * unsafeEval}, this is a call to the indirect eval function, not
     * the direct eval operator.
     */
    var unsafeEval = eval;
    var UnsafeFunction = Function;

    /**
     * Fails if {@code programSrc} does not parse as a strict Program
     * production, or, almost equivalently, as a FunctionBody
     * production.
     *
     * <p>We use Crock's trick of simply passing {@code programSrc} to
     * the original {@code Function} constructor, which will throw a
     * SyntaxError if it does not parse as a FunctionBody. We used to
     * use Ankur's trick (need link) which is more correct, in that it
     * will throw if {@code programSrc} does not parse as a Program
     * production, which is the relevant question. However, the
     * difference -- whether return statements are accepted -- does
     * not matter for our purposes. And testing reveals that Crock's
     * trick executes over 100x faster on V8.
     */
    function verifyStrictProgram(programSrc) {
      try {
        UnsafeFunction('"use strict";' + programSrc);
      } catch (err) {
        // debugger; // Useful for debugging -- to look at programSrc
        throw err;
      }
    }

    /**
     * Fails if {@code exprSource} does not parse as a strict
     * Expression production.
     *
     * <p>To verify that exprSrc parses as a strict Expression, we
     * verify that (when followed by ";") it parses as a strict
     * Program, and that when surrounded with parens it still parses
     * as a strict Program. We place a newline before the terminal
     * token so that a "//" comment cannot suppress the close paren.
     */
    function verifyStrictExpression(exprSrc) {
      verifyStrictProgram(exprSrc + ';');
      verifyStrictProgram('( ' + exprSrc + '\n);');
    }

    /**
     * Make a virtual global object whose initial own properties are
     * a copy of the own properties of {@code sharedImports}.
     *
     * <p>Further uses of {@code copyToImports} to copy properties
     * onto this imports object will overwrite, effectively shadowing
     * the {@code sharedImports}. You should shadow by overwriting
     * rather than inheritance so that shadowing makes the original
     * binding inaccessible.
     *
     * <p>The returned imports object is extensible and all its
     * properties are configurable and non-enumerable. Once fully
     * initialized, the caller can of course freeze the imports
     * objects if desired. A reason not to do so it to emulate
     * traditional JavaScript intermodule linkage by side effects to a
     * shared (virtual) global object.
     *
     * <p>See {@code copyToImports} for the precise semantic of the
     * property copying.
     */
    function makeImports() {
      var imports = create(null);
      copyToImports(imports, sharedImports);
      return imports;
    }

    /**
     * For all the own properties of {@code from}, copy their
     * descriptors to {@code imports}, except that each property
     * added to {@code imports} is unconditionally configurable
     * and non-enumerable.
     *
     * <p>By copying descriptors rather than values, any accessor
     * properties of {@code env} become accessors of {@code imports}
     * with the same getter and setter. If these do not use their
     * {@code this} value, then the original and any copied properties
     * are effectively joined. If the getter/setter do use their
     * {@code this}, when accessed with {@code imports} as the base,
     * their {@code this} will be bound to the {@code imports} rather
     * than {@code from}. If {@code from} contains writable value
     * properties, this will copy the current value of the property,
     * after which they may diverge.
     *
     * <p>We make these configurable so that {@code imports} can
     * be further configured before being frozen. We make these
     * non-enumerable in order to emulate the normal behavior of
     * built-in properties of typical global objects, such as the
     * browser's {@code window} object.
     */
    function copyToImports(imports, from) {
      gopn(from).forEach(function(name) {
        var desc = gopd(from, name);
        desc.enumerable = false;
        desc.configurable = true;
        defProp(imports, name, desc);
      });
      return imports;
    }

    /**
     * Make a frozen scope object which reflects all access onto
     * {@code imports}, for use by {@code with} to prevent
     * access to any {@code freeNames} other than those found on the.
     * {@code imports}.
     */
    function makeScopeObject(imports, freeNames) {
      var scopeObject = create(null);
      // Note: Although this loop is a bottleneck on some platforms,
      // it does not help to turn it into a for(;;) loop, since we
      // still need an enclosing function per accessor property
      // created, to capture its own unique binding of
      // "name". (Embarrasing fact: despite having often written about
      // this very danger, I engaged in this mistake in a misbegotten
      // optimization attempt here.)
      freeNames.forEach(function interceptName(name) {
        var desc = gopd(imports, name);
        if (!desc || desc.writable !== false || desc.configurable) {
          // If there is no own property, or it isn't a non-writable
          // value property, or it is configurable. Note that this
          // case includes accessor properties. The reason we wrap
          // rather than copying over getters and setters is so the
          // this-binding of the original getters and setters will be
          // the imports rather than the scopeObject.
          desc = {
            get: function scopedGet() {
              if (name in imports) {
                var result = imports[name];
                if (typeof result === 'function') {
                  // If it were possible to know that the getter call
                  // was on behalf of a simple function call to the
                  // gotten function, we could instead return that
                  // function as bound to undefined. Unfortunately,
                  // without parsing (or possibly proxies?), that isn't
                  // possible.
                }
                return result;
              }
              // if it were possible to know that the getter call was on
              // behalf of a typeof expression, we'd return the string
              // "undefined" here instead. Unfortunately, without
              // parsing or proxies, that isn't possible.
              throw new ReferenceError('"' + name + '" not in scope');
            },
            set: function scopedSet(newValue) {
              if (name in imports) {
                imports[name] = newValue;
              }
              throw new TypeError('Cannot set "' + name + '"');
            },
            enumerable: false
          };
        }
        desc.enumerable = false;
        defProp(scopeObject, name, desc);
      });
      return freeze(scopeObject);
    }


    /**
     * Given SES source text that must not be run directly using any
     * of the built-in unsafe evaluators on this platform, we instead
     * surround it with a prelude and postlude.
     *
     * <p>Evaluating the resulting expression return a function that
     * <i>can</i>be called to execute the original expression safely,
     * in a controlled scope. See "makeCompiledExpr" for precisely the
     * pattern that must be followed to call the resulting function
     * safely.
     *
     * Notice that the source text placed around {@code exprSrc}
     * <ul>
     * <li>brings no variable names into scope, avoiding any
     *     non-hygienic name capture issues, and
     * <li>does not introduce any newlines preceding exprSrc, so
     *     that all line number which a debugger might report are
     *     accurate wrt the original source text. And except for the
     *     first line, all the column numbers are accurate too.
     * </ul>
     *
     * <p>TODO(erights): Find out if any platforms have any way to
     * associate a file name and line number with eval'ed text, so
     * that we can do something useful with the optional {@code
     * opt_sourcePosition} to better support debugging.
     */
    function securableWrapperSrc(exprSrc, opt_sourcePosition) {
      verifyStrictExpression(exprSrc);

      return '(function() { ' +
        // non-strict code, where this === scopeObject
        '  with (this) { ' +
        '    return function() { ' +
        '      "use strict"; ' +
        '      return ( ' +
        // strict code, where this === imports
        '        ' + exprSrc + '\n' +
        '      );\n' +
        '    };\n' +
        '  }\n' +
        '})';
    }
    ses.securableWrapperSrc = securableWrapperSrc;


    /**
     * Given a wrapper function, such as the result of evaluating the
     * source that securableWrapperSrc returns, and a list of all the
     * names that we want to intercept to redirect to the imports,
     * return a corresponding <i>compiled expr</i> function.
     *
     * <p>A compiled expr function, when called on an imports
     * object, evaluates the original expression in a context where
     * all its free variable references that appear in freeNames are
     * redirected to the corresponding property of imports.
     */
    function makeCompiledExpr(wrapper, freeNames) {
      if (dirty) { fail('Initial cleaning failed'); }

      function compiledCode(imports) {
        var scopeObject = makeScopeObject(imports, freeNames);
        return wrapper.call(scopeObject).call(imports);
      };
      compiledCode.prototype = null;
      return compiledCode;
    }
    ses.makeCompiledExpr = makeCompiledExpr;

    /**
     * Compiles {@code exprSrc} as a strict expression into a function
     * of an {@code imports}, that when called evaluates {@code
     * exprSrc} in a virtual global environment whose {@code this} is
     * bound to that {@code imports}, and whose free variables
     * refer only to the properties of that {@code imports}.
     *
     * <p>When SES is provided primitively, it should provide an
     * analogous {@code compileProgram} function that accepts a
     * Program and return a function that evaluates it to the
     * Program's completion value. Unfortunately, this is not
     * practical as a library without some non-standard support from
     * the platform such as a parser API that provides an AST.
     *
     * <p>Thanks to Mike Samuel and Ankur Taly for this trick of using
     * {@code with} together with RegExp matching to intercept free
     * variable access without parsing.
     */
    function compileExpr(exprSrc, opt_sourcePosition) {
      var wrapperSrc = securableWrapperSrc(exprSrc, opt_sourcePosition);
      var wrapper = unsafeEval(wrapperSrc);
      var freeNames = atLeastFreeVarNames(exprSrc);
      var result = makeCompiledExpr(wrapper, freeNames);
      return freeze(result);
    }


    var directivePattern = (/^['"](?:\w|\s)*['"]$/m);

    /**
     * A stereotyped form of the CommonJS require statement.
     */
    var requirePattern = (/^(?:\w*\s*(?:\w|\$|\.)*\s*=)?\s*require\s*\(\s*['"]((?:\w|\$|\.|\/)+)['"]\s*\)$/m);

    /**
     * As an experiment, recognize a stereotyped prelude of the
     * CommonJS module system.
     */
    function getRequirements(modSrc) {
      var result = [];
      var stmts = modSrc.split(';');
      var stmt;
      var i = 0, ilen = stmts.length;
      for (; i < ilen; i++) {
        stmt = stmts[i].trim();
        if (stmt !== '') {
          if (!directivePattern.test(stmt)) { break; }
        }
      }
      for (; i < ilen; i++) {
        stmt = stmts[i].trim();
        if (stmt !== '') {
          var m = requirePattern.exec(stmt);
          if (!m) { break; }
          result.push(m[1]);
        }
      }
      return freeze(result);
    }

    /**
     * A module source is actually any valid FunctionBody, and thus
     * any valid Program.
     *
     * <p>In addition, in case the module source happens to begin with
     * a streotyped prelude of the CommonJS module system, the
     * function resulting from module compilation has an additional
     * {@code "requirements"} property whose value is a list of the
     * module names being required by that prelude. These requirements
     * are the module's "immediate synchronous dependencies".
     *
     * <p>This {@code "requirements"} property is adequate to
     * bootstrap support for a CommonJS module system, since a loader
     * can first load and compile the transitive closure of an initial
     * module's synchronous depencies before actually executing any of
     * these module functions.
     *
     * <p>With a similarly lightweight RegExp, we should be able to
     * similarly recognize the {@code "load"} syntax of <a href=
     * "http://wiki.ecmascript.org/doku.php?id=strawman:simple_modules#syntax"
     * >Sam and Dave's module proposal for ES-Harmony</a>. However,
     * since browsers do not currently accept this syntax,
     * {@code getRequirements} above would also have to extract these
     * from the text to be compiled.
     */
    function compileModule(modSrc, opt_sourcePosition) {
      var exprSrc = '(function() {' + modSrc + '}).call(this)';

      // Follow the pattern in compileExpr
      var wrapperSrc = securableWrapperSrc(exprSrc, opt_sourcePosition);
      var wrapper = unsafeEval(wrapperSrc);
      var freeNames = atLeastFreeVarNames(exprSrc);
      var moduleMaker = makeCompiledExpr(wrapper, freeNames);

      moduleMaker.requirements = getRequirements(modSrc);
      return freeze(moduleMaker);
    }

    /**
     * A safe form of the {@code Function} constructor, which
     * constructs strict functions that can only refer freely to the
     * {@code sharedImports}.
     *
     * <p>The returned function is strict whether or not it declares
     * itself to be.
     */
    function FakeFunction(var_args) {
      var params = [].slice.call(arguments, 0);
      var body = params.pop();
      body = String(body || '');
      params = params.join(',');
      var exprSrc = '(function(' + params + '\n){' + body + '})';
      return compileExpr(exprSrc)(sharedImports);
    }
    FakeFunction.prototype = UnsafeFunction.prototype;
    FakeFunction.prototype.constructor = FakeFunction;
    global.Function = FakeFunction;

    /**
     * A safe form of the indirect {@code eval} function, which
     * evaluates {@code src} as strict code that can only refer freely
     * to the {@code sharedImports}.
     *
     * <p>Given our parserless methods of verifying untrusted sources,
     * we unfortunately have no practical way to obtain the completion
     * value of a safely evaluated Program. Instead, we adopt a
     * compromise based on the following observation. All Expressions
     * are valid Programs, and all Programs are valid
     * FunctionBodys. If {@code src} parses as a strict expression,
     * then we evaluate it as an expression and correctly return its
     * completion value, since that is simply the value of the
     * expression.
     *
     * <p>Otherwise, we evaluate {@code src} as a FunctionBody and
     * return what that would return from its implicit enclosing
     * function. If {@code src} is simply a Program, then it would not
     * have an explicit {@code return} statement, and so we fail to
     * return its completion value.
     *
     * <p>When SES {@code eval} is provided primitively, it should
     * accept a Program and evaluate it to the Program's completion
     * value. Unfortunately, this is not possible on ES5 without
     * parsing.
     */
    function fakeEval(src) {
      try {
        verifyStrictExpression(src);
      } catch (x) {
        src = '(function() {' + src + '\n}).call(this)';
      }
      return compileExpr(src)(sharedImports);
    }

    if (TAME_GLOBAL_EVAL) {
      global.eval = fakeEval;
    }

    var defended = WeakMap();
    var defending = WeakMap();
    /**
     * To define a defended object is to tamperProof it and all objects
     * transitively reachable from it via transitive reflective
     * property and prototype traversal.
     */
    function def(node) {
      var defendingList = [];
      function recur(val) {
        if (!val) { return; }
        var t = typeof val;
        if (t === 'number' || t === 'string' || t === 'boolean') { return; }
        if (defended.get(val) || defending.get(val)) { return; }
        defending.set(val, true);
        defendingList.push(val);

        tamperProof(val);

        recur(getProto(val));

        // How to optimize? This is a performance sensitive loop, but
        // forEach seems to be faster on Chrome 18 Canary but a
        // for(;;) loop seems better on FF 12 Nightly.
        gopn(val).forEach(function(p) {
          if (typeof val === 'function' &&
              (p === 'caller' || p === 'arguments')) {
            return;
          }
          var desc = gopd(val, p);
          recur(desc.value);
          recur(desc.get);
          recur(desc.set);
        });
      }
      try {
        recur(node);
      } catch (err) {
        defending = WeakMap();
        throw err;
      }
      defendingList.forEach(function(obj) {
        defended.set(obj, true);
      });
      return node;
    }


    /**
     * makeArrayLike() produces a constructor for the purpose of
     * taming things like nodeLists.  The result, ArrayLike, takes an
     * instance of ArrayLike and two functions, getItem and getLength,
     * which put it in a position to do taming on demand.
     *
     * <p>The constructor returns a new object that inherits from the
     * {@code proto} passed in.
     */
    var makeArrayLike;
    (function() {
      var itemMap = WeakMap(), lengthMap = WeakMap();
      function lengthGetter() {
        var getter = lengthMap.get(this);
        return getter ? getter() : void 0;
      }
      constFunc(lengthGetter);

      var nativeProxies = global.Proxy && (function () {
        var obj = {0: 'hi'};
        var p = global.Proxy.create({
          get: function () {
            var P = arguments[0];
            if (typeof P !== 'string') { P = arguments[1]; }
            return obj[P];
          }
        });
        return p[0] === 'hi';
      })();
      if (nativeProxies) {
        (function () {
          function ArrayLike(proto, getItem, getLength) {
            if (typeof proto !== 'object') {
              throw new TypeError('Expected proto to be an object.');
            }
            if (!(proto instanceof ArrayLike)) {
              throw new TypeError('Expected proto to be instanceof ArrayLike.');
            }
            var obj = create(proto);
            itemMap.set(obj, getItem);
            lengthMap.set(obj, getLength);
            return obj;
          }

          function ownPropDesc(P) {
            P = '' + P;
            if (P === 'length') {
              return { get: lengthGetter };
            } else if (typeof P === 'number' || P === '' + (+P)) {
              return {
                get: constFunc(function() {
                  var getter = itemMap.get(this);
                  return getter ? getter(+P) : void 0;
                }),
                enumerable: true,
                configurable: true
              };
            }
            return void 0;
          }
          function propDesc(P) {
            var opd = ownPropDesc(P);
            if (opd) {
              return opd;
            } else {
              return gopd(Object.prototype, P);
            }
          }
          function has(P) {
            P = '' + P;
            return (P === 'length') ||
                (typeof P === 'number') ||
                (P === '' + +P) ||
                (P in Object.prototype);
          }
          function hasOwn(P) {
            P = '' + P;
            return (P === 'length') ||
                (typeof P === 'number') ||
                (P === '' + +P);
          }
          function getPN() {
            var result = getOwnPN ();
            var objPropNames = gopn(Object.prototype);
            result.push.apply(result, objPropNames);
            return result;
          }
          function getOwnPN() {
            var lenGetter = lengthMap.get(this);
            if (!lenGetter) { return void 0; }
            var len = lenGetter();
            var result = ['length'];
            for (var i = 0; i < len; ++i) {
              result.push('' + i);
            }
            return result;
          };
          function del(P) {
            P = '' + P;
            if ((P === 'length') || ('' + +P === P)) { return false; }
            return true;
          }

          ArrayLike.prototype = global.Proxy.create({
            getPropertyDescriptor: propDesc,
            getOwnPropertyDescriptor: ownPropDesc,
            has: has,
            hasOwn: hasOwn,
            getPropertyNames: getPN,
            getOwnPropertyNames: getOwnPN,
            'delete': del,
            fix: function() { return void 0; }
          }, Object.prototype);
          tamperProof(ArrayLike);
          makeArrayLike = function() { return ArrayLike; };
        })();
      } else {
        (function() {
          // Make BiggestArrayLike.prototype be an object with a fixed
          // set of numeric getters.  To tame larger lists, replace
          // BiggestArrayLike and its prototype using
          // makeArrayLike(newLength).

          // See
          // http://graphics.stanford.edu/~seander/bithacks.html#RoundUpPowerOf2
          function nextUInt31PowerOf2(v) {
            v &= 0x7fffffff;
            v |= v >> 1;
            v |= v >> 2;
            v |= v >> 4;
            v |= v >> 8;
            v |= v >> 16;
            return v + 1;
          }

          // The current function whose prototype has the most numeric getters.
          var BiggestArrayLike = void 0;
          var maxLen = 0;
          makeArrayLike = function(length) {
            if (!BiggestArrayLike || length > maxLen) {
              var len = nextUInt31PowerOf2(length);
              // Create a new ArrayLike constructor to replace the old one.
              var BAL = function(proto, getItem, getLength) {
                if (typeof(proto) !== 'object') {
                  throw new TypeError('Expected proto to be an object.');
                }
                if (!(proto instanceof BAL)) {
                  throw new TypeError(
                      'Expected proto to be instanceof ArrayLike.');
                }
                var obj = create(proto);
                itemMap.set(obj, getItem);
                lengthMap.set(obj, getLength);
                return obj;
              };
              // Install native numeric getters.
              for (var i = 0; i < len; i++) {
                (function(j) {
                  function get() {
                    return itemMap.get(this)(j);
                  }
                  defProp(BAL.prototype, j, {
                    get: constFunc(get),
                    enumerable: true
                  });
                })(i);
              }
              // Install native length getter.
              defProp(BAL.prototype, 'length', { get: lengthGetter });
              // TamperProof and cache the result
              tamperProof(BAL);
              tamperProof(BAL.prototype);
              BiggestArrayLike = BAL;
              maxLen = len;
            }
            return BiggestArrayLike;
          };
        })();
      }
    })();

    global.cajaVM = { // don't freeze here

      /**
       * This is about to be deprecated once we expose ses.logger.
       *
       * <p>In the meantime, privileged code should use ses.logger.log
       * instead of cajaVM.log.
       */
      log: constFunc(function log(str) {
        if (typeof console !== 'undefined' && 'log' in console) {
          // We no longer test (typeof console.log === 'function') since,
          // on IE9 and IE10preview, in violation of the ES5 spec, it
          // is callable but has typeof "object". See
          // https://connect.microsoft.com/IE/feedback/details/685962/
          //   console-log-and-others-are-callable-but-arent-typeof-function
          console.log(str);
        }
      }),
      tamperProof: constFunc(tamperProof),
      constFunc: constFunc(constFunc),
      // def: see below
      is: constFunc(ses.is),

      compileExpr: constFunc(compileExpr),
      compileModule: constFunc(compileModule),
      // compileProgram: compileProgram, // Cannot be implemented in ES5.1.
      eval: fakeEval,               // don't freeze here
      Function: FakeFunction,       // don't freeze here,

      sharedImports: sharedImports, // don't freeze here
      makeImports: constFunc(makeImports),
      copyToImports: constFunc(copyToImports),

      makeArrayLike: constFunc(makeArrayLike)
    };
    var extensionsRecord = extensions();
    gopn(extensionsRecord).forEach(function (p) {
      defProp(cajaVM, p,
              gopd(extensionsRecord, p));
    });

    // Move this down here so it is not available during the call to
    // extensions().
    global.cajaVM.def = constFunc(def);

  })();

  var propertyReports = {};

  /**
   * Report how a property manipulation went.
   */
  function reportProperty(severity, status, path) {
    ses.updateMaxSeverity(severity);
    var group = propertyReports[status] || (propertyReports[status] = {
      severity: severity,
      list: []
    });
    group.list.push(path);
  }

  /**
   * Initialize accessible global variables and {@code sharedImports}.
   *
   * For each of the whitelisted globals, we read its value, freeze
   * that global property as a data property, and mirror that property
   * with a frozen data property of the same name and value on {@code
   * sharedImports}, but always non-enumerable. We make these
   * non-enumerable since ES5.1 specifies that all these properties
   * are non-enumerable on the global object.
   */
  keys(whitelist).forEach(function(name) {
    var desc = gopd(global, name);
    if (desc) {
      var permit = whitelist[name];
      if (permit) {
        var newDesc = {
          value: global[name],
          writable: false,
          configurable: false
        };
        try {
          defProp(global, name, newDesc);
        } catch (err) {
          reportProperty(ses.severities.NEW_SYMPTOM,
                         'Global ' + name + ' cannot be made readonly: ' + err);
        }
        defProp(sharedImports, name, newDesc);
      }
    }
  });
  if (TAME_GLOBAL_EVAL) {
    defProp(sharedImports, 'eval', {
      value: cajaVM.eval,
      writable: false,
      enumerable: false,
      configurable: false
    });
  }

  /**
   * The whiteTable should map from each path-accessible primordial
   * object to the permit object that describes how it should be
   * cleaned.
   *
   * We initialize the whiteTable only so that {@code getPermit} can
   * process "*" and "skip" inheritance using the whitelist, by
   * walking actual superclass chains.
   */
  var whiteTable = WeakMap();
  function register(value, permit) {
    if (value !== Object(value)) { return; }
    if (typeof permit !== 'object') {
      return;
    }
    var oldPermit = whiteTable.get(value);
    if (oldPermit) {
      fail('primordial reachable through multiple paths');
    }
    whiteTable.set(value, permit);
    keys(permit).forEach(function(name) {
      if (permit[name] !== 'skip') {
        var sub = value[name];
        register(sub, permit[name]);
      }
    });
  }
  register(sharedImports, whitelist);

  /**
   * Should the property named {@code name} be whitelisted on the
   * {@code base} object, and if so, with what Permit?
   *
   * <p>If it should be permitted, return the Permit (where Permit =
   * true | "*" | "skip" | Record(Permit)), all of which are
   * truthy. If it should not be permitted, return false.
   */
  function getPermit(base, name) {
    var permit = whiteTable.get(base);
    if (permit) {
      if (hop.call(permit, name)) { return permit[name]; }
    }
    while (true) {
      base = getProto(base);
      if (base === null) { return false; }
      permit = whiteTable.get(base);
      if (permit && hop.call(permit, name)) {
        var result = permit[name];
        if (result === '*' || result === 'skip') {
          return result;
        } else {
          return false;
        }
      }
    }
  }

  var cleaning = WeakMap();

  /**
   * Delete the property if possible, else try to poison.
   */
  function cleanProperty(base, name, path) {
    function poison() {
      throw new TypeError('Cannot access property ' + path);
    }
    var diagnostic;

    if (typeof base === 'function') {
      if (name === 'caller') {
        diagnostic = ses.makeCallerHarmless(base, path);
        // We can use a severity of SAFE here since if this isn't
        // safe, it is the responsibility of repairES5.js to tell us
        // so. All the same, we should inspect the reports on all
        // platforms we care about to see if there are any surprises.
        reportProperty(ses.severities.SAFE,
                       diagnostic, path);
        return true;
      }
      if (name === 'arguments') {
        diagnostic = ses.makeArgumentsHarmless(base, path);
        // We can use a severity of SAFE here since if this isn't
        // safe, it is the responsibility of repairES5.js to tell us
        // so. All the same, we should inspect the reports on all
        // platforms we care about to see if there are any surprises.
        reportProperty(ses.severities.SAFE,
                       diagnostic, path);
        return true;
      }
    }

    var deleted = void 0;
    var err = void 0;
    try {
      deleted = delete base[name];
    } catch (er) { err = er; }
    var exists = hop.call(base, name);
    if (deleted) {
      if (!exists) {
        reportProperty(ses.severities.SAFE,
                       'Deleted', path);
        return true;
      }
      reportProperty(ses.severities.SAFE_SPEC_VIOLATION,
                     'Bounced back', path);
    } else if (deleted === false) {
      reportProperty(ses.severities.SAFE_SPEC_VIOLATION,
                     'Strict delete returned false rather than throwing', path);
    } else if (err instanceof TypeError) {
      // This is the normal abnormal case, so leave it to the next
      // section to emit a diagnostic.
      //
      // reportProperty(ses.severities.SAFE_SPEC_VIOLATION,
      //                'Cannot be deleted', path);
    } else {
      reportProperty(ses.severities.NEW_SYMPTOM,
                     'Delete failed with' + err, path);
    }

    try {
      defProp(base, name, {
        get: poison,
        set: poison,
        enumerable: false,
        configurable: false
      });
    } catch (cantPoisonErr) {
      try {
        // Perhaps it's writable non-configurable, in which case we
        // should still be able to freeze it in a harmless state.
        var value = gopd(base, name).value;
        defProp(base, name, {
          value: value === null ? null : void 0,
          writable: false,
          configurable: false
        });
      } catch (cantFreezeHarmless) {
        reportProperty(ses.severities.NOT_ISOLATED,
                       'Cannot be poisoned', path);
        return false;
      }
    }
    var desc2 = gopd(base, name);
    if (desc2.get === poison &&
        desc2.set === poison &&
        !desc2.configurable) {
      try {
        var dummy2 = base[name];
      } catch (expectedErr) {
        if (expectedErr instanceof TypeError) {
          reportProperty(ses.severities.SAFE,
                         'Successfully poisoned', path);
          return true;
        }
      }
    } else if ((desc2.value === void 0 || desc2.value === null) &&
               !desc2.writable &&
               !desc2.configurable) {
      reportProperty(ses.severities.SAFE,
                     'Frozen harmless', path);
      return false;
    }
    reportProperty(ses.severities.NEW_SYMTOM,
                   'Failed to be poisoned', path);
    return false;
  }

  /**
   * Assumes all super objects are otherwise accessible and so will be
   * independently cleaned.
   */
  function clean(value, prefix) {
    if (value !== Object(value)) { return; }
    if (cleaning.get(value)) { return; }
    cleaning.set(value, true);
    gopn(value).forEach(function(name) {
      var path = prefix + (prefix ? '.' : '') + name;
      var p = getPermit(value, name);
      if (p) {
        if (p === 'skip') {
          reportProperty(ses.severities.SAFE,
                         'Skipped', path);
        } else {
          var sub = value[name];
          clean(sub, path);
        }
      } else {
        cleanProperty(value, name, path);
      }
    });
  }
  clean(sharedImports, '');

  /**
   * This protection is now gathered here, so that a future version
   * can skip it for non-defensive frames that must only be confined.
   */
  cajaVM.def(sharedImports);

  keys(propertyReports).sort().forEach(function(status) {
    var group = propertyReports[status];
    ses.logger.reportDiagnosis(group.severity, status, group.list);
  });

  ses.logger.reportMax();

  if (ses.ok()) {
    // We succeeded. Enable safe Function, eval, and compile* to work.
    dirty = false;
    ses.logger.log('initSES succeeded.');
  } else {
    ses.logger.error('initSES failed.');
  }
};
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview
 * This is a pure-ES5 implementation of ejectors, guards, and trademarks as
 * otherwise provided by ES5/3. It is incorporated into the cajaVM object by
 * hookupSESPlus.js.
 *
 * <p>Assumes ES5. Compatible with ES5-strict.
 *
 * // provides ses.ejectorsGuardsTrademarks
 * @author kpreid@switchb.org
 * @requires WeakMap, cajaVM
 * @overrides ses, ejectorsGuardsTrademarksModule
 */
var ses;

(function ejectorsGuardsTrademarksModule(){
  "use strict";

  ses.ejectorsGuardsTrademarks = function ejectorsGuardsTrademarks() {

    /**
     * During the call to {@code ejectorsGuardsTrademarks}, {@code
     * ejectorsGuardsTrademarks} must not call {@code cajaVM.def},
     * since startSES.js has not yet finished cleaning things. See the
     * doc-comments on the {@code extensions} parameter of
     * startSES.js.
     *
     * <p>Instead, we define here some conveniences for freezing just
     * enough without prematurely freezing primodial objects
     * transitively reachable from these.
     */
    var freeze = Object.freeze;
    var constFunc = cajaVM.constFunc;


    /**
     * Returns a new object whose only utility is its identity and (for
     * diagnostic purposes only) its name.
     */
    function Token(name) {
      name = '' + name;
      return freeze({
        toString: constFunc(function tokenToString() {
          return name;
        })
      });
    }


    ////////////////////////////////////////////////////////////////////////
    // Ejectors
    ////////////////////////////////////////////////////////////////////////

    /**
     * One-arg form is known in scheme as "call with escape
     * continuation" (call/ec).
     *
     * <p>In this analogy, a call to {@code callWithEjector} emulates a
     * labeled statement. The ejector passed to the {@code attemptFunc}
     * emulates the label part. The {@code attemptFunc} itself emulates
     * the statement being labeled. And a call to {@code eject} with
     * this ejector emulates the return-to-label statement.
     *
     * <p>We extend the normal notion of call/ec with an
     * {@code opt_failFunc} in order to give more the sense of a
     * {@code try/catch} (or similarly, the {@code escape} special
     * form in E). The {@code attemptFunc} is like the {@code try}
     * clause and the {@code opt_failFunc} is like the {@code catch}
     * clause. If omitted, {@code opt_failFunc} defaults to the
     * {@code identity} function.
     *
     * <p>{@code callWithEjector} creates a fresh ejector -- a one
     * argument function -- for exiting from this attempt. It then calls
     * {@code attemptFunc} passing that ejector as argument. If
     * {@code attemptFunc} completes without calling the ejector, then
     * this call to {@code callWithEjector} completes
     * likewise. Otherwise, if the ejector is called with an argument,
     * then {@code opt_failFunc} is called with that argument. The
     * completion of {@code opt_failFunc} is then the completion of the
     * {@code callWithEjector} as a whole.
     *
     * <p>The ejector stays live until {@code attemptFunc} is exited,
     * at which point the ejector is disabled. Calling a disabled
     * ejector throws.
     *
     * <p>Historic note: This was first invented by John C. Reynolds in
     * <a href="http://doi.acm.org/10.1145/800194.805852"
     * >Definitional interpreters for higher-order programming
     * languages</a>. Reynold's invention was a special form as in E,
     * rather than a higher order function as here and in call/ec.
     */
    function callWithEjector(attemptFunc, opt_failFunc) {
      var failFunc = opt_failFunc || function (x) { return x; };
      var disabled = false;
      var token = new Token('ejection');
      var stash = void 0;
      function ejector(result) {
        if (disabled) {
          throw new Error('ejector disabled');
        } else {
          // don't disable here.
          stash = result;
          throw token;
        }
      }
      constFunc(ejector);
      try {
        try {
          return attemptFunc(ejector);
        } finally {
          disabled = true;
        }
      } catch (e) {
        if (e === token) {
          return failFunc(stash);
        } else {
          throw e;
        }
      }
    }

    /**
     * Safely invokes {@code opt_ejector} with {@code result}.
     * <p>
     * If {@code opt_ejector} is falsy, disabled, or returns
     * normally, then {@code eject} throws. Under no conditions does
     * {@code eject} return normally.
     */
    function eject(opt_ejector, result) {
      if (opt_ejector) {
        opt_ejector(result);
        throw new Error('Ejector did not exit: ', opt_ejector);
      } else {
        throw new Error(result);
      }
    }

    ////////////////////////////////////////////////////////////////////////
    // Sealing and Unsealing
    ////////////////////////////////////////////////////////////////////////

    function makeSealerUnsealerPair() {
      var boxValues = new WeakMap(true); // use key lifetime

      function seal(value) {
        var box = freeze({});
        boxValues.set(box, value);
        return box;
      }
      function optUnseal(box) {
        return boxValues.has(box) ? [boxValues.get(box)] : null;
      }
      function unseal(box) {
        var result = optUnseal(box);
        if (result === null) {
          throw new Error("That wasn't one of my sealed boxes!");
        } else {
          return result[0];
        }
      }
      return freeze({
        seal: constFunc(seal),
        unseal: constFunc(unseal),
        optUnseal: constFunc(optUnseal)
      });
    }


    ////////////////////////////////////////////////////////////////////////
    // Trademarks
    ////////////////////////////////////////////////////////////////////////

    var stampers = new WeakMap(true);

    /**
     * Internal routine for making a trademark from a table.
     *
     * <p>To untangle a cycle, the guard made by {@code makeTrademark}
     * is not yet stamped. The caller of {@code makeTrademark} must
     * stamp it before allowing the guard to escape.
     *
     * <p>Note that {@code makeTrademark} is called during the call to
     * {@code ejectorsGuardsTrademarks}, and so must not call {@code
     * cajaVM.def}.
     */
    function makeTrademark(typename, table) {
      typename = '' + typename;

      var stamp = freeze({
        toString: constFunc(function() { return typename + 'Stamp'; })
      });

      stampers.set(stamp, function(obj) {
        table.set(obj, true);
        return obj;
      });

      return freeze({
        toString: constFunc(function() { return typename + 'Mark'; }),
        stamp: stamp,
        guard: freeze({
          toString: constFunc(function() { return typename + 'T'; }),
          coerce: constFunc(function(specimen, opt_ejector) {
            if (!table.get(specimen)) {
              eject(opt_ejector,
                    'Specimen does not have the "' + typename + '" trademark');
            }
            return specimen;
          })
        })
      });
    }

    /**
     * Objects representing guards should be marked as such, so that
     * they will pass the {@code GuardT} guard.
     * <p>
     * {@code GuardT} is generally accessible as
     * {@code cajaVM.GuardT}. However, {@code GuardStamp} must not be
     * made generally accessible, but rather only given to code trusted
     * to use it to deem as guards things that act in a guard-like
     * manner: A guard MUST be immutable and SHOULD be idempotent. By
     * "idempotent", we mean that<pre>
     *     var x = g(specimen, ej); // may fail
     *     // if we're still here, then without further failure
     *     g(x) === x
     * </pre>
     */
    var GuardMark = makeTrademark('Guard', new WeakMap());
    var GuardT = GuardMark.guard;
    var GuardStamp = GuardMark.stamp;
    stampers.get(GuardStamp)(GuardT);

    /**
     * The {@code Trademark} constructor makes a trademark, which is a
     * guard/stamp pair, where the stamp marks and freezes unfrozen
     * records as carrying that trademark and the corresponding guard
     * cerifies objects as carrying that trademark (and therefore as
     * having been marked by that stamp).
     *
     * <p>By convention, a guard representing the type-like concept
     * 'Foo' is named 'FooT'. The corresponding stamp is
     * 'FooStamp'. And the record holding both is 'FooMark'. Many
     * guards also have {@code of} methods for making guards like
     * themselves but parameterized by further constraints, which are
     * usually other guards. For example, {@code T.ListT} is the guard
     * representing frozen array, whereas {@code
     * T.ListT.of(cajaVM.GuardT)} represents frozen arrays of guards.
     */
    function Trademark(typename) {
      var result = makeTrademark(typename, new WeakMap());
      stampers.get(GuardStamp)(result.guard);
      return result;
    };

    /**
     * Given that {@code stamps} is a list of stamps and
     * {@code record} is a non-frozen object, this marks record with
     * the trademarks of all of these stamps, and then freezes and
     * returns the record.
     * <p>
     * If any of these conditions do not hold, this throws.
     */
    function stamp(stamps, record) {
      // TODO: Should nonextensible objects be stampable?
      if (Object.isFrozen(record)) {
        throw new TypeError("Can't stamp frozen objects: " + record);
      }
      stamps = Array.prototype.slice.call(stamps, 0);
      var numStamps = stamps.length;
      // First ensure that we will succeed before applying any stamps to
      // the record.
      var i;
      for (i = 0; i < numStamps; i++) {
        if (!stampers.has(stamps[i])) {
          throw new TypeError("Can't stamp with a non-stamp: " + stamps[i]);
        }
      }
      for (i = 0; i < numStamps; i++) {
        // Only works for real stamps, postponing the need for a
        // user-implementable auditing protocol.
        stampers.get(stamps[i])(record);
      }
      return freeze(record);
    };

    ////////////////////////////////////////////////////////////////////////
    // Guards
    ////////////////////////////////////////////////////////////////////////

    /**
     * First ensures that g is a guard; then does
     * {@code g.coerce(specimen, opt_ejector)}.
     */
    function guard(g, specimen, opt_ejector) {
      g = GuardT.coerce(g); // failure throws rather than ejects
      return g.coerce(specimen, opt_ejector);
    }

    /**
     * First ensures that g is a guard; then checks whether the specimen
     * passes that guard.
     * <p>
     * If g is a coercing guard, this only checks that g coerces the
     * specimen to something rather than failing. Note that trademark
     * guards are non-coercing, so if specimen passes a trademark guard,
     * then specimen itself has been marked with that trademark.
     */
    function passesGuard(g, specimen) {
      g = GuardT.coerce(g); // failure throws rather than ejects
      return callWithEjector(
        constFunc(function(opt_ejector) {
          g.coerce(specimen, opt_ejector);
          return true;
        }),
        constFunc(function(ignored) {
          return false;
        })
      );
    }


    /**
     * Create a guard which passes all objects present in {@code table}.
     * This may be used to define trademark-like systems which do not require
     * the object to be frozen.
     *
     * {@code typename} is used for toString and {@code errorMessage} is used
     * when an object does not pass the guard.
     */
    function makeTableGuard(table, typename, errorMessage) {
      var g = {
        toString: constFunc(function() { return typename + 'T'; }),
        coerce: constFunc(function(specimen, opt_ejector) {
          if (!table.get(specimen)) { eject(opt_ejector, errorMessage); }
          return specimen;
        })
      };
      stamp([GuardStamp], g);
      return freeze(g);
    }

    ////////////////////////////////////////////////////////////////////////
    // Exporting
    ////////////////////////////////////////////////////////////////////////

    return freeze({
      callWithEjector: constFunc(callWithEjector),
      eject: constFunc(eject),
      makeSealerUnsealerPair: constFunc(makeSealerUnsealerPair),
      GuardT: GuardT,
      makeTableGuard: constFunc(makeTableGuard),
      Trademark: constFunc(Trademark),
      guard: constFunc(guard),
      passesGuard: constFunc(passesGuard),
      stamp: constFunc(stamp)
    });
  };
})();
;
// Copyright (C) 2011 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * @fileoverview Call {@code ses.startSES} to turn this frame into a
 * SES environment following object-capability rules.
 *
 * <p>Assumes ES5 plus WeakMap. Compatible with ES5-strict or
 * anticipated ES6.
 *
 * @author Mark S. Miller
 * @requires this
 * @overrides ses, hookupSESPlusModule
 */

(function hookupSESPlusModule(global) {
  "use strict";

  if (!ses.ok()) {
    return;
  }

  try {
    ses.startSES(global,
                 ses.whitelist,
                 ses.atLeastFreeVarNames,
                 ses.ejectorsGuardsTrademarks);
  } catch (err) {
    ses.updateMaxSeverity(ses.severities.NOT_SUPPORTED);
    ses.logger.error('hookupSESPlus failed with: ', err);
  }
})(this);

