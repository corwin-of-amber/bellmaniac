// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: http://codemirror.net/LICENSE

/**
 * Adapted from Codemirror's Scheme mode by Koh Zi Han, based on implementation by Koh Zi Chun
 */

(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {
"use strict";

CodeMirror.defineMode("bellmania", function () {
    var BUILTIN = "builtin", COMMENT = "comment", STRING = "string", SPECIAL = "special",
        ATOM = "atom", NUMBER = "number", BRACKET = "bracket", KEYWORD = "keyword";
    var INDENT_WORD_SKIP = 2;

    function makeKeywords(str) {
        var obj = {}, words = str.split(" ");
        for (var i = 0; i < words.length; ++i) obj[words[i]] = true;
        return obj;
    }

    // actually reserved in language
    var keywords = makeKeywords("set fix");
    var operators = makeKeywords("/ + × ∩ - * ↦ :");

    // tactics
    var tactics = makeKeywords("Slice Synth Stratify Distrib Assoc Let SlashToReduce SaveAs");

    var boxedRegex = new RegExp(/\ud83c[\udd30-\udd38](\u0332)?/);

    function stateStack(indent, type, prev) { // represents a state stack object
        this.indent = indent;
        this.type = type;
        this.prev = prev;
    }

    function pushStack(state, indent, type) {
        state.indentStack = new stateStack(indent, type, state.indentStack);
    }

    function popStack(state) {
        state.indentStack = state.indentStack.prev;
    }

    var decimalMatcher = new RegExp(/^(?:[-+]i|[-+](?:(?:(?:\d+#+\.?#*|\d+\.\d*#*|\.\d+#*|\d+)(?:[esfdl][-+]?\d+)?)|\d+#*\/\d+#*)i|[-+]?(?:(?:(?:\d+#+\.?#*|\d+\.\d*#*|\.\d+#*|\d+)(?:[esfdl][-+]?\d+)?)|\d+#*\/\d+#*)@[-+]?(?:(?:(?:\d+#+\.?#*|\d+\.\d*#*|\.\d+#*|\d+)(?:[esfdl][-+]?\d+)?)|\d+#*\/\d+#*)|[-+]?(?:(?:(?:\d+#+\.?#*|\d+\.\d*#*|\.\d+#*|\d+)(?:[esfdl][-+]?\d+)?)|\d+#*\/\d+#*)[-+](?:(?:(?:\d+#+\.?#*|\d+\.\d*#*|\.\d+#*|\d+)(?:[esfdl][-+]?\d+)?)|\d+#*\/\d+#*)?i|(?:(?:(?:\d+#+\.?#*|\d+\.\d*#*|\.\d+#*|\d+)(?:[esfdl][-+]?\d+)?)|\d+#*\/\d+#*))(?=[()\s;"]|$)/i);

    function isBinaryNumber (stream) {
        return stream.match(binaryMatcher);
    }

    function isOctalNumber (stream) {
        return stream.match(octalMatcher);
    }

    function isDecimalNumber (stream, backup) {
        if (backup === true) {
            stream.backUp(1);
        }
        return stream.match(decimalMatcher);
    }

    function isHexNumber (stream) {
        return stream.match(hexMatcher);
    }

    return {
        startState: function () {
            return {
                indentStack: null,
                indentation: 0,
                mode: false,
                sExprComment: false
            };
        },

        token: function (stream, state) {
            if (state.indentStack === null && stream.sol()) {
                // update indentation, but only if indentStack is empty
                state.indentation = stream.indentation();
            }

            // skip spaces
            if (stream.eatSpace()) {
                return null;
            }
            var returnType = null;

            switch(state.mode){
                case "string": // multi-line string parsing mode
                    var next, escaped = false;
                    while ((next = stream.next()) !== null) {
                        if (next == "\"" && !escaped) {
                            state.mode = false;
                            break;
                        }
                        escaped = !escaped && next == "\\";
                    }
                    returnType = STRING;
                    break;
                case "comment": // multi-line comment ends with */
                    var next, maybeEnd = false;
                    while ((next = stream.next()) !== null) {
                        if (next == "/" && maybeEnd) {
                            state.mode = false;
                            break;
                        }
                        maybeEnd = (next == "*");
                    }
                    returnType = COMMENT;
                    break;
                default: // default parsing mode
                    var ch = stream.next();
                    if (ch == "\"") { // enter string parsing mode
                        state.mode = "string";
                        returnType = STRING;
                    } else if (ch == "`") { // everything from backtick to whitespace/separator is an atom
                        stream.eatWhile(/[^\s()\[\]⟨⟩,]/);
                        returnType = ATOM;
                    } else if (ch == "'") {
                        returnType = ATOM;
                    } else if (ch == ":") {
                        returnType = BUILTIN;
                    } else if (ch == '/') {
                        if (stream.eat("*")) {                    // Multi-line comment
                            state.mode = "comment"; // toggle to comment mode
                            returnType = COMMENT;
                        } else if (stream.eat('/')) {
                            stream.skipToEnd(); // rest of the line is a comment
                            returnType = COMMENT;
                        }
                    } else if (/^[-+0-9.]/.test(ch) && isDecimalNumber(stream, true)) { // decimal number
                        returnType = NUMBER;
                    } else if (ch == "(" || ch == "[" || ch == "⟨") {
                      var keyWord = ''; var indentTemp = stream.column(), letter;
                        pushStack(state, indentTemp + stream.current().length, ch);

                        if(typeof state.sExprComment == "number") state.sExprComment++;
                        returnType = BRACKET;
                    } else if (ch === "\ud83c") {
                        stream.eatWhile(/[\udd30-\udd49\u0332]/);
                        returnType = ATOM;
                    } else if (ch == ")" || ch == "]" || ch == "⟩") {
                        returnType = BRACKET;
                        var opn = {")": "(", "]": "[", "⟩": "⟨"};
                        if (state.indentStack !== null && state.indentStack.type === opn[ch]) {
                            popStack(state);
                        }
                    } else {
                        stream.eatWhile(/[\w\$_\-!$%&*+\.\/<=>?@\^~]/);
                        if (keywords && keywords.propertyIsEnumerable(stream.current())) {
                            returnType = KEYWORD;
                        } else if (operators && operators.propertyIsEnumerable(stream.current())) {
                            returnType = BUILTIN;
                        } else if (tactics && tactics.propertyIsEnumerable(stream.current())) {
                            returnType = SPECIAL;
                        } else {
                            returnType = "variable";
                        }
                    }
            }
            return (typeof state.sExprComment == "number") ? COMMENT : returnType;
        },

        indent: function (state) {
            if (state.indentStack === null) return state.indentation;
            return state.indentStack.indent;
        },

        closeBrackets: {pairs: "()[]{}⟨⟩\"\""}
    };
});

CodeMirror.defineMIME("text/x-bellmania", "bellmania");

});
