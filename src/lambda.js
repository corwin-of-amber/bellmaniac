// Generated automatically by nearley
// http://github.com/Hardmath123/nearley
(function () {
function id(x) {return x[0]; }
var grammar = {
    ParserRules: [
    {"name": "expression", "symbols": ["applicationExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "expression", "symbols": ["lambdaExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "applicationExpression", "symbols": ["applicationOnNonLambdaExpression", "_", "lambdaOrRootExpression"], "postprocess":  function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } },
    {"name": "applicationExpression", "symbols": ["rootExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "applicationOnNonLambdaExpression", "symbols": ["applicationOnNonLambdaExpression", "_", "rootExpression"], "postprocess":  function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } },
    {"name": "applicationOnNonLambdaExpression", "symbols": ["rootExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "lambdaOrRootExpression", "symbols": ["lambdaExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "lambdaOrRootExpression", "symbols": ["rootExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "rootExpression", "symbols": ["leftparen", "expression", "rightparen"], "postprocess":  function(d) {return d[1];} },
    {"name": "rootExpression", "symbols": ["variable"], "postprocess":  function(d) {return d[0]; } },
    {"name": "lambdaExpression", "symbols": ["lambda", "_", " ebnf$1", "arrow", "_", "expression"], "postprocess": 
	function(d) {
		var curry = function(vars, lbody) {
			if (vars.length === 1) {
				return {$: "Abstraction", var: vars[0][0], lbody: lbody};
			} else {
				return {$: "Abstraction", var: vars[0][0], lbody: curry(vars.slice(1), lbody)};
			}
		};
		return curry(d[2], d[5]);
	} },
    {"name": "variable", "symbols": ["letter", "idrest"], "postprocess":  function(d) {return {$: "Identifier", kind: "variable", literal: d[0].concat(d[1])}; } },
    {"name": "variable", "symbols": ["op"], "postprocess":  function(d) {return d[0]; } },
    {"name": "_", "symbols": [" ebnf$2"], "postprocess":  function(d) {return null; } },
    {"name": "opchar", "symbols": [/[!%&#*+:<=>?@^|~\\\-\/]/], "postprocess":  function(d) {return d[0]; } },
    {"name": "op", "symbols": [" ebnf$3"], "postprocess":  function(d) { return d[0].join(""); } },
    {"name": "letter", "symbols": [/[a-zA-Z\u00C0-\u1FFF\u2C00-\uD7FF]/], "postprocess":  function(d) {return d[0]; } },
    {"name": "digit", "symbols": [/[0-9]/], "postprocess":  function(d) {return d[0]; } },
    {"name": "letterOrDigit", "symbols": ["letter"], "postprocess":  function(d) {return d[0]; } },
    {"name": "letterOrDigit", "symbols": ["digit"], "postprocess":  function(d) {return d[0]; } },
    {"name": "idrest", "symbols": [" ebnf$4"], "postprocess":  function(d) {return d[0].join(""); } },
    {"name": "idrest", "symbols": [" ebnf$5", "underscore", "op"], "postprocess":  function(d) {return d[0].join("").concat("_").concat(d[2]);} },
    {"name": "idrest", "symbols": [" ebnf$6", "underscore", " ebnf$7"], "postprocess":  function(d) {return d[0].join("").concat("_").concat(d[2].join(""));} },
    {"name": "arrow", "symbols": [{"literal":"↦"}]},
    {"name": "leftparen", "symbols": [{"literal":"("}]},
    {"name": "rightparen", "symbols": [{"literal":")"}]},
    {"name": "lambda", "symbols": [{"literal":"λ"}]},
    {"name": "underscore", "symbols": [{"literal":"_"}]},
    {"name": " ebnf$1", "symbols": [" subexpression$8"]},
    {"name": " ebnf$1", "symbols": [" subexpression$9", " ebnf$1"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$2", "symbols": [/[\s]/]},
    {"name": " ebnf$2", "symbols": [/[\s]/, " ebnf$2"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$3", "symbols": []},
    {"name": " ebnf$3", "symbols": ["opchar", " ebnf$3"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$4", "symbols": []},
    {"name": " ebnf$4", "symbols": ["letterOrDigit", " ebnf$4"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$5", "symbols": []},
    {"name": " ebnf$5", "symbols": ["letterOrDigit", " ebnf$5"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$6", "symbols": []},
    {"name": " ebnf$6", "symbols": ["letterOrDigit", " ebnf$6"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$7", "symbols": []},
    {"name": " ebnf$7", "symbols": ["letterOrDigit", " ebnf$7"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " subexpression$8", "symbols": ["variable", "_"]},
    {"name": " subexpression$9", "symbols": ["variable", "_"]}
]
  , ParserStart: "expression"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();
