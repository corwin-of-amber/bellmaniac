// Generated automatically by nearley
// http://github.com/Hardmath123/nearley
(function () {
function id(x) {return x[0]; }
var grammar = {
    ParserRules: [
    {"name": "expression", "symbols": ["untypedExpression", " ebnf$1"], "postprocess":  function(d) { if (d[1] === null) { return d[0]; } else { d[0].type = d[1][3]; return d[0]; } } },
    {"name": "untypedExpression", "symbols": ["applicationExpression"], "postprocess":  function(d) { return d[0];} },
    {"name": "untypedExpression", "symbols": ["lambdaExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "applicationExpression", "symbols": ["applicationWithInfixExpression"], "postprocess":  function(d) { return d[0]; } },
    {"name": "applicationExpression", "symbols": ["applicationWithoutInfixExpression"], "postprocess":  function(d) { return d[0]; } },
    {"name": "applicationWithInfixExpression", "symbols": ["applicationOnNonLambdaExpression", "__", "infixOperator", "__", "applicationExpression"], "postprocess":  function(d) {return {$: "Application", lhs: {$: "Application", lhs: d[2], rhs: d[0]}, rhs: d[4]}; } },
    {"name": "applicationWithoutInfixExpression", "symbols": ["applicationOnNonLambdaExpression", "__", "lambdaOrRootExpression"], "postprocess":  function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } },
    {"name": "applicationWithoutInfixExpression", "symbols": ["rootExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "applicationOnNonLambdaExpression", "symbols": ["applicationOnNonLambdaExpression", "__", "rootExpression"], "postprocess":  function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } },
    {"name": "applicationOnNonLambdaExpression", "symbols": ["rootExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "lambdaOrRootExpression", "symbols": ["lambdaExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "lambdaOrRootExpression", "symbols": ["rootExpression"], "postprocess":  function(d) {return d[0]; } },
    {"name": "rootExpression", "symbols": ["leftparen", "expression", "rightparen"], "postprocess":  function(d) {return d[1];} },
    {"name": "rootExpression", "symbols": ["variable"], "postprocess":  function(d) {return d[0]; } },
    {"name": "lambdaExpression", "symbols": ["lambda", "_", " ebnf$2", "arrow", "_", "expression"], "postprocess": 
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
    {"name": "identifier", "symbols": ["letter", "idrest"], "postprocess":  function(d) {return d[0].concat(d[1]); } },
    {"name": "identifier", "symbols": ["op"], "postprocess":  function(d) {return d[0]; } },
    {"name": "variable", "symbols": ["identifier"], "postprocess":  function(d) {return {$: "Identifier", kind: "variable", literal: d[0]}; } },
    {"name": "infixOperator", "symbols": ["backtick", "variable", "backtick"], "postprocess":  function(d) {return d[1]; } },
    {"name": "type", "symbols": ["type", "_", "typeArrow", "_", "rootType"], "postprocess":  function(d) {return {$: "Tree", kind: "function", from: d[0], to: d[4]};} },
    {"name": "type", "symbols": ["type", "_", "typeOperator", "_", "rootType"], "postprocess":  function(d) {return {$: "Tree", kind: "operation", lhs: d[0], rhs: d[4], operator: d[2]}; } },
    {"name": "type", "symbols": ["rootType"], "postprocess":  function(d) {return d[0]; } },
    {"name": "typeOperator", "symbols": [/[*<>∩∪\\]/], "postprocess":  function(d) {return d[0]; } },
    {"name": "rootType", "symbols": ["leftparen", "type", "rightparen"], "postprocess":  function(d) {return d[2];} },
    {"name": "rootType", "symbols": ["typeVariable"], "postprocess":  function(d) {return d[0]; } },
    {"name": "typeVariable", "symbols": ["letter"], "postprocess":  function(d) {return {$: "Identifier", kind: "type", literal: d[0]}; } },
    {"name": "_", "symbols": [" ebnf$3"], "postprocess":  function(d) {return null; } },
    {"name": "__", "symbols": [" ebnf$4"], "postprocess":  function(d) {return null; } },
    {"name": "opchar", "symbols": [/[!%&#*+<=>?@^|~\\\-\/]/], "postprocess":  function(d) {return d[0]; } },
    {"name": "op", "symbols": [" ebnf$5"], "postprocess":  function(d) { return d[0].join(""); } },
    {"name": "letter", "symbols": [/[a-zA-Z\u0024\u005F\u00C0-\u1FFF\u2C00-\uD7FF]/], "postprocess":  function(d) {return d[0]; } },
    {"name": "digit", "symbols": [/[0-9]/], "postprocess":  function(d) {return d[0]; } },
    {"name": "letterOrDigit", "symbols": ["letter"], "postprocess":  function(d) {return d[0]; } },
    {"name": "letterOrDigit", "symbols": ["digit"], "postprocess":  function(d) {return d[0]; } },
    {"name": "idrest", "symbols": [" ebnf$6"], "postprocess":  function(d) {return d[0].join(""); } },
    {"name": "idrest", "symbols": [" ebnf$7", "underscore", "op"], "postprocess":  function(d) {return d[0].join("").concat("_").concat(d[2]);} },
    {"name": "arrow", "symbols": [{"literal":"↦"}]},
    {"name": "leftparen", "symbols": [{"literal":"("}]},
    {"name": "rightparen", "symbols": [{"literal":")"}]},
    {"name": "lambda", "symbols": [{"literal":"λ"}]},
    {"name": "underscore", "symbols": [{"literal":"_"}]},
    {"name": "backtick", "symbols": [{"literal":"`"}]},
    {"name": "colon", "symbols": [{"literal":":"}]},
    {"name": " string$8", "symbols": [{"literal":"-"}, {"literal":">"}], "postprocess": function joiner(d) {
        return d.join('');
    }},
    {"name": "typeArrow", "symbols": [" string$8"]},
    {"name": " ebnf$1", "symbols": [" subexpression$9"], "postprocess": id},
    {"name": " ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": " ebnf$2", "symbols": [" subexpression$10"]},
    {"name": " ebnf$2", "symbols": [" subexpression$11", " ebnf$2"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$3", "symbols": []},
    {"name": " ebnf$3", "symbols": [/[\s]/, " ebnf$3"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$4", "symbols": [/[\s]/]},
    {"name": " ebnf$4", "symbols": [/[\s]/, " ebnf$4"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$5", "symbols": ["opchar"]},
    {"name": " ebnf$5", "symbols": ["opchar", " ebnf$5"], "postprocess": function (d) {
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
    {"name": " subexpression$9", "symbols": ["_", "colon", "_", "type"]},
    {"name": " subexpression$10", "symbols": ["variable", "_"]},
    {"name": " subexpression$11", "symbols": ["variable", "_"]}
]
  , ParserStart: "expression"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();
