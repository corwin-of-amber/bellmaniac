// Generated automatically by nearley
// http://github.com/Hardmath123/nearley
(function () {
function id(x) {return x[0]; }
var grammar = {
    ParserRules: [
    {"name": "expression", "symbols": ["setDeclaration"], "postprocess":  id },
    {"name": "expression", "symbols": ["untypedExpression", " ebnf$1"], "postprocess":  function(d) {
		if (d[1] === null) {
			return d[0];
		} else {
			d[0].type = d[1][3];
			return d[0].type && d[0];
		} } },
    {"name": " string$2", "symbols": [{"literal":":"}, {"literal":"s"}, {"literal":"e"}, {"literal":"t"}], "postprocess": function joiner(d) {
        return d.join('');
    }},
    {"name": "setDeclaration", "symbols": ["identifier", " string$2"], "postprocess":  function(d) { return declareSet(d[0]); } },
    {"name": "untypedExpression", "symbols": ["applicationExpression"], "postprocess":  id },
    {"name": "untypedExpression", "symbols": ["lambdaExpression"], "postprocess":  id },
    {"name": "applicationExpression", "symbols": ["applicationWithInfixExpression"], "postprocess":  id },
    {"name": "applicationExpression", "symbols": ["applicationWithoutInfixExpression"], "postprocess":  id },
    {"name": "applicationWithInfixExpression", "symbols": ["applicationOnNonLambdaExpression", "_", "notatedInfixOperator", "_", "applicationExpression"], "postprocess":  function(d) {return application(application(d[2], d[0]), d[4]);} },
    {"name": "applicationWithInfixExpression", "symbols": ["applicationOnNonLambdaExpression", "_", "defaultInfixOperator", "_", "applicationExpression"], "postprocess":  function(d) {return tree(d[2], [d[0], d[4]]); } },
    {"name": "applicationWithoutInfixExpression", "symbols": ["applicationOnNonLambdaExpression", "__", "rootExpression"], "postprocess":  function(d) {return application(d[0], d[2]); } },
    {"name": "applicationWithoutInfixExpression", "symbols": ["parenthesizedExpression", "__", "lambdaExpression"], "postprocess":  function(d) {return application(d[0], d[2]); } },
    {"name": "applicationWithoutInfixExpression", "symbols": ["fixedOrRootExpression"], "postprocess":  id },
    {"name": "applicationOnNonLambdaExpression", "symbols": ["applicationOnNonLambdaExpression", "__", "rootExpression"], "postprocess":  function(d) {return application(d[0], d[2]); } },
    {"name": "applicationOnNonLambdaExpression", "symbols": ["fixedOrRootExpression"], "postprocess":  id },
    {"name": "lambdaOrRootExpression", "symbols": ["lambdaExpression"], "postprocess":  id },
    {"name": "lambdaOrRootExpression", "symbols": ["rootExpression"], "postprocess":  id },
    {"name": "fixedOrRootExpression", "symbols": ["fixedExpression"], "postprocess":  id },
    {"name": "fixedOrRootExpression", "symbols": ["rootExpression"], "postprocess":  id },
    {"name": "fixedExpression", "symbols": ["fix", "__", "rootExpression"], "postprocess":  function(d) { return fixedExpression(d[2]); } },
    {"name": "rootExpression", "symbols": ["parenthesizedExpression"], "postprocess":  id },
    {"name": "rootExpression", "symbols": ["listExpression"], "postprocess":  id },
    {"name": "rootExpression", "symbols": ["variable"], "postprocess":  id },
    {"name": "listExpression", "symbols": ["leftbracket", "_", "expression", " ebnf$3", "_", "rightbracket"], "postprocess":  function(d) {
	var consHelper = function (vars) {
		if (vars.length === 0) {
			return variable("nil");
		} else {
			return cons(vars[0][3], consHelper(vars.slice(1)));
		}
	}
	return cons(d[2], consHelper(d[3]));
} },
    {"name": "parenthesizedExpression", "symbols": ["leftparen", "expression", "rightparen"], "postprocess":  function(d) {return d[1];} },
    {"name": "lambdaExpression", "symbols": [" ebnf$4", "arrow", "_", "expression"], "postprocess": 
	function(d) {
		var curry = function(vars, lbody) {
			if (vars.length === 1) {
				return abstraction(vars[0][0], lbody);
			} else {
				return abstraction(vars[0][0], curry(vars.slice(1), lbody));
			}
		};
		return curry(d[0], d[3]);
	} },
    {"name": "possiblyTypedLambdaParameter", "symbols": ["variable"], "postprocess":  id },
    {"name": "possiblyTypedLambdaParameter", "symbols": ["leftparen", "variable", "_", "colon", "_", "type", "rightparen"], "postprocess":  function(d) {
		d[1].type = d[5];
		return d[5] && d[1]; } },
    {"name": "variable", "symbols": ["identifier"], "postprocess":  function(d) {return variable(d[0]); } },
    {"name": "notatedInfixOperator", "symbols": ["backtick", "variable", "backtick"], "postprocess":  function(d) {return d[1]; } },
    {"name": "notatedInfixOperator", "symbols": [/[+*\-]/], "postprocess":  function(d) {return tree(operator(d[0]),[]); } },
    {"name": "defaultInfixOperator", "symbols": [{"literal":"/"}], "postprocess":  function(d) {return operator(d[0]); } },
    {"name": "type", "symbols": ["typeWithOperations", "_", "typeArrow", "_", "type"], "postprocess":  function(d) {return typeOperation(d[2], d[0], d[4]); } },
    {"name": "type", "symbols": ["typeWithOperations"], "postprocess":  id },
    {"name": "typeWithOperations", "symbols": ["typeWithOperations", "_", "typeOperator", "_", "rootType"], "postprocess":  function(d) {return typeOperation(d[2], d[0], d[4]); } },
    {"name": "typeWithOperations", "symbols": ["rootType"], "postprocess":  id },
    {"name": "typeOperator", "symbols": [/[×∩]/], "postprocess":  id },
    {"name": "rootType", "symbols": ["leftparen", "type", "rightparen"], "postprocess":  function(d) {return d[1];} },
    {"name": "rootType", "symbols": ["typeVariable"], "postprocess":  id },
    {"name": "typeVariable", "symbols": ["identifier"], "postprocess":  function(d) {return typeVariable(d[0]); } },
    {"name": "identifier", "symbols": ["letter", "idrest"], "postprocess":  function(d) {return d[0].concat(d[1]); } },
    {"name": "identifier", "symbols": ["op"], "postprocess":  id },
    {"name": "idrest", "symbols": [" ebnf$5"], "postprocess":  function(d) {return d[0].join(""); } },
    {"name": "idrest", "symbols": [" ebnf$6", "underscore", "op"], "postprocess":  function(d) {return d[0].join("").concat("_").concat(d[2]);} },
    {"name": "letterOrDigit", "symbols": ["letter"], "postprocess":  id },
    {"name": "letterOrDigit", "symbols": ["digit"], "postprocess":  id },
    {"name": "letter", "symbols": [/[a-zA-Z$_\u00C0-\u1FFF\u2080-\u2089\u2C00-\uD7FF]/], "postprocess":  id },
    {"name": "digit", "symbols": [/[0-9]/], "postprocess":  id },
    {"name": "op", "symbols": ["validStandaloneOpchars"], "postprocess":  id },
    {"name": "op", "symbols": ["opchar", " ebnf$7"], "postprocess":  function(d) { return [d[0]].concat(d[1]).join(""); } },
    {"name": "validStandaloneOpchars", "symbols": [/[!%&*+<>?^|~\\\-]/], "postprocess":  id },
    {"name": "opchar", "symbols": ["validStandaloneOpchars"], "postprocess":  id },
    {"name": "opchar", "symbols": [/[=#@\:]/], "postprocess":  id },
    {"name": "_", "symbols": [" ebnf$8"], "postprocess":  function(d) {return null; } },
    {"name": "__", "symbols": [" ebnf$9"], "postprocess":  function(d) {return null; } },
    {"name": "arrow", "symbols": [{"literal":"↦"}]},
    {"name": "leftparen", "symbols": [{"literal":"("}]},
    {"name": "rightparen", "symbols": [{"literal":")"}]},
    {"name": "leftbracket", "symbols": [{"literal":"⟨"}]},
    {"name": "rightbracket", "symbols": [{"literal":"⟩"}]},
    {"name": "underscore", "symbols": [{"literal":"_"}]},
    {"name": "forwardslash", "symbols": [{"literal":"/"}]},
    {"name": "backtick", "symbols": [{"literal":"`"}]},
    {"name": "colon", "symbols": [{"literal":":"}]},
    {"name": "comma", "symbols": [{"literal":","}]},
    {"name": " string$10", "symbols": [{"literal":"-"}, {"literal":">"}], "postprocess": function joiner(d) {
        return d.join('');
    }},
    {"name": "typeArrow", "symbols": [" string$10"], "postprocess":  id },
    {"name": " string$11", "symbols": [{"literal":"f"}, {"literal":"i"}, {"literal":"x"}], "postprocess": function joiner(d) {
        return d.join('');
    }},
    {"name": "fix", "symbols": [" string$11"]},
    {"name": " ebnf$1", "symbols": [" subexpression$12"], "postprocess": id},
    {"name": " ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": " ebnf$3", "symbols": []},
    {"name": " ebnf$3", "symbols": [" subexpression$13", " ebnf$3"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$4", "symbols": [" subexpression$14"]},
    {"name": " ebnf$4", "symbols": [" subexpression$15", " ebnf$4"], "postprocess": function (d) {
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
    {"name": " ebnf$7", "symbols": ["opchar"]},
    {"name": " ebnf$7", "symbols": ["opchar", " ebnf$7"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$8", "symbols": []},
    {"name": " ebnf$8", "symbols": [/[\s]/, " ebnf$8"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " ebnf$9", "symbols": [/[\s]/]},
    {"name": " ebnf$9", "symbols": [/[\s]/, " ebnf$9"], "postprocess": function (d) {
                    return [d[0]].concat(d[1]);
                }},
    {"name": " subexpression$12", "symbols": ["_", "colon", "_", "type"]},
    {"name": " subexpression$13", "symbols": ["_", "comma", "_", "expression"]},
    {"name": " subexpression$14", "symbols": ["possiblyTypedLambdaParameter", "__"]},
    {"name": " subexpression$15", "symbols": ["possiblyTypedLambdaParameter", "__"]}
]
  , ParserStart: "expression"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();
