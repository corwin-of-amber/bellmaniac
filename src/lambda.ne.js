// Generated automatically by nearley
// http://github.com/Hardmath123/nearley
(function () {
function id(x) {return x[0]; }
var grammar = {
    ParserRules: [
    {"name": "expression", "symbols": ["setMode"], "postprocess": id},
    {"name": "expression", "symbols": ["setDeclaration"], "postprocess": id},
    {"name": "expression", "symbols": ["subsetDeclaration"], "postprocess": id},
    {"name": "expression", "symbols": ["possiblyTypedExpression"], "postprocess": id},
    {"name": "expression", "symbols": ["routineDeclaration"], "postprocess": id},
    {"name": "routineDeclaration", "symbols": ["variable", "routineDeclaration$ebnf$1", "_", "colondash", "_", "possiblyTypedExpression"], "postprocess":  function(d) {
        	var output = {isRoutine: true};
        	output[d[0].root.literal] = {params: d[1] || [], body: d[5]};
        	return output;
        } },
    {"name": "paramList", "symbols": ["leftsquarebracket", "_", "variable", "paramList$ebnf$1", "_", "rightsquarebracket"], "postprocess":  function(d) {
        	if (d[3].length === 0) {
        		return [d[2]];
        	} else {
        		return [d[2]].concat(d[3].map(take(3)));
        	}
        } },
    {"name": "possiblyTypedExpression", "symbols": ["untypedExpression", "possiblyTypedExpression$ebnf$1"], "postprocess":  function(d) {
        if (d[1] === null) {
        	return d[0];
        } else {
        	d[0].type = d[1][3];
        	return d[0].type && d[0];
        } } },
    {"name": "setMode", "symbols": [{"literal":"∵"}], "postprocess": function() { return {setMode: "tactic"}; }},
    {"name": "setMode", "symbols": [{"literal":"∎"}], "postprocess": function() { return {setMode: "tactic"}; }},
    {"name": "setDeclaration$string$1", "symbols": [{"literal":"s"}, {"literal":"e"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "setDeclaration", "symbols": ["variable", "setDeclaration$ebnf$1", "_", "colon", "_", "setDeclaration$string$1"], "postprocess": 
        function(d, loc, reject) { return declareSets(d[0], d[1].map(take(1))) || reject; } },
    {"name": "subsetDeclaration", "symbols": ["variable", "subsetDeclaration$ebnf$1", "_", "subseteq", "_", "variable"], "postprocess": 
        function(d, loc, reject) { return declareSubsets(d[0], d[1].map(take(1)), d[5]) || reject; } },
    {"name": "untypedExpression", "symbols": ["applicationExpression"], "postprocess": id},
    {"name": "untypedExpression", "symbols": ["lambdaExpression"], "postprocess": id},
    {"name": "applicationExpression", "symbols": ["applicationWithInfixExpression"], "postprocess": id},
    {"name": "applicationExpression", "symbols": ["applicationWithoutInfixExpression"], "postprocess": id},
    {"name": "applicationWithInfixExpression", "symbols": ["applicationExpression", "_", "notatedInfixOperator", "_", "applicationWithoutInfixExpression"], "postprocess": function(d) {return application(application(d[2], d[0]), d[4]);}},
    {"name": "applicationWithInfixExpression", "symbols": ["applicationExpression", "_", "defaultInfixOperator", "_", "applicationWithoutInfixExpression"], "postprocess": function(d) {return tree(d[2], [d[0], d[4]]); }},
    {"name": "applicationWithoutInfixExpression", "symbols": ["applicationOnNonLambdaExpression", "__", "fixedOrRootExpression"], "postprocess": function(d) {return application(d[0], d[2]); }},
    {"name": "applicationWithoutInfixExpression", "symbols": ["parenthesizedExpression", "__", "lambdaExpression"], "postprocess": function(d) {return application(d[0], d[2]); }},
    {"name": "applicationWithoutInfixExpression", "symbols": ["fixedOrRootExpression"], "postprocess": id},
    {"name": "applicationOnNonLambdaExpression", "symbols": ["applicationOnNonLambdaExpression", "__", "fixedOrRootExpression"], "postprocess": function(d) {return application(d[0], d[2]); }},
    {"name": "applicationOnNonLambdaExpression", "symbols": ["rootExpression"], "postprocess": id},
    {"name": "lambdaOrRootExpression", "symbols": ["lambdaExpression"], "postprocess": id},
    {"name": "lambdaOrRootExpression", "symbols": ["rootExpression"], "postprocess": id},
    {"name": "fixedOrRootExpression", "symbols": ["fixedExpression"], "postprocess": id},
    {"name": "fixedOrRootExpression", "symbols": ["rootExpression"], "postprocess": id},
    {"name": "fixedExpression", "symbols": ["fix", "__", "lambdaOrRootExpression"], "postprocess": function(d) { return fixedExpression(d[2]); }},
    {"name": "rootExpression", "symbols": ["parenthesizedExpression"], "postprocess": id},
    {"name": "rootExpression", "symbols": ["listExpression"], "postprocess": id},
    {"name": "rootExpression", "symbols": ["variable"], "postprocess": id},
    {"name": "rootExpression", "symbols": ["integer"], "postprocess": id},
    {"name": "rootExpression", "symbols": ["backtick", "_", "type"], "postprocess": take(2)},
    {"name": "listExpression", "symbols": ["leftbracket", "_", "expression", "listExpression$ebnf$1", "_", "rightbracket"], "postprocess":  function(d) {
        	var consHelper = function (vars) {
        		if (vars.length === 0) {
        			return variable("nil");
        		} else {
        			return cons(vars[0][3], consHelper(vars.slice(1)));
        		}
        	}
        	return cons(d[2], consHelper(d[3]));
        } },
    {"name": "parenthesizedExpression", "symbols": ["leftparen", "expression", "rightparen"], "postprocess": function(d) {return d[1];}},
    {"name": "lambdaExpression", "symbols": ["lambdaExpression$ebnf$1", "arrow", "_", "expression"], "postprocess": 
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
    {"name": "possiblyTypedLambdaParameter", "symbols": ["variable"], "postprocess": id},
    {"name": "possiblyTypedLambdaParameter", "symbols": ["leftparen", "variable", "_", "colon", "_", "type", "rightparen"], "postprocess":  function(d) {
        d[1].type = d[5];
        return d[5] && d[1]; } },
    {"name": "variable", "symbols": ["identifier"], "postprocess": function(d, loc, reject) {return variable(d[0]) || reject; }},
    {"name": "variable", "symbols": ["escaped"], "postprocess": function(d) { return tree(identifier(d[0],'variable')); }},
    {"name": "integer", "symbols": ["num"], "postprocess": function(d) { return tree(identifier(d[0],'?')); }},
    {"name": "notatedInfixOperator", "symbols": ["backtick", "variable", "backtick"], "postprocess": function(d) {return d[1]; }},
    {"name": "notatedInfixOperator", "symbols": [/[+*\-]/], "postprocess": function(d, loc, reject) {return tree(identifier(d[0],'variable')); }},
    {"name": "defaultInfixOperator", "symbols": [{"literal":"/"}], "postprocess": function(d) {return operator(d[0]); }},
    {"name": "type", "symbols": ["typeWithOperations", "_", "typeArrow", "_", "type"], "postprocess": function(d) {return functionType(d[0], d[4]); }},
    {"name": "type", "symbols": ["typeWithOperations"], "postprocess": id},
    {"name": "typeWithOperations", "symbols": ["typeWithOperations", "_", {"literal":"×"}, "_", "rootType"], "postprocess": function(d) {return typeOperation(d[2], d[0], d[4]); }},
    {"name": "typeWithOperations", "symbols": ["typeWithOperations", "_", {"literal":"∩"}, "_", "variable"], "postprocess": function(d) {return typeOperation(d[2], d[0], d[4]); }},
    {"name": "typeWithOperations", "symbols": ["rootType"], "postprocess": id},
    {"name": "rootType", "symbols": ["leftparen", "type", "rightparen"], "postprocess": function(d) {return d[1];}},
    {"name": "rootType", "symbols": ["typeVariable"], "postprocess": id},
    {"name": "typeVariable", "symbols": ["identifier"], "postprocess": function(d, loc, reject) {return typeVariable(d[0]) || reject; }},
    {"name": "identifier", "symbols": ["letter", "idrest"], "postprocess": function(d) {return d[0].concat(d[1]); }},
    {"name": "identifier", "symbols": ["op"], "postprocess": id},
    {"name": "identifier", "symbols": ["identifier$ebnf$1"], "postprocess": function(d) {return d[0].join(""); }},
    {"name": "idrest", "symbols": ["idrest$ebnf$1"], "postprocess": function(d) {return d[0].join(""); }},
    {"name": "idrest", "symbols": ["idrest$ebnf$2", "underscore", "op"], "postprocess": function(d) {return d[0].join("").concat("_").concat(d[2]);}},
    {"name": "letterOrDigit", "symbols": ["letter"], "postprocess": id},
    {"name": "letterOrDigit", "symbols": ["digit"], "postprocess": id},
    {"name": "letter", "symbols": [/[a-zA-Z$_\u00C0-\u00D6\u00D8-\u1FFF\u2080-\u2089\u2C00-\uD7FF]/], "postprocess": id},
    {"name": "digit", "symbols": [/[0-9]/], "postprocess": id},
    {"name": "letter", "symbols": [/[\uD83C\uDD30-\uDD49]/], "postprocess": id},
    {"name": "num", "symbols": ["num$ebnf$1"], "postprocess": function(d) { return parseInt(d[0].join("")); }},
    {"name": "op", "symbols": ["validStandaloneOpchars"], "postprocess": id},
    {"name": "op", "symbols": ["opchar", "op$ebnf$1"], "postprocess": function(d) { return [d[0]].concat(d[1]).join(""); }},
    {"name": "validStandaloneOpchars", "symbols": [/[!%&*+<>?^|~\\\-]/], "postprocess": id},
    {"name": "opchar", "symbols": ["validStandaloneOpchars"], "postprocess": id},
    {"name": "opchar", "symbols": [/[=#@\:]/], "postprocess": id},
    {"name": "escaped", "symbols": [/["]/, "escaped$ebnf$1", /["]/], "postprocess": function(d) { return d[1].join(""); }},
    {"name": "_", "symbols": ["_$ebnf$1"], "postprocess": function(d) {return null; }},
    {"name": "__", "symbols": ["__$ebnf$1"], "postprocess": function(d) {return null; }},
    {"name": "arrow", "symbols": [{"literal":"↦"}]},
    {"name": "leftparen", "symbols": [{"literal":"("}]},
    {"name": "rightparen", "symbols": [{"literal":")"}]},
    {"name": "leftbracket", "symbols": [{"literal":"⟨"}]},
    {"name": "rightbracket", "symbols": [{"literal":"⟩"}]},
    {"name": "leftsquarebracket", "symbols": [{"literal":"["}]},
    {"name": "rightsquarebracket", "symbols": [{"literal":"]"}]},
    {"name": "underscore", "symbols": [{"literal":"_"}]},
    {"name": "forwardslash", "symbols": [{"literal":"/"}]},
    {"name": "colondash$string$1", "symbols": [{"literal":":"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "colondash", "symbols": ["colondash$string$1"]},
    {"name": "backtick", "symbols": [{"literal":"`"}]},
    {"name": "subseteq", "symbols": [{"literal":"⊆"}]},
    {"name": "colon", "symbols": [{"literal":":"}]},
    {"name": "comma", "symbols": [{"literal":","}]},
    {"name": "typeArrow$string$1", "symbols": [{"literal":"-"}, {"literal":">"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "typeArrow", "symbols": ["typeArrow$string$1"], "postprocess": id},
    {"name": "typeArrow", "symbols": [{"literal":"→"}], "postprocess": function() { return "->"; }},
    {"name": "fix$string$1", "symbols": [{"literal":"f"}, {"literal":"i"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "fix", "symbols": ["fix$string$1"]},
    {"name": "routineDeclaration$ebnf$1", "symbols": ["routineDeclaration$ebnf$1$subexpression$1"], "postprocess": id},
    {"name": "routineDeclaration$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "paramList$ebnf$1", "symbols": []},
    {"name": "paramList$ebnf$1", "symbols": ["paramList$ebnf$1$subexpression$1", "paramList$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "possiblyTypedExpression$ebnf$1", "symbols": ["possiblyTypedExpression$ebnf$1$subexpression$1"], "postprocess": id},
    {"name": "possiblyTypedExpression$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "setDeclaration$ebnf$1", "symbols": []},
    {"name": "setDeclaration$ebnf$1", "symbols": ["setDeclaration$ebnf$1$subexpression$1", "setDeclaration$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "subsetDeclaration$ebnf$1", "symbols": []},
    {"name": "subsetDeclaration$ebnf$1", "symbols": ["subsetDeclaration$ebnf$1$subexpression$1", "subsetDeclaration$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "listExpression$ebnf$1", "symbols": []},
    {"name": "listExpression$ebnf$1", "symbols": ["listExpression$ebnf$1$subexpression$1", "listExpression$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "lambdaExpression$ebnf$1", "symbols": ["lambdaExpression$ebnf$1$subexpression$1"]},
    {"name": "lambdaExpression$ebnf$1", "symbols": ["lambdaExpression$ebnf$1$subexpression$2", "lambdaExpression$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "identifier$ebnf$1", "symbols": [{"literal":"."}]},
    {"name": "identifier$ebnf$1", "symbols": [{"literal":"."}, "identifier$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "idrest$ebnf$1", "symbols": []},
    {"name": "idrest$ebnf$1", "symbols": ["letterOrDigit", "idrest$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "idrest$ebnf$2", "symbols": []},
    {"name": "idrest$ebnf$2", "symbols": ["letterOrDigit", "idrest$ebnf$2"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "num$ebnf$1", "symbols": ["digit"]},
    {"name": "num$ebnf$1", "symbols": ["digit", "num$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "op$ebnf$1", "symbols": ["opchar"]},
    {"name": "op$ebnf$1", "symbols": ["opchar", "op$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "escaped$ebnf$1", "symbols": []},
    {"name": "escaped$ebnf$1", "symbols": [/[^"]/, "escaped$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "_$ebnf$1", "symbols": []},
    {"name": "_$ebnf$1", "symbols": [/[\s]/, "_$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "__$ebnf$1", "symbols": [/[\s]/]},
    {"name": "__$ebnf$1", "symbols": [/[\s]/, "__$ebnf$1"], "postprocess": function arrconcat(d) {return [d[0]].concat(d[1]);}},
    {"name": "routineDeclaration$ebnf$1$subexpression$1", "symbols": ["_", "paramList"]},
    {"name": "paramList$ebnf$1$subexpression$1", "symbols": ["_", "comma", "_", "variable"]},
    {"name": "possiblyTypedExpression$ebnf$1$subexpression$1", "symbols": ["_", "colon", "_", "type"]},
    {"name": "setDeclaration$ebnf$1$subexpression$1", "symbols": ["__", "variable"]},
    {"name": "subsetDeclaration$ebnf$1$subexpression$1", "symbols": ["__", "variable"]},
    {"name": "listExpression$ebnf$1$subexpression$1", "symbols": ["_", "comma", "_", "expression"]},
    {"name": "lambdaExpression$ebnf$1$subexpression$1", "symbols": ["possiblyTypedLambdaParameter", "__"]},
    {"name": "lambdaExpression$ebnf$1$subexpression$2", "symbols": ["possiblyTypedLambdaParameter", "__"]}
]
  , ParserStart: "expression"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();
