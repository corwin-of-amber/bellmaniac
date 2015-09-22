expression 	-> applicationExpression {% function(d) {return d[0]; } %}
             | lambdaExpression {% function(d) {return d[0]; } %}

applicationExpression -> applicationWithInfixExpression {% function(d) { return d[0]; } %}
	| applicationWithoutInfixExpression{% function(d) { return d[0]; } %}

applicationWithInfixExpression -> applicationOnNonLambdaExpression _ infixOp _ applicationExpression
	{% function(d) {return {$: "Application", lhs: {$: "Application", lhs: d[2], rhs: d[0]}, rhs: d[4]}; } %}

# for left associativity, parsing application as <A> <B> must have no application expressions in <B>
# also no lambda expressions in <A> (since such a lambda expression would include B in its body)

applicationWithoutInfixExpression -> applicationOnNonLambdaExpression _ lambdaOrRootExpression {% function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } %}
		 | rootExpression {% function(d) {return d[0]; } %}

applicationOnNonLambdaExpression -> applicationOnNonLambdaExpression _ rootExpression {% function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } %}
		 | rootExpression {% function(d) {return d[0]; } %}

lambdaOrRootExpression -> lambdaExpression {% function(d) {return d[0]; } %}
						| rootExpression {% function(d) {return d[0]; } %}

rootExpression -> leftparen expression rightparen {% function(d) {return d[1];} %}
          | variable {% function(d) {return d[0]; } %}

lambdaExpression -> lambda _ ( variable _ ):+ arrow _ expression  {%
	function(d) {
		var curry = function(vars, lbody) {
			if (vars.length === 1) {
				return {$: "Abstraction", var: vars[0][0], lbody: lbody};
			} else {
				return {$: "Abstraction", var: vars[0][0], lbody: curry(vars.slice(1), lbody)};
			}
		};
		return curry(d[2], d[5]);
	} %}

variable      -> letter idrest {% function(d) {return {$: "Identifier", kind: "variable", literal: d[0].concat(d[1])}; } %}
	| op {% function(d) {return {$: "Identifier", kind: "variable", literal: d[0]}; } %}
infixOp -> backtick variable backtick {% function(d) {return d[1]; } %}

# SYMBOLS

_ -> [\s]:+    {% function(d) {return null; } %}
opchar -> [!%&#*+:<=>?@^|~\\\-\/] {% function(d) {return d[0]; } %}
op -> opchar:* {% function(d) { return d[0].join(""); } %}
## unicode ranges for letter regex taken from http://stackoverflow.com/questions/150033/regular-expression-to-match-non-english-characters
letter -> [a-zA-Z\u0024\u005F\u00C0-\u1FFF\u2C00-\uD7FF] {% function(d) {return d[0]; } %}
digit -> [0-9] {% function(d) {return d[0]; } %}
letterOrDigit -> letter {% function(d) {return d[0]; } %} | digit {% function(d) {return d[0]; } %}
idrest -> letterOrDigit:* {% function(d) {return d[0].join(""); } %}
		| letterOrDigit:* underscore op {% function(d) {return d[0].join("").concat("_").concat(d[2]);} %}
arrow -> "↦"
leftparen -> "("
rightparen -> ")"
lambda -> "λ"
underscore -> "_"
backtick -> "`"

