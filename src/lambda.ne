###############################
####### ROOT EXPRESSION #######
###############################

expression 	-> untypedExpression (_ colon _ type):? {% function(d) { if (d[1] === null) { return d[0]; } else { d[0].type = d[1][3]; return d[0]; } } %}

###########################################
####### LAMBDA CALCULUS EXPRESSIONS #######
###########################################

untypedExpression -> applicationExpression {% function(d) { return d[0];} %}
             | lambdaExpression {% function(d) {return d[0]; } %}

applicationExpression -> applicationWithInfixExpression {% function(d) { return d[0]; } %}
	| applicationWithoutInfixExpression{% function(d) { return d[0]; } %}

applicationWithInfixExpression -> applicationOnNonLambdaExpression __ infixOperator __ applicationExpression
	{% function(d) {return {$: "Application", lhs: {$: "Application", lhs: d[2], rhs: d[0]}, rhs: d[4]}; } %}

# for left associativity, parsing application as <A> <B> must have no application expressions in <B>
# also no lambda expressions in <A> (since such a lambda expression would include B in its body)

applicationWithoutInfixExpression -> applicationOnNonLambdaExpression __ lambdaOrRootExpression {% function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } %}
		 | rootExpression {% function(d) {return d[0]; } %}

applicationOnNonLambdaExpression -> applicationOnNonLambdaExpression __ rootExpression {% function(d) {return {$: "Application", lhs: d[0], rhs: d[2]}; } %}
		 | rootExpression {% function(d) {return d[0]; } %}

lambdaOrRootExpression -> lambdaExpression {% function(d) {return d[0]; } %}
						| rootExpression {% function(d) {return d[0]; } %}

rootExpression -> leftparen expression rightparen {% function(d) {return d[1];} %}
          | variable {% function(d) {return d[0]; } %}

lambdaExpression -> lambda _ ( possiblyTypedVariable _ ):+ arrow _ expression  {%
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

possiblyTypedVariable -> leftparen possiblyTypedVariable rightparen {% function(d) {return d[1];} %}
	| variable (_ colon _ type):? {% function(d) { if (d[1] === null) { return d[0]; } else { d[0].type = d[1][3]; return d[0]; } } %}

variable -> identifier {% function(d) {return {$: "Identifier", kind: "variable", literal: d[0]}; } %}

infixOperator -> backtick variable backtick {% function(d) {return d[1]; } %}

################################
####### TYPE EXPRESSIONS #######
################################

type -> type _ typeArrow _ rootType {% function(d) {return {$: "Tree", kind: "function", from: d[0], to: d[4]};} %}
	| type _ typeOperator _ rootType {% function(d) {return {$: "Tree", kind: "operation", lhs: d[0], rhs: d[4], operator: d[2]}; } %}
	| rootType {% function(d) {return d[0]; } %}

typeOperator -> [*<>∩∪\\] {% function(d) {return d[0]; } %}

rootType -> leftparen type rightparen {% function(d) {return d[1];} %}
	| typeVariable {% function(d) {return d[0]; } %}

typeVariable -> letter {% function(d) {return {$: "Identifier", kind: "type", literal: d[0]}; } %}

####################################
####### TOKENS FOR TOKENIZER #######
####################################

identifier      -> letter idrest {% function(d) {return d[0].concat(d[1]); } %}
	| op {% function(d) {return d[0]; } %}

idrest -> letterOrDigit:* {% function(d) {return d[0].join(""); } %}
		| letterOrDigit:* underscore op {% function(d) {return d[0].join("").concat("_").concat(d[2]);} %}

letterOrDigit -> letter {% function(d) {return d[0]; } %} | digit {% function(d) {return d[0]; } %}

## unicode ranges for letter regex taken from http://stackoverflow.com/questions/150033/regular-expression-to-match-non-english-characters
letter -> [a-zA-Z$_\u00C0-\u1FFF\u2C00-\uD7FF] {% function(d) {return d[0]; } %}
digit -> [0-9] {% function(d) {return d[0]; } %}

op -> validStandaloneOpchars {% function(d) {return d[0]; } %}
	| opchar opchar:+ {% function(d) { return d[0].join(""); } %}

validStandaloneOpchars -> [!%&*+<>?^|~\\\-] {% function(d) {return d[0]; } %}
opchar -> validStandaloneOpchars {% function(d) {return d[0]; } %} | [=#@\:] {% function(d) {return d[0]; } %}

# _ represents optional whitespace; __ represents compulsory whitespace
_ -> [\s]:*    {% function(d) {return null; } %}
__ -> [\s]:+   {% function(d) {return null; } %}

arrow -> "↦"
leftparen -> "("
rightparen -> ")"
lambda -> "λ"
underscore -> "_"
backtick -> "`"
colon -> ":"
typeArrow -> "->"