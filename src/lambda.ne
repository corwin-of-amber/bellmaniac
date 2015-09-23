###############################
####### ROOT EXPRESSION #######
###############################

expression 	-> untypedExpression (_ colon _ type):? {% function(d) { if (d[1] === null) { return d[0]; } else { d[0].type = d[1][3]; return d[0]; } } %}

###########################################
####### LAMBDA CALCULUS EXPRESSIONS #######
###########################################

untypedExpression -> applicationExpression {% function(d) { return d[0];} %}
             | lambdaExpression {% id %}

applicationExpression -> applicationWithInfixExpression {% id %}
	| applicationWithoutInfixExpression{% id %}

applicationWithInfixExpression -> applicationOnNonLambdaExpression __ infixOperator __ applicationExpression
	{% function(d) {return {$: "Tree", lhs: {$: "Tree", lhs: d[2], rhs: d[0]}, rhs: d[4]}; } %}

# to parse application as <A> <B>, we need to have:
# - no unparenthesized lambdas in A (otherwise lambda body would include B)
# - no unparenthesized applications in B (because left associativity)
# - no unparenthesized variables / applications in A if B is a lambda (otherwise A could be treated as parameters of B)

applicationWithoutInfixExpression -> applicationOnNonLambdaExpression __ rootExpression {% function(d) {return application(d[0], d[2]); } %}
		| parenthesizedExpression __ lambdaExpression {% function(d) {return application(d[0], d[2]); } %}
		| rootExpression {% id %}

applicationOnNonLambdaExpression -> applicationOnNonLambdaExpression __ rootExpression {% function(d) {return application(d[0], d[2]); } %}
		 | rootExpression {% id %}

lambdaOrRootExpression -> lambdaExpression {% id %}
						| rootExpression {% id %}

rootExpression -> parenthesizedExpression {% id %}
          | variable {% id %}

parenthesizedExpression -> leftparen expression rightparen {% function(d) {return d[1];} %}

lambdaExpression -> ( possiblyTypedVariable _ ):+ arrow _ expression  {%
	function(d) {
		var curry = function(vars, lbody) {
			if (vars.length === 1) {
				return abstraction(vars[0][0], lbody);
			} else {
				return abstraction(vars[0][0], curry(vars.slice(1), lbody));
			}
		};
		return curry(d[0], d[3]);
	} %}

possiblyTypedVariable -> variable {% function(d) {return d[0];} %}
	| leftparen variable _ colon _ type rightparen {% function(d) { d[1].type = d[5]; return d[1]; } %}

variable -> identifier {% function(d) {return variable(d[0]); } %}

infixOperator -> backtick variable backtick {% function(d) {return d[1]; } %}

################################
####### TYPE EXPRESSIONS #######
################################

type -> typeWithOperations _ typeArrow _ type {% function(d) {return typeOperation(d[2], d[0], d[4]); } %}
	| typeWithOperations {% id %}

## assume type operators (\, * and ∩) are left associative
typeWithOperations -> typeWithOperations __ typeOperator __ rootType {% function(d) {return typeOperation(d[2], d[0], d[4]); } %}
	| rootType {% id %}

typeOperator -> [*∩\\] {% id %}

rootType -> leftparen type rightparen {% function(d) {return d[1];} %}
	| typeVariable {% id %}

typeVariable -> identifier {% function(d) {return typeVariable(d[0]); } %}

####################################
####### TOKENS FOR TOKENIZER #######
####################################

identifier      -> letter idrest {% function(d) {return d[0].concat(d[1]); } %}
	| op {% id %}

idrest -> letterOrDigit:* {% function(d) {return d[0].join(""); } %}
		| letterOrDigit:* underscore op {% function(d) {return d[0].join("").concat("_").concat(d[2]);} %}

letterOrDigit -> letter {% function(d) {return d[0]; } %} | digit {% function(d) {return d[0]; } %}

## unicode ranges for letter regex taken from http://stackoverflow.com/questions/150033/regular-expression-to-match-non-english-characters
letter -> [a-zA-Z$_\u00C0-\u1FFF\u2C00-\uD7FF] {% function(d) {return d[0]; } %}
digit -> [0-9] {% function(d) {return d[0]; } %}

op -> validStandaloneOpchars {% function(d) {return d[0]; } %}
	| opchar opchar:+ {% function(d) { return [d[0]].concat(d[1]).join(""); } %}

validStandaloneOpchars -> [!%&*+<>?^|~\\\-] {% function(d) {return d[0]; } %}
opchar -> validStandaloneOpchars {% function(d) {return d[0]; } %} | [=#@\:] {% function(d) {return d[0]; } %}

# _ represents optional whitespace; __ represents compulsory whitespace
_ -> [\s]:*    {% function(d) {return null; } %}
__ -> [\s]:+   {% function(d) {return null; } %}

arrow -> "↦"
leftparen -> "("
rightparen -> ")"
underscore -> "_"
backtick -> "`"
colon -> ":"
typeArrow -> "->" {% id %}