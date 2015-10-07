###############################
####### ROOT EXPRESSION #######
###############################

expression 	-> setDeclaration {% id %}
	| untypedExpression (_ colon _ type):? {% function(d) {
		if (d[1] === null) {
			return d[0];
		} else {
			d[0].type = d[1][3];
			return d[0].type && d[0];
		} } %}

###############################
####### SET DECLARATION #######
###############################

setDeclaration -> identifier ":set" {% function(d) { return declareSet(d[0]); } %}

###########################################
####### LAMBDA CALCULUS EXPRESSIONS #######
###########################################

untypedExpression -> applicationExpression {% id %}
    | lambdaExpression {% id %}

applicationExpression -> applicationWithInfixExpression {% id %}
	| applicationWithoutInfixExpression {% id %}

applicationWithInfixExpression -> applicationOnNonLambdaExpression _ notatedInfixOperator _ applicationExpression {% function(d) {return application(application(d[2], d[0]), d[4]);} %}
	| applicationOnNonLambdaExpression _ defaultInfixOperator _ applicationExpression {% function(d) {return tree(d[2], [d[0], d[4]]); } %}

# to parse application as <A> <B>, we need to have:
# - no unparenthesized lambdas in A (otherwise lambda body would include B)
# - no unparenthesized applications in B (because left associativity)
# - no unparenthesized variables / applications in A if B is a lambda (otherwise A could be treated as parameters of B)

applicationWithoutInfixExpression -> applicationOnNonLambdaExpression __ rootExpression {% function(d) {return application(d[0], d[2]); } %}
	| parenthesizedExpression __ lambdaExpression {% function(d) {return application(d[0], d[2]); } %}
	| fixedOrRootExpression {% id %}

applicationOnNonLambdaExpression -> applicationOnNonLambdaExpression __ rootExpression {% function(d) {return application(d[0], d[2]); } %}
	| fixedOrRootExpression {% id %}

lambdaOrRootExpression -> lambdaExpression {% id %}
	| rootExpression {% id %}

fixedOrRootExpression -> fixedExpression {% id %}
	| rootExpression {% id %}

fixedExpression -> fix __ rootExpression {% function(d) { return fixedExpression(d[2]); } %}

rootExpression -> parenthesizedExpression {% id %}
 	| listExpression {% id %}
    | variable {% id %}

listExpression -> leftbracket _ expression (_ comma _ expression):* _ rightbracket {% function(d) {
	var consHelper = function (vars) {
		if (vars.length === 0) {
			return variable("nil");
		} else {
			return cons(vars[0][3], consHelper(vars.slice(1)));
		}
	}
	return cons(d[2], consHelper(d[3]));
} %}

parenthesizedExpression -> leftparen expression rightparen {% function(d) {return d[1];} %}

lambdaExpression -> ( possiblyTypedLambdaParameter __ ):+ arrow _ expression  {%
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

possiblyTypedLambdaParameter -> variable {% id %}
	| leftparen variable _ colon _ type rightparen {% function(d) {
		d[1].type = d[5];
		return d[5] && d[1]; } %}

variable -> identifier {% function(d) {return variable(d[0]); } %}

notatedInfixOperator -> backtick variable backtick {% function(d) {return d[1]; } %}
	| [+*\-] {% function(d) {return tree(operator(d[0]),[]); } %}

defaultInfixOperator -> "/" {% function(d) {return operator(d[0]); } %}

################################
####### TYPE EXPRESSIONS #######
################################

type -> typeWithOperations _ typeArrow _ type {% function(d) {return typeOperation(d[2], d[0], d[4]); } %}
	| typeWithOperations {% id %}

## assume type operators (\, * and ∩) are left associative
typeWithOperations -> typeWithOperations _ typeOperator _ rootType {% function(d) {return typeOperation(d[2], d[0], d[4]); } %}
	| rootType {% id %}

typeOperator -> [×∩] {% id %}

rootType -> leftparen type rightparen {% function(d) {return d[1];} %}
	| typeVariable {% id %}

typeVariable -> identifier {% function(d) {return typeVariable(d[0]); } %}

####################################
####### TOKENS FOR TOKENIZER #######
####################################

identifier -> letter idrest {% function(d) {return d[0].concat(d[1]); } %}
	| op {% id %}

idrest -> letterOrDigit:* {% function(d) {return d[0].join(""); } %}
	| letterOrDigit:* underscore op {% function(d) {return d[0].join("").concat("_").concat(d[2]);} %}

letterOrDigit -> letter {% id %}
	| digit {% id %}

## unicode ranges for letter regex taken from http://stackoverflow.com/questions/150033/regular-expression-to-match-non-english-characters
letter -> [a-zA-Z$_\u00C0-\u1FFF\u2080-\u2089\u2C00-\uD7FF] {% id %}
digit -> [0-9] {% id %}

op -> validStandaloneOpchars {% id %}
	| opchar opchar:+ {% function(d) { return [d[0]].concat(d[1]).join(""); } %}

validStandaloneOpchars -> [!%&*+<>?^|~\\\-] {% id %}
opchar -> validStandaloneOpchars {% id %}
	| [=#@\:] {% id %}

# _ represents optional whitespace; __ represents compulsory whitespace
_ -> [\s]:*    {% function(d) {return null; } %}
__ -> [\s]:+   {% function(d) {return null; } %}

arrow -> "↦"
leftparen -> "("
rightparen -> ")"
leftbracket -> "⟨"
rightbracket -> "⟩"
underscore -> "_"
forwardslash -> "/"
backtick -> "`"
colon -> ":"
comma -> ","
typeArrow -> "->" {% id %}
fix -> "fix"