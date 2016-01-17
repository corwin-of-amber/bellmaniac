###############################
####### ROOT EXPRESSION #######
###############################

expression 	-> setMode {% id %}
    | setDeclaration {% id %}
    | subsetDeclaration {% id %}
    | possiblyTypedExpression {% id %}
    | routineDeclaration {% id %}

routineDeclaration -> variable (_ paramList):? _ colondash _ possiblyTypedExpression {% function(d) {
    return {
      kind: 'routine',
      name: d[0].root.literal,
      params: d[1] ? d[1][1] : [],
      body: d[5]
    };
} %}

paramList -> leftsquarebracket _ typeVariable (_ comma _ typeVariable):* _ rightsquarebracket {% function(d) {
	if (d[3].length === 0) {
		return [d[2]];
	} else {
		return [d[2]].concat(d[3].map(take(3)));
	}
} %}

possiblyTypedExpression -> untypedExpression (_ colon _ type):? {% function(d) {
		if (d[1] === null) {
			return d[0];
		} else {
			d[0].type = d[1][3];
			return d[0].type && d[0];
		} } %}

###########################
####### MODE SWITCH #######
###########################

setMode ->
    "∵" {% function() { return {setMode: "tactic"}; } %}
  | "∎" {% function() { return {setMode: "tactic"}; } %}

###############################
####### SET DECLARATION #######
###############################

setDeclaration -> variable (__ variable):* _ colon _ "set" {%
  function(d, loc, reject) { return declareSets(d[0], d[1].map(take(1))) || reject; } %}

subsetDeclaration -> variable (__ variable):* _ subseteq  _ typeVariable {%
  function(d, loc, reject) { return declareSubsets(d[0], d[1].map(take(1)), d[5]) || reject; } %}

###########################################
####### LAMBDA CALCULUS EXPRESSIONS #######
###########################################

untypedExpression -> applicationExpression {% id %}
    | lambdaExpression {% id %}

applicationExpression -> applicationWithInfixExpression {% id %}
	| applicationWithoutInfixExpression {% id %}

applicationWithInfixExpression -> applicationExpression _ notatedInfixOperator _ applicationWithoutInfixExpression {% function(d) {return application(application(d[2], d[0]), d[4]);} %}
	| applicationExpression _ defaultInfixOperator _ applicationWithoutInfixExpression {% function(d) {return tree(d[2], [d[0], d[4]]); } %}

# to parse application as <A> <B>, we need to have:
# - no unparenthesized lambdas in A (otherwise lambda body would include B)
# - no unparenthesized applications in B (because left associativity)
# - no unparenthesized variables / applications in A if B is a lambda (otherwise A could be treated as parameters of B)

applicationWithoutInfixExpression -> applicationOnNonLambdaExpression __ fixedOrRootExpression {% function(d) {return application(d[0], d[2]); } %}
	| parenthesizedExpression __ lambdaExpression {% function(d) {return application(d[0], d[2]); } %}
	| fixedOrRootExpression {% id %}

applicationOnNonLambdaExpression -> applicationOnNonLambdaExpression __ fixedOrRootExpression {% function(d) {return application(d[0], d[2]); } %}
	| rootExpression {% id %}

lambdaOrRootExpression -> lambdaExpression {% id %}
	| rootExpression {% id %}

fixedOrRootExpression -> fixedExpression {% id %}
	| rootExpression {% id %}

fixedExpression -> fix __ lambdaOrRootExpression {% function(d) { return fixedExpression(d[2]); } %}

rootExpression -> parenthesizedExpression {% id %}
 	| listExpression {% id %}
    | variable {% id %}
    | integer {% id %}
    | backtick _ type {% take(2) %}

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

variable -> identifier {% function(d, loc, reject) {return variable(d[0]) || reject; } %}
    | escaped {% function(d) { return tree(identifier(d[0],'variable')); } %}

integer -> num {% function(d) { return tree(identifier(d[0],'?')); } %}

notatedInfixOperator -> backtick variable backtick {% function(d) {return d[1]; } %}
	| [+*\-] {% function(d, loc, reject) {return tree(identifier(d[0],'variable')); } %}

defaultInfixOperator -> "/" {% function(d) {return operator(d[0]); } %}

################################
####### TYPE EXPRESSIONS #######
################################

type -> typeWithOperations _ typeArrow _ type {% function(d) {return functionType(d[0], d[4]); } %}
	| typeWithOperations {% id %}

## type operators (× and ∩) are right associative
typeWithOperations ->
      typeWithOperations _ "×" _ rootType {% function(d) {return typeOperation(d[2], d[0], d[4]); } %}
    | typeWithOperations _ "∩" _ variable {% function(d) {return typeOperation(d[2], d[0], d[4]); } %}
	| rootType {% id %}

rootType -> leftparen type rightparen {% function(d) {return d[1];} %}
	| typeVariable {% id %}

typeVariable -> identifier {% function(d, loc, reject) {return typeVariable(d[0]) || reject; } %}

####################################
####### TOKENS FOR TOKENIZER #######
####################################

identifier -> letter idrest {% function(d) {return d[0].concat(d[1]); } %}
	| op {% id %}
    | ".":+ {% function(d) {return d[0].join(""); } %}

idrest -> letterOrDigit:* {% function(d) {return d[0].join(""); } %}
	| letterOrDigit:* underscore op {% function(d) {return d[0].join("").concat("_").concat(d[2]);} %}

letterOrDigit -> letter {% id %}
	| digit {% id %}

## unicode ranges for letter regex taken from http://stackoverflow.com/questions/150033/regular-expression-to-match-non-english-characters
letter -> [a-zA-Z$_\u00C0-\u00D6\u00D8-\u1FFF\u2080-\u2089\u2C00-\uD7FF] {% id %}
digit -> [0-9] {% id %}

letter -> [\uD83C\uDD30-\uDD49] {% id %}    # boxed letters

num -> digit:+ {% function(d) { return parseInt(d[0].join("")); } %}

op -> validStandaloneOpchars {% id %}
	| opchar opchar:+ {% function(d) { return [d[0]].concat(d[1]).join(""); } %}

validStandaloneOpchars -> [!%&*+<>?^|~\\\-] {% id %}
opchar -> validStandaloneOpchars {% id %}
	| [=#@\:] {% id %}

escaped -> ["] [^"]:* ["] {% function(d) { return d[1].join(""); } %}

# _ represents optional whitespace; __ represents compulsory whitespace
_ -> [\s]:*    {% function(d) {return null; } %}
__ -> [\s]:+   {% function(d) {return null; } %}

arrow -> "↦"
leftparen -> "("
rightparen -> ")"
leftbracket -> "⟨"
rightbracket -> "⟩"
leftsquarebracket -> "["
rightsquarebracket -> "]"
underscore -> "_"
forwardslash -> "/"
colondash -> ":-"
backtick -> "`"
subseteq -> "⊆"
colon -> ":"
comma -> ","
typeArrow -> "->" {% id %} | "→" {% function() { return "->"; } %}
fix -> "fix"