root = exports ? this

root.scope = []
root.id = (d) -> d && d[0]
root.take = (index) -> (d) -> d && d[index]
root.keywords = ["set", "fix", "/", "+", "×", "∩", "-", "*"]

## combinators

root.tree = (root, subtrees) ->
	$: \Tree,
	root: root,
	subtrees: subtrees

root.identifier = (literal, kind) ->
	$: \Identifier,
	literal: literal,
	kind: kind

root.operator = (literal) -> identifier(literal, \operator)

root.genericIdentifier = (literal) -> identifier(literal, \?)

## variables and type-variables: convert to false if literals are reserved keywords

root.declareSet = (literal) ->
	if root.keywords.indexOf(literal) == -1
		newSet = tree(identifier(literal, \set), [])
		root.scope.push newSet
		newSet
	else
		# console.error <| "Literal " + literal + " is reserved."
		false

root.declareSets = (head, tail) ->
	for literal in [head] ++ tail
		if !(newSet = root.declareSet(literal))
			return false
	newSet # returns last set?
        
root.typeVariable = (literal) ->
	if root.keywords.indexOf(literal) > -1
		# console.error <| "Literal " + literal + " is reserved."
		false
	else if root.scope.filter((set) ->
		set.root.literal == literal
	).length > 0
		tree(identifier(literal, \set), [])
	else
		# console.error <| "Literal " + literal + " has not yet been declared as a set."
		tree(identifier(literal, 'type variable'), [])

root.variable = (literal) ->
	if root.keywords.indexOf(literal) == -1 && root.scope.filter((set) ->
		set.root.literal == literal
	).length == 0
		tree(identifier(literal, \variable), [])
	else
		# console.error <| "Literal " + literal + " is reserved or has been declared as a set."
		false

## recursive calls; trickle up nulls if any subtree is null

root.abstraction = (par, body) -> par && body && tree(genericIdentifier(\↦), [par, body])

root.application = (lhs, rhs) -> lhs && rhs && tree(genericIdentifier(\@), [lhs, rhs])

root.typeOperation = (op, lhs, rhs) -> op && lhs && rhs && tree(operator(op), [lhs, rhs])

root.slashExpression = (lhs, rhs) -> lhs && rhs && tree(operator(\/), [lhs, rhs])

root.fixedExpression = (subj) -> subj && tree(operator(\fix), [subj])

root.cons = (car, cdr) -> application(application(variable(\cons), car), cdr)