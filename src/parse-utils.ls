root = exports ? this

root.scope = []
root.id = (d) -> d && d[0]
root.keywords = ["set", "fix", "/"]

## combinators

root.tree = (root, subtrees) ->
	$: \Tree,
	root: root,
	subtrees: subtrees

root.identifier = (literal, kind) ->
	$: \Identifier,
	literal: literal,
	kind: kind

root.genericIdentifier = (literal) -> identifier(literal, \?)

## variables and type-variables: convert to null if literals are reserved keywords

root.declareSet = (literal) ->
	if root.keywords.indexOf(literal) == -1
		newSet = tree(identifier(literal, \set), [])
		root.scope.push newSet
		newSet
	else
		# console.error <| "Literal " + literal + " is reserved."
		null

root.typeVariable = (literal) ->
	if root.keywords.indexOf(literal) == -1 && root.scope.filter((set) ->
		set.root.literal == literal
	).length > 0
		tree(identifier(literal, \set))
	else
		# console.error <| "Literal " + literal + " is reserved or has not yet been declared as a set."
		null

root.variable = (literal) ->
	if root.keywords.indexOf(literal) == -1 && root.scope.filter((set) ->
		set.root.literal == literal
	).length == 0
		tree(identifier(literal, \variable), [])
	else
		# console.error <| "Literal " + literal + " is reserved or has been declared as a set."
		null

## recursive calls; trickle up nulls if any subtree is null

root.abstraction = (par, body) -> par && body && tree(genericIdentifier(\↦), [par, body])

root.application = (lhs, rhs) -> lhs && rhs && tree(genericIdentifier(\@), [lhs, rhs])

root.typeOperation = (op, lhs, rhs) -> op && lhs && rhs && tree(tree(op), [lhs, rhs])

root.slashExpression = (lhs, rhs) -> lhs && rhs && tree(genericIdentifier(\/), [lhs, rhs])