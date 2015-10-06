root = exports ? this

root.id = (d) -> d[0]

root.tree = (root, subtrees) ->
	$: \Tree,
	root: root,
	subtrees: subtrees

root.identifier = (literal, kind) ->
	$: \Identifier,
	literal: literal,
	kind: kind

root.genericIdentifier = (literal) -> identifier(literal, \?)

root.variable = (literal) -> tree(identifier(literal, \variable), [])

root.abstraction = (par, body) -> tree(genericIdentifier(\↦), [par, body])

root.application = (lhs, rhs) -> tree(genericIdentifier(\@), [lhs, rhs])

root.typeOperation = (op, lhs, rhs) -> tree(tree(op), [lhs, rhs])

root.typeVariable = (literal) -> tree(identifier(literal, \?), [])