var id = function(d) { return d[0]; };

var tree = function(root, subtrees) {
	return {$: "Tree", root: root, subtrees: subtrees};
};

var identifier = function(literal, kind) {
	return {$: "Identifier", literal: literal, kind: kind};
};

var genericIdentifier = function(literal) {
	return identifier(literal, "?");
};

var variable = function(literal) {
	return tree(identifier(literal, "variable"), []);
};

var abstraction = function(par, body) {
	return tree(identifier("↦", "?"), [par, body]);
};

var application = function(lhs, rhs) {
	return tree(identifier("@", "?"), [lhs, rhs]);
};

var typeOperation = function(op, lhs, rhs) {
	return tree(genericIdentifier(op), [lhs, rhs]);
};

var typeVariable = function(literal) {
	return tree(genericIdentifier(literal), []);
};