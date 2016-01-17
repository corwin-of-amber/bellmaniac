root = exports ? this

root.scope = []
root.id = (d) -> d && d[0]
root.take = (index) -> (d) -> d && d[index]
root.keywords = ["set", "fix", "/", "+", "×", "∩", "-", "*", ":-"]

## combinators

root.tree = (root, subtrees) ->
    $: \Tree
    root: root
    subtrees: subtrees

root.identifier = (literal, kind) ->
    $: \Identifier
    literal: literal
    kind: kind
    ns: if literal is /^\?/ then "*" else undefined

root.operator = (literal) -> identifier(literal, \operator)

root.genericIdentifier = (literal) -> identifier(literal, \?)

toPretty = (t) ->
  if t.subtrees.length > 0
    "#{t.root.literal}{#{t.subtrees.map toPretty .join ', '}}"
  else
    "#{t.root.literal}"

## variables and type-variables: convert to false if literals are reserved keywords

root.declareSet = (literal) ->
    if root.keywords.indexOf(literal) == -1
        identifier(literal, \set)
            root.scope.push ..
    else
        # console.error <| "Literal " + literal + " is reserved."
        void

root.declareSets = (head, tail) ->
    kind: \set
    multiple:
        for v in [head, ...tail]
            identifier(v.root.literal, \set)

root.declareSubsets = (head, tail, superset) ->
    if !(superset.subtrees.length == 0 && superset.root.kind == \set)
        return void  # bleh. this does not report the reason for rejection.
        # should report: "expected a set type but found '#{toPretty superset}'"
    kind: \set
    multiple:
        for v in [head, ...tail]
            [identifier(v.root.literal, \set), identifier(superset.root.literal, \set)]

root.typeVariable = (literal) ->
    if root.keywords.indexOf(literal) > -1
        # console.error <| "Literal " + literal + " is reserved."
        void
    else if root.scope.some((set) ->
        set.literal == literal || set[0]?.literal == literal
    )
        tree(identifier(literal, \set), [])
    else
        # console.error <| "Literal " + literal + " has not yet been declared as a set."
        tree(identifier(literal, "type variable"), [])

root.variable = (literal) ->
    if literal not in root.keywords && !root.scope.some((.literal == literal))
        tree(identifier(literal, \variable), [])
    else
        # console.error <| "Literal " + literal + " is reserved or has been declared as a set."
        void

## recursive calls; trickle up nulls if any subtree is null

root.abstraction = (par, body) -> par && body && tree(genericIdentifier(\↦), [par, body])

root.application = (lhs, rhs) -> lhs && rhs && tree(genericIdentifier(\@), [lhs, rhs])

root.typeOperation = (op, lhs, rhs) -> op && lhs && rhs && tree(operator(op), [lhs, rhs])

root.functionType = (lhs, rhs) -> lhs && rhs && tree(genericIdentifier(\->), [lhs, rhs])

root.slashExpression = (lhs, rhs) -> lhs && rhs && tree(operator(\/), [lhs, rhs])

root.fixedExpression = (subj) -> subj && tree(operator(\fix), [subj])

root.cons = (car, cdr) -> application(application(variable(\cons), car), cdr)
