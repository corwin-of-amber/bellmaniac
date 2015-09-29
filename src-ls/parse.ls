spawn = require \child_process .spawn
_ = require \lodash
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*$/

angular.module 'app', [\RecursionHelper, \ui.codemirror]
  ..controller "Ctrl" ($scope) !->

    $scope.code = "moo"
    $scope.editorOptions =
        mode:  "scheme",
        theme: "material"
    $scope.parsed = {}
    $scope.output = {}
    $scope.data = []

    $scope.codemirrorLoaded = (editor) ->
        words =
            * text: "α", displayText: "\\alpha"
            * text: "β", displayText: "\\beta"
            * text: "γ", displayText: "\\gamma"
            * text: "δ", displayText: "\\delta"
            * text: "ε", displayText: "\\epsilon"
            * text: "ζ", displayText: "\\zeta"
            * text: "η", displayText: "\\eta"
            * text: "θ", displayText: "\\theta"
            * text: "ι", displayText: "\\iota"
            * text: "κ", displayText: "\\kappa"
            * text: "λ", displayText: "\\lambda"
            * text: "μ", displayText: "\\mu"
            * text: "ν", displayText: "\\nu"
            * text: "ξ", displayText: "\\xi"
            * text: "ο", displayText: "\\omicron"
            * text: "π", displayText: "\\pi"
            * text: "ρ", displayText: "\\rho"
            * text: "σ", displayText: "\\sigma"
            * text: "τ", displayText: "\\tau"
            * text: "υ", displayText: "\\upsilon"
            * text: "φ", displayText: "\\phi"
            * text: "χ", displayText: "\\chi"
            * text: "ψ", displayText: "\\psi"
            * text: "ω", displayText: "\\omega"
            * text: "↦", displayText: "|->"
            * text: "×", displayText: "\\times"
            * text: "∩", displayText: "\\cap"

        CodeMirror.registerHelper "hint", "anyword", (editor, options) ->
            delimiters = /[\\|]/
            whitespace = /\s/
            cur = editor.getCursor(); curLine = editor.getLine(cur.line)
            start = cur.ch; end = start
            while (end < curLine.length && !whitespace.test(curLine.charAt(end)))
                end += 1
            while (start >= 1 && !delimiters.test(curLine.charAt(start)) && !whitespace.test(curLine.charAt(start-1)))
                start -= 1
            curWord = if start != end then curLine.slice(start, end) else ""

            filteredWords = words.filter (w) ->
                curWord.length > 0 && w.displayText.indexOf(curWord) == 0

            list: filteredWords,
            from: CodeMirror.Pos(cur.line, start),
            to: CodeMirror.Pos(cur.line, end)

        CodeMirror.commands.autocomplete = (cm) ->
            cm.showHint hint: CodeMirror.hint.anyword, completeSingle: false

        editor.on 'keyup', (editor, e) !->
            keycode = e.keyCode
            valid =
                (keycode > 47 && keycode < 58)   || # number keys
                (keycode == 32 || keycode == 13)   || # spacebar & return key(s) (if you want to allow carriage returns)
                (keycode > 64 && keycode < 91)   || # letter keys
                (keycode > 95 && keycode < 112)  || # numpad keys
                (keycode > 185 && keycode < 193) || # ;=,-./` (in order)
                (keycode > 218 && keycode < 223)    # [\]' (in order)

            if valid
                CodeMirror.commands.autocomplete(editor)

    $scope.parseAndDisplay = !->
        p = new nearley.Parser grammar.ParserRules, grammar.ParserStart
        try
            parsed = p.feed $scope.code
            console.assert parsed.results.length == 1, parsed.results
            $scope.parsed = parsed.results[0]

            jar = spawn "java", <[-jar lib/bell.jar -]>

            jar.stdout.once \data, (data) !->
                # console.log(JSON.parse data);
                $scope.output = JSON.parse data
                $scope.data = [{value: JSON.parse data}]
                $scope.$apply!
                jar.kill \SIGINT

            jar.stderr.once \data, (data) !->
                console.log 'Java error: ' + data
                jar.kill \SIGINT

            jar.stdin.setEncoding('utf-8')
            jar.stdin.write <| JSON.stringify(parsed.results[0]) + "\n"
            jar.stdin.end!
        catch err
            console.err 'Parsing error: ' + err


  ..filter "collapse" ->
    lead = -> it.match /^\s*/ .0.length
    (input, indent) ->
      (""+input).split /\n/ \
        .filter (-> lead(it) < indent) \
        .join "\n"
  ..directive "display" (RecursionHelper) ->
    restrict: 'E'
    scope:
      o: '=o'
    template: $ '#display' .html!
    compile: (element) ->
      RecursionHelper.compile(element)
  ..directive "compute" ->
    scope: {}
    transclude: 'element'
    link: (scope, element, attrs,
           ctrl, $transclude) ->
      expr = attrs.let
      mo = expr?.match LET_RE
      if !mo?
        throw Error("invalid let '#expr'")
      lhs = mo[1]
      rhs = mo[2]
      $transclude (clone, scope) ->
        scope.$watch rhs, (v) ->
          scope[lhs] = v
        , true
        $(clone).insertAfter element

  ..filter "isString" -> _.isString

  ..filter "display" ->
    (input) ->
      if _.isString input
        input
      else if input.tape?
        last = 0
        text = input.tape.text
        []
          for [[u,v], mark] in input.tape.markup
            x = text.substring(last,u)
            y = text.substring(u,v)
            cls = ['mark'] ++ (if mark.type? then ['tip'] else [])
            last = v
            if x.length then ..push [x]
            if y.length then ..push [y,cls,mark.type]
          x = text.substring(last)
          if x.length then ..push [x]
        #JSON.stringify input.tape.markup
      else
        [JSON.stringify input]

