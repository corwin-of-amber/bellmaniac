spawn = require \child_process .spawn
_ = require \lodash
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*$/
assert = require \assert

angular.module 'app', [\RecursionHelper, \ui.codemirror]
  ..controller "Ctrl" ($scope) !->

    $scope.code = localStorage.getItem('codeMirrorContents') || "a b"
    $scope.editorOptions =
        mode:  "scheme",
        theme: "material"
    $scope.parsed = {}
    $scope.output = {}
    $scope.data = []

    # hinting and autoreplace functionality
    hintWords =
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
        * text: "×", displayText: "\\times"
        * text: "∩", displayText: "\\cap"

    autoWords =
        * text: "↦", displayText: "|->"
        * text: "\u27E8", displayText: "\\<"
        * text: "\u27E9", displayText: "\\>"

    for i in [0 to 9]
        charCode = "208" + i
        autoWords.push {
            text: String.fromCharCode(parseInt(charCode, 16)),
            displayText: "_" + i
        }

    findCurWord = (editor, delimiters) ->
        whitespace = /\s/
        cur = editor.getCursor()
        curLine = editor.getLine(cur.line)

        start = cur.ch; end = start
        while (start >= 1 && !delimiters.test(curLine.charAt(start)) && !whitespace.test(curLine.charAt(start-1)))
            start -= 1
        curWord = if start != end then curLine.slice(start, end) else ""
        word: curWord,
        start: start,
        end: end

    hintReplace = (editor) ->
        curPos = findCurWord(editor, /\\/)
        curWord = curPos.word
        cur = editor.getCursor()

        filteredWords = hintWords.filter (w) ->
            curWord.length > 0 && w.displayText.indexOf(curWord) == 0

        list: filteredWords,
        from: CodeMirror.Pos(cur.line, curPos.start),
        to: CodeMirror.Pos(cur.line, curPos.end)

    autoReplace = (editor) ->
        curPos = findCurWord(editor, /[_|\\]/)
        curWord = curPos.word
        cur = editor.getCursor()

        filteredWords = autoWords.filter (w) ->
            curWord == w.displayText

        if filteredWords.length > 0
            editor.replaceRange(filteredWords[0].text,
                CodeMirror.Pos(cur.line, curPos.start),
                CodeMirror.Pos(cur.line, curPos.end))

    $scope.codemirrorLoaded = (editor) ->

        CodeMirror.registerHelper "hint", "anyword", hintReplace

        CodeMirror.commands.autocomplete = (cm) ->
            cm.showHint hint: CodeMirror.hint.anyword, completeSingle: false

        editor.on 'keyup', (editor, e) !->
            localStorage.setItem('codeMirrorContents', editor.getValue())
            keycode = e.keyCode
            valid =
                (keycode > 47 && keycode < 58)   || # number keys
                (keycode == 32 || keycode == 13)   || # spacebar & return key(s) (if you want to allow carriage returns)
                (keycode > 64 && keycode < 91)   || # letter keys
                (keycode > 95 && keycode < 112)  || # numpad keys
                (keycode > 185 && keycode < 193) || # ;=,-./` (in order)
                (keycode > 218 && keycode < 223)    # [\]' (in order)

            if valid
                autoReplace(editor)
                CodeMirror.commands.autocomplete(editor)

    $scope.splitTextToBlocks = (input) ->
        lines = input.split "\n"
        blocks = []
        for i in lines
            if i.length > 0
                console.log i
                if i[0] == "\t" && blocks.length > 0
                    blocks[blocks.length - 1] = blocks[blocks.length - 1].concat(" " + i.slice(1))
                else
                    blocks.push(i)
        console.log blocks
        blocks

    $scope.parseAndDisplay = !->
        $scope.parsed = []
        $scope.output = []
        $scope.data = []

        blocks = $scope.splitTextToBlocks($scope.code)
        try
            buffer = []
            jar = spawn "java", <[-jar lib/bell.jar -]>
            jar.stdout.setEncoding('utf-8')
            jar.stdout.on \data, (data) !->
                buffer.push(data)

            jar.stdout.on \end, !->
                outputFromJar = []
                ctr = 0
                for i in [1 to buffer.length]
                    try
                        output = JSON.parse buffer.slice(ctr, i).join("")
                        $scope.output.push output
                        $scope.data.push {value: output}
                        ctr = i
                    catch err
                $scope.$apply!

            jar.stderr.on \data, (data) !->
                console.error 'Java error: ' + data

            # reset global list of sets to empty
            window.scope = []
            $scope.parsed = _.chain(blocks)
            .map((block) ->
                # parse block with nearley, filter only non-false results, assert parse unambiguous
                p = new nearley.Parser grammar.ParserRules, grammar.ParserStart
                parsed = p.feed block
                console.debug parsed.results
                results = _.filter parsed.results, (r) -> r
                assert results.length == 1, JSON.stringify(results) + " is not a unique parse."
                results[0]
            ).filter((block) ->
                # only take the expressions that aren't set declarations
                # set declarations are implicitly pushed to window.scope
                block.root.kind != \set
            # ).map((block) ->
            #     # wrap each expression in another layer that includes scope
            #     check: block,
            #     scope: window.scope
            ).value!

            jar.stdin.setEncoding('utf-8')
            for parsedBlock in $scope.parsed
                jar.stdin.write <| JSON.stringify(parsedBlock)
                jar.stdin.write "\n\n"
            jar.stdin.end!
        catch err
            console.error err
            $scope.parsed = err

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

