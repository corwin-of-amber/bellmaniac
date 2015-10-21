spawn = require \child_process .spawn
_ = require \lodash
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*$/
assert = require \assert

angular.module 'app', [\RecursionHelper, \ui.codemirror]
  ..controller "Ctrl" ($scope) !->

    $scope.code = localStorage.getItem('codeMirrorContents') || "a b"
    $scope.editorOptions =
        mode:  "scheme",
        matchBrackets:
          bracketRegex: /[(){}[\]⟨⟩]/
          bracketMatching: {"(": ")>", ")": "(<", "[": "]>", "]": "[<", "{": "}>", "}": "{<", "⟨": "⟩>", "⟩": "⟨<"}
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
        * text: "×", displayText: "\\*"

    # subscript digits
    for i in [0 to 9]
        charCode = 0x2080 + i
        autoWords.push do
            text: String.fromCharCode(charCode),
            displayText: "_#i"
        
    # boxed letters
    for letter in ['A' to 'Z']
        charCode = 0xdd30 + letter.charCodeAt(0) - 0x41
        autoWords.push do
            text: "\ud83c" + String.fromCharCode(charCode)
            displayText: "[#letter]"
        autoWords.push do
            text: "\ud83c" + String.fromCharCode(charCode) + "\u0332" # underbar
            displayText: "[#{letter}_]"

    findCurWord = (editor, delimiters) ->
        whitespace = /\s/
        cur = editor.getCursor()
        curLine = editor.getLine(cur.line)

        [start, end] = [cur.ch - 1, cur.ch]
        while (start >= 0 && !delimiters.test(curLine.charAt(start)) && !whitespace.test(curLine.charAt(start-1)))
            start -= 1
        curWord = if start != end then curLine.slice(start, end) else ""
        word: curWord,
        start: start,
        end: end

    findSuffixWord = (editor, words) ->
        cur = editor.getCursor()
        curLine = editor.getLine(cur.line)

        matches = []
        [start, end, i] = [cur.ch - 1, cur.ch, 1]
        while start >= 0 && words.length > 0
            c = curLine.charAt(start)
            words = words.filter (.displayText[*-i] == c)
            matches ++= words.filter (.displayText.length == i) .map ->
              word: it
              start: start
              end: end
            start -= 1
            i += 1

        matches

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
        cur = editor.getCursor()

        filteredWords = findSuffixWord(editor, autoWords)
        
        if filteredWords.length > 0
            curPos = filteredWords[0]
            editor.replaceRange(curPos.word.text,
              CodeMirror.Pos(cur.line, curPos.start),
              CodeMirror.Pos(cur.line, curPos.end))

    $scope.codemirrorLoaded = (editor) ->

        CodeMirror.registerHelper "hint", "anyword", hintReplace

        CodeMirror.commands.autocomplete = (cm) ->
            cm.showHint hint: CodeMirror.hint.anyword, completeSingle: false

        editor.on 'change', (editor, changeObj) !->
            localStorage.setItem('codeMirrorContents', editor.getValue())
            text = changeObj.text[0]  # pretty hackey
            valid = text? && text.length == 1 && (
                (text >= "a" && text <= "z") ||
                (text >= "A" && text <= "Z") ||
                (text >= "0" && text <= "9") ||
                (text in <[ ; = , - . / ` [ \ ] ' < > * ]>)
                )

            if valid
                autoReplace(editor)
                CodeMirror.commands.autocomplete(editor)

    $scope.splitTextToBlocks = (input) ->
        input.split /\n+(?!\s)/ .filter (== /\S/)

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
                for block in buffer.join("").split(/\n\n+(?=\S)/)
                    try
                        output = JSON.parse block
                        $scope.output.push output
                        $scope.data.push {value: output}
                    catch err
                        console.error err.stack
                        $scope.data.push {error: err.toString!}
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
            ).map((block) ->
                # wrap each expression in another layer that includes scope
                check: block
                # scope: window.scope
            ).value!

            toStream = (stream) ->
              for parsedBlock in $scope.parsed
                  stream.write <| JSON.stringify(parsedBlock)
                  stream.write "\n\n"
              stream.end!
            
            fs.writeFileSync "/tmp/synopsis.txt" $scope.code

            stream = fs.createWriteStream "/tmp/synopsis.json"
            stream.once \open -> toStream stream

            jar.stdin.setEncoding('utf-8')
            toStream jar.stdin
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

