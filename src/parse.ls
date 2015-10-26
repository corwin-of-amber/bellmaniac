spawn = require \child_process .spawn
_ = require \lodash
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*$/
assert = require \assert

angular.module 'app', [\RecursionHelper, \ui.codemirror]
  ..controller "Ctrl" ($scope) !->

    $scope.code = localStorage.getItem('codeMirrorContents') || "a b"
    $scope.parsed = {}
    $scope.output = {}
    $scope.data = []

    $scope.editor = initEditor((cm)->)

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

