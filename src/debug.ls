_ = require \lodash
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*$/

angular.module 'app', [\RecursionHelper, \ui.codemirror]
  ..controller "Ctrl" ($scope, $timeout) !->

    initState = ->
        $scope.parsed = []
        $scope.output = []
        $scope.errorMsg = ""
        if ($scope.cm)
          $scope.cm.removeOverlay($scope.cm.currentOverlay)

    $scope.code = localStorage.getItem('codeMirrorContents') || "a b"
    initState()

    $scope.cmOptions = cmOptions()
    $scope.loaded = initEditor((cm) -> , (cm) ->
      $scope.cm = cm)

    $scope.parseAndDisplay = !->

        initState()

        success = (output) ->
            $timeout(->
                $scope.parsed = output.fromNearley
                $scope.output = output.fromJar
            )

        error = (err, output) ->
            $timeout(->
                $scope.errorMsg = err.message
                $scope.cm.currentOverlay = errorOverlay($scope.cm.getLine(err.line - 1), err.offset + 1)
                $scope.cm.addOverlay($scope.cm.currentOverlay)
            )

        bellmaniaParse({isTactic: false, text: $scope.code}, success, error)

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

