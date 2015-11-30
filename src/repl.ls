_ = require \lodash
spawn = require \child_process .spawn
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*$/

angular.module 'app', [\RecursionHelper, \ui.codemirror, \ui.select, \ngBootbox, \frapontillo.bootstrap-switch]
  ..controller "Ctrl" ($scope, $timeout, $ngBootbox) !->
    $scope.verification = true # verify by default

    submitCm = (cm, parent, callback=->) ->
        cm.removeOverlay(cm.currentOverlay)

        calc = cm.parent
        calc.output = null
        calc.error = null
        calc.loading = true
        thisIdx = _.findIndex($scope.history, (h) ->
            h.id == calc.id
        )
        thisId = thisIdx + 1 # "id" of In[] and Out[] start from 1

        cellName = "cell#{thisIdx + 1}"
        isTactic = thisIdx > 0

        success = (output) ->
            $timeout ->
                calc.output = output.fromJar
                calc.fromNearley = output.fromNearley
                calc.scope = output.scope

                if (thisId == ($scope.history.length))
                    $scope.history.push({id: thisId + 1, input: "", output: null, error: null})
                calc.loading = false
                if isTactic && $scope.verification
                    calc.verifyStatus = "In Progress"
                    $scope.asyncVerify(cellName, calc)
                callback(null, calc)

        error = (err) ->
            $timeout ->
                calc.error =
                  msg: err.message
                  stack: err.stack
                  stackshow: false

                if err.line? && err.offset?
                  line = err.line - 1
                  offset = err.offset + 1
                  while (offset >= cm.getLine(line).length)
                    offset = offset - cm.getLine(line).length - 1
                    line += 1
                  cm.currentOverlay = errorOverlay(cm.getLine(line), offset)
                  cm.addOverlay(cm.currentOverlay)
                calc.loading = false
                callback(err)

        if isTactic
            # parse as a tactic
            bellmaniaParse({
                isTactic: true,
                text: calc.input,
                termJson: _.last($scope.history[thisIdx-1].output).value.term
                scope: $scope.history[thisIdx-1].scope
                },
                success, error, cellName)
        else
            # parse as a term
            bellmaniaParse({isTactic: false, text: calc.input}, success, error)

        cm.getInputField().blur()
        $scope.mostRecentId = thisId
        $scope.$apply()


    $scope.cmOptions = cmOptions()
    $scope.wrapper = (parent) ->
        submitCallback = (cm) ->
            submitCm(cm, parent)

        loadCallback = (cm) ->
            cm.parent = parent
            parent.cm = cm

        initEditor(submitCallback, loadCallback)

    $scope.history = [
        {id: 1, input: "a b", output: null, error: null}
    ]
    $scope.mostRecentId = 1
    $scope.isInvalid = (h) ->
        return ($scope.mostRecentId < h.id && h.output != null)
    $scope.output = {}
    $scope.data = []

    $scope.reset = ->
      $scope.history = [
          {id: 1, input: "", output: null, error: null}
      ]

    $scope.save = ->
      saveText = JSON.stringify({
        mostRecentId: $scope.mostRecentId,
        history: _.map($scope.history, (h) ->
          {id: h.id, input: h.input}
        )
      })
      bb = new Blob([saveText], {type: "application/json"})
      blobURL = (window.URL || window.webkitURL).createObjectURL(bb);
      anchor = document.createElement("a");
      anchor.download = 'newfile.json'
      anchor.href = blobURL
      anchor.click()

    $scope.load = ->
      if ($scope.file)
        reader = new FileReader();
        reader.onload = ->
          try
            $scope.$apply( ->
              loaded = JSON.parse(reader.result)
              $scope.mostRecentId = loaded.mostRecentId
              $scope.history = _.map(loaded.history, (h) ->
                h.error = null
                h.output = null
                h
              )
            )
            $timeout ->
              async.eachSeries _.take($scope.history, $scope.mostRecentId), (h, callback) ->
                submitCm h.cm, h, callback
          catch {message}
            bootbox.alert(message)

        reader.readAsText($scope.file)

    $scope.toggleStackShow = (err) ->
        err.stackshow = !err.stackshow

    $scope.asyncVerify = (cellName, calc) ->
        fs.readdir '/tmp/' + cellName, (err, files) ->
            calc.processes = {}
            async.each files, (file, callback) ->
                z3 = spawn('z3', ['/tmp/' + cellName + '/' + file])
                calc.processes[file] = z3
                z3.stdout.on 'data', (data) ->
                    result = data.toString('utf8')
                    if (result == 'unsat\n')
                        callback()
                    else if (result == 'sat\n')
                        callback(result)
                z3.stderr.on 'data', (data) ->
                    result = data.toString('utf8')
                    callback(result)
            , (err) ->
                if (err != null)
                    calc.verifyStatus = "Error"
                else
                    calc.verifyStatus = "Success"
                $scope.$apply()

    $scope.abortVerification = (calc) ->
        if (calc.verifyStatus == "In Progress")
            _.each calc.processes, (p) ->
                p.kill('SIGINT')
            calc.verifyStatus = "Aborted"

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
  ..directive 'fileChange', ->
    restrict: 'A',
    require: 'ngModel',
    scope: {
      fileChange: '&'
    },
    link: (scope, element, attrs, ctrl) ->
      onChange = ->
        ctrl.$setViewValue(element[0].files[0])
        scope.fileChange()

      element.on('change', onChange);

      scope.$on('destroy', ->
        element.off('change', onChange)
      )

  ..filter "isString" -> _.isString

  ..filter "display" ->
    f = (input) ->
      if _.isString input
        [input]
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
      else
        [JSON.stringify input]

