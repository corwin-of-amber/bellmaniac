_ = require \lodash
spawn = require \child_process .spawn
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*?\|\s*([\s\S]+?)\s*$/

angular.module 'app', <[ RecursionHelper ui.codemirror ui.select ngBootbox frapontillo.bootstrap-switch indexedDB]>
  ..config ($indexedDBProvider) !->
    console.log "config"
    $indexedDBProvider
      .connection 'bell.notebook'
      .upgradeDatabase 1, (event, db, tx) ->
        console.log "creating object store"
        db.createObjectStore('cells', {keyPath: 'id'})
  ..controller "Ctrl" ($scope, $timeout, $ngBootbox, $indexedDB) !->
    $scope.verification = true # verify by default

    submitCm = (cm, parent, callback=->) ->
      cm.removeOverlay(cm.currentOverlay)

      calc = parent
      calc.output = null
      calc.error = null
      calc.verifyStatus = null
      calc.loading = true
      thisIdx = _.findIndex($scope.history, (h) ->
          h.id == calc.id
      )
      thisId = thisIdx + 1 # "id" of In[] and Out[] start from 1

      cellName = "cell-#{thisId}"
      isTactic = thisIdx > 0

      success = (output) ->
        $timeout ->
          calc.output = output.fromJar
          calc.fromNearley = output.fromNearley
          calc.scope = output.scope
          calc.routines = output.routines
          
          cleanse calc
          db.update-cells [calc]

          if (thisId == ($scope.history.length))
            $scope.history.push({id: thisId + 1, input: "", output: null, error: null})
          calc.loading = false
          if output.isTactic && $scope.verification
            calc.verifyStatus = "In Progress"
            $scope.asyncVerify(cellName, calc)
          else
            calc.verifyStatus = void
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
        bellmaniaParse do
          isTactic: true,
          text: calc.input,
          term: _.last($scope.history[thisIdx-1].output).value.term
          scope: $scope.history[thisIdx-1].scope
          routines: $scope.history[thisIdx-1].routines || {}
          verify: $scope.verification
          , success, error, cellName
      else
          # parse as a term
          bellmaniaParse({isTactic: false, text: calc.input, routines: {}}, success, error, cellName)

      cm.getInputField().blur()
      $scope.mostRecentId = thisId
      $scope.$apply()

    if localStorage['bell.presentMode']
      if JSON.parse(that)
        $ \body .addClass 'presentMode'

    $scope.togglePresent = !->
      $ \body .toggleClass 'presentMode'
      localStorage['bell.presentMode'] = JSON.stringify ($ \body .hasClass 'presentMode')

    $scope.bind = (cell) ->
      onChange = (oldValue, newValue) ->
        if oldValue !== newValue then db.update-cells [cell]

      #$scope.$watch (-> cell.input), onChange
      $scope.$watch (-> cell.verifyStatus), onChange
      
    $scope.cmOptions = cmOptions()
    $scope.wrapper = (parent-cell) ->
      submitCallback = (cm) ->
        if parent-cell.input then submitCm(cm, parent-cell)

      loadCallback = (cm) ->
        cm.parent = parent-cell
        parent-cell.cm = cm

      initEditor(submitCallback, loadCallback)

    $scope.history = [
      {id: 1, input: "", output: null, error: null}
    ]
    $scope.mostRecentId = 1
    $scope.isOutdated = (h) ->
        h.output? && $scope.mostRecentId < h.id
    $scope.output = {}
    $scope.data = []

    $scope.reset = ->
      $scope.history = [
        {id: 1, input: "", output: null, error: null}
      ]

    marshal = ->
      JSON.stringify do
        mostRecentId: $scope.mostRecentId,
        history: $scope.history.map (h) ->
          {id: h.id, input: h.input}

    $scope.save = ->
      saveText = marshal!
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
            $scope.$apply ->
              loaded = JSON.parse(reader.result)
              $scope.mostRecentId = loaded.mostRecentId
              $scope.history = loaded.history.map (<<< {error: null, output: null})
              db.update-cells!
            $timeout ->
              async.eachSeries _.take($scope.history, $scope.mostRecentId), (h, callback) ->
                if h.input
                  submitCm h.cm, h, callback
          catch {message}
            bootbox.alert(message)

        reader.readAsText($scope.file)

    #------------------
    # Persistence Part
    #------------------
    
    db =
      cells: (cb) -> $indexedDB.openStore 'cells' cb
      e: (err) -> console.error "indexedDB error; " + e.stack
      record: (cell) -> {cell.id, cell.input, cell.output, cell.scope, cell.routines, cell.verifyStatus}
      restore-from: ->
        store <~ @cells
        store.getAll!then (cells) ->
          if cells.length
            console.log "read #{cells.length} cells"
            cells.for-each cleanse
            $scope.history = cells[0 to 2]
            for let cell, i in cells[3 to]
              $timeout (-> $scope.history.push cell), i*200
        , @~e
      update-cells: (cells ? $scope.history, cb=->) ->
        records = cells.map @~record
        store <~ @cells
        store.upsert records .then ->
          console.log "updated [#{cells.map (.id)}]" ; cb!
        , @~e
      clear: (cb=->) ->
        @cells (.clear!then -> console.log "cleared" ; cb!)
          
    db.restore-from!    

    window.db = db
        
    cleanse = (cell) ->
      #console.log cell
      if cell.output?
        for subcell in cell.output
          cleanse subcell.value
      if cell.display?
        cleanse cell.display
      if cell.vbox?
        cell.vbox.for-each cleanse
      if cell.tree?
        cleanse cell.tree
      if cell.$ == 'Tree'
        cleanse cell.root
        cell.subtrees.for-each cleanse
      if cell.tape?
        for [_, mark] in cell.tape.markup
          mark.term = void
  
    #----------------
    # Execution Part
    #----------------
    
    $scope.runAll = ->
      $timeout ->
        async.eachSeries $scope.history, (h, callback) ->
          if h.input
            submitCm h.cm, h, callback

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
            $scope.abortVerification calc # in case some processes are still running
            calc.verifyStatus = "Error"
          else
            calc.verifyStatus = "Success"
          $scope.$apply()

    $scope.abortVerification = (calc) ->
      if (calc.verifyStatus == "In Progress")
        for name, p of calc.processes
          console.log "killing " + p.pid
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
  ..directive "compute" ($filter) ->
    scope: {}
    transclude: 'element'
    link: (scope, element, attrs,
           ctrl, $transclude) ->
      expr = attrs.let
      mo = expr?.match LET_RE
      if !mo? then throw Error("invalid let '#expr'")
      [lhs, rhs, filt] = mo[1 to]
      $transclude (clone, scope) ->
        scope.$watch rhs, (v) ->
          if filt? then v = $filter(filt)(v)
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
        #console.log "display tape"
        last = 0
        [text, annot] = input.tape.text.split '\t'
        reformatType = -> it?.split('->')?.join('→')
        []
          for [[u,v], mark] in input.tape.markup
            x = text.substring(last,u)
            y = text.substring(u,v)
            #mark.term = void    # bahh. Angular scalability issue.
            if mark.term?
              console.log mark
            cls = ['mark'] ++ (if mark.type? then ['tip'] else [])
            last = v
            if x.length then ..push [x]
            if y.length then ..push [y,cls,reformatType(mark.type)]
          x = text.substring(last)
          if x.length then ..push [x]
          if annot?
            ..push [reformatType(annot), ['annotation']]
      else
        [JSON.stringify input]

