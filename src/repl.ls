_ = require \lodash
{execFile} = require \child_process
LET_RE = /^\s*([\s\S]+?)\s+=\s+([\s\S]+?)\s*?\|\s*([\s\S]+?)\s*$/

angular.module 'app', <[ RecursionHelper ui.codemirror ui.select ngBootbox frapontillo.bootstrap-switch indexedDB]>
  ..config ($indexedDBProvider) !->
    $indexedDBProvider
      .connection 'bell.notebook'
      .upgradeDatabase 1, (event, db, tx) ->
        console.log "creating object store"
        db.createObjectStore('cells', {keyPath: 'id'})
  ..controller "Ctrl" ($scope, $timeout, $ngBootbox, $indexedDB) !->
    $scope.verification = true # verify by default

    submitCm = (cell, callback=->) ->
      cm = cell.cm
      cm.removeOverlay(cm.currentOverlay)

      cell.output = null
      cell.error = null
      cell.verifyStatus = null
      cell.loading = true
      thisIdx = _.findIndex($scope.history, (h) ->
          h.id == cell.id
      )

      cellName = "cell-#{cell.id}"
      isTactic = thisIdx > 0

      progress = (output) ->
        $timeout ->
          cell.output = output.fromJar[-1 to]
            cleanse output: ..
      
      success = (output) ->
        $timeout ->
          cell.output = output.fromJar[-1 to]
          cell.fromNearley = output.fromNearley
          cell.scope = output.scope
          cell.routines = output.routines
          
          cleanse cell
          db.update-cells [cell]

          if thisIdx == $scope.history.length - 1
            ui-commands.add-cell-after cell
          if output.isTactic && $scope.verification
            cell.verifyStatus = "In Progress"
            $scope.asyncVerify(cellName, cell)
          else
            cell.verifyStatus = void
          cell.loading = false
          callback(null, cell)

      error = (err) ->
        $timeout ->
          cell.error =
            msg: err.message
            stack: err.stack
            stackshow: false

          if err.line? && err.offset?
            line = err.line - 1
            offset = err.offset
            while (offset >= cm.getLine(line).length)
              offset = offset - cm.getLine(line).length
              line += 1
            cm.currentOverlay = errorOverlay(cm.getLine(line), offset + 1)
            cm.addOverlay(cm.currentOverlay)
          cell.loading = false
          callback(err)

      if isTactic
        # parse as a tactic
        bellmaniaParse do
          isTactic: true,
          text: cell.input,
          term: _.last($scope.history[thisIdx-1].output)?.value?.term
          scope: $scope.history[thisIdx-1].scope
          routines: collectRoutines($scope.history)
          verify: $scope.verification
          , success, error, progress, cellName
      else
          # parse as a term
          bellmaniaParse({isTactic: false, text: cell.input, routines: {}}, success, error, progress, cellName)

      cm.getInputField().blur()
      $scope.mostRecentId = cell.id

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
    
    ui-commands =
      execute: (cell) -> if cell.input then submitCm cell
      add-cell-after: (cell) -> $scope.insert-at cell.id
      delete-cell: (cell) -> $scope.delete-at cell.id - 1
      goto-next: (cell) -> $scope.history[cell.id]?.cm?.focus!
      goto-prev: (cell) -> $scope.history[cell.id - 2]?.cm?.focus!
      
    editor-command = (cmd) -> (cm) -> $scope.$apply -> cmd cm.parent
    
    seq = (...fs) -> -> for f in fs then f ...
    
    $scope.cmOptions = cmOptions()
      [e,u] = [editor-command, ui-commands]
      ..extraKeys =
        'Cmd-Enter':     seq (e u~execute), \
                             (e u~goto-next)
        'Ctrl-Enter':    seq (e u~add-cell-after), \
                             (e u~goto-next)
        'Cmd-Backspace': seq (e u~goto-prev), \
                             (e u~delete-cell)
          
    $scope.cmLoaded = (parent-cell) ->
      (cm) ->
        cm.parent = parent-cell
        parent-cell.cm = cm
        initEditor(cm)

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
      db.clear ->
        db.update-cells!
      
    $scope.insert-at = (idx) ->
      for h in $scope.history[idx to]
        h.id += 1
      $scope.history.splice idx, 0, \
        {id: idx + 1, input: "", output: null, error: null}
        
    $scope.delete-at = (idx) ->
      $scope.history.splice idx, 1
      for h in $scope.history[idx to]
        h.id -= 1

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

    $scope.load = (file) ->
      if file
        reader = new FileReader()
         ..onload = ->
          try
            $scope.$apply ->
              loaded = JSON.parse(reader.result)
              $scope.mostRecentId = loaded.mostRecentId
              $scope.history = loaded.history.map (<<< {error: null, output: null})
              db.clear ->
                db.update-cells!
              $scope.file = void
          catch {message}
            bootbox.alert(message)

        reader.readAsText(file)

    #------------------
    # Persistence Part
    #------------------
    
    db =
      cells: (cb) -> $indexedDB.openStore 'cells' cb
      e: (err) -> console.error "indexedDB error; " + e.stack
      record: (cell) -> {cell.id, cell.input, cell.fromNearley, cell.output, cell.scope, cell.routines, cell.verifyStatus}
      restore-from: ->
        store <~ @cells
        store.getAll!then (cells) ->
          if cells.length
            console.log "read #{cells.length} cells"
            cells.for-each cleanse
            if cells.length <= 3
              $scope.history = cells
            else
              $scope.history = cells[0 to 2]
              for let cell, i in cells[3 to]
                $timeout (-> $scope.history.push cell), i*200
        , @~e
      update-cells: (cells ? $scope.history, cb=->) ->
        records = cells.map @~record
        store <~ @cells
        store.upsert records .then cb, @~e
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
            submitCm h, callback

    $scope.compileAll = ->
      loop-blocks = []
      rec-blocks = {}
      for h in $scope.history
        if h.output?
          for block in h.output
            if block.emit?
              loop-blocks.push \
                {term: block.value.term, scope: h.scope, emit: block.emit}
            else if (r = loop-blocks[*-1])?
              emit = {} <<< r.emit <<< {style: "rec"}
              rec-blocks[r.emit.name] = \
                {term: block.value.term, scope: h.scope, emit}
              
      program-blocks = loop-blocks ++ [v for k,v of rec-blocks].reverse!
      
      fs.writeFileSync '/tmp/emit.json', (program-blocks.map JSON.stringify .join "\n\n")
      
    $scope.toggleStackShow = (err) ->
      err.stackshow = !err.stackshow

    $scope.asyncVerify = (cellName, calc) ->
      fs.readdir '/tmp/' + cellName, (err, files) ->
        calc.processes = {}
        async.each files, (file, callback) ->
          smt = execFile 'cvc4', ["/tmp/#cellName/#file"], (err, stdout, stderr) ->
            if err? then callback(err, stderr)
            else if stdout == 'unsat\n' then callback()
            else callback(stdout, stderr)
          calc.processes[file] = smt
        , (err) ->
          if err?
            if calc.verifyStatus != "Aborted"
              $scope.abortVerification calc # in case some processes are still running
              calc.verifyStatus = "Error"
          else
            calc.verifyStatus = "Success"
          $scope.$apply()

    $scope.abortVerification = (calc) ->
      if (calc.verifyStatus == "In Progress")
        calc.verifyStatus = "Aborted"
        for name, p of calc.processes
          console.log "killing " + p.pid
          p.kill('SIGINT')
    
    collectRoutines = (history) ->
      {}
        for h in history
          for block in h.fromNearley || []
            if block.kind == 'routine'
              ..[block.name] = block

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
  ..directive "rich" ->
    restrict: 'A'
    link: (scope, element, attrs) -> 
      scope.$watch attrs.rich, (value) ->
        if value.hat?
          element.empty!append ($('<hat>').text(value.hat))
        else
          element.text(value)
  ..directive "compute" ($filter) ->
    scope: {}
    transclude: 'element'
    link: (scope, element, attrs,
           ctrl, $transclude) ->
      expr = attrs.let
      mo = expr?.match LET_RE
      if !mo? then throw Error("invalid let '#expr'")
      [lhs, rhs, filt] = mo[1 to]
      x = scope.$parent.$parent
      x.$on 'turn' -> x.o.flag = 1
      $transclude (clone, scope) ->
        scope.$watch rhs, (v) ->
          if filt? then v = $filter(filt)(v)
          scope[lhs] = v
        , true
        $(clone).insertAfter element
        
  # Adapted from fileChange directive, http://stackoverflow.com/a/35748459/37639
  ..directive 'filePick', ->
    restrict: 'A',
    scope: {
      filePick: '&'
    },
    link: (scope, element, attrs) ->
      onChange = ->
        file = element[0].files[0]
        scope.filePick({file})
        if file then element.prop('value', '')  # make event fire again next time

      element.on 'change' onChange

      scope.$on 'destroy' ->
        element.off('change', onChange)

  ..filter "isString" -> _.isString

  ..filter "display" ->
    f = (input, flag) ->
      if _.isString input
        [input]
      else if input.tape?
        last-pos = 0
        [text, annot] = input.tape.text.split '\t'
        reformatText = -> 
          if (mo = /^(.)\u0302$/.exec it)? then {hat: mo.1} else it
        reformatType = -> it?.replace /->/g '→'
        []
          for [[u,v], mark] in (if input.flag then input.tape.markup else [])
            x = text.substring(last-pos, u)
            y = text.substring(u, v)
            cls = ['tape-mark'] ++ (if mark.type? then ['tip'] else [])
            last-pos = v
            if x.length then ..push [reformatText(x)]
            if y.length then ..push [reformatText(y), cls, reformatType(mark.type)]
          x = text.substring(last-pos)
          if x.length then ..push [reformatText(x)]
          if annot?
            ..push [reformatType(annot), ['annotation']]
      else
        [JSON.stringify input]

