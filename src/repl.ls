fs = require \fs
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

    set-mode = (mode) ->
      if mode == 'loading'
        $('.toolbar .btn').addClass 'disabled'
        $('div.flash').text 'Loading'
      else
        $('#new,#save,#load,#rewind').removeClass 'disabled'
        $('div.flash').empty!
      if mode == 'ready'
        $('#run').removeClass 'disabled'
        $('#stop').addClass 'disabled'
        $('#compile').removeClass 'disabled'
      else if mode == 'running'
        $('#run').addClass 'disabled'
        $('#stop').removeClass 'disabled'
        $('#compile').addClass 'disabled'
      else if mode == 'compiling'
        $('#run').addClass 'disabled'
        $('#stop').removeClass 'disabled'
        $('#compile').addClass 'disabled'        

    set-mode 'ready'
        
    checkpoint = (callback) ->
      if checkpoint.stop
        err = new Error "Aborted."
        if callback then callback err 
        throw err
      
    submitCm = (cell, callback=->) ->
      cm = cell.cm
      cm.removeOverlay(cm.currentOverlay)

      if !(cell.input.trim!)
        callback! ; return    # empty input - why bother
      
      set-mode 'running'

      cell.output = null
      cell.error = null
      cell.verifyStatus = null
      cell.loading = true
      thisIdx = _.findIndex($scope.history, (h) ->
          h.id == cell.id
      )

      cellName = "cell-#{cell.id}"

      cp-callback = (err) ->
        if err? then $scope.$apply ->
          cell.error = {msg: err.message}
          cell.loading = false
      
      progress = (output) ->
        checkpoint callback
        $timeout ->
          cell.output = output.fromJar[-1 to]
            cleanse output: ..
      
      success = (output) ->
        set-mode 'ready'
        checkpoint cp-callback
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
        set-mode 'ready'
        checkpoint cp-callback
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

      # Grab values from previous cell
      lastScope = void
      idx = thisIdx
      while !lastScope? && idx > 0
        idx = idx - 1
        lastScope = $scope.history[idx].scope
      
      if thisIdx > 0
        lastTerm = _.last($scope.history[thisIdx-1].output)?.value?.term
      else
        lastTerm = void
        
      # Parse, serialize term, and send to engine
      bellmaniaParse do
        text: cell.input,
        term: lastTerm
        scope: lastScope
        routines: collectRoutines($scope.history)
        verify: $scope.verification
        , success, error, progress, cellName

    if localStorage['bell.presentMode']
      if JSON.parse(that)
        $ \body .addClass 'presentMode'

    $scope.togglePresent = !->
      $ \body .toggleClass 'presentMode'
      $scope.history.forEach (.cm.refresh!)  # CodeMirror needs to adapt to font change
      localStorage['bell.presentMode'] = JSON.stringify ($ \body .hasClass 'presentMode')

    $scope.bind = (cell) ->
      $scope.$watch (-> cell.verifyStatus), (oldValue, newValue) ->
        if oldValue !== newValue then db.update-cells [cell]
    
    ui-commands =
      execute: (cell) -> if cell.input then checkpoint.stop = false; submitCm cell
      add-cell-after: (cell) -> $scope.insert-at cell.id
      delete-cell: (cell) -> $scope.delete-at cell.id - 1
      goto-next: (cell) -> $scope.history[cell.id]?.cm?.focus!
      goto-prev: (cell) -> $scope.history[cell.id - 2]?.cm?.focus!
      
    editor-command = (cmd) -> (cm) -> $scope.$apply -> cmd cm.parent
    
    seq = (...fs) -> -> for f in fs then f ...
    
    $scope.cmOptions = cmOptions()
      [e,u] = [editor-command, ui-commands]
      [Cmd-Enter, Ctrl-Enter, Cmd-Backspace] =
        if process.platform == 'darwin' then <[ Cmd-Enter Ctrl-Enter Cmd-Backspace ]>
        else                                 <[ Ctrl-Enter Alt-Enter Ctrl-Backspace ]>
      ..extraKeys =
        (Cmd-Enter):     seq (e u~execute), \
                             (e u~goto-next)
        (Ctrl-Enter):    seq (e u~add-cell-after), \
                             (e u~goto-next)
        (Cmd-Backspace): seq (e u~goto-prev), \
                             (e u~delete-cell)

    if process.platform != 'darwin'
      $('span.keystroke').html('<kbd>Ctrl</kbd>+<kbd>↵</kbd>')
          
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

    currentFilename = localStorage['bell.filename']
      
    $scope.reset = ->
      $scope.history = [
        {id: 1, input: "", output: null, error: null}
      ]
      currentFilename := void ; delete localStorage['bell.filename']
      db.clear ->
        db.update-cells!
      
    $scope.insert-at = (idx) ->
      for h in $scope.history[idx to]
        h.id += 1
      $scope.history.splice idx, 0, \
        {id: idx + 1, input: "", output: null, error: null}
      db.update-cells $scope.history[idx to]
        
    $scope.delete-at = (idx) ->
      $scope.history.splice idx, 1
      for h in $scope.history[idx to]
        h.id -= 1
      db.clear ->  # TODO can be more efficient
        db.update-cells!

    $scope.toggleStackShow = (err) ->
      err.stackshow = !err.stackshow

    $scope.save = ->
      saveText = marshal!
      bb = new Blob([saveText], {type: "application/json"})
      blobURL = (window.URL || window.webkitURL).createObjectURL(bb);
      anchor = document.createElement("a");
      anchor.download = currentFilename || 'newfile.json'
      anchor.href = blobURL
      anchor.click()
      # TODO how to update currentFilename when the user selects a file?

    $scope.load = (file) ->
      if file
        currentFilename := localStorage["bell.filename"] = file.name
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

    marshal = ->
      JSON.stringify do
        mostRecentId: $scope.mostRecentId,
        history: $scope.history.map (h) ->
          {id: h.id, input: h.input}

    #------------------
    # Persistence Part
    #------------------
    
    db =
      cells: (cb) -> $indexedDB.openStore 'cells' cb
      e: (err) -> console.error "indexedDB error; " + e.stack
      record: (cell) -> {cell.id, cell.input, cell.fromNearley, cell.output, cell.scope, cell.routines, cell.verifyStatus}
      restore-from: ->
        set-mode 'loading'
        store <~ @cells
        store.getAll!then (cells) ->
          if cells.length
            console.log "read #{cells.length} cells"
            cells.for-each cleanse
            # Start with 3 cells then add the others gradually;
            # Hopefully this makes the ui a bit more responsive
            $scope.history = _.compact cells[0 to 2]
            async.eachSeries cells[3 to], (cell, callback) ->
              $timeout ->
                $scope.history.push cell
                callback!
              , 200
            , -> set-mode 'ready'
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

    is-complete = (cell) ->
      cell.output && !cell.error

    is-satisfied = (cell) ->
      cell.deps.every is-complete

    $scope.runAll = !->
      db.update-cells!
      # start from the first cell that was not run
      script = _.dropWhile $scope.history, is-complete
        ..forEach parse-deps
      checkpoint.stop = false
      async.whilst (-> script.length), (callback) ->
        h = extract-first script, is-satisfied
        h.cm.getInputField!focus!  # note: cm.focus! would also grab window focus
        submitCm h, callback

    $scope.stop = ->
      checkpoint.stop = true
      bellmaniaParse.abort!
            
    $scope.rewind = ->
      $scope.stop!
      for h in $scope.history
        delete h.fromNearley
        delete h.output
      db.update-cells!

    # cells with text "depends on ##,##,##" have explicit dependencies
    # "depends on" can be abbreviated as "dep", "dep.", "deps", or "deps."
    parse-deps = (cell) !->
      if cell.input? && (mo = /\bdep(?:s?[.]?|ends on)\s*([0-9,\s]+)/.exec cell.input)?
        dep-ids = mo[1].split /[,\s]+/ .map (-> +it)
        cell.deps = [.. for $scope.history when ..id in dep-ids]
      else
        cell.deps = []

    # Like _.find, but removes the element that was found from the array
    extract-first = (array, predicate, fromIndex) ->
      idx = _.findIndex(array, predicate)
      if idx >= 0
        array[idx]
          array.splice idx, 1; ..

    collectRoutines = (history) ->
      {}
        for h in history
          for block in h.fromNearley || []
            if block.kind == 'routine'
              ..[block.name] = block

    #-------------------
    # Verification Part
    #-------------------

    $scope.asyncVerify = (cellName, calc) ->
      # Solver selection heuristic;  @@@ MUCH HACK
      solver = if calc.input is /SynthAuto/ then 'z3' else 'cvc4'
      
      fs.readdir "/tmp/#cellName", (err, files) ->
        calc.processes = {}
        calc.verifyStart = new Date
        async.each files, (file, callback) ->
          smt = execFile solver, ["/tmp/#cellName/#file"], (err, stdout, stderr) ->
            if err? then callback(err, stderr)
            else if stdout == 'unsat\n' then callback()
            else callback(stdout, stderr)
          calc.processes[file] = smt
        , (err) -> $scope.$apply ->
          calc.verifyEnd = new Date
          if err?
            if calc.verifyStatus != "Aborted"
              $scope.abortVerification calc # in case some processes are still running
              calc.verifyStatus = "Error"
          else
            calc.verifyStatus = "Success"

    $scope.abortVerification = (calc) ->
      if (calc.verifyStatus == "In Progress")
        calc.verifyStatus = "Aborted"
        for name, p of calc.processes
          console.log "killing " + p.pid
          p.kill('SIGTERM')
    
    $scope.verifyTitle = (cell) ->
      if cell.verifyStatus == 'Success' 
        if (duration = cell.verifyEnd - cell.verifyStart)
          "Verified (#{Math.round(duration/100) / 10}s)."
        else "Verified."
      else if cell.verifyStatus == 'Error' then "Verification failed."
    
    #------------------
    # Compilation Part
    #------------------

    $scope.compileAll = ->
      set-mode 'compiling'
      
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

      outf = (currentFilename ? "output.json").replace(/\.[a-z]+$/, '.cpp').toLowerCase!

      loop-blocks ++ [v for k,v of rec-blocks].reverse!
        bellmania-codegen .., outf, -> set-mode 'ready'
      
    window.$scope = $scope

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
      y = x
      while y && !y.o?.progress
        y = y.$parent
      if !y  # - for efficiency, skip this for in-progress cells
        x.$on 'turn' -> x.o.flag = 1
      $transclude (clone, scope) ->
        scope.$watch "(#{rhs}).flag" ->
          v = scope.$eval rhs
          if filt? then v = $filter(filt)(v)
          scope[lhs] = v
        #scope.$watch rhs, (v) ->
        #  if filt? then v = $filter(filt)(v)
        #  scope[lhs] = v
        #, true
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


# Sticky toolbar polyfill
$ ->
  menu = document.querySelector('.toolbar');
  menuPosition = menu.getBoundingClientRect();
  placeholder = document.createElement('div');
  placeholder.style.width = menuPosition.width + 'px';
  placeholder.style.height = menuPosition.height + 'px';
  placeholder.classList.add('toolbar-placeholder');
  isAdded = false;

  window.addEventListener 'scroll', ->
      if (window.pageYOffset >= menuPosition.top && !isAdded)
          menu.classList.add('sticky');
          menu.parentNode.insertBefore(placeholder, menu);
          isAdded := true;
      else if (window.pageYOffset < menuPosition.top && isAdded)
          menu.classList.remove('sticky');
          menu.parentNode.removeChild(placeholder);
          isAdded := false;
