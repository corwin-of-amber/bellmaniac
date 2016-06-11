
fs = require 'fs-extra'
spawn = require \child_process .spawn
assert = require \assert
_ = require \lodash

root = exports ? this

readResponseBlocks = (stream, parsedInputs, success, error, progress) ->
  stream.setEncoding('utf-8')
  blocks = []
  buffer = ""
  err-occurred = void
  stream.on \data, (data) !-> 
    # NAIVE
    buffer := buffer + data
    chunks = buffer.split(/\n\n+/)
    while chunks.length > 1
      process chunks.shift!
    buffer := chunks[0]
    if 0
      chunks = (buffer.join("") + data).split(/\n\n+/)
      buffer.splice(0, buffer.length, chunks[0])
      for chunk in chunks[1 to]
        process(buffer.join(""))
        buffer.splice(0, buffer.length, chunk)
    
  stream.on \end, !-> if !err-occurred then success(blocks)

  process = (block) ->
    if (block = block.trim!)
        inputBlock = parsedInputs[blocks.length]  # TODO subtract number of progress blocks
        try
            outputBlock = JSON.parse(block)
            if (outputBlock.error)
                throw outputBlock
            blocks.push {value: outputBlock, emit: emitData inputBlock}
            progress(blocks)
        catch err
            # add line number from input before re-throwing
            # so that correct line can be highlighted
            # TODO this was broken by the progress feature :(
            inputBlock
              err.line = (..?check ? ..?tactic)?.line
            console.error err.stack
            console.log block
            err-occurred := err
            error(err)

wrapWith = (term, root) ->
    if (term.root.literal != root.literal)
        tree(root, [term])
    else
        term
        
encapsName = (routine-def) ->
  fmt-param = ->
    console.assert it.$ == 'Tree' && it.subtrees.length == 0 && it.root.$ == 'Identifier'
    it.root.literal
  params = routine-def.params.map fmt-param .join ','
  "#{routine-def.name}[#{params}]"

emitData = (block) ->   # @param block   Parsed input block
  if block?.kind == 'routine'
    {name: encapsName(block), style: "loop"}
  
# input is of the form
#     {isTactic: bool,
#      text: string from codemirror
#      term:? previous term (AST) if isTactic is true
#      scope:? previous scope if isTactic is true
#     }
root.bellmaniaParse = (input, success, error, progress, name='synopsis') ->

    parser = new Parser
  
    blocks = parser.splitTextToBlocks(parser.stripComments(input.text))

    try
        output =
            fromNearley: []
            fromJar: []

        # spawn jar and initialize jar behavior
        launch = if root.devmode then <[../Bellmaniac/bell ui.CLI]> else <[java -jar lib/bell.jar]>
        tmpdir = "/tmp/#name/"
          fs.removeSync ..
        flags =
            if input.dryRun then <[--dry-run]>
            else if input.verify then <[--cert all --prover null --tmpdir]> ++ [tmpdir]
            else <[--cert none]>
        env = {} <<< process.env <<< configure-env!
        jar = spawn launch[0], launch[1 to] ++ flags ++ <[-]>, {env}

        fromStream = (stream, callback) ->
            stream.setEncoding('utf-8')
            buffer = []
            stream.on \data, (data) !-> 
              buffer.push(data)
            stream.on \end, !-> callback(buffer.join(""), true)

        fromStream jar.stderr, (err) !->
            if err != ""
                error({message: err}, output)

        # configure global scope, mode, and routines
        parser.scope = input.scope ? []  |>  (.[to])
        parser.routines = _.clone(input.routines)
        
        output.fromNearley = _.chain blocks 
        .map parser~processBlock
        .filter (block) -> block.kind != \set && !(block.set-mode?)
            # only take the expressions that aren't set declarations or mode switches.
            # these are handled internally by Parser
        .value!

        output.scope = parser.scope
        output.routines = parser.routines
        output.isTactic = input.isTactic && \
            !_.any(output.fromNearley, (block) -> block.kind == \routine)

        if output.isTactic
            term = wrapWith(input.term, identifier(\program, '?'))
            blocks =
                for parsedBlock in output.fromNearley
                    tactic: parsedBlock
                    term: term
                    scope: root.scope
                    routines: parser.routines
        else
            blocks =
                for parsedBlock in output.fromNearley
                    check: 
                        if parsedBlock.kind == 'routine' 
                            parsedBlock.body
                        else parsedBlock
                    scope: root.scope
                    #emit:
                    #    if parsedBlock.kind == 'routine'
                    #        {name: encapsName(parsedBlock), style: "loop"}

        # This will read asynchronously from child process' output
        readResponseBlocks jar.stdout, output.fromNearley, (blocks) ->
          output.fromJar = blocks
          success(output)
        , (err) -> error(err, output)
        , (blocks) -> # progress
          output.fromJar = blocks
          progress(output)

        toStream = (stream) ->
            for block in blocks
                stream.write <| JSON.stringify(block)
                stream.write "\n\n"
            stream.end!

        fs.writeFileSync "/tmp/#name.txt" input.text

        stream = fs.createWriteStream "/tmp/#name.json"
        stream.once \open -> toStream stream

        jar.stdin.setEncoding('utf-8')
        toStream jar.stdin

    catch err
        error(err)


class Parser

  (@mode = "check", @scope = [], @routines = {}) ->
  
  stripComments: (input) ->
    input.replace //  \s* \/\/ .*$  |  \/\* [\s\S]*? \*\/  //mg, ''

  splitTextToBlocks: (input) ->
    blocks = input.split /(\n+)(?!\s)/ .map ->
      text: it
    countLines = (text) -> (text.match(/\n/g)||[]).length
    _.reduce blocks, ((l,blk) -> blk.line = l ; l + countLines(blk.text)), 1
    blocks .filter (.text == /\S/)

  processBlock: (block) ->
    @parseBlock block
      @absorbParse ..

  parseBlock: (block) ->
    # Pass the current scope.
    # TODO: is it possible to avoid using a global here?
    root.scope = @scope
    
    # parse block with nearley, filter only non-false results, assert parse unambiguous
    p = new nearley.Parser grammar.ParserRules, grammar.ParserStart
    try
        text = block.text.trim()
        parsed = p.feed text
        results = _.compact parsed.results  # TODO: compact unneeded?
        if results.length == 0 then throw {offset: text.length - 1, message: "Unexpected end of expression"}
        assert results.length == 1, "Ambiguous parse (got #{results.length}): #{JSON.stringify(results)}"
        results[0] <<< {@mode, block.line}
    catch err
        err.line = block.line
        throw err
        
  absorbParse: (parsedBlock) ->
    parsedBlock
      if ..set-mode?
        @mode = ..set-mode
      if ..kind == \set
        if ..multiple? then @scope.push ... ..multiple
        else @scope.push ..
      if ..kind == \routine
        @routines[..name] = parsedBlock



if localStorage? && localStorage['bell.devmode']
    root.devmode = JSON.parse(localStorage['bell.devmode'])
