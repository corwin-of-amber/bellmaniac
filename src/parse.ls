
fs = require 'fs-extra'
spawn = require \child_process .spawn
assert = require \assert
_ = require \lodash

root = exports ? this

readResponseBlocks = (output, parsedInputs) ->
    for block, blockIdx in output.split(/\n\n+(?=\S)/).filter(-> it)
        try
            outputBlock = JSON.parse(block)
            if (outputBlock.error)
                throw outputBlock
            {value: outputBlock}
        catch err
            # add line number from input before re-throwing
            # so that correct line can be highlighted
            parsedInputs[blockIdx]
              err.line = (..?check ? ..?tactic)?.line
            throw err

wrapWith = (term, root) ->
    if (term.root.literal != root.literal)
        tree(root, [term])
    else
        term

# input is of form
#     {isTactic: bool,
#      text: string from codemirror
#      term:? previous term (AST) if isTactic is true
#      scope:? previous scope if isTactic is true
#     }
root.bellmaniaParse = (input, success, error, name='synopsis') ->

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
            else []
        env = {} <<< process.env <<< configure-env!
        jar = spawn launch[0], launch[1 to] ++ flags ++ <[-]>, {env}

        fromStream = (stream, callback) ->
            stream.setEncoding('utf-8')
            buffer = []
            stream.on \data, (data) !-> buffer.push(data)
            stream.on \end, !-> callback(buffer.join(""))

        fromStream jar.stdout, (out) !->
            try
                output.fromJar = readResponseBlocks out, output.fromNearley
                success(output)
            catch err
                error(err, output)

        fromStream jar.stderr, (err) !->
            if err != ""
                error({message: err}, output)

        # configure global scope, mode, and routines
        parser.scope = input.scope ? []
        parser.routines = _.clone(input.routines)
        
        output.fromNearley = _.chain blocks 
        .map parser~processBlock
        .filter (block) -> block.kind != \set && !(block.set-mode?)
            # only take the expressions that aren't set declarations or mode switches.
            # these are handled internally by Parser
        .value!
        #.map((block) ->
            # wrap each expression in another layer that includes scope
        #    (block.mode): block
        #    scope: root.scope
        #).value!

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
        #if results[0].isRoutine
        #    toCheck = {}
        #    for k,v of results[0]
        #        if k != \isRoutine
        #            @routines[k] = v
        #            toCheck = v.body
        #    toCheck <<< {@mode, block.line, isRoutine: true}
        #else
        #    results[0] <<< {@mode, block.line}
        #        if ..set-mode? then @mode = ..set-mode
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
