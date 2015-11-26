spawn = require \child_process .spawn
assert = require \assert
_ = require \lodash

root = exports ? this

stripComments = (input) ->
    input.replace //  \s* \/\/ .*$  |  \/\* [\s\S]*? \*\/  //mg, ''

root.splitTextToBlocks = (input) ->
    blocks = input.split /(\n+)(?!\s)/ .map ->
      text: it
    countLines = (text) -> (text.match(/\n/g)||[]).length
    _.reduce blocks, ((x,y) -> y.line = x ; x + countLines(y.text)), 1
    blocks .filter (.text == /\S/)

readResponseBlocks = (output, parsedInputs) ->
    for block, blockIdx in output.split(/\n\n+(?=\S)/)
        try
            outputBlock = JSON.parse(block)
            if (outputBlock.error)
                throw outputBlock
            {value: outputBlock}
        catch err
            # add line number from input before re-throwing
            # so that correct line can be highlighted
            parsedInputs[blockIdx]
              err.line = (..check ? ..tactic)?.line
            throw err

# input is of form
#     {isTactic: bool,
#      text: string from codemirror
#      termJson:? previous json if isTactic is true
#      scope:? previous scope if isTactic is true
#     }
root.bellmaniaParse = (input, success, error) ->

    blocks = splitTextToBlocks(stripComments(input.text))

    try
        output =
            fromNearley: []
            fromJar: []

        # spawn jar and initialize jar behavior
        jar = spawn "java", <[-jar lib/bell.jar -]>
        #jar = spawn "../Bellmaniac/bell", <[ui.CLI -]>

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

        # reset global list of sets to empty
        root.scope = []

        mode = "check"

        output.fromNearley = _.chain(blocks)
        .map((block) ->
            # parse block with nearley, filter only non-false results, assert parse unambiguous
            p = new nearley.Parser grammar.ParserRules, grammar.ParserStart
            try
                parsed = p.feed block.text
                results = _.compact parsed.results
                if results.length == 0 then throw {message: "No possible parse of input found."}
                assert results.length == 1, JSON.stringify(results) + " is not a unique parse."
                results[0] <<< {mode, block.line}
                  if ..set-mode? then mode := ..set-mode
            catch err
                err.line = block.line
                throw err
        ).filter((block) -> block.kind != \set && !(block.set-mode?)
            # only take the expressions that aren't set declarations
            # nearley has already pushed set declarations to root.scope
        ).map((block) ->
            # wrap each expression in another layer that includes scope
            (block.mode): block
            scope: window.scope
        ).value!


        toStream = (stream) ->
            if input.isTactic
                for parsedBlock in output.fromNearley
                    if (input.termJson.root.literal != \program)
                        term = tree(identifier(\program, '?'), [input.termJson])
                    else
                        term = input.termJson
                    tacticBlock = {
                        tactic: parsedBlock.check,
                        term: term
                        scope: parsedBlock.scope
                    }

                    stream.write <| JSON.stringify(tacticBlock)
                    stream.write "\n\n"
            else
                for parsedBlock in output.fromNearley
                    stream.write <| JSON.stringify(parsedBlock)
                    stream.write "\n\n"
            stream.end!

        fs.writeFileSync "/tmp/synopsis.txt" input.text

        stream = fs.createWriteStream "/tmp/synopsis.json"
        stream.once \open -> toStream stream

        jar.stdin.setEncoding('utf-8')
        toStream jar.stdin

    catch err
        error(err)