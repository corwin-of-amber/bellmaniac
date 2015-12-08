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

wrapWith = (term, rootLiteral, kind='?') ->
    if (term.root.literal != rootLiteral)
        tree(identifier(rootLiteral, kind), [term])
    else
        term

# input is of form
#     {isTactic: bool,
#      text: string from codemirror
#      termJson:? previous json if isTactic is true
#      scope:? previous scope if isTactic is true
#     }
root.bellmaniaParse = (input, success, error, name='synopsis') ->

    blocks = splitTextToBlocks(stripComments(input.text))

    try
        output =
            fromNearley: []
            fromJar: []

        # spawn jar and initialize jar behavior
        launch = if root.devmode then <[../Bellmaniac/bell ui.CLI]> else <[java -jar lib/bell.jar]>
        flags =
            if input.dryRun then <[--dry-run]>
            else if input.verify then <[--cert all --prover null --tmpdir]> ++ ["/tmp/" + name + "/"]
            else []
        jar = spawn launch[0], launch[1 to] ++ flags ++ <[-]>

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

        if (input.scope)
            output.scope = _.uniq(window.scope.concat(input.scope), (s) ->
                s.literal ? s[0].literal
            )
        else
            output.scope = window.scope

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
            scope: output.scope
        ).value!

        toStream = (stream) ->
            if input.isTactic
                for parsedBlock in output.fromNearley
                    term = wrapWith(input.termJson, \program)

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

        fs.writeFileSync "/tmp/#name.txt" input.text

        stream = fs.createWriteStream "/tmp/#name.json"
        stream.once \open -> toStream stream

        jar.stdin.setEncoding('utf-8')
        toStream jar.stdin

    catch err
        error(err)


if localStorage? && localStorage['bell.devmode']
    root.devmode = JSON.parse(localStorage['bell.devmode'])
