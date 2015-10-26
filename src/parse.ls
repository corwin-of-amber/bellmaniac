spawn = require \child_process .spawn
assert = require \assert
_ = require \lodash

root = exports ? this

splitTextToBlocks = (input) ->
    input.split /\n+(?!\s)/ .filter (== /\S/)

root.bellmaniaParse = (input, success, error) ->

    blocks = splitTextToBlocks(input)

    try
        buffer = []

        output =
            fromNearley: []
            fromJar: []

        # spawn jar and initialize jar behavior
        jar = spawn "java", <[-jar lib/bell.jar -]>
        jar.stdout.setEncoding('utf-8')
        jar.stdout.on \data, (data) !->
            buffer.push(data)

        jar.stdout.on \end, !->
            try
                for block in buffer.join("").split(/\n\n+(?=\S)/)
                    outputBlock = JSON.parse(block)
                    if (outputBlock.error)
                        throw outputBlock
                    output.fromJar.push({value: outputBlock})
                success(output)
            catch err
                console.log err
                error(err)

        jar.stderr.on \data, (data) !->
            error(data)

        # reset global list of sets to empty
        root.scope = []

        output.fromNearley = _.chain(blocks)
        .map((block) ->
            # parse block with nearley, filter only non-false results, assert parse unambiguous
            p = new nearley.Parser grammar.ParserRules, grammar.ParserStart
            parsed = p.feed block
            results = _.filter parsed.results, (r) -> r
            assert results.length > 0, "No possible parse of input found."
            assert results.length == 1, JSON.stringify(results) + " is not a unique parse."
            results[0]
        ).filter((block) ->
            # only take the expressions that aren't set declarations
            # nearley has already pushed set declarations to root.scope
            block.root.kind != \set
        ).map((block) ->
            # wrap each expression in another layer that includes scope
            check: block
            # scope: window.scope
        ).value!

        toStream = (stream) ->
            for parsedBlock in output.fromNearley
                stream.write <| JSON.stringify(parsedBlock)
                stream.write "\n\n"
            stream.end!

        fs.writeFileSync "/tmp/synopsis.txt" input

        stream = fs.createWriteStream "/tmp/synopsis.json"
        stream.once \open -> toStream stream

        jar.stdin.setEncoding('utf-8')
        toStream jar.stdin

    catch err

        error(err)