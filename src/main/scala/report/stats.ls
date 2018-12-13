fs = require \fs

stats = JSON.parse fs.readFileSync "stats.json"

benchmarks = <[ Paren Gap Accordion LCS Knapsack Bitonic ]>

seconds = -> Math.round(it/100) / 10

ljust = (s, n) -> s + (" " * (n - s.length))

benchmarks.for-each (benchmark) ->
    accum = {}
    for k,v of stats
        if (k.match /^(.*?)-/ ?.1) == benchmark
            for k,l of v
                if k == "Let" then k = "Stratify"
                accum[k] = (accum[k] ? []) ++ l

    avgs = {}
    for k,v of accum
        avgs[k] = seconds( v.reduce((+)) / v.length )

    console.log "  {\\bf #{ljust benchmark, 20}}  &  #{avgs.Slice ? ''}  &  #{avgs.Stratify ? ''}   &   #{avgs.Synth ? ''}  &  #{avgs.Sketch ? ''}     \\\\"
    console.log "  \\hline"
