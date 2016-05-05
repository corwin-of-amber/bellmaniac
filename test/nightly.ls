fs = require 'fs'
path = require 'path'
child_process = require 'child_process'

logdir = '/tmp/bell-nightly'
bell-flags = '--nocache --cert all --prover cvc4'

benchmarks =
  * Paren: 
      phases: <[ A B C ]>
  * Gap:
      phases: <[ B C ]>  # 'A' currently has a problem with a Synth proof
  * LCS:
      phases: <[ A ]>
  * Accordion:
      phases: <[ A B C D ]>
  * Knapsack:
      phases: <[ A B ]>
  * Bitonic:
      phases: <[ A B C ]>


if ! fs.existsSync logdir  # I know. but lstat and access are ugly and just stupid
  fs.mkdir logdir

for bench in benchmarks
  for name, {phases} of bench
    console.log name, phases
    for phase in phases
      log = fs.openSync(path.join(logdir, "#{name}-#{phase}.log"), 'w')
      cmd = "./bell examples.#name #bell-flags examples/intermediates/#{name}-#{phase}.synopsis.json"
      console.log cmd
      try
        child_process.execSync cmd, stdio: ['ignore', log, log]
      catch
        console.log  "  [FAILED]"
