fs = require 'fs'
path = require 'path'
child_process = require 'child_process'

logdir = '/tmp/bell-nightly'
bell-flags = '--nocache'

benchmarks =
  * Paren: 
      phases: <[ A B C ]>
  * Gap:
      phases: <[ A B C ]>
  * LCS:
      phases: <[ A ]>
  * Accordion:
      phases: <[ A B C D ]>
  * Knapsack:
      phases: <[ A B ]>


if ! fs.existsSync logdir  # I know. but lstat and access are ugly
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
