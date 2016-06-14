fs = require 'fs'
spawn = require \child_process .spawn
assert = require \assert
root = exports ? this


bellmania-codegen = (input-filename, callback) ->
  if ! fs.statSync(input-filename).isFile!
    throw new Error "Not a regular file: '#{input-filename}'"
    
  output-filename = '/tmp/bell.cpp'

  launch = if root.devmode then <[../Bellmaniac/bell ui.CLI]> else <[java -jar lib/bell.jar]>
  flags = []
  env = {} <<< process.env <<< configure-env!
  jar = spawn launch[0], launch[1 to] ++ flags ++ [input-filename], {env}
  #  running-processes.started ..

  jar.stdout.on 'data' -> console.log "."
  jar.stderr.on 'data' ->
  
  jar.on 'close', (code) ->
    assert code == 0, "Pre-compilation failed (code=#{code})"
    launch = if root.devmode then <[../Bellmania.Codegen/bellgen]> else <[java -jar lib/bellgen.jar]>
    flags = <[ -o ]> ++ [output-filename]
    jar = spawn launch[0], launch[1 to] ++ flags ++ ['/tmp/prog.json'], {env}
    jar.stdout.on 'data' -> console.log "."
    jar.stderr.on 'data' ->
    jar.on 'close', (code) ->
      console.log "Compilation finished (code=#{code})"
      if code == 0
        window.alert "Output written to '#{output-filename}'"
      callback!


root <<< {bellmania-codegen}