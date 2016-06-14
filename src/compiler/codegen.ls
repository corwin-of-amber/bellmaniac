fs = require 'fs'
path = require 'path'
spawn = require \child_process .spawn
assert = require \assert
_ = require \lodash

root = exports ? this


write-blocks = (blocks) ->
  config = get-config!
  tmpdir = config.paths.tmpdir ? "/tmp"

  path.join tmpdir, 'emit.json'
    fs.writeFileSync .., (blocks.map JSON.stringify .join "\n\n")


bellmania-codegen = (input, callback) ->

  input-filename = 
    if _.isString(input) then input
    else if _.isArray(input) then write-blocks input
    else assert false, "Invalid input for codegen"

  if ! fs.statSync(input-filename).isFile!
    throw new Error "Not a regular file: '#{input-filename}'"

  config = get-config!
  tmpdir = config.paths.tmpdir ? "/tmp"

  output-filename = config.output.filename ? path.join tmpdir, 'bell.cpp'
    try
      fs.unlinkSync ..
    catch e
      if e.code != 'ENOENT' then throw new Error "Can not write regular file: '#{..}'"

  launch = if root.devmode then <[../Bellmaniac/bell ui.CLI]> else <[java -jar lib/bell.jar]>
  flags = []
  env = {} <<< process.env <<< configure-env!
  jar = spawn launch[0], launch[1 to] ++ flags ++ [input-filename], {env}
  #  running-processes.started ..

  for ,s of jar.{stdin,stdout,stderr} then s.setEncoding('utf-8')

  jar.stdout.on 'data' -> console.log "."
  jar.stderr.on 'data' -> console.warn it

  jar.on 'close', (code) ->
    assert code == 0, "Pre-compilation failed (code=#{code})"
    launch = if root.devmode then <[../Bellmania.Codegen/bellgen]> else <[java -jar lib/bellgen.jar]>
    flags = <[ -o ]> ++ [output-filename]
    jar = spawn launch[0], launch[1 to] ++ flags ++ ['/tmp/prog.json'], {env}
    for ,s of jar.{stdin,stdout,stderr} then s.setEncoding('utf-8')
    #  running-processes.started ..
    jar.stdout.on 'data' -> console.log "."
    jar.stderr.on 'data' -> console.warn it
    jar.on 'close', (code) ->
      console.log "Compilation finished (code=#{code})"
      if code == 0
        window.alert "Output written to '#{output-filename}'"
      callback!


root <<< {bellmania-codegen}