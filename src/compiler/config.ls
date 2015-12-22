fs = require \fs
path = require \path


get-config = ->
  fn = path.join(projdir, 'data', 'config.json')
  try
    JSON.parse fs.readFileSync(fn, 'utf-8')
  catch e
    if e instanceof SyntaxError
      console.error "Malformed configuration file '#{fn}'"
    else if e.syscall?  # will be 'open' or 'read'
      console.error "Cannot #{e.syscall} configuration file '#{fn}'"

configure-env = (config ? get-config!) ->
  path = (process.env.PATH ? "").split!filter (!="")
  dyld = (process.env.DYLD_LIBRARY_PATH ? "").split!filter (!="")
  c-path = 
    if (sketchfe = config.paths['sketch-frontend'])?
      {PATH: ([sketchfe] ++ path).join ":"}
    else {}
  c-dyld =
    if (z3 = config.paths['z3'])?
      {DYLD_LIBRARY_PATH: ([z3] ++ dyld).join ":"}
    else {}
  c-bell =
    if (bell = config.paths['bellmania'])?
      {BELLMANIA_HOME: bell}
    else {}
  {} <<< c-path <<< c-dyld <<< c-bell


@ <<< {get-config, configure-env}
