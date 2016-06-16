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

or-nosc = (x,y) -> x||y

configure-env = (config ? get-config!) ->
  path = (process.env.PATH ? "").split!filter (!="")
  dyld = (process.env.DYLD_LIBRARY_PATH ? "").split!filter (!="")
  ld = (process.env.LD_LIBRARY_PATH ? "").split!filter (!="")
  c-path = 
    if (sketchfe = config.paths['sketch-frontend'])?
      {PATH: ([sketchfe] ++ path).join ":"}
    else {}
  c-dyld =
    if or-nosc (z3 = config.paths['z3'])?, (sketchbe = config.paths['sketch-backend'])?
      {DYLD_LIBRARY_PATH: ([z3,sketchbe].filter(->it) ++ dyld).join ":",
       LD_LIBRARY_PATH:   ([z3,sketchbe].filter(->it) ++ ld).join ":"}
    else {}
  c-bell =
    if (bell = config.paths['bellmania'])?
      {BELLMANIA_HOME: bell}
    else {}
  {} <<< c-path <<< c-dyld <<< c-bell


@ <<< {get-config, configure-env}
