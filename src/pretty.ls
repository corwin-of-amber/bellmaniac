_ = require \lodash


class PrettyPrint

  render = (obj) ->
    if obj.display
      render obj.display
    else if obj.vbox
      $ '<div>'
        for el in obj.vbox
          render el .append-to ..
    else if obj.tree
      render obj.tree
    else if obj.tape
      render-tape obj.tape
    else if obj.$ == 'Tree'
      $ '<ul>' .addClass 'c'
        $ '<li>' .append-to ..
          render obj.root .append-to ..
          for s in obj.subtrees
            render s .append-to ..
    else if _.isString obj
      $ '<span>' .text obj.replace /->/g '→'
    else
      $ '<span>' .text do
        JSON.stringify Object.keys obj

  reformat-type = -> it?.replace /->/g '→'

  render-mark = (obj, mark) ->
    render obj
      if mark? then ..addClass 'tape-mark'
      if mark?.type then ..addClass 'tip' .attr 'data-tip' reformat-type mark.type

  render-tape = (tape) ->
    [text, annot] = tape.text.split '\t'
    c = $ '<span>'
      emit = (text, mark) -> 
        if text
          render-mark text, mark .addClass 'code' .append-to ..
    last-pos = 0
    for [[u,v], mark] in tape.markup
      emit text.substring(last-pos, u)
      emit text.substring(u, v), mark
      last-pos = v
    emit text.substring(last-pos)
    emit annot ?.addClass 'annotation'
    c

  render: render


export PrettyPrint