errorOverlay = function(line, offset) {
  return { token: function(stream) {
    if (stream.string === line) {
      if (offset) {
        if (stream.pos < offset - 1) {
          stream.pos = offset - 1;
        } else if (stream.pos == offset - 1) {
          stream.next();
          return "underline-error";
        } else {
          stream.skipToEnd();
        }
      } else {
        stream.skipToEnd();
        return "underline-error";
      }
    } else {
      stream.skipToEnd();
    }
  }};
};
