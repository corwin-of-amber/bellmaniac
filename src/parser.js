var spawn = require('child_process').spawn;

$(document).ready(function() {

    var parseAndDisplay = function() {
        var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
        try {
            var parsed = p.feed(cm.getValue());
            console.assert(parsed.results.length === 1, parsed.results);

            $("#parseduntabbed").text(JSON.stringify(parsed.results[0], null, 0));
            $("#parsedtabbed").text(JSON.stringify(parsed.results[0], null, 4));

            var jar = spawn("java", ["-jar", "bell.jar", '-']);

            jar.stdout.once('data', function (data) {
                $("#outputuntabbed").text(data);

                var result = JSON.parse(data);
                $("#outputtabbed").text(JSON.stringify(result, null, 4));

                jar.kill('SIGINT');
            });

            jar.stderr.once('data', function (data) {
              console.log('stderr: ' + data);

              jar.kill('SIGINT');
            });

            jar.stdin.setEncoding('utf-8');
            jar.stdin.write(JSON.stringify(parsed.results[0]) + "\n");
            jar.stdin.end();

        } catch (err) {
            console.log('parsed err: ', err);
        }
    };

    $("#submit").click(parseAndDisplay);

    var words = [
        {text: "α", displayText: "\\alpha"},
        {text: "β", displayText: "\\beta"},
        {text: "γ", displayText: "\\gamma"},
        {text: "δ", displayText: "\\delta"},
        {text: "ε", displayText: "\\epsilon"},
        {text: "ζ", displayText: "\\zeta"},
        {text: "η", displayText: "\\eta"},
        {text: "θ", displayText: "\\theta"},
        {text: "ι", displayText: "\\iota"},
        {text: "κ", displayText: "\\kappa"},
        {text: "λ", displayText: "\\lambda"},
        {text: "μ", displayText: "\\mu"},
        {text: "ν", displayText: "\\nu"},
        {text: "ξ", displayText: "\\xi"},
        {text: "ο", displayText: "\\omicron"},
        {text: "π", displayText: "\\pi"},
        {text: "ρ", displayText: "\\rho"},
        {text: "σ", displayText: "\\sigma"},
        {text: "τ", displayText: "\\tau"},
        {text: "υ", displayText: "\\upsilon"},
        {text: "φ", displayText: "\\phi"},
        {text: "χ", displayText: "\\chi"},
        {text: "ψ", displayText: "\\psi"},
        {text: "ω", displayText: "\\omega"},
        {text: "↦", displayText: "|->"},
        {text: "×", displayText: "\\times"},
        {text: "∩", displayText: "\\cap"}];

    CodeMirror.registerHelper("hint", "anyword", function(editor, options) {
        var delimiters = /[\\|]/;
        var whitespace = /\s/;
        var cur = editor.getCursor(), curLine = editor.getLine(cur.line);
        var start = cur.ch, end = start;
        while (end < curLine.length && !whitespace.test(curLine.charAt(end))) {
            end ++;
        }
        while (start >= 1 && !delimiters.test(curLine.charAt(start)) && !whitespace.test(curLine.charAt(start-1))) {
            start --;
        }
        var curWord = start != end ? curLine.slice(start, end) : "";

        var filteredWords = words.filter(function(w) {return curWord.length > 0 && w.displayText.indexOf(curWord) === 0;});

        return {list: filteredWords, from: CodeMirror.Pos(cur.line, start), to: CodeMirror.Pos(cur.line, end)};
    });

    CodeMirror.commands.autocomplete = function(cm) {
        cm.showHint({hint: CodeMirror.hint.anyword, completeSingle: false});
    };

    var cm = CodeMirror.fromTextArea($("#code")[0], {
      mode:  "scheme",
      theme: "material"
    });

    cm.on('keyup', function(cm, e){
        var keycode = e.keyCode;

        var valid =
            (keycode > 47 && keycode < 58)   || // number keys
            keycode == 32 || keycode == 13   || // spacebar & return key(s) (if you want to allow carriage returns)
            (keycode > 64 && keycode < 91)   || // letter keys
            (keycode > 95 && keycode < 112)  || // numpad keys
            (keycode > 185 && keycode < 193) || // ;=,-./` (in order)
            (keycode > 218 && keycode < 223);   // [\]' (in order)

        if (valid) {
            CodeMirror.commands.autocomplete(cm);
        }
    });
});
