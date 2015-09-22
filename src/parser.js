$(document).ready(function() {
	var replacements = [
		[/\\alpha/g, "α"],
		[/\\beta/g, "β"],
		[/\\gamma/g, "γ"],
		[/\\delta/g, "δ"],
		[/\\epsilon/g, "ε"],
		[/\\zeta/g, "ζ"],
		[/\\eta/g, "η"],
		[/\\theta/g, "θ"],
		[/\\iota/g, "ι"],
		[/\\kappa/g, "κ"],
		[/\\lambda/g, "λ"],
		[/\\mu/g, "μ"],
		[/\\nu/g, "ν"],
		[/\\xi/g, "ξ"],
		[/\\omicron/g, "ο"],
		[/\\pi/g, "π"],
		[/\\rho/g, "ρ"],
		[/\\sigma/g, "σ"],
		[/\\tau/g, "τ"],
		[/\\upsilon/g, "υ"],
		[/\\phi/g, "φ"],
		[/\\chi/g, "χ"],
		[/\\psi/g, "ψ"],
		[/\\omega/g, "ω"],
		[/\|->/g,"↦"]];

	var parseAndDisplay = function() {
		var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
		try {
			var parsed = p.feed($("#input").val());
			console.assert(parsed.results.length === 1, parsed.results);
			$("#results").text(JSON.stringify(parsed.results[0], null, 4));
		} catch (err) {
			$("#results").text(err);
		}
	};

	$("#input").keyup(function(e) {

		var text = $("#input").val();
		for (var i = 0; i < replacements.length; i++) {
			text = text.replace(replacements[i][0], replacements[i][1]);
		}
		$("#input").val(text);

		// if pressed enter
		if (13 === e.keyCode) {
			parseAndDisplay();
		}
	});

	$("#submit").click(parseAndDisplay);

});
