root = exports ? this

# these words cause an autocomplete hint to pop-up
hintWords =
	* text: "α", displayText: "\\alpha"
	* text: "β", displayText: "\\beta"
	* text: "γ", displayText: "\\gamma"
	* text: "δ", displayText: "\\delta"
	* text: "ε", displayText: "\\epsilon"
	* text: "ζ", displayText: "\\zeta"
	* text: "η", displayText: "\\eta"
	* text: "θ", displayText: "\\theta"
	* text: "ι", displayText: "\\iota"
	* text: "κ", displayText: "\\kappa"
	* text: "λ", displayText: "\\lambda"
	* text: "μ", displayText: "\\mu"
	* text: "ν", displayText: "\\nu"
	* text: "ξ", displayText: "\\xi"
	* text: "ο", displayText: "\\omicron"
	* text: "π", displayText: "\\pi"
	* text: "ρ", displayText: "\\rho"
	* text: "σ", displayText: "\\sigma"
	* text: "τ", displayText: "\\tau"
	* text: "υ", displayText: "\\upsilon"
	* text: "φ", displayText: "\\phi"
	* text: "χ", displayText: "\\chi"
	* text: "ψ", displayText: "\\psi"
	* text: "ω", displayText: "\\omega"
	* text: "×", displayText: "\\times"
	* text: "∩", displayText: "\\cap"

# these words autoreplace without any hint required
autoWords =
	* text: "↦", displayText: "|->"
	* text: "\u27E8", displayText: "\\<"
	* text: "\u27E9", displayText: "\\>"
	* text: "×", displayText: "\\*"

# subscript digits
for i in [0 to 9]
	charCode = 0x2080 + i
	autoWords.push do
		text: String.fromCharCode(charCode),
		displayText: "_#i"

# boxed letters
for letter in ['A' to 'Z']
	charCode = 0xdd30 + letter.charCodeAt(0) - 0x41
	autoWords.push do
		text: "\ud83c" + String.fromCharCode(charCode)
		displayText: "[#letter]"
	autoWords.push do
		text: "\ud83c" + String.fromCharCode(charCode) + "\u0332" # underbar
		displayText: "[#{letter}_]"

findCurWord = (editor, delimiters) ->
	whitespace = /\s/
	cur = editor.getCursor()
	curLine = editor.getLine(cur.line)

	[start, end] = [cur.ch - 1, cur.ch]
	while (start >= 0 && !delimiters.test(curLine.charAt(start)) && !whitespace.test(curLine.charAt(start-1)))
		start -= 1
	curWord = if start != end then curLine.slice(start, end) else ""
	word: curWord,
	start: start,
	end: end

findSuffixWord = (editor, words) ->
	cur = editor.getCursor()
	curLine = editor.getLine(cur.line)

	matches = []
	[start, end, i] = [cur.ch - 1, cur.ch, 1]
	while start >= 0 && words.length > 0
		c = curLine.charAt(start)
		words = words.filter (.displayText[*-i] == c)
		matches ++= words.filter (.displayText.length == i) .map ->
			word: it
			start: start
			end: end
		start -= 1
		i += 1

	matches

hintReplace = (editor) ->
	curPos = findCurWord(editor, /\\/)
	curWord = curPos.word
	cur = editor.getCursor()

	filteredWords = hintWords.filter (w) ->
		curWord.length > 0 && w.displayText.indexOf(curWord) == 0

	list: filteredWords,
	from: CodeMirror.Pos(cur.line, curPos.start),
	to: CodeMirror.Pos(cur.line, curPos.end)

autoReplace = (editor) ->
	cur = editor.getCursor()

	filteredWords = findSuffixWord(editor, autoWords)

	if filteredWords.length > 0
		curPos = filteredWords[0]
		editor.replaceRange(curPos.word.text,
			CodeMirror.Pos(cur.line, curPos.start),
			CodeMirror.Pos(cur.line, curPos.end))

root.cmOptions = ->
	mode:  "scheme"
	matchBrackets:
		bracketRegex: /[(){}[\]⟨⟩]/
		bracketMatching: {"(": ")>", ")": "(<", "[": "]>", "]": "[<", "{": "}>", "}": "{<", "⟨": "⟩>", "⟩": "⟨<"}
	theme: "neat"
	styleActiveLine: true
	viewportMargin: Infinity

root.initEditor = (submitCallback, loadedCallback) ->
	(editor) ->
		CodeMirror.registerHelper "hint", "anyword", hintReplace

		CodeMirror.commands.autocomplete = (cm) ->
			cm.showHint hint: CodeMirror.hint.anyword, completeSingle: false

		editor.on 'change', (editor, changeObj) !->
			localStorage.setItem('codeMirrorContents', editor.getValue())
			text = changeObj.text[0]  # pretty hackey
			valid = text? && text.length == 1 && (
				(text >= "a" && text <= "z") ||
				(text >= "A" && text <= "Z") ||
				(text >= "0" && text <= "9") ||
				(text in <[ ; = , - . / ` [ \ ] ' < > * ]>)
				)
			if valid
				autoReplace(editor)
				CodeMirror.commands.autocomplete(editor)

		if submitCallback
			editor.setOption("extraKeys", {
				"Cmd-Enter": submitCallback
			})

		if loadedCallback
			loadedCallback(editor)