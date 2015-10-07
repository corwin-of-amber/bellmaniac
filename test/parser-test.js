var assert = chai.assert;

describe("Parser", function() {
  describe("Basic function application", function() {
    it("a", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"a","kind":"variable"},"subtrees":[]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a b", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a b");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"a","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"b","kind":"variable"},"subtrees":[]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a b c", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a b c");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"a","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"b","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"c","kind":"variable"},"subtrees":[]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a (b c)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a (b c)");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"a","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"b","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"c","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(a b) c", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(a b) c");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"a","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"b","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"c","kind":"variable"},"subtrees":[]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a (b c doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a (b c");
          assert.equal(parsed.results.length, 0, "No parsings found");
    });

  });

  describe("Basic lambda abstractions", function() {
    it("x ↦ x", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ x");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ x y", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ x y");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x y ↦ x y", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x y ↦ x y");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]}]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x y z ↦ x", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x y z ↦ x");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]}]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ y ↦ z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ y ↦ z");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ (y ↦ z)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ (y ↦ z)");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x y) ↦ z doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          assert.throw(function() {p.feed("(x y) ↦ z");}, Error, "nearley: No possible parsings (@6: \'↦\').");
    });

    it("(x ↦ y) ↦ z doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          assert.throw(function() {p.feed("(x ↦ y) ↦ z");}, Error, "nearley: No possible parsings (@8: \'↦\').");
    });
  });

  describe("Infix operations", function() {
    it("x `infix` y", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x `infix` y");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"infix","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x `infix` y z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x `infix` y z");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"infix","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x y `infix` z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x y `infix` z");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"infix","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]}]}]},{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a b c `infix` d e f", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a b c `infix` d e f");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"infix","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"a","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"b","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"c","kind":"variable"},"subtrees":[]}]}]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"d","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"e","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"f","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a `infix1` b `infix2` c", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a `infix1` b `infix2` c");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"infix1","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"a","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"infix2","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"b","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"c","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("`infix` doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          assert.throw(function() {p.feed("`infix`");}, Error, "nearley: No possible parsings (@0: \'`\').");
    });

    it("x `infix` doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x `infix`");
          assert.equal(parsed.results.length, 0, "No parsings found");
    });

    it("`infix` y doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          assert.throw(function() {p.feed("`infix` y");}, Error, "nearley: No possible parsings (@0: \'`\').");
    });

    it("x `infix1` `infix2` y doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          assert.throw(function() {p.feed("x `infix1` `infix2` y");}, Error, "nearley: No possible parsings (@11: \'`\').");
    });

  });

  describe("Interaction of function applications and lambda abstractions", function() {
    it("x (y ↦ z)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x (y ↦ z)");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x) y ↦ z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(x) y ↦ z");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x ↦ y) (z ↦ w)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(x ↦ y) (z ↦ w)");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"w","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ y z ↦ w", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ y z ↦ w");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"w","kind":"variable"},"subtrees":[]}]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ y (z ↦ w)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ y (z ↦ w)");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"w","kind":"variable"},"subtrees":[]}]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ (y z ↦ w)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ (y z ↦ w)");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"w","kind":"variable"},"subtrees":[]}]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x ↦ y) z ↦ w", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(x ↦ y) z ↦ w");
          var expected = {"$":"Tree","root":{"$":"Identifier","literal":"@","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"x","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"y","kind":"variable"},"subtrees":[]}]},{"$":"Tree","root":{"$":"Identifier","literal":"↦","kind":"?"},"subtrees":[{"$":"Tree","root":{"$":"Identifier","literal":"z","kind":"variable"},"subtrees":[]},{"$":"Tree","root":{"$":"Identifier","literal":"w","kind":"variable"},"subtrees":[]}]}]};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x ↦ y z) ↦ w doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          assert.throw(function() {p.feed("(x ↦ y z) ↦ w");}, Error, "nearley: No possible parsings (@10: \'↦\').");
    });
  });

  describe("Slash operator", function() {
    it("TODO", function() {
    });
  });

  describe("Fixpoint operator", function() {
    it("TODO", function() {
    });
  });

  describe("Type declarations", function() {
    it("TODO", function() {
    });
  });

  describe("List concatenation", function() {
    it("TODO", function() {
    });
  });

  describe("Type annotations", function() {
    it("a:T", function() {
    });

    it("(a:T)", function() {
    });

    it("(a):T", function() {
    });

    it("a:(T)", function() {
    });

    it("a:P->Q", function() {
    });

    it("TODO", function() {
    });
  });

  describe("Tokenization and whitespace", function() {
    it("TODO", function() {
    });
  });


});