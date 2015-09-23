var assert = chai.assert;

describe("Parser", function() {
  describe("Basic function application", function() {
    it("a", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a");
          var expected = {"$":"Identifier","kind":"variable","literal":"a"};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a b", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a b");
          var expected = {"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"a"},"rhs":{"$":"Identifier","kind":"variable","literal":"b"}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a b c", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a b c");
          var expected = {"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"a"},"rhs":{"$":"Identifier","kind":"variable","literal":"b"}},"rhs":{"$":"Identifier","kind":"variable","literal":"c"}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("a (b c)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a (b c)");
          var expected = {"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"a"},"rhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"b"},"rhs":{"$":"Identifier","kind":"variable","literal":"c"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(a b) c", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(a b) c");
          var expected = {"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"a"},"rhs":{"$":"Identifier","kind":"variable","literal":"b"}},"rhs":{"$":"Identifier","kind":"variable","literal":"c"}};
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
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Identifier","kind":"variable","literal":"x"}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ x y", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ x y");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"x"},"rhs":{"$":"Identifier","kind":"variable","literal":"y"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x y ↦ x y", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x y ↦ x y");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"x"},"rhs":{"$":"Identifier","kind":"variable","literal":"y"}}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x y z ↦ x", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x y z ↦ x");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"z"},"lbody":{"$":"Identifier","kind":"variable","literal":"x"}}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ y ↦ z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ y ↦ z");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Identifier","kind":"variable","literal":"z"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ (y ↦ z)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ (y ↦ z)");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Identifier","kind":"variable","literal":"z"}}};
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
          var expected = {"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"infix"},"rhs":{"$":"Identifier","kind":"variable","literal":"x"}},"rhs":{"$":"Identifier","kind":"variable","literal":"y"}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x `infix` y z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x `infix` y z");
          var expected = {"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"infix"},"rhs":{"$":"Identifier","kind":"variable","literal":"x"}},"rhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"y"},"rhs":{"$":"Identifier","kind":"variable","literal":"z"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x y `infix` z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x y `infix` z");
          var expected = {"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"infix"},"rhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"x"},"rhs":{"$":"Identifier","kind":"variable","literal":"y"}}},"rhs":{"$":"Identifier","kind":"variable","literal":"z"}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });


    it("a b c `infix` d e f", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a b c `infix` d e f");
          var expected = {"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"infix"},"rhs":{"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"a"},"rhs":{"$":"Identifier","kind":"variable","literal":"b"}},"rhs":{"$":"Identifier","kind":"variable","literal":"c"}}},"rhs":{"$":"Application","lhs":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"d"},"rhs":{"$":"Identifier","kind":"variable","literal":"e"}},"rhs":{"$":"Identifier","kind":"variable","literal":"f"}}};
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


  });


  describe("Interaction of function applications and lambda abstractions", function() {
    it("x (y ↦ z)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x (y ↦ z)");
          var expected = {"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"x"},"rhs":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Identifier","kind":"variable","literal":"z"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x) y ↦ z", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(x) y ↦ z");
          var expected = {"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"x"},"rhs":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Identifier","kind":"variable","literal":"z"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x ↦ y) (z ↦ w)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(x ↦ y) (z ↦ w)");
          var expected = {"$":"Application","lhs":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Identifier","kind":"variable","literal":"y"}},"rhs":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"z"},"lbody":{"$":"Identifier","kind":"variable","literal":"w"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ y z ↦ w", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ y z ↦ w");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"z"},"lbody":{"$":"Identifier","kind":"variable","literal":"w"}}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ y (z ↦ w)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ y (z ↦ w)");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Application","lhs":{"$":"Identifier","kind":"variable","literal":"y"},"rhs":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"z"},"lbody":{"$":"Identifier","kind":"variable","literal":"w"}}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("x ↦ (y z ↦ w)", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("x ↦ (y z ↦ w)");
          var expected = {"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"y"},"lbody":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"z"},"lbody":{"$":"Identifier","kind":"variable","literal":"w"}}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x ↦ y) z ↦ w", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("(x ↦ y) z ↦ w");
          var expected = {"$":"Application","lhs":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"x"},"lbody":{"$":"Identifier","kind":"variable","literal":"y"}},"rhs":{"$":"Abstraction","var":{"$":"Identifier","kind":"variable","literal":"z"},"lbody":{"$":"Identifier","kind":"variable","literal":"w"}}};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });

    it("(x ↦ y z) ↦ w doesn't parse", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          assert.throw(function() {p.feed("(x ↦ y z) ↦ w");}, Error, "nearley: No possible parsings (@10: \'↦\').");
    });
  });

  describe("Types", function() {
    it("TODO", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a");
          var expected = {"$":"Identifier","kind":"variable","literal":"a"};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });
  });

  describe("Tokenization and whitespace", function() {
    it("TODO", function() {
          var p = new nearley.Parser(grammar.ParserRules, grammar.ParserStart);
          var parsed = p.feed("a");
          var expected = {"$":"Identifier","kind":"variable","literal":"a"};
          assert.equal(parsed.results.length, 1, "Parse is unambiguous");
          assert.deepEqual(parsed.results[0], expected, "Parse is correct");
    });
  });


});