package jpose.parser;

import static org.junit.jupiter.api.Assertions.*;

import java.util.List;

import org.junit.jupiter.api.Test;

import jpose.syntax.SyDeclClassLit;
import jpose.syntax.SyExpressionLet;
import jpose.syntax.SyExpressionValue;
import jpose.syntax.SyIntLit;
import jpose.syntax.SyPrimitiveConstantInt;
import jpose.syntax.SyPrimitiveConstantSymbol;
import jpose.syntax.SyProgramLit;
import jpose.syntax.SyReferenceConstantNull;
import jpose.syntax.SySymbolExpression;
import jpose.syntax.SyValuePrimitiveConstant;
import jpose.syntax.SyValueReferenceConstant;

class TestParser {	
	@Test
	void testTokenizer1() {
		var t = new Tokenizer();
		var l = t.tokenize("let wy := 4 in null");
		assertEquals(List.of("let", "wy", ":=", "4", "in", "null"), l);
	}
	
	@Test
	void testTokenizer2() {
		var t = new Tokenizer();
		var l = t.tokenize("let x := (@ _10) in null");
		assertEquals(List.of("let", "x", ":=", "(", "@", "_10", ")", "in", "null"), l);
	}
	
	@Test
	void testParser1() {
		var p = new ParserMatchToken("a");
		var pStar = p.star();
		var r = pStar.parse(List.of("a", "a", "a"));
		assertTrue(r.parsed().isPresent());
		assertEquals(List.of("a", "a", "a"), r.parsed().get());
		assertEquals(List.of(), r.tokensResidual());
	}
	
	@Test
	void testParser2() {
		var p = new ParserValue();
		var r = p.parse(List.of("null", "foo", "baz"));
		assertTrue(r.parsed().isPresent());
		assertEquals(new SyValueReferenceConstant(new SyReferenceConstantNull()), r.parsed().get());
		assertEquals(List.of("foo", "baz"), r.tokensResidual());
	}
	
	@Test
	void testParser3() {
		var p = new ParserValue();
		var r = p.parse(List.of("X3", "aa"));
		assertTrue(r.parsed().isPresent());
		assertEquals(new SyValuePrimitiveConstant(new SyPrimitiveConstantSymbol(new SySymbolExpression(3))), r.parsed().get());
		assertEquals(List.of("aa"), r.tokensResidual());
	}
	
	@Test
	void testParser4() {
		var p = new ParserExpression();
		var r = p.parse(List.of("let", "wu", ":=", "3", "in", "null", "one", "two", "three"));
		assertTrue(r.parsed().isPresent());
		assertEquals(new SyExpressionLet("wu", new SyExpressionValue(new SyValuePrimitiveConstant(new SyPrimitiveConstantInt(new SyIntLit(3)))), new SyExpressionValue(new SyValueReferenceConstant(new SyReferenceConstantNull()))), r.parsed().get());
		assertEquals(List.of("one", "two", "three"), r.tokensResidual());
	}
	
	@Test
	void testParser5() {
		var s = "class Object {  } (2 + 3)";
		var p = new ParserProgram();
		var r = p.parse(s);
		assertTrue(r.parsed().isPresent());
		var prg = (SyProgramLit) r.parsed().get();
		assertEquals(1, prg.classes().size());
		var cls = ((SyDeclClassLit) prg.classes().get(0));
		assertEquals("Object", cls.className());
		assertEquals(0, cls.fields().size());
		assertEquals(0, cls.methods().size());
		assertEquals("", cls.superclassName());
	}
	
	@Test
	void testParser6() {
		var s = "class Object {  } class Class1 extends Object {  int m(int x) := (2 + x); } (new Class1.m[3])";
		var p = new ParserProgram();
		var r = p.parse(s);
		assertTrue(r.parsed().isPresent());
		var prg = (SyProgramLit) r.parsed().get();
		assertEquals(2, prg.classes().size());
		var cls1 = ((SyDeclClassLit) prg.classes().get(0));
		assertEquals("Object", cls1.className());
		assertEquals(0, cls1.fields().size());
		assertEquals(0, cls1.methods().size());
		assertEquals("", cls1.superclassName());
		var cls2 = ((SyDeclClassLit) prg.classes().get(1));
		assertEquals("Class1", cls2.className());
		assertEquals(0, cls2.fields().size());
		assertEquals(1, cls2.methods().size());
		assertEquals("Object", cls2.superclassName());
	}
	
	@Test
	void testParser7() {
		var pa = new ParserMatchToken("a");
		var pb = new ParserMatchToken("b");
		var pc = new ParserMatchToken("c");
		var pd = new ParserMatchToken("d");
		var p = pa.andThen(_1 -> pb.andThen(_2 -> pc).star().andThen(_3 -> pd));
		var r = p.parse("a b c b c b c d");
		assertTrue(r.parsed().isPresent());
	}
	
	@Test
	void testParser8() {
		var s = "class Object { } \n"
				+ "\n"
				+ "class Void extends Object { } \n"
				+ "\n"
				+ "class LoopFrame extends Object { \n"
				+ "  Node n; \n"
				+ "  int i; \n"
				+ "} \n"
				+ "\n"
				+ "class Node extends Object { \n"
				+ "  int max; \n"
				+ "  Node next; \n"
				+ "  bool hasNullWithin(Void foo1) := \n"
				+ "    let f := new LoopFrame in \n"
				+ "    let foo2 := (f.n := (this.next)) in \n"
				+ "    let foo3 := (f.i := 1) in \n"
				+ "    let fPost := (this.doLoop[f]) in \n"
				+ "    ((fPost.n) = null); \n"
				+ "\n"
				+ "  LoopFrame doLoop(LoopFrame f) := \n"
				+ "    if ((f.n) = null) then f \n"
				+ "    else if ((this.max) < (f.i)) then f \n"
				+ "    else \n"
				+ "      let foo4 := (f.n := ((f.n).next)) in \n"
				+ "      let foo5 := (f.i := ((f.i) + 1)) in \n"
				+ "      (this.doLoop[f]); \n"
				+ "} \n"
				+ "\n"
				+ "let y := Y0 in \n"
				+ "let foo6 := (y.max := 4) in \n"
				+ "(y.hasNullWithin[new Void])";
		var p = new ParserProgram();
		var r = p.parse(s);
		assertTrue(r.parsed().isPresent());
	}
	
	@Test
	void testParser9() {
		var p = new ParserExpression();
		var r = p.parse(List.of("let", "x", ":=", "(", "@", "_10", ")", "in", "null"));
		assertTrue(r.parsed().isPresent());
	}
}
