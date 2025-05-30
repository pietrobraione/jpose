package jpose.parser;

import java.util.List;

import jpose.syntax.SyExpression;
import jpose.syntax.SyExpressionAdd;
import jpose.syntax.SyExpressionAnd;
import jpose.syntax.SyExpressionEq;
import jpose.syntax.SyExpressionGetfield;
import jpose.syntax.SyExpressionId;
import jpose.syntax.SyExpressionIf;
import jpose.syntax.SyExpressionInstanceof;
import jpose.syntax.SyExpressionInvoke;
import jpose.syntax.SyExpressionLet;
import jpose.syntax.SyExpressionLt;
import jpose.syntax.SyExpressionNew;
import jpose.syntax.SyExpressionNot;
import jpose.syntax.SyExpressionOr;
import jpose.syntax.SyExpressionPutfield;
import jpose.syntax.SyExpressionSub;
import jpose.syntax.SyExpressionValue;
import jpose.syntax.SyExpressionVariable;

public final class ParserExpression implements Parser<SyExpression> {
	@Override
	public ParseResult<SyExpression> parse(List<String> tokens) {
		var sigma = new ParserValue();
		var identifier = new ParserIdentifier();
		var expression = new ParserExpression();
		var pnew = new ParserMatchToken("new");
		var plet = new ParserMatchToken("let");
		var pAssign = new ParserMatchToken(":=");
		var pin = new ParserMatchToken("in");
		var pif = new ParserMatchToken("if");
		var pthen = new ParserMatchToken("then");
		var pelse = new ParserMatchToken("else");
		var pLeftParens = new ParserMatchToken("(");
		var pRightParens = new ParserMatchToken(")");
		var pPlus = new ParserMatchToken("+");
		var pMinus = new ParserMatchToken("-");
		var pLt = new ParserMatchToken("<");
		var pAnd = new ParserMatchToken("&&");
		var pOr = new ParserMatchToken("||");
		var pNot = new ParserMatchToken("~");
		var pEq = new ParserMatchToken("=");
		var pinstanceof = new ParserMatchToken("instanceof");
		var pDot = new ParserMatchToken(".");
		var pLeftSqBracket = new ParserMatchToken("[");
		var pRightSqBracket = new ParserMatchToken("]");
		var pAt = new ParserMatchToken("@");
		
		return sigma.transform(x -> (SyExpression) new SyExpressionValue(x)).alt(
			   pnew.andThen(_1 ->
			     identifier.transform(x -> (SyExpression) new SyExpressionNew(x)))).alt(
		       plet.andThen(_1 -> 
		         identifier.andThen(x ->
		         pAssign.andThen(_2 ->
		         expression.andThen(y ->
		         pin.andThen(_3 ->
		         expression.transform(z -> (SyExpression) new SyExpressionLet(x, y, z)))))))).alt(
		       pif.andThen(_1 ->
		         expression.andThen(x ->
		         pthen.andThen(_2 -> 
		         expression.andThen(y ->
		         pelse.andThen(_3 ->
		         expression.transform(z -> (SyExpression) new SyExpressionIf(x, y, z)))))))).alt(
		       identifier.transform(x -> (SyExpression) new SyExpressionVariable(x))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pPlus.andThen(_2 -> 
		         expression.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionAdd(x, y))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pMinus.andThen(_2 -> 
		         expression.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionSub(x, y))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pLt.andThen(_2 -> 
		         expression.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionLt(x, y))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pAnd.andThen(_2 -> 
		         expression.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionAnd(x, y))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pOr.andThen(_2 -> 
		         expression.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionOr(x, y))))))).alt(
		       pLeftParens.andThen(_1 ->
		         pNot.andThen(_2 -> 
		         expression.andThen(x -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionNot(x)))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pEq.andThen(_2 -> 
		         expression.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionEq(x, y))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pinstanceof.andThen(_2 -> 
		         identifier.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionInstanceof(x, y))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pDot.andThen(_2 -> 
		         identifier.andThen(y ->
		         pLeftSqBracket.andThen(_3 ->
		         expression.andThen(z ->
		         pRightSqBracket.andThen(_4 ->
		         pRightParens.transform(_5 -> (SyExpression) new SyExpressionInvoke(x, y, z)))))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pDot.andThen(_2 -> 
		         identifier.andThen(y ->
		         pAssign.andThen(_3 ->
		         expression.andThen(z ->
		         pRightParens.transform(_4 -> (SyExpression) new SyExpressionPutfield(x, y, z))))))))).alt(
		       pLeftParens.andThen(_1 ->
		         expression.andThen(x -> 
		         pDot.andThen(_2 -> 
		         identifier.andThen(y -> 
		         pRightParens.transform(_3 -> (SyExpression) new SyExpressionGetfield(x, y))))))).alt(
		  	   pLeftParens.andThen(_1 ->
		  	     pAt.andThen(_2-> 
		  	     identifier.andThen(x ->
		  	     pRightParens.transform(_3 -> (SyExpression) new SyExpressionId(x)))))).parse(tokens);
	}
}
