package jpose.syntax;

public sealed interface SyExpression permits SyExpressionVariable, SyExpressionValue, SyExpressionNew,
SyExpressionGetfield, SyExpressionPutfield, SyExpressionLet, SyExpressionAdd, SyExpressionSub, SyExpressionLt, 
SyExpressionAnd, SyExpressionOr, SyExpressionNot, SyExpressionEq, SyExpressionInstanceof, SyExpressionIf, 
SyExpressionInvoke, SyExpressionId {
	public SyExpression replace(String variableName, SyExpression syExpression);
}
