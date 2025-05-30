package jpose.syntax;

import java.util.Objects;

public record SyExpressionId(String idName) implements SyExpression {
	public SyExpressionId {
		Objects.requireNonNull(idName);
	}

	@Override
	public SyExpressionId replace(String variableName, SyExpression syExpression) {
		Objects.requireNonNull(variableName);
		Objects.requireNonNull(syExpression);
		
		return this;
	}
}
