package jpose.parser;

import java.util.ArrayList;
import java.util.List;

public final class ParserIdentifier implements Parser<String> {
	@Override
	public ParseResult<String> parse(List<String> tokens) {
		if (tokens.isEmpty()) {
			return new ParseResult<>(tokens, OptionalError.error("Expected identifier, found end of stream"));
		} else {
			var token = tokens.getFirst();
			if (token.length() >= 1 && (Character.isAlphabetic(token.charAt(0)) || token.charAt(0) == '_')) {
				var tokensEtc = new ArrayList<>(tokens.subList(1, tokens.size()));
				return new ParseResult<>(tokensEtc, OptionalError.of(token));
			} else {
				return new ParseResult<>(tokens, OptionalError.error("Expected identifier, found " + token));
			}
		}
	}
}
