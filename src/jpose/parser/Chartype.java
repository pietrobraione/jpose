package jpose.parser;

enum Chartype {
	WHITE, ALPHA, DIGIT, OTHER;
	
	static Chartype classifyChar(char c) {
		if (Character.isWhitespace(c)) {
			return WHITE;
		} else if (Character.isAlphabetic(c) || c == '_') {
			return ALPHA;
		} else if (Character.isDigit(c)) {
			return DIGIT;
		} else {
			return OTHER;
		}
	}
}
