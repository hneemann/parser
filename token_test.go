package parser

import (
	"github.com/stretchr/testify/assert"
	"testing"
)

func TestNewTokenizer(t *testing.T) {
	tok := NewTokenizer("test", simpleNumber{}, simpleIdentifier{}, simpleOperator{})
	assert.EqualValues(t, Token{tIdent, "test"}, tok.Next())
	assert.EqualValues(t, TokenEof, tok.Next())

	tok = NewTokenizer("püp", simpleNumber{}, simpleIdentifier{}, simpleOperator{})
	assert.EqualValues(t, Token{tIdent, "püp"}, tok.Next())
	assert.EqualValues(t, TokenEof, tok.Next())

	tok = NewTokenizer("a 'A'", simpleNumber{}, simpleIdentifier{}, simpleOperator{})
	assert.EqualValues(t, Token{tIdent, "a"}, tok.Next())
	assert.EqualValues(t, Token{tIdent, "A"}, tok.Next())
	assert.EqualValues(t, TokenEof, tok.Next())

	tok = NewTokenizer("'püp'", simpleNumber{}, simpleIdentifier{}, simpleOperator{})
	assert.EqualValues(t, Token{tIdent, "püp"}, tok.Next())
	assert.EqualValues(t, TokenEof, tok.Next())

	tok = NewTokenizer("\"püp\"", simpleNumber{}, simpleIdentifier{}, simpleOperator{})
	assert.EqualValues(t, Token{tString, "püp"}, tok.Next())
	assert.EqualValues(t, TokenEof, tok.Next())

	tok = NewTokenizer("(a)", simpleNumber{}, simpleIdentifier{}, simpleOperator{})
	assert.EqualValues(t, Token{tOpen, "("}, tok.Next())
	assert.EqualValues(t, Token{tIdent, "a"}, tok.Next())
	assert.EqualValues(t, Token{tClose, ")"}, tok.Next())
	assert.EqualValues(t, TokenEof, tok.Next())

	tok = NewTokenizer("5.5", simpleNumber{}, simpleIdentifier{}, simpleOperator{})
	assert.EqualValues(t, Token{tNumber, "5.5"}, tok.Next())
	assert.EqualValues(t, TokenEof, tok.Next())

}
