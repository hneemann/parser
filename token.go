package parser

import (
	"fmt"
	"strings"
	"unicode/utf8"
)

type TokenType int

const (
	tIdent TokenType = iota
	tOpen
	tClose
	tOpenBracket
	tCloseBracket
	tOpenCurly
	tCloseCurly
	tDot
	tComma
	tColon
	tSemicolon
	tNumber
	tString
	tOperate
	tEof
	tInvalid
)

const (
	EOF rune = 0
)

var TokenEof = Token{tEof, "EOF"}

type Token struct {
	typ   TokenType
	image string
}

func (t Token) String() string {
	return fmt.Sprintf("'%v' [%v]", t.image, t.typ)
}

type Tokenizer struct {
	str           string
	isLast        bool
	last          rune
	tok           chan Token
	isToken       bool
	token         Token
	number        Matcher
	identifier    Matcher
	operator      Matcher
	textOperators map[string]string
}

type Matcher interface {
	MatchesFirst(r rune) bool
	Matches(r rune) bool
}

func NewTokenizer(text string, number, identifier, operator Matcher) *Tokenizer {
	t := make(chan Token)
	tok := &Tokenizer{
		str:           text,
		textOperators: map[string]string{},
		number:        number,
		identifier:    identifier,
		operator:      operator,
		tok:           t}
	go tok.run(t)
	return tok
}

func (t *Tokenizer) SetTextOperators(textOp map[string]string) *Tokenizer {
	t.textOperators = textOp
	return t
}

func (t *Tokenizer) Peek() Token {
	if t.isToken {
		return t.token
	}

	var ok bool
	t.token, ok = <-t.tok
	if ok {
		t.isToken = true
		return t.token
	} else {
		return TokenEof
	}
}

func (t *Tokenizer) Next() Token {
	tok := t.Peek()
	t.isToken = false
	return tok
}

func (t *Tokenizer) run(tokens chan<- Token) {
	for {
		switch t.next() {
		case ' ', '\n', '\r', '\t':
			continue
		case EOF:
			close(tokens)
			return
		case '(':
			tokens <- Token{tOpen, "("}
		case ')':
			tokens <- Token{tClose, ")"}
		case '[':
			tokens <- Token{tOpenBracket, "["}
		case ']':
			tokens <- Token{tCloseBracket, "]"}
		case '{':
			tokens <- Token{tOpenCurly, "{"}
		case '}':
			tokens <- Token{tCloseCurly, "}"}
		case '.':
			tokens <- Token{tDot, "."}
		case ':':
			tokens <- Token{tColon, ":"}
		case ',':
			tokens <- Token{tComma, ","}
		case ';':
			tokens <- Token{tSemicolon, ";"}
		case '"':
			image := t.read(func(c rune) bool { return c != '"' })
			t.next()
			tokens <- Token{tString, image}
		case '\'':
			image := t.read(func(c rune) bool { return c != '\'' })
			t.next()
			tokens <- Token{tIdent, image}
		default:
			t.unread()
			switch c := t.peek(); {
			case t.number.MatchesFirst(c):
				image := t.read(t.number.Matches)
				tokens <- Token{tNumber, image}
			case t.identifier.MatchesFirst(c):
				image := t.read(t.identifier.Matches)
				if t, ok := t.textOperators[image]; ok {
					tokens <- Token{tOperate, t}
				} else {
					tokens <- Token{tIdent, image}
				}
			case t.operator.MatchesFirst(c):
				image := t.read(t.operator.Matches)
				tokens <- Token{tOperate, image}
			default:
				tokens <- Token{tInvalid, string(t.peek())}
			}
		}
	}
}

func (t *Tokenizer) peek() rune {
	if t.isLast {
		return t.last
	}
	if len(t.str) == 0 {
		t.last = 0
		return EOF
	}
	var size int
	t.last, size = utf8.DecodeRuneInString(t.str)
	t.isLast = true
	t.str = t.str[size:]
	return t.last
}

func (t *Tokenizer) consume() {
	if !t.isLast {
		t.peek()
	}
	t.isLast = false
}

func (t *Tokenizer) unread() {
	t.isLast = true
}

func (t *Tokenizer) next() rune {
	n := t.peek()
	t.consume()
	return n
}

func (t *Tokenizer) read(valid func(c rune) bool) string {
	str := strings.Builder{}
	for {
		if c := t.next(); c != 0 && valid(c) {
			str.WriteRune(c)
		} else {
			t.unread()
			return str.String()
		}
	}
}
