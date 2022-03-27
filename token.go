package parser

import (
	"fmt"
	"strings"
	"unicode"
	"unicode/utf8"
)

type TokenType int

const (
	tIdent TokenType = iota
	tOpen
	tClose
	tComma
	tNumber
	tString
	tOperate
	tEof
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
	str     string
	isLast  bool
	last    rune
	tok     chan Token
	isToken bool
	token   Token
	number  Number
}

type Number interface {
	IsNumberFirst(r rune) bool
	isNumber(r rune) bool
}

func NewTokenizer(text string, number Number) *Tokenizer {
	t := make(chan Token)
	tok := &Tokenizer{str: text, number: number, tok: t}
	go tok.run(t)
	return tok
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
		case ' ':
			continue
		case EOF:
			close(tokens)
			return
		case '(':
			tokens <- Token{tOpen, "("}
		case ')':
			tokens <- Token{tClose, ")"}
		case ',':
			tokens <- Token{tComma, ","}
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
			case t.number.IsNumberFirst(c):
				image := t.read(t.number.isNumber)
				tokens <- Token{tNumber, image}
			case unicode.IsLetter(c):
				image := t.read(func(c rune) bool { return unicode.IsLetter(c) || unicode.IsNumber(c) })
				tokens <- Token{tIdent, image}
			default:
				image := t.read(func(c rune) bool {
					return !(unicode.IsLetter(c) || unicode.IsNumber(c) || c == '(' || c == ' ' || c == '"' || c == '\'' || c == ',')
				})
				tokens <- Token{tOperate, image}
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
