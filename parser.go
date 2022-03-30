// Package parser help to implement simple, configurable expression parsers
package parser

import (
	"errors"
	"fmt"
	"strconv"
	"strings"
	"unicode"
)

type operator[V any] struct {
	operator string
	operate  func(a, b V) V
}

type simpleNumber struct {
}

func (s simpleNumber) MatchesFirst(r rune) bool {
	return unicode.IsNumber(r)
}

func (s simpleNumber) Matches(r rune) bool {
	return s.MatchesFirst(r) || r == '.'
}

type simpleIdentifier struct {
}

func (s simpleIdentifier) MatchesFirst(r rune) bool {
	return unicode.IsLetter(r)
}

func (s simpleIdentifier) Matches(r rune) bool {
	return unicode.IsLetter(r) || unicode.IsNumber(r)
}

type simpleOperator struct {
}

func (s simpleOperator) MatchesFirst(r rune) bool {
	return s.Matches(r)
}

func (s simpleOperator) Matches(r rune) bool {
	return strings.ContainsRune("+-*/&|!~<=>^", r)
}

type function[V any] struct {
	minArgs  int
	maxArgs  int
	function func(a ...V) V
}

// Parser is the base class of the parser
// V ist the value type this expression parser works on
type Parser[V any] struct {
	operators     []operator[V]
	unary         map[string]func(a V) V
	functions     map[string]function[V]
	numToValue    func(s string) (V, error)
	strToValue    func(s string) (V, error)
	arrayHandler  Array[V]
	textOperators map[string]string
	number        Matcher
	identifier    Matcher
	operator      Matcher
}

// Variables is the interface which allows the evaluator to access variables
type Variables[V any] interface {
	// Get returns the value of the given name
	Get(name string) (V, bool)
}

// VarMap is a simple map based implementation of the Variables interface
type VarMap[V any] map[string]V

func (m VarMap[V]) Get(name string) (V, bool) {
	v, ok := m[name]
	return v, ok
}

// Array allows creating and to access arrays
type Array[V any] interface {
	// Create creates an array
	Create([]V) V
	// GetElement returns a value from an array
	GetElement(index V, list V) (V, error)
}

type expression[V any] func(context Variables[V]) V

// Function is the return type of the parser
type Function[V any] func(context Variables[V]) (V, error)

// New creates a new Parser
func New[V any]() *Parser[V] {
	return &Parser[V]{
		unary:      map[string]func(V) V{},
		functions:  map[string]function[V]{},
		number:     simpleNumber{},
		identifier: simpleIdentifier{},
		operator:   simpleOperator{},
	}
}

// Op adds an operation to the parser
// The name gives the operation name e.g."+" and the function
// needs to implement the operation.
func (p *Parser[V]) Op(name string, operate func(a, b V) V) *Parser[V] {
	p.operators = append(p.operators, operator[V]{
		operator: name,
		operate:  operate,
	})
	return p
}

// Unary is used to declare unary operations like "-" or "!".
func (p *Parser[V]) Unary(name string, operate func(a V) V) *Parser[V] {
	p.unary[name] = operate
	return p
}

//Func declares a function
func (p *Parser[V]) Func(name string, f func(a ...V) V, min, max int) *Parser[V] {
	p.functions[name] = function[V]{
		minArgs:  min,
		maxArgs:  max,
		function: f,
	}
	return p
}

// Number sets the number Matcher
func (p *Parser[V]) Number(num Matcher) *Parser[V] {
	p.number = num
	return p
}

// Identifier sets the identifier Matcher
func (p *Parser[V]) Identifier(ident Matcher) *Parser[V] {
	p.identifier = ident
	return p
}

// Operator sets the operator Matcher
func (p *Parser[V]) Operator(operator Matcher) *Parser[V] {
	p.operator = operator
	return p
}

// TextOperator sets a map of text aliases for operators.
// Allows setting e.g. "plus" as an alias for "+"
func (p *Parser[V]) TextOperator(textOperators map[string]string) *Parser[V] {
	p.textOperators = textOperators
	return p
}

// ValFromNum is used to set a converter that creates values from numbers
func (p *Parser[V]) ValFromNum(toVal func(val string) (V, error)) *Parser[V] {
	p.numToValue = toVal
	return p
}

// ValFromStr is used to set a converter that creates values from strings
func (p *Parser[V]) ValFromStr(toVal func(val string) (V, error)) *Parser[V] {
	p.strToValue = toVal
	return p
}

// ValFromList is used to set a converter that creates values from a list of values
func (p *Parser[V]) ArrayHandler(h Array[V]) *Parser[V] {
	p.arrayHandler = h
	return p
}

// Parse parses the given string and returns a Function
func (p *Parser[V]) Parse(str string) (f Function[V], err error) {
	defer func() {
		rec := recover()
		if rec != nil {
			if thisErr, ok := rec.(error); ok {
				err = thisErr
			} else {
				err = fmt.Errorf("%s", rec)
			}
			f = nil
		}
	}()
	tokenizer :=
		NewTokenizer(str, p.number, p.identifier, p.operator).
			SetTextOperators(p.textOperators)

	e := p.parse(tokenizer, 0)
	t := tokenizer.Next()
	if t.typ != tEof {
		return nil, errors.New(unexpected("EOF", t))
	}
	return func(context Variables[V]) (v V, ierr error) {
		defer func() {
			rec := recover()
			if rec != nil {
				if thisErr, ok := rec.(error); ok {
					ierr = thisErr
				} else {
					ierr = fmt.Errorf("%s", rec)
				}
			}
		}()
		return e(context), nil
	}, nil
}

type parserFunc[V any] func(tokenizer *Tokenizer) expression[V]

func (p *Parser[V]) parse(tokenizer *Tokenizer, op int) expression[V] {
	next := p.nextParserCall(op)
	operator := p.operators[op]
	a := next(tokenizer)
	for {
		t := tokenizer.Peek()
		if t.typ == tOperate && t.image == operator.operator {
			tokenizer.Next()
			aa := a
			bb := next(tokenizer)
			a = func(context Variables[V]) V {
				return operator.operate(aa(context), bb(context))
			}
		} else {
			return a
		}
	}
}

func (p *Parser[V]) nextParserCall(op int) parserFunc[V] {
	if op+1 < len(p.operators) {
		return func(tokenizer *Tokenizer) expression[V] {
			return p.parse(tokenizer, op+1)
		}
	} else {
		return p.parseNonOperator
	}
}

func (p *Parser[V]) parseNonOperator(tokenizer *Tokenizer) expression[V] {
	expression := p.parseLiteral(tokenizer)
	if tokenizer.Peek().typ == tOpenBracket {
		if p.arrayHandler == nil {
			panic("unknown token type: " + tokenizer.Next().image)
		}
		tokenizer.Next()
		indexExpr := p.parse(tokenizer, 0)
		t := tokenizer.Next()
		if t.typ != tCloseBracket {
			panic(unexpected("}", t))
		}
		return func(context Variables[V]) V {
			index := indexExpr(context)
			list := expression(context)
			v, err := p.arrayHandler.GetElement(index, list)
			if err != nil {
				panic(fmt.Errorf("index error: %w", err))
			}
			return v
		}
	}
	return expression
}

func (p *Parser[V]) parseLiteral(tokenizer *Tokenizer) expression[V] {
	t := tokenizer.Next()
	switch t.typ {
	case tIdent:
		name := t.image
		if tokenizer.Peek().typ != tOpen {
			return func(context Variables[V]) V {
				if v, ok := context.Get(name); ok {
					return v
				} else {
					panic("variable '" + name + "' not found!")
				}
			}
		} else {
			tokenizer.Next()
			args := p.parseArgs(tokenizer, tClose)
			if f, ok := p.functions[name]; ok {
				if len(args) < f.minArgs {
					panic("function '" + name + "' requires at least " + strconv.Itoa(f.minArgs) + " arguments")
				} else if len(args) > f.maxArgs {
					panic("function '" + name + "' requires at most " + strconv.Itoa(f.maxArgs) + " arguments")
				} else {
					return func(context Variables[V]) V {
						a := make([]V, len(args))
						for i, e := range args {
							a[i] = e(context)
						}
						return f.function(a...)
					}
				}
			} else {
				panic("function '" + name + "' not found")
			}
		}
	case tOpenBracket:
		if p.arrayHandler == nil {
			panic("unknown token type: " + t.image)
		}
		args := p.parseArgs(tokenizer, tCloseBracket)
		return func(context Variables[V]) V {
			a := make([]V, len(args))
			for i, e := range args {
				a[i] = e(context)
			}
			return p.arrayHandler.Create(a)
		}
	case tOperate:
		u := p.unary[t.image]
		if u == nil {
			panic("unary operator '" + t.image + "' not found!")
		}
		e := p.parse(tokenizer, 0)
		return func(context Variables[V]) V {
			return u(e(context))
		}
	case tNumber:
		if p.numToValue == nil {
			panic("no number values allowed")
		}
		v, err := p.numToValue(t.image)
		if err != nil {
			panic(err)
		}
		return func(context Variables[V]) V {
			return v
		}
	case tString:
		if p.strToValue == nil {
			panic("no string values allowed")
		}
		v, err := p.strToValue(t.image)
		if err != nil {
			panic(err)
		}
		return func(context Variables[V]) V {
			return v
		}
	case tOpen:
		e := p.parse(tokenizer, 0)
		t := tokenizer.Next()
		if t.typ != tClose {
			panic(unexpected(")", t))
		}
		return e
	default:
		panic("unknown token type: " + t.image)
	}
}

func (p *Parser[V]) parseArgs(tokenizer *Tokenizer, closeList TokenType) []expression[V] {
	var args []expression[V]
	for {
		args = append(args, p.parse(tokenizer, 0))
		t := tokenizer.Next()
		if t.typ == closeList {
			return args
		}
		if t.typ != tComma {
			panic(unexpected(",", t))
		}
	}
}

func unexpected(expected string, found Token) string {
	return fmt.Sprintf("unexpected token, expected '%s', found %v", expected, found)
}
