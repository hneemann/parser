// Package parser help to implement simple, configurable expression parsers
package parser

import (
	"errors"
	"fmt"
	"reflect"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

type operator[V any] struct {
	operator string
	operate  func(a, b Expression[V], context Variables[V]) V
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
	isPure   bool
}

// Parser is the base class of the parser
// V ist the value type this expression parser works on
type Parser[V any] struct {
	operators      []operator[V]
	unary          map[string]func(a V) V
	functions      map[string]function[V]
	constants      map[string]V
	constantsLocal map[string]V
	numToValue     func(s string) (V, error)
	strToValue     func(s string) (V, error)
	arrayHandler   Array[V]
	lambdaCreator  LambdaCreator[V]
	mapHandler     Map[V]
	textOperators  map[string]string
	number         Matcher
	identifier     Matcher
	operator       Matcher
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

// LambdaCreator allows creating Lambdas
type LambdaCreator[V any] interface {
	// Create creates a Lambda
	Create(Lambda[V]) V

	// IsLambda checks, if argument is a lambda expression
	IsLambda(V) (Lambda[V], bool)
}

// Map allows creating and to access maps
type Map[V any] interface {
	// Create creates a map
	Create(map[string]V) V
	// GetElement returns a value from the map
	GetElement(key string, mapValue V) (V, error)
}

type Expression[V any] interface {
	Eval(context Variables[V]) V
	// isConstant returns true if this expression does not depend on the context
	isConstant() bool
}

type ExpressionFunc[V any] func(context Variables[V]) V

func (e ExpressionFunc[V]) Eval(context Variables[V]) V {
	return e(context)
}

func (e ExpressionFunc[V]) isConstant() bool {
	return false
}

type ConstExpression[V any] struct {
	constVal V
}

func (e ConstExpression[V]) Eval(context Variables[V]) V {
	return e.constVal
}

func (e ConstExpression[V]) isConstant() bool {
	return true
}

// Function is the return type of the parser
type Function[V any] func(context Variables[V]) (V, error)

// Lambda is used to store a lambda function
type Lambda[V any] interface {
	// Eval evaluates the lambda expression
	Eval(V) V
}

type simpleLambda[V any] struct {
	exp  Expression[V]
	name string
}

func (l simpleLambda[V]) Eval(value V) V {
	c := VarMap[V]{l.name: value}
	return l.exp.Eval(c)
}

type addVarContext[V any] struct {
	name   string
	value  V
	parent Variables[V]
}

func (avc addVarContext[V]) Get(name string) (V, bool) {
	if name == avc.name {
		return avc.value, true
	}
	return avc.parent.Get(name)
}

type closure[V any] struct {
	simpleLambda[V]
	context Variables[V]
}

func (c closure[V]) Eval(value V) V {
	return c.exp.Eval(addVarContext[V]{c.name, value, c.context})
}

// New creates a new Parser
func New[V any]() *Parser[V] {
	return &Parser[V]{
		unary:      map[string]func(V) V{},
		functions:  map[string]function[V]{},
		constants:  map[string]V{},
		number:     simpleNumber{},
		identifier: simpleIdentifier{},
		operator:   simpleOperator{},
	}
}

// Op adds an operation to the parser
// The name gives the operation name e.g."+" and the function
// needs to implement the operation.
func (p *Parser[V]) Op(name string, operate func(a, b V) V) *Parser[V] {
	return p.OpContext(name, func(a, b Expression[V], c Variables[V]) V {
		return operate(a.Eval(c), b.Eval(c))
	})
}

// OpContext adds an operation to the parser
// The name gives the operation name e.g."+" and the function
// needs to implement the operation.
func (p *Parser[V]) OpContext(name string, operate func(a, b Expression[V], context Variables[V]) V) *Parser[V] {
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
//Here, functions are allowed whose result does not depend only on the arguments.
//This function may return different results if it is called several times with
//the same arguments. For performance reasons no pure function should be declared here.
//The random function is an example of a non-pure function: The result is different
//for each call, even if the arguments are always the same.
func (p *Parser[V]) Func(name string, f func(a ...V) V, min, max int) *Parser[V] {
	p.functions[name] = function[V]{
		minArgs:  min,
		maxArgs:  max,
		function: f,
		isPure:   false,
	}
	return p
}

//PureFunc declares a pure function
//A pure function is a function whose result depends only on its arguments.
//If a pure function is called several times with the same arguments, always
//the same result must be returned.
//The sin function or the sqrt function are examples of a pure function: If the
//argument is always the same, the result is also the same for each call.
func (p *Parser[V]) PureFunc(name string, f func(a ...V) V, min, max int) *Parser[V] {
	p.functions[name] = function[V]{
		minArgs:  min,
		maxArgs:  max,
		function: f,
		isPure:   true,
	}
	return p
}

//Const declares a constant
func (p *Parser[V]) Const(name string, val V) *Parser[V] {
	p.constants[name] = val
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

// ArrayHandler is used to set a converter that creates values from a list of values
func (p *Parser[V]) ArrayHandler(h Array[V]) *Parser[V] {
	p.arrayHandler = h
	return p
}

// LambdaHandler is used to set a converter that creates lambdas from an expression
func (p *Parser[V]) LambdaCreator(h LambdaCreator[V]) *Parser[V] {
	p.lambdaCreator = h
	return p
}

// MapHandler is used to set a converter that creates values from a map of values
func (p *Parser[V]) MapHandler(m Map[V]) *Parser[V] {
	p.mapHandler = m
	return p
}

// Parse parses the given string and returns a Function
func (p *Parser[V]) Parse(str string) (f Function[V], isConst bool, err error) {
	return p.ParseConst(str, nil)
}

// ParseConst parses the given string with additional constants and returns a Function
func (p *Parser[V]) ParseConst(str string, constants map[string]V) (f Function[V], isConst bool, err error) {
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

	p.constantsLocal = constants
	e := p.parseExpression(tokenizer)
	t := tokenizer.Next()
	if t.typ != tEof {
		return nil, false, errors.New(unexpected("EOF", t))
	}

	if e.isConstant() {
		c := e.Eval(nil)
		return func(context Variables[V]) (v V, ierr error) {
			return c, nil
		}, true, nil
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
		return e.Eval(context), nil
	}, false, nil
}

type parserFunc[V any] func(tokenizer *Tokenizer) Expression[V]

func (p *Parser[V]) parseExpression(tokenizer *Tokenizer) Expression[V] {
	t := tokenizer.Peek()
	if t.typ == tIdent && t.image == "let" {
		tokenizer.Next()
		t = tokenizer.Next()
		if t.typ != tIdent {
			panic("no identifier followed by let")
		}
		name := t.image
		if t := tokenizer.Next(); t.typ != tOperate || t.image != "=" {
			panic(unexpected("=", t))
		}
		exp := p.parse(tokenizer, 0)
		if t := tokenizer.Next(); t.typ != tSemicolon || t.image != ";" {
			panic(unexpected(";", t))
		}
		inner := p.parseExpression(tokenizer)
		return ExpressionFunc[V](func(context Variables[V]) V {
			val := exp.Eval(context)
			innerContext := addVarContext[V]{name: name, value: val, parent: context}
			return inner.Eval(innerContext)
		})
	} else {
		return p.parse(tokenizer, 0)
	}
}

func (p *Parser[V]) parse(tokenizer *Tokenizer, op int) Expression[V] {
	next := p.nextParserCall(op)
	operator := p.operators[op]
	a := next(tokenizer)
	for {
		t := tokenizer.Peek()
		if t.typ == tOperate && t.image == operator.operator {
			tokenizer.Next()
			aa := a
			bb := next(tokenizer)

			if aa.isConstant() && bb.isConstant() {
				r := operator.operate(aa, bb, nil)
				a = ConstExpression[V]{constVal: r}
			} else {
				a = ExpressionFunc[V](func(context Variables[V]) V {
					return operator.operate(aa, bb, context)
				})
			}
		} else {
			return a
		}
	}
}

func (p *Parser[V]) nextParserCall(op int) parserFunc[V] {
	if op+1 < len(p.operators) {
		return func(tokenizer *Tokenizer) Expression[V] {
			return p.parse(tokenizer, op+1)
		}
	} else {
		return p.parseNonOperator
	}
}

func (p *Parser[V]) parseNonOperator(tokenizer *Tokenizer) Expression[V] {
	expression := p.parseLiteral(tokenizer)
	for {
		inner := expression
		switch tokenizer.Peek().typ {
		case tDot:
			tokenizer.Next()
			t := tokenizer.Next()
			if t.typ != tIdent {
				panic("invalid token: " + t.image)
			}
			name := t.image
			if tokenizer.Peek().typ != tOpen {
				//Map access
				if p.mapHandler == nil {
					panic("unknown token type: " + tokenizer.Next().image)
				}
				if inner.isConstant() {
					v, err := p.mapHandler.GetElement(name, inner.Eval(nil))
					if err != nil {
						panic(fmt.Errorf("map error: %w", err))
					}
					expression = ConstExpression[V]{v}
				} else {
					expression = ExpressionFunc[V](func(context Variables[V]) V {
						mapValue := inner.Eval(context)
						v, err := p.mapHandler.GetElement(name, mapValue)
						if err != nil {
							panic(fmt.Errorf("map error: %w", err))
						}
						return v
					})
				}
			} else {
				//Method call
				tokenizer.Next()
				args, argsConst := p.parseArgs(tokenizer, tClose)
				if inner.isConstant() && argsConst {
					a := make([]reflect.Value, len(args)+1)
					a[0] = reflect.ValueOf(inner.Eval(nil))
					for i, e := range args {
						if e.isConstant() {
							a[i+1] = reflect.ValueOf(e.Eval(nil))
						} else {
							panic("arg not const")
						}
					}
					expression = ConstExpression[V]{callFunc(inner.Eval(nil), name, a)}
				} else {
					expression = ExpressionFunc[V](func(context Variables[V]) V {
						value := inner.Eval(context)

						if p.lambdaCreator != nil && len(args) == 1 {
							v, err := p.mapHandler.GetElement(name, value)
							if err == nil {
								if l, ok := p.lambdaCreator.IsLambda(v); ok {
									return l.Eval(args[0].Eval(context))
								}
							}
						}

						a := make([]reflect.Value, len(args)+1)
						a[0] = reflect.ValueOf(value)
						for i, e := range args {
							a[i+1] = reflect.ValueOf(e.Eval(context))
						}

						return callFunc(value, name, a)
					})
				}
			}
		case tOpenBracket:
			if p.arrayHandler == nil {
				panic("unknown token type: " + tokenizer.Next().image)
			}
			tokenizer.Next()
			indexExpr := p.parseExpression(tokenizer)
			t := tokenizer.Next()
			if t.typ != tCloseBracket {
				panic(unexpected("}", t))
			}
			if indexExpr.isConstant() && inner.isConstant() {
				r, err := p.arrayHandler.GetElement(indexExpr.Eval(nil), inner.Eval(nil))
				if err != nil {
					panic(fmt.Errorf("index error: %w", err))
				}
				expression = ConstExpression[V]{r}
			} else {
				expression = ExpressionFunc[V](func(context Variables[V]) V {
					index := indexExpr.Eval(context)
					list := inner.Eval(context)
					v, err := p.arrayHandler.GetElement(index, list)
					if err != nil {
						panic(fmt.Errorf("index error: %w", err))
					}
					return v
				})
			}
		default:
			return expression
		}
	}
}

func callFunc[V any](value V, name string, args []reflect.Value) V {
	name = firstRuneUpper(name)
	typeOf := reflect.TypeOf(value)
	if m, ok := typeOf.MethodByName(name); ok {
		res := m.Func.Call(args)
		if len(res) == 1 {
			if v, ok := res[0].Interface().(V); ok {
				return v
			} else {
				panic(fmt.Errorf("result of method %v is not a value. It is: %v", name, res[0]))
			}
		} else {
			panic(fmt.Errorf("method %v does not return a single value: %v", name, len(res)))
		}
	} else {
		panic(fmt.Errorf("method %v not found", name))
	}
}

func firstRuneUpper(name string) string {
	r, l := utf8.DecodeRune([]byte(name))
	if unicode.IsUpper(r) {
		return name
	}
	return string(unicode.ToUpper(r)) + name[l:]
}

func (p *Parser[V]) parseLiteral(tokenizer *Tokenizer) Expression[V] {
	t := tokenizer.Next()
	switch t.typ {
	case tIdent:
		name := t.image
		if tokenizer.Peek().typ != tOpen {
			// check if 'name' is a constant
			if val, ok := p.constants[name]; ok {
				return ConstExpression[V]{val}
			}
			if p.constantsLocal != nil {
				if val, ok := p.constantsLocal[name]; ok {
					return ConstExpression[V]{val}
				}
			}

			// not a constant, needs to be requested at evaluation time
			return ExpressionFunc[V](func(context Variables[V]) V {
				if context == nil {
					panic("context is nil, variable '" + name + "' not found!")
				}
				if v, ok := context.Get(name); ok {
					return v
				} else {
					panic("variable '" + name + "' not found!")
				}
			})
		} else {
			tokenizer.Next()
			args, allArgsConst := p.parseArgs(tokenizer, tClose)
			if f, ok := p.functions[name]; ok {
				if len(args) < f.minArgs {
					panic("function '" + name + "' requires at least " + strconv.Itoa(f.minArgs) + " arguments")
				} else if len(args) > f.maxArgs {
					panic("function '" + name + "' requires at most " + strconv.Itoa(f.maxArgs) + " arguments")
				} else {
					if f.isPure && allArgsConst {
						a := make([]V, len(args))
						for i, e := range args {
							a[i] = e.Eval(nil)
						}
						r := f.function(a...)
						return ConstExpression[V]{r}
					}
					return ExpressionFunc[V](func(context Variables[V]) V {
						a := make([]V, len(args))
						for i, e := range args {
							a[i] = e.Eval(context)
						}
						return f.function(a...)
					})
				}
			} else {
				if p.lambdaCreator != nil && len(args) == 1 {
					return ExpressionFunc[V](func(context Variables[V]) V {
						if v, ok := context.Get(name); ok {
							if l, ok := p.lambdaCreator.IsLambda(v); ok {
								arg := args[0].Eval(context)
								return l.Eval(arg)
							}
						}
						panic("lambda '" + name + "' not found")
					})
				}
				panic("function '" + name + "' not found")
			}
		}
	case tOpenCurly:
		if p.mapHandler == nil {
			panic("unknown token type: " + t.image)
		}
		args, allArgsConst := p.parseMap(tokenizer)
		if allArgsConst {
			m := map[string]V{}
			for k, v := range args {
				m[k] = v.Eval(nil)
			}
			return ConstExpression[V]{p.mapHandler.Create(m)}
		}
		return ExpressionFunc[V](func(context Variables[V]) V {
			m := map[string]V{}
			for k, v := range args {
				m[k] = v.Eval(context)
			}
			return p.mapHandler.Create(m)
		})
	case tOpenBracket:
		if p.arrayHandler == nil {
			panic("unknown token type: " + t.image)
		}
		args, allArgsConst := p.parseArgs(tokenizer, tCloseBracket)
		if allArgsConst {
			a := make([]V, len(args))
			for i, e := range args {
				a[i] = e.Eval(nil)
			}
			return ConstExpression[V]{p.arrayHandler.Create(a)}
		}
		return ExpressionFunc[V](func(context Variables[V]) V {
			a := make([]V, len(args))
			for i, e := range args {
				a[i] = e.Eval(context)
			}
			return p.arrayHandler.Create(a)
		})
	case tOperate:
		if p.lambdaCreator != nil && t.image == "->" {
			// lambda
			t := tokenizer.Next()
			if t.typ != tIdent {
				panic("lambda ident is missing!")
			}
			e := p.parseExpression(tokenizer)
			return ConstExpression[V]{p.lambdaCreator.Create(simpleLambda[V]{e, t.image})}
		} else if p.lambdaCreator != nil && t.image == "-->" {
			// closure
			t := tokenizer.Next()
			if t.typ != tIdent {
				panic("lambda ident is missing!")
			}
			e := p.parseExpression(tokenizer)
			return ExpressionFunc[V](func(context Variables[V]) V {
				return p.lambdaCreator.Create(closure[V]{simpleLambda[V]{e, t.image}, context})
			})
		} else {
			u := p.unary[t.image]
			if u == nil {
				panic("unary operator '" + t.image + "' not found!")
			}
			e := p.parseLiteral(tokenizer)
			if e.isConstant() {
				return ConstExpression[V]{u(e.Eval(nil))}
			} else {
				return ExpressionFunc[V](func(context Variables[V]) V {
					return u(e.Eval(context))
				})
			}
		}
	case tNumber:
		if p.numToValue == nil {
			panic("no number values allowed")
		}
		v, err := p.numToValue(t.image)
		if err != nil {
			panic(err)
		}
		return ConstExpression[V]{v}
	case tString:
		if p.strToValue == nil {
			panic("no string values allowed")
		}
		v, err := p.strToValue(t.image)
		if err != nil {
			panic(err)
		}
		return ConstExpression[V]{v}
	case tOpen:
		e := p.parseExpression(tokenizer)
		t := tokenizer.Next()
		if t.typ != tClose {
			panic(unexpected(")", t))
		}
		return e
	default:
		panic("unknown token type: " + t.image)
	}
}

func (p *Parser[V]) parseArgs(tokenizer *Tokenizer, closeList TokenType) ([]Expression[V], bool) {
	var args []Expression[V]
	if tokenizer.Peek().typ == closeList {
		tokenizer.Next()
		return args, true
	}
	allConst := true
	for {
		element := p.parseExpression(tokenizer)
		if !element.isConstant() {
			allConst = false
		}
		args = append(args, element)
		t := tokenizer.Next()
		if t.typ == closeList {
			return args, allConst
		}
		if t.typ != tComma {
			panic(unexpected(",", t))
		}
	}
}

func (p Parser[V]) parseMap(tokenizer *Tokenizer) (map[string]Expression[V], bool) {
	m := map[string]Expression[V]{}
	allEntriesConst := true
	for {
		switch t := tokenizer.Next(); t.typ {
		case tCloseCurly:
			return m, allEntriesConst
		case tIdent:
			if c := tokenizer.Next(); c.typ != tColon {
				panic(unexpected(":", c))
			}
			entry := p.parseExpression(tokenizer)
			if !entry.isConstant() {
				allEntriesConst = false
			}
			m[t.image] = entry
			if tokenizer.Peek().typ == tComma {
				tokenizer.Next()
			}
		default:
			panic(unexpected(",", t))
		}
	}
}

func unexpected(expected string, found Token) string {
	return fmt.Sprintf("unexpected token, expected '%s', found %v", expected, found)
}
