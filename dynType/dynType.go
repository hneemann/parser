package dynType

import (
	"bytes"
	"fmt"
	"github.com/hneemann/parser"
	"math"
	"strconv"
	"strings"
)

type Value interface {
	Bool() bool
	String() string
	Float() float64
}

type vFloat float64

func (v vFloat) Bool() bool {
	return v != 0
}

func (v vFloat) String() string {
	return fmt.Sprintf("%f", v)
}

func (v vFloat) Float() float64 {
	return float64(v)
}

type vString string

func (v vString) Bool() bool {
	return v == "true"
}

func (v vString) String() string {
	return string(v)
}

func (v vString) Float() float64 {
	fl, err := strconv.ParseFloat(string(v), 64)
	if err != nil {
		return 0
	}
	return fl
}

type vBool bool

func (v vBool) Bool() bool {
	return bool(v)
}

func (v vBool) String() string {
	if v {
		return "true"
	} else {
		return "false"
	}
}

func (v vBool) Float() float64 {
	if v {
		return 1
	} else {
		return 0
	}
}

type vLambda struct {
	e parser.Expression[Value]
}

func (v vLambda) Bool() bool {
	return false
}

func (v vLambda) Float() float64 {
	return 0
}

func (v vLambda) String() string {
	return ""
}

type vList []Value

func (v vList) Bool() bool {
	return false
}

func (v vList) String() string {
	var b bytes.Buffer
	for i, v := range v {
		if i == 0 {
			b.WriteString("[")
		} else {
			b.WriteString(",")
		}
		b.WriteString(v.String())
	}
	b.WriteString("]")
	return b.String()
}

func createVars(e Value) parser.Variables[Value] {
	if myMap, ok := e.(parser.Variables[Value]); ok {
		return myMap
	} else {
		return vMap{"this": e}
	}
}

func (v vList) Filter(lambda vLambda) vList {
	var res vList
	for _, entry := range v {
		if lambda.e.Eval(createVars(entry)).Bool() {
			res = append(res, entry)
		}
	}
	return res
}

func (v vList) Map(lambda vLambda) vList {
	var res vList
	for _, entry := range v {
		res = append(res, lambda.e.Eval(createVars(entry)))
	}
	return res
}

func (v vList) Reduce(lambda vLambda) Value {
	var res Value
	for i, entry := range v {
		if i == 0 {
			res = entry
		} else {
			res = lambda.e.Eval(vMap{"value": res, "this": entry})
		}
	}
	return res
}

func (v vList) Sum() Value {
	var res float64
	for _, entry := range v {
		res += entry.Float()
	}
	return vFloat(res)
}

func (v vList) First() Value {
	return v[0]
}

type vMap map[string]Value

func (v vMap) Bool() bool {
	return false
}

func (v vList) Float() float64 {
	return 0
}

func (v vMap) String() string {
	var b bytes.Buffer
	b.WriteString("{")
	first := true
	for k, v := range v {
		if first {
			first = false
		} else {
			b.WriteString(",")
		}
		b.WriteString(k)
		b.WriteString(":")
		b.WriteString(v.String())
	}
	b.WriteString("}")
	return b.String()
}

func (v vMap) Float() float64 {
	return 0
}

func (v vMap) Get(name string) (Value, bool) {
	val, ok := v[name]
	return val, ok
}

func notPossible(a Value, op string, b Value) string {
	return fmt.Sprintf("operation not possible: %v %s %v", a, op, b)
}

func notPossibleUnary(op string, b Value) string {
	return fmt.Sprintf("operation not possible: %s %v", op, b)
}

func vNeg(a Value) Value {
	if a, ok := a.(vFloat); ok {
		return -a
	}
	panic(notPossibleUnary("-", a))
}

func vNot(a Value) Value {
	if a, ok := a.(vBool); ok {
		return !a
	}
	panic(notPossibleUnary("!", a))
}

func vAdd(a, b Value) Value {
	if a, ok := a.(vFloat); ok {
		if b, ok := b.(vFloat); ok {
			return a + b
		}
	}
	if a, ok := a.(vString); ok {
		if b, ok := b.(vString); ok {
			return a + b
		}
	}
	panic(notPossible(a, "+", b))
}

func vSub(a, b Value) Value {
	if a, ok := a.(vFloat); ok {
		if b, ok := b.(vFloat); ok {
			return a - b
		}
	}
	panic(notPossible(a, "-", b))
}

func vMul(a, b Value) Value {
	if a, ok := a.(vFloat); ok {
		if b, ok := b.(vFloat); ok {
			return a * b
		}
	}
	panic(notPossible(a, "*", b))
}

func vDiv(a, b Value) Value {
	if a, ok := a.(vFloat); ok {
		if b, ok := b.(vFloat); ok {
			return a / b
		}
	}
	panic(notPossible(a, "/", b))
}

func vAnd(a, b Value) Value {
	if a, ok := a.(vBool); ok {
		if b, ok := b.(vBool); ok {
			return a && b
		}
	}
	panic(notPossible(a, "&", b))
}

func vOr(a, b Value) Value {
	if a, ok := a.(vBool); ok {
		if b, ok := b.(vBool); ok {
			return a || b
		}
	}
	panic(notPossible(a, "|", b))
}

func vLike(a, b Value) Value {
	if a, ok := a.(vString); ok {
		if b, ok := b.(vString); ok {
			return vBool(strings.Contains(strings.ToLower(string(a)), strings.ToLower(string(b))))
		}
	}
	if b, ok := b.(vList); ok {
		for _, e := range b {
			if e == a {
				return vBool(true)
			}
		}
		return vBool(false)
	}
	panic(notPossible(a, "~", b))
}

func vEqual(a, b Value) Value {
	if a, ok := a.(vFloat); ok {
		if b, ok := b.(vFloat); ok {
			return vBool(a == b)
		}
	}
	if a, ok := a.(vString); ok {
		if b, ok := b.(vString); ok {
			return vBool(a == b)
		}
	}
	if a, ok := a.(vBool); ok {
		if b, ok := b.(vBool); ok {
			return vBool(a == b)
		}
	}
	panic(notPossible(a, "=", b))
}
func vLess(a, b Value) Value {
	if a, ok := a.(vFloat); ok {
		if b, ok := b.(vFloat); ok {
			return vBool(a < b)
		}
	}
	if a, ok := a.(vString); ok {
		if b, ok := b.(vString); ok {
			return vBool(a < b)
		}
	}
	panic(notPossible(a, "<", b))
}

func vLessEqual(a, b Value) Value {
	if a, ok := a.(vFloat); ok {
		if b, ok := b.(vFloat); ok {
			return vBool(a <= b)
		}
	}
	if a, ok := a.(vString); ok {
		if b, ok := b.(vString); ok {
			return vBool(a <= b)
		}
	}
	panic(notPossible(a, "<=", b))
}

func parseNum(s string) (Value, error) {
	v, err := strconv.ParseFloat(s, 64)
	if err != nil {
		return vFloat(0), err
	}
	return vFloat(v), nil
}

func parseStr(s string) (Value, error) {
	return vString(s), nil
}

type arrayHandler struct {
}

func (c arrayHandler) Create(v []Value) Value {
	return vList(v)
}

func (c arrayHandler) GetElement(i Value, list Value) (Value, error) {
	if list, ok := list.(vList); ok {
		i := int(math.Round(i.Float()))
		if i < 0 || i >= len(list) {
			return vBool(false), fmt.Errorf("%v index out of bounds %d", list, i)
		}
		return list[i], nil
	} else {
		return vBool(false), fmt.Errorf("%v is not a list", list)
	}
}

type lambdaHandler struct {
}

func (c lambdaHandler) Create(e parser.Expression[Value]) Value {
	return vLambda{e}
}

type mapHandler struct {
}

func (m mapHandler) Create(aMap map[string]Value) Value {
	return vMap(aMap)
}

func (m mapHandler) GetElement(key string, mapValue Value) (Value, error) {
	if m2, ok := mapValue.(vMap); ok {
		if v, ok := m2[key]; ok {
			return v, nil
		} else {
			return vBool(false), fmt.Errorf("%s not available in %v", key, mapValue)
		}

	} else {
		return vBool(false), fmt.Errorf("%v is not a map", mapValue)
	}
}

func swap(f func(a Value, b Value) Value) func(a Value, b Value) Value {
	return func(a Value, b Value) Value {
		return f(b, a)
	}
}

func New() *parser.Parser[Value] {
	return parser.New[Value]().
		PureFunc("float", func(a ...Value) Value { return vFloat(a[0].Float()) }, 1, 1).
		PureFunc("bool", func(a ...Value) Value { return vBool(a[0].Bool()) }, 1, 1).
		PureFunc("string", func(a ...Value) Value { return vString(a[0].String()) }, 1, 1).
		ValFromNum(parseNum).
		ValFromStr(parseStr).
		ArrayHandler(arrayHandler{}).
		LambdaHandler(lambdaHandler{}).
		MapHandler(mapHandler{}).
		Const("true", vBool(true)).
		Const("false", vBool(false)).
		Unary("-", vNeg).
		Unary("!", vNot).
		Op("|", vOr).
		Op("&", vAnd).
		Op("=", vEqual).
		Op("!=", func(a, b Value) Value { return vBool(!vEqual(a, b).Bool()) }).
		Op("~", vLike).
		Op("<", vLess).
		Op(">", swap(vLess)).
		Op("<=", vLessEqual).
		Op(">=", swap(vLessEqual)).
		Op("+", vAdd).
		Op("-", vSub).
		Op("*", vMul).
		Op("/", vDiv)
}
