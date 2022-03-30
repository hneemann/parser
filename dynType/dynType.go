package dynType

import (
	"bytes"
	"fmt"
	"github.com/hneemann/parser"
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

func (v vList) Float() float64 {
	return 0
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

func convertList(list []Value) Value {
	return vList(list)
}

func swap(f func(a Value, b Value) Value) func(a Value, b Value) Value {
	return func(a Value, b Value) Value {
		return f(b, a)
	}
}

func New() *parser.Parser[Value] {
	return parser.New[Value]().
		Func("float", func(a ...Value) Value { return vFloat(a[0].Float()) }, 1, 1).
		Func("bool", func(a ...Value) Value { return vBool(a[0].Bool()) }, 1, 1).
		Func("string", func(a ...Value) Value { return vString(a[0].String()) }, 1, 1).
		ValFromNum(parseNum).
		ValFromStr(parseStr).
		ValFromList(convertList).
		Unary("-", vNeg).
		Unary("!", vNot).
		Op("|", vOr).
		Op("&", vAnd).
		Op("=", vEqual).
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
