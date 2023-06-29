package dynType

import (
	"bytes"
	"fmt"
	"github.com/hneemann/parser"
	"math"
	"sort"
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

type vClosure struct {
	closure parser.Closure[Value]
}

func (v vClosure) Bool() bool {
	return false
}

func (v vClosure) Float() float64 {
	return 0
}

func (v vClosure) String() string {
	return ""
}

func (v vClosure) Eval(val ...Value) Value {
	return v.closure.Eval(val)
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

func (v vList) Filter(closure vClosure) vList {
	if closure.closure.Args() != 1 {
		panic("filter needs closure with one argument")
	}
	var res vList
	for _, entry := range v {
		if closure.closure.Eval([]Value{entry}).Bool() {
			res = append(res, entry)
		}
	}
	return res
}

func (v vList) Map(closure vClosure) vList {
	if closure.closure.Args() != 1 {
		panic("map needs closure with one argument")
	}
	var res vList
	for _, entry := range v {
		res = append(res, closure.closure.Eval([]Value{entry}))
	}
	return res
}

func (v vList) Reduce(initial Value, closure vClosure) Value {
	if closure.closure.Args() != 2 {
		panic("reduce needs closure with two arguments")
	}
	res := initial
	for _, entry := range v {
		res = closure.closure.Eval([]Value{res, entry})
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

func (v vList) Unique() vList {
	m := map[Value]struct{}{}
	for i := range v {
		e := v[i]
		m[e] = struct{}{}
	}
	var l vList
	for e := range m {
		l = append(l, e)
	}
	return l
}

type listOrder struct {
	list    vList
	closure vClosure
}

func (l listOrder) Len() int {
	return len(l.list)
}

func (l listOrder) Less(i, j int) bool {
	vi := l.closure.Eval(l.list[i])
	vj := l.closure.Eval(l.list[j])
	si, oki := vi.(vString)
	sj, okj := vj.(vString)
	if oki && okj {
		return si < sj
	}
	return vi.Float() < vj.Float()
}

func (l listOrder) Swap(i, j int) {
	l.list[i], l.list[j] = l.list[j], l.list[i]
}

func (v vList) Order(closure vClosure) vList {
	if closure.closure.Args() != 1 {
		panic("order needs closure with one argument")
	}
	lo := listOrder{list: v, closure: closure}
	sort.Sort(lo)
	return lo.list
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

type closureHandler struct {
}

func (c closureHandler) Create(l parser.Closure[Value]) Value {
	return vClosure{l}
}

func (c closureHandler) IsClosure(value Value) (parser.Closure[Value], bool) {
	if l, ok := value.(vClosure); ok {
		return l.closure, true
	}
	return nil, false
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
		PureFunc("list", func(a ...Value) Value {
			n := int(a[0].Float())
			l := make(vList, n, n)
			for i := 0; i < n; i++ {
				l[i] = vFloat(i)
			}
			return l
		}, 1, 1).
		PureFunc("ite", func(a ...Value) Value {
			if a[0].Bool() {
				return a[1]
			} else {
				return a[2]
			}
		}, 3, 3).
		ValFromNum(parseNum).
		ValFromStr(parseStr).
		ArrayHandler(arrayHandler{}).
		ClosureHandler(closureHandler{}).
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
