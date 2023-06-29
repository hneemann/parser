package dynType

import (
	"github.com/hneemann/parser"
	"github.com/stretchr/testify/assert"
	"math"
	"strconv"
	"strings"
	"testing"
)

func Test_Simple(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		res  Value
	}{
		{name: "simple", exp: "2+2", res: vFloat(4)},
		{name: "prio", exp: "2+2*3", res: vFloat(8)},
		{name: "str add", exp: "\"aa\"+\"bb\"", res: vString("aabb")},
		{name: "and", exp: "1<2 & 3<5", res: vBool(true)},
		{name: "and false", exp: "1<2 & 3>5", res: vBool(false)},
		{name: "or", exp: "1<2 | 3>5", res: vBool(true)},
		{name: "or false", exp: "2<1 | 3>5", res: vBool(false)},
		{name: "lessGr", exp: "1<2 = 5>3", res: vBool(true)},
		{name: "lessGr2", exp: "1<2 != 5>3", res: vBool(false)},

		{name: "conv bool to string", exp: "string(1<2)", res: vString("true")},
		{name: "conv bool to string", exp: "string(1>2)", res: vString("false")},
		{name: "conv bool to float", exp: "float(1<2)", res: vFloat(1)},
		{name: "conv bool to float", exp: "float(1>2)", res: vFloat(0)},
		{name: "conv bool to bool", exp: "bool(1<2)", res: vBool(true)},
		{name: "conv bool to bool", exp: "bool(1>2)", res: vBool(false)},

		{name: "conv float to string", exp: "string(1)", res: vString("1.000000")},
		{name: "conv float to float", exp: "float(1)", res: vFloat(1)},
		{name: "conv float to bool", exp: "bool(1)", res: vBool(true)},
		{name: "conv float to bool", exp: "bool(-1)", res: vBool(true)},
		{name: "conv float to bool", exp: "bool(0)", res: vBool(false)},

		{name: "conv string to string", exp: "string(\"hallo\")", res: vString("hallo")},
		{name: "conv string to float", exp: "float(\"1.5\")", res: vFloat(1.5)},
		{name: "conv string to float", exp: "float(\"hallo\")", res: vFloat(0)},
		{name: "conv string to bool", exp: "bool(\"true\")", res: vBool(true)},
		{name: "conv float to bool", exp: "bool(\"false\")", res: vBool(false)},
		{name: "conv float to bool", exp: "bool(\"bla\")", res: vBool(false)},

		{name: "list 1", exp: "1 ~ [1,2,3]", res: vBool(true)},
		{name: "list 2", exp: "1 ~ [4,2,3]", res: vBool(false)},
		{name: "list index", exp: "[4,2,3][1]", res: vFloat(2)},

		{name: "map 1", exp: "{k1:1,k2:5}.k2", res: vFloat(5)},
		{name: "map 2", exp: "{k1:[1,2,3],k2:[4,5,6]}.k2[1]", res: vFloat(5)},
		{name: "map 3", exp: "{k1:[1,2,3],k2:[4,{a:\"true\",b:\"false\"},6]}.k2[1].a", res: vString("true")},
	}

	p := New()
	for _, test := range tests {
		v, isConst, err := p.Parse(test.exp)
		assert.True(t, isConst, test.name)
		assert.NoError(t, err, test.name)
		r, err := v(nil)
		assert.NoError(t, err, test.name)
		assert.EqualValues(t, test.res, r, test.name)
	}
}

func Test_NonConst(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		res  Value
	}{
		{name: "simple", exp: "two+two", res: vFloat(4)},
		{name: "prio", exp: "two+two*three", res: vFloat(8)},
		{name: "str add", exp: "\"aa\"+str", res: vString("aastrVal")},
		{name: "and", exp: "one<two & three<5", res: vBool(true)},
		{name: "and false", exp: "1<two & three>5", res: vBool(false)},
		{name: "or", exp: "1<two | three>5", res: vBool(true)},
		{name: "or false", exp: "2<one | 3>5", res: vBool(false)},
		{name: "lessGr", exp: "1<2 = 5>three", res: vBool(true)},
		{name: "lessGr2", exp: "one<2 != 5>three", res: vBool(false)},

		{name: "conv bool to string", exp: "string(one<2)", res: vString("true")},
		{name: "conv bool to string", exp: "string(1>two)", res: vString("false")},
		{name: "conv bool to float", exp: "float(1<two)", res: vFloat(1)},
		{name: "conv bool to float", exp: "float(one>2)", res: vFloat(0)},
		{name: "conv bool to bool", exp: "bool(1<two)", res: vBool(true)},
		{name: "conv bool to bool", exp: "bool(one>2)", res: vBool(false)},

		{name: "conv float to string", exp: "string(one)", res: vString("1.000000")},
		{name: "conv float to float", exp: "float(one)", res: vFloat(1)},
		{name: "conv float to bool", exp: "bool(one)", res: vBool(true)},
		{name: "conv float to bool", exp: "bool(-one)", res: vBool(true)},
		{name: "conv float to bool", exp: "bool(zero)", res: vBool(false)},

		{name: "conv string to string", exp: "string(str)", res: vString("strVal")},
		{name: "conv string to float", exp: "float(numStr)", res: vFloat(1.5)},
		{name: "conv string to float", exp: "float(str)", res: vFloat(0)},
		{name: "conv string to bool", exp: "bool(strTrue)", res: vBool(true)},
		{name: "conv float to bool", exp: "bool(strFalse)", res: vBool(false)},
		{name: "conv float to bool", exp: "bool(str)", res: vBool(false)},

		{name: "list 1", exp: "1 ~ [one,2,3]", res: vBool(true)},
		{name: "list 2", exp: "1 ~ [4,two,3]", res: vBool(false)},
		{name: "list index", exp: "[4,two,3][1]", res: vFloat(2)},

		{name: "map 1", exp: "{k1:1,k2:five}.k2", res: vFloat(5)},
		{name: "map 2", exp: "{k1:[1,2,3],k2:[4,five,6]}.k2[1]", res: vFloat(5)},
		{name: "map 3", exp: "{k1:[1,2,3],k2:[4,{a:str,b:\"false\"},6]}.k2[1].a", res: vString("strVal")},
	}

	vars := parser.VarMap[Value]{
		"zero":     vFloat(0),
		"one":      vFloat(1),
		"two":      vFloat(2),
		"three":    vFloat(3),
		"five":     vFloat(5),
		"str":      vString("strVal"),
		"strTrue":  vString("true"),
		"strFalse": vString("false"),
		"numStr":   vString("1.5"),
	}

	p := New()
	for _, test := range tests {
		v, isConst, err := p.Parse(test.exp)
		assert.False(t, isConst, test.name)
		assert.NoError(t, err, test.name)
		r, err := v(vars)
		assert.NoError(t, err, test.name)
		assert.EqualValues(t, test.res, r, test.name)
	}
}

func Test_DeclareConst(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		res  Value
	}{
		{name: "simple", exp: "pi*2", res: vFloat(math.Pi * 2)},
	}

	p := New().Const("pi", vFloat(math.Pi))
	for _, test := range tests {
		v, isConst, err := p.Parse(test.exp)
		assert.True(t, isConst, test.name)
		assert.NoError(t, err, test.name)
		r, err := v(nil)
		assert.NoError(t, err, test.name)
		assert.EqualValues(t, test.res, r, test.name)
	}
}

func Test_Invalid(t *testing.T) {
	p := New()
	_, _, err := p.Parse("2<3 & \"test\"")
	assert.Error(t, err)
}

func Test_Neg(t *testing.T) {
	tests := []struct {
		name    string
		exp     string
		res     Value
		isConst bool
	}{
		{name: "map.neg", exp: "let m={a:2,b:3}; -m.a*2", res: vFloat(-4), isConst: false},
		{name: "map.neg", exp: "let m={a:2,b:3}; -(-m.a*2)", res: vFloat(4), isConst: false},
		{name: "map.neg", exp: "let m={a:2,b:3}; -m.a+m.b", res: vFloat(1), isConst: false},
		{name: "arr.neg", exp: "let a=[1,2,3]; -a[1]*2", res: vFloat(-4), isConst: false},
	}

	p := New()
	for _, test := range tests {
		v, isConst, err := p.Parse(test.exp)
		assert.EqualValues(t, isConst, test.isConst, test.name)
		assert.NoError(t, err, test.name, test.name)
		r, err := v(nil)
		assert.NoError(t, err, test.name)
		assert.EqualValues(t, test.res, r, test.name)
	}
}

func Test_Lambda(t *testing.T) {
	tests := []struct {
		name    string
		exp     string
		res     float64
		isConst bool
	}{
		{name: "first", exp: "[{a:1,b:1},{a:2,b:4},{a:3,b:9},{a:4,b:16}].filter(e->e.a>1).first().b", res: 4},
		{name: "sum", exp: "[{a:1,b:1},{a:2,b:4},{a:3,b:9},{a:4,b:16}].filter(e->e.a>1).map(e->e.a*e.b).sum()", res: 99},
		{name: "reduce", exp: "[{a:1,b:1},{a:2,b:4},{a:3,b:9},{a:4,b:16}].filter(e->e.a>1).map(e->e.a*e.b).reduce(0, closure(sum,v)->sum+v)", res: 99},
		{name: "max", exp: "[{a:1,b:1},{a:2,b:4},{a:4,b:16},{a:3,b:9}].map(e->e.b).reduce(0,closure(max,v)->ite(max>v,max,v))", res: 16},
		{name: "simple", exp: "let sqr=x->x*x;sqr(5)", res: 25},
		{name: "simpleLong", exp: "let sqr=closure(x)->x*x;sqr(5)", res: 25},
		{name: "two", exp: "let sum=closure(a,b)->a+b;sum(20,5)", res: 25},
		{name: "map", exp: "let map={a:x->x*x,b:5};map.a(map.b)", res: 25},
		{name: "list", exp: "list(10).map(i->{a:i, b:i*i}).map(e->e.b).sum()", res: 285},
		{name: "list2", exp: "list(10).map(i->i*i).sum()", res: 285},
		{name: "newton", exp: "let sqrt=x->list(10).reduce(1,closure(xn,n)->xn+(x-xn*xn)/(2*xn));sqrt(2)", res: math.Sqrt(2)},
	}

	p := New()
	for _, test := range tests {
		v, isConst, err := p.Parse(test.exp)
		assert.EqualValues(t, isConst, test.isConst, test.name)
		assert.NoError(t, err, test.name)
		r, err := v(nil)
		assert.NoError(t, err, test.name)
		if f, ok := r.(vFloat); ok {
			assert.InDelta(t, float64(test.res), float64(f), 1e-6, test.name)
		} else {
			t.Fail()
		}
	}
}

func Test_stream(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		res  Value
	}{
		{name: "first", exp: "list.filter(e->e.a>1).first().b", res: vFloat(4)},
		{name: "sum", exp: "list.filter(e->e.a>1).map(e->e.a*e.b).sum()", res: vFloat(99)},
		{name: "reduce", exp: "list.filter(e-> e.a>1).map(e->e.a*e.b).reduce(0,closure(s,v)->s+v)", res: vFloat(99)},
	}

	var list vList
	for i := 1; i <= 4; i++ {
		list = append(list, vMap{"a": vFloat(i), "b": vFloat(i * i)})
	}
	c := parser.VarMap[Value]{"list": list}
	p := New()
	for _, test := range tests {
		v, isConst, err := p.Parse(test.exp)
		assert.False(t, isConst, test.name)
		assert.NoError(t, err, test.name)
		r, err := v(c)
		assert.NoError(t, err, test.name)
		assert.EqualValues(t, test.res, r, test.name)
	}
}

func Test_closure(t *testing.T) {
	exp := "list.map(e->e.a).unique().order(e->e).map(name->[name,list.filter(e->e.a=name).map(e->e.b).sum()])"

	var list vList
	var result vList
	for i := 1; i <= 4; i++ {
		list = append(list, vMap{"a": vString("num" + strconv.Itoa(i)), "b": vFloat(i * i)})
		list = append(list, vMap{"a": vString("num" + strconv.Itoa(i)), "b": vFloat(i*i + 1)})
		result = append(result, vList{vString("num" + strconv.Itoa(i)), vFloat(2*i*i + 1)})
	}
	p := New()

	v, isConst, err := p.Parse(exp)
	assert.False(t, isConst)
	assert.NoError(t, err)
	r, err := v(parser.VarMap[Value]{"list": list})
	assert.NoError(t, err)
	assert.EqualValues(t, result, r)
}

func Test_MethodNotFound(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		res  string
	}{
		{name: "method", exp: "[1,2].notAvail()", res: "Map("},
		{name: "func", exp: "let x=notAvail();1", res: "ite("},
	}

	for _, test := range tests {
		v, _, err := New().Parse(test.exp)
		assert.NoError(t, err)
		_, err = v(parser.VarMap[Value]{})
		assert.Error(t, err)
		assert.True(t, strings.Contains(err.Error(), test.res), test.name+"->"+err.Error())
	}
}
