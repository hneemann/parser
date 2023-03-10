package dynType

import (
	"github.com/hneemann/parser"
	"github.com/stretchr/testify/assert"
	"math"
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
