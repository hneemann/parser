package dynType

import (
	"github.com/stretchr/testify/assert"
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
	}

	p := New()
	for _, test := range tests {
		v, err := p.Parse(test.exp)
		assert.NoError(t, err, test.name)
		r, err := v(nil)
		assert.NoError(t, err, test.name)
		assert.EqualValues(t, test.res, r, test.name)
	}
}

func Test_Invalid(t *testing.T) {
	p := New()
	f, err := p.Parse("2<3 & \"test\"")
	_, err = f(nil)
	assert.Error(t, err)
}
