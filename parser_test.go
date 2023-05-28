package parser

import (
	"github.com/stretchr/testify/assert"
	"strconv"
	"testing"
)

func Test_Calculate(t *testing.T) {
	p := NewFloat()
	assert.EqualValues(t, 5, eval(t, mustConst(t, p, "2+3")))
	assert.EqualValues(t, 4, eval(t, mustConst(t, p, "2*2")))
	assert.EqualValues(t, 8, eval(t, mustConst(t, p, "2+3*2")))
	assert.EqualValues(t, 7, eval(t, mustConst(t, p, "2*2+3")))
	assert.EqualValues(t, 4, eval(t, mustConst(t, p, "10/5*2")))
	assert.EqualValues(t, -2, eval(t, mustConst(t, p, "-2")))
	assert.EqualValues(t, -2, eval(t, mustConst(t, p, "-(1+1)")))

	assert.EqualValues(t, 6, eval(t, mustConst(t, p, "2*(1+2)")))
	assert.EqualValues(t, 6, eval(t, mustConst(t, p, "(1+2)*2")))

	assert.EqualValues(t, 9, eval(t, mustConst(t, p, "1+2^3")))
	assert.EqualValues(t, 2, eval(t, mustConst(t, p, "4^0.5")))
}

func eval(t *testing.T, f Function[float64]) float64 {
	v, err := f(nil)
	assert.NoError(t, err)
	return v
}

func evalVar(t *testing.T, f Function[float64], vars VarMap[float64]) float64 {
	v, err := f(vars)
	assert.NoError(t, err)
	return v
}

func mustConst(t *testing.T, p *Parser[float64], s string) Function[float64] {
	f, isConst, err := p.Parse(s)
	assert.True(t, isConst)
	assert.NoError(t, err)
	return f
}

func mustVar(t *testing.T, p *Parser[float64], s string) Function[float64] {
	f, isConst, err := p.Parse(s)
	assert.False(t, isConst)
	assert.NoError(t, err)
	return f
}

func Test_Bool(t *testing.T) {
	p := NewFloat()

	assert.EqualValues(t, 1, eval(t, mustConst(t, p, "5=5")))
	assert.EqualValues(t, 0, eval(t, mustConst(t, p, "5=4")))
	assert.EqualValues(t, 1, eval(t, mustConst(t, p, "!(4=5)")))

	assert.EqualValues(t, 1, eval(t, mustConst(t, p, "1=1 & 2=2")))
	assert.EqualValues(t, 0, eval(t, mustConst(t, p, "1=1 & 2=3")))

	assert.EqualValues(t, 1, eval(t, mustConst(t, p, "!(1=2) & 2=2")))
}

func Test_Var(t *testing.T) {
	p := New[float64]().
		Op("+", func(a, b float64) float64 { return a + b }).
		ValFromNum(func(s string) (float64, error) { return strconv.ParseFloat(s, 64) })

	assert.EqualValues(t, 9, evalVar(t, mustVar(t, p, "a+b"), map[string]float64{"a": 5, "b": 4}))
}

func Test_PureFunc(t *testing.T) {
	p := NewFloat().
		PureFunc("f", func(a ...float64) float64 {
			return a[0] + a[1]
		}, 2, 2)

	assert.EqualValues(t, 6, eval(t, mustConst(t, p, "f(2,3)+1")))
}

func Test_NonPureFunc(t *testing.T) {
	i := 0
	p := NewFloat().
		Func("f", func(a ...float64) float64 {
			i++
			return float64(i)
		}, 0, 0)

	f := mustVar(t, p, "f()")
	assert.EqualValues(t, 1, eval(t, f))
	assert.EqualValues(t, 2, eval(t, f))
	assert.EqualValues(t, 3, eval(t, f))
}

func Test_TextOperator(t *testing.T) {
	p := NewFloat().TextOperator(map[string]string{
		"plus": "+",
		"is":   "=",
	})

	assert.EqualValues(t, 3, eval(t, mustConst(t, p, "1 plus 2")))
	assert.EqualValues(t, 1, eval(t, mustConst(t, p, "2 is 2")))
}

func Test_Invalid(t *testing.T) {
	p := NewFloat()

	_, _, err := p.Parse("5+#5")
	assert.Error(t, err)
	_, _, err = p.Parse("5#5")
	assert.Error(t, err)
}

func Test_firstRuneUpper(t *testing.T) {
	tests := []struct {
		name string
		str  string
		want string
	}{
		{name: "1", str: "a", want: "A"},
		{name: "2", str: "A", want: "A"},
		{name: "3", str: "ab", want: "Ab"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			assert.Equalf(t, tt.want, firstRuneUpper(tt.str), "firstRuneUpper(%v)", tt.str)
		})
	}
}

func Test_Let(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		want float64
	}{
		{name: "1", exp: "let a=5;a*a", want: 25},
		{name: "2", exp: "let a=5;let b=6;a*b", want: 30},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			p := NewFloat()
			e, _, err := p.Parse(tt.exp)
			assert.NoError(t, err)
			res, err := e(nil)
			assert.NoError(t, err)
			assert.EqualValues(t, tt.want, res)
		})
	}
}
