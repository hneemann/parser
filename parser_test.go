package parser

import (
	"github.com/stretchr/testify/assert"
	"strconv"
	"testing"
)

func Test_Calculate(t *testing.T) {
	p := NewFloat()
	assert.EqualValues(t, 5, eval(t, must(t, p, "2+3")))
	assert.EqualValues(t, 4, eval(t, must(t, p, "2*2")))
	assert.EqualValues(t, 8, eval(t, must(t, p, "2+3*2")))
	assert.EqualValues(t, 7, eval(t, must(t, p, "2*2+3")))
	assert.EqualValues(t, 4, eval(t, must(t, p, "10/5*2")))
	assert.EqualValues(t, -2, eval(t, must(t, p, "-2")))
	assert.EqualValues(t, -2, eval(t, must(t, p, "-(1+1)")))

	assert.EqualValues(t, 6, eval(t, must(t, p, "2*(1+2)")))
	assert.EqualValues(t, 6, eval(t, must(t, p, "(1+2)*2")))

	assert.EqualValues(t, 9, eval(t, must(t, p, "1+2^3")))
	assert.EqualValues(t, 2, eval(t, must(t, p, "4^0.5")))
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

func must(t *testing.T, p *Parser[float64], s string) Function[float64] {
	f, err := p.Parse(s)
	assert.NoError(t, err)
	return f
}

func Test_Bool(t *testing.T) {
	p := NewFloat()

	assert.EqualValues(t, 1, eval(t, must(t, p, "5=5")))
	assert.EqualValues(t, 0, eval(t, must(t, p, "5=4")))
	assert.EqualValues(t, 1, eval(t, must(t, p, "!(4=5)")))

	assert.EqualValues(t, 1, eval(t, must(t, p, "1=1 & 2=2")))
	assert.EqualValues(t, 0, eval(t, must(t, p, "1=1 & 2=3")))

	assert.EqualValues(t, 1, eval(t, must(t, p, "!(1=2) & 2=2")))
}

func Test_Var(t *testing.T) {
	p := New[float64]().
		Op("+", func(a, b float64) float64 { return a + b }).
		ValFromNum(func(s string) (float64, error) { return strconv.ParseFloat(s, 64) })

	assert.EqualValues(t, 9, evalVar(t, must(t, p, "a+b"), map[string]float64{"a": 5, "b": 4}))
}

func Test_Func(t *testing.T) {
	p := NewFloat().
		Func("f", func(a ...float64) float64 {
			return a[0] + a[1]
		}, 2, 2)

	assert.EqualValues(t, 6, eval(t, must(t, p, "f(2,3)+1")))
}

func Test_TextOperator(t *testing.T) {
	p := NewFloat().TextOperator(map[string]string{
		"plus": "+",
		"is":   "=",
	})

	assert.EqualValues(t, 3, eval(t, must(t, p, "1 plus 2")))
	assert.EqualValues(t, 1, eval(t, must(t, p, "2 is 2")))
}

func Test_Invalid(t *testing.T) {
	p := NewFloat()

	_, err := p.Parse("5+#5")
	assert.Error(t, err)
	_, err = p.Parse("5#5")
	assert.Error(t, err)
}
