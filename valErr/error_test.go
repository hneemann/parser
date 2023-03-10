package valErr

import (
	"github.com/hneemann/parser"
	"github.com/stretchr/testify/assert"
	"testing"
)

func Test(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		res  ValErr
	}{
		{name: "simple", exp: "1+2e", res: ValErr{Val: 1, Err: 2}},
		{name: "mul no error", exp: "2*(2+1e)", res: ValErr{Val: 4, Err: 2}},
		{name: "mul error", exp: "(5+1e)*(6+1e)", res: ValErr{Val: 30, Err: 4.69}},
		{name: "div", exp: "(10+1e)/(5+1e)", res: ValErr{Val: 2, Err: 1.18}},
		{name: "pow", exp: "(10+1e)^(2+0.1e)", res: ValErr{Val: 100, Err: 9.68}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			f, isConst, err := NewError().Parse(test.exp)
			assert.True(t, isConst, test.name)
			assert.NoError(t, err)
			r, err := f(nil)
			assert.NoError(t, err)
			assert.InDelta(t, test.res.Val, r.Val, 1e-2)
			assert.InDelta(t, test.res.Err, r.Err, 1e-2)
		})
	}
}

func Test_NonConst(t *testing.T) {
	tests := []struct {
		name string
		exp  string
		res  ValErr
	}{
		{name: "simple", exp: "one+error(two)", res: ValErr{Val: 1, Err: 2}},
		{name: "mul no error", exp: "2*(two+1e)", res: ValErr{Val: 4, Err: 2}},
		{name: "mul error", exp: "(five+1e)*(six+1e)", res: ValErr{Val: 30, Err: 4.69}},
		{name: "div", exp: "(10+1e)/(five+1e)", res: ValErr{Val: 2, Err: 1.18}},
		{name: "pow", exp: "(10+1e)^(two+0.1e)", res: ValErr{Val: 100, Err: 9.68}},
	}

	vars := parser.VarMap[ValErr]{
		"one":  ValErr{Val: 1},
		"two":  ValErr{Val: 2},
		"five": ValErr{Val: 5},
		"six":  ValErr{Val: 6},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			f, isConst, err := NewError().Parse(test.exp)
			assert.False(t, isConst, test.name)
			assert.NoError(t, err)
			r, err := f(vars)
			assert.NoError(t, err)
			assert.InDelta(t, test.res.Val, r.Val, 1e-2)
			assert.InDelta(t, test.res.Err, r.Err, 1e-2)
		})
	}
}
