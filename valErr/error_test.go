package valErr

import (
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
		{name: "div", exp: "(10+1e)^(2+0.1e)", res: ValErr{Val: 100, Err: 9.68}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			f, err := NewError().Parse(test.exp)
			assert.NoError(t, err)
			r, err := f(nil)
			assert.NoError(t, err)
			assert.InDelta(t, test.res.Val, r.Val, 1e-2)
			assert.InDelta(t, test.res.Err, r.Err, 1e-2)
		})
	}
}
