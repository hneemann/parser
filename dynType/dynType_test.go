package dynType

import (
	"fmt"
	"github.com/stretchr/testify/assert"
	"testing"
)

func Test_Simple(t *testing.T) {
	p := New()
	v, err := p.Parse("\"Testtext\" ~ \"tt\"")
	assert.NoError(t, err)
	r, err := v(nil)
	assert.NoError(t, err)

	fmt.Println(r)
}
