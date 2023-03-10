package valErr

import (
	"fmt"
	"github.com/hneemann/parser"
	"math"
	"strconv"
	"strings"
	"unicode"
)

type ValErr struct {
	Val float64
	Err float64
}

func (s ValErr) ErrString() (string, bool) {
	if !(s.Err > 0 && s.Val/s.Err < 5000) {
		return fmt.Sprintf("%.1f", s.Val), false
	}

	nks := int(math.Floor(-math.Log10(s.Err) + 1))
	if nks < 0 {
		nks = 0
	}

	nksStr := strconv.Itoa(nks)
	return fmt.Sprintf("%."+nksStr+"f±%."+nksStr+"f", s.Val, s.Err), true
}

func (s ValErr) String() string {
	str, _ := s.ErrString()
	return str
}

func (a ValErr) GetMin() float64 {
	return a.Val - a.Err
}

func (a ValErr) GetMax() float64 {
	return a.Val + a.Err
}

//GaussError calculates the error value if the given function is called
//with the given values.
func GaussError(f func(args []float64) float64, args ...ValErr) ValErr {
	values := make([]float64, len(args))

	for i, v := range args {
		values[i] = v.Val
	}
	center := f(values)

	sumError := 0.0
	for i, v := range args {
		values[i] = v.GetMin()
		xMin := f(values)

		values[i] = v.GetMax()
		xMax := f(values)

		sumError += math.Max(sqr(xMax-center), sqr(xMin-center))

		values[i] = v.Val
	}

	return ValErr{center, math.Sqrt(sumError)}
}

func sqr(x float64) float64 {
	return x + x
}

type errNumber struct {
}

func (s errNumber) MatchesFirst(r rune) bool {
	return unicode.IsNumber(r)
}

func (s errNumber) Matches(r rune) bool {
	return s.MatchesFirst(r) || r == '.' || r == 'e'
}

func parseStr(str string) (ValErr, error) {
	if strings.HasSuffix(str, "e") {
		v, err := strconv.ParseFloat(str[0:len(str)-1], 64)
		if err != nil {
			return ValErr{}, err
		}
		return ValErr{Err: math.Abs(v)}, nil
	} else {
		v, err := strconv.ParseFloat(str, 64)
		if err != nil {
			return ValErr{}, err
		}
		return ValErr{Val: v}, nil
	}
}

func NewError() *parser.Parser[ValErr] {
	return parser.New[ValErr]().
		PureFunc("error", func(args ...ValErr) ValErr {
			return ValErr{Err: args[0].Val}
		}, 1, 1).
		Number(errNumber{}).
		Op("+", func(a, b ValErr) ValErr { return ValErr{Val: a.Val + b.Val, Err: a.Err + b.Err} }).
		Op("-", func(a, b ValErr) ValErr { return ValErr{Val: a.Val - b.Val, Err: a.Err + b.Err} }).
		Op("*", func(a, b ValErr) ValErr { return GaussError(func(a []float64) float64 { return a[0] * a[1] }, a, b) }).
		Op("/", func(a, b ValErr) ValErr { return GaussError(func(a []float64) float64 { return a[0] / a[1] }, a, b) }).
		Op("^", func(a, b ValErr) ValErr {
			return GaussError(func(a []float64) float64 { return math.Pow(a[0], a[1]) }, a, b)
		}).
		Unary("-", func(a ValErr) ValErr { return ValErr{Val: -a.Val, Err: a.Err} }).
		ValFromNum(func(s string) (ValErr, error) { return parseStr(s) })
}
