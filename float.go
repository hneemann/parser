package parser

import (
	"math"
	"strconv"
)

func NewFloat() *Parser[float64] {
	return New[float64]().
		Op("&", func(a, b float64) float64 {
			if (a != 0) && (b != 0) {
				return 1
			} else {
				return 0
			}
		}).
		Op("|", func(a, b float64) float64 {
			if (a != 0) || (b != 0) {
				return 1
			} else {
				return 0
			}
		}).
		Op("=", func(a, b float64) float64 {
			if a == b {
				return 1
			} else {
				return 0
			}
		}).
		Op("<", func(a, b float64) float64 {
			if a < b {
				return 1
			} else {
				return 0
			}
		}).
		Op(">", func(a, b float64) float64 {
			if a > b {
				return 1
			} else {
				return 0
			}
		}).
		Op("<=", func(a, b float64) float64 {
			if a <= b {
				return 1
			} else {
				return 0
			}
		}).
		Op(">=", func(a, b float64) float64 {
			if a >= b {
				return 1
			} else {
				return 0
			}
		}).
		Op("+", func(a, b float64) float64 { return a + b }).
		Op("-", func(a, b float64) float64 { return a - b }).
		Op("*", func(a, b float64) float64 { return a * b }).
		Op("/", func(a, b float64) float64 { return a / b }).
		Op("^", func(a, b float64) float64 { return math.Pow(a, b) }).
		Unary("-", func(a float64) float64 { return -a }).
		Unary("!", func(a float64) float64 {
			if a == 0 {
				return 1
			} else {
				return 0
			}
		}).
		Func("sin", func(a ...float64) float64 { return math.Sin(a[0]) }, 1, 1).
		Func("cos", func(a ...float64) float64 { return math.Cos(a[0]) }, 1, 1).
		Func("tan", func(a ...float64) float64 { return math.Tan(a[0]) }, 1, 1).
		Func("sqr", func(a ...float64) float64 { return a[0] * a[0] }, 1, 1).
		Func("sqrt", func(a ...float64) float64 { return math.Sqrt(a[0]) }, 1, 1).
		ValFromNum(func(s string) (float64, error) { return strconv.ParseFloat(s, 64) })
}
