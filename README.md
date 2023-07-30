# Note #

This parser is no longer maintained. Too many technical debts have 
accumulated over time. Instead of an extensive re-factorization, I
decided to take only the tokenizer and redevelop the parser, and 
separate the parser and code generator (actually a function 
generator).

See [parser2](https://github.com/hneemann/parser2)

# Parser #

A simple parser that is able to parse expressions. It is configurable 
to many use cases. It supports a generic value type. This allows a dynamic 
type system, which requires runtime type checking.

# Examples #

The file _float.go_ contains a simple example of a float based expression 
parser and the packages _valErr_ and _dynType_  contain two more advanced 
example parsers.
