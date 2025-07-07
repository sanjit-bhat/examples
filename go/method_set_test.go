package main

import (
	"testing"
)

type fooer interface {
	foo()
}

type Bar0 struct{}

func (b *Bar0) foo() {}

type Bar1 struct{}

func (b Bar1) foo() {}

func baz[T fooer]() {}

func TestMethodSet(t *testing.T) {
	baz[*Bar0]()
	// *Bar0 is fooer. but that doesn't make Bar0 fooer.
	// baz[Bar0]()

	baz[Bar1]()
	// since Bar1 is fooer, *Bar1 is also fooer.
	// see https://go.dev/ref/spec#Method_sets.
	baz[*Bar1]()

	var f0 Bar0
	// but Go still auto-converts Bar0 to *Bar0 here.
	f0.foo()

	f1 := &Bar1{}
	f1.foo()
}
