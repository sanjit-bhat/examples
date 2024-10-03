package main

// Go type casting might panic, depending on the number of ret vals used.

import (
	"go/ast"
	"testing"
)

func assertPanic(t *testing.T, f func()) {
	defer func() {
		if r := recover(); r == nil {
			t.Fatal()
		}
	}()
	f()
}

func TestTypeCast(t *testing.T) {
	var e ast.Expr
	e = &ast.Ident{Name: "h"}

	e0, ok0 := e.(*ast.SelectorExpr)
	if e0 != nil {
		t.Fatal()
	}
	if ok0 {
		t.Fatal()
	}

	assertPanic(t, func() {
		_ = e.(*ast.SelectorExpr)
	})
}
