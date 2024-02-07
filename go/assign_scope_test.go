package main

/*
If you change scopes and use `:=` (because one of the return
variables is fresh), the other variables automatically
becomes fresh as well.
This seems unintuitive.
*/

import (
	"testing"
)

func retFour() (int, int) {
	return 4, 4
}

func TestBad(t *testing.T) {
	a := 5
	for i := 0; i < 1; i++ {
		a, err := retFour()
		t.Log(a, err)
	}
	if a != 5 {
		t.Fatal()
	}
	t.Log("Unintuitive that a scope change caused `:=` to refer to a fresh var")
}

func TestGood(t *testing.T) {
	a := 5
	for i := 0; i < 1; i++ {
		var err int
		a, err = retFour()
		t.Log(a, err)
	}
	if a != 4 {
		t.Fatal()
	}
	t.Log("To fix this, you have to change the `:=` to a `=`")
}

func TestGood2(t *testing.T) {
	a := 5
	a, err := retFour()
	t.Log(a, err)
	if a != 4 {
		t.Fatal()
	}
	t.Log("If there's no scope change, then `:=` uses the existing var")
}
