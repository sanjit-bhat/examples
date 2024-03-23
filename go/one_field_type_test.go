package main

import (
	"reflect"
	"testing"
)

// [Reference](https://go.dev/ref/spec#Type_declarations).

// Type definition.
// In many ways, this behaves as an alias for []byte,
// but actually, it's a distinct type.
type ByteDecl []byte

// This allows us to create receivers.
func (b ByteDecl) receiver() {
	b[0] = 4
}

// Alias declaration.
type ByteAlias = []byte

/*
This would fail since ByteAlias is a literal alias for []byte.
func (b ByteAlias) receiver() {
    b[0] = 4
}
*/

func TestTypeOneField(t *testing.T) {
	var decl ByteDecl = []byte{2, 2}
	t.Log("easily convert from original type to re-decl", decl)

	var sl []byte = decl
	t.Log("easily convert from re-decl to original type", sl)

	decl.receiver()
	t.Log("add receiver methods, wouldn't be possible with alias", decl)

	var alias ByteAlias = []byte{2, 2}

	tDecl := reflect.TypeOf(decl)
	tSl := reflect.TypeOf(sl)
	tAlias := reflect.TypeOf(alias)

	if tDecl == tSl {
		t.Fatal("decl should have diff type than sl")
	}

	if tAlias != tSl {
		t.Fatal("alias should have same type as sl")
	}

	/*
	   TODO: I think v1 should have a bigger size than b1.
	   After all, it's a different type, and that information should
	   take up extra space at runtime.
	   Maybe this only shows up if we create an interface that
	   accepts multiple structs like ByteDecl?
	*/
	if tDecl.Size() != tSl.Size() {
		t.Fatal("until proved wrong, they should have the same size")
	}
}
