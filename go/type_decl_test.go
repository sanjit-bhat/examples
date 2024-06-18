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
This fails since you can't add methods to built-in types.
func (b ByteAlias) receiver() {
    b[0] = 4
}
*/

func fooSlByte(o []byte) {}

type byteDecl byte

func fooByte(o byte) {}

type slIntDecl []int

func fooSlInt(o []int) {}

type mapDecl map[int]int

func fooMap(o map[int]int) {}

func TestTypeDecl(t *testing.T) {
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

	t.Log("for some reason, need to cast with primitive re-decl but not with slice/map re-decl")
	fooSlByte(decl)
	var bDecl byteDecl
	fooByte(byte(bDecl))
	var slIDecl slIntDecl
	fooSlInt(slIDecl)
	var mDecl mapDecl
	fooMap(mDecl)
}
