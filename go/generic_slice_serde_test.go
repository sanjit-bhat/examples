package main

import (
	"github.com/tchajed/marshal"
	"testing"
)

/*
TODO: make int and slice enc themselves satisfy the interface.
*/

type BinaryAppender interface {
	AppendBinary(b []byte) []byte
}

type BinaryUnmarshaler interface {
	UnmarshalBinary(b []byte) ([]byte, bool)
}

type BinaryUnmarshalerPtr[T any] interface {
	*T
	BinaryUnmarshaler
}

type Foo struct {
	X uint64
}

func (f *Foo) AppendBinary(b []byte) []byte {
	b = marshal.WriteInt(b, f.X)
	return b
}

func (f *Foo) UnmarshalBinary(b []byte) (rem []byte, err bool) {
	rem = b
	f.X, rem, err = ReadInt(rem)
	return
}

func EncodeSlice[T BinaryAppender](b []byte, data []T) []byte {
	b = marshal.WriteInt(b, uint64(len(data)))
	for _, x := range data {
		b = x.AppendBinary(b)
	}
	return b
}

func DecodeSlice[T0 any, T1 BinaryUnmarshalerPtr[T0]](b []byte) (data []T1, rem []byte, err bool) {
	rem = b
	l, rem, err := ReadInt(rem)
	if err {
		return
	}
	data = make([]T1, l)
	for i := range data {
		data[i] = new(T0)
		rem, err = data[i].UnmarshalBinary(rem)
		if err {
			return
		}
	}
	return
}

func TestGenericSliceSerde(t *testing.T) {
	f0 := &Foo{X: 10}
	f1 := &Foo{X: 11}
	b := EncodeSlice(nil, []*Foo{f0, f1})
	d, _, err := DecodeSlice[Foo](b)
	if err {
		t.Fatal()
	}
	if len(d) != 2 || d[0].X != 10 || d[1].X != 11 {
		t.Fatal()
	}
}

func ReadInt(b []byte) (data uint64, rem []byte, err bool) {
	rem = b
	if len(rem) < 8 {
		err = true
		return
	}
	data, rem = marshal.ReadInt(rem)
	return
}
