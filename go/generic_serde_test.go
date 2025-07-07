package main

import (
	"github.com/tchajed/marshal"
	"testing"
)

// # Marshaling interfaces

type BinaryAppender interface {
	AppendBinary(b []byte) []byte
}

type BinaryUnmarshaler interface {
	UnmarshalBinary(b []byte) ([]byte, bool)
}

type Marshal[T BinaryAppender] interface {
	*T
	BinaryUnmarshaler
}

// # UInt64

type UInt64 uint64

func (i UInt64) AppendBinary(b []byte) []byte {
	b = marshal.WriteInt(b, uint64(i))
	return b
}

func (i *UInt64) UnmarshalBinary(b []byte) (rem []byte, err bool) {
	d, rem, err := ReadInt(b)
	*i = UInt64(d)
	return
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

// # Foo

type Foo struct {
	X uint64
}

func (f Foo) AppendBinary(b []byte) []byte {
	b = UInt64(f.X).AppendBinary(b)
	return b
}

func (f *Foo) UnmarshalBinary(b []byte) (rem []byte, err bool) {
	rem = b
	rem, err = (*UInt64)(&f.X).UnmarshalBinary(rem)
	return
}

// # Slice

type Slice[T0 BinaryAppender, T1 Marshal[T0]] []T0

func (s Slice[T0, T1]) AppendBinary(b []byte) []byte {
	b = UInt64(len(s)).AppendBinary(b)
	for _, x := range s {
		b = x.AppendBinary(b)
	}
	return b
}

func (s *Slice[T0, T1]) UnmarshalBinary(b []byte) (rem []byte, err bool) {
	rem = b
	l := new(UInt64)
	rem, err = l.UnmarshalBinary(b)
	if err {
		return
	}
	*s = make([]T0, uint64(*l))
	for i := range *s {
		var x T1 = &(*s)[i]
		rem, err = x.UnmarshalBinary(rem)
		if err {
			return
		}
	}
	return
}

// # Tests

func TestGenericSerde0(t *testing.T) {
	f0 := Foo{X: 10}
	f1 := Foo{X: 11}
	b := Slice[Foo, *Foo]{f0, f1}.AppendBinary(nil)
	d := new(Slice[Foo, *Foo])
	_, err := d.UnmarshalBinary(b)
	if err {
		t.Fatal()
	}
	if len(*d) != 2 || (*d)[0].X != 10 || (*d)[1].X != 11 {
		t.Fatal()
	}
}
