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

// BinaryUnmarshalerPtr is a [BinaryUnmarshaler] and also a ptr to something.
// this allows slice decoding to allocate the underlying thing.
type BinaryUnmarshalerPtr[T any] interface {
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

type Slice0[T BinaryAppender] []T

func (s Slice0[T]) AppendBinary(b []byte) []byte {
	b = UInt64(len(s)).AppendBinary(b)
	for _, x := range s {
		b = x.AppendBinary(b)
	}
	return b
}

type Slice1[T0 any, T1 BinaryUnmarshalerPtr[T0]] []T1

func (s *Slice1[T0, T1]) UnmarshalBinary(b []byte) (rem []byte, err bool) {
	rem = b
	l := new(UInt64)
	rem, err = l.UnmarshalBinary(b)
	if err {
		return
	}
	*s = make([]T1, uint64(*l))
	for i := range *s {
		// allocate the underlying type T0.
		(*s)[i] = new(T0)
		rem, err = (*s)[i].UnmarshalBinary(rem)
		if err {
			return
		}
	}
	return
}

// # Test

func TestGenericSerde(t *testing.T) {
	f0 := Foo{X: 10}
	f1 := Foo{X: 11}
	b := Slice0[Foo]{f0, f1}.AppendBinary(nil)
	d := new(Slice1[Foo, *Foo])
	_, err := d.UnmarshalBinary(b)
	if err {
		t.Fatal()
	}
	if len(*d) != 2 || (*d)[0].X != 10 || (*d)[1].X != 11 {
		t.Fatal()
	}
}
