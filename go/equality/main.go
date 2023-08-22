package main

import (
	"fmt"
	"reflect"

	"github.com/google/go-cmp/cmp"
)

type S1 struct {
	data uint64
}

func exUint() {
	s1 := S1{5}
	s2 := s1

	fmt.Println("s1 == s2", s1 == s2)
	fmt.Println("s1.data == s2.data", s1.data == s2.data)
}

type S2 struct {
	data []byte
}

func exSliceReflect() {
	s1 := S2{make([]byte, 1)}
	s2 := s1

	// s1 == s1 and s1.data == s2.data both don't work because
	// equality in the "==" sense is not defined on slices
	// (and therefore structs containing slices).

	fmt.Println("reflect.DeepEqual(s1, s2)", reflect.DeepEqual(s1, s2))
}

func exSliceModReflect() {
	s1 := S2{make([]byte, 1)}
	s2 := s1
	s2.data = make([]byte, 1)

	// Should return true because reflect.DeepEqual
	// allows for slice equality by element equality.
	fmt.Println("reflect.DeepEqual(s1, s2)", reflect.DeepEqual(s1, s2))
}

// Equality of S2 based on pointer equality (not element value equality).
func (s S2) Equal(o S2) bool {
	sData := s.data
	oData := o.data
	sLen0 := len(sData) == 0
	oLen0 := len(oData) == 0
	lenEq := len(sData) == len(oData)
	capEq := cap(sData) == cap(oData)
	lenAndCapEq := lenEq && capEq
	if sLen0 || oLen0 {
		return lenAndCapEq
	}
	// This needs to come after checking if they have 0 len.
	ptrsEq := &sData[0] == &oData[0]
	return ptrsEq && lenAndCapEq
}

func exSliceModCmp() {
	s1 := S2{make([]byte, 1)}
	s2 := s1
	s2.data = make([]byte, 1)

	// Should return false because cmp.Equal uses our Equal func,
	// which doesn't do element value equality.
	fmt.Println("cmp.Equal(s1, s2)", cmp.Equal(s1, s2))
}

func main() {
	fmt.Println("exUint")
	exUint()
	fmt.Println("exSliceReflect")
	exSliceReflect()
	fmt.Println("exSliceModReflect")
	exSliceModReflect()
	fmt.Println("exSliceModCmp")
	exSliceModCmp()
}
