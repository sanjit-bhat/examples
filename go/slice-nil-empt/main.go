package main

import (
	"bytes"
	"fmt"
	"reflect"
	"unsafe"
)

func main() {
	sEmpt := make([]byte, 0)
	sNil := []byte(nil)
	shEmpt := (*reflect.SliceHeader)(unsafe.Pointer(&sEmpt))
	shNil := (*reflect.SliceHeader)(unsafe.Pointer(&sNil))
	// The empt slice could have any (non-zero) data pointer
	// (presumably, any addr points to an empty array),
	// while the nil slice will have a zero (nil) data pointer.
	fmt.Printf("empt slice: %+v\n", shEmpt)
	fmt.Printf("nil slice: %+v\n", shNil)

	// As such, equality between empty slice and nil fails.
	fmt.Println("sEmpt == nil", sEmpt == nil)
	// bytes.Equal *passes*, as per its
	// [semantics.]: https://pkg.go.dev/bytes#Equal
	fmt.Println("bytes.Equal(sEmpt, sNil)", bytes.Equal(sEmpt, sNil))
	// reflect.DeepEqual fails as per its
	// [semantics.]: https://pkg.go.dev/reflect#DeepEqual
	fmt.Println("reflect.DeepEqual(sEmpt, sNil)", reflect.DeepEqual(sEmpt, sNil))
}
