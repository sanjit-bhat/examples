package main

import "time"
import "fmt"

/*
What's running:
- Both threads have a pointer to a slice,
which itself points to an underlying array.
- One thread appends a lot to the slice and re-writes the slice.
- Another thread simultaneously does a range over the
changing slice and reads the values in that range.

Behavior:
- When running them simultaneouly,
the read thread stops near the end of the array
and makes no progress.

Race condition with read thread:
- By range semantics for slices:
once at beginning, reads length and copies slice.
(https://garbagecollected.org/2017/02/22/go-range-loop-internals/)
- Occasionally the underlying array will get big
and get copied to a different one.
However, I don't think the old array will get reclaimed
since a slice to it is still stored in the range.
- This is why I'm a bit confused why it's stalling.
*/

func readSlice(s *[]int) {
    c := 0
    //fmt.Println("orig len", l)
    for idx, a := range *s {
        if idx % 1000000 == 0 {
            fmt.Println("another 1M")
        }
        c += a
    }
    fmt.Println(c)
}

func appendSlice(s *[]int) {
    for i := 0; i < 100000000; i++ {
        *s = append(*s, i)
    }
    fmt.Println("done appending")
}

func main() {
    sl := make([]int, 10)
    s := &sl
    go appendSlice(s)
    time.Sleep(time.Second)
    for i := 0; i < 100; i++ {
        fmt.Println("starting", i)
        readSlice(s)
    }
}
