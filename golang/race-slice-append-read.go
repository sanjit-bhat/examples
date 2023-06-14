package main

import (
    "fmt"
    "time"
)

/*
Update:
- This doesn't happen anymore once I switched from amd64 to arm64.
Must've been running slower on my M1 and triggering
some extra behavior.

What's running:
- Both threads have a pointer to a slice,
which itself points to an underlying array.
- One thread appends a lot to the slice and re-writes the slice.
- Another thread simultaneously does a range over the
changing slice and reads the values in that range.

Behavior:
- When running them simultaneously,
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
    fmt.Println("read: starting")
    c := 0
    fmt.Println("read: orig len:", len(*s))
    for idx, a := range *s {
        if idx % 1e6 == 0 {
            fmt.Println("read: processed another 1M")
        }
        c += a
    }
    fmt.Println("read: done:", c)
}

func appendSlice(s *[]int) {
    fmt.Println("append: starting")
    for i := 0; i < 1e7; i++ {
        *s = append(*s, i)
    }
    fmt.Println("append: done")
}

func main() {
    sl := make([]int, 10)
    s := &sl
    go appendSlice(s)
    time.Sleep(time.Second)
    readSlice(s)
}
