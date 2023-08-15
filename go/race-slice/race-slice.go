package main

import (
    "fmt"
    "sync"
)

/*
sliceCopyRace:
Concurrent reads and writes to a slice reference is a data race.

sliceCopyNoRace:
To prevent the race, lock both reads and writes.

arrReadNoRace:
Do the prev fix of locking the slice read
and making a new slice copy.
Now, concurrent reads to the underlying array
with potential re-sizing does not trigger
the race detector.
I'm not sure if it's actually a race, though.
*/

func sliceCopyRace() {
    sl := make([]int, 1)
    var wg sync.WaitGroup
    wg.Add(2)
    go func() {
        for i := 0; i < 1e6; i++ {
            sl2 := sl
            _ = sl2
            // Anything that triggers a slice read,
            // including len(), also works.
            // l := len(sl)
            // l += 1
        }
        wg.Done() 
    }()
    go func() {
        // Had to unroll the normal loop syntax to get the race
        // detector to actually find the append write.
        i := 0
        for {
            if !(i < 1e6) {
                break
            }
            sl = append(sl, i)
            i += 1
        }
        wg.Done()
    }()
    wg.Wait()
}

func sliceCopyNoRace() {
    sl := make([]int, 1)
    var wg sync.WaitGroup
    wg.Add(2)
    var mu sync.Mutex
    go func() {
        for i := 0; i < 1e6; i++ {
            mu.Lock()
            sl2 := sl
            _ = sl2
            mu.Unlock()
        }
        wg.Done()
    }()
    go func() {
        i := 0
        for {
            if !(i < 1e6) {
                break
            }
            mu.Lock()
            sl = append(sl, i)
            mu.Unlock()
            i += 1
        }
        wg.Done()
    }()
    wg.Wait()
}

func arrReadNoRace() {
    sl := make([]int, 1)
    var wg sync.WaitGroup
    wg.Add(2)
    var mu sync.Mutex
    go func() {
        // The iterations aren't necessary
        // to trigger the data race without locks.
        // However, I wanted as many reads as possible
        // so that if a race existed with reading,
        // the race detector would find it.
        for iter := 0; iter < 1000; iter++ {
            // Removing these locks creates a data race.
            mu.Lock()
            slCopy := sl
            mu.Unlock()
            c := 0
            for i := 0; i < len(slCopy); i++ {
                c += slCopy[i]
            }
        }
        wg.Done()
    }()
    go func() {
        i := 0
        for {
            if !(i < 1e8) {
                break
            }
            mu.Lock()
            sl = append(sl, i)
            mu.Unlock()
            i += 1
        }
        wg.Done()
    }()
    wg.Wait()
}

func main() {
    fmt.Println("sliceCopyRace")
    sliceCopyRace()
    fmt.Println("sliceCopyNoRace")
    sliceCopyNoRace()
    fmt.Println("arrReadNoRace")
    arrReadNoRace()
}
