package main

import (
    "fmt"
    "sync"
)

/*
Ref: https://go.dev/ref/mem.
Certain things (atomics, locks, goroutines, channels)
create synchronization points, which establish
happens-before relations at runtime, which remove data races.

racey1NoSync:
This is a data race because the write to 'a'
and the read from 'a' can happen in any order.
The race detector will pick this up.
Even with data races, Go (not C/C++) guarantees
that the read will always observe either a prior
value ("") or the written value ("hello").

notRacey1Chan:
For unbuffered channels,
the receive happens before the completion of the send.
Because it is unbuffered, the receive and send 
sync their starts.
Furthermore, by program sequencing, the assignment happens
before the send start.
Therefore, the assignment also happens before the
receive and the print.

notRacey2Locks:
Whichever Lock() runs first, it's corresponding Unlock()
happens before the other Lock().
Therefore, it's write happens before the other write,
and there are no data races.
However, there is still non-determinism in the output
because the happens-before relation is only decided at runtime.
Key point: non-det can still happen in non-racey programs.

racey1Chan:
While a channel is buffered, sends sync before recvs.
Furthermore, because it is buffered, the send and receive
starts don't need to sync.
So here, send sync, read string, write string, recv sync.
There's a data race bc read and write with no happens-before.
*/

var a1 string
func racey1NoSync() {
	go func() { a1 = "hello" }()
	fmt.Println(a1)
}

var a2 string
func notRacey1Chan() {
    ch := make(chan struct{}) 
    go func() {
        a2 = "hello"
        ch <- struct{}{}
    }()
    <-ch
    fmt.Println(a2)
}

var a3 string
func notRacey2Locks() {
    var wg sync.WaitGroup 
    var mu sync.Mutex
    wg.Add(2)
    go func() {
        mu.Lock()
        a3 = "hello"
        mu.Unlock()
        wg.Done()
    }()
    go func() {
        mu.Lock()
        a3 = "world"
        mu.Unlock()
        wg.Done()
    }()
    wg.Wait()
    fmt.Println(a3)
}

var a4 string
func racey1Chan() {
    ch := make(chan int, 1) 
    go func() {
        a4 = "hello"
        <- ch
    }()
    ch <- 0
    fmt.Println(a4)
}

func main() {
    fmt.Println("racey program, either hello or empty:")
    racey1NoSync()
    fmt.Println("not racey program, required hello:")
    notRacey1Chan()
    fmt.Println("not racey program, but still non-det:")
    notRacey2Locks()
    fmt.Println("racey program, subtle channel:")
    racey1Chan()
}
