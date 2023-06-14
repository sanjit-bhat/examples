package main

import (
    "fmt"
    "time"
    "sync"
)

/*
Results: make(chan int) is a blocking channel,
while make(chan int, 2) is a non-blocking channel.

Start two threads with a shared channel.
One thread immediately sends a value on the channel
and prints when it finishes.
The other thread waits for a second, reads from the channel,
and finishes.
If the first thread finishes a second before the second,
we know it didn't block until its msg was received.
If they finish at the same time, then the first thread blocked. 
*/

func sdr(ch chan int) {
    ch <- 1
    fmt.Println("sdr: done")
}

func rcvr(ch chan int) {
    time.Sleep(2 * time.Second)
    v := <- ch
    fmt.Println("rcvr: done:", v) 
}

func main() {
    fmt.Println("--- with make(chan int) ---")
    ch := make(chan int)
    var wg sync.WaitGroup
    wg.Add(2)
    go func() {
        sdr(ch)
        wg.Done()
    }()
    go func() {
        rcvr(ch)
        wg.Done()
    }()
    wg.Wait()

    fmt.Println("--- with make(chan int, 2) ---")
    ch = make(chan int, 2)
    wg.Add(2)
    go func() {
        sdr(ch)
        wg.Done()
    }()
    go func() {
        rcvr(ch)
        wg.Done()
    }()
    wg.Wait()
}
