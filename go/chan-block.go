package main

import (
    "fmt"
    "time"
    "sync"
)

/*
Results: make(chan int) is a blocking channel,
while make(chan int, n) is a non-blocking channel.
However, once there are already n elements buffered
in the channel, it starts to block.

Start two threads with a shared channel.
One thread immediately sends a value on the channel
and prints when it finishes.
The other thread waits for a second, reads from the channel,
and finishes.
If the first thread finishes a second before the second,
we know it didn't block until its msg was received.
If they finish at the same time, then the first thread blocked. 
*/

func sdr(ch chan int, numSend int) {
    for i := 1; i <= numSend; i++ {
        ch <- i
        fmt.Println("sdr: sent:", i)
    }
    fmt.Println("sdr: done")
}

func rcvr(ch chan int, numRcv int) {
    time.Sleep(2 * time.Second)
    for i := 1; i <= numRcv; i++ {
        v := <- ch
        fmt.Println("rcvr: got:", v)
    }
    fmt.Println("rcvr: done") 
}

func main() {
    fmt.Println("--- with make(chan int), one val ---")
    time.Sleep(2 * time.Second)
    ch := make(chan int)
    var wg sync.WaitGroup
    wg.Add(2)
    go func() {
        sdr(ch, 1)
        wg.Done()
    }()
    go func() {
        rcvr(ch, 1)
        wg.Done()
    }()
    wg.Wait()

    fmt.Println("--- with make(chan int, 1), one val ---")
    time.Sleep(2 * time.Second)
    ch = make(chan int, 1)
    wg.Add(2)
    go func() {
        sdr(ch, 1)
        wg.Done()
    }()
    go func() {
        rcvr(ch, 1)
        wg.Done()
    }()
    wg.Wait()

    fmt.Println("--- with make(chan int, 1), two vals ---")
    time.Sleep(2 * time.Second)
    ch = make(chan int, 1)
    wg.Add(2)
    go func() {
        sdr(ch, 2)
        wg.Done()
    }()
    go func() {
        rcvr(ch, 2)
        wg.Done()
    }()
    wg.Wait()
}
