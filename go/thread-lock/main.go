package main

import (
    "fmt"
    "sync"
)

/*
First thread locks.
Second thread unlocks.
Third thread locks. It should be able to lock.

This demonstrates that to Unlock,
you need not be on the same thread that Lock'd.
*/

func main() {
    var mu sync.Mutex
    oneDone := make(chan struct{}, 1)
    twoDone := make(chan struct{}, 1)
    threeDone := make(chan struct{}, 1)

    go func() {
        mu.Lock()
        oneDone <- struct{}{}
    }()
    go func() {
        <-oneDone
        mu.Unlock()
        twoDone <- struct{}{}
    }()
    go func() {
        <-twoDone
        mu.Lock()
        threeDone <- struct{}{}
    }()

    <-threeDone
    fmt.Println("success")
}
