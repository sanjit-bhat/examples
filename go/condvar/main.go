package main

import (
	"fmt"
	"sync"
)

func child(done *bool, mu *sync.Mutex, cv *sync.Cond) {
	mu.Lock()
	*done = true
	cv.Signal()
	mu.Unlock()
}

func main() {
	mu := sync.Mutex{}
	cv := sync.Cond{L: &mu}
	done := false

	go child(&done, &mu, &cv)

	mu.Lock()
	for !done {
		cv.Wait()
	}
	mu.Unlock()

	if done {
		fmt.Println("correctly ran child thread before parent")
	} else {
		fmt.Println("something went wrong")
	}
}
