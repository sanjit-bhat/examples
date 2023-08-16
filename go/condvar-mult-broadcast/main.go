package main

import (
	"fmt"
	"sync"
)

func child(done *int, mu *sync.Mutex, cv *sync.Cond) {
	mu.Lock()
	*done += 1
	cv.Broadcast()
	mu.Unlock()
}

func main() {
	mu := sync.Mutex{}
	cv := sync.Cond{L: &mu}
	done := 0

	go child(&done, &mu, &cv)
	mu.Lock()
	for done != 1 {
		cv.Wait()
	}
	mu.Unlock()

	go child(&done, &mu, &cv)
	mu.Lock()
	for done != 2 {
		cv.Wait()
	}
	mu.Unlock()

	if done == 2 {
		fmt.Println("correctly ran child thread before parent")
	} else {
		fmt.Println("something went wrong")
	}
}
