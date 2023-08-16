package main

import (
	"fmt"
	"sync"
	"time"
)

func capture() {
	var i int
	func() {
		i += 1
	}()
	fmt.Println(i)
}

func args() {
	var i int
	func(iCopy int) {
		iCopy += 1
	}(i)
	fmt.Println(i)
}

type wrapper struct {
	wg sync.WaitGroup
}

// Note: this is caught with vet copylocks analysis
// (sync.WaitGroup contains sync.NoCopy).
// But adding here for demonstration.
// The bug: wg is passed by val instead of by ref to the goroutines.
func buggyWaitGroup() {
	n := 10
	var wg sync.WaitGroup
	wg.Add(n)
	for i := 0; i < n; i++ {
		go func(w sync.WaitGroup) {
			w.Done()
		}(wg)
	}

	t := time.NewTimer(time.Millisecond * 100)
	wgC := make(chan struct{})
	go func() {
		wg.Wait()
		var e struct{}
		wgC <- e
	}()

	select {
	case <-t.C:
		fmt.Println("bad: wg's didn't finish before timer ran out")
	case <-wgC:
		fmt.Println("good: wg's finished before timer ran out")
	}
}

func doWork(work int, realWork int) {
	if work != realWork {
		fmt.Printf("bad: got work %v, expected work %v\n", work, realWork)
	}
}

// Note: this is caught with vet loopclosure analysis.
// But adding here for demonstration.
// The bug: i is passed by ref instead of by val to the goroutines.
func buggyWorkerData() {
	n := 3
	work := make([]int, n)
	for i := 0; i < n; i++ {
		work[i] = i
	}

	var wg sync.WaitGroup
	wg.Add(n - 1)
	for i := 0; i < n-1; i++ {
		go func(j int) {
			defer wg.Done()
			time.Sleep(time.Millisecond * 10)
			doWork(work[i], j)
		}(i)
	}
	wg.Wait()
}

func main() {
	fmt.Println("captures passed by ref")
	capture()
	fmt.Println("args passed by val, along with lots of other stuff")
	args()
	buggyWorkerData()
	buggyWaitGroup()
}
