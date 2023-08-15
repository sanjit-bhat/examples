package main

import (
	"fmt"
	"log"
	"sync"
	"sync/atomic"
	"time"
)

// The core of this example is from:
// https://github.com/golang/go/issues/21165#issuecomment-1622392204.
// Which is Russ Cox's example of where it's more natural to use a condvar
// than a channel, and in turn, why Go should retain condvars
// in its stdlib.

// A WorkQ is a deduplicating unbounded work queue with a fixed number of workers.
type WorkQ struct {
	mu      sync.Mutex
	queued  map[any]bool
	work    map[any]func()
	closed  bool
	ready   sync.Cond // len(w.work) > 0 || w.closed && w.running == 0
	done    int
	running int
	workers sync.WaitGroup
	start   time.Time
	next    time.Time
}

var success atomic.Uint64

const reportPeriod = 1 * time.Second

// lock locks the queue and ensures that w.ready.L is initialized.
func (w *WorkQ) lock() {
	w.mu.Lock()
	if w.queued == nil {
		w.queued = make(map[any]bool)
	}
	if w.work == nil {
		w.work = make(map[any]func())
	}
	if w.ready.L == nil {
		w.ready.L = &w.mu
	}
	if w.start.IsZero() {
		w.start = time.Now()
		w.next = w.start
	}
}

// unlock unlocks the queue and signals w.ready if a worker should be woken up.
func (w *WorkQ) unlock() {
	if len(w.work) > 0 || w.closed && w.running == 0 {
		w.ready.Signal()
	}
	w.mu.Unlock()
}

// Start starts n workers.
func (w *WorkQ) Start(n int) {
	for i := 0; i < n; i++ {
		w.workers.Add(1)
		go w.run()
	}
}

// run runs a single worker loop.
func (w *WorkQ) run() {
	defer w.workers.Done()
	w.lock()
	for {
		for len(w.work) == 0 {
			if w.closed && w.running == 0 {
				w.unlock()
				return
			}
			w.ready.Wait()
		}
		var do func()
		for name, f := range w.work {
			delete(w.work, name)
			do = f
			break
		}

		w.running++
		w.unlock()
		do()
		w.lock()
		w.running--

		w.done++
		now := time.Now()
		if now.After(w.next) {
			log.Printf("%v %d/%d done", time.Since(w.start).Round(1*time.Second), w.done, len(w.queued))
			for w.next.Before(now) {
				w.next = w.next.Add(reportPeriod)
			}
		}
	}
}

// Wait closes the work queue and waits for all work to be completed.
func (w *WorkQ) Wait() {
	w.lock()
	w.closed = true
	w.unlock()
	w.workers.Wait()
}

// Add adds work with the given name and function.
// If work with the given id has been queued before, Add does nothing.
// The id must be comparable so it can be used as a map key.
func (w *WorkQ) Add(id any, f func()) {
	w.lock()
	if !w.queued[id] {
		w.queued[id] = true
		w.work[id] = f
	}
	w.unlock()
}

func work() {
	a := 1
	b := 1
	for i := 0; i < 1000000; i++ {
		c := a + b
		a = b
		b = c
	}
	if b == -1492849609893380520 {
		success.Add(1)
	}
}

func main() {
	wq := new(WorkQ)
	ib := 10000
	jb := 10
	for i := 0; i < ib; i++ {
		for j := 0; j < jb; j++ {
			id := i*jb + j
			wq.Add(id, work)
		}
		wq.Start(jb)
	}
	wq.Wait()

	c := success.Load()
	g := ib * jb
	if c == uint64(g) {
		fmt.Println("success")
	} else {
		fmt.Printf("error: supposed to do %v work, actually did %v work\n", g, c)
	}
}
