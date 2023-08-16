package main

import (
	"errors"
	"io"
	"log"
	"net"
	"os"
	"os/signal"
	"runtime/pprof"
	"strings"
	"sync"
	"syscall"
	"time"

	"golang.org/x/sync/errgroup"
)

func oneReq(conn net.Conn) error {
    b := []byte("hello\n")
    _, err := conn.Write(b)
    if err != nil {
        return err
    }
    b = make([]byte, 1024)
    n, err := conn.Read(b)
    if err != nil {
        return err
    }
    s := string(b[:n])
    if s != "hello server\n" {
        log.Printf("got %v from server\n", s)
        return errors.New("server wrong ret val")
    }
    return nil
}

const port = ":1234"

func client() error {
    conn, err := net.Dial("tcp", port)
    defer conn.Close()
    if err != nil {
        return err
    }
    n := 100
    for i := 0; i < n; i++ {
        // TODO: Investigate why if I parallelize oneReq,
        // the oneReq string equality checks start to fail.
        if err := oneReq(conn); err != nil {
            return err
        }
    }
    return nil
}

func clients() {
    n := 100
    g := new(errgroup.Group)
    for i := 0; i < n; i++ {
        g.Go(client)
    }
    if err := g.Wait(); err == nil {
        log.Println("client success")
    } else {
        log.Println("client failure", err)
    }
}

func writeResp(conn net.Conn, s string) error {
    b := []byte(s + " server\n")
    _, err := conn.Write(b)
    return err
}

func handleConn(conn net.Conn) error {
    // Could read lines with Scanner, but I want to do this at a lower
    // level of abstraction to learn the most.
    for {
        b := make([]byte, 1024)
        n, err := conn.Read(b)
        s := string(b[:n])
        if strings.HasSuffix(s, "\n") {
            if err2 := writeResp(conn, strings.TrimSuffix(s, "\n")); err2 != nil {
                return err2
            }
        }
        if errors.Is(err, io.EOF) {
            return nil
        } else if err != nil {
            return err
        }
    }
}

type notifT struct{}

// We need this because "net" doesn't have any support
// for threading a ctx all the way through listener.Accept() calls.
// There is a ListenConfig.Listen(ctx), but that subtly only
// uses the context for addr resolution, not subsequent listen ops. 
// See this open issue for the ListenConfig subtlety:
// [issue]: https://github.com/golang/go/issues/50861.
func stopLn(ln net.Listener, cancel chan notifT) {
    time.Sleep(time.Second*2)
    close(cancel)
    ln.Close()
}

func server() {
    ln, err := net.Listen("tcp", port)
    if err != nil {
        log.Fatalln("server failure", err)
    }

    g := new(errgroup.Group)
    cancel := make(chan notifT, 1)
    g.Go(func() error {
        stopLn(ln, cancel)
        return nil
    })

    for {
        conn, err := ln.Accept()
        if err != nil {
            select {
            case <-cancel:
                // Break terminates innermost for, switch, or select.
                // so need additional break (below) or break labels.
                break
            default:
                log.Fatalln("server failure", err)
            }
            break
        }
        g.Go(func() error {
            return handleConn(conn)
        })
    }
    if err := g.Wait(); err == nil {
        log.Println("server success")
    } else {
        log.Println("server failure", err)
    }
}

// Used for debugging deadlocks.
func dumpStacks(sigs chan os.Signal) {
    <-sigs
    // pprof.Lookup has other options like heap, threadcreate, block:
    // [docs]: https://pkg.go.dev/runtime/pprof.
    pprof.Lookup("goroutine").WriteTo(os.Stderr, 1)
    signal.Reset()
    syscall.Kill(syscall.Getpid(), syscall.SIGINT) 
}

func main() {
    sigs := make(chan os.Signal, 1)
    signal.Notify(sigs, syscall.SIGINT)
    go func() {
        dumpStacks(sigs)
    }()

    var wg sync.WaitGroup
    wg.Add(2)
    go func() {
        defer wg.Done()
        server()
    }()
    time.Sleep(time.Millisecond*50)
    go func() {
        defer wg.Done()
        clients()
    }()
    wg.Wait()
}
