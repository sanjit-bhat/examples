package main

import "fmt"

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

func main() {
    fmt.Println("captures passed by ref")
    capture()
    fmt.Println("args passed by val, along with lots of other stuff")
    args()

}
