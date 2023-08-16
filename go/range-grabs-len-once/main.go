package main

import "fmt"

func main() {
	s := []int{1, 2, 3}
	fmt.Println("len at beginning:", len(s))
	addedElems := false
	for i, a := range s {
		if !addedElems {
			s = append(s, 4)
			s = append(s, 5)
			fmt.Println("len after adding:", len(s))
			addedElems = true
		}
		fmt.Println("range read elem:", i, a)
	}
}
