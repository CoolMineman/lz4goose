package main

import (
	"fmt"
	"lz4goose/rle"
)

func main() {
	a := []byte{2, 1, 3, 2}
	out := make([]byte, 10)
	b := []byte{1, 1, 2, 2, 2}
	ret := rle.DecompressRle(out, a) == uint64(len(b))
	for i := 0; i < len(b); i++ {
		if out[i] != b[i] {
			ret = false
		}
	}
	fmt.Println(ret)
	out2 := make([]byte, 10)
	out2_len, succ := rle.CompressRle(out2, b)
	ret2 := succ && out2_len == uint64(len(a))
	for i := 0; i < len(a); i++ {
		if out2[i] != a[i] {
			ret2 = false
		}
	}
	fmt.Println(out2)
	fmt.Println(ret2)
}
