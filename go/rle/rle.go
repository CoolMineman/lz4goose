package rle

func DecompressRle(dst []byte, src []byte) uint64 {
	out := uint64(0)
	for i := uint64(0); i < uint64(len(src)); i += 2 {
		runlen := src[i]
		val := src[i+1]
		for j := uint64(0); j < uint64(runlen); j++ {
			dst[out] = val
			out += 1
		}
	}
	return out
}

func CompressRle(dst []byte, src []byte) (uint64, bool) {
	out := uint64(0)
	for i := uint64(0); i < uint64(len(src)); {
		v := src[i]
		j := i + 1
		for j < uint64(len(src)) && v == src[j] && j-i < 255 {
			j++
		}
		if out+2 >= uint64(len(dst)) {
			return 0, false
		}
		dst[out] = byte(j - i)
		dst[out+1] = v
		i = j
		out += 2
	}
	return out, true
}
