from ctypes import CDLL
import ctypes as ct

from sys import argv

sample_name = argv[1]
sample_path = argv[2]

lz4_c = CDLL("vendor/lz4/bin/lz4.so")

# LZ4LIB_API int LZ4_compress_default(const char* src, char* dst, int srcSize, int dstCapacity);
lz4_c.LZ4_compress_default.argtypes = [ct.POINTER(ct.c_char), ct.POINTER(ct.c_char), ct.c_int, ct.c_int]
lz4_c.LZ4_compress_default.restype = ct.c_int

def compress_lz4(in_py):
    in_size = len(in_py)
    in_c = (ct.c_char * in_size)()
    for i, b in enumerate(in_py):
        in_c[i] = b
    out_size = 17000000
    out_c = (ct.c_char * out_size)()
    r = lz4_c.LZ4_compress_default(in_c, out_c, in_size, out_size)
    if r == 0:
        raise "WOMP WOMP"
    return list(out_c[:r])

def write_test(name, in_bin, out_bin):
    with open(f'test_files/decompressed/{name}.bin', 'wb') as in_file:
        in_file.write(bytearray(in_bin))
    with open(f'test_files/compressed/{name}.bin', 'wb') as out_file:
        out_file.write(bytearray(out_bin))

def rocq_array(arr):
    return f"[{"; ".join(f"W8 {v}" for v in arr)}]"

def compress_gen_test(name, in_bin):
    write_test(name, in_bin, compress_lz4(in_bin))

with open(sample_path, 'rb') as file:
    compress_gen_test(sample_name, file.read())
