import ninja_syntax as n
import sys
import os
import os.path as op
import io
import subprocess
from collections import defaultdict

w = n.Writer(sys.stdout, width=9999)

w.variable("ninja_dyndep_version", "1")

v_files = []
for root, dirs, files in os.walk("."):
    if str(root).startswith("./vendor/perennial/external/coqutil/etc/coq-scripts/"):
        continue
    if str(root).startswith("./vendor/goose/"):
        continue
    for filename in files:
        if filename.endswith(".v"):
            v_files.append((root, filename))
discovered_deps = defaultdict(list)
proc = subprocess.Popen(
    ["rocq", "dep", "-vos", "-f", "_CoqProject"] +
    [str(op.join(root, file)) for root, file in v_files],
    stdout=subprocess.PIPE
)
for line in io.TextIOWrapper(proc.stdout, encoding="utf-8"):
    mk_out, mk_in = line.strip().split(": ")
    mk_out, mk_in = mk_out.split(' '), mk_in.split(' ')
    for mo in mk_out:
        discovered_deps[mo] = sorted(mk_in)

def rext(s, ext, new_ext):
    return s[:len(s)-len(ext)] + new_ext

for root, filename in v_files:
    w.build(
        rule="dyndep",
        outputs=[op.join(root, rext(filename, ".v", ".vo"))],
        implicit=discovered_deps[str(op.join(root, rext(filename, ".v", ".vo")))]
    )
