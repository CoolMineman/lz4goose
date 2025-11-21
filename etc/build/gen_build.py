import ninja_syntax as n
import sys
import os
import os.path as op

def rext(s, ext, new_ext):
    return s[:len(s)-len(ext)] + new_ext

w = n.Writer(sys.stdout, width=9999)

v_files = []
for root, dirs, files in os.walk("."):
    sr = str(root)
    if (
        sr.startswith("./vendor/perennial/external/coqutil/etc/coq-scripts/") or
        sr.startswith("./vendor/goose/") or
        sr.startswith("./rocq/code/") or
        sr.startswith("./rocq/generatedproof/")
    ):
        continue
    for filename in files:
        if filename.endswith(".v"):
            v_files.append(str(op.join(root, filename)))

go_files = []
go_modules = []
for root, dirs, files in os.walk("./go"):
    is_mod = False
    for filename in files:
        if filename.endswith(".go"):
            go_files.append(str(op.join(root, filename)))
            is_mod = True
    if is_mod:
        go_modules.append(str(root))

with open("_CoqProject", "r") as f:
    args = []
    for l in f:
        l = l.strip()
        if not l or l[0] == '#':
            continue
        args.append(l.replace("-arg ", ""))
    w.variable("rocq_args", args)
w.newline()

w.rule(
    "goose",
    "cd ./vendor/goose/ && go run ./cmd/goose/main.go -out ../../rocq/code -dir ../../go ./... && cd ../..",
    description="GOOSE",
    restat=True
)
goose_outputs = ["./rocq/code/lz4goose/" + go_mod.removeprefix("./go/") + ".v" for go_mod in go_modules]
w.build(
    rule="goose",
    outputs=[],
    implicit=go_files,
    implicit_outputs=goose_outputs,
)
w.rule(
    "proofgen",
    "cd ./vendor/goose/ && go run ./cmd/proofgen/main.go -out ../../rocq/generatedproof -configdir ../../rocq/code -dir ../../go ./... && cd ../..",
    description="PROOFGEN",
    restat=True
)
proofgen_outputs = ["./rocq/generatedproof/lz4goose/" + go_mod.removeprefix("./go/") + ".v" for go_mod in go_modules]
w.build(
    rule="proofgen",
    outputs=[],
    implicit=go_files,
    implicit_outputs=proofgen_outputs,
)
w.newline()
all_v_files = v_files + goose_outputs + proofgen_outputs
w.rule(
    "rocq_vo",
    "rocq compile $rocq_args -noglob $in -o $out",
    description="ROCQC $in"
)
w.newline()
w.rule(
    "get_rocq_deps",
    "python etc/build/gen_deps.py | $out",
    description="ROCQ DEP"
)
w.build(
    rule="get_rocq_deps",
    outputs="etc/build/.rocqdeps",
    implicit=all_v_files,
    order_only=[
        "etc/build/gen/.goose",
        "etc/build/gen/.proofgen"
    ]
)
w.newline()

for v_file in all_v_files:
    w.build(
        rule="rocq_vo",
        inputs=[v_file],
        outputs=[rext(v_file, ".v", ".vo")],
        dyndep="etc/build/.rocqdeps"
    )
for v_file in all_v_files:
    if v_file.startswith("./rocq/"):
        w.default(rext(v_file, ".v", ".vo"))
