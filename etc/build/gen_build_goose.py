import ninja_syntax as n
import sys
import os
import os.path as op
import io
import subprocess
from collections import defaultdict

w = n.Writer(sys.stdout, width=9999)

go_files = []
for root, dirs, files in os.walk("../../go"):
    for filename in files:
        go_files.append(str(op.join(root, filename)))

w.rule("goose", "cd ../../vendor/goose/ && go run ./cmd/goose/main.go -out ../../rocq/code -dir ../../go ./... && touch ../../etc/build/gen/.goose_build")
w.build(
    rule="goose",
    outputs="gen/.goose_build",
    inputs=go_files,
)

w.rule("proofgen", "cd ../../vendor/goose/ && go run ./cmd/proofgen/main.go -out ../../rocq/generatedproof -configdir ../../rocq/code -dir ../../go ./... && touch ../../etc/build/gen/.proofgen_build")
w.build(
    rule="proofgen",
    outputs="gen/.proofgen_build",
    inputs=['gen/.goose_build'] + go_files,
)