#!/bin/bash

rm -rf out outfile outfile.eval

cp "$1" src/scheduler.rs
cargo b --release
make |& tee outfile
python eval.py outfile > outfile.eval
