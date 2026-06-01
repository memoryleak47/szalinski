#!/bin/bash

cp "$1" src/scheduler.rs
cargo b --release
rm -rf out
make
