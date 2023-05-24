#!/bin/sh
systemd-run --scope -p MemoryLimit=10G -- cargo run --release --example bench_tiling