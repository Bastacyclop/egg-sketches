#!/bin/sh
RESULTS=bench/results.csv

cargo build --release --example bench_tiling
RUN=./target/release/examples/bench_tiling

echo "search name, iteration number, physical memory, virtual memory, e-graph nodes, e-graph classes, applied rules, total time, hook time, search time, apply time, rebuild time" > ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_1d 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_2d 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_3d 2>> ${RESULTS}
sed -i '/^Running scope/d' ${RESULTS}