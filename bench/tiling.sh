#!/bin/sh
RESULTS=bench/tiling/results.csv
mkdir -p bench/tiling/

cargo build --release --example bench_tiling || exit
RUN=./target/release/examples/bench_tiling

echo "search_name, iteration_number, physical_memory, virtual_memory, e-nodes, e-classes, applied_rules, total_time, hook_time, search_time, apply_time, rebuild_time, found" > ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_1d_s 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_1d_r 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_1d 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_2d_s 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_2d_r 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_2d 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_3d_s 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_3d_r 2>> ${RESULTS}
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} tile_3d 2>> ${RESULTS}
sed -i '/^Running scope/d' ${RESULTS}
sed -i '/^Killed/d' ${RESULTS}
