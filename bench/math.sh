#!/bin/sh
RESULTS=bench/math/results.csv
mkdir -p bench/math/

cargo build --release --example bench_math_sketch || exit
RUN=./target/release/examples/bench_math_sketch

echo "search_name, iteration_number, physical_memory, virtual_memory, e-nodes, e-classes, applied_rules, total_time, hook_time, search_time, apply_time, rebuild_time, found" > ${RESULTS}
for i in `seq 0 3`; do
  sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} binomial4 ${i} 2>> ${RESULTS}
done
sudo systemd-run --scope -p MemoryLimit=10G -- ${RUN} binomial4 2>> ${RESULTS}

sed -i '/^Running scope/d' ${RESULTS}
sed -i '/^Killed/d' ${RESULTS}
