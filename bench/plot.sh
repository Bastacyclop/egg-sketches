#!/bin/bash

for workdir in ./bench/tiling ./bench/math
do
  python3 ./bench/plot.py $workdir
  python3 ./bench/plot_time.py $workdir
done
