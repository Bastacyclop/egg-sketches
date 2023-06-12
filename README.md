# Sketches for [egg](https://github.com/egraphs-good/egg)

[![Main branch docs](https://img.shields.io/badge/docs-main-blue)](https://bastacyclop.github.io/egg-sketches/egg_sketches)

`egg-sketches` is a library adding support for program sketches on top of the `egg` (**e**-**g**raphs **g**ood) library,
an e-graph library optimized for equality saturation.
*Sketches* are program patterns that are satisfied by a family of programs.
They can also be seen as incomplete or partial programs as they can leave details unspecified.

This library is born from our paper on [*Sketch-Guided Equality Saturation*](https://arxiv.org/abs/2111.13040),
a semi-automatic technique that allows programmers to provide program sketches to guide rewriting.

Please cite our paper if you use this repository for your research!

<details class="bibtex">
    <summary>BibTeX</summary>
    <code><pre>@article{2021-sketch-guided-eqsat,
  author    = {Thomas Koehler and
               Phil Trinder and
               Michel Steuwer},
  title     = {Sketch-Guided Equality Saturation: Scaling Equality Saturation to
               Complex Optimizations in Languages with Bindings},
  journal   = {CoRR},
  volume    = {abs/2111.13040},
  year      = {2021},
  url       = {https://arxiv.org/abs/2111.13040},
  eprinttype = {arXiv},
  eprint    = {2111.13040},
  timestamp = {Tue, 10 May 2022 15:24:30 +0200},
  biburl    = {https://dblp.org/rec/journals/corr/abs-2111-13040.bib},
  bibsource = {dblp computer science bibliography, https://dblp.org}
}
</pre></code>
</details>

## Running benchmarks

```sh
./bench/tiling.sh
./bench/math.sh
./bench/plot.sh
```
