# Sketches for [egg](https://github.com/egraphs-good/egg)

[![Main branch docs](https://img.shields.io/badge/docs-main-blue)](https://bastacyclop.github.io/egg-sketches/egg_sketches)

`egg-sketches` is a library adding support for program sketches on top of the `egg` (**e**-**g**raphs **g**ood) library,
an e-graph library optimized for equality saturation.
*Sketches* are program patterns that are satisfied by a family of programs.
They can also be seen as incomplete or partial programs as they can leave details unspecified.

This library is born from our paper on [*Guided Equality Saturation*](https://doi.org/10.1145/3632900),
a semi-automatic technique that allows programmers to guide rewriting with, for example, program sketches.

Please cite our paper if you use this repository for your research!

<details class="bibtex">
    <summary>BibTeX</summary>
    <code><pre>@article{2024-guided-eqsat,
author = {Koehler, Thomas and Goens, Andr\'{e}s and Bhat, Siddharth and Grosser, Tobias and Trinder, Phil and Steuwer, Michel},
title = {Guided Equality Saturation},
year = {2024},
issue_date = {January 2024},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
volume = {8},
number = {POPL},
url = {https://doi.org/10.1145/3632900},
doi = {10.1145/3632900},
journal = {Proc. ACM Program. Lang.},
month = {jan},
articleno = {58},
numpages = {32},
keywords = {theorem provers, e-graphs, equality saturation, optimizing compilers}
}
</pre></code>
</details>
