#![warn(missing_docs)]
/*!

`egg-sketches` is a library adding support for program sketches on top of the `egg` (**e**-**g**raphs **g**ood) library,
an e-graph library optimized for equality saturation.

*Sketches* are program patterns that are satisfied by a family of programs.
They can also be seen as incomplete or partial programs as they can leave details unspecified.

This library is born from our paper on [*Sketch-Guided Equality Saturation*](https://arxiv.org/abs/2111.13040),
a semi-automatic technique that allows programmers to provide program sketches to guide rewriting.

If you're new to `egg`,  e-graphs or equality saturation, the `egg` [tutorial](https://egraphs-good.github.io/egg/egg/tutorials/index.html) is good to get started.

To see examples of how to use this sketch libary, you can look at the [tests](https://github.com/Bastacyclop/egg-sketches/blob/main/tests) on Github.

*/

pub(crate) use egg::*;

pub mod analysis;
mod extract;
mod hashcons;
mod sketch;

pub use {
    extract::eclass_extract_sketch,
    // extract::extract_sketch,
    extract::eclass_satisfies_sketch,
    extract::satisfies_sketch,
    sketch::{Sketch, SketchNode},
};

pub(crate) type BuildHasher = fxhash::FxBuildHasher;

pub(crate) type HashMap<K, V> = hashbrown::HashMap<K, V, BuildHasher>;
pub(crate) type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;

pub(crate) type IndexMap<K, V> = indexmap::IndexMap<K, V, BuildHasher>;
pub(crate) type IndexSet<K> = indexmap::IndexSet<K, BuildHasher>;
