# Zeta23 sources included here

The contour-counting proofs in this directory come from [Anthropic PBC’s Zeta23](https://github.com/anthropics/zeta-23-lean/tree/3635e74826a4c1fcece7d1cd2b6fa75e43a00510), pinned at `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`. This port takes them through Thomas Lince’s [zeta-lab](https://github.com/teal-sea/zeta-lab/tree/a401821c9608526425f3d4cf7ff8e59bc37e1c79) at `a401821c9608526425f3d4cf7ff8e59bc37e1c79`.

This checkout includes 24 selected Lean modules under `Zeta23/`, including excerpts of three modules. These imports support `RHHeight.Main`. The root Zeta23 module, Lake configuration, comparator wrappers, and upstream audit remain in their source repositories. The [source map](SOURCE_MAP.json) records the path and checksum of each selected source. See [the modification notes](MODIFICATIONS.md) for the changes to the excerpts and the Lean 4.36 port.

The files retain their original copyright notices, including the credits for PrimeNumberTheoremAnd and mathlib where applicable. The Zeta23 [Apache-2.0 license](Zeta23.LICENSE) and [notices](Zeta23.NOTICE) are included verbatim. The [historical zeta-lab provenance note](https://github.com/teal-sea/zeta-lab/blob/a401821c9608526425f3d4cf7ff8e59bc37e1c79/lean/vendor/zeta23/UPSTREAM.md) documents its earlier port and build history.
