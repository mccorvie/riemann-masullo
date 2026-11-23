# Low zeta zeros

These modules come from Thomas Lince’s [zeta-lab](https://github.com/teal-sea/zeta-lab/tree/a401821c9608526425f3d4cf7ff8e59bc37e1c79), pinned at `a401821c9608526425f3d4cf7ff8e59bc37e1c79`. Its Hardy-function sign tests, interval enclosures and height-52 assembly are distributed under the [MIT license](LICENSE).

The contour-counting dependencies come from Anthropic PBC’s Zeta23 at `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, via zeta-lab. See the [source and scope notes](Zeta23.UPSTREAM.md), [Apache license](Zeta23.LICENSE) and [notices](Zeta23.NOTICE). The nested PrimeNumberTheoremAnd and Mathlib credits remain in their original file headers. PrimeNumberTheoremAnd is pinned there at `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`.

[SOURCE_MAP.json](SOURCE_MAP.json) identifies each selected upstream file and its SHA-256 checksum. The local port redirects imports into this directory, narrows whole-Mathlib imports and adapts proofs to the host toolchain. No authorship of the imported proofs is claimed.

[MODIFICATIONS.md](MODIFICATIONS.md) describes the local changes.
