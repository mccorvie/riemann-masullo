# Modifications

Changes to the Tau Ceti sources at `8794ab329bb60340fa690a2902cf995f0571721b`,
as required by section 4(b) of the Apache License 2.0.

Each Lean file keeps its original copyright, license and author header and adds a
notice with the source path, commit and pointer to this document. The `module`
headers and `public section` markers are carried over. Imports of retained Tau Ceti
modules use the vendored paths, and the upstream `TauCeti` namespace becomes
`RiemannMasullo.External.TauCeti`. Declaration names within each namespace and the
retained proof bodies are as upstream.

## `Analysis/Normed/Group/LocallyBounded.lean`

- Omit the `GeneralDomain` section, which proves
  `isLocallyBoundedOn_of_isCompact_closure_range`, and drop its
  `Mathlib.Topology.CompactOpen` import.
- Trim the module docstring to the retained predicate and API and update the declaration
  references.

## `Analysis/Complex/Conformal/NormalFamilies.lean`

- Retain the closed-ball helper and the chain of estimates through
  `IsLocallyBoundedOn.equicontinuousOn`. Omit the separate `LipschitzOnWith` form
  `lipschitzOnWith_of_forall_mem_closedBall_two_mul_norm_le`, the Cauchy kernel
  estimate `norm_inv_smul_sub_inv_smul_le`, and the derivative-family results
  `IsLocallyBoundedOn.deriv` and `IsLocallyBoundedOn.equicontinuousOn_deriv`.
- Drop `Mathlib.Topology.MetricSpace.Lipschitz`, which supplied the omitted
  `LipschitzOnWith` form.
- Trim the module docstring to the retained estimates and update its declaration and file
  references.

## `Topology/ContinuousMap/Ascoli.lean`

- Retain the section variables and
  `ArzelaAscoli.isCompact_closure_range_of_equicontinuous`, with its original
  namespace and full declaration name. The library signature comparison
  verifies that this name is a new declaration.
- Retain only the `Mathlib.Topology.UniformSpace.Ascoli` import and trim the module
  docstring to the retained result. The other compact-open results, approximation
  lemmas and periodic and Lipschitz compactness estimates are outside this excerpt.
  Neither `TauCeti.Topology.UniformSpace.Ascoli` nor `TauCeti.Algebra.Order.Floor.Ring`
  is needed.

## `Analysis/Complex/Conformal/Montel/Precompact.lean`

- Omit `isCompact_closure_range_iff_isLocallyBoundedOn` and update the module
  docstring to describe the retained implication and refer to the vendored modules.
- Update the `montel` reference in the retained declaration's docstring.

## `Analysis/Complex/Conformal/Montel/Basic.lean`

- Update the module docstring to describe the vendored compactness result and omit the
  reference to the unvendored Vitali module.
