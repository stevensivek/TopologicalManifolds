# Topological manifolds in Lean

This repository contains code for studying topological manifolds in Lean.  It includes some of the following:

* A new HasInvarianceOfDomain class, and a proof that `EuclideanSpace ℝ (Fin 1)` belongs to it.
* Theorems asserting that a ModelWithCorners whose underlying space has invariance of domain behaves as expected: the boundary and interior of a manifold are well-defined, are closed and open respectively, can be detected by any choice of charts, etc.
* Proofs that pushouts in `TopCat` are well-behaved and preserve key properties like IsEmbedding.
* Gluing constructions for a pair of spaces equipped with homeomorphic subsets of each, with Double and Completion as special cases.
* Proofs that a space has double `ℝ` or `𝕊¹` iff that space is either `[0,∞)` or the unit interval `[0,1]`, respectively.

The constructions on Gluing.lean (and consequently Double1.lean) currently seem to require the declaration of a universe because `TopCat` does, but ideally this dependence will be removed at some point.
