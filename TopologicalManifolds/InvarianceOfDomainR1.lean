/-
Copyright (c) 2025 Steven Sivek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek
-/
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import «TopologicalManifolds».InvarianceOfDomain

open Set Function Topology Manifold ModelWithCorners

/-!
# Invariance of domain for ℝ

In this file we prove that both ℝ and the homeomorphic `EuclideanSpace ℝ (Fin 1)`
satisfy invariance of domain: a continuous `PartialEquiv` takes neighborhoods of
a point in its source to neighborhoods of its image.

## Main results

- `instHasInvarianceOfDomain_Real` : `ℝ` has invariance of domain.
- `instHasInvarianceOfDomain_R1` : the 1-dimensional Euclidean space
  `EuclideanSpace ℝ (Fin 1)` = ℝ¹ has invariance of domain.
-/

namespace InvarianceOfDomain

theorem invariance_of_domain_Real
    {x : ℝ} {s : Set ℝ} {f : PartialEquiv ℝ ℝ} (hfCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x) := by
  intro h hfSource
  simp only [mem_nhds_iff] at h
  obtain ⟨t, hts, htOpen, htx⟩ := h
  obtain ⟨u, huRb, hxu, hut⟩ := by
    exact Real.isTopologicalBasis_Ioo_rat.isOpen_iff.mp htOpen x htx
  simp only [mem_iUnion, mem_singleton_iff, exists_prop] at huRb
  obtain ⟨a, b, hab, huIoo⟩ := huRb
  rw [huIoo] at hxu
  obtain ⟨c, hc⟩ := by exact exists_between hxu.1
  obtain ⟨d, hd⟩ := by exact exists_between hxu.2
  have hxcd : x ∈ Ioo c d := by
    simp only [mem_Ioo]
    exact ⟨by linarith, by linarith⟩

  have hfSource' : Icc c d ⊆ s := calc
    Icc c d ⊆ Ioo a b := by exact Icc_subset_Ioo hc.1 hd.2
    _ ⊆ t             := by rwa [← huIoo]
    _ ⊆ s             := by exact hts
  replace hfSource : Icc c d ⊆ f.source := calc
    Icc c d ⊆ s  := by exact hfSource'
    _ ⊆ f.source := by exact hfSource
  have hfInj : InjOn f (Icc c d) := by
    exact f.injOn.mono hfSource
  replace hfCont : ContinuousOn f (Icc c d) := by
    exact hfCont.mono hfSource

  cases (hfCont.strictMonoOn_of_injOn_Icc' (by linarith) hfInj) with
  | inl h => -- strictly monotone
    have : Icc (f c) (f d) ∈ nhds (f x) := by
      apply Icc_mem_nhds
      · refine (h.lt_iff_lt ?_ (mem_Icc_of_Ioo hxcd)).mpr hc.2
        simp only [mem_Icc, le_refl, true_and]
        linarith
      · refine (h.lt_iff_lt (mem_Icc_of_Ioo hxcd) ?_).mpr hd.1
        simp only [mem_Icc, le_refl, and_true]
        linarith
    rw [← hfCont.image_Icc_of_monotoneOn (by linarith) h.monotoneOn] at this
    exact Filter.mem_of_superset this (monotone_image hfSource')
  | inr h => -- strictly antitone
    have : Icc (f d) (f c) ∈ nhds (f x) := by
      apply Icc_mem_nhds
      · refine (h.lt_iff_gt ?_ (mem_Icc_of_Ioo hxcd)).mpr hd.1
        simp only [mem_Icc, le_refl, and_true]
        linarith
      · refine (h.lt_iff_gt (mem_Icc_of_Ioo hxcd) ?_).mpr hc.2
        simp only [mem_Icc, le_refl, true_and]
        linarith
    rw [← hfCont.image_Icc_of_antitoneOn (by linarith) h.antitoneOn] at this
    exact Filter.mem_of_superset this <| monotone_image hfSource'

instance instHasInvarianceOfDomain_Real : HasInvarianceOfDomain ℝ where
  invariance_of_domain := invariance_of_domain_Real

instance instHasInvarianceOfDomain_R1 :
    HasInvarianceOfDomain (EuclideanSpace ℝ (Fin 1)) := by
  exact HasInvarianceOfDomain_from_homeomorph <| Homeomorph.funUnique (Fin 1) ℝ

end InvarianceOfDomain
