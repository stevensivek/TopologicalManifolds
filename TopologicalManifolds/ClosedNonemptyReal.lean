/-
Copyright (c) 2025 Steven Sivek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek
-/
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Closed, nonempty subsets of ℝ

In this file we classify closed, connected, nonempty proper subsets of ℝ.

## Main results

- `realClosedNonempty` : a closed, connected, nonempty proper subset Ω ⊆ ℝ is equal
  to either `Icc (sInf Ω) (sSup Ω)` or `Ici (sInf Ω)` or `Iic (sSup Ω)`.
- `realCompactNonempty` : a compact, connected, nonempty subset Ω ⊆ ℝ is equal to
  `Icc (sInf Ω) (sSup Ω)`.
- `homeomorph_Ici_Ici_zero` : any interval of the form `Ici a` = [a,∞) is homeomorphic
  to `Ici (0 : ℝ)` = [0,∞).
- `homeomorph_Iic_Ici_zero` : any interval of the form `Iic a` = (-∞,a] is homeomorphic
  to `Ici (0 : ℝ)` = [0,∞).
- `homeomorph_Icc_unitInterval` : any interval of the form `Icc a b` = [a,b] with `a < b`
  is homeomorphic to `unitInterval` = `Icc 0 1` = [0,1].
- `homeomorph_halfSpace` : the type `EuclideanHalfSpace 1` is homeomorphic to
  `Ici (0 : ℝ)` = [0,∞).
-/

open Set Function Topology

namespace ClosedNonempty_Real

private lemma hIco : ∀ a b : ℝ, Ico a b = ∅ ∨ ¬ IsClosed (Ico a b) := by
  intro a b
  by_cases hab : a < b
  · right
    by_contra h
    apply closure_eq_iff_isClosed.mpr at h
    have : b ∈ Ico a b := by
      rw [← h, closure_Ico]
      simp only [mem_Icc, le_refl, and_true]
      exact le_of_lt hab
      exact ne_of_lt hab
    exact (notMem_Ico_of_ge (Preorder.le_refl b)) this
  · left; rw [Ico_eq_empty hab]

private lemma hIoc : ∀ a b : ℝ, Ioc a b = ∅ ∨ ¬ IsClosed (Ioc a b) := by
  intro a b
  by_cases hab : a < b
  · right
    by_contra h
    apply closure_eq_iff_isClosed.mpr at h
    have : a ∈ Ioc a b := by
      rw [← h, closure_Ioc]
      simp only [mem_Icc, le_refl, true_and]
      exact le_of_lt hab
      exact ne_of_lt hab
    exact (notMem_Ioc_of_le (Preorder.le_refl a)) this
  · left; rw [Ioc_eq_empty hab]

private lemma hIoo : ∀ a b : ℝ, Ioo a b = ∅ ∨ ¬ IsClosed (Ioo a b) := by
  intro a b
  by_cases hab : a < b
  · right
    by_contra h
    apply closure_eq_iff_isClosed.mpr at h
    have : b ∈ Ioo a b := by
      rw [← h, closure_Ioo]
      simp only [mem_Icc, le_refl, and_true]
      exact le_of_lt hab
      exact ne_of_lt hab
    exact (notMem_Ioo_of_ge (Preorder.le_refl b)) this
  · left; rw [Ioo_eq_empty hab]

private lemma hIio : ∀ a : ℝ, Iio a = ∅ ∨ ¬ IsClosed (Iio a) := by
  intro a
  right
  by_contra h
  apply closure_eq_iff_isClosed.mpr at h
  have : a ∈ Iio a := by
    rw [← h, closure_Iio]
    simp only [mem_Iic, le_refl]
  exact notMem_Iio_self this

private lemma hIoi : ∀ a : ℝ, Ioi a = ∅ ∨ ¬ IsClosed (Ioi a) := by
  intro a
  right
  by_contra h
  apply closure_eq_iff_isClosed.mpr at h
  have : a ∈ Ioi a := by
    rw [← h, closure_Ioi]
    simp only [mem_Ici, le_refl]
  exact notMem_Ioi_self this

theorem realClosedNonempty {Ω : Set ℝ} (hNonempty : Nonempty Ω) (hClosed : IsClosed Ω)
    (hConnected : IsConnected Ω) (hProperSubset : Ω ≠ univ) :
    Ω = Icc (sInf Ω) (sSup Ω) ∨ Ω = Ici (sInf Ω) ∨ Ω = Iic (sSup Ω) := by

  obtain hInt := IsPreconnected.mem_intervals (IsConnected.isPreconnected hConnected)
  simp only [mem_insert_iff, mem_singleton_iff] at hInt

  have hΩ : ¬ (Ω = ∅ ∨ ¬ IsClosed Ω) := by
    push_neg
    exact ⟨Nonempty.of_subtype, hClosed⟩

  have hNotNonClosed (s : Set ℝ) (hENC : s = ∅ ∨ ¬ IsClosed s) : Ω ≠ s := by
    by_contra h
    rw [← h] at hENC
    exact hΩ hENC
  have hNotIco : Ω ≠ Ico (sInf Ω) (sSup Ω) := by
    exact hNotNonClosed (Ico (sInf Ω) (sSup Ω)) (hIco (sInf Ω) (sSup Ω))
  have hNotIoc : Ω ≠ Ioc (sInf Ω) (sSup Ω) := by
    exact hNotNonClosed (Ioc (sInf Ω) (sSup Ω)) (hIoc (sInf Ω) (sSup Ω))
  have hNotIoo : Ω ≠ Ioo (sInf Ω) (sSup Ω) := by
    exact hNotNonClosed (Ioo (sInf Ω) (sSup Ω)) (hIoo (sInf Ω) (sSup Ω))
  have hNotIio : Ω ≠ Iio (sSup Ω) := by
    exact hNotNonClosed (Iio (sSup Ω)) (hIio (sSup Ω))
  have hNotIoi : Ω ≠ Ioi (sInf Ω) := by
    exact hNotNonClosed (Ioi (sInf Ω)) (hIoi (sInf Ω))
  have hNotEmpty : Ω ≠ ∅ := by exact nonempty_iff_ne_empty'.mp hNonempty

  simp only [hNotIco, hNotIoc, hNotIoo, hNotIio, hNotIoi, hNotEmpty, hProperSubset,
             false_or, or_false] at hInt
  exact hInt

private lemma hIciNotCompact {a : ℝ} : ¬ IsCompact (Ici a) := by
  by_contra h
  obtain ⟨x, hxIci, ⟨hxUB,_⟩⟩ := IsCompact.exists_isLUB h nonempty_Ici
  have h_gt : x + 1 > x := by
    nth_rewrite 2 [← add_zero x]
    exact (add_lt_add_iff_left x).mpr (zero_lt_one' ℝ)
  have : x + 1 ≥ a := by
    exact Preorder.le_trans a x (x + 1) hxIci (le_of_lt h_gt)
  apply (lt_self_iff_false x).mp
  exact lt_of_lt_of_le h_gt (hxUB this)

private lemma hIicNotCompact {a : ℝ} : ¬ IsCompact (Iic a) := by
  by_contra h
  obtain ⟨x, hxIic, ⟨hxLB,_⟩⟩ := IsCompact.exists_isGLB h nonempty_Iic
  have h_lt : x - 1 < x := by
    nth_rewrite 2 [← add_zero x]
    exact (add_lt_add_iff_left x).mpr neg_one_lt_zero
  have : x - 1 ≤ a := by -- x-1 ≤ x ≤ a
    exact Preorder.le_trans (x - 1) x a (le_of_lt h_lt) hxIic
  apply (lt_self_iff_false (x - 1)).mp
  exact lt_of_lt_of_le h_lt (hxLB this)

theorem realCompactNonempty {Ω : Set ℝ}
    (hNonempty : Nonempty Ω) (hCompact : IsCompact Ω) (hConnected : IsConnected Ω) :
    Ω = Icc (sInf Ω) (sSup Ω) := by
  have hNotIci : Ω ≠ Ici (sInf Ω) := by
    by_contra h; rw [h] at hCompact
    exact hIciNotCompact hCompact

  have hNotIic : Ω ≠ Iic (sSup Ω) := by
    by_contra h; rw [h] at hCompact
    exact hIicNotCompact hCompact

  have hNotUniv : Ω ≠ univ := by
    by_contra h; rw [h] at hCompact
    exact not_compactSpace_iff.mpr instNoncompactSpaceReal
          <| isCompact_univ_iff.mp hCompact

  obtain h := realClosedNonempty hNonempty (IsCompact.isClosed hCompact) hConnected hNotUniv
  simp only [hNotIci, hNotIic, or_false] at h
  exact h

end ClosedNonempty_Real


namespace ClosedInterval_homeomorph

private lemma hIci_sub (a : ℝ) (t : Ici (a : ℝ)) : t - a ∈ Ici 0 := by
    obtain ⟨x, hx⟩ := t
    have : x - a ≥ 0 := by exact sub_nonneg_of_le hx
    exact this

private lemma hIci_add (a : ℝ) (t : Ici (0 : ℝ)) : t + a ∈ Ici a := by
    obtain ⟨x, hx⟩ := t
    have : x + a ≥ a := by exact le_add_of_nonneg_left hx
    exact this

def homeomorph_Ici_Ici_zero (a : ℝ) : Homeomorph (Ici a) (Ici (0 : ℝ)) := {
  toFun : Ici a → Ici (0 : ℝ) := fun t ↦ ⟨t - a, hIci_sub a t⟩,
  invFun : Ici (0 : ℝ) → Ici a := fun t ↦ ⟨t + a, hIci_add a t⟩,
  left_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    exact eq_sub_iff_add_eq.mp rfl,
  right_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    exact sub_eq_iff_eq_add.mpr rfl,
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Continuous.add continuous_subtype_val continuous_const,
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Continuous.add continuous_subtype_val continuous_const,
}

lemma homeomorph_Ici_zero_eq_id :
    homeomorph_Ici_Ici_zero 0 = Homeomorph.refl (Ici (0 : ℝ)) := by
  ext x
  simp only [NNReal.val_eq_coe, Homeomorph.refl_apply, id_eq, NNReal.coe_inj]
  apply Subtype.mk_eq_mk.mpr
  rw [sub_zero]

lemma homeomorph_Ici_zero_eq_id_apply {x : Ici (0 : ℝ)} :
    homeomorph_Ici_Ici_zero 0 x = x := by
  simp only [homeomorph_Ici_zero_eq_id, Homeomorph.refl_apply, id_eq]

private lemma hIic_flip (a : ℝ) (t : Iic a) : - ↑t ∈ Ici (- a) := by
  obtain ⟨x, hx⟩ := t
  have : - x ≥ - a := by exact neg_le_neg_iff.mpr hx
  exact this

private lemma hIci_flip (a : ℝ) (t : Ici (-a)) : - ↑t ∈ Iic a := by
  obtain ⟨x, hx⟩ := t
  have : - x ≤ a := by exact neg_le.mp hx
  exact this

def homeomorph_Iic_flip (a : ℝ) : Homeomorph (Iic a) (Ici (-a)) := {
  toFun : Iic a → Ici (-a) := fun t ↦ ⟨- t, hIic_flip a t⟩,
  invFun : Ici (-a) → Iic a := fun t ↦ ⟨- t, hIci_flip a t⟩,
  left_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    simp only [neg_neg],
  right_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    simp only [neg_neg],
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Continuous.comp' ContinuousNeg.continuous_neg continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Continuous.comp' ContinuousNeg.continuous_neg continuous_subtype_val
}

def homeomorph_Iic_Ici_zero (a : ℝ) : Homeomorph (Iic a) (Ici (0 : ℝ)) :=
  (homeomorph_Iic_flip a).trans (homeomorph_Ici_Ici_zero (-a))

private lemma hIcc_shift_left {a b : ℝ} (t : Icc a b) : t - a ∈ Icc 0 (b - a) := by
  obtain ⟨_, hx⟩ := t
  exact ⟨sub_nonneg_of_le hx.1, tsub_le_tsub_right hx.2 a⟩

private lemma hIcc_shift_right {a b : ℝ} (t : Icc 0 (b - a)) : t + a ∈ Icc a b := by
  obtain ⟨_, hx⟩ := t
  exact ⟨le_add_of_nonneg_left hx.1, le_sub_iff_add_le.mp hx.2⟩

def homeomorph_Icc_shift (a b : ℝ) : Homeomorph (Icc a b) (Icc 0 (b - a)) := {
  toFun : Icc a b → Icc 0 (b - a) := fun t ↦ ⟨t - a, hIcc_shift_left t⟩,
  invFun : Icc 0 (b - a) → Icc a b := fun t ↦ ⟨t + a, hIcc_shift_right t⟩,
  left_inv := by exact fun x ↦ Subtype.mk_eq_mk.mpr <| sub_add_cancel ↑x a,
  right_inv := by exact fun x ↦ Subtype.mk_eq_mk.mpr <| add_sub_cancel_right ↑x a,
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Continuous.sub continuous_subtype_val continuous_const,
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Continuous.add continuous_subtype_val continuous_const,
}

private lemma hIcc_rescale_divide {a : ℝ} {ha : a > 0} (t : Icc 0 a) :
    t / a ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨x, hx⟩ := t
  have : x / a ≥ 0 := by
    rw [← zero_div a]
    exact (div_le_div_iff_of_pos_right ha).mpr hx.1
  exact ⟨this, (div_le_one₀ ha).mpr hx.2⟩

private lemma hIcc_rescale_multiply {a : ℝ} {ha : a > 0} (t : Icc (0 : ℝ) 1) :
    t * a ∈ Icc 0 a := by
  obtain ⟨x, hx⟩ := t
  exact ⟨(mul_nonneg_iff_of_pos_right ha).mpr hx.1,
         (mul_le_iff_le_one_left ha).mpr hx.2⟩

noncomputable def homeomorph_Icc_rescale {a : ℝ} (ha : a > 0) :
    Homeomorph (Icc 0 a) (Icc (0 : ℝ) 1) := {
  toFun : Icc 0 a → Icc (0 : ℝ) 1 := fun t ↦ ⟨t / a, hIcc_rescale_divide t⟩,
  invFun : Icc (0 : ℝ) 1 → Icc 0 a := fun t ↦ ⟨t * a, hIcc_rescale_multiply t⟩,
  left_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    · rw [mul_comm_div ↑x a a, div_self <| Ne.symm (ne_of_lt ha), mul_one]
    · exact (fun _ ↦ ha)
    · exact (fun _ ↦ ha),
  right_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    rw [mul_div_cancel_right₀ ↑x <| Ne.symm (ne_of_lt ha)],
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.div continuous_subtype_val continuous_const
    exact fun _ ↦ Ne.symm (ne_of_lt ha),
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Continuous.mul continuous_subtype_val continuous_const
}

noncomputable def homeomorph_Icc_unitInterval {a b : ℝ} (hab : a < b) :
    Homeomorph (Icc a b) unitInterval := by
  let f : Icc a b ≃ₜ Icc 0 (b - a) := homeomorph_Icc_shift a b
  let g : Icc 0 (b - a) ≃ₜ unitInterval := homeomorph_Icc_rescale (sub_pos.mpr hab)
  exact f.trans g

def homeomorph_halfSpace : EuclideanHalfSpace 1 ≃ₜ Ici (0 : ℝ) := {
  toFun : EuclideanHalfSpace 1 → Ici (0 : ℝ) :=
    fun t ↦ ⟨(Homeomorph.funUnique (Fin 1) ℝ) t.val, t.property⟩,
  invFun : Ici (0 : ℝ) → EuclideanHalfSpace 1 :=
    fun t ↦ ⟨(Homeomorph.funUnique (Fin 1) ℝ).symm t.val, t.property⟩,
  left_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    apply Homeomorph.symm_apply_apply (Homeomorph.funUnique (Fin 1) ℝ),
  right_inv := by
    exact fun _ ↦ Subtype.mk_eq_mk.mpr rfl,
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.comp' ?_ continuous_subtype_val
    exact Homeomorph.continuous (Homeomorph.funUnique (Fin 1) ℝ),
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.comp' ?_ continuous_subtype_val
    exact Homeomorph.continuous_symm (Homeomorph.funUnique (Fin 1) ℝ)
}

end ClosedInterval_homeomorph
