/-
Copyright (c) 2025 Steven Sivek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek
-/
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Star.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import «TopologicalManifolds».InvarianceOfDomainR1
import «TopologicalManifolds».ClosedNonemptyReal
import «TopologicalManifolds».Gluing

/-!
# Doubles of 1-manifolds

In this file we prove some results about doubles of 1-manifolds with boundary.  Here M is
understood to be a 1-manifold with boundary if it is an instance of
`ChartedSpace (EuclideanHalfSpace 1) M`.

## Main results

- `double_halfInterval`: the double of `EuclideanHalfSpace 1` is homeomorphic
  to `EuclideanSpace ℝ (Fin 1)` = ℝ¹.
- `double_is_R`: if the double of `M` is homeomorphic to `ℝ`, then `M` is
  homeomorphic to `Ici (0 : ℝ)` = [0,∞).
- `double_is_R_iff` : the double of `M` is homeomorphic to `ℝ` if and only if
  `M` is homeomorphic to `Ici (0 : ℝ)` = [0,∞).
- `double_unitInterval`: the double of `unitInterval` = [0,1] is homeomorphic
  to `Circle` = 𝕊¹.
- `double_is_circle`: if the double of `M` is homeomorphic to `Circle` = 𝕊¹,
  then `M` is homeomorphic to `unitInterval` = [0,1].
- `double_is_circle_iff` : the double of `M` is homeomorphic to `Circle` = 𝕊¹
  if and only if `M` is homeomorphic to `unitInterval` = [0,1].
-/

open Set Function Manifold Topology

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

namespace DoubleInterval
open Gluing Double ComplexConjugate TopCat

theorem double_halfInterval : Nonempty (double (𝓡∂ 1) (EuclideanHalfSpace 1) ≃ₜ ℝ¹) := by
  let H := EuclideanHalfSpace 1
  let φ : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have hφ {t : ℝ¹} : φ t = t 0 := by exact rfl

  let f₀ : H → ℝ := fun t ↦ φ t.val
  have hfCont : Continuous f₀ := by
    apply Continuous.comp (Homeomorph.continuous φ)
    exact continuous_iff_le_induced.mpr fun _ a ↦ a
  let f : C(H, ℝ) := ⟨f₀, hfCont⟩

  have hfClosed : IsClosedMap f := by
    apply IsClosedMap.comp (Homeomorph.isClosedMap φ)
    apply IsClosed.isClosedMap_subtype_val
    have : IsClosed (Subtype.val '' (@univ H)) := by
      simp only [Fin.isValue, image_univ, Subtype.range_coe_subtype]
      have : IsClosed {x : ℝ¹ | 0 ≤ φ x} := by
        rw [show {x : ℝ¹ | 0 ≤ φ x} = φ ⁻¹' (Ici (0 : ℝ)) by rfl]
        exact IsClosed.preimage (Homeomorph.continuous φ) isClosed_Ici
      exact this
    simp_all only [Fin.isValue, image_univ, Subtype.range_coe_subtype]
    exact this

  let g₀ : H → ℝ := fun t ↦ - (φ t.val)
  let g : C(H, ℝ) := ⟨g₀, Continuous.neg hfCont⟩

  have hgClosed : IsClosedMap g := by
    exact IsClosedMap.comp (g := fun x ↦ - x) (isClosedMap_neg ℝ) hfClosed

  haveI : f 0 = g 0 := by
    rw [show f 0 = 0 by exact rfl, show g 0 = - 0 by exact rfl]
    exact zero_eq_neg.mpr rfl

  have bdryH : (𝓡∂ 1).boundary H = {0} := by
    haveI : frontier (range (𝓡∂ 1)) = {y : ℝ¹ | (0 : ℝ) = y 0} := by
      exact frontier_range_modelWithCornersEuclideanHalfSpace 1
    ext x
    apply Iff.trans ModelWithCorners.isBoundaryPoint_iff
    rw [extChartAt_coe x, chartAt_self_eq, PartialHomeomorph.refl_apply]
    simp_all only [mem_singleton_iff, Function.comp_apply, id_eq, mem_setOf_eq]
    constructor <;> intro hx
    · apply EuclideanHalfSpace.ext_iff.mpr
      rw [show (𝓡∂ 1) x 0 = x.val 0 by exact rfl] at hx
      exact (show x.val = φ.symm 0 by exact EquivLike.inv_apply_eq.mp (Eq.symm hx))
    · apply EuclideanHalfSpace.ext_iff.mp at hx
      rw [show (𝓡∂ 1) x 0 = x.val 0 by exact rfl, hx]
      rfl

  have w : CategoryTheory.CategoryStruct.comp (bdry_inc' (𝓡∂ 1) H) (TopCat.ofHom f) =
           CategoryTheory.CategoryStruct.comp (bdry_inc' (𝓡∂ 1) H) (TopCat.ofHom g) := by
    ext x
    simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply]
    rw [show (bdry_inc' (𝓡∂ 1) H) x = ↑x by exact rfl]
    simp_all only [Fin.isValue, ContinuousMap.coe_mk, φ, f, f₀, g, g₀]
    have hx : x.val = (0 : H) := by
      apply eq_of_mem_singleton
      rw [← bdryH]
      exact Subtype.coe_prop x
    rwa [hx]

  let ψ : double (𝓡∂ 1) H ⟶ (TopCat.of ℝ) :=
    double.desc (𝓡∂ 1) H f g w

  have hInjective : Injective ψ := by
    have hInjf : Injective f := by
      intro s t hst
      simp_all only [Fin.isValue, ContinuousMap.coe_mk, φ, H, f, f₀]
      apply EuclideanHalfSpace.ext
      apply PiLp.ext
      intro i
      rwa [Fin.fin_one_eq_zero i]
    have hInjg : Injective g := by
      intro s t hst
      have : f s = f t := by
        simp_all only [Fin.isValue, ContinuousMap.coe_mk, neg_inj, φ, H, f, f₀, g, g₀]
      exact hInjf this
    apply desc_injective_double (X := TopCat.of ℝ) (h := f) (k := g) (𝓡∂ 1) H w hInjf hInjg
    intro y z hyz
    rw [bdryH]
    simp only [mem_singleton_iff]
    haveI : f y ≥ 0 := by exact Subtype.coe_prop y
    haveI : f y ≤ 0 := by
      rw [hyz, show g z = - f z by exact rfl]
      simp only [Left.neg_nonpos_iff]
      exact Subtype.coe_prop z
    have : f y = 0 := by linarith
    exact hInjf this

  have hSurjective : Surjective ψ := by
    apply desc_surjective_double (X := TopCat.of ℝ) (𝓡∂ 1) H f g w
    apply univ_subset_iff.mp
    intro x _
    apply (mem_union x (range f) (range g)).mpr
    simp only [mem_range]
    by_cases hx : x ≥ 0
    · left
      use ⟨(φ.symm x), hx⟩
      exact hφ
    · right
      replace hx : - x > 0 := by exact Left.neg_pos_iff.mpr (lt_of_not_ge hx)
      let y : H := ⟨φ.symm (- x), le_of_lt hx⟩
      use y
      apply neg_inj.mp
      rw [show - g y = f y by exact neg_eq_iff_eq_neg.mpr rfl]
      exact hφ

  have hBijective : Bijective ψ := by exact ⟨hInjective, hSurjective⟩
  have hContinuous : Continuous ψ := by exact ContinuousMap.continuous (TopCat.Hom.hom ψ)

  have hClosed : IsClosedMap ψ := by
    exact desc_isClosedMap_double (X := TopCat.of ℝ) (𝓡∂ 1) H f g w hfClosed hgClosed

  have ψ₀ : (double (𝓡∂ 1) H) ≃ₜ ℝ := Equiv.toHomeomorphOfContinuousClosed
                                      (Equiv.ofBijective ψ hBijective) hContinuous hClosed
  exact Nonempty.intro (ψ₀.trans φ.symm)

theorem double_is_R
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
    (hDouble : Nonempty ((double (𝓡∂ 1) M) ≃ₜ ℝ)) :
    Nonempty (M ≃ₜ Ici (0 : ℝ)) := by

  have hConnectedDouble : ConnectedSpace (double (𝓡∂ 1) M) := by
    apply connectedSpace_iff_univ.mpr
    let ψ : ℝ ≃ₜ double (𝓡∂ 1) M := hDouble.some.symm
    rw [← EquivLike.range_eq_univ ψ, ← image_univ]
    exact (Homeomorph.isConnected_image ψ).mpr isConnected_univ
  have hConnected : ConnectedSpace M := by
    exact connected_of_connected_double (𝓡∂ 1) M hConnectedDouble

  let M_inl : M → double (𝓡∂ 1) M := double.inl (𝓡∂ 1) M
  let to_R : double (𝓡∂ 1) M ≃ₜ ℝ := hDouble.some
  let φ : M → ℝ := to_R ∘ M_inl

  have hMNonempty : Nonempty M := by
    apply (nonempty_iff_nonempty_double (𝓡∂ 1) M).mpr
    exact Nonempty.intro (hDouble.some.symm 0)

  have hMInlNotSurjective : ¬ Surjective M_inl :=
    by exact not_surjective_double_inl (𝓡∂ 1) M
             ((𝓡∂ 1).isNonempty_interior M hMNonempty)

  have hCE : IsClosedEmbedding φ := by
    apply IsClosedEmbedding.comp
    · exact Homeomorph.isClosedEmbedding to_R
    · exact isClosedEmbedding_double_inl (𝓡∂ 1) M

  let Ω : Set ℝ := φ '' univ
  let ψ : M ≃ₜ Ω := (Homeomorph.Set.univ M).symm.trans
                  <| hCE.toIsEmbedding.homeomorphImage univ

  have hCont : Continuous φ := by exact IsClosedEmbedding.continuous hCE
  have hClosed : IsClosed Ω := by
    exact (IsClosedEmbedding.isClosed_iff_image_isClosed hCE).mp isClosed_univ
  have hNotR : Ω ≠ univ := by
    by_contra h
    rw [show Ω = range φ by exact image_univ] at h
    exact hMInlNotSurjective <| (EquivLike.comp_surjective M_inl to_R).mp (range_eq_univ.mp h)

  have hNotIcc : Ω ≠ Icc (sInf Ω) (sSup Ω) := by
    have hMnoncompact : ¬ CompactSpace M := by
      by_contra hCompact
      have : CompactSpace (double (𝓡∂ 1) M) := by
       exact compact_double_of_compact (𝓡∂ 1) M hCompact
      exact (not_compactSpace_iff.mpr instNoncompactSpaceReal) (Homeomorph.compactSpace to_R)
    by_contra h
    have hΩcompact : IsCompact (univ : Set Ω) := by
      rw [h]; exact isCompact_iff_isCompact_univ.mp isCompact_Icc
    have : CompactSpace M := by
      apply isCompact_univ_iff.mp
      rw [← image_univ_of_surjective (Homeomorph.surjective ψ.symm)]
      exact IsCompact.image hΩcompact (Homeomorph.continuous_symm ψ)
    exact hMnoncompact this

  obtain h_Ici_or_Iic := ClosedNonempty_Real.realClosedNonempty
    (Nonempty.intro (ψ hMNonempty.some)) hClosed
    (IsConnected.image (connectedSpace_iff_univ.mp hConnected) φ (continuousOn_univ.mpr hCont))
    hNotR
  simp [hNotIcc, false_or] at h_Ici_or_Iic

  cases h_Ici_or_Iic with
  | inl hIci =>
    let φM : M ≃ₜ Ici (sInf Ω) := by rwa [← hIci]
    exact Nonempty.intro <| φM.trans <| ClosedInterval_homeomorph.homeomorph_Ici_Ici_zero (sInf Ω)
  | inr hIic =>
    let φM : M ≃ₜ Iic (sSup Ω) := by rwa [← hIic]
    exact Nonempty.intro <| φM.trans <| ClosedInterval_homeomorph.homeomorph_Iic_Ici_zero (sSup Ω)

theorem double_is_R_iff {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] :
    Nonempty ((double (𝓡∂ 1) M) ≃ₜ ℝ) ↔ Nonempty (M ≃ₜ Ici (0 : ℝ)) := by
  constructor <;> intro h
  · exact double_is_R h
  · let φ : M ≃ₜ EuclideanHalfSpace 1 :=
      h.some.trans ClosedInterval_homeomorph.homeomorph_halfSpace.symm
    exact Nonempty.intro <| (double_homeomorph (𝓡∂ 1) φ).trans
                         <| double_halfInterval.some.trans
                         <| Homeomorph.funUnique (Fin 1) ℝ

theorem double_unitInterval : Nonempty (double (𝓡∂ 1) unitInterval ≃ₜ Circle) := by
  let m : ℝ → ℝ := fun t ↦ Real.pi * t
  let f₀ : unitInterval → ℂ := fun t ↦ Complex.exp ((m t) * Complex.I)
  have hfCircle : ∀ t : unitInterval, f₀ t ∈ Submonoid.unitSphere ℂ := by
    intro t
    rw [show (f₀ t ∈ Submonoid.unitSphere ℂ) = (dist (f₀ t) (0 : ℂ) = 1) by rfl,
        dist_zero_right, Complex.norm_exp_ofReal_mul_I (m t)]
  let f₁ : unitInterval → Circle := fun t ↦ ⟨f₀ t, hfCircle t⟩
  have hfCont : Continuous f₁ := by apply Continuous.subtype_mk (by continuity)
  let f : C(unitInterval, Circle) := ⟨f₁, hfCont⟩

  let g₀ : unitInterval → ℂ := fun t ↦ conj (f₀ t)
  have hgCircle : ∀ t : unitInterval, g₀ t ∈ Submonoid.unitSphere ℂ := by
    intro t
    rw [show (g₀ t ∈ Submonoid.unitSphere ℂ) = (dist (g₀ t) (0 : ℂ) = 1) by rfl,
        dist_zero_right, Complex.norm_conj (f₀ t),
        Complex.norm_exp_ofReal_mul_I (m t)]
  let g₁ : unitInterval → Circle := fun t ↦ ⟨g₀ t, hgCircle t⟩
  have hgCont : Continuous g₁ := by apply Continuous.subtype_mk (by continuity)
  let g : C(unitInterval, Circle) := ⟨g₁, hgCont⟩

  haveI : f 0 = g 0 := by
    simp_all only [Complex.ofReal_mul, ContinuousMap.coe_mk, Icc.coe_zero,
      Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, map_one,
      f, f₁, f₀, m, g, g₁, g₀]

  haveI : f 1 = g 1 := by
    simp_all only [Complex.ofReal_mul, ContinuousMap.coe_mk, Icc.coe_one,
      Complex.ofReal_one, mul_one, Complex.exp_pi_mul_I, map_neg, map_one,
      f, f₁, f₀, m, g, g₁, g₀]

  have w : CategoryTheory.CategoryStruct.comp (bdry_inc' (𝓡∂ 1) unitInterval) (TopCat.ofHom f) =
           CategoryTheory.CategoryStruct.comp (bdry_inc' (𝓡∂ 1) unitInterval) (TopCat.ofHom g) := by
    ext x
    simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply, SetLike.coe_eq_coe]
    by_cases hx : x = (0:ℝ)
    · have : (bdry_inc' (𝓡∂ 1) unitInterval) x = 0 := by
        simp_all only [Icc.coe_eq_zero]
        exact hx
      rwa [this]
    · have : x = (1:ℝ) := by
        let s1 : Set unitInterval := singleton 1
        simp_all only [Icc.coe_eq_zero, Icc.coe_eq_one]
        have hxBoundary : ↑x ∈ insert (0 : unitInterval) s1 := by
          rw [← show (𝓡∂ 1).boundary unitInterval = insert 0 {1} by
                exact boundary_Icc (hxy := by exact fact_iff.mpr Real.zero_lt_one)]
          exact Subtype.coe_prop x
        exact mem_singleton_iff.mp (Set.mem_of_mem_insert_of_ne hxBoundary hx)
      have : (bdry_inc' (𝓡∂ 1) unitInterval) x = 1 := by
        simp only [Icc.coe_eq_one] at this
        exact this
      rwa [this]

  let ψ : double (𝓡∂ 1) unitInterval ⟶ (TopCat.of Circle) :=
    double.desc (𝓡∂ 1) unitInterval f g w

  have hInjective : Injective ψ := by
    have mul_pi_in_Icc_0_pi (u : unitInterval) :
        Real.pi * u.val ∈ Icc 0 Real.pi := by
      have h0 : 0 ≤ Real.pi * u.val := by calc
        0 = Real.pi * 0 := by exact Eq.symm (mul_zero Real.pi)
        _ ≤ Real.pi * u := by
          exact (mul_le_mul_iff_right₀ Real.pi_pos).mpr (unitInterval.nonneg u)
      have hπ : Real.pi * u.val ≤ Real.pi := by calc
        Real.pi * u.val ≤ Real.pi * 1 := by
          exact (mul_le_mul_iff_right₀ Real.pi_pos).mpr (unitInterval.le_one u)
        _ = Real.pi := by exact MulOneClass.mul_one Real.pi
      exact ⟨h0, hπ⟩

    have divide_pi {a b : unitInterval} (hab : Real.pi * a = Real.pi * b) : a = b := by
      apply mul_eq_mul_left_iff.mp at hab
      cases hab with
      | inl h => exact SetCoe.ext h
      | inr h => exact False.elim (Real.pi_ne_zero h)

    have eq_if_same_cos (s t : unitInterval) :
        Real.cos (Real.pi * s) = Real.cos (Real.pi * t) → s = t := by
      intro hcos
      have : Real.pi * s = Real.pi * t := by
        exact Real.injOn_cos (mul_pi_in_Icc_0_pi s) (mul_pi_in_Icc_0_pi t) hcos
      exact divide_pi this

    have hfInj : Injective f := by
      intro s t hf
      have : Real.cos (Real.pi * s) = Real.cos (Real.pi * t) := by calc
        Real.cos (Real.pi * s) = (f s).val.re := by
          exact Eq.symm (Complex.exp_ofReal_mul_I_re (m s))
        _ = (f t).val.re := by exact congrArg Complex.re (congrArg Subtype.val hf)
        _ = Real.cos (Real.pi * t) := by exact Complex.exp_ofReal_mul_I_re (m t)
      exact eq_if_same_cos s t this

    have hgInj : Injective g := by
      intro s t hg
      have : Real.cos (Real.pi * s) = Real.cos (Real.pi * t) := by calc
        Real.cos (Real.pi * s) = (g s).val.re := by
          exact Eq.symm (Complex.exp_ofReal_mul_I_re (m s))
        _ = (g t).val.re := by exact congrArg Complex.re (congrArg Subtype.val hg)
        _ = Real.cos (Real.pi * t) := by exact Complex.exp_ofReal_mul_I_re (m t)
      exact eq_if_same_cos s t this

    have hBoundary : ∀ y z : unitInterval,
        f y = g z → y ∈ (𝓡∂ 1).boundary unitInterval := by
      intro y z hyz
      have f_im (u : unitInterval) : (f u).val.im ≥ 0 := by calc
        (f u).val.im = Real.sin (Real.pi * u) := by
          exact Complex.exp_ofReal_mul_I_im (Real.pi * u)
        _ ≥ 0 := by exact Real.sin_nonneg_of_mem_Icc (mul_pi_in_Icc_0_pi u)

      have hfim : (f y).val.im ≥ 0 := by exact f_im y
      have hgim : (g z).val.im ≤ 0 := by
        have : (f z).val.im ≥ 0 := by exact f_im z
        calc
          (g z).val.im = - (f z).val.im := by exact rfl
          _ ≤ 0 := by linarith
      rw [← show (f y).val.im = (g z).val.im by
            exact ((Complex.ext_iff.mp) (congrArg Subtype.val hyz)).2] at hgim
      have hsin_zero : Real.sin (Real.pi * y) = 0 := by calc
        Real.sin (Real.pi * y) = (f y).val.im := by
          exact Eq.symm (Complex.exp_ofReal_mul_I_im (Real.pi * y))
        _ = 0 := by linarith
      have : (Real.pi * y) ≤ 0 ∨ (Real.pi * y) ≥ Real.pi := by
        by_contra h
        push_neg at h
        have : 0 ≠ Real.sin (Real.pi * y) := by
          apply ne_of_lt
          exact Real.sin_pos_of_mem_Ioo h
        exact this (Eq.symm hsin_zero)
      have hy : y = 0 ∨ y = 1 := by
        cases this with
        | inl h =>
          left
          have : Real.pi * y = Real.pi * 0 := by
            rw [mul_zero]
            exact le_antisymm h (mul_nonneg Real.pi_nonneg (unitInterval.nonneg y))
          exact divide_pi this
        | inr h =>
          right
          have : Real.pi * y = Real.pi * 1 := by
            have : Real.pi * y ≤ Real.pi * 1 := by
              exact (mul_le_mul_iff_of_pos_left Real.pi_pos).mpr unitInterval.le_one'
            nth_rewrite 2 [← mul_one Real.pi] at h
            exact le_antisymm this h
          exact divide_pi this

      have : (𝓡∂ 1).boundary unitInterval = {0,1} := by exact boundary_Icc
      cases hy with
      | inl h => rw [h, this]; exact mem_insert 0 {1}
      | inr h => rw [h, this]; exact mem_insert_of_mem 0 (mem_singleton 1)

    exact desc_injective_double (X := TopCat.of Circle) (h := f) (k := g)
        (𝓡∂ 1) unitInterval w hfInj hgInj hBoundary

  have hSurjective : Surjective ψ := by
    apply desc_surjective_double (X := TopCat.of Circle) (𝓡∂ 1) unitInterval f g w
    apply univ_subset_iff.mp
    intro x _
    apply (mem_union x (range f) (range g)).mpr
    simp only [mem_range, Subtype.exists, mem_Icc]
    have : |x.val.re| ≤ 1 := by calc
      |x.val.re| ≤ ‖x.val‖ := by exact Complex.abs_re_le_norm x
      _ = 1 := by exact norm_eq_of_mem_sphere x
    have hx_re_neg1 : x.val.re ≥ -1 := by exact neg_le_of_abs_le this
    have hx_re_pos1 : x.val.re ≤ 1 := by exact le_of_max_le_left this

    let t := (Real.arccos x.val.re) / Real.pi
    have ht0 : t ≥ 0 := by calc
      t ≥ 0 / Real.pi := by
        exact (div_le_div_iff_of_pos_right Real.pi_pos).mpr
              (Real.arccos_nonneg x.val.re)
      _ = 0 := by exact zero_div Real.pi
    have ht1 : t ≤ 1 := by calc
      t ≤ Real.pi / Real.pi := by
        exact (div_le_div_iff_of_pos_right Real.pi_pos).mpr
              (Real.arccos_le_pi x.val.re)
      _ = 1 := by exact (div_eq_one_iff_eq Real.pi_ne_zero).mpr rfl
    have htIcc : Real.pi * t ∈ Icc 0 Real.pi := by
      have : Real.pi * t ≤ Real.pi := by
        nth_rewrite 2 [← mul_one Real.pi]
        exact mul_le_mul_of_nonneg_left ht1 Real.pi_nonneg
      exact ⟨mul_nonneg Real.pi_nonneg ht0, this⟩

    have hCos : Real.cos (Real.pi * t) = x.val.re := by
      rw [show t = (Real.arccos x.val.re) / Real.pi by rfl]
      rw [mul_div_cancel₀]
      exact Real.cos_arccos hx_re_neg1 hx_re_pos1
      exact Real.pi_ne_zero

    have hSin_abs: Real.sin (Real.pi * t) = |x.val.im| := by
      rw [← abs_of_nonneg (Real.sin_nonneg_of_mem_Icc htIcc)]
      calc
        |Real.sin (Real.pi * t)| = √(1 - Real.cos (Real.pi * t) ^ 2) := by
          exact Real.abs_sin_eq_sqrt_one_sub_cos_sq (Real.pi * t)
        _ = √(1 ^ 2 - x.val.re ^ 2) := by rw [hCos, one_pow 2]
        _ = √(‖x.val‖ ^ 2 - x.val.re ^ 2) := by rw [norm_eq_of_mem_sphere x]
        _ = √(x.val.im ^ 2) := by
          rw [Complex.sq_norm x.val, pow_two x.val.re, pow_two x.val.im]
          rw [Complex.normSq_apply x.val, add_sub_cancel_left]
        _ = |x.val.im| := by exact Real.sqrt_sq_eq_abs x.val.im

    rw [← Complex.exp_ofReal_mul_I_re (Real.pi * t)] at hCos
    rw [← Complex.exp_ofReal_mul_I_im (Real.pi * t)] at hSin_abs
    by_cases h : x.val.im ≥ 0
    · left
      rw [abs_of_nonneg h] at hSin_abs
      have : Complex.exp ((Real.pi * t : ℝ) * Complex.I) = x := by
        exact Complex.ext_iff.mpr ⟨hCos, hSin_abs⟩
      use t, ⟨ht0, ht1⟩
      exact Circle.ext_iff.mpr this
    · right
      rw [abs_of_neg (lt_of_not_ge h)] at hSin_abs
      have : conj Complex.exp ((Real.pi * t : ℝ) * Complex.I) = x := by
        rw [← starRingEnd_self_apply x.val]
        apply congrArg conj
        apply Complex.ext_iff.mpr
        rw [Complex.conj_re, Complex.conj_im]
        exact ⟨hCos, hSin_abs⟩
      use t, ⟨ht0, ht1⟩
      exact Circle.ext_iff.mpr this

  haveI : CompactSpace (double (𝓡∂ 1) unitInterval) := by
    exact compact_double_of_compact (𝓡∂ 1) unitInterval (compactSpace_Icc 0 1)
  haveI : T2Space Circle := by exact instT2SpaceOfR1SpaceOfT0Space
  have hCont : Continuous ψ := by exact ContinuousMap.continuous (TopCat.Hom.hom ψ)
  have hBijective : Bijective ψ := ⟨hInjective, hSurjective⟩
  let φ : double (𝓡∂ 1) unitInterval ≃ₜ Circle :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ψ hBijective) hCont
  exact Nonempty.intro φ

instance Circle.isConnectedSpace : ConnectedSpace Circle := by
  apply connectedSpace_iff_univ.mpr
  have : Circle.exp '' (@univ ℝ) = univ := by
    simp only [image_univ]
    apply range_eq_univ.mpr
    exact LeftInverse.surjective Circle.leftInverse_exp_arg
  rw [← this]
  apply IsConnected.image isConnected_univ Circle.exp
  exact continuousOn_univ.mpr (ContinuousMap.continuous Circle.exp)

private theorem Homeomorph.isConnected {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (hConn : ConnectedSpace X) : ConnectedSpace Y := by
  apply connectedSpace_iff_univ.mpr
  rw [← image_univ_of_surjective (Homeomorph.surjective φ)]
  apply IsConnected.image ?_ φ ?_
  · exact connectedSpace_iff_univ.mp hConn
  · exact continuousOn_univ.mpr (Homeomorph.continuous φ)

private def punctured_circle : Set Circle := {(1 : Circle)}ᶜ

noncomputable def punctured_circle_homeo :
    punctured_circle ≃ₜ Ioo (0 : ℝ) (2 * Real.pi) := by
  haveI : Fact (0 < 2 * Real.pi) := by exact { out := Real.two_pi_pos }
  let f₀ : Circle ≃ₜ AddCircle (2 * Real.pi) := AddCircle.homeomorphCircle'.symm
  let pAddS1 : Set (AddCircle (2 * Real.pi)) := {0}ᶜ
  have hf1 : f₀ 1 = 0 := by
    rw [AddCircle.homeomorphCircle'_symm_apply]
    simp only [OneMemClass.coe_one, Complex.arg_one, QuotientAddGroup.mk_zero]
  have hPuncture {x : Circle} : x ∈ punctured_circle ↔ f₀ x ∈ pAddS1 := by
    apply not_iff_not.mp
    constructor <;> intro hx
    · apply notMem_compl_iff.mp at hx
      apply notMem_compl_iff.mpr
      simp only [mem_singleton_iff] at hx ⊢
      rwa [← hx] at hf1
    · apply notMem_compl_iff.mp at hx
      apply notMem_compl_iff.mpr
      simp only [mem_singleton_iff] at hx ⊢
      rw [← hx] at hf1
      exact (Homeomorph.injective f₀) (Eq.symm hf1)

  have hMapsTo_f : MapsTo f₀ punctured_circle pAddS1 := by
    exact fun _ ↦ hPuncture.mp
  have hMapsTo_fsymm : MapsTo f₀.symm pAddS1 punctured_circle := by
    intro y hy
    apply mem_preimage.mp
    rw [Homeomorph.preimage_symm]
    obtain ⟨z,hz⟩ := (Homeomorph.surjective f₀) y
    rw [← hz] at hy ⊢
    exact mem_image_of_mem f₀ <| hPuncture.mpr hy

  let f : Homeomorph punctured_circle pAddS1 := {
    toFun := MapsTo.restrict f₀ punctured_circle pAddS1 hMapsTo_f,
    invFun := MapsTo.restrict f₀.symm pAddS1 punctured_circle hMapsTo_fsymm,
    left_inv := by intro _; simp_all [Subtype.ext_iff],
    right_inv := by intro _; simp_all [Subtype.ext_iff],
    continuous_toFun := by
      apply Continuous.restrict hMapsTo_f
      exact Homeomorph.continuous_symm AddCircle.homeomorphCircle',
    continuous_invFun := by
      apply Continuous.restrict hMapsTo_fsymm
      exact Homeomorph.continuous_symm f₀
  }

  let g₀ : PartialHomeomorph ℝ (AddCircle (2 * Real.pi)) :=
    AddCircle.partialHomeomorphCoe (2 * Real.pi) 0
  have hgsource : g₀.source = Ioo (0 : ℝ) (2 * Real.pi) := by
    obtain h' := AddCircle.partialHomeomorphCoe_source (2 * Real.pi) 0
    rwa [zero_add] at h'
  have hgtarget : g₀.target = pAddS1 := by
    exact AddCircle.partialHomeomorphCoe_target (2 * Real.pi) 0
  let g : Ioo (0 : ℝ) (2 * Real.pi) ≃ₜ pAddS1 := by
    rw [← hgsource, ← hgtarget]
    exact g₀.toHomeomorphSourceTarget
  exact f.trans g.symm

theorem double_is_circle
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
    (hDouble : Nonempty ((double (𝓡∂ 1) M) ≃ₜ Circle)) :
    Nonempty (M ≃ₜ unitInterval) := by

  have hConnectedDouble : ConnectedSpace (double (𝓡∂ 1) M) := by
    apply connectedSpace_iff_univ.mpr
    let ψ : Circle ≃ₜ double (𝓡∂ 1) M := hDouble.some.symm
    rw [← EquivLike.range_eq_univ ψ, ← image_univ]
    exact (Homeomorph.isConnected_image ψ).mpr isConnected_univ
  have hConnected : ConnectedSpace M := by
    exact connected_of_connected_double (𝓡∂ 1) M hConnectedDouble

  have hCompact : CompactSpace M := by
    exact (compact_double_iff_compact (𝓡∂ 1) M).mp
          (Homeomorph.compactSpace hDouble.some.symm)
  have hDouble_nonempty : Nonempty (double (𝓡∂ 1) M) := by
    have : Nonempty Circle := by exact One.instNonempty
    use (hDouble.some).symm this.some
  have hInterior_nonempty : Nonempty ((𝓡∂ 1).interior M) := by
    apply (𝓡∂ 1).isNonempty_interior M
    exact (nonempty_iff_nonempty_double (𝓡∂ 1) M).mpr hDouble_nonempty
  have hBoundary_nonempty : Nonempty ((𝓡∂ 1).boundary M) := by
    apply nonempty_boundary_of_connected_double
    · exact hInterior_nonempty
    · exact hConnectedDouble

  have : ∃ z : (double (𝓡∂ 1) M), z ∉ range (double.inl (𝓡∂ 1) M) := by
    exact not_forall.mp <| not_surjective_double_inl (𝓡∂ 1) M hInterior_nonempty
  obtain ⟨z, hz⟩ := this

  let φ : (double (𝓡∂ 1) M) ≃ₜ Circle := hDouble.some
  haveI : IsTopologicalGroup Circle := by exact Circle.instIsTopologicalGroup
  let f : (double (𝓡∂ 1) M) ≃ₜ Circle := φ.trans (Homeomorph.mulLeft (φ z)⁻¹)
  have hfz : f z = (1 : Circle) := by
    rw [Homeomorph.trans_apply, congrFun (Homeomorph.coe_mulLeft (φ z)⁻¹) (φ z)]
    simp_all only [nonempty_subtype, mem_range, not_exists, inv_mul_cancel]

  have : MapsTo (f ∘ (double.inl (𝓡∂ 1) M)) (@univ M) punctured_circle := by
    intro x hx
    simp only [comp_apply, punctured_circle]
    rw [← hfz]
    apply notMem_singleton_iff.mpr
    by_contra h
    apply Homeomorph.injective f at h
    exact hz (by simp only [mem_range]; use x)
  let f' : (@univ M) → punctured_circle :=
    MapsTo.restrict (f ∘ (double.inl (𝓡∂ 1) M)) (@univ M) punctured_circle this
  have hf'Embed : IsEmbedding f' := by
    apply IsEmbedding.restrict ?_ this
    exact IsEmbedding.comp (Homeomorph.isEmbedding f) (isEmbedding_double_inl (𝓡∂ 1) M)

  let g : M → ℝ :=
    Subtype.val ∘ punctured_circle_homeo ∘ f' ∘ (Homeomorph.Set.univ M).symm
  have hgEmbed : IsEmbedding g := by
    apply IsEmbedding.comp IsEmbedding.subtypeVal
    apply IsEmbedding.comp <| Homeomorph.isEmbedding punctured_circle_homeo
    apply IsEmbedding.comp hf'Embed
    exact Homeomorph.isEmbedding (Homeomorph.Set.univ M).symm

  have hΩCompact : IsCompact (range g) := by
    exact isCompact_range <| IsEmbedding.continuous hgEmbed
  have hΩClosed : IsClosed (range g) := by exact IsCompact.isClosed hΩCompact
  have hgConnected : IsConnected (range g) := by
    apply isConnected_range <| IsEmbedding.continuous hgEmbed
  have hRangeNonempty : range g ≠ ∅ := by
    exact nonempty_iff_ne_empty'.mp <| instNonemptyRange g

  obtain hRange := ClosedNonempty_Real.realCompactNonempty
                   (instNonemptyRange g) hΩCompact hgConnected

  have hInfSup : sInf (range g) < sSup (range g) := by
    by_contra h
    obtain h' := LE.le.lt_or_eq' <| le_of_not_gt h
    cases h' with
    | inl hlt =>
      rw [Icc_eq_empty_of_lt hlt] at hRange
      exact (nonempty_iff_ne_empty'.mp <| instNonemptyRange g) hRange
    | inr heq =>
      rw [heq, Icc_eq_singleton_iff.mpr ⟨rfl, rfl⟩] at hRange
      apply range_eq_singleton_iff.mp at hRange
      let p : M := hBoundary_nonempty.some
      let q : M := hInterior_nonempty.some
      have : p ≠ q := by
        by_contra h
        have : ¬ (𝓡∂ 1).IsBoundaryPoint p := by
          rw [h]
          exact (ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint q).mp
                <| Subtype.coe_prop hInterior_nonempty.some
        exact this <| Subtype.coe_prop hBoundary_nonempty.some
      exact this <| hgEmbed.injective (show g p = g q by rw [hRange p, hRange q])

  have ψ : M ≃ₜ range g := IsEmbedding.toHomeomorph hgEmbed
  rw [hRange] at ψ
  exact Nonempty.intro
        <| ψ.trans <| ClosedInterval_homeomorph.homeomorph_Icc_unitInterval hInfSup

theorem double_is_circle_iff
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] :
    Nonempty ((double (𝓡∂ 1) M) ≃ₜ Circle) ↔ Nonempty (M ≃ₜ unitInterval) := by
  constructor <;> intro h
  · exact double_is_circle h
  · exact Nonempty.intro <| (double_homeomorph (𝓡∂ 1) h.some).trans double_unitInterval.some

/-
universe u
instance chartedSpaceULift (X : Type*) [TopologicalSpace X] :
    ChartedSpace X (ULift X) where
  atlas := {Homeomorph.ulift.toPartialHomeomorph}
  chartAt _ := Homeomorph.ulift.toPartialHomeomorph
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _

theorem double_is_circle_iff'
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] :
    Nonempty ((double (𝓡∂ 1) M) ≃ₜ Circle) ↔ Nonempty (M ≃ₜ unitInterval) := by
  constructor <;> intro h
  · exact double_is_circle h
  · have : ChartedSpace (EuclideanHalfSpace 1) (ULift unitInterval) := by
      have : ChartedSpace unitInterval (ULift unitInterval) := by
        exact chartedSpaceULift unitInterval
      exact ChartedSpace.comp (EuclideanHalfSpace 1) unitInterval (ULift unitInterval)

    let φ : (double (𝓡∂ 1) M) ≃ₜ (double (𝓡∂ 1) (ULift unitInterval)) :=
      double_homeomorph (𝓡∂ 1) (h.some.trans Homeomorph.ulift.symm)
    let ψ : (double (𝓡∂ 1) (ULift unitInterval)) ≃ₜ (double (𝓡∂ 1) unitInterval) :=
      double_homeomorph (𝓡∂ 1) (Homeomorph.ulift) -- doesn't work because of universe issues
    exact Nonempty.intro <| φ.trans <| ψ.trans double_unitInterval.some
-/

end DoubleInterval
