/-
Copyright (c) 2025 Steven Sivek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek
-/
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Interiors and boundaries

In this file we prove theorems about the interiors and boundaries of charted spaces,
assuming that the underlying Euclidean spaces have invariance of domain.  Separately
we will prove invariance of domain for ℝ¹ = `EuclideanSpace ℝ (Fin 1)`, establishing
that 1-manifolds with boundary have closed boundary.

## Main definitions

- `HasInvarianceOfDomain` : a topological space `X` belongs to this class if any
  continuous `f ∈ PartialEquiv X X` sends neighborhoods of points `x ∈ f.source`
  to neighborhoods of `f x`.

## Main results

In each of these results we assume that the spaces in question are all
modeled on `I : ModelWithCorners 𝕜 E H` satisfying `HasInvarianceOfDomain E`.

- `isInteriorPoint_iff_any_chart` : a point `x ∈ M` is an interior point iff
  `I (f x)` is in the interior of `range I` for *every* `f : PartialHomeomorph M H`
  whose source contains `x`.  (By definition, `isInteriorPoint` only requires this
  for the specific chart `f = chartAt H x`.)
- `isBoundaryPoint_iff_any_chart` : a point `x ∈ M` is a boundary point iff
  `I (f x)` is in the frontier of `range I` for *every* `f : PartialHomeomorph M H`
  whose source contains x.  (By definition, `isBoundaryPoint` only requires this
  for the specific chart `f = chartAt H x`.)
- `isOpen_interior` : `I.interior M` is open.
- `dense_interior`: `I.interior M` is dense in M.
- `isNonempty_interior` : if `M` is nonempty then `I.interior M` is nonempty.
- `isClosed_boundary` : `I.boundary M` is closed.
- `isNowhereDense_boundary` : `I.boundary M` is nowhere dense.
- `homeomorph_boundary`: any homeomorphism `φ : X ≃ₜ Y` produces a homeomorphism
  `I.boundary X ≃ₜ I.boundary Y`.
- `homeomorph_interior`: any homeomorphism `φ : X ≃ₜ Y` produces a homeomorphism
  `I.interior X ≃ₜ I.interior Y`.
- `instBoundarylessManifold_interior`: `I.interior Y` is a `BoundarylessManifold`.
-/

open Set Function Topology TopologicalSpace

namespace InvarianceOfDomain

class HasInvarianceOfDomain (X : Type*) [TopologicalSpace X] : Prop where
  invariance_of_domain {x : X} {s : Set X} {f : PartialEquiv X X}
                       (hCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x)

theorem maps_nhds_to_nhds (X : Type*) [TopologicalSpace X]
    [instID : HasInvarianceOfDomain X] {x : X} {s : Set X} {f : PartialEquiv X X}
    (hCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x) := by
  exact instID.invariance_of_domain hCont

/-
  The following theorems prove that invariance of domain is preserved under
  homeomorphism.  Elsewhere we will prove that ℝ has invariance of domain,
  and then use this to deduce the same for `EuclideanSpace ℝ (Fin 1)`.
-/

/-- Invariance of domain is preserved under homeomorphisms. -/
theorem maps_nhds_to_nhds_from_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [HasInvarianceOfDomain Y]
    (φ : Homeomorph X Y) {x : X} {s : Set X} {f : PartialEquiv X X}
    (hfCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x) := by
  intro h hfSource

  let x' : Y := φ x
  let s' : Set Y := φ '' s
  let f' : PartialEquiv Y Y :=
    φ.symm.toPartialEquiv.trans (f.trans φ.toPartialEquiv)

  have h' : s' ∈ nhds x' := by
    apply mem_interior_iff_mem_nhds.mp
    rw [← φ.image_interior]
    exact mem_image_of_mem (⇑φ) (mem_interior_iff_mem_nhds.mpr h)

  have hfSource' : s' ⊆ f'.source := by
    let φinv := φ.symm.toPartialEquiv
    let fφ := f.trans φ.toPartialEquiv
    have h₁ : f'.source = φinv ⁻¹' fφ.source := by
      rw [← univ_inter (φinv ⁻¹' fφ.source), show univ = φinv.source by rfl]
      exact PartialEquiv.trans_source φinv fφ
    have h₂ : fφ.source = f.source := by
      exact inter_eq_self_of_subset_left (by exact fun _ _ ↦ trivial)
    rw [h₁, h₂]
    apply image_subset_iff.mp
    have : φ.symm '' s' = φ ⁻¹' s' := by
      ext a
      simp only [mem_preimage]
      constructor <;> intro ha
      · obtain ⟨b, _, hφb⟩ := ha
        rwa [← show b = φ a by rw [← φ.apply_symm_apply b]; exact congrArg φ hφb]
      · rw [← φ.symm_apply_apply a]
        exact mem_image_of_mem φ.symm ha
    rwa [show φinv '' s' = φ.symm '' s' by rfl, this, φ.preimage_image s]

  have hfCont' : ContinuousOn f' f'.source := by
    have hCont : ContinuousOn (f.trans φ.toPartialEquiv) f.source := by
      rw [← show φ.toPartialEquiv ∘ f = f.trans φ.toPartialEquiv by exact rfl]
      apply Continuous.comp_continuousOn φ.continuous hfCont
    have : f.source = (↑φ.symm.toPartialEquiv '' f'.source) := by
      apply (preimage_eq_iff_eq_image ?_).mp ?_
      · exact φ.symm.bijective
      · simp_all only [PartialEquiv.trans_source, Equiv.toPartialEquiv_source,
          Equiv.toPartialEquiv_apply, Homeomorph.coe_toEquiv, preimage_univ, inter_univ,
          univ_inter, PartialEquiv.coe_trans, s', f']
    rw [this] at hCont
    rw [show f' = (f.trans φ.toPartialEquiv) ∘ φ.symm.toPartialEquiv by exact rfl]
    exact ContinuousOn.image_comp_continuous hCont φ.continuous_symm

  have hφ_symm_comp_f' (y : X) : φ.symm (f' (φ y)) = f y := by
    rw [← φ.symm_apply_apply (f y)]
    apply congrArg φ.symm
    calc
      f' (φ y) = (f.trans φ.toPartialEquiv) (φ.symm (φ y)) := by rfl
      _ = (f.trans φ.toPartialEquiv) y := by
        exact congrArg (f.trans φ.toPartialEquiv) (φ.symm_apply_apply y)
      _ = φ (f y) := by rfl

  have hφfs : φ '' (f '' s) = (f') '' s' := by
    ext y
    constructor <;> rintro ⟨z, ⟨w, hws, hwz⟩, hzy⟩
    · rw [← hzy, ← hwz, ← φ.symm_apply_apply w]
      apply mem_image_of_mem
      exact mem_image_of_mem φ hws
    · rw [← hzy, ← hwz, (EquivLike.inv_apply_eq (e := φ)).mp (hφ_symm_comp_f' w)]
      apply mem_image_of_mem
      exact mem_image_of_mem f hws

  have : (f '' s) ∈ nhds (f x) ↔ ((f') '' s') ∈ nhds (f' x') := by
    rw [← hφfs, φ.image_eq_preimage (f '' s)]
    have : Filter.map φ.symm (nhds (f' x')) = nhds (f x) := by
      rw [← hφ_symm_comp_f' x]
      exact φ.symm.map_nhds_eq (f' x')
    rw [← this]
    rfl
  apply this.mpr
  exact maps_nhds_to_nhds Y hfCont' h' hfSource'

def HasInvarianceOfDomain_from_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [HasInvarianceOfDomain Y] (φ : Homeomorph X Y) :
    HasInvarianceOfDomain X where
  invariance_of_domain := by exact maps_nhds_to_nhds_from_homeomorph φ

end InvarianceOfDomain

namespace ModelWithCorners

open InvarianceOfDomain

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [ChartedSpace H M] in
variable (I) (M) in
/-- If some `PartialHomeomorph M H` sends a point to the interior of `range I`, then
so does any other `PartialHomeomorph M H`. -/
theorem independence_of_interior [HasInvarianceOfDomain E] {x : M}
    {f g : PartialHomeomorph M H} (hfSource : x ∈ f.source) (hgSource : x ∈ g.source) :
    I (f x) ∈ interior (range I) → I (g x) ∈ interior (range I) := by
  intro hfInterior
  apply mem_interior_iff_mem_nhds.mp at hfInterior
  apply mem_interior_iff_mem_nhds.mpr

  let f' : PartialEquiv M E := f.toPartialEquiv.trans I.toPartialEquiv
  have hf'symmCont : ContinuousOn f'.symm f'.target := by
    apply ContinuousOn.comp (PartialHomeomorph.continuousOn f.symm) ?_ ?_
    · simp only [PartialEquiv.restr_coe_symm, toPartialEquiv_coe_symm]
      exact continuousOn_symm I
    · simp only [PartialEquiv.symm_source, PartialEquiv.restr_coe_symm,
        toPartialEquiv_coe_symm, PartialHomeomorph.symm_toPartialEquiv]
      simp only [f', PartialEquiv.trans_target, target_eq, toPartialEquiv_coe_symm]
      exact fun _ hy ↦ mem_preimage.mp <| mem_of_mem_inter_right hy

  let U₀ : Set M := f.source ∩ g.source
  have hU₀nhds : U₀ ∈ nhds x := by
    apply IsOpen.mem_nhds (IsOpen.inter f.open_source g.open_source) ⟨hfSource, hgSource⟩

  let U : Set E := (f') '' U₀
  have hUf'target : U ⊆ f'.target := by
    rw [← f'.image_source_eq_target]
    apply image_mono
    simp [f']
    exact inter_subset_left
  have hf'MapsToU : MapsTo f'.symm U U₀ := by
    intro _ ⟨_, _, hzy⟩
    subst hzy
    simp_all [f', U₀]

  let g' : PartialEquiv M E := g.toPartialEquiv.trans I.toPartialEquiv
  have hg'Cont : ContinuousOn g' U₀ := by
    apply ContinuousOn.mono ?_ <| show U₀ ⊆ g.source by exact inter_subset_right
    apply ContinuousOn.comp ?_ g.continuousOn g.mapsTo
    apply ContinuousOn.mono ?_ (fun _ _ ↦ trivial)
    exact continuousOn_univ.mpr <| I.continuous

  let φ : PartialEquiv E E := f'.symm.trans g'
  have hφCont : ContinuousOn φ U := by
    simp only [PartialEquiv.coe_trans, φ]
    apply ContinuousOn.comp (g := g') hg'Cont ?_ hf'MapsToU
    exact ContinuousOn.mono hf'symmCont hUf'target
  rw [← show φ (I (f x)) = I (g x)
      by simp [φ, f', g', PartialHomeomorph.left_inv f hfSource]]
  have hUφsource : U ⊆ φ.source := by
    rw [PartialEquiv.trans_source]
    simp only [PartialEquiv.symm_source, subset_inter_iff]
    simp_all [f', U, U₀, g', φ]
    exact hf'MapsToU.2

  have hUNhds : U ∈ nhds (I (f x)) := by
    apply nhds_of_nhdsWithin_of_nhds hfInterior
    rw [show U = I '' (f '' U₀) by rw [← image_comp I f U₀]; rfl]
    apply image_mem_nhdsWithin I
    exact PartialHomeomorph.image_mem_nhds f hfSource hU₀nhds

  let φ' : PartialEquiv E E := φ.restr U
  have hφCont'U : ContinuousOn φ' U := by simp [φ']; exact hφCont
  have hφ'Cont : ContinuousOn φ' φ'.source := by
    rw [PartialEquiv.restr_source φ U]
    exact ContinuousOn.mono hφCont'U inter_subset_right

  have : U ⊆ φ'.source := by
    rw [PartialEquiv.restr_source]
    exact subset_inter hUφsource fun _ a ↦ a
  obtain hMapsNhds := maps_nhds_to_nhds E hφ'Cont hUNhds this
  have : (φ') '' U ⊆ range I := by
    rintro _ ⟨z, _, hzy⟩
    rw [← hzy]
    exact mem_range_self (g (f'.symm z))
  exact Filter.mem_of_superset hMapsNhds this

variable (I) in
/-- A point lies in the interior of M iff *any* `PartialHomeomorph M H`
sends it to the interior of `range I`. -/
theorem isInteriorPoint_iff_any_chart {x : M} [HasInvarianceOfDomain E]
    {f : PartialHomeomorph M H} (hfSource : x ∈ f.source) :
    I.IsInteriorPoint x ↔ I (f x) ∈ interior (range I) := by
  constructor <;> intro hx
  · apply isInteriorPoint_iff.mp at hx
    exact (independence_of_interior I M (ChartedSpace.mem_chart_source x) hfSource)
          (by exact (interior_mono <| extChartAt_target_subset_range x) hx)
  · apply isInteriorPoint_iff.mpr
    apply (chartAt H x).mem_interior_extend_target
          ((chartAt H x).map_source <| ChartedSpace.mem_chart_source x)
    exact independence_of_interior I M hfSource (ChartedSpace.mem_chart_source x) hx

variable (I) in
/-- A point lies on the boundary of M iff *any* `PartialHomeomorph M H`
sends it to the frontier of `range I`. -/
theorem isBoundaryPoint_iff_any_chart {x : M} [HasInvarianceOfDomain E]
    {f : PartialHomeomorph M H} (hfSource : x ∈ f.source) :
    (I.IsBoundaryPoint x ↔ I (f x) ∈ frontier (range I)) := by
  apply not_iff_not.mp
  apply Iff.trans <| Iff.symm <| I.isInteriorPoint_iff_not_isBoundaryPoint x
  obtain hInt := I.isInteriorPoint_iff_any_chart hfSource
  rw [← self_diff_frontier] at hInt
  constructor <;> intro hx
  · exact notMem_of_mem_diff <| hInt.mp hx
  · exact hInt.mpr <| mem_diff_of_mem (mem_range_self (f x)) hx

variable (I) (M) in
/-- Given any `f : PartialHomeomorph M H`, if we restrict to `f.source` then the
preimage under I ∘ f of the interior of `range I` is the interior of `M`. -/
theorem preimage_chart_interior [HasInvarianceOfDomain E] (f : PartialHomeomorph M H) :
    f.source ∩ (f.extend I) ⁻¹' (interior (range I)) = f.source ∩ I.interior M := by
  apply Subset.antisymm_iff.mpr
  constructor <;> rintro t ⟨htSource, htInterior⟩
  · apply mem_inter htSource
    apply mem_preimage.mp at htInterior
    by_contra h
    have : t ∈ I.boundary M := by
      by_contra hNotBoundary
      exact h <| (I.isInteriorPoint_iff_not_isBoundaryPoint t).mpr hNotBoundary
    obtain htFrontier := (I.isBoundaryPoint_iff_any_chart htSource).mp this
    exact show (f.extend I) t ∈ (∅ : Set E) by
      rw [← Disjoint.inter_eq disjoint_interior_frontier]
      exact mem_inter htInterior htFrontier
  · apply mem_inter htSource
    simp only [mem_preimage]
    exact (I.isInteriorPoint_iff_any_chart htSource).mp htInterior

variable (I) (M) in
/-- Any `f : PartialHomeomorph M H` sends the interior of `M` to the interior of `range I`. -/
theorem image_chart_interior [HasInvarianceOfDomain E] (f : PartialHomeomorph M H) :
    (f.extend I) '' (f.source ∩ (I.interior M)) ⊆ interior (range I) := by
  rw [← I.preimage_chart_interior M]
  exact image_subset_iff.mpr inter_subset_right

variable (I) (M) in
/-- Any `f : PartialHomeomorph M H` maps the interior of `M` to the interior of `range I`. -/
theorem mapsTo_chart_interior [HasInvarianceOfDomain E] (f : PartialHomeomorph M H) :
    MapsTo (f.extend I) (f.source ∩ I.interior M) (interior (range I)) := by
  exact fun _ ht ↦ I.image_chart_interior M f <| mem_image_of_mem (f.extend I) ht

variable (I) (M) in
/-- Given any `f : PartialHomeomorph M H`, if we restrict to `f.source` then the
preimage under I ∘ f of the frontier of `range I` is the boundary of `M`. -/
theorem preimage_chart_frontier [HasInvarianceOfDomain E] (f : PartialHomeomorph M H) :
    f.source ∩ (f.extend I) ⁻¹' (frontier (range I)) = f.source ∩ I.boundary M := by
  apply Subset.antisymm_iff.mpr
  constructor <;> rintro t ⟨htSource, htFrontier⟩
  · apply mem_preimage.mp at htFrontier
    exact mem_inter htSource <| (I.isBoundaryPoint_iff_any_chart htSource).mpr htFrontier
  · apply mem_inter htSource
    simp only [mem_preimage]
    exact (I.isBoundaryPoint_iff_any_chart htSource).mp htFrontier

variable (I) (M) in
/-- Any `f : PartialHomeomorph M H` sends the boundary of `M` to the frontier of `range I`. -/
theorem image_chart_boundary [HasInvarianceOfDomain E] (f : PartialHomeomorph M H) :
    (f.extend I) '' (f.source ∩ I.boundary M) ⊆ frontier (range I) := by
  rw [← I.preimage_chart_frontier M f]
  exact image_subset_iff.mpr inter_subset_right

variable (I) (M) in
/-- Any `f : PartialHomeomorph M H` maps the boundary of `M` to the frontier of `range I`. -/
theorem mapsTo_chart_boundary [HasInvarianceOfDomain E] (f : PartialHomeomorph M H) :
    MapsTo (f.extend I) (f.source ∩ I.boundary M) (frontier (range I)) := by
  exact fun _ ht ↦ (I.image_chart_boundary M f) (mem_image_of_mem (f.extend I) ht)

variable (I) (M) in
/-- The interior of `M` is an open set. -/
theorem isOpen_interior [HasInvarianceOfDomain E] : IsOpen (I.interior M) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  apply I.isInteriorPoint_iff.mp at hx
  let φ := extChartAt I x
  obtain ⟨s, hsTarget, hsOpen, hxs⟩ := by exact mem_interior.mp hx

  haveI : φ.symm '' s ⊆ I.interior M := by
    rw [PartialEquiv.symm_image_eq_source_inter_preimage φ hsTarget]
    apply preimage_subset_iff.mpr
    rintro a ⟨haSource, haψInv⟩
    rw [extChartAt_source] at haSource
    have : φ a ∈ interior (range I) := by
      apply interior_mono <| extChartAt_target_subset_range x
      apply interior_mono hsTarget
      rwa [interior_eq_iff_isOpen.mpr hsOpen]
    exact (I.isInteriorPoint_iff_any_chart haSource).mpr this

  haveI : IsOpen (φ.symm '' s) := by
    rw [PartialEquiv.symm_image_eq_source_inter_preimage φ hsTarget]
    exact ContinuousOn.isOpen_inter_preimage
      (continuousOn_extChartAt x) (isOpen_extChartAt_source x) hsOpen

  haveI : x ∈ φ.symm '' s := by
    rw [← extChartAt_to_inv (I := I) x]
    exact mem_image_of_mem φ.symm hxs

  use (φ.symm '' s)

variable (I) (M) in
/-- The interior of `M` is a dense set. -/
theorem dense_interior [HasInvarianceOfDomain E] : Dense (I.interior M) := by
  intro x
  by_cases hx : x ∈ I.interior M
  · exact subset_closure hx
  · apply mem_closure_iff.mpr
    by_contra! h
    obtain ⟨U, hUOpen, hxU, hUint⟩ := h
    replace hUint : U ⊆ I.boundary M := by
      rw [← I.compl_interior]
      exact Disjoint.subset_compl_right <| disjoint_iff_inter_eq_empty.mpr hUint
    let φ : PartialHomeomorph M H := chartAt H x
    let V : Set M := U ∩ φ.source
    let W : Set E := I '' (φ '' V)
    have : V ∈ nhds x := by
      apply (IsOpen.mem_nhds_iff <| IsOpen.inter hUOpen φ.open_source).mpr
      exact mem_inter hxU <| ChartedSpace.mem_chart_source x
    have hWNhd : W ∈ nhdsWithin (I (φ x)) (range I) := by
      apply image_mem_nhdsWithin I
      refine φ.image_mem_nhds ?_ this
      exact ChartedSpace.mem_chart_source x
    have hFrontier : frontier (range I) ∈ nhdsWithin (I (φ x)) (range I) := by
      apply Filter.mem_of_superset hWNhd ?_
      rw [show W = (φ.extend I) '' V by simp; exact image_image I φ V]
      intro y ⟨x',hx',hx'y⟩
      rw [← hx'y, show (φ.extend I) x' = I (φ x') by rfl]
      apply (I.isBoundaryPoint_iff_any_chart (inter_subset_right hx')).mp
      exact hUint <| mem_of_mem_inter_left hx'
    obtain ⟨A, hAOpen, hIφxA, hAintRange⟩ := mem_nhdsWithin.mp hFrontier

    have hIφxClosure : I (φ x) ∈ closure (interior (range ↑I)) := by
      rw [← I.range_eq_closure_interior]
      exact mem_range_self (φ x)
    obtain hAIntNonempty := mem_closure_iff.mp hIφxClosure A hAOpen hIφxA
    let q : E := hAIntNonempty.some
    obtain ⟨hqA, hqInt⟩ := (mem_inter_iff q A (interior (range I))).mp
                           <| Nonempty.some_mem hAIntNonempty
    have : q ∈ (interior (range I))ᶜ := by
      exact mem_of_mem_inter_right <| hAintRange
            <| mem_inter hqA <| interior_subset hqInt
    exact this hqInt

variable (I) (M) in
/-- If `M` is nonempty, then so is its interior. -/
theorem isNonempty_interior [HasInvarianceOfDomain E] :
    Nonempty M → Nonempty (I.interior M) := by
  exact fun hM ↦ Nonempty.to_subtype <| (Dense.nonempty_iff (I.dense_interior M)).mpr hM

variable (I) (M) in
/-- The boundary of `M` is a closed set. -/
theorem isClosed_boundary [HasInvarianceOfDomain E] : IsClosed (I.boundary M) := by
  apply isOpen_compl_iff.mp
  rw [ModelWithCorners.compl_boundary]
  exact I.isOpen_interior M

variable (I) (M) in
/-- The boundary of `M` is nowhere dense. -/
theorem isNowhereDense_boundary [HasInvarianceOfDomain E] :
    IsNowhereDense (I.boundary M) := by
  obtain hOpenCompl := I.isOpen_interior M
  obtain hDenseCompl := I.dense_interior M
  rw [← I.compl_boundary] at hOpenCompl hDenseCompl
  exact (isClosed_isNowhereDense_iff_compl.mpr ⟨hOpenCompl, hDenseCompl⟩).2

variable (I) in
/-- A homeomorphism between manifolds sends the interior of one to the interior of the other. -/
theorem homeomorph_image_interior [HasInvarianceOfDomain E] {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
    (φ : X ≃ₜ Y) : φ '' (I.interior X) = I.interior Y := by
  ext y
  constructor
  · rintro ⟨x, hxInt, hxy⟩
    let ψ : PartialHomeomorph Y H := φ.symm.toPartialHomeomorph.trans (chartAt H x)
    have hySource : y ∈ ψ.source := by subst hxy; simp_all [ψ]
    apply (I.isInteriorPoint_iff_any_chart hySource).mpr
    rw [show ψ y = (chartAt H x) x by simp [ψ, ← hxy]]
    exact (I.isInteriorPoint_iff_any_chart <| ChartedSpace.mem_chart_source x).mp hxInt
  · intro hy
    let x : X := φ.symm y
    let ψ : PartialHomeomorph Y H := φ.symm.toPartialHomeomorph.trans (chartAt H x)
    have hySource : y ∈ ψ.source := by simp [ψ, x]
    have : I (ψ y) ∈ interior (range I) := by
      exact (I.isInteriorPoint_iff_any_chart hySource).mp hy
    rw [show ψ y = (chartAt H x) x by simp [ψ, x]] at this
    rw [← φ.apply_symm_apply y]
    exact mem_image_of_mem φ this

variable (I) in
/-- A homeomorphism between manifolds sends the boundary of one to the boundary of the other. -/
theorem homeomorph_image_boundary [HasInvarianceOfDomain E] {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
    (φ : X ≃ₜ Y) : φ '' (I.boundary X) = I.boundary Y := by
  rw [← compl_interior, ← compl_interior, image_compl_eq φ.bijective]
  rw [I.homeomorph_image_interior φ]

private def homeomorph_restrict {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
    {A : Set X} {B : Set Y} (φ : X ≃ₜ Y) (hφ : φ '' A = B) : A ≃ₜ B :=
  have hφimage (p : A) : φ p.val ∈ B := by
    rw [← hφ]
    exact mem_image_of_mem φ <| Subtype.coe_prop p
  let i : A → B := fun p ↦ ⟨φ p, hφimage p⟩
  have hiCont : Continuous i := by
    apply Continuous.subtype_mk ?_ hφimage
    exact Continuous.comp' (Homeomorph.continuous φ) continuous_subtype_val

  have hφsymm (p : B) : φ.symm p.val ∈ A := by
    have : φ (φ.symm p.val) ∈ φ '' A := by
      rw [φ.apply_symm_apply p, hφ]
      exact Subtype.coe_prop p
    obtain ⟨x, hxA, hφ⟩ := this
    rwa [φ.injective hφ] at hxA
  let j : B → A := fun p ↦ ⟨φ.symm p, hφsymm p⟩
  have hjCont : Continuous j := by
    apply Continuous.subtype_mk ?_ hφsymm
    exact Continuous.comp' (Homeomorph.continuous_symm φ) continuous_subtype_val

  {
    toFun := i,
    invFun := j,
    left_inv := by
      intro x; simp only [Homeomorph.symm_apply_apply, Subtype.coe_eta, j, i],
    right_inv := by
      intro x; simp only [Homeomorph.apply_symm_apply, Subtype.coe_eta, j, i],
    continuous_toFun := hiCont,
    continuous_invFun := hjCont
  }

variable (I) in
/-- A homeomorphism between manifolds induces a homeomorphism between their boundaries. -/
def homeomorph_boundary [HasInvarianceOfDomain E] {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
    (φ : X ≃ₜ Y) : I.boundary X ≃ₜ I.boundary Y := by
  exact homeomorph_restrict (H := H) φ (I.homeomorph_image_boundary φ)

variable (I) in
lemma homeomorph_boundary_apply [HasInvarianceOfDomain E]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [ChartedSpace H Y] (φ : X ≃ₜ Y) {x : I.boundary X} :
  (homeomorph_boundary I φ) x = φ x.val := by rfl

variable (I) in
/-- A homeomorphism between manifolds induces a homeomorphism between their interiors. -/
def homeomorph_interior [HasInvarianceOfDomain E] {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
    (φ : X ≃ₜ Y) : I.interior X ≃ₜ I.interior Y := by
  exact homeomorph_restrict (H := H) φ (I.homeomorph_image_interior φ)

variable (I) in
lemma homeomorph_interior_apply [HasInvarianceOfDomain E]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [ChartedSpace H Y] (φ : X ≃ₜ Y) {x : I.interior X} :
  (homeomorph_interior I φ) x = φ x.val := by rfl

variable (I) in
/-- If one manifold is homeomorphic to the interior of another, then it is a
BoundarylessManifold. -/
theorem boundaryless_homeomorph_interior [HasInvarianceOfDomain E] {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
    (φ : X ≃ₜ I.interior Y) : BoundarylessManifold I X := by
  apply Boundaryless.of_boundary_eq_empty
  rw [← I.compl_interior]
  apply compl_empty_iff.mpr
  apply univ_subset_iff.mp

  by_cases hY : Nonempty Y
  · intro x _
    let i : C(I.interior Y, Y) :=
      (ContinuousMap.mk Subtype.val).comp
        (ContinuousMap.inclusion (t := @univ Y) (fun _ _ ↦ trivial))
    have hiEmbed : IsOpenEmbedding i := by
      constructor
      · exact IsEmbedding.comp IsEmbedding.subtypeVal (IsEmbedding.inclusion fun _ a ↦ a)
      · have : range i = I.interior Y := by
          ext y; simp_all [i]
          constructor <;> intro h
          · obtain ⟨_, _, h'⟩ := h; rwa [← h']
          · use y, h; rfl
        rw [this]
        exact I.isOpen_interior Y
    haveI : Nonempty (I.interior Y) := by exact I.isNonempty_interior Y hY
    let y : Y := (φ x).val
    let ψ : PartialHomeomorph X H :=
      φ.toPartialHomeomorph.trans <| hiEmbed.toPartialHomeomorph.trans <| chartAt H y
    have hxSource : x ∈ ψ.source := by
      simp [ψ]; exact ChartedSpace.mem_chart_source y
    apply (I.isInteriorPoint_iff_any_chart hxSource).mpr
    exact Subtype.coe_prop (φ x)
  · haveI : IsEmpty Y := by exact not_nonempty_iff.mp hY
    rw [show @univ X = ∅ by by_contra! h; exact IsEmpty.false (φ h.some)]
    exact empty_subset (I.interior X)

variable (I) (M) in
noncomputable instance instChartedSpaceInterior [HasInvarianceOfDomain E] :
    ChartedSpace H (I.interior M) := by
  exact TopologicalSpace.Opens.instChartedSpace ⟨I.interior M, I.isOpen_interior M⟩

variable (I) (M) in
/-- The interior of a manifold is a BoundarylessManifold. -/
instance instBoundarylessManifold_interior [HasInvarianceOfDomain E] :
    BoundarylessManifold I (I.interior M) := by
  exact I.boundaryless_homeomorph_interior <| Homeomorph.refl (I.interior M)

end ModelWithCorners
