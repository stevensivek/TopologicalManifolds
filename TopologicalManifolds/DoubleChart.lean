/-
Copyright (c) 2025 Steven Sivek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek
-/
import Mathlib.Tactic
import «TopologicalManifolds».Gluing
import «TopologicalManifolds».InvarianceOfDomain

open Set Function Topology Manifold InvarianceOfDomain

namespace Double

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [HasInvarianceOfDomain E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

omit [HasInvarianceOfDomain E] in
private lemma interiorIntoDouble (il : C(M, double I M)) (hlEmbedding : IsEmbedding il) :
    ∃ ψ : C(I.interior M, double I M),
      IsEmbedding ψ ∧ range ψ = il '' (I.interior M) ∧
      (∀ x : I.interior M, ψ x = il x.val):= by
  have hMapsTo : MapsTo il (I.interior M) (@univ (double I M)) :=
    by exact fun _ _ ↦ trivial
  let j₀ : I.interior M → @univ (double I M) :=
    MapsTo.restrict il (I.interior M) univ hMapsTo
  let j : I.interior M → double I M := (Subtype.val : @univ (double I M) → double I M) ∘ j₀
  have hjRange : range j = il '' (I.interior M) := by
    simp only [j, range_comp, j₀, MapsTo.range_restrict, Subtype.image_preimage_coe, univ_inter]
  have hjEmbed : IsEmbedding j := by
    apply IsEmbedding.comp (g := Subtype.val)
    · exact IsEmbedding.subtypeVal
    · exact hlEmbedding.restrict hMapsTo
  have hjApply : ∀ x : I.interior M, j x = il x.val := by
    intro x
    simp_all only [comp_apply, MapsTo.val_restrict_apply, j, j₀]
  use ⟨j, hjEmbed.continuous⟩
  exact ⟨hjEmbed, hjRange, hjApply⟩

theorem doubled_target_chart {x : M} {φ : PartialHomeomorph M H}
    (hφ : x ∈ φ.source) (hx : I (φ x) ∈ interior (range I)) :
    ∃ ψ : PartialHomeomorph M (double I H), x ∈ ψ.source := by
  let U : Set M := φ.source ∩ (I.interior M)
  have hxU : x ∈ U := by
    exact mem_inter hφ <| (I.isInteriorPoint_iff_any_chart hφ).mpr hx
  let V : Set H := φ '' U
  have hUOpen : IsOpen U := by
    exact IsOpen.inter φ.open_source (I.isOpen_interior M)
  have hVOpen : IsOpen V := by
    exact φ.isOpen_image_source_inter (I.isOpen_interior M)
  have hVInt : V ⊆ I.interior H := by
    intro t ⟨s, hsU, hst⟩
    have hIt : I t ∈ interior (range I) := by
      rw [← hst]
      exact (I.mapsTo_chart_interior M φ) hsU
    have : t ∈ (Homeomorph.refl H).toPartialHomeomorph.source := by exact trivial
    exact (I.isInteriorPoint_iff_any_chart this).mpr hIt

  let φ_restr : PartialHomeomorph M H := φ.restrOpen U hUOpen
  have hφ_restr_cont : Continuous (U.restrict φ_restr) := by
    apply ContinuousOn.restrict
    exact ContinuousOn.mono φ.continuousOn inter_subset_left
  let φ₀ : C(U, H) := ⟨U.restrict φ_restr, hφ_restr_cont⟩
  have hφ₀OpenEmbed : IsOpenEmbedding φ₀ := by
    have : φ_restr.source = U := by
      rw [φ.restrOpen_source U hUOpen]
      exact inter_eq_self_of_subset_right inter_subset_left
    obtain h := φ_restr.isOpenEmbedding_restrict
    rwa [this] at h
  have hφ₀Range : range φ₀ = V := by
    simp_all [V, U, φ₀, φ_restr]; rfl

  let il : C(H, double I H) := TopCat.Hom.hom (double.inl I H)
  let ir : C(H, double I H) := TopCat.Hom.hom (double.inr I H)
  obtain ⟨j, hjEmbed, hjRange, _⟩ :=
    interiorIntoDouble I H il (isEmbedding_double_inl I H)
  have hjOpenEmbed : IsOpenEmbedding j := by
    apply (isOpenEmbedding_iff j).mpr ⟨hjEmbed, ?_⟩
    rw [hjRange]
    exact isOpen_double_inl_interior I H

  have hφ₀Int (u : U) : φ₀ u ∈ I.interior H := by
    exact hVInt <| mem_image_of_mem φ u.property
  let ψ₀ : U → I.interior H := codRestrict φ₀ (I.interior H) hφ₀Int
  have hψ₀Embed : IsEmbedding ψ₀ := by
    exact hφ₀OpenEmbed.toIsEmbedding.codRestrict (I.interior H) hφ₀Int

  let ψ : C(U, double I H) := ContinuousMap.comp ⟨j, hjEmbed.continuous⟩ ⟨ψ₀, hψ₀Embed.continuous⟩
  have hψOpenEmbed : IsOpenEmbedding ψ := by
    apply IsOpenEmbedding.comp (g := j) hjOpenEmbed
    simp only [ContinuousMap.coe_mk, ψ₀]
    apply (isOpenEmbedding_iff ψ₀).mpr ⟨hψ₀Embed, ?_⟩
    have : range ψ₀ = Subtype.val ⁻¹' V := by
      rw [← hφ₀Range]
      simp_all only
      exact MapsTo.range_restrict φ_restr U (I.interior H) (fun x hx ↦ hφ₀Int ⟨x, hx⟩)
    rw [this]
    exact IsOpen.preimage_val hVOpen

  haveI : Nonempty U := by exact Nonempty.intro ⟨x, hxU⟩
  let f : PartialHomeomorph U (double I H) :=
    IsOpenEmbedding.toPartialHomeomorph ψ hψOpenEmbed
  let U' : TopologicalSpace.Opens M := ⟨U,hUOpen⟩
  let g : PartialHomeomorph U M :=
    U'.partialHomeomorphSubtypeCoe <| Nonempty.intro ⟨x, hxU⟩
  use g.symm ≫ₕ f
  rw [g.symm.trans_source, g.symm_source]
  have hxg : x ∈ g.target := by rwa [U'.partialHomeomorphSubtypeCoe_target]
  apply mem_inter hxg
  simp only [mem_preimage]
  have hMapsTo : MapsTo il (I.interior H) (@univ (double I H)) :=
    by exact fun _ _ ↦ trivial
  have : g.symm x = ⟨x, hxU⟩ := by
    exact g.injOn (hMapsTo hx) trivial (g.right_inv hxg)
  rw [this]
  exact hMapsTo hx

private lemma doubleChart_interior_side {x : M} {φ : PartialHomeomorph M H}
    (hφ : x ∈ φ.source) (hx : I (φ x) ∈ interior (range I))
    (il : C(M, double I M)) (hEmbed : IsEmbedding il)
    (hIntOpen : IsOpen (il '' (I.interior M))) :
    ∃ ψ : PartialHomeomorph (double I M) (double I H), il x ∈ ψ.source := by
  let x' : I.interior M := ⟨x, (I.isInteriorPoint_iff_any_chart hφ).mpr hx⟩
  obtain ⟨ψ, hψ⟩ := doubled_target_chart I M hφ hx

  obtain ⟨j, hjEmbed, hjRange, hjApply⟩ :=
    interiorIntoDouble I M il hEmbed
  have hjOpenEmbed : IsOpenEmbedding j := by
    apply (isOpenEmbedding_iff j).mpr ⟨hjEmbed, ?_⟩
    rwa [hjRange]

  have hIntNonempty : Nonempty (I.interior M) := by
    exact I.isNonempty_interior M <| Nonempty.intro x
  let j' : PartialHomeomorph (I.interior M) (double I M) :=
    hjOpenEmbed.toPartialHomeomorph
  have hxj'Source : x' ∈ j'.source := by trivial
  have hj'x : j' x' = il x := by
    simp only [j', hjOpenEmbed.toPartialHomeomorph_apply]
    exact hjApply x'
  have hinlxj' : il x ∈ j'.target := by
    rw [← hj'x]
    exact j'.map_source hxj'Source

  let Mint : TopologicalSpace.Opens M := ⟨I.interior M, I.isOpen_interior M⟩
  let j'' : PartialHomeomorph M (double I M) :=
    (Mint.partialHomeomorphSubtypeCoe hIntNonempty).symm ≫ₕ j'
  have hxj'' : x ∈ j''.source := by
    rw [PartialHomeomorph.trans_source]
    apply mem_inter
    · rw [PartialHomeomorph.symm_source, Mint.partialHomeomorphSubtypeCoe_target]
      exact x'.property
    · simpa only [mem_preimage]
  have hj''symminlx : j''.symm (il x) = x := by
    simp [j'']
    obtain h := (j'.eq_symm_apply hxj'Source hinlxj').mpr hj'x
    exact congrArg Subtype.val <| Eq.symm h

  let k : PartialHomeomorph (double I M) (double I H) := j''.symm ≫ₕ ψ
  have : il x ∈ k.source := by
    rw [PartialHomeomorph.trans_source, j''.symm_source]
    apply mem_inter
    · rw [PartialHomeomorph.trans_target, PartialHomeomorph.symm_target]
      exact mem_inter hinlxj' hxj'Source
    · apply mem_preimage.mpr
      rwa [hj''symminlx]
  use k

/-- If `x` is in the interior of H, then `(double.inl I M) x` lies in
    a chart of the form `PartialHomeomorph (double I M) (double I H)`. -/
theorem doubleChart_interior_left {x : M} {φ : PartialHomeomorph M H}
    (hφ : x ∈ φ.source) (hx : I (φ x) ∈ interior (range I)) :
    ∃ ψ : PartialHomeomorph (double I M) (double I H),
      (double.inl I M) x ∈ ψ.source := by
  exact doubleChart_interior_side I M hφ hx
        (TopCat.Hom.hom (double.inl I M)) (isEmbedding_double_inl I M)
        (isOpen_double_inl_interior I M)

/-- If `x` is in the interior of H, then `(double.inr I M) x` lies in
    a chart of the form `PartialHomeomorph (double I M) (double I H)`. -/
theorem doubleChart_interior_right {x : M} {φ : PartialHomeomorph M H}
    (hφ : x ∈ φ.source) (hx : I (φ x) ∈ interior (range I)) :
    ∃ ψ : PartialHomeomorph (double I M) (double I H),
      (double.inr I M) x ∈ ψ.source := by
  exact doubleChart_interior_side I M hφ hx
        (TopCat.Hom.hom (double.inr I M)) (isEmbedding_double_inr I M)
        (isOpen_double_inr_interior I M)


end Double
