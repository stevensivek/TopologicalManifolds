/-
Copyright (c) 2025 Steven Sivek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek
-/
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import «TopologicalManifolds».InvarianceOfDomain
import «TopologicalManifolds».Pushout

open Set Function Topology Manifold CategoryTheory CategoryTheory.Limits

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]

open ModelWithCorners InvarianceOfDomain

namespace Gluing

private def inclusion_mk {X : Type*} [TopologicalSpace X] (Y : Set X) : C(Y, X) :=
  (ContinuousMap.mk Subtype.val).comp
    (ContinuousMap.inclusion (s := Y) (t := @univ X) (by exact fun _ _ ↦ trivial))

private def inc_mk' {X : Type*} [TopologicalSpace X] (Y : Set X) :
  TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom <| inclusion_mk Y

private lemma range_inclusion_mk {X : Type*} [TopologicalSpace X] (Y : Set X) :
    range (inclusion_mk Y) = Y := by
  ext x
  simp_all only [mem_range, Subtype.exists]
  apply Iff.intro <;> intro hx
  · obtain ⟨_, ⟨_, h⟩⟩ := hx
    rwa [← h]
  · use x, hx; rfl

private theorem inclusion.isEmbedding {X : Type*} [TopologicalSpace X] (Y : Set X) :
    IsEmbedding (inclusion_mk Y) := by
  exact IsEmbedding.comp (IsEmbedding.subtypeVal) (IsEmbedding.inclusion fun _ a ↦ a)

private theorem inclusion.injective {X : Type*} [TopologicalSpace X] (Y : Set X) :
    Injective (inclusion_mk Y) := by
  exact (inclusion.isEmbedding Y).injective

private theorem inclusion.isClosedEmbedding
    {X : Type*} [TopologicalSpace X] (Y : Set X) (hY : IsClosed Y) :
    IsClosedEmbedding (inclusion_mk Y) := by
  apply (isClosedEmbedding_iff (inclusion_mk Y)).mpr ⟨inclusion.isEmbedding Y, ?_⟩
  rwa [range_inclusion_mk Y]

def bdry_inc' (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    TopCat.of (I.boundary M) ⟶ TopCat.of M :=
  inc_mk' (I.boundary M)

lemma range_bdry_inc' (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    range (bdry_inc' I M) = I.boundary M := by
  simp only [bdry_inc']
  exact range_inclusion_mk (I.boundary M)

variable
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (A : Set X) (B : Set Y)
  (φ : A ≃ₜ B)

private def inc_homeo' : (TopCat.of A) ⟶ (TopCat.of Y) :=
  TopCat.ofHom <| ContinuousMap.comp (inclusion_mk B) φ

private theorem inc_homeo.isEmbedding : IsEmbedding (inc_homeo' A B φ) := by
  apply IsEmbedding.comp (inclusion.isEmbedding B) φ.isEmbedding

private theorem inc_homeo.isClosedEmbedding (hB : IsClosed B) :
    IsClosedEmbedding (inc_homeo' A B φ) := by
  apply IsClosedEmbedding.comp (inclusion.isClosedEmbedding B hB) φ.isClosedEmbedding

private theorem inc_homeo.injective : Injective (inc_homeo' A B φ) := by
  exact (inc_homeo.isEmbedding A B φ).injective

lemma range_inc_homeo : range (inc_homeo' A B φ) = B := by
  simp only [inc_homeo', TopCat.ofHom_comp, TopCat.hom_comp, TopCat.hom_ofHom,
      ContinuousMap.coe_comp, ContinuousMap.coe_coe, EquivLike.range_comp]
  exact range_inclusion_mk B

noncomputable def glued_cocone : PushoutCocone (inc_mk' A) (inc_homeo' A B φ) :=
  pushout.cocone (inc_mk' A) (inc_homeo' A B φ)

noncomputable def glued : TopCat := (glued_cocone A B φ).pt

noncomputable def glued.inl : (TopCat.of X) ⟶ (glued A B φ) :=
  (glued_cocone A B φ).inl

noncomputable def glued.inr : (TopCat.of Y) ⟶ (glued A B φ) :=
  (glued_cocone A B φ).inr

noncomputable def glued.zero : (TopCat.of A) ⟶ (glued A B φ) :=
  (inc_mk' A) ≫ (glued.inl A B φ)

lemma glued.zero_def : glued.zero A B φ = (inc_mk' A) ≫ (glued.inl A B φ) := by rfl

noncomputable def glued.desc {Z : TopCat} (h : C(X, Z)) (k : C(Y, Z))
    (w : CategoryStruct.comp (inc_mk' A) (TopCat.ofHom h)
       = CategoryStruct.comp (inc_homeo' A B φ) (TopCat.ofHom k) := by aesop_cat) :
    (glued A B φ) ⟶ TopCat.of Z :=
  pushout.desc (TopCat.ofHom h) (TopCat.ofHom k) w

theorem glued.w : CategoryStruct.comp (inc_mk' A) (glued.inl A B φ) =
                  CategoryStruct.comp (inc_homeo' A B φ) (glued.inr A B φ) := by
  exact (IsPushout.of_hasPushout (inc_mk' A) (inc_homeo' A B φ)).w

theorem glued_isOpen_iff (U : Set (glued A B φ)) :
    IsOpen U ↔ IsOpen ((glued.inl A B φ) ⁻¹' U) ∧ IsOpen ((glued.inr A B φ) ⁻¹' U) := by
  exact TopCat.Pushout.glued_isOpen_iff (inc_mk' A) (inc_homeo' A B φ) U

theorem glued_isClosed_iff (U : Set (glued A B φ)) :
    IsClosed U ↔   IsClosed ((glued.inl A B φ) ⁻¹' U)
                 ∧ IsClosed ((glued.inr A B φ) ⁻¹' U) := by
  exact TopCat.Pushout.glued_isClosed_iff (inc_mk' A) (inc_homeo' A B φ) U

theorem connected_glued_of_connected :
  Nonempty A → ConnectedSpace X → ConnectedSpace Y →
    ConnectedSpace (glued A B φ) := by
  exact fun hA hM hM' ↦ TopCat.Pushout.glued_connected_of_connected
                        (inc_mk' A) (inc_homeo' A B φ) hA hM hM'

theorem compact_glued_of_compact :
    CompactSpace X → CompactSpace Y → CompactSpace (glued A B φ) := by
  exact fun hM hM' ↦ TopCat.Pushout.glued_compact_of_compact
                     (inc_mk' A) (inc_homeo' A B φ) hM hM'

theorem T2_glued_of_T2 :
    T2Space X → T2Space Y → IsClosed A → IsClosed B → T2Space (glued A B φ) := by
  exact fun hX hY hAClosed hBClosed ↦ TopCat.Pushout.T2_of_T2_closed_embedding
        (inc_mk' A) (inc_homeo' A B φ) hX hY
        (inclusion.isClosedEmbedding A hAClosed)
        (inc_homeo.isClosedEmbedding A B φ hBClosed)

theorem jointly_surjective_glued :
    range (glued.inl A B φ) ∪ range (glued.inr A B φ) = @univ (glued A B φ) := by
  exact TopCat.Pushout.glued_surjective' (inc_mk' A) (inc_homeo' A B φ)

theorem continuous_glued_inl : Continuous (glued.inl A B φ) := by
  exact (ConcreteCategory.hom <| glued.inl A B φ).continuous

theorem isEmbedding_glued_inl : IsEmbedding (glued.inl A B φ) := by
  exact TopCat.Pushout.inl_embedding_of_embedding_right
        (inc_mk' A) (inc_homeo' A B φ) (inc_homeo.isEmbedding A B φ)

theorem isInducing_glued_inl : IsInducing (glued.inl A B φ) := by
  exact (isEmbedding_glued_inl A B φ).isInducing

theorem injective_glued_inl : Injective (glued.inl A B φ) := by
  exact (isEmbedding_glued_inl A B φ).injective

theorem isClosedEmbedding_glued_inl (hB : IsClosed B) :
    IsClosedEmbedding (glued.inl A B φ) := by
  exact TopCat.Pushout.inl_closed_embedding_of_closed_embedding_right
        (inc_mk' A) (inc_homeo' A B φ) (inc_homeo.isClosedEmbedding A B φ hB)

theorem continuous_glued_inr : Continuous (glued.inr A B φ) := by
  exact (ConcreteCategory.hom <| glued.inr A B φ).continuous

theorem isEmbedding_glued_inr : IsEmbedding (glued.inr A B φ) := by
  exact TopCat.Pushout.inr_embedding_of_embedding_left
        (inc_mk' A) (inc_homeo' A B φ) (inclusion.isEmbedding A)

theorem isInducing_glued_inr : IsInducing (glued.inr A B φ) := by
  exact (isEmbedding_glued_inr A B φ).isInducing

theorem injective_glued_inr : Injective (glued.inr A B φ) := by
  exact (isEmbedding_glued_inr A B φ).injective

theorem isClosedEmbedding_glued_inr (hA : IsClosed A) :
    IsClosedEmbedding (glued.inr A B φ) := by
  exact TopCat.Pushout.inr_closed_embedding_of_closed_embedding_left
        (inc_mk' A) (inc_homeo' A B φ) (inclusion.isClosedEmbedding A hA)

theorem continuous_glued_zero : Continuous (glued.zero A B φ) := by
  exact (ConcreteCategory.hom <| glued.zero A B φ).continuous

theorem isEmbedding_glued_zero : IsEmbedding (glued.zero A B φ) := by
  apply IsEmbedding.comp (g := glued.inl A B φ)
  · exact isEmbedding_glued_inl A B φ
  · exact inclusion.isEmbedding A

theorem isInducing_glued_zero : IsInducing (glued.zero A B φ) := by
  exact (isEmbedding_glued_zero A B φ).isInducing

theorem injective_glued_zero : Injective (glued.zero A B φ) := by
  exact (isEmbedding_glued_zero A B φ).injective

theorem isClosedEmbedding_glued_zero (hA : IsClosed A) (hB : IsClosed B) :
    IsClosedEmbedding (glued.zero A B φ) := by
  apply IsClosedEmbedding.comp (g := glued.inl A B φ)
  · exact isClosedEmbedding_glued_inl A B φ hB
  · exact inclusion.isClosedEmbedding A hA

theorem glued_range_inl_intersect_inr :
    (range (glued.inl A B φ)) ∩ (range (glued.inr A B φ)) =
     range (glued.zero A B φ) := by
  apply TopCat.Pushout.inl_mono_intersection_inl_inr (inc_mk' A) (inc_homeo' A B φ)
  exact (inclusion.isEmbedding A).injective

lemma glued_inl_locus_eq_inr_locus :
    (glued.inl A B φ) '' A = (glued.inr A B φ) '' B := by
  have : (inc_homeo' A B φ) '' univ = B := by
    rw [image_univ]
    exact range_inc_homeo A B φ
  rw [← congrArg (image (glued.inr A B φ)) this, ← image_comp,
      ← hom_comp, ← glued.w A B φ, hom_comp, image_comp, image_univ,
      show range (inc_mk' A) = A by exact range_inclusion_mk A]

theorem glued_range_inl_intersect_inr' :
    (range (glued.inl A B φ)) ∩ (range (glued.inr A B φ)) =
     (glued.inl A B φ) '' A := by
  obtain h := glued_range_inl_intersect_inr A B φ
  rw [glued.zero_def A B φ] at h
  simp only [TopCat.hom_comp, ContinuousMap.coe_comp, range_comp] at h
  rwa [show range (inc_mk' A) = A by exact range_inclusion_mk A] at h

theorem glued_range_inl_intersect_inr'' :
    (range (glued.inl A B φ)) ∩ (range (glued.inr A B φ)) =
     (glued.inr A B φ) '' B := by
  rw [← glued_inl_locus_eq_inr_locus]
  exact glued_range_inl_intersect_inr' A B φ

theorem glued_image_inl_complement :
    (glued.inl A B φ) '' Aᶜ = (range (glued.inr A B φ))ᶜ := by
  apply Subset.antisymm
  · obtain h := glued_range_inl_intersect_inr' A B φ
    rw [← image_union_image_compl_eq_range (s := A) (glued.inl A B φ),
      union_inter_distrib_right] at h
    apply congrArg (fun s ↦ (glued.inl A B φ) '' Aᶜ ∩ s) at h
    have hAcA : (glued.inl A B φ) '' Aᶜ ∩ (glued.inl A B φ) '' A = ∅ := by
      rw [← image_inter (injective_glued_inl A B φ), compl_inter_self A, image_empty]
    rw [inter_union_distrib_left, ← inter_assoc, hAcA, empty_inter, empty_union,
        ← inter_assoc, inter_self] at h
    exact subset_compl_iff_disjoint_right.mpr <| disjoint_iff_inter_eq_empty.mpr h
  · intro x hx
    have hinl : x ∈ range (glued.inl A B φ) := by
      have : x ∈ range (glued.inl A B φ) ∨ x ∈ range (glued.inr A B φ) := by
        apply (mem_union x (range (glued.inl A B φ)) (range (glued.inr A B φ))).mp
        rw [jointly_surjective_glued]; trivial
      have : ¬ (x ∈ range (glued.inr A B φ)) := by exact hx
      simp_all only [mem_compl_iff, not_false_eq_true, mem_range, or_false, not_exists]
    rw [← image_univ, ← compl_union_self Aᶜ, image_union, compl_compl] at hinl
    apply (mem_union x ((glued.inl A B φ) '' A) ((glued.inl A B φ) '' Aᶜ)).mp at hinl
    have : x ∉ (glued.inl A B φ) '' A := by
      rw [← glued_range_inl_intersect_inr']
      simp only [mem_inter_iff, not_and]
      exact fun _ ↦ hx
    simp_all only [mem_compl_iff, mem_range, not_exists, mem_image, false_or, not_and]

theorem glued_image_inr_complement :
    (glued.inr A B φ) '' Bᶜ = (range (glued.inl A B φ))ᶜ := by
  let il := glued.inl A B φ
  let ir := glued.inr A B φ
  have : il '' A ⊆ (ir '' Bᶜ)ᶜ := by
    by_contra h
    obtain ⟨x, hxA, hxB⟩ := not_subset.mp h
    have hxB' : x ∈ ir '' Bᶜ := by exact not_notMem.mp hxB
    have : x ∈ ir '' B := by
      rw [← glued_range_inl_intersect_inr'']
      apply mem_inter
      · exact mem_range_of_mem_image il A hxA
      · exact mem_range_of_mem_image ir Bᶜ hxB'
    obtain ⟨s, hsB, hsx⟩ := this
    obtain ⟨t, htB, htx⟩ := hxB'
    rw [← htx] at hsx
    rw [(injective_glued_inr A B φ) hsx] at hsB
    exact htB hsB
  have h : (il '' A) ∩ (ir '' Bᶜ)ᶜ = il '' A := by
    simp_all only [image_subset_iff, preimage_compl, inter_eq_left]
  have h' : il '' Aᶜ = (il '' A)ᶜ ∩ (ir '' Bᶜ)ᶜ := calc
    il '' Aᶜ = (range ir)ᶜ := by exact glued_image_inl_complement A B φ
    _ = ((ir '' B) ∪ (ir '' Bᶜ))ᶜ := by
      rw [← image_union_image_compl_eq_range ir]
    _ = (ir '' B)ᶜ ∩ (ir '' Bᶜ)ᶜ := by rw [compl_union]
    _ = (il '' A)ᶜ ∩ (ir '' Bᶜ)ᶜ := by rw [← glued_inl_locus_eq_inr_locus]
  have : range il = (ir '' Bᶜ)ᶜ := calc
    range il = (il '' A) ∪ (il '' Aᶜ) := by
      exact Eq.symm <| image_union_image_compl_eq_range il
    _ = ((il '' A) ∩ (ir '' Bᶜ)ᶜ) ∪ ((il '' A)ᶜ ∩ (ir '' Bᶜ)ᶜ) := by
      rw [h']; nth_rewrite 1 [← h]; rfl
    _ = (ir '' Bᶜ)ᶜ := by
      rw [← union_inter_distrib_right, union_compl_self, univ_inter]
  rw [← compl_compl (ir '' Bᶜ)]
  exact congrArg compl (Eq.symm this)

theorem glued_trichotomy (x : glued A B φ) :
    x ∈ (glued.inl A B φ) '' Aᶜ ∨ x ∈ (glued.inr A B φ) '' Bᶜ ∨
    x ∈ range (glued.zero A B φ) := by
  have hx : x ∈ range (glued.inl A B φ) ∨ x ∈ range (glued.inr A B φ) := by
    rw [← mem_union, jointly_surjective_glued]
    trivial
  rw [← image_univ, ← compl_union_self A, image_union, mem_union,
      ← image_univ, ← compl_union_self B, image_union, mem_union,
      or_assoc, ← glued_inl_locus_eq_inr_locus A B φ] at hx
  nth_rewrite 3 [or_comm] at hx
  simp only [or_self_left] at hx
  rcases hx with (h | h | h)
  · left; exact h
  · right; right
    rw [glued.zero_def A B φ]
    have : x ∈ (glued.inl A B φ) '' range (inc_mk' A) := by
      rwa [show range (inc_mk' A) = A by exact range_inclusion_mk A]
    simpa only [TopCat.hom_comp, ContinuousMap.coe_comp, range_comp]
  · right; left; exact h

theorem compact_glued_iff_compact (hA : IsClosed A) (hB : IsClosed B) :
    CompactSpace (glued A B φ) ↔ CompactSpace X ∧ CompactSpace Y := by
  constructor <;> intro h
  · constructor
    · exact (isClosedEmbedding_glued_inl A B φ hB).compactSpace
    · exact (isClosedEmbedding_glued_inr A B φ hA).compactSpace
  · exact compact_glued_of_compact A B φ h.1 h.2

theorem desc_surjective_glued {Z : TopCat} (h : C(X, Z)) (k : C(Y, Z))
    (w : CategoryStruct.comp (inc_mk' A) (TopCat.ofHom h)
       = CategoryStruct.comp (inc_homeo' A B φ) (TopCat.ofHom k) := by aesop_cat) :
    (range h) ∪ (range k) = @univ Z → Surjective (glued.desc A B φ h k w) := by
  exact TopCat.Pushout.desc_surjective_of_jointly_surjective
        (inc_mk' A) (inc_homeo' A B φ) (TopCat.ofHom h) (TopCat.ofHom k) w

theorem inl_desc_glued {Z : TopCat} (h : C(X, Z)) (k : C(Y, Z))
    (w : CategoryStruct.comp (inc_mk' A) (TopCat.ofHom h)
       = CategoryStruct.comp (inc_homeo' A B φ) (TopCat.ofHom k) := by aesop_cat) :
    CategoryStruct.comp (glued.inl A B φ) (glued.desc A B φ h k w)
    = TopCat.ofHom h := by
  exact pushout.inl_desc (TopCat.ofHom h) (TopCat.ofHom k) w

theorem inr_desc_glued {Z : TopCat} (h : C(X, Z)) (k : C(Y, Z))
    (w : CategoryStruct.comp (inc_mk' A) (TopCat.ofHom h)
       = CategoryStruct.comp (inc_homeo' A B φ) (TopCat.ofHom k) := by aesop_cat) :
    CategoryStruct.comp (glued.inr A B φ) (glued.desc A B φ h k w)
    = TopCat.ofHom k := by
  exact pushout.inr_desc (TopCat.ofHom h) (TopCat.ofHom k) w

theorem desc_injective_glued {Z : TopCat} (h : C(X, Z)) (k : C(Y, Z))
    (w : CategoryStruct.comp (inc_mk' A) (TopCat.ofHom h)
       = CategoryStruct.comp (inc_homeo' A B φ) (TopCat.ofHom k) := by aesop_cat)
    (hInjh : Injective h) (hInjk : Injective k)
    (hZero : ∀ y : X, ∀ z : Y, (h y = k z → y ∈ A)) :
    Injective (glued.desc A B φ h k w) := by
  rw [← range_inclusion_mk A] at hZero
  exact TopCat.Pushout.desc_injective (inc_mk' A) (inc_homeo' A B φ)
        (TopCat.ofHom h) (TopCat.ofHom k) w
        (inclusion.injective A) (inc_homeo.injective A B φ)
        hInjh hInjk hZero

theorem desc_isClosedMap_glued {Z : TopCat} (h : C(X, Z)) (k : C(Y, Z))
    (w : CategoryStruct.comp (inc_mk' A) (TopCat.ofHom h)
       = CategoryStruct.comp (inc_homeo' A B φ) (TopCat.ofHom k) := by aesop_cat) :
    IsClosedMap h → IsClosedMap k → IsClosedMap (glued.desc A B φ h k w) := by
  exact TopCat.Pushout.desc_isClosedMap (Ω := Z)
        (inc_mk' A) (inc_homeo' A B φ) (TopCat.ofHom h) (TopCat.ofHom k) w

theorem glued_inl_preimage_range_inr :
    (glued.inl A B φ) ⁻¹' (range (glued.inr A B φ)) = A := by
  ext x
  constructor <;> intro hx
  · apply mem_preimage.mp at hx
    have : (glued.inl A B φ) x ∈ range (glued.inl A B φ) ∩ range (glued.inr A B φ) := by
      exact mem_inter (mem_range_self x) hx
    rw [glued_range_inl_intersect_inr' A B φ] at this
    obtain ⟨y,hy,hyx⟩ := this
    apply injective_glued_inl A B φ at hyx
    rwa [hyx] at hy
  · apply mem_preimage.mpr
    have : (glued.inl A B φ) x ∈ (glued.inl A B φ) '' A := by
      exact mem_image_of_mem (glued.inl A B φ) hx
    rw [← glued_range_inl_intersect_inr' A B φ] at this
    exact mem_of_mem_inter_right this

theorem glued_inr_preimage_range_inl :
    (glued.inr A B φ) ⁻¹' (range (glued.inl A B φ)) = B := by
  ext x
  constructor <;> intro hx
  · apply mem_preimage.mp at hx
    have : (glued.inr A B φ) x ∈ range (glued.inl A B φ) ∩ range (glued.inr A B φ) := by
      exact mem_inter hx (mem_range_self x)
    rw [glued_range_inl_intersect_inr'' A B φ] at this
    obtain ⟨y,hy,hyx⟩ := this
    apply injective_glued_inr A B φ at hyx
    rwa [hyx] at hy
  · apply mem_preimage.mpr
    have : (glued.inr A B φ) x ∈ (glued.inr A B φ) '' B := by
      exact mem_image_of_mem (glued.inr A B φ) hx
    rw [← glued_range_inl_intersect_inr'' A B φ] at this
    exact mem_of_mem_inter_left this

theorem glued_inl_preimage_inr_complement :
    (glued.inl A B φ) ⁻¹' ((glued.inr A B φ) '' Bᶜ) = ∅ := by
  apply subset_empty_iff.mp
  intro x hx
  simp only [mem_preimage, mem_image] at hx
  obtain ⟨y,hy,hyx⟩ := hx
  have : (glued.inr A B φ) y ∈ (glued.inr A B φ) '' B := by
    rw [← glued_range_inl_intersect_inr'' A B φ]
    simp only [mem_inter_iff, mem_range, exists_apply_eq_apply, and_true]
    use x
    exact Eq.symm hyx
  obtain ⟨y', hyB, hy'⟩ := this
  have : y' = y := by exact (injective_glued_inr A B φ) hy'
  rw [(injective_glued_inr A B φ) hy'] at hyB
  exact hy hyB

theorem glued_inr_preimage_inl_complement :
    (glued.inr A B φ) ⁻¹' ((glued.inl A B φ) '' Aᶜ) = ∅ := by
  apply subset_empty_iff.mp
  intro x hx
  simp only [mem_preimage, mem_image] at hx
  obtain ⟨y,hy,hyx⟩ := hx
  have : (glued.inl A B φ) y ∈ (glued.inl A B φ) '' A := by
    rw [← glued_range_inl_intersect_inr' A B φ]
    simp only [mem_inter_iff, mem_range, exists_apply_eq_apply, true_and]
    use x
    exact Eq.symm hyx
  obtain ⟨y', hyB, hy'⟩ := this
  have : y' = y := by exact (injective_glued_inl A B φ) hy'
  rw [(injective_glued_inl A B φ) hy'] at hyB
  exact hy hyB

theorem nonempty_iff_nonempty_glued :
    (Nonempty X) ∨ (Nonempty Y) ↔ Nonempty (glued A B φ) := by
  have hrangeX : Nonempty X ↔ (range (glued.inl A B φ)).Nonempty := by
    exact Iff.symm range_nonempty_iff_nonempty
  have hrangeY : Nonempty Y ↔ (range (glued.inr A B φ)).Nonempty := by
    exact Iff.symm range_nonempty_iff_nonempty
  constructor <;> intro h
  · cases h with
    | inl hX => apply hrangeX.mp at hX; use hX.some
    | inr hY => apply hrangeY.mp at hY; use hY.some
  · apply nonempty_iff_univ_nonempty.mp at h
    rw [← jointly_surjective_glued A B φ] at h
    simp only [union_nonempty] at h
    cases h with
    | inl h' => left; exact hrangeX.mpr h'
    | inr h' => right; exact hrangeY.mpr h'

end Gluing

namespace Double
open Gluing

variable
  (I : ModelWithCorners 𝕜 E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

noncomputable def double_cocone :
    PushoutCocone (bdry_inc' I M) (bdry_inc' I M) :=
  glued_cocone (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

noncomputable def double := (double_cocone I M).pt

noncomputable def double.inl : (TopCat.of M) ⟶ double I M := (double_cocone I M).inl

noncomputable def double.inr : (TopCat.of M) ⟶ double I M := (double_cocone I M).inr

noncomputable def double.zero : (TopCat.of (I.boundary M)) ⟶ double I M :=
  (inc_mk' (I.boundary M)) ≫ (double.inl I M)

lemma double.zero_def : double.zero I M = (inc_mk' (I.boundary M)) ≫ (double.inl I M) := by rfl

noncomputable def double.desc {X : TopCat} (h k : C(M, X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    (double I M) ⟶ X :=
  glued.desc (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M)) h k w

theorem double.w : CategoryStruct.comp (bdry_inc' I M) (double.inl I M) =
                  CategoryStruct.comp (bdry_inc' I M) (double.inr I M) := by
  exact glued.w (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_isOpen_iff (U : Set (double I M)) :
    IsOpen U ↔ IsOpen ((double.inl I M) ⁻¹' U) ∧ IsOpen ((double.inr I M) ⁻¹' U) := by
  exact glued_isOpen_iff (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M)) U

theorem double_isClosed_iff (U : Set (double I M)) :
    IsClosed U ↔ IsClosed ((double.inl I M) ⁻¹' U) ∧ IsClosed ((double.inr I M) ⁻¹' U) := by
  exact glued_isClosed_iff (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M)) U

theorem connected_double_of_connected :
    Nonempty (I.boundary M) → ConnectedSpace M → ConnectedSpace (double I M) := by
  exact fun hbdry hM ↦ connected_glued_of_connected
                      (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))
                      hbdry hM hM

theorem compact_double_of_compact : CompactSpace M → CompactSpace (double I M) := by
  exact fun hM ↦ compact_glued_of_compact (I.boundary M) (I.boundary M)
                 (Homeomorph.refl (I.boundary M)) hM hM

theorem compact_double_iff_compact [HasInvarianceOfDomain E] :
    CompactSpace (double I M) ↔ CompactSpace M := by
  apply Iff.trans <| compact_glued_iff_compact (I.boundary M) (I.boundary M)
      (Homeomorph.refl (I.boundary M)) (I.isClosed_boundary M) (I.isClosed_boundary M)
  exact and_iff_left_of_imp fun a ↦ a

theorem T2_double_of_T2 [HasInvarianceOfDomain E] : T2Space M → T2Space (double I M) := by
  exact fun hM ↦ T2_glued_of_T2 (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))
                  hM hM (I.isClosed_boundary M) (I.isClosed_boundary M)

theorem jointly_surjective_double :
    range (double.inl I M) ∪ range (double.inr I M) = @univ (double I M) := by
  exact jointly_surjective_glued (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem continuous_double_inl : Continuous (double.inl I M) := by
  exact (ConcreteCategory.hom <| double.inl I M).continuous

theorem isClosedEmbedding_double_inl [HasInvarianceOfDomain E] :
    IsClosedEmbedding (double.inl I M) := by
  exact isClosedEmbedding_glued_inl
    (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))
    (I.isClosed_boundary M)

theorem isEmbedding_double_inl : IsEmbedding (double.inl I M) := by
  exact isEmbedding_glued_inl (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem isInducing_double_inl : IsInducing (double.inl I M) := by
  exact isInducing_glued_inl (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem injective_double_inl : Injective (double.inl I M) := by
  exact injective_glued_inl (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem continuous_double_inr : Continuous (double.inr I M) := by
  exact (ConcreteCategory.hom <| double.inr I M).continuous

theorem isClosedEmbedding_double_inr [HasInvarianceOfDomain E] :
    IsClosedEmbedding (double.inr I M) := by
  exact isClosedEmbedding_glued_inr
    (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))
    (I.isClosed_boundary M)

theorem isEmbedding_double_inr : IsEmbedding (double.inr I M) := by
  exact isEmbedding_glued_inr (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem isInducing_double_inr : IsInducing (double.inr I M) := by
  exact isInducing_glued_inr (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem injective_double_inr : Injective (double.inr I M) := by
  exact injective_glued_inr (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem continuous_double_zero : Continuous (double.zero I M) := by
  exact (ConcreteCategory.hom <| double.zero I M).continuous

theorem isClosedEmbedding_double_zero [HasInvarianceOfDomain E] :
    IsClosedEmbedding (double.zero I M) := by
  exact isClosedEmbedding_glued_zero
    (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))
    (I.isClosed_boundary M) (I.isClosed_boundary M)

theorem isEmbedding_double_zero : IsEmbedding (double.zero I M) := by
  exact isEmbedding_glued_zero (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem isInducing_double_zero : IsInducing (double.zero I M) := by
  exact isInducing_glued_zero (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem injective_double_zero : Injective (double.zero I M) := by
  exact injective_glued_zero (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_range_inl_intersect_inr :
    (range (double.inl I M)) ∩ (range (double.inr I M)) =
     range ((bdry_inc' I M) ≫ (double.inl I M)) := by
  exact glued_range_inl_intersect_inr (I.boundary M) (I.boundary M)
        (Homeomorph.refl (I.boundary M))

theorem double_range_inl_intersect_inr' :
    (range (double.inl I M)) ∩ (range (double.inr I M)) =
    (double.inl I M) '' (I.boundary M) := by
  exact glued_range_inl_intersect_inr'
        (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_range_inl_intersect_inr'' :
    (range (double.inl I M)) ∩ (range (double.inr I M)) =
    (double.inr I M) '' (I.boundary M) := by
  exact glued_range_inl_intersect_inr''
        (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_image_inl_interior :
    (double.inl I M) '' (I.interior M) = (range (double.inr I M))ᶜ := by
  rw [← compl_boundary]
  exact glued_image_inl_complement (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem isOpen_double_inl_interior [HasInvarianceOfDomain E] :
    IsOpen ((double.inl I M) '' (I.interior M)) := by
  rw [double_image_inl_interior]
  apply isOpen_compl_iff.mpr
  exact (isClosedEmbedding_double_inr I M).isClosed_range

theorem double_image_inr_interior :
    (double.inr I M) '' (I.interior M) = (range (double.inl I M))ᶜ := by
  rw [← compl_boundary]
  exact glued_image_inr_complement (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem isOpen_double_inr_interior [HasInvarianceOfDomain E] :
    IsOpen ((double.inr I M) '' (I.interior M)) := by
  rw [double_image_inr_interior]
  apply isOpen_compl_iff.mpr
  exact (isClosedEmbedding_double_inl I M).isClosed_range

theorem double_trichotomy (x : double I M) :
    x ∈ (double.inl I M) '' (I.interior M) ∨ x ∈ (double.inr I M) '' (I.interior M) ∨
    x ∈ range (double.zero I M) := by
  rw [← compl_boundary]
  exact glued_trichotomy (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M)) x

theorem desc_surjective_double {X : TopCat} (h k : C(M, X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    (range h) ∪ (range k) = @univ X → Surjective (double.desc I M h k w) := by
  exact desc_surjective_glued (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M)) h k w

theorem inl_desc_double {X : TopCat} (h k : C(M, X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    CategoryStruct.comp (double.inl I M) (double.desc I M h k w) = TopCat.ofHom h := by
  exact inl_desc_glued (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M)) h k w

theorem inr_desc_double {X : TopCat} (h k : C(M, X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    CategoryStruct.comp (double.inr I M) (double.desc I M h k w) = TopCat.ofHom k := by
  exact inr_desc_glued (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M)) h k w

noncomputable def double_swap_morphism : double I M ⟶ double I M :=
  double.desc I M (TopCat.Hom.hom (double.inr I M))
                  (TopCat.Hom.hom (double.inl I M))
                  (Eq.symm (double.w I M))

theorem double_inl_swap_eq_inr :
   (double.inl I M) ≫ (double_swap_morphism I M) = double.inr I M := by
  exact inl_desc_double I M (TopCat.Hom.hom (double.inr I M))
    (TopCat.Hom.hom (double.inl I M)) (Eq.symm (double.w I M))

theorem double_inr_swap_eq_inl :
   (double.inr I M) ≫ (double_swap_morphism I M) = double.inl I M := by
  exact inr_desc_double I M (TopCat.Hom.hom (double.inr I M))
    (TopCat.Hom.hom (double.inl I M)) (Eq.symm (double.w I M))

theorem double_swap_involution :
    (double_swap_morphism I M) ≫ (double_swap_morphism I M) = 𝟙 (double I M) := by
  ext x
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply,
             TopCat.hom_id, ContinuousMap.id_apply]
  have : x ∈ univ := by trivial
  rw [← jointly_surjective_double] at this
  simp only [mem_union, mem_range] at this
  rcases this with (h | h) <;> (
    obtain ⟨y,hy⟩ := h
    rw [← hy]
    nth_rewrite 2 [← ContinuousMap.comp_apply]
    rw [← TopCat.hom_comp]
  )
  · rw [double_inl_swap_eq_inr, ← ContinuousMap.comp_apply,
        ← TopCat.hom_comp, double_inr_swap_eq_inl]
  · rw [double_inr_swap_eq_inl, ← ContinuousMap.comp_apply,
        ← TopCat.hom_comp, double_inl_swap_eq_inr]

noncomputable def double_swap : double I M ≃ₜ double I M where
  toFun := double_swap_morphism I M
  invFun := double_swap_morphism I M
  left_inv := by
    exact fun x ↦ congrFun
      (congrArg (DFunLike.coe ∘ TopCat.Hom.hom) (double_swap_involution I M)) x
  right_inv := by
    exact fun x ↦ congrFun
      (congrArg (DFunLike.coe ∘ TopCat.Hom.hom) (double_swap_involution I M)) x
  continuous_toFun := by
    exact (TopCat.Hom.hom (double_swap_morphism I M)).continuous
  continuous_invFun := by
    exact (TopCat.Hom.hom (double_swap_morphism I M)).continuous

theorem desc_injective_double {X : TopCat} (h k : C(M, X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom k) := by aesop_cat)
    (hInjh : Injective h) (hInjk : Injective k)
    (hBoundary : ∀ y z : M, (h y = k z → y ∈ I.boundary M)) :
    Injective (double.desc I M h k w) := by
  exact desc_injective_glued (I.boundary M) (I.boundary M)
        (Homeomorph.refl (I.boundary M)) h k w hInjh hInjk hBoundary

theorem desc_isClosedMap_double {X : TopCat} (h k : C(M, X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    IsClosedMap h → IsClosedMap k → IsClosedMap (double.desc I M h k w) := by
  exact desc_isClosedMap_glued (I.boundary M) (I.boundary M)
        (Homeomorph.refl (I.boundary M)) h k w

theorem double_inl_eq_inr {a b : M} (hab : (double.inl I M) a = (double.inr I M) b) :
    a ∈ I.boundary M ∧ a = b := by
  let x := (double.inl I M) a
  have : x ∈ range ((bdry_inc' I M) ≫ (double.inl I M)) := by
    rw [← double_range_inl_intersect_inr]
    apply mem_inter
    · exact mem_range_self a
    · rw [show x = (double.inr I M) b by exact hab]
      exact mem_range_self b
  obtain ⟨y, hy⟩ := this
  have hy' : ((bdry_inc' I M) ≫ (double.inr I M)) y = x := by rwa [← double.w]
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hy hy'
  rw [show x = (double.inr I M) b by exact hab] at hy'
  have hay : (bdry_inc' I M) y = a := by exact (injective_double_inl I M) hy
  constructor
  · rw [← range_bdry_inc' I M]
    apply mem_range.mpr
    use y
  · rw [(injective_double_inr I M) hy'] at hay
    exact Eq.symm hay

theorem double_inl_preimage_range_inr :
    (double.inl I M) ⁻¹' (range (double.inr I M)) = I.boundary M := by
  exact glued_inl_preimage_range_inr
        (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_inr_preimage_range_inl :
    (double.inr I M) ⁻¹' (range (double.inl I M)) = I.boundary M := by
  exact glued_inr_preimage_range_inl
        (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_inl_preimage_inr_interior :
    (double.inl I M) ⁻¹' ((double.inr I M) '' (I.interior M)) = ∅ := by
  rw [← compl_boundary]
  exact glued_inl_preimage_inr_complement
        (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_inr_preimage_inl_interior :
    (double.inr I M) ⁻¹' ((double.inl I M) '' (I.interior M)) = ∅ := by
  rw [← compl_boundary]
  exact glued_inr_preimage_inl_complement
        (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem double_inl_eq_inr_of_boundary {a : M} (ha : a ∈ I.boundary M) :
    (double.inl I M) a = (double.inr I M) a := by
  rw [show a = (bdry_inc' I M) ⟨a,ha⟩ by rfl,
      ← ContinuousMap.comp_apply, ← ContinuousMap.comp_apply]
  apply congrFun
  exact congrArg DFunLike.coe <| congrArg ConcreteCategory.hom <| double.w I M

theorem double_interior_range_inl [HasInvarianceOfDomain E] :
    interior (range (double.inl I M)) = (double.inl I M) '' (I.interior M) := by
  apply Subset.antisymm_iff.mpr
  constructor <;> intro x hx
  · obtain ⟨U, hURange, hUOpen, hU⟩ := mem_interior.mp hx
    by_contra h
    have : x ∈ (double.inl I M) '' univ := by
      rw [image_univ]
      exact hURange hU
    have : x ∈ (double.inl I M) '' (I.boundary M) := by
      rw [← compl_interior]
      rw [← union_compl_self (I.interior M), image_union, mem_union] at this
      simp only [h, false_or] at this
      exact this
    obtain ⟨y, hyBdry, hyx⟩ := this
    rw [double_inl_eq_inr_of_boundary I M hyBdry] at hyx
    let V : Set M := (double.inr I M) ⁻¹' U
    have hyV : y ∈ V := by
      exact show (double.inr I M) y ∈ U by rwa [hyx]
    have : V ⊆ interior (closure (I.boundary M)) := by
      rw [closure_eq_iff_isClosed.mpr <| isClosed_boundary I M]
      apply (IsOpen.subset_interior_iff <| hUOpen.preimage (continuous_double_inr I M)).mpr
      rw [← double_inr_preimage_range_inl I M]
      exact fun _ ht ↦ hURange ht
    rw [isNowhereDense_boundary I M] at this
    exact this hyV
  · apply mem_interior.mpr
    use (double.inl I M) '' (I.interior M)
    exact ⟨image_subset_range (double.inl I M) (I.interior M),
           isOpen_double_inl_interior I M, hx⟩

theorem double_frontier_range_inl [HasInvarianceOfDomain E] :
    frontier (range (double.inl I M)) = (double.inl I M) '' (I.boundary M) := by
  rw [← closure_diff_interior, double_interior_range_inl,
        closure_eq_iff_isClosed.mpr (isClosedEmbedding_double_inl I M).isClosed_range,
      ← image_univ, ← image_diff (injective_double_inl I M),
      ← compl_eq_univ_diff, I.compl_interior]

theorem double_interior_range_inr [HasInvarianceOfDomain E] :
    interior (range (double.inr I M)) = (double.inr I M) '' (I.interior M) := by
  have hswap_inl_inr : (double_swap I M) ∘ (double.inl I M) = double.inr I M := by
    exact congrArg (DFunLike.coe ∘ ConcreteCategory.hom) <| double_inl_swap_eq_inr I M
  have : (double_swap I M) '' (range (double.inl I M)) = range (double.inr I M) := by
    rw [← image_univ, ← image_univ, ← image_comp]
    exact congrFun (congrArg image hswap_inl_inr) univ
  rw [← this, ← hswap_inl_inr, image_comp,
      ← (double_swap I M).image_interior (range (double.inl I M))]
  exact congrArg (image (double_swap I M)) <| double_interior_range_inl I M

theorem double_frontier_range_inr [HasInvarianceOfDomain E] :
    frontier (range (double.inr I M)) = (double.inr I M) '' (I.boundary M) := by
  rw [← closure_diff_interior, double_interior_range_inr,
        closure_eq_iff_isClosed.mpr (isClosedEmbedding_double_inr I M).isClosed_range,
      ← image_univ, ← image_diff (injective_double_inr I M),
      ← compl_eq_univ_diff, I.compl_interior]

noncomputable def double_inverse : (double I M) ⟶ (TopCat.of M) :=
  double.desc I M (Homeomorph.refl M) (Homeomorph.refl M) rfl

theorem double_left_inv_inl : LeftInverse (double_inverse I M) (double.inl I M) := by
  intro x
  simp only [double_inverse]
  rw [← ContinuousMap.comp_apply, ← TopCat.hom_comp,
      inl_desc_double I M (X := TopCat.of M) (Homeomorph.refl M) (Homeomorph.refl M) rfl]
  rfl

theorem double_left_inv_inr : LeftInverse (double_inverse I M) (double.inr I M) := by
  intro x
  simp only [double_inverse]
  rw [← ContinuousMap.comp_apply, ← TopCat.hom_comp,
      inr_desc_double I M (X := TopCat.of M) (Homeomorph.refl M) (Homeomorph.refl M) rfl]
  rfl

theorem double_unique_preimage (x : double I M) :
    ∃! t : M, (double.inl I M) t = x ∨ (double.inr I M) t = x := by
  have h : x ∈ univ := by trivial
  rw [← jointly_surjective_double I M, mem_union, ← image_univ, ← image_univ] at h
  rcases h with (hh|hh) <;>
      ( obtain ⟨y,_,hy⟩ := hh
        use y )
  · constructor
    · left; exact hy
    · intro z hz; rw [← hy] at hz
      cases hz with
      | inl hh => exact (injective_double_inl I M) hh
      | inr hh => exact Eq.symm (double_inl_eq_inr I M (Eq.symm hh)).2
  · constructor
    · right; exact hy
    · intro z hz; rw [← hy] at hz
      cases hz with
      | inl hh => exact (double_inl_eq_inr I M hh).2
      | inr hh => exact (injective_double_inr I M) hh

theorem not_surjective_double_inl :
    Nonempty (I.interior M) → ¬ Surjective (double.inl I M) := by
  intro hInt
  obtain ⟨x,hx⟩ := by exact nonempty_subtype.mp hInt
  by_contra h
  obtain ⟨y, hy⟩ := by exact h ((double.inr I M) x)
  obtain ⟨hBoundary, hyx⟩ := by exact double_inl_eq_inr I M hy
  rw [hyx, ← ModelWithCorners.compl_interior] at hBoundary
  exact hBoundary hx

theorem not_surjective_double_inr :
    Nonempty (I.interior M) → ¬ Surjective (double.inr I M) := by
  intro hInt
  obtain ⟨x,hx⟩ := by exact nonempty_subtype.mp hInt
  by_contra h
  obtain ⟨y, hy⟩ := by exact h ((double.inl I M) x)
  obtain ⟨hBoundary, hyx⟩ := by exact double_inl_eq_inr I M (Eq.symm hy)
  rw [← ModelWithCorners.compl_interior] at hBoundary
  exact hBoundary hx

theorem nonempty_boundary_of_connected_double [HasInvarianceOfDomain E] :
    Nonempty (I.interior M) → ConnectedSpace (double I M) → Nonempty (I.boundary M) := by
  intro hM hConn
  apply connectedSpace_iff_univ.mp at hConn
  by_contra h
  apply not_nonempty_iff.mp at h
  haveI : Nonempty M := by use (Classical.choice hM).val
  have : ¬ IsConnected (@univ (double I M)) := by
    by_contra h'
    obtain ⟨_, hIP⟩ := h'
    apply isPreconnected_closed_iff.mp at hIP
    have hUniv_subset : univ ⊆ range (double.inl I M) ∪ range (double.inr I M) := by
      simp only [univ_subset_iff]
      exact jointly_surjective_double I M
    obtain h'' := hIP (range (double.inl I M)) (range (double.inr I M))
                      (isClosedEmbedding_double_inl I M).isClosed_range
                      (isClosedEmbedding_double_inr I M).isClosed_range
                      hUniv_subset
    simp [univ_inter] at h''
    have hNonempty : (range (double.inl I M)) ∩ (range (double.inr I M)) ≠ ∅ := by
      apply nonempty_iff_ne_empty.mp
      exact h'' (range_nonempty (double.inl I M)) (range_nonempty (double.inr I M))
    have hEmpty : range (double.inl I M) ∩ range (double.inr I M) = ∅ := by
      rw [double_range_inl_intersect_inr I M]
      exact range_eq_empty ((bdry_inc' I M) ≫ (double.inl I M))
    exact hNonempty hEmpty
  exact this hConn

theorem nonempty_iff_nonempty_double : Nonempty M ↔ Nonempty (double I M) := by
  have : Nonempty M ↔ Nonempty M ∨ Nonempty M := by
    exact Iff.symm (or_iff_left_of_imp fun a ↦ a)
  apply Iff.trans this
  exact nonempty_iff_nonempty_glued (I.boundary M) (I.boundary M) (Homeomorph.refl (I.boundary M))

theorem connected_of_connected_double [HasInvarianceOfDomain E] :
    ConnectedSpace (double I M) → ConnectedSpace M := by
  intro hConn
  apply connectedSpace_iff_univ.mpr
  constructor
  · apply nonempty_iff_univ_nonempty.mp
    have : Nonempty (double I M) := by exact ConnectedSpace.toNonempty
    obtain x : double I M := this.some
    have : x ∈ range (double.inl I M) ∨ x ∈ range (double.inr I M) := by
      rw [← mem_union, jointly_surjective_double I M]; trivial
    simp only [mem_range] at this
    obtain ⟨y,_⟩ | ⟨y,_⟩ := this <;> use y
  · intro U V hUOpen hVOpen hUniv hUNonempty hVNonempty
    simp_all only [univ_inter]
    by_contra hUV

    have is_complement {X : Type u} {U V : Set X}
        (hU : univ ⊆ U ∪ V) (hI : U ∩ V = ∅) : U = Vᶜ := by
      simp only [univ_subset_iff] at hU
      ext x
      constructor <;> intro hx
      · by_contra h
        have : x ∈ (∅ : Set X) := by rw [← hI]; exact ⟨hx, not_notMem.mp h⟩
        exact h fun a ↦ h fun a ↦ this
      · have : x ∈ U ∪ V := by rw [hU]; trivial
        simp only [mem_union] at this
        simp_all only [mem_compl_iff, or_false]

    have hUVc : U = Vᶜ := by
      exact is_complement hUniv (not_nonempty_iff_eq_empty.mp hUV)

    have hUClosed : IsClosed U := by
      rw [hUVc]; exact isClosed_compl_iff.mpr hVOpen
    have hVClosed : IsClosed V := by
      apply isOpen_compl_iff.mp; rwa [← hUVc]
    let sU : Set (double I M) := ((double.inl I M) '' U) ∪ ((double.inr I M) '' U)
    let sV : Set (double I M) := ((double.inl I M) '' V) ∪ ((double.inr I M) '' V)
    have hsU_Nonempty : Nonempty sU := by
      apply Nonempty.to_subtype
      apply Nonempty.inl
      use (double.inl I M) hUNonempty.some
      exact mem_image_of_mem (double.inl I M) hUNonempty.some_mem
    have hsV_Nonempty : Nonempty sV := by
      apply Nonempty.to_subtype
      apply Nonempty.inl
      use (double.inl I M) hVNonempty.some
      exact mem_image_of_mem (double.inl I M) hVNonempty.some_mem

    obtain hlCE := isClosedEmbedding_double_inl I M
    obtain hrCE := isClosedEmbedding_double_inr I M
    have hsUClosed : IsClosed sU := by
      apply IsClosed.union
      · exact hlCE.isClosed_iff_image_isClosed.mp hUClosed
      · exact hrCE.isClosed_iff_image_isClosed.mp hUClosed
    have hsVClosed : IsClosed sV := by
      apply IsClosed.union
      · exact hlCE.isClosed_iff_image_isClosed.mp hVClosed
      · exact hrCE.isClosed_iff_image_isClosed.mp hVClosed

    have hCover : univ ⊆ sU ∪ sV := by
      intro x hx
      rw [← jointly_surjective_double I M] at hx
      simp only [mem_union] at hx ⊢
      simp only [univ_subset_iff] at hUniv
      rw [← image_univ, ← image_univ, ← hUniv] at hx
      cases hx with
      | inl h =>
        simp only [image_union, mem_union] at h
        cases h with
        | inl h' => left; exact mem_union_left ((double.inr I M) '' U) h'
        | inr h' => right; exact mem_union_left ((double.inr I M) '' V) h'
      | inr h =>
        simp only [image_union, mem_union] at h
        cases h with
        | inl h' => left; exact mem_union_right ((double.inl I M) '' U) h'
        | inr h' => right; exact mem_union_right ((double.inl I M) '' V) h'

    have simultaneous_preimages {A B : Set M} {f g : C(M, double I M)}
        (h : ¬ ((f '' A) ∩ (g '' B) = ∅)) :
        ∃ y z : M, y ∈ A ∧ z ∈ B ∧ f y = g z := by
      obtain hx := (nonempty_iff_ne_empty'.mpr h).some
      let x : double I M := hx
      have hxf : x ∈ f '' A := by
        exact mem_of_mem_inter_left <| Subtype.coe_prop hx
      have hxg : x ∈ g '' B := by
        exact mem_of_mem_inter_right <| Subtype.coe_prop hx
      simp only [mem_image] at hxf hxg
      obtain ⟨y, hyA, hyx⟩ := hxf
      obtain ⟨z, hzB, hzx⟩ := hxg
      rw [← hzx] at hyx
      use y, z

    have hDisjoint : sU ∩ sV = ∅ := by
      rw [inter_union_distrib_left, union_inter_distrib_right, union_inter_distrib_right]
      simp only [union_empty_iff]
      constructor
      · constructor <;> by_contra h
        · obtain ⟨y,z,hyU,hzV,hyz⟩ := simultaneous_preimages h
          rw [(injective_double_inl I M) hyz] at hyU
          exact hUV <| nonempty_of_mem ⟨hyU, hzV⟩
        · obtain ⟨y,z,hyU,hzV,hyz⟩ := simultaneous_preimages h
          obtain ⟨_, hzy⟩ := double_inl_eq_inr I M (Eq.symm hyz)
          rw [hzy] at hzV
          exact hUV <| nonempty_of_mem ⟨hyU, hzV⟩
      · constructor <;> by_contra h
        · obtain ⟨y,z,hyU,hzV,hyz⟩ := simultaneous_preimages h
          obtain ⟨_, hzy⟩ := double_inl_eq_inr I M hyz
          rw [hzy] at hyU
          exact hUV <| nonempty_of_mem ⟨hyU, hzV⟩
        · obtain ⟨y,z,hyU,hzV,hyz⟩ := simultaneous_preimages h
          rw [(injective_double_inr I M) hyz] at hyU
          exact hUV <| nonempty_of_mem ⟨hyU, hzV⟩

    have hsUsVc : sU = sVᶜ := by
      exact is_complement hCover hDisjoint
    have hsUOpen : IsOpen sU := by
      rw [hsUsVc]; exact IsClosed.isOpen_compl
    have hsVOpen : IsOpen sV := by
      apply isClosed_compl_iff.mp; rwa [← hsUsVc]
    rw [← univ_inter (sU ∩ sV)] at hDisjoint

    have hPreconnected : IsPreconnected (@univ (double I M)) := by
      exact isPreconnected_univ
    obtain hP := isPreconnected_iff_subset_of_disjoint.mp hPreconnected
                 sU sV hsUOpen hsVOpen hCover hDisjoint
    simp only [univ_subset_iff] at hP
    cases hP with
    | inl h =>
      rw [h] at hsUsVc
      have : ¬ Nonempty sV := by
        apply not_nonempty_iff_eq_empty'.mpr
        exact compl_univ_iff.mp (Eq.symm hsUsVc)
      exact this hsV_Nonempty
    | inr h =>
      rw [h, compl_univ] at hsUsVc
      exact (not_nonempty_iff_eq_empty'.mpr hsUsVc) hsU_Nonempty

noncomputable def double_homeomorph [HasInvarianceOfDomain E] {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H X] [ChartedSpace H Y]
    (φ : X ≃ₜ Y) : double I X ≃ₜ double I Y := by
  let i₁ : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom φ
  let i₂ : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom φ
  let f := bdry_inc' I X
  let g := bdry_inc' I Y
  let fX : pushout f f ≅ double I X := by exact Iso.refl (pushout f f)
  let gY : pushout g g ≅ double I Y := by exact Iso.refl (pushout g g)

  let φ' : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom φ
  have : IsIso φ' := by
    apply (TopCat.isIso_iff_isHomeomorph φ').mpr
    simp_all only [TopCat.hom_ofHom, ContinuousMap.coe_coe, φ']
    exact Homeomorph.isHomeomorph φ

  let φbdry' : TopCat.of (I.boundary X) ⟶ TopCat.of (I.boundary Y) :=
    TopCat.ofHom (homeomorph_boundary I φ)
  have : IsIso φbdry' := by
    apply (TopCat.isIso_iff_isHomeomorph φbdry').mpr
    simp_all only [TopCat.hom_ofHom, ContinuousMap.coe_coe, φbdry']
    exact Homeomorph.isHomeomorph (homeomorph_boundary I φ)

  have hComm : CategoryStruct.comp f φ' = CategoryStruct.comp φbdry' g := by
    simp_all only [f, g, φbdry']; rfl

  let ψ := pushout.map f f g g φ' φ' φbdry' hComm hComm
  haveI : IsIso ψ := by
    exact pushout.map_isIso f f g g φ' φ' φbdry' hComm hComm
  let ψ₀ : double I X ⟶ double I Y :=
    CategoryStruct.comp fX.inv <| CategoryStruct.comp ψ gY.hom
  have hIso : IsIso ψ₀ := by
    apply IsIso.comp_isIso
  exact TopCat.homeoOfIso (asIso ψ₀)

theorem isOpen_doubled {U : Set M} :
    IsOpen U → IsOpen (((double.inl I M) '' U) ∪ ((double.inr I M) '' U)) := by
  intro hUOpen
  let V : Set (double I M) := ((double.inl I M) '' U) ∪ ((double.inr I M) '' U)
  let inl := double.inl I M
  let inr := double.inr I M
  apply (double_isOpen_iff I M V).mpr
  have hInl : inl ⁻¹' V = U := by
    apply Subset.antisymm_iff.mpr
    constructor
    · rw [show V = (inl '' U) ∪ (inr '' U) by rfl, preimage_union]
      apply union_subset
      · rw [preimage_image_eq U (injective_double_inl I M)]
      · rintro x ⟨y,hy,hrl⟩
        rwa [← (double_inl_eq_inr I M (Eq.symm hrl)).2] at hy
    · exact fun ⦃a⦄ b ↦ subset_union_left ((subset_preimage_image inl U) b)
  have hInr : inr ⁻¹' V = U := by
    apply Subset.antisymm_iff.mpr
    constructor
    · rw [show V = (inl '' U) ∪ (inr '' U) by rfl, preimage_union]
      apply union_subset
      · rintro x ⟨y,hy,hrl⟩
        rwa [(double_inl_eq_inr I M hrl).2] at hy
      · rw [preimage_image_eq U (injective_double_inr I M)]
    · exact fun ⦃a⦄ b ↦ subset_union_right ((subset_preimage_image inr U) b)
  exact ⟨by rwa [hInl], by rwa [hInr]⟩

end Double

namespace Completion
open Gluing

variable
  (I : ModelWithCorners 𝕜 E H)
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

-- The inclusion map from ∂M × [0,∞) into the completion
def tail_inclusion : C(I.boundary M, (I.boundary M) × Iic (0:ℝ)) :=
  ContinuousMap.prodMk (α := I.boundary M)
    (ContinuousMap.id (α := I.boundary M))
    (ContinuousMap.const (α := I.boundary M) ⟨0, by exact right_mem_Iic⟩)

def tail_inc' : (TopCat.of (I.boundary M)) ⟶ (TopCat.of ((I.boundary M) × Iic (0:ℝ))) :=
  TopCat.ofHom (tail_inclusion I M)

private def tail_bdry : Set ((I.boundary M) × Iic (0:ℝ)) :=
  ((@univ (I.boundary M)) ×ˢ {⟨0, right_mem_Iic⟩})

private lemma isClosed_tail_bdry : IsClosed (tail_bdry I M) := by
  apply IsClosed.prod isClosed_univ isClosed_singleton

private lemma compl_tail_bdry :
    (tail_bdry I M)ᶜ = ((@univ (I.boundary M)) ×ˢ {⟨0, right_mem_Iic⟩}ᶜ) := by
  simp only [tail_bdry]
  ext x
  simp_all only [mem_compl_iff, mem_prod, mem_univ, mem_singleton_iff, true_and]

private def completion_gluing : Homeomorph (I.boundary M) (tail_bdry I M) where
  toFun := fun x ↦ ⟨(x,⟨0, right_mem_Iic⟩), by exact mk_mem_prod trivial rfl⟩
  invFun := fun y ↦ y.1.1
  left_inv := by intro x; simp only
  right_inv := by
    intro ⟨⟨x1,⟨x2,x2prop⟩⟩, xprop⟩
    simp only [tail_bdry] at xprop
    simp_all only
    simp_all only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
    simp_all only [mem_prod, mem_univ, mem_singleton_iff, Subtype.mk.injEq, true_and]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private lemma range_tail_inclusion :
    range (tail_inclusion I M) = tail_bdry I M := by
  apply Subset.antisymm_iff.mpr
  constructor <;> intro x ⟨y, hy⟩
  · simp [tail_inclusion] at hy
    simp only [tail_bdry, mem_prod, mem_univ, mem_singleton_iff, true_and]
    rw [← hy]
  · simp [tail_inclusion]
    use x.1
    simp only [Subtype.coe_eta, Subtype.coe_prop, exists_const, mem_singleton_iff] at hy ⊢
    exact congrArg (Prod.mk x.1) (Eq.symm hy)

private theorem tail_inclusion.isEmbedding : IsEmbedding (tail_inclusion I M) := by
  apply isEmbedding_prodMkLeft

private theorem tail_inclusion.injective : Injective (tail_inclusion I M) := by
  exact ((isEmbedding_iff (tail_inclusion I M)).mp
         (tail_inclusion.isEmbedding I M)).2

private theorem tail_inclusion.isClosedEmbedding :
    IsClosedEmbedding (tail_inclusion I M) := by
  apply (isClosedEmbedding_iff (tail_inclusion I M)).mpr
  constructor
  · exact tail_inclusion.isEmbedding I M
  · rw [range_tail_inclusion I M]
    exact isClosed_tail_bdry I M

noncomputable def completion_cocone : PushoutCocone (bdry_inc' I M) (tail_inc' I M) :=
  glued_cocone (I.boundary M) (tail_bdry I M) (completion_gluing I M)

noncomputable def completion : TopCat := (completion_cocone I M).pt

noncomputable def completion.inl : (TopCat.of M) ⟶ (completion I M) :=
  (completion_cocone I M).inl

noncomputable def completion.inr : TopCat.of ((I.boundary M) × (Iic (0:ℝ))) ⟶ (completion I M) :=
  (completion_cocone I M).inr

noncomputable def completion.zero : (TopCat.of (I.boundary M)) ⟶ (completion I M) :=
  (bdry_inc' I M) ≫ (completion.inl I M)

noncomputable def completion.desc {X : TopCat}
    (h : C(M, X)) (k : C((I.boundary M) × (Iic (0 : ℝ)), X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (tail_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    (completion I M) ⟶ X :=
  glued.desc (I.boundary M) (tail_bdry I M) (completion_gluing I M) h k w

theorem completion.w :
    CategoryStruct.comp (bdry_inc' I M) (completion.inl I M) =
    CategoryStruct.comp (tail_inc' I M) (completion.inr I M) := by
  exact glued.w (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem completion_isOpen_iff (U : Set (completion I M)) :
    IsOpen U ↔ IsOpen ((completion.inl I M) ⁻¹' U) ∧ IsOpen ((completion.inr I M) ⁻¹' U) := by
  exact glued_isOpen_iff (I.boundary M) (tail_bdry I M) (completion_gluing I M) U

theorem completion_isClosed_iff (U : Set (completion I M)) :
    IsClosed U ↔   IsClosed ((completion.inl I M) ⁻¹' U)
                 ∧ IsClosed ((completion.inr I M) ⁻¹' U) := by
  exact glued_isClosed_iff (I.boundary M) (tail_bdry I M) (completion_gluing I M) U

theorem T2_completion_of_T2 [HasInvarianceOfDomain E] :
    T2Space M → T2Space (completion I M) := by
  intro hM
  have hTail : T2Space ((I.boundary M) × (Iic (0 : ℝ))) := by exact Prod.t2Space
  exact T2_glued_of_T2 (I.boundary M) (tail_bdry I M) (completion_gluing I M) hM hTail
        (I.isClosed_boundary M) (isClosed_tail_bdry I M)

theorem jointly_surjective_completion :
    range (completion.inl I M) ∪ range (completion.inr I M) = @univ (completion I M) := by
  exact jointly_surjective_glued (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem continuous_completion_inl : Continuous (completion.inl I M) := by
  exact (ConcreteCategory.hom <| completion.inl I M).continuous

theorem isEmbedding_completion_inl : IsEmbedding (completion.inl I M) := by
  exact isEmbedding_glued_inl (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem isClosedEmbedding_completion_inl :
    IsClosedEmbedding (completion.inl I M) := by
  exact isClosedEmbedding_glued_inl (I.boundary M) (tail_bdry I M) (completion_gluing I M)
        (isClosed_tail_bdry I M)

theorem isInducing_completion_inl : IsInducing (completion.inl I M) := by
  exact isInducing_glued_inl (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem injective_completion_inl : Injective (completion.inl I M) := by
  exact injective_glued_inl (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem continuous_completion_inr : Continuous (completion.inr I M) := by
  exact (ConcreteCategory.hom <| completion.inr I M).continuous

theorem isEmbedding_completion_inr : IsEmbedding (completion.inr I M) := by
  exact isEmbedding_glued_inr (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem isInducing_completion_inr : IsInducing (completion.inr I M) := by
  exact isInducing_glued_inr (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem isClosedEmbedding_completion_inr [HasInvarianceOfDomain E] :
    IsClosedEmbedding (completion.inr I M) := by
  exact isClosedEmbedding_glued_inr (I.boundary M) (tail_bdry I M) (completion_gluing I M)
        (I.isClosed_boundary M)

theorem injective_completion_inr : Injective (completion.inr I M) := by
   exact injective_glued_inr (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem continuous_completion_zero : Continuous (completion.zero I M) := by
  exact (ConcreteCategory.hom <| completion.zero I M).continuous

theorem isEmbedding_completion_zero : IsEmbedding (completion.zero I M) := by
  exact isEmbedding_glued_zero (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem isClosedEmbedding_completion_zero [HasInvarianceOfDomain E] :
    IsClosedEmbedding (completion.zero I M) := by
  exact isClosedEmbedding_glued_zero (I.boundary M) (tail_bdry I M) (completion_gluing I M)
        (I.isClosed_boundary M) (isClosed_tail_bdry I M)

theorem isInducing_completion_zero : IsInducing (completion.zero I M) := by
  exact isInducing_glued_zero (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem injective_completion_zero : Injective (completion.zero I M) := by
  exact injective_glued_zero (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem completion_range_inl_intersect_inr :
    (range (completion.inl I M)) ∩ (range (completion.inr I M)) =
    range ((bdry_inc' I M) ≫ (completion.inl I M)) := by
  exact glued_range_inl_intersect_inr (I.boundary M) (tail_bdry I M) (completion_gluing I M)

lemma completion_inl_locus_eq_inr_locus :
    (completion.inl I M) '' (I.boundary M) =
    (completion.inr I M) '' (((@univ (I.boundary M)) ×ˢ {⟨0, right_mem_Iic⟩})) := by
  exact glued_inl_locus_eq_inr_locus (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem completion_range_inl_intersect_inr' :
    (range (completion.inl I M)) ∩ (range (completion.inr I M)) =
     (completion.inl I M) '' (I.boundary M) := by
  exact glued_range_inl_intersect_inr' (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem completion_range_inl_intersect_inr'' :
    (range (completion.inl I M)) ∩ (range (completion.inr I M)) =
    (completion.inr I M) '' ((@univ (I.boundary M)) ×ˢ {⟨0, right_mem_Iic⟩}) := by
  exact glued_range_inl_intersect_inr'' (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem completion_image_inl_interior :
    (completion.inl I M) '' (I.interior M) = (range (completion.inr I M))ᶜ := by
  rw [← compl_boundary]
  exact glued_image_inl_complement (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem isOpen_completion_inl_interior [HasInvarianceOfDomain E] :
    IsOpen ((completion.inl I M) '' (I.interior M)) := by
  rw [completion_image_inl_interior]
  apply isOpen_compl_iff.mpr
  exact (isClosedEmbedding_completion_inr I M).isClosed_range

theorem completion_image_inr_interior :
    (completion.inr I M) '' ((@univ (I.boundary M)) ×ˢ {⟨0, right_mem_Iic⟩}ᶜ) =
    (range (completion.inl I M))ᶜ := by
  rw [← compl_tail_bdry I M]
  exact glued_image_inr_complement (I.boundary M) (tail_bdry I M) (completion_gluing I M)

theorem isOpen_completion_inr_interior :
    IsOpen ((completion.inr I M) '' ((@univ (I.boundary M)) ×ˢ {⟨0, right_mem_Iic⟩}ᶜ)) := by
  rw [completion_image_inr_interior]
  apply isOpen_compl_iff.mpr
  exact (isClosedEmbedding_completion_inl I M).isClosed_range

theorem completion_trichotomy (x : completion I M) :
    x ∈ (completion.inl I M) '' (I.interior M) ∨
    x ∈ (completion.inr I M) '' ((@univ (I.boundary M)) ×ˢ {⟨0, right_mem_Iic⟩}ᶜ) ∨
    x ∈ range (completion.zero I M) := by
  rw [← compl_boundary, ← compl_tail_bdry I M]
  exact glued_trichotomy (I.boundary M) (tail_bdry I M) (completion_gluing I M) x

theorem desc_surjective_completion {X : TopCat}
    (h : C(M, X)) (k : C((I.boundary M) × (Iic (0 : ℝ)), X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (tail_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    (range h) ∪ (range k) = @univ X → Surjective (completion.desc I M h k w) := by
  exact desc_surjective_glued (I.boundary M) (tail_bdry I M) (completion_gluing I M) h k w

theorem inl_desc_completion {X : TopCat}
    (h : C(M, X)) (k : C((I.boundary M) × (Iic (0 : ℝ)), X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (tail_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    CategoryStruct.comp (completion.inl I M) (completion.desc I M h k w)
    = TopCat.ofHom h := by
  exact inl_desc_glued (I.boundary M) (tail_bdry I M) (completion_gluing I M) h k w

theorem inr_desc_completion {X : TopCat}
    (h : C(M, X)) (k : C((I.boundary M) × (Iic (0 : ℝ)), X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (tail_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    CategoryStruct.comp (completion.inr I M) (completion.desc I M h k w)
    = TopCat.ofHom k := by
  exact inr_desc_glued (I.boundary M) (tail_bdry I M) (completion_gluing I M) h k w

theorem desc_injective_completion {X : TopCat}
    (h : C(M, X)) (k : C((I.boundary M) × (Iic (0 : ℝ)), X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (tail_inc' I M) (TopCat.ofHom k) := by aesop_cat)
    (hInjh : Injective h) (hInjk : Injective k)
    (hBoundary : ∀ y : M, ∀ z : (I.boundary M) × (Iic (0 : ℝ)),
                (h y = k z → y ∈ I.boundary M)) :
    Injective (completion.desc I M h k w) := by
  exact desc_injective_glued (I.boundary M) (tail_bdry I M) (completion_gluing I M)
        h k w hInjh hInjk hBoundary

theorem desc_isClosedMap_completion {X : TopCat}
    (h : C(M, X)) (k : C((I.boundary M) × (Iic (0 : ℝ)), X))
    (w : CategoryStruct.comp (bdry_inc' I M) (TopCat.ofHom h)
       = CategoryStruct.comp (tail_inc' I M) (TopCat.ofHom k) := by aesop_cat) :
    IsClosedMap h → IsClosedMap k → IsClosedMap (completion.desc I M h k w) := by
  exact desc_isClosedMap_glued (I.boundary M) (tail_bdry I M) (completion_gluing I M) h k w

theorem connected_completion_of_connected :
    ConnectedSpace M → ConnectedSpace (completion I M) := by
  intro hM
  have : Nonempty M := by exact hM.toNonempty
  let x : completion I M := (completion.inl I M) hM.toNonempty.some
  have hx : x ∈ range (completion.inl I M) := by
    exact mem_range_self ConnectedSpace.toNonempty.some
  have hConn_inl : IsConnected (range (completion.inl I M)) := by
    rw [← image_univ]
    apply IsConnected.image (connectedSpace_iff_univ.mp hM)
    exact continuousOn_univ.mpr (TopCat.Hom.hom (completion.inl I M)).continuous

  have hTail : ∀ y ∈ range (completion.inr I M),
      connectedComponent x = connectedComponent y := by
    intro y ⟨z,hz⟩
    let Ctail : Set ((I.boundary M) × (Iic (0 : ℝ))) :=
      (connectedComponent z.1) ×ˢ univ
    let z' : (I.boundary M) × (Iic (0 : ℝ)) := (z.1, ⟨0, right_mem_Iic⟩)
    have hzTail : z ∈ Ctail := by
      exact mem_prod.mpr ⟨mem_connectedComponent, by trivial⟩
    have hz'Tail : z' ∈ Ctail := by
      exact mem_prod.mpr ⟨mem_connectedComponent, by trivial⟩
    have hCtail : IsConnected Ctail := by
      apply IsConnected.prod isConnected_connectedComponent
      apply connectedSpace_iff_univ.mp <| Subtype.connectedSpace isConnected_Iic

    let y' : completion I M := (completion.inr I M) z'
    have : y ∈ connectedComponent y' := by
      have : IsConnected ((completion.inr I M) '' Ctail) := by
        apply IsConnected.image hCtail
        exact (TopCat.Hom.hom <| completion.inr I M).continuous.continuousOn
      have : (completion.inr I M) '' Ctail ⊆ connectedComponent y' := by
        exact this.subset_connectedComponent
              <| mem_image_of_mem (completion.inr I M) hz'Tail
      rw [← hz]
      exact this <| mem_image_of_mem (completion.inr I M) hzTail
    rw [← connectedComponent_eq this]

    have : y' ∈ range (completion.inl I M) := by
      have hy'inr : y' = ((completion.inr I M) ∘ (tail_inc' I M)) z.1 := by
        rw [comp_apply]
        simp only [y', z']
        apply congrArg (completion.inr I M)
        rfl
      apply mem_range.mpr
      use ((bdry_inc' I M) z.1)
      rw [← ConcreteCategory.comp_apply, hy'inr]
      apply congrFun ?_ z.1
      exact congrArg DFunLike.coe <| congrArg ConcreteCategory.hom <| completion.w I M
    exact connectedComponent_eq <| hConn_inl.subset_connectedComponent hx this

  apply connectedSpace_iff_connectedComponent.mpr
  use x
  apply univ_subset_iff.mp
  intro w hw
  rw [← jointly_surjective_completion I M] at hw
  simp only [mem_union] at hw
  cases hw with
  | inl hl => exact (hConn_inl.subset_connectedComponent hx) hl
  | inr hr => exact connectedComponent_eq_iff_mem.mp <| Eq.symm <| hTail w hr

theorem nonempty_iff_nonempty_completion :
    (Nonempty M) ↔ Nonempty (completion I M) := by
  have hrange : Nonempty M ↔ (range (completion.inl I M)).Nonempty := by
    exact Iff.symm range_nonempty_iff_nonempty
  constructor <;> intro h
  · apply hrange.mp at h; use h.some
  · apply nonempty_iff_univ_nonempty.mp at h
    rw [← jointly_surjective_completion I M] at h
    simp only [union_nonempty] at h
    cases h with
    | inl h' => exact range_nonempty_iff_nonempty.mp h'
    | inr h' => apply range_nonempty_iff_nonempty.mp at h'
                use (nonempty_prod.mp h').1.some.val

end Completion

/-
variable
  --(I : ModelWithCorners ℝ ℝ¹ (EuclideanHalfSpace 1))
  (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]

instance chartedSpaceULift (H : Type*) [TopologicalSpace H] :
    ChartedSpace H (ULift H) where
  atlas := {Homeomorph.ulift.toPartialHomeomorph}
  chartAt _ := Homeomorph.ulift.toPartialHomeomorph
  mem_chart_source x := mem_univ x
  chart_mem_atlas _ := mem_singleton _
-/

/-
open CategoryTheory TopCat

lemma L {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (φ : X ≃ₜ Y) : φ ≫ φ.symm = fun y ↦ y := by exact?

instance isIso_homeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (φ : X ≃ₜ Y) :
  CategoryTheory.Iso (TopCat.of X) (TopCat.of Y) where
    hom := TopCat.ofHom φ
    inv := TopCat.ofHom φ.symm
    hom_inv_id := by exact?

--universe v w w'
def pushout_ulift {X Y Z : TopCat} {f : X ⟶ Y} {g : X ⟶ Z} :
    (pushout.cocone (TopCat.uliftFunctor.map f) (TopCat.uliftFunctor.map g)).pt ≃ₜ
    ULift (pushout.cocone f g).pt := by
  --have : PreservesColimitsOfSize uliftFunctor := by sorry
  have : TopCat.uliftFunctor.comp (forget TopCat) ≅
      (forget TopCat).comp CategoryTheory.uliftFunctor := by
    exact uliftFunctorCompForgetIso

  have IP := IsPushout.of_hasPushout f g
  let W : TopCat := (pushout.cocone f g).pt
  let f' := TopCat.uliftFunctor.map f
  let g' := TopCat.uliftFunctor.map g
  let e₁ : X ≃ₜ TopCat.uliftFunctor.obj X := Homeomorph.ulift.symm
  let e₁': X ≅ (TopCat.uliftFunctor.obj X) :=
    TopCat.ofHom ⟨e₁.toFun, e₁.continuous_toFun⟩
  let e₂ : Y ≃ₜ ULift Y := Homeomorph.ulift.symm
  let e₂' : Y ⟶ (TopCat.uliftFunctor.obj Y) :=
    TopCat.ofHom ⟨e₂.toFun, e₂.continuous_toFun⟩
  let e₃ : Z ≃ₜ ULift Z := Homeomorph.ulift.symm
  let e₃' : Z ⟶ (TopCat.uliftFunctor.obj Z) :=
    TopCat.ofHom ⟨e₃.toFun, e₃.continuous_toFun⟩
  let e₄ : W ≃ₜ ULift W := Homeomorph.ulift.symm
  have commf : CategoryStruct.comp f e₂ = CategoryStruct.comp e₁ f' := by rfl

  have : IsPushout f' g' (TopCat.uliftFunctor.map (pushout.inl f g))
                         (TopCat.uliftFunctor.map (pushout.inr f g)) := by
    apply IsPushout.of_iso IP commf
    · rfl

  let F : WalkingSpan ⥤ TopCat := span f g
  let CC : Cocone F := pushout.cocone f g
  have hCC : IsColimit CC := by exact pushout.isColimit f g
    --exact Classical.choice hPushout.isColimit' -- is this really necessary?

  let G := TopCat.uliftFunctor
  let CC' : Cocone (F ⋙ G) := Functor.mapCocone G CC
  have : PreservesColimitsOfSize G := by
    exact CategoryTheory.Limits.Types.instPreservesColimitsOfSizeUliftFunctor
  have hCC' : Nonempty (IsColimit CC') := by
    --apply PreservesColimitsOfSize.preservesFiniteColimits G
    exact PreservesColimitsOfSize.preservesColimitsOfShape (F := TopCat.uliftFunctor)
    --CategoryTheory.Limits.isColimitOfPreserves G hCC
    --isColimitOfPreserves G hCC

  sorry
-/
