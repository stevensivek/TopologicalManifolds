/-
Copyright (c) 2025 Steven Sivek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sivek
-/
import Mathlib.Tactic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Adhesive

open Set Function Topology CategoryTheory CategoryTheory.Limits TopCat

namespace TopCat.IsPushout

theorem glued_surjective {X Y Z W : TopCat} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
    (hPushout : IsPushout f g h k) :
    ∀ w : W, (∃ y : Y, h y = w) ∨ (∃ y : Z, k y = w) := by
  let F : WalkingSpan ⥤ TopCat := span f g
  let CC : Cocone F := PushoutCocone.mk h k hPushout.w
  have hCC : IsColimit CC := by exact hPushout.isColimit'.some

  have jointly_surjective: ∀ w : W, ∃ j y, CC.ι.app j y = w := by
    let G := forget TopCat
    let CC' : Cocone (F ⋙ G) := Functor.mapCocone G CC
    have hCC' : IsColimit CC' := by exact isColimitOfPreserves G hCC
    have hSurj' : ∀ (w' : G.obj W), ∃ j y', CC'.ι.app j y' = w' := by
      exact fun w' ↦ Types.jointly_surjective_of_isColimit hCC' w'

    intro w
    let φ : G.obj W ≅ CC'.pt :=
      IsColimit.coconePointUniqueUpToIso hCC' hCC'
    have hιinv (j : WalkingSpan) : G.map (CC.ι.app j) = CC'.ι.app j ≫ φ.inv := by
      exact Eq.symm (IsColimit.comp_coconePointUniqueUpToIso_inv hCC' hCC' j)
    let w' : CC'.pt := φ.hom w
    obtain ⟨j, y', hw'⟩ := hSurj' w'
    use j, y'
    calc
      (G.map (CC.ι.app j)) y' = ((CC'.ι.app j) ≫ φ.inv) y' := by
        exact congrFun (hιinv j) y'
      _ = φ.inv w' := by rw [← hw']; rfl
      _ = w := by exact CategoryTheory.hom_inv_id_apply φ w

  intro x
  obtain ⟨j, y, hjy⟩ := jointly_surjective x
  match j with
  | some WalkingPair.left => left; use y; rw [← hjy]; apply congrArg; rfl
  | some WalkingPair.right => right; use y; rw [← hjy]; apply congrArg; rfl
  | none => left; use (f y); rwa [PushoutCocone.condition_zero CC] at hjy

theorem glued_surjective' {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    (range h) ∪ (range k) = @univ W := by
  apply univ_subset_iff.mp
  intro w _
  apply (mem_union w (range h) (range k)).mpr
  cases (glued_surjective hPushout w) with
  | inl h => left;  obtain ⟨y,_⟩ := h; apply mem_range.mpr; use y
  | inr h => right; obtain ⟨y,_⟩ := h; apply mem_range.mpr; use y

theorem desc_surjective_of_jointly_surjective {X Y Z W Ω : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k)
    (h' : Y ⟶ Ω) (k' : Z ⟶ Ω) (w : f ≫ h' = g ≫ k' := by aesop_cat) :
    (range h') ∪ (range k') = @univ Ω → Surjective (IsPushout.desc hPushout h' k' w) := by
  intro hsurj
  let IPdesc : W ⟶ Ω := IsPushout.desc hPushout h' k' w
  apply range_eq_univ.mp
  apply univ_subset_iff.mp
  have hl : range (h ≫ IPdesc) ⊆ range IPdesc := by exact range_comp_subset_range h IPdesc
  have hr : range (k ≫ IPdesc) ⊆ range IPdesc := by exact range_comp_subset_range k IPdesc
  rw [IsPushout.inl_desc hPushout h' k' w] at hl
  rw [IsPushout.inr_desc hPushout h' k' w] at hr
  rw [← hsurj]
  exact union_subset hl hr

private lemma pullback_find_preimage {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (y : Y)
    (hPushout : IsPushout f g h k) (hfInj : Injective f) :
    (h y ∈ range k) → ∃ x : X, f x = y := by
  intro hiy
  simp_all [mem_range]
  obtain ⟨z,hz⟩ := hiy
  let G := forget TopCat
  let inl' := G.map h
  let inr' := G.map k
  have IP : IsPullback (G.map f) (G.map g) (G.map h) (G.map k) := by
    apply (mono_iff_injective f).mpr at hfInj
    apply Adhesive.isPullback_of_isPushout_of_mono_left
    exact Functor.map_isPushout G hPushout
  let one_pt : Set Y := {y}
  let h' : (TopCat.of one_pt) ⟶ Y := TopCat.ofHom (ContinuousMap.const one_pt y)
  let k' : (TopCat.of one_pt) ⟶ Z := TopCat.ofHom (ContinuousMap.const one_pt z)
  have w : (G.map h') ≫ inl' = (G.map k') ≫ inr' := by aesop
  let liftW : (G.obj (TopCat.of one_pt)) ⟶ (G.obj X) := IP.lift (G.map h') (G.map k') w

  let a : one_pt := (instNonemptyOfInhabited (α := one_pt)).some
  use (liftW a)
  calc
    (TopCat.Hom.hom f) (liftW a) = (liftW ≫ (G.map f)) a := by rfl
    _ = (G.map h') a := by
      exact congrFun (IsPullback.lift_fst IP (G.map h') (G.map k') w) a
    _ = y := by rfl

lemma inl_mono_intersection_inl_inr {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    Injective f → (range h) ∩ (range k) = range (f ≫ h) := by
  intro hfInj
  ext w
  simp_all [mem_range]
  constructor <;> intro hw
  · obtain ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ := hw
    have : h y ∈ range k := by rw [hy, ← hz]; exact mem_range_self z
    obtain ⟨x, hx⟩ := pullback_find_preimage y hPushout hfInj this
    use x
    rw [hx, hy]
  · obtain ⟨y, hy⟩ := hw
    constructor
    · use f y
    · use g y
      rw [← ConcreteCategory.comp_apply, ← hPushout.w, ConcreteCategory.comp_apply, hy]

theorem glued_compact_of_compact {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    CompactSpace Y → CompactSpace Z → CompactSpace W := by
  intro hY hZ
  apply isCompact_univ_iff.mp
  rw [← glued_surjective' hPushout, ← image_univ, ← image_univ]
  apply isCompact_univ_iff.mpr at hY
  apply isCompact_univ_iff.mpr at hZ
  apply IsCompact.union
  · exact IsCompact.image hY <| ContinuousMap.continuous (TopCat.Hom.hom h)
  · exact IsCompact.image hZ <| ContinuousMap.continuous (TopCat.Hom.hom k)

theorem glued_isOpen_iff {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) (U : Set W) :
    IsOpen U ↔ (IsOpen (h ⁻¹' U)) ∧ (IsOpen (k ⁻¹' U)) := by
  let PC := PushoutCocone.mk h k hPushout.w
  have hPC : IsColimit PC := by exact hPushout.isColimit'.some
  rw [TopCat.isOpen_iff_of_isColimit PC hPC]
  constructor
  · exact fun hj ↦ ⟨hj (some WalkingPair.left), hj (some WalkingPair.right)⟩
  · intro hOpen j
    match j with
    | some WalkingPair.left => exact hOpen.left
    | some WalkingPair.right => exact hOpen.right
    | none =>
      rw [PushoutCocone.condition_zero PC]
      exact IsOpen.preimage (ContinuousMap.continuous (TopCat.Hom.hom f)) hOpen.left

theorem glued_isClosed_iff {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) (U : Set W) :
    IsClosed U ↔ (IsClosed (h ⁻¹' U)) ∧ (IsClosed (k ⁻¹' U)) := by
  haveI := glued_isOpen_iff hPushout Uᶜ
  simp_all only [preimage_compl, isOpen_compl_iff]

theorem glued_connected_of_connected {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    Nonempty X → ConnectedSpace Y → ConnectedSpace Z → ConnectedSpace W := by
  intro hX hY hZ
  apply connectedSpace_iff_univ.mp at hY
  apply connectedSpace_iff_univ.mp at hZ
  apply connectedSpace_iff_univ.mpr
  rw [← glued_surjective' hPushout, ← image_univ, ← image_univ]
  apply IsConnected.union
  · apply nonempty_def.mpr
    obtain ⟨x, _⟩ := by exact nonempty_def.mp (nonempty_iff_univ_nonempty.mp hX)
    use h (f x)
    refine mem_inter ?_ ?_ <;> simp only [image_univ, mem_range]
    · use f x
    · use g x; rw [← comp_app, ← comp_app, hPushout.w]
  · apply IsConnected.image hY h
    exact continuousOn_univ.mpr (ContinuousMap.continuous (TopCat.Hom.hom h))
  · apply IsConnected.image hZ k
    exact continuousOn_univ.mpr (ContinuousMap.continuous (TopCat.Hom.hom k))

private lemma forget_mono_of_injective {X Y : TopCat} {f : X ⟶ Y} :
    Injective f → Mono ((forget TopCat).map f) := by
  intro hf
  haveI : Mono f := by exact (TopCat.mono_iff_injective f).mpr hf
  haveI : Functor.PreservesMonomorphisms (forget TopCat) := by
    exact Functor.preservesMonomorphisms_of_isRightAdjoint (forget TopCat)
  exact Functor.map_mono (forget TopCat) f

theorem inr_injective_of_injective_left {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    Injective f → Injective k := by
  intro hf
  apply (mono_iff_injective k).mp
  apply (Functor.mono_map_iff_mono (forget TopCat) k).mp
  haveI : Mono ((forget TopCat).map f) := by exact forget_mono_of_injective hf
  apply Adhesive.mono_of_isPushout_of_mono_left (f := (forget TopCat).map f)
  apply Functor.map_isPushout
  exact hPushout

theorem inl_injective_of_injective_right {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    Injective g → Injective h := by
  exact inr_injective_of_injective_left <| IsPushout.flip_iff.mp hPushout

theorem zero_injective_of_injective {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    Injective f → Injective g → Injective (f ≫ h) := by
  intro hf hg
  haveI : Injective h := by exact inl_injective_of_injective_right hPushout hg
  simp_all only [hom_comp, ContinuousMap.coe_comp, Injective.of_comp_iff]

theorem desc_injective {X Y Z W Ω : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k)
    (h' : Y ⟶ Ω) (k' : Z ⟶ Ω) (w : f ≫ h' = g ≫ k' := by aesop_cat)
    (hInjf : Injective f) (hInjg : Injective g)
    (hInjh' : Injective h') (hInjk' : Injective k')
    (hRange_f : ∀ y : Y, ∀ z : Z, (h' y = k' z → y ∈ range f)) :
    Injective (hPushout.desc h' k' w) := by
  intro p q hpq
  have hInjh : Injective h := by exact inl_injective_of_injective_right hPushout hInjg
  have hInjk : Injective k := by exact inr_injective_of_injective_left hPushout hInjf
  rw [← hPushout.inl_desc h' k' w] at hInjh'
  let hInjk'' : Injective k' := by exact hInjk'
  rw [← hPushout.inr_desc h' k' w] at hInjk''
  simp only [TopCat.hom_comp, ContinuousMap.coe_comp] at hInjh' hInjk'
  let ψ : W ⟶ Ω := hPushout.desc h' k' w
  have hInj_inl : InjOn ψ (range h) := by exact Injective.injOn_range hInjh'
  have hInj_inr : InjOn ψ (range k) := by exact Injective.injOn_range hInjk''
  have inl_or_inr (w : W) : w ∉ range h → w ∈ range k := by
    intro hz
    haveI : w ∈ range h ∨ w ∈ range k := by
      rw [← mem_union, glued_surjective' hPushout]
      exact _root_.trivial
    simp_all only [mem_range, not_exists, exists_false, false_or]

  have hpq_equal {a b : W} :
      a ∈ range h → b ∈ range k →
      (hPushout.desc h' k' w) a = (hPushout.desc h' k' w) b → a = b := by
    intro ha hb hab
    obtain ⟨y,hy⟩ := mem_range.mp ha
    obtain ⟨z,hz⟩ := mem_range.mp hb
    have : y ∈ range f := by
      apply hRange_f y z
      rw [← hPushout.inl_desc h' k' w]
      nth_rewrite 2 [← hPushout.inr_desc h' k' w]
      simpa only [TopCat.hom_comp, ContinuousMap.comp_apply, hy, hz]
    obtain ⟨ω, hω⟩ := mem_range.mp this
    rw [← hy, ← hz, ← hω, ← ConcreteCategory.comp_apply, hPushout.w, ConcreteCategory.comp_apply]
    apply (Injective.eq_iff hInjk).mpr
    apply (Injective.eq_iff hInjk').mp
    rw [← ConcreteCategory.comp_apply, ← w, ConcreteCategory.comp_apply, hω]
    rw [← hPushout.inl_desc h' k' w]
    nth_rewrite 2 [← hPushout.inr_desc h' k' w]
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
    rwa [hy, hz]

  by_cases hp : p ∈ range h <;> by_cases hq : q ∈ range h
  · exact hInj_inl hp hq hpq
  · exact hpq_equal hp (inl_or_inr q hq) hpq
  · exact Eq.symm (hpq_equal hq (inl_or_inr p hp) (Eq.symm hpq))
  · exact hInj_inr (inl_or_inr p hp) (inl_or_inr q hq) hpq

theorem desc_isClosedMap {X Y Z W Ω : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k)
    (h' : Y ⟶ Ω) (k' : Z ⟶ Ω) (w : f ≫ h' = g ≫ k' := by aesop_cat) :
    IsClosedMap h' → IsClosedMap k' → IsClosedMap (hPushout.desc h' k' w) := by
  intro hhClosed hkClosed U hU
  let ψ : W ⟶ Ω := hPushout.desc h' k' w

  have hfimg : IsClosed ((h') '' (h ⁻¹' U)) := by
    apply hhClosed (h ⁻¹' U)
    exact IsClosed.preimage (ContinuousMap.continuous (TopCat.Hom.hom h)) hU

  have hgimg : IsClosed ((k') '' (k ⁻¹' U)) := by
    apply hkClosed (k ⁻¹' U)
    exact IsClosed.preimage (ContinuousMap.continuous (TopCat.Hom.hom k)) hU

  have : ψ '' U = ((h') '' (h ⁻¹' U)) ∪ ((k') '' (k ⁻¹' U)) := by
    have : U = (h '' (h ⁻¹' U)) ∪ (k '' (k ⁻¹' U)) := by
      ext x
      constructor <;> intro hx
      · have : x ∈ range h ∨ x ∈ range k := by
          rw [← mem_union, glued_surjective' hPushout]; trivial
        cases this with
        | inl hh => left; obtain ⟨y, hy⟩ := hh
                    rw [← hy]
                    exact mem_image_of_mem h <| by simp only [mem_preimage]; rwa [hy]
        | inr hh => right; obtain ⟨y, hy⟩ := hh
                    rw [← hy]
                    exact mem_image_of_mem k <| by simp only [mem_preimage]; rwa [hy]
      · have : h '' (h ⁻¹' U) ∪ k '' (k ⁻¹' U) ⊆ U := by
          nth_rewrite 3 [← union_self U]
          exact union_subset_union (image_preimage_subset h U) (image_preimage_subset k U)
        exact this hx
    have hU_union : ψ '' U = ψ '' (h '' (h ⁻¹' U)) ∪ ψ '' (k '' (k ⁻¹' U)) := by
      apply congrArg (fun V ↦ ψ '' V) at this
      rwa [image_union] at this
    rw [← image_comp, ← image_comp] at hU_union
    rw [show (ConcreteCategory.hom ψ) ∘ (ConcreteCategory.hom h) = h ≫ ψ by rfl,
        show (ConcreteCategory.hom ψ) ∘ (ConcreteCategory.hom k) = k ≫ ψ by rfl] at hU_union
    rw [hPushout.inl_desc h' k' w, hPushout.inr_desc h' k' w] at hU_union
    exact hU_union
  rw [this]
  exact IsClosed.union hfimg hgimg

-- The following is from Lemma 3.6 of https://ncatlab.org/nlab/show/subspace+topology#pushout.
private lemma inl_induce_right_induce {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsInducing f → IsInducing k := by
  intro hf
  have hfInduced (U : Set X) (hU : IsOpen U) : ∃ V : Set Y, IsOpen V ∧ f ⁻¹' V = U := by
    rw [hf.eq_induced (tX := X.str) (tY := Y.str)] at hU
    exact isOpen_induced_iff.mp hU

  -- want to show: every open in Z is the preimage of an open Ω ⊆ W
  have inrInduced (U : Set Z) (hU : IsOpen U) :
      ∃ Ω : Set W, IsOpen Ω ∧ U = k ⁻¹' Ω := by
    have : IsOpen (g ⁻¹' U) := by
      let g' : C(X, Z) := ConcreteCategory.hom g
      exact IsOpen.preimage (ContinuousMap.continuous g') hU
    obtain ⟨V, ⟨hV, hfVgU⟩⟩ := hfInduced (g ⁻¹' U) this

    let χUmap : Z → ULift Prop := fun z ↦ ULift.up (z ∈ U)
    have : Continuous χUmap := by
      exact Continuous.comp continuous_uliftUp (isOpen_iff_continuous_mem.mp hU)
    let χU : C(Z, ULift Prop) := ⟨χUmap, this⟩

    let χVmap : Y → ULift Prop := fun y ↦ ULift.up (y ∈ V)
    have : Continuous χVmap := by
      exact Continuous.comp continuous_uliftUp (isOpen_iff_continuous_mem.mp hV)
    let χV : C(Y, ULift Prop) := ⟨χVmap, this⟩

    have hComm : f ≫ (TopCat.ofHom χV) = g ≫ (TopCat.ofHom χU) := by
      apply ConcreteCategory.ext_apply
      simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply]
      intro x
      rw [show χV (f x) = ULift.up (x ∈ f⁻¹' V) by rfl,
          show χU (g x) = ULift.up (x ∈ g ⁻¹' U) by rfl, hfVgU]
    let poMorphism : W ⟶ TopCat.of (ULift Prop) :=
      IsPushout.desc hPushout (TopCat.ofHom χV) (TopCat.ofHom χU) hComm
    let poMorphism' : C(W, ULift Prop) := ConcreteCategory.hom poMorphism

    let Ω : Set W := poMorphism ⁻¹' {ULift.up True}
    have hΩopen : IsOpen Ω := by
      apply IsOpen.preimage (ContinuousMap.continuous poMorphism')
      have : IsOpen ((Homeomorph.ulift (X := Prop)).symm '' {True}) := by
        exact (Homeomorph.isOpenMap Homeomorph.ulift.symm) {True} isOpen_singleton_true
      rwa [image_singleton] at this

    have hUχ : U = χU ⁻¹' {ULift.up True} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor <;> intro hx
      · have : χU x = ULift.up (x ∈ U) := rfl
        rwa [eq_true hx] at this
      · simp_all only [ContinuousMap.coe_mk, ULift.up.injEq, χU, χUmap]

    have hU_as_preimage_Ω : U = k ⁻¹' Ω := by
      rw [show Ω = poMorphism ⁻¹' {ULift.up True} by rfl]
      have : k ≫ poMorphism = TopCat.ofHom χU := by
        exact IsPushout.inr_desc hPushout (TopCat.ofHom χV) (TopCat.ofHom χU) hComm
      have : ⇑poMorphism' ∘ ⇑(ConcreteCategory.hom k) = χU := by
        rw [show χU = ConcreteCategory.hom (TopCat.ofHom χU) by rfl, ← this]
        rfl
      rwa [← preimage_comp, this]

    use Ω

  -- now we show that the original topology on Z agrees with the one induced by k
  apply (isInducing_iff k).mpr
  apply TopologicalSpace.ext_iff.mpr
  intro Ω
  constructor <;> intro hΩ
  · obtain ⟨W, ⟨hWopen, hWinv⟩⟩ := inrInduced Ω hΩ
    apply isOpen_induced_iff.mpr
    use W
    exact ⟨hWopen, Eq.symm hWinv⟩
  · apply isOpen_induced_iff.mp at hΩ
    obtain ⟨Ω₀, ⟨hΩ₀open, hΩ₀inv⟩⟩ := hΩ
    have : IsOpen (k ⁻¹' Ω₀) := by
      let k' : C(Z, W) := ConcreteCategory.hom k
      exact IsOpen.preimage (ContinuousMap.continuous k') hΩ₀open
    rwa [hΩ₀inv] at this

theorem inr_inducing_of_inducing_left {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsInducing f → IsInducing k := by
  exact fun hf ↦ (inl_induce_right_induce hPushout) hf

theorem inl_inducing_of_inducing_right {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsInducing g → IsInducing h := by
  exact inr_inducing_of_inducing_left <| IsPushout.flip_iff.mp hPushout

theorem zero_inducing_of_inducing {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsInducing f → IsInducing g → IsInducing (f ≫ h) := by
  intro hf hg
  apply IsInducing.comp ?_ hf
  exact inl_inducing_of_inducing_right hPushout hg

theorem inr_embedding_of_embedding_left {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsEmbedding f → IsEmbedding k := by
  exact fun hf ↦ ⟨inr_inducing_of_inducing_left hPushout hf.1,
                  inr_injective_of_injective_left hPushout hf.2⟩

theorem inl_embedding_of_embedding_right {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsEmbedding g → IsEmbedding h := by
  exact inr_embedding_of_embedding_left <| IsPushout.flip_iff.mp hPushout

theorem zero_embedding_of_embedding {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsEmbedding f → IsEmbedding g → IsEmbedding (f ≫ h) := by
  intro hf hg
  apply IsEmbedding.comp ?_ hf
  exact inl_embedding_of_embedding_right hPushout hg

private lemma pushout_image_preimage {X Y Z W : TopCat}
    (f : X ⟶ Y) (g : X ⟶ Z) (i : Y ⟶ W) (j : Z ⟶ W)
    (hPushout : IsPushout f g i j) (hfInj : Injective f) :
    i ⁻¹' (j '' (@univ Z)) = f '' (g ⁻¹' (@univ Z)) := by
  ext y
  rw [show g ⁻¹' (@univ Z) = @univ X by rfl]
  constructor <;> intro hy
  · -- goal : y ∈ inl ⁻¹' (inr '' (@univ Z)) → y ∈ f '' (@univ X)
    apply mem_preimage.mp at hy
    rw [image_univ] at hy
    obtain ⟨x, hx⟩ := pullback_find_preimage y hPushout hfInj hy
    rw [← hx]
    exact mem_image_of_mem f _root_.trivial
  · -- goal : y ∈ f '' (@univ X) → y ∈ inl ⁻¹' (inr '' (@univ Z))
    have hcondImage : (pushout.inr f g) '' (g '' (@univ X)) ⊆ (pushout.inr f g) '' (@univ Z) := by
      exact image_mono fun ⦃a⦄ a ↦ _root_.trivial
    have : f '' (@univ X) ⊆ i ⁻¹' (j '' (@univ Z)) := calc
      f '' (@univ X) ⊆ i ⁻¹' (i '' (f '' (@univ X))) := by
        exact subset_preimage_image i (f '' (@univ X))
      _ ⊆ i ⁻¹' ((f ≫ i) '' (@univ X)) := by rw [image_image]; rfl
      _ ⊆ i ⁻¹' ((g ≫ j) '' (@univ X)) := by rw [hPushout.w]
      _ = i ⁻¹' (j '' (g '' (@univ X))) := by
        simp_all only [image_univ, mem_range, image_subset_iff, preimage_range, subset_univ,
          hom_comp, ContinuousMap.comp_apply]
        ext
        simp_all only [mem_preimage, mem_range, mem_image, exists_exists_eq_and]
      _ ⊆ i ⁻¹' (j '' (@univ Z)) := by
        simp_all [subset_def]
        intro _ x' _
        use (g x')
    exact this hy

theorem inr_open_embedding_of_open_embedding_left {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsOpenEmbedding f → IsOpenEmbedding k := by
  intro hf
  have fgInvOpen : IsOpen (f '' (g ⁻¹' (@univ Z))) := by
    apply (IsOpenEmbedding.isOpen_iff_image_isOpen hf).mp
    exact IsOpen.preimage (ContinuousMap.continuous (Hom.hom g)) isOpen_univ

  let inrZ := k '' (@univ Z)
  have hinrZpreimage : IsOpen (k ⁻¹' inrZ) := by
    rw [preimage_image_univ]
    exact isOpen_univ
  have openInr_iff : IsOpen inrZ ↔ IsOpen (h ⁻¹' inrZ) := by
    constructor
    · exact fun hz ↦ IsOpen.preimage (ContinuousMap.continuous (Hom.hom h)) hz
    · exact fun hz ↦ (glued_isOpen_iff hPushout inrZ).mpr ⟨hz, hinrZpreimage⟩
  rw [pushout_image_preimage f g h k hPushout hf.1.2] at openInr_iff
  constructor
  · exact (inr_embedding_of_embedding_left hPushout) (IsOpenEmbedding.isEmbedding hf)
  · rw [← image_univ]; exact openInr_iff.mpr fgInvOpen

theorem inl_open_embedding_of_open_embedding_right {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsOpenEmbedding g → IsOpenEmbedding h := by
  exact inr_open_embedding_of_open_embedding_left <| IsPushout.flip_iff.mp hPushout

theorem inr_closed_embedding_of_closed_embedding_left {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsClosedEmbedding f → IsClosedEmbedding k := by
  -- literally the same proof as in the open case, but replacing every "Open" with "Closed"
  intro hf
  have fgInvClosed : IsClosed (f '' (g ⁻¹' (@univ Z))) := by
    apply (IsClosedEmbedding.isClosed_iff_image_isClosed hf).mp
    exact IsClosed.preimage (ContinuousMap.continuous (Hom.hom g)) isClosed_univ

  let inrZ := k '' (@univ Z)
  have hinrZpreimage : IsClosed (k ⁻¹' inrZ) := by
    rw [preimage_image_univ]
    exact isClosed_univ
  have closedInr_iff : IsClosed inrZ ↔ IsClosed (h ⁻¹' inrZ) := by
    constructor
    · exact fun hz ↦  IsClosed.preimage (ContinuousMap.continuous (Hom.hom h)) hz
    · exact fun hz ↦ (glued_isClosed_iff hPushout inrZ).mpr ⟨hz, hinrZpreimage⟩
  rw [pushout_image_preimage f g h k hPushout hf.1.2] at closedInr_iff
  constructor
  · exact (inr_embedding_of_embedding_left hPushout) (IsClosedEmbedding.isEmbedding hf)
  · rw [← image_univ]; exact closedInr_iff.mpr fgInvClosed

theorem inl_closed_embedding_of_closed_embedding_right {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (hPushout : IsPushout f g h k) :
    IsClosedEmbedding g → IsClosedEmbedding h := by
  exact inr_closed_embedding_of_closed_embedding_left <| IsPushout.flip_iff.mp hPushout

private lemma IsClosedEmbedding.prodMap {A B C D : TopCat} {φ : A ⟶ B} {ψ : C ⟶ D}
    (hφ : IsClosedEmbedding φ) (hψ : IsClosedEmbedding ψ) : IsClosedEmbedding (Prod.map φ ψ) := by
  obtain ⟨hφEmbed, hφClosed⟩ := by exact (isClosedEmbedding_iff φ).mp hφ
  obtain ⟨hψEmbed, hψClosed⟩ := by exact (isClosedEmbedding_iff ψ).mp hψ
  apply (isClosedEmbedding_iff (Prod.map φ ψ)).mpr
  constructor
  · exact IsEmbedding.prodMap hφEmbed hψEmbed
  · rw [← image_univ] at hφClosed hψClosed
    rw [← image_univ, ← univ_prod_univ, prodMap_image_prod φ ψ univ univ]
    exact IsClosed.prod hφClosed hψClosed

private lemma diagonal_of_union {Y Z W : TopCat} {h : Y ⟶ W} {k : Z ⟶ W}
    (hUnion : (@univ W) = (range h) ∪ (range k)) :
    diagonal W = ((Prod.map h h) '' (diagonal Y)) ∪ (Prod.map k k) '' (diagonal Z) := by
  have hwRange (w : W) : w ∈ range h ∨ w ∈ range k := by
    apply mem_or_mem_of_mem_union
    rw [← hUnion]
    trivial

  ext ww
  have : ww ∈ ((Prod.map h h) '' (diagonal Y)) ∨ ww ∈ ((Prod.map k k) '' (diagonal Z)) ↔
         ww ∈ ((Prod.map h h) '' (diagonal Y)) ∪ ((Prod.map k k) '' (diagonal Z)) := by
    exact Iff.symm <| mem_union ww (Prod.map h h '' (diagonal Y)) (Prod.map k k '' (diagonal Z))
  refine Iff.trans ?_ this
  constructor <;> intro hwDiagonal
  · cases (hwRange ww.fst) with
    | inl hh =>
      left
      obtain ⟨y, hy⟩ := by exact mem_range.mp hh
      apply (mem_image (Prod.map h h) (diagonal Y) ww).mpr
      use (y, y)
      exact ⟨rfl, by rw [Prod.map_apply, hy,
        show (ww.1,ww.1) = (ww.1,ww.2) by exact congrArg (Prod.mk ww.1) hwDiagonal]⟩
    | inr hk =>
      right
      obtain ⟨z, hz⟩ := by exact mem_range.mp hk
      apply (mem_image (Prod.map k k) (diagonal Z) ww).mpr
      use (z, z)
      exact ⟨rfl, by rw [Prod.map_apply, hz,
        show (ww.1,ww.1) = (ww.1,ww.2) by exact congrArg (Prod.mk ww.1) hwDiagonal]⟩
  · obtain hh | hh := hwDiagonal <;>
    { rw [mem_image] at hh
      obtain ⟨x, hxDiag, hhx⟩ := hh
      rw [Prod.map_apply, hxDiag] at hhx
      exact mem_of_eq_of_mem (Eq.symm hhx) rfl }

theorem T2_of_T2_closed_embedding {X Y Z W : TopCat}
    {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
    (hPushout : IsPushout f g h k) :
    T2Space Y → T2Space Z → IsClosedEmbedding f → IsClosedEmbedding g → T2Space W := by
  intro hY_T2 hZ_T2 hf hg
  have hh : IsClosedEmbedding h := by
    exact inl_closed_embedding_of_closed_embedding_right hPushout hg
  have hk : IsClosedEmbedding k := by
    exact inr_closed_embedding_of_closed_embedding_left hPushout hf
  apply t2_iff_isClosed_diagonal.mpr
  rw [diagonal_of_union (Eq.symm (glued_surjective' hPushout))]
  refine IsClosed.union ?_ ?_
  · refine (IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp ?_
    · exact IsClosedEmbedding.prodMap hh hh
    · exact t2_iff_isClosed_diagonal.mp hY_T2
  · refine (IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp ?_
    · exact IsClosedEmbedding.prodMap hk hk
    · exact t2_iff_isClosed_diagonal.mp hZ_T2

end TopCat.IsPushout

namespace TopCat.Pushout

theorem glued_surjective {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    ∀ x : (pushout.cocone f g).pt, (∃ y : Y, (pushout.inl f g) y = x)
                                 ∨ (∃ y : Z, (pushout.inr f g) y = x) := by
  exact TopCat.IsPushout.glued_surjective (IsPushout.of_hasPushout f g)

theorem glued_surjective' {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    (range (pushout.inl f g)) ∪ (range (pushout.inr f g))
    = @univ (pushout.cocone f g).pt := by
  exact TopCat.IsPushout.glued_surjective' (IsPushout.of_hasPushout f g)

theorem desc_surjective_of_jointly_surjective {X Y Z Ω : TopCat} (f : X ⟶ Y) (g : X ⟶ Z)
    (h' : Y ⟶ Ω) (k' : Z ⟶ Ω) (w : f ≫ h' = g ≫ k' := by aesop_cat) :
    (range h') ∪ (range k') = @univ Ω → Surjective (pushout.desc h' k' w) := by
  intro hsurj
  apply range_eq_univ.mp
  apply univ_subset_iff.mp
  have hl : range ((pushout.inl f g) ≫ (pushout.desc h' k' w)) ⊆ range (pushout.desc h' k' w) := by
    exact range_comp_subset_range (pushout.inl f g) (pushout.desc h' k' w)
  have hr : range ((pushout.inr f g) ≫ (pushout.desc h' k' w)) ⊆ range (pushout.desc h' k' w) := by
    exact range_comp_subset_range (pushout.inr f g) (pushout.desc h' k' w)
  rw [pushout.inl_desc h' k' w] at hl
  rw [pushout.inr_desc h' k' w] at hr
  rw [← hsurj]
  exact union_subset hl hr

theorem intersection_range_inl_inr {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    (Injective f) →
    (range (pushout.inl f g)) ∩ (range (pushout.inr f g)) =
    range ((pushout.cocone f g).ι.app WalkingSpan.zero) := by
  intro hf
  let hIP := IsPushout.of_hasPushout f g
  rw [show (pushout.cocone f g).ι.app WalkingSpan.zero = f ≫ pushout.inl f g by
           exact PushoutCocone.condition_zero (pushout.cocone f g)]
  exact TopCat.IsPushout.inl_mono_intersection_inl_inr hIP hf

theorem intersection_range_inl_inr' {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    (Injective g) →
    (range (pushout.inl f g)) ∩ (range (pushout.inr f g)) =
    range ((pushout.cocone f g).ι.app WalkingSpan.zero) := by
  intro hg
  have hIP : IsPushout g f (pushout.inr f g) (pushout.inl f g) := by
    exact IsPushout.flip_iff.mp (IsPushout.of_hasPushout f g)
  have : (pushout.cocone f g).ι.app WalkingSpan.zero = g ≫ pushout.inr f g := by
    rw [hIP.w]
    exact PushoutCocone.condition_zero (pushout.cocone f g)
  rw [this, inter_comm (range (pushout.inl f g)) (range (pushout.inr f g))]
  exact TopCat.IsPushout.inl_mono_intersection_inl_inr  hIP hg

lemma inl_mono_intersection_inl_inr {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    Injective f → (range (pushout.inl f g)) ∩ (range (pushout.inr f g)) =
    range (f ≫ (pushout.inl f g)) := by
  exact TopCat.IsPushout.inl_mono_intersection_inl_inr (IsPushout.of_hasPushout f g)

theorem glued_compact_of_compact {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    CompactSpace Y → CompactSpace Z → CompactSpace (pushout.cocone f g).pt := by
  exact TopCat.IsPushout.glued_compact_of_compact (IsPushout.of_hasPushout f g)

theorem glued_isOpen_iff {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z)
    (U : Set (pushout.cocone f g).pt) :
    IsOpen U ↔   (IsOpen ((pushout.inl f g) ⁻¹' U))
               ∧ (IsOpen ((pushout.inr f g) ⁻¹' U)) := by
  exact TopCat.IsPushout.glued_isOpen_iff (IsPushout.of_hasPushout f g) U

theorem glued_isClosed_iff {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z)
    (U : Set (pushout.cocone f g).pt) :
    IsClosed U ↔   (IsClosed ((pushout.inl f g) ⁻¹' U))
                 ∧ (IsClosed ((pushout.inr f g) ⁻¹' U)) := by
  exact TopCat.IsPushout.glued_isClosed_iff (IsPushout.of_hasPushout f g) U

theorem glued_connected_of_connected {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    Nonempty X → ConnectedSpace Y → ConnectedSpace Z → ConnectedSpace (pushout.cocone f g).pt := by
  exact TopCat.IsPushout.glued_connected_of_connected (IsPushout.of_hasPushout f g)

theorem inr_injective_of_injective_left {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    Injective f → Injective (pushout.inr f g) := by
  exact TopCat.IsPushout.inr_injective_of_injective_left (IsPushout.of_hasPushout f g)

theorem inl_injective_of_injective_right {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    Injective g → Injective (pushout.inl f g) := by
  exact TopCat.IsPushout.inl_injective_of_injective_right (IsPushout.of_hasPushout f g)

theorem zero_injective_of_injective {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    Injective f → Injective g →
    Injective ((pushout.cocone f g).ι.app WalkingSpan.zero) := by
  intro hf hg
  rw [PushoutCocone.condition_zero]
  apply Injective.comp (g := pushout.inl f g) ?_ hf
  exact (inl_injective_of_injective_right f g) hg

theorem desc_injective {X Y Z Ω : TopCat} (f : X ⟶ Y) (g : X ⟶ Z)
    (h' : Y ⟶ Ω) (k' : Z ⟶ Ω) (w : f ≫ h' = g ≫ k' := by aesop_cat)
    (hInjf : Injective f) (hInjg : Injective g)
    (hInjh' : Injective h') (hInjk' : Injective k')
    (hRange_f : ∀ y : Y, ∀ z : Z, (h' y = k' z → y ∈ range f)) :
    Injective (pushout.desc h' k' w) := by
  have : pushout.desc h' k' w = (IsPushout.of_hasPushout f g).desc h' k' w := by
    ext <;> simp only [colimit.ι_desc, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app]
    · simp only [IsPushout.inl_desc]
    · simp only [IsPushout.inr_desc]
  rw [this]
  exact TopCat.IsPushout.desc_injective (IsPushout.of_hasPushout f g)
        h' k' w hInjf hInjg hInjh' hInjk' hRange_f

theorem desc_isClosedMap {X Y Z Ω : TopCat}
    (f : X ⟶ Y) (g : X ⟶ Z) (h' : Y ⟶ Ω) (k' : Z ⟶ Ω) (w : f ≫ h' = g ≫ k' := by aesop_cat) :
    IsClosedMap h' → IsClosedMap k' → IsClosedMap (pushout.desc h' k' w) := by
  intro hh hk
  have : pushout.desc h' k' w = (IsPushout.of_hasPushout f g).desc h' k' w := by
    ext <;> simp only [colimit.ι_desc, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app]
    · simp only [IsPushout.inl_desc]
    · simp only [IsPushout.inr_desc]
  rw [this]
  exact TopCat.IsPushout.desc_isClosedMap (IsPushout.of_hasPushout f g) h' k' w hh hk

theorem inr_inducing_of_inducing_left {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsInducing f → IsInducing (pushout.inr f g) := by
  exact TopCat.IsPushout.inr_inducing_of_inducing_left (IsPushout.of_hasPushout f g)

theorem inl_inducing_of_inducing_right {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsInducing g → IsInducing (pushout.inl f g) := by
  exact TopCat.IsPushout.inl_inducing_of_inducing_right (IsPushout.of_hasPushout f g)

theorem zero_inducing_of_inducing {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsInducing f → IsInducing g →
    IsInducing ((pushout.cocone f g).ι.app WalkingSpan.zero) := by
  intro hf hg
  rw [PushoutCocone.condition_zero]
  apply IsInducing.comp (g := pushout.inl f g) ?_ hf
  exact (inl_inducing_of_inducing_right f g) hg

theorem inr_embedding_of_embedding_left {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsEmbedding f → IsEmbedding (pushout.inr f g) := by
  exact TopCat.IsPushout.inr_embedding_of_embedding_left (IsPushout.of_hasPushout f g)

theorem inl_embedding_of_embedding_right {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsEmbedding g → IsEmbedding (pushout.inl f g) := by
  exact TopCat.IsPushout.inl_embedding_of_embedding_right (IsPushout.of_hasPushout f g)

theorem zero_embedding_of_embedding {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsEmbedding f → IsEmbedding g →
    IsEmbedding ((pushout.cocone f g).ι.app WalkingSpan.zero) := by
  intro hf hg
  rw [PushoutCocone.condition_zero]
  apply IsEmbedding.comp (g := pushout.inl f g) ?_ hf
  exact (inl_embedding_of_embedding_right f g) hg

theorem inr_open_embedding_of_open_embedding_left {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsOpenEmbedding f → IsOpenEmbedding (pushout.inr f g) := by
  exact TopCat.IsPushout.inr_open_embedding_of_open_embedding_left (IsPushout.of_hasPushout f g)

theorem inl_open_embedding_of_open_embedding_right {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsOpenEmbedding g → IsOpenEmbedding (pushout.inl f g) := by
  exact TopCat.IsPushout.inl_open_embedding_of_open_embedding_right (IsPushout.of_hasPushout f g)

theorem inr_closed_embedding_of_closed_embedding_left {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsClosedEmbedding f → IsClosedEmbedding (pushout.inr f g) := by
  exact TopCat.IsPushout.inr_closed_embedding_of_closed_embedding_left
        (IsPushout.of_hasPushout f g)

theorem inl_closed_embedding_of_closed_embedding_right {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsClosedEmbedding g → IsClosedEmbedding (pushout.inl f g) := by
  exact TopCat.IsPushout.inl_closed_embedding_of_closed_embedding_right
        (IsPushout.of_hasPushout f g)

theorem T2_of_T2_closed_embedding {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    T2Space Y → T2Space Z → IsClosedEmbedding f → IsClosedEmbedding g →
    T2Space (pushout.cocone f g).pt := by
  exact TopCat.IsPushout.T2_of_T2_closed_embedding (IsPushout.of_hasPushout f g)

end TopCat.Pushout
