import Mathlib.Tactic -- import all the tactics
import Mathlib.Geometry.Manifold.Instances.Real
import «OneManifold».RealLemmas
import «OneManifold».OverlapLemmas

/-!
This file contains several theorems about gluing constructions that produce
spaces homeomorphic to ℝ.

## Main results

- `homeomorph_real_of_glue_closed_iic_ici` : If X is the union of two closed
  sets `A ≃ₜ Iic c` and `B ≃ₜ Ici d`, and that `A ∩ B` consists of a single
  point identified with each of the endpoints `c` and `d`.  Then X is
  homeomorphic to ℝ.

- `homeomorph_real_of_glue_open_real_real`: Suppose that X is Hausdorff and
  can be written as the union of two open sets `U` and `V`, each of which is
  homeomorphic to ℝ.  If `U ∩ V` is connected, then X is homeomorphic to ℝ.
-/

open Set Function
set_option linter.style.emptyLine false

/- A union of two closed sets homeomorphic to (-∞,0] and to [0,∞), intersecting
   only at the zero point of either interval, is homeomorphic to ℝ. -/
lemma glue_closed_intervals_real₀ {Y : Type*} [TopologicalSpace Y] (A B : Set Y)
    (hA : IsClosed A) (hB : IsClosed B) (φ : A ≃ₜ Iic (0 : ℝ)) (ψ : B ≃ₜ Ici (0 : ℝ))
    {y : Y} (hAy : y ∈ A) (hBy : y ∈ B) (hInter : A ∩ B = {y}) (hUnion : A ∪ B = univ)
    (hφy : φ ⟨y, hAy⟩ = (0 : ℝ)) (hψy : ψ ⟨y, hBy⟩ = (0 : ℝ)) :
    Nonempty (Y ≃ₜ ℝ) := by
  classical -- need to know that A, B are decidable
  have h_not_A_B (x : Y): ¬(x ∈ A) → x ∈ B := by
    intro h
    have : x ∈ A ∨ x ∈ B := by
      apply (mem_union x A B).mp
      simp only [hUnion, mem_univ]
    simpa only [h, false_or] using this

  let f : Y → ℝ := fun x => if h : x ∈ A then φ ⟨x, h⟩ else ψ ⟨x, h_not_A_B x h⟩
  have hfφ (x : Y) (hx : x ∈ A) : f x = φ ⟨x, hx⟩ := by
    simp_all only [f, NNReal.val_eq_coe, NNReal.coe_eq_zero, ↓reduceDIte]
  have hfψ (x : Y) (hx : x ∈ B) : f x = ψ ⟨x, hx⟩ := by
    by_cases hx' : x ∈ A
    · have : x = y := by
        apply mem_singleton_iff.mp
        rw [← hInter]
        exact mem_inter hx' hx
      simp_all [f]
    · have : x ∈ B := by exact h_not_A_B x hx'
      simp_all only [f, NNReal.val_eq_coe, NNReal.coe_eq_zero, ↓reduceDIte]

  have hfContOnA : ContinuousOn f A := by
    refine continuousOn_iff_continuous_restrict.mpr ?_
    have h : A.restrict f = fun a => (φ a).val := by
      ext x
      exact hfφ x x.property
    have : Continuous fun (a : A) => (φ a).val := by fun_prop
    rwa [← h] at this

  have hfContOnB : ContinuousOn f B := by
    refine continuousOn_iff_continuous_restrict.mpr ?_
    have h : B.restrict f = fun b => (ψ b).val := by
      ext x
      exact hfψ x x.property
    have : Continuous fun (b : B) => (ψ b).val := by fun_prop
    rwa [← h] at this

  have hfCont : Continuous f := by
    apply continuousOn_univ.mp
    rw [← hUnion]
    exact (continuousOn_union_iff_of_isClosed hA hB).mpr ⟨hfContOnA, hfContOnB⟩

  let g : ℝ → Y := fun x => if h : x ≤ 0 then φ.symm ⟨x,h⟩ else ψ.symm ⟨x,le_of_not_ge h⟩
  have hgContOnLe : ContinuousOn g (Iic (0 : ℝ)) := by
    have h : (Iic (0 : ℝ)).restrict g = fun x => (φ.symm x).val := by
      ext x
      simp only [g, restrict_apply, Subtype.coe_eta, dite_eq_left_iff, not_le]
      exact fun h => False.elim <| (not_le_of_gt h) (Subtype.property x)
    apply continuousOn_iff_continuous_restrict.mpr
    simp only [h]
    fun_prop
  have hgContOnGe : ContinuousOn g (Ici (0 : ℝ)) := by
    have h : (Ici (0 : ℝ)).restrict g = fun x => (ψ.symm x).val := by
      ext x
      simp only [g, restrict_apply, Subtype.coe_eta, dite_eq_right_iff]
      intro hxle
      have : (0 : ℝ) ≤ ↑x := by exact Subtype.property x
      have : ↑x = (0 : ℝ) := by simp only [le_antisymm_iff, hxle, true_and, this]
      simp only [NNReal.val_eq_coe]
      have hψsymm_x : ψ.symm x = ⟨y, hBy⟩ := by
        have : ψ ⟨y, hBy⟩ = x := by simp_all
        apply congrArg ψ.symm at this
        simp only [ψ.symm_apply_apply] at this
        exact Eq.symm this
      have hφsymm_x : φ.symm ⟨x.val, hxle⟩ = ⟨y, hAy⟩ := by
        have : φ ⟨y, hAy⟩ = ⟨x.val, hxle⟩ := by
          simp only [Subtype.ext_iff, hφy, this]
        apply congrArg φ.symm at this
        simp only [φ.symm_apply_apply] at this
        exact Eq.symm this
      have : (φ.symm ⟨↑x, hxle⟩).val = (ψ.symm x).val := by
        simp only [hψsymm_x, hφsymm_x]
      exact this
    apply continuousOn_iff_continuous_restrict.mpr
    simp only [h]
    fun_prop
  have hgCont : Continuous g := by
    apply continuousOn_univ.mp
    rw [show @univ ℝ = Iic (0 : ℝ) ∪ Ici (0 : ℝ) by exact Eq.symm Iic_union_Ici]
    exact (continuousOn_union_iff_of_isClosed isClosed_Iic isClosed_Ici).mpr
          ⟨hgContOnLe, hgContOnGe⟩

  have hleftinv : LeftInverse g f := by
    intro x
    simp_all only [NNReal.val_eq_coe, NNReal.coe_eq_zero, ↓reduceDIte, implies_true, f]
    by_cases h : x ∈ A
    · simp_all only [↓reduceDIte]
      have : (φ ⟨x, h⟩).val ≤ 0 := by exact Subtype.coe_prop (φ ⟨x, h⟩)
      simp_all only [g, ↓reduceDIte, Subtype.coe_eta, Homeomorph.symm_apply_apply]
    · simp_all only [↓reduceDIte]
      have hxB : x ∈ B := by exact h_not_A_B x h
      have hnonneg : 0 ≤ (ψ ⟨x, hxB⟩).val := by exact Subtype.coe_prop (ψ ⟨x, hxB⟩)
      by_cases h0 : (ψ ⟨x, hxB⟩).val = 0
      · simp_all only [NNReal.val_eq_coe, NNReal.zero_le_coe, NNReal.coe_eq_zero, NNReal.coe_zero]
        simp only [le_refl, ↓reduceDIte, g]
        have h' : ↑x ∈ A := by
          rw [← hψy] at h0
          apply ψ.injective at h0
          simp only [Subtype.mk.injEq] at h0
          rwa [← h0] at hAy
        apply Subtype.coe_eq_iff.mpr
        use h'
        exact φ.symm_apply_eq.mpr <| False.elim (h h')
      · have : (0 : ℝ) < ψ ⟨x, hxB⟩ := by
          exact lt_of_le_of_ne hnonneg fun a ↦ h0 (Eq.symm a)
        have : ¬ (↑(ψ ⟨x, hxB⟩) ≤ (0 : ℝ)) := by exact not_le_of_gt this
        simp_all only [g, NNReal.val_eq_coe, NNReal.zero_le_coe, NNReal.coe_eq_zero, NNReal.coe_pos]
        simp_all only [not_le, NNReal.coe_pos, ↓reduceDIte]
        apply Subtype.coe_eq_iff.mpr
        use hxB
        exact ψ.symm_apply_eq.mpr rfl

  have hrightinv : RightInverse g f := by
    intro x
    simp_all only [NNReal.val_eq_coe, NNReal.coe_eq_zero, ↓reduceDIte, implies_true, f]

    by_cases hx0 : x ≤ 0
    · simp_all [g]
    · have : g x ∉ A := by
        have : g x = ψ.symm ⟨x, le_of_not_ge hx0⟩ := by simp_all [g]
        have : g x ∈ B := by simp only [this, Subtype.coe_prop]
        by_contra hgx
        have hgxy : g x = y := by
          apply mem_singleton_iff.mp
          rw [← hInter]
          exact mem_inter hgx this
        have hx_ne_0 : x ≠ 0 := by
          have : x > 0 := by exact lt_of_not_ge hx0
          exact Ne.symm <| ne_of_lt this
        have : x = 0 := by
          simp only [hx0, ↓reduceDIte, g] at hgxy
          apply Subtype.coe_eq_iff.mp at hgxy
          obtain ⟨_, hz⟩ := hgxy
          obtain hψxy := congrArg ψ hz
          simp only [ψ.apply_symm_apply, hψy] at hψxy
          apply congrArg Subtype.val at hψxy
          simp only [NNReal.val_eq_coe, NNReal.coe_zero] at hψxy
          exact hψxy
        exact hx_ne_0 this
      simp_all only [not_le, ↓reduceDIte]
      apply Subtype.coe_eq_iff.mpr
      use (le_of_lt hx0)
      apply Eq.symm
      apply ψ.symm_apply_eq.mp
      apply Eq.symm
      simp only [g, not_le.mpr hx0, ↓reduceDIte, Subtype.coe_eta]
      rfl

  let ρ : Y ≃ₜ ℝ := {
    toFun : Y → ℝ := f,
    invFun : ℝ → Y := g,
    left_inv := hleftinv,
    right_inv := hrightinv,
    continuous_toFun := hfCont,
    continuous_invFun := hgCont
  }
  exact Nonempty.intro ρ

/- A union of two closed sets homeomorphic to (-∞,c] and to [d,∞), intersecting
   only at the point identified with c and with d in either interval, is
  homeomorphic to ℝ. -/
theorem homeomorph_real_of_glue_closed_iic_ici
    {Y : Type*} [TopologicalSpace Y] (A B : Set Y) {c d : ℝ}
    (hA : IsClosed A) (hB : IsClosed B) (φ : A ≃ₜ Iic c) (ψ : B ≃ₜ Ici d)
    {y : Y} (hAy : y ∈ A) (hBy : y ∈ B) (hInter : A ∩ B = {y}) (hUnion : A ∪ B = univ)
    (hφy : φ ⟨y, hAy⟩ = c) (hψy : ψ ⟨y, hBy⟩ = d) :
    Nonempty (Y ≃ₜ ℝ) := by

  let φ' : A ≃ₜ Iic (0 : ℝ) := φ.trans <| iicHomeo_iic0 c

  have hφ'y : φ' ⟨y, hAy⟩ = (0 : ℝ) := by
    have (x : Iic c) : (iicHomeo_iic0 c) x = x.val - c := by rfl
    simp [φ', hφy, this]

  let ψ' : B ≃ₜ Ici (0 : ℝ) := ψ.trans <| iciHomeo_ici0 d
  have hψ'y : ψ' ⟨y, hBy⟩ = (0 : ℝ) := by
    simp only [ψ.trans_apply, NNReal.val_eq_coe, NNReal.coe_eq_zero, ψ']
    apply Subtype.mk_eq_mk.mpr
    simp only [hψy, sub_self]

  exact glue_closed_intervals_real₀ A B hA hB φ' ψ' hAy hBy hInter hUnion hφ'y hψ'y

/- Let X be a Hausdorff space covered by two open sets U ≃ₜ ℝ and V ≃ₜ ℝ, with
   U ∩ V connected.  Then X ≃ₜ ℝ. -/
theorem homeomorph_real_of_glue_open_real_real {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUniv : U ∪ V = @univ X) (hConn : IsConnected (U ∩ V))
    (hUR : Nonempty (U ≃ₜ ℝ)) (hVR : Nonempty (V ≃ₜ ℝ)) : Nonempty (X ≃ₜ ℝ) := by
  let x : X := hConn.nonempty.some
  have hxUV : x ∈ U ∩ V := by exact hConn.nonempty.some_mem

  -- First deal with the cases where U and V are nested one inside the other
  rcases (cover_nested_or_not U V) with hUV | hVU | ⟨hNotUV, hNotVU⟩
  · rw [union_eq_self_of_subset_left hUV] at hUniv
    have : X ≃ₜ V := by rw [hUniv]; exact (Homeomorph.Set.univ X).symm
    exact Nonempty.intro <| this.trans hVR.some
  · rw [union_eq_self_of_subset_right hVU] at hUniv
    have : X ≃ₜ U := by rw [hUniv]; exact (Homeomorph.Set.univ X).symm
    exact Nonempty.intro <| this.trans hUR.some

  -- From now on we have hNotUV : ¬(U ⊆ V) and hNotVU : ¬(V ⊆ U)
  obtain ⟨φ₀, hφ₀Source, hφ₀Target⟩ := real_chart_to_partial_homeomorph hU hUR.some
  obtain ⟨ψ₀, hψ₀Source, hψ₀Target⟩ := real_chart_to_partial_homeomorph hV hVR.some

  obtain ⟨hUConn, hVConn⟩ : IsConnected U ∧ IsConnected V := by
    rw [← hφ₀Source, ← hψ₀Source]
    constructor <;> apply partial_homeomorph_IsConnected_source <;> assumption

  have hxComponent : connectedComponentIn (U ∩ V) x = U ∩ V := by
    apply Subset.antisymm
    · exact connectedComponentIn_subset (U ∩ V) x
    · exact hConn.isPreconnected.subset_connectedComponentIn hxUV Subset.rfl

  obtain ⟨φ, hφSource, hφTarget, ⟨a, hφUV⟩⟩ := by
    exact choose_intersection_component_left
          hφ₀Source hφ₀Target hV hVConn hNotUV hNotVU hxUV

  have hφComponent : connectedComponentIn (φ '' (U ∩ V)) (φ x) = φ '' (U ∩ V) := by
    have : IsConnected (φ '' (U ∩ V)) := by
      rw [← hφSource] at hConn ⊢
      exact hConn.image φ <| φ.continuousOn.mono inter_subset_left
    exact this.isPreconnected.connectedComponentIn <| mem_image_of_mem φ hxUV

  obtain ⟨ψ, hψSource, hψTarget, ⟨b, hψUV⟩⟩ := by
    have hxUV' : x ∈ V ∩ U := by rwa [inter_comm] at hxUV
    exact choose_intersection_component_right
          hψ₀Source hψ₀Target hU hUConn hNotVU hNotUV hxUV'
  rw [inter_comm] at hψUV

  have hψComponent : connectedComponentIn (ψ '' (U ∩ V)) (ψ x) = ψ '' (U ∩ V) := by
    have : IsConnected (ψ '' (U ∩ V)) := by
      rw [← hψSource] at hConn ⊢
      exact hConn.image ψ <| ψ.continuousOn.mono inter_subset_right
    exact this.isPreconnected.connectedComponentIn <| mem_image_of_mem ψ hxUV

  let f := φ.symm.trans ψ
  have hf_image : f '' (Iio a) = (Ioi b) := by
    exact transition_iio_to_ioi hφSource hψSource hxUV hφUV hψUV
  have hf_mono : StrictMonoOn f (Iio a) := by
    exact monotone_iio_to_ioi hφSource hφTarget hψSource hψTarget hxUV hφUV hψUV
  have hf_val : f (φ x) = ψ x := by simp_all [f]

  have hφxa : φ x ∈ Iio a := by
    rw [← hφUV]
    exact mem_connectedComponentIn <| mem_image_of_mem (↑φ) hxUV

  have hψxb : ψ x ∈ Ioi b := by
    rw [← hf_val, ← hf_image]
    exact mem_image_of_mem f hφxa

  let A : Set X := ψ.symm '' (Iic (ψ x))
  have hAV : A ⊆ V := by
    intro t ht
    have : t ∈ ψ.symm '' ψ.symm.source := by
      rw [ψ.symm_source, hψTarget]
      exact image_mono (s := Iic (ψ x)) (fun _ _ ↦ trivial) ht
    rwa [← hψSource, ← ψ.symm_target, ← ψ.symm.image_source_eq_target]

  let B : Set X := φ.symm '' (Ici (φ x))
  have hBU : B ⊆ U := by
    intro t ht
    have : t ∈ φ.symm '' φ.symm.source := by
      rw [φ.symm_source, hφTarget]
      exact image_mono (s := Ici (φ x)) (fun _ _ ↦ trivial) ht
    rwa [← hφSource, ← φ.symm_target, ← φ.symm.image_source_eq_target]

  have hAB_cover_UV : U ∩ V ⊆ A ∪ B := by
    have hUV_split := connectedComponentIn_split
                      hxUV hφSource hφTarget hψSource hψTarget hφUV hψUV
    rw [← hxComponent, hUV_split, union_comm]
    apply union_subset_union <;> apply image_mono
    · exact fun _ ht ↦ ht.2
    · exact fun _ ht ↦ ht.1

  have hAB_univ : A ∪ B = univ := by
    apply univ_subset_iff.mp
    rw [← hUniv]
    intro t ht
    by_cases h : t ∈ U ∩ V
    · exact hAB_cover_UV h
    · by_cases h' : t ∈ U
      · rw [← hφSource, ← φ.symm_target, ← φ.symm.image_source_eq_target,
            φ.symm_source, hφTarget] at h'
        have : U ∩ V = φ.symm '' (Iio a) := by
          rw [← hφUV, hφComponent, ← image_comp]
          apply Subset.antisymm <;> intro y hy
          · rw [show y = (φ.symm ∘ φ) y by simp_all only [comp_apply, mem_inter_iff, φ.left_inv]]
            exact mem_image_of_mem (φ.symm ∘ φ) hy
          · obtain ⟨z,hz,hyz⟩ := hy
            exact mem_of_eq_of_mem (by simp_all only [comp_apply, mem_inter_iff, φ.left_inv]) hz
        rw [this] at h
        apply mem_union_right A <| (image_mono <| Ici_subset_Ici.mpr <| le_of_lt hφxa) ?_
        have : InjOn φ.symm univ := by
          rw [← hφTarget]
          exact φ.symm.injOn
        rw [← compl_Iio, compl_eq_univ_diff, this.image_diff, univ_inter]
        exact mem_diff_of_mem h' h
      · replace h' : t ∈ V := by simpa only [mem_union, h', false_or] using ht
        rw [← hψSource, ← ψ.symm_target, ← ψ.symm.image_source_eq_target,
            ψ.symm_source, hψTarget] at h'
        have : U ∩ V = ψ.symm '' (Ioi b) := by
          rw [← hψUV, hψComponent, ← image_comp]
          apply Subset.antisymm <;> intro y hy
          · rw [show y = (ψ.symm ∘ ψ) y by simp_all only [comp_apply, mem_inter_iff, ψ.left_inv]]
            exact mem_image_of_mem (ψ.symm ∘ ψ) hy
          · obtain ⟨z,hz,hyz⟩ := hy
            exact mem_of_eq_of_mem (by simp_all only [comp_apply, mem_inter_iff, ψ.left_inv]) hz
        rw [this] at h
        apply mem_union_left B <| (image_mono <| Iic_subset_Iic.mpr <| le_of_lt hψxb) ?_
        rw [← compl_Ioi, compl_eq_univ_diff, image_diff]
        · exact mem_diff_of_mem h' h
        · exact ψ.injective_symm_of_target_eq_univ hψTarget

  have hxAB : x ∈ A ∩ B := by
    obtain ⟨hxφSource, hxψSource⟩ : x ∈ φ.source ∧ x ∈ ψ.source := by
      rw [hφSource, hψSource]
      exact ⟨mem_of_mem_inter_left hxUV, mem_of_mem_inter_right hxUV⟩
    apply mem_inter
    · rw [← ψ.left_inv hxψSource]
      exact mem_image_of_mem ψ.symm self_mem_Iic
    · rw [← φ.left_inv hxφSource]
      exact mem_image_of_mem φ.symm self_mem_Iic
  obtain ⟨hxA, hxB⟩ := (mem_inter_iff x A B).mp hxAB

  have hABinter : A ∩ B = {x} := by
    apply Subset.antisymm
    · intro s hs
      rw [inter_comm] at hs
      have hsUV : s ∈ U ∩ V := inter_subset_inter hBU hAV hs
      have hsCpt : s ∈ connectedComponentIn (U ∩ V) x := by rwa [hxComponent]
      exact overlap_intersection hφSource hφTarget hψSource hψTarget
                                 hφUV hψUV hxUV hφxa hsCpt hsUV hs
    · exact singleton_subset_iff.mpr hxAB

  have hA : IsClosed A := by
    apply isOpen_compl_iff.mp
    rw [compl_eq_univ_diff, ← hAB_univ, union_diff_left, ← diff_self_inter, inter_comm, hABinter]
    simp only [B]
    nth_rewrite 2 [show x = φ.symm (φ x) by simp_all]
    rw [← image_singleton, ← image_diff, Ici_diff_left]
    · refine φ.isOpen_image_symm_of_subset_target isOpen_Ioi ?_
      exact subset_of_subset_of_eq (subset_univ <| Ioi (φ x)) <| Eq.symm hφTarget
    · exact φ.injective_symm_of_target_eq_univ hφTarget

  have hB : IsClosed B := by
    apply isOpen_compl_iff.mp
    have : B ∩ A = {x} := by rwa [inter_comm]
    rw [compl_eq_univ_diff, ← hAB_univ, union_diff_right, ← diff_self_inter, inter_comm, this]
    simp only [A]
    nth_rewrite 2 [show x = ψ.symm (ψ x) by simp_all]
    rw [← image_singleton, ← image_diff, Iic_diff_right]
    · refine ψ.isOpen_image_symm_of_subset_target isOpen_Iio ?_
      exact subset_of_subset_of_eq (subset_univ <| Iio (ψ x)) <| Eq.symm hψTarget
    · exact ψ.injective_symm_of_target_eq_univ hψTarget

  -- now need A ≃ₜ Iic (ψ x) and B ≃ₜ Ici (φ x)
  let symm_subset_homeo {η : OpenPartialHomeomorph X ℝ} (hη : η.target = univ)
      (S : Set ℝ) : η.symm '' S ≃ₜ S := by
    apply (η.symm.homeomorphOfImageSubsetSource ?_ rfl).symm
    rw [η.symm_source, hη]
    exact fun _ _ ↦ trivial
  let ηA : A ≃ₜ Iic (ψ x) := symm_subset_homeo hψTarget (Iic (ψ x))
  let ηB : B ≃ₜ Ici (φ x) := symm_subset_homeo hφTarget (Ici (φ x))

  obtain ⟨hηAx, hηBx⟩ : ηA ⟨x, hxA⟩ = ψ x ∧ ηB ⟨x, hxB⟩ = φ x := by
    simp_all only [OpenPartialHomeomorph.homeomorphOfImageSubsetSource_symm_apply,
      OpenPartialHomeomorph.symm_symm, MapsTo.val_restrict_apply, A, B, ηA, ηB,
      symm_subset_homeo, and_self]

  exact homeomorph_real_of_glue_closed_iic_ici
        A B hA hB ηA ηB hxA hxB hABinter hAB_univ hηAx hηBx
