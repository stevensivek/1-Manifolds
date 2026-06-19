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

section RealGlueIicIci

variable {α : Type*} [LinearOrder α] [TopologicalSpace α]

private lemma mem_union_and_not_mem_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hUnion : A ∪ B = univ) {t : X} (ht : t ∉ A) : t ∈ B := by
  have : t ∈ A ∪ B := hUnion ▸ trivial
  simpa only [mem_union, ht, false_or] using this

noncomputable def glue_iic_ici_map {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) (hUnion : A ∪ B = univ) : X → α :=
  fun t => if h : t ∈ A then φ ⟨t, h⟩ else ψ ⟨t, mem_union_and_not_mem_left hUnion h⟩

lemma glue_iic_ici_map_eval_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) (hUnion : A ∪ B = univ)
    {t : X} (hA : t ∈ A) :
    (glue_iic_ici_map φ ψ hUnion) t = φ ⟨t, hA⟩ := by
  simp only [glue_iic_ici_map, hA, ↓reduceDIte]

private lemma eval_homeomorph_subtype_of_symm_val
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {φ : A ≃ₜ Y} {x : X} {y : Y} (hφ : ↑(φ.symm y) = x) :
    ∀ h : x ∈ A, φ ⟨x, h⟩ = y := by
  subst x
  exact fun _ ↦ by simp only [Subtype.coe_eta, φ.apply_symm_apply]

lemma glue_iic_ici_map_eval_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) (hUnion : A ∪ B = univ)
    {x : X} (hInter : A ∩ B = {x})
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x)
    {t : X} (hB : t ∈ B) :
    (glue_iic_ici_map φ ψ hUnion) t = ψ ⟨t, hB⟩ := by
  by_cases hA : t ∈ A <;> simp only [glue_iic_ici_map, hA, ↓reduceDIte]
  · have : t = x := mem_singleton_iff.mp <| hInter ▸ mem_inter hA hB
    subst t
    rw [eval_homeomorph_subtype_of_symm_val hφx hA, eval_homeomorph_subtype_of_symm_val hψx hB]

lemma glue_iic_ici_map_continuousOn_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) (hUnion : A ∪ B = univ) :
    ContinuousOn (glue_iic_ici_map φ ψ hUnion) A := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : A.restrict (glue_iic_ici_map φ ψ hUnion) = fun a => (φ a).val := by
    ext x
    simp only [restrict_apply]
    exact glue_iic_ici_map_eval_left φ ψ hUnion (Subtype.coe_prop x)
  exact this ▸ Continuous.subtype_val φ.continuous

lemma glue_iic_ici_map_continuousOn_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) (hUnion : A ∪ B = univ)
    {x : X} (hInter : A ∩ B = {x})
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x) :
    ContinuousOn (glue_iic_ici_map φ ψ hUnion) B := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : B.restrict (glue_iic_ici_map φ ψ hUnion) = fun b => (ψ b).val := by
    ext x
    simp only [restrict_apply]
    exact glue_iic_ici_map_eval_right φ ψ hUnion hInter hφx hψx (Subtype.coe_prop x)
  exact this ▸ Continuous.subtype_val ψ.continuous

lemma glue_iic_ici_map_continuous {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) (hUnion : A ∪ B = univ)
    {x : X} (hInter : A ∩ B = {x})
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x)
    (hAClosed : IsClosed A) (hBClosed : IsClosed B) :
    Continuous (glue_iic_ici_map φ ψ hUnion) := by
  apply continuousOn_univ.mp
  exact hUnion ▸ (continuousOn_union_iff_of_isClosed hAClosed hBClosed).mpr
    ⟨glue_iic_ici_map_continuousOn_left φ ψ hUnion,
     glue_iic_ici_map_continuousOn_right φ ψ hUnion hInter hφx hψx⟩

noncomputable def glue_iic_ici_symm {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) : α → X :=
  fun t => if h : t ≤ z then φ.symm ⟨t, h⟩ else ψ.symm ⟨t, le_of_not_ge h⟩

lemma glue_iic_ici_symm_eval_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z)
    {t : α} (hA : t ∈ Iic z) :
    (glue_iic_ici_symm φ ψ) t = φ.symm ⟨t, hA⟩ := by
  simp only [glue_iic_ici_symm, mem_Iic.mp hA, ↓reduceDIte]

lemma glue_iic_ici_symm_eval_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) {x : X}
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x)
    {t : α} (hB : t ∈ Ici z) :
    (glue_iic_ici_symm φ ψ) t = ψ.symm ⟨t, hB⟩ := by
  by_cases hA : t ≤ z <;> simp only [glue_iic_ici_symm, hA, ↓reduceDIte]
  · have : t = z := eq_of_le_of_ge hA (mem_Ici.mp hB)
    subst t
    rw [hφx, hψx]

lemma glue_iic_ici_symm_continuousOn_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) :
    ContinuousOn (glue_iic_ici_symm φ ψ) (Iic z) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : (Iic z).restrict (glue_iic_ici_symm φ ψ) = fun t => (φ.symm t).val := by
    ext t
    rw [restrict_apply, glue_iic_ici_symm_eval_left φ ψ (Subtype.coe_prop t)]
  exact this ▸ Continuous.subtype_val φ.symm.continuous

lemma glue_iic_ici_symm_continuousOn_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) {x : X}
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x) :
    ContinuousOn (glue_iic_ici_symm φ ψ) (Ici z) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : (Ici z).restrict (glue_iic_ici_symm φ ψ) = fun t => (ψ.symm t).val := by
    ext t
    simp only [restrict_apply]
    exact glue_iic_ici_symm_eval_right φ ψ hφx hψx (Subtype.coe_prop t)
  exact this ▸ Continuous.subtype_val ψ.symm.continuous

lemma glue_iic_ici_symm_continuous {X : Type*} [TopologicalSpace X]
    [ClosedIciTopology α] [ClosedIicTopology α]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) {x : X}
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x) :
    Continuous (glue_iic_ici_symm φ ψ) := by
  apply continuousOn_univ.mp
  rw [← Iic_union_Ici (a := z)]
  exact (continuousOn_union_iff_of_isClosed isClosed_Iic isClosed_Ici).mpr
    ⟨glue_iic_ici_symm_continuousOn_left φ ψ,
     glue_iic_ici_symm_continuousOn_right φ ψ hφx hψx⟩

lemma glue_iic_ici_left_inverse {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) {x : X}
    (hUnion : A ∪ B = univ) (hInter : A ∩ B = {x})
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x) :
    LeftInverse (glue_iic_ici_symm φ ψ) (glue_iic_ici_map φ ψ hUnion) := by
  intro t
  by_cases ht : t ∈ A
  · rw [glue_iic_ici_map_eval_left φ ψ hUnion ht,
        glue_iic_ici_symm_eval_left φ ψ <| Subtype.coe_prop (φ ⟨t, ht⟩)]
    simp only [Subtype.coe_eta, φ.symm_apply_apply]
  · have ht' : t ∈ B := mem_union_and_not_mem_left hUnion ht
    have : ↑(ψ ⟨t, ht'⟩) ∈ Ici z := Subtype.coe_prop (ψ ⟨t, ht'⟩)
    rw [glue_iic_ici_map_eval_right φ ψ hUnion hInter hφx hψx ht',
        glue_iic_ici_symm_eval_right φ ψ hφx hψx this]
    simp only [Subtype.coe_eta, ψ.symm_apply_apply]

lemma glue_iic_ici_right_inverse {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)] {z : α}
    (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) {x : X}
    (hUnion : A ∪ B = univ) (hInter : A ∩ B = {x})
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x) :
    RightInverse (glue_iic_ici_symm φ ψ) (glue_iic_ici_map φ ψ hUnion) := by
  intro t
  by_cases ht : t ∈ Iic z
  · rw [glue_iic_ici_symm_eval_left φ ψ ht,
        glue_iic_ici_map_eval_left φ ψ hUnion <| Subtype.coe_prop (φ.symm ⟨t, ht⟩)]
    simp only [Subtype.coe_eta, φ.apply_symm_apply]
  · have ht' : t ∈ Ici z := mem_Ici.mpr <| Std.le_of_not_ge ht
    have : ↑(ψ.symm ⟨t, ht'⟩) ∈ B := Subtype.coe_prop (ψ.symm ⟨t, ht'⟩)
    rw [glue_iic_ici_symm_eval_right φ ψ hφx hψx ht',
        glue_iic_ici_map_eval_right φ ψ hUnion hInter hφx hψx this]
    simp only [Subtype.coe_eta, ψ.apply_symm_apply]

/- A union of two closed sets homeomorphic to the subsets (-∞, z] and [z, ∞)
   in an ordered space, intersecting only at the endpoint of either interval,
   is homeomorphic to the ordered space. -/
lemma homeomorph_of_glue_closed_intervals {X : Type*} [TopologicalSpace X]
    [ClosedIciTopology α] [ClosedIicTopology α]
    {A B : Set X} {z : α} (φ : A ≃ₜ Iic z) (ψ : B ≃ₜ Ici z) {x : X}
    (hUnion : A ∪ B = univ) (hInter : A ∩ B = {x})
    (hφx : ↑(φ.symm ⟨z, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨z, self_mem_Iic⟩) = x)
    (hAClosed : IsClosed A) (hBClosed : IsClosed B) :
    Nonempty (X ≃ₜ α) := by
  classical -- need membership in A to be decidable
  let ρ : X ≃ₜ α := {
    toFun : X → α := glue_iic_ici_map φ ψ hUnion,
    invFun : α → X := glue_iic_ici_symm φ ψ,
    left_inv := glue_iic_ici_left_inverse φ ψ hUnion hInter hφx hψx,
    right_inv := glue_iic_ici_right_inverse φ ψ hUnion hInter hφx hψx,
    continuous_toFun := glue_iic_ici_map_continuous φ ψ hUnion hInter hφx hψx hAClosed hBClosed,
    continuous_invFun := glue_iic_ici_symm_continuous φ ψ hφx hψx
  }
  exact Nonempty.intro ρ

private lemma homeo_symm {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set X} {D : Set Y} {α : C ≃ₜ D} {z : X} {y : D}
    (hC : z ∈ C) (hα : (α ⟨z, hC⟩).val = y.val) : ↑(α.symm y) = z :=
  Subtype.coe_eq_iff.mpr ⟨hC, α.symm_apply_eq.mpr <| SetCoe.ext (Eq.symm hα)⟩

/- A union of two closed sets homeomorphic to the subsets (-∞, c] and to [d, ∞)
   in ℝ, intersecting only at their respective endpoints, is homeomorphic to ℝ. -/
theorem homeomorph_real_of_glue_closed_iic_ici {X : Type*} [TopologicalSpace X]
    {A B : Set X} {c d : ℝ} (φ : A ≃ₜ Iic c) (ψ : B ≃ₜ Ici d)
    (hUnion : A ∪ B = univ) {x : X} (hInter : A ∩ B = {x})
    (hφx : ↑(φ.symm ⟨c, self_mem_Iic⟩) = x) (hψx : ↑(ψ.symm ⟨d, self_mem_Iic⟩) = x)
    (hA : IsClosed A) (hB : IsClosed B) :
    Nonempty (X ≃ₜ ℝ) := by
  have hxA : x ∈ A := mem_of_mem_inter_left <| hInter ▸ mem_singleton x
  have hxB : x ∈ B := mem_of_mem_inter_right <| hInter ▸ mem_singleton x
  let φ' : A ≃ₜ Iic (0 : ℝ) := φ.trans <| iicHomeo_iic0 c
  let ψ' : B ≃ₜ Ici (0 : ℝ) := ψ.trans <| iciHomeo_ici0 d
  obtain ⟨hφ'x, hψ'x⟩ : φ' ⟨x, hxA⟩ = (0 : ℝ) ∧ ψ' ⟨x, hxB⟩ = (0 : ℝ) := by
    simp only [φ', ψ', Homeomorph.trans_apply,
      eval_homeomorph_subtype_of_symm_val hφx hxA, iicHomeo_iic0_eval,
      eval_homeomorph_subtype_of_symm_val hψx hxB, iciHomeo_ici0_eval,
      sub_self, true_and]
  exact homeomorph_of_glue_closed_intervals φ' ψ' hUnion hInter
        (homeo_symm hxA hφ'x) (homeo_symm hxB hψ'x) hA hB

end RealGlueIicIci

/- Let X be a Hausdorff space covered by two open sets U ≃ₜ ℝ and V ≃ₜ ℝ, with
   U ∩ V connected.  Then X ≃ₜ ℝ. -/
theorem homeomorph_real_of_glue_open_real_real {X : Type*} [TopologicalSpace X] [T2Space X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUniv : U ∪ V = @univ X) (hConn : IsConnected (U ∩ V))
    (hUR : Nonempty (U ≃ₜ ℝ)) (hVR : Nonempty (V ≃ₜ ℝ)) : Nonempty (X ≃ₜ ℝ) := by
  let x : X := hConn.nonempty.some
  have hxUV : x ∈ U ∩ V := hConn.nonempty.some_mem

  -- First deal with the cases where U and V are nested one inside the other
  rcases (cover_nested_or_not U V) with hUV | hVU | ⟨hNotUV, hNotVU⟩
  · rw [union_eq_self_of_subset_left hUV] at hUniv
    have : X ≃ₜ V := hUniv ▸ (Homeomorph.Set.univ X).symm
    exact Nonempty.intro <| this.trans hVR.some
  · rw [union_eq_self_of_subset_right hVU] at hUniv
    have : X ≃ₜ U := hUniv ▸ (Homeomorph.Set.univ X).symm
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
  have hf_image : f '' (Iio a) = (Ioi b) :=
    transition_iio_to_ioi hφSource hψSource hxUV hφUV hψUV
  have hf_mono : StrictMonoOn f (Iio a) :=
    monotone_iio_to_ioi hφSource hφTarget hψSource hψTarget hxUV hφUV hψUV
  have hf_val : f (φ x) = ψ x := by simp_all [f]

  have hφxa : φ x ∈ Iio a := hφUV ▸ mem_connectedComponentIn <| mem_image_of_mem φ hxUV

  have hψxb : ψ x ∈ Ioi b := by
    rw [← hf_val, ← hf_image]
    exact mem_image_of_mem f hφxa

  let A : Set X := ψ.symm '' (Iic (ψ x))
  have hAV : A ⊆ V := by
    apply subset_trans (image_mono (s := Iic (ψ x)) (subset_univ _)) ?_
    rw [← hψTarget, ψ.symm_image_target_eq_source, hψSource]

  let B : Set X := φ.symm '' (Ici (φ x))
  have hBU : B ⊆ U := by
    apply subset_trans (image_mono (s := Ici (φ x)) (subset_univ _)) ?_
    rw [← hφTarget, φ.symm_image_target_eq_source, hφSource]

  have hAB_cover_UV : U ∩ V ⊆ A ∪ B := by
    have hUV_split := connectedComponentIn_split
                      hxUV hφSource hφTarget hψSource hψTarget hφUV hψUV
    rw [← hxComponent, hUV_split, union_comm]
    apply union_subset_union <;> apply image_mono
    · exact Ioc_subset_Iic_self
    · exact Ico_subset_Ici_self

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
          · obtain ⟨z, hz, hyz⟩ := hy
            exact mem_of_eq_of_mem (by simp_all only [comp_apply, mem_inter_iff, φ.left_inv]) hz
        rw [this] at h
        apply mem_union_right A <| (image_mono <| Ici_subset_Ici.mpr <| le_of_lt hφxa) ?_
        have : InjOn φ.symm univ := hφTarget ▸ φ.symm.injOn
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
          · obtain ⟨z, hz, hyz⟩ := hy
            exact mem_of_eq_of_mem (by simp_all only [comp_apply, mem_inter_iff, ψ.left_inv]) hz
        apply mem_union_left B <| (image_mono <| Iic_subset_Iic.mpr <| le_of_lt hψxb) ?_
        rw [← compl_Ioi, compl_eq_univ_diff, image_diff]
        · exact mem_diff_of_mem h' (this ▸ h)
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
    have : φ.symm (φ x) = x :=
      φ.left_inv <| hφSource ▸ mem_of_subset_of_mem inter_subset_left hxUV
    nth_rewrite 2 [← this]
    rw [← image_singleton, ← image_diff, Ici_diff_left]
    · refine φ.isOpen_image_symm_of_subset_target isOpen_Ioi ?_
      exact subset_of_subset_of_eq (subset_univ <| Ioi (φ x)) <| Eq.symm hφTarget
    · exact φ.injective_symm_of_target_eq_univ hφTarget

  have hB : IsClosed B := by
    apply isOpen_compl_iff.mp
    have : B ∩ A = {x} := by rwa [inter_comm]
    rw [compl_eq_univ_diff, ← hAB_univ, union_diff_right, ← diff_self_inter, inter_comm, this]
    simp only [A]
    have : ψ.symm (ψ x) = x :=
      ψ.left_inv <| hψSource ▸ mem_of_subset_of_mem inter_subset_left (by rwa [inter_comm] at hxUV)
    nth_rewrite 2 [← this]
    rw [← image_singleton, ← image_diff, Iic_diff_right]
    · refine ψ.isOpen_image_symm_of_subset_target isOpen_Iio ?_
      exact subset_of_subset_of_eq (subset_univ <| Iio (ψ x)) <| Eq.symm hψTarget
    · exact ψ.injective_symm_of_target_eq_univ hψTarget

  -- now need A ≃ₜ Iic (ψ x) and B ≃ₜ Ici (φ x)
  let symm_subset_homeo {η : OpenPartialHomeomorph X ℝ} (hη : η.target = univ)
      (S : Set ℝ) : η.symm '' S ≃ₜ S := by
    apply (η.symm.homeomorphOfImageSubsetSource ?_ rfl).symm
    rw [η.symm_source, hη]
    exact subset_univ _
  let ηA : A ≃ₜ Iic (ψ x) := symm_subset_homeo hψTarget (Iic (ψ x))
  let ηB : B ≃ₜ Ici (φ x) := symm_subset_homeo hφTarget (Ici (φ x))

  obtain ⟨hηAx, hηBx⟩ : ηA ⟨x, hxA⟩ = ψ x ∧ ηB ⟨x, hxB⟩ = φ x := by
    simp_all only [OpenPartialHomeomorph.homeomorphOfImageSubsetSource_symm_apply,
      OpenPartialHomeomorph.symm_symm, MapsTo.val_restrict_apply, A, B, ηA, ηB,
      symm_subset_homeo, and_self]

  exact homeomorph_real_of_glue_closed_iic_ici ηA ηB hAB_univ hABinter
    (homeo_symm hxA hηAx) (homeo_symm hxB hηBx) hA hB
