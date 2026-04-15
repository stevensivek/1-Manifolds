import Mathlib.Tactic -- import all the tactics
import Mathlib.Analysis.Complex.Circle
import «OneManifold».GlueReal
import «OneManifold».GlueCircle

/-!
The main result of this file is `union_of_two_real_lines`, which says that if
a Hausdorff space X contains two open sets with nonempty intersection, each of
which is homeomorphic to ℝ, then their union is homeomorphic to either ℝ or a
circle.
-/

open Set Function

/- X is a Hausdorff space -/
variable {X : Type*} [TopologicalSpace X] [T2Space X]

/- If X is a connected Hausdorff space covered by two open sets, each of which is
   homeomorphic to ℝ, then X is homeomorphic to either ℝ or a circle. -/
lemma union_of_two_real_lines' [ConnectedSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUniv : U ∪ V = @univ X) (hUR : Nonempty (U ≃ₜ ℝ)) (hVR : Nonempty (V ≃ₜ ℝ)) :
    Nonempty (X ≃ₜ ℝ) ∨ Nonempty (X ≃ₜ Circle) := by
  /- Either U and V are nested one inside the other, or they overlap -/
  rcases (cover_nested_or_not U V) with hUV | hVU | ⟨hNotUV, hNotVU⟩
  · left
    rw [union_eq_self_of_subset_left hUV] at hUniv
    have : X ≃ₜ V := by rw [hUniv]; exact (Homeomorph.Set.univ X).symm
    exact Nonempty.intro <| this.trans hVR.some
  · left
    rw [union_eq_self_of_subset_right hVU] at hUniv
    have : X ≃ₜ U := by rw [hUniv]; exact (Homeomorph.Set.univ X).symm
    exact Nonempty.intro <| this.trans hUR.some
  · by_cases h : IsConnected (U ∩ V)
    · left; exact homeomorph_real_of_glue_open_real_real hU hV hUniv h hUR hVR
    · right; exact homeomorph_circle_of_glue_open_real_real hU hV hUniv h hUR hVR

/- If U and V are open sets, then their images in the subtype U ∪ V are
   open sets homeomorphic to U and V. -/
lemma union_subtype_homeomorph {Y : Type*} [TopologicalSpace Y] {U V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen {t : {x // x ∈ U ∪ V} | t.val ∈ U}
    ∧ IsOpen {t : {x // x ∈ U ∪ V} | t.val ∈ V}
    ∧ ({t : {x // x ∈ U ∪ V} | t.val ∈ U} ∪ {t : {x // x ∈ U ∪ V} | t.val ∈ V} = univ)
    ∧ Nonempty (U ≃ₜ {t : {x // x ∈ U ∪ V} | t.val ∈ U})
    ∧ Nonempty (V ≃ₜ {t : {x // x ∈ U ∪ V} | t.val ∈ V}) := by
  let Z := {x // x ∈ U ∪ V}
  let U' : Set Z := {x | x.val ∈ U}
  let V' : Set Z := {x | x.val ∈ V}
  have hU' : IsOpen U' := by
    refine isOpen_mk.mpr ?_
    use U
    exact ⟨hU, rfl⟩
  have hV' : IsOpen V' := by
    refine isOpen_mk.mpr ?_
    use V
    exact ⟨hV, rfl⟩
  have hUniv : U' ∪ V' = univ := by
    apply univ_subset_iff.mp
    intro x _
    rcases (Subtype.coe_prop x) with hxU | hxV
    · left; exact hxU
    · right; exact hxV
  let fU : U ≃ₜ U' := {
    toFun : U → U' := fun (t : U) => ⟨⟨t.val, mem_union_left V t.prop⟩, t.prop⟩,
    invFun : U' → U := fun (t : U') => ⟨t, t.prop⟩,
    left_inv := by (intro _; simp only [Subtype.coe_eta]),
    right_inv := by (intro _; simp only [Subtype.coe_eta]),
    continuous_toFun := by fun_prop,
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.comp'
      · apply continuous_induced_dom
      · apply continuous_induced_dom
  }
  let fV : V ≃ₜ V' := {
    toFun : V → V' := fun (t : V) => ⟨⟨t.val, mem_union_right U t.prop⟩, t.prop⟩,
    invFun : V' → V := fun (t : V') => ⟨t, t.prop⟩,
    left_inv := by (intro _; simp only [Subtype.coe_eta]),
    right_inv := by (intro _; simp only [Subtype.coe_eta]),
    continuous_toFun := by fun_prop,
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.comp'
      · apply continuous_induced_dom
      · apply continuous_induced_dom
  }
  exact ⟨hU', hV', hUniv, Nonempty.intro fU, Nonempty.intro fV⟩

/- Given two overlapping open sets in a Hausdorff space X, if each open set is
   homeomorphic to ℝ then their union in X is homeomorphic to either ℝ or a circle. -/
lemma union_of_two_real_lines {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hInter : Nonempty (U ∩ V : Set X))
    (hUR : Nonempty (U ≃ₜ ℝ)) (hVR : Nonempty (V ≃ₜ ℝ)) :
    Nonempty ((U ∪ V : Set X) ≃ₜ ℝ) ∨ Nonempty ((U ∪ V : Set X) ≃ₜ Circle) := by
  obtain ⟨hU', hV', hUniv, hUU', hVV'⟩ := union_subtype_homeomorph hU hV
  have : ConnectedSpace {x // x ∈ U ∪ V} := by
    apply isConnected_iff_connectedSpace.mp
    have hConn (W : Set X) : Nonempty (W ≃ₜ ℝ) → IsConnected W := by
      intro hWR
      apply isConnected_iff_connectedSpace.mpr
      have : IsConnected (@univ W) := by
        exact hWR.some.symm.isConnected_preimage.mp isConnected_univ
      exact connectedSpace_iff_univ.mpr this
    exact IsConnected.union Nonempty.of_subtype (hConn U hUR) (hConn V hVR)
  apply union_of_two_real_lines' hU' hV' hUniv ?_ ?_
  · exact Nonempty.intro <| hUU'.some.symm.trans hUR.some
  · exact Nonempty.intro <| hVV'.some.symm.trans hVR.some
