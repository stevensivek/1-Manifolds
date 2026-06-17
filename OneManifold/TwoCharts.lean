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

/- If U is open and U ⊆ Ω, then the image of U in the subtype Ω is an open
   set homeomorphic to U. -/
lemma open_subtype_homeomorph {Y : Type*} [TopologicalSpace Y] {U Ω : Set Y}
    (hU : IsOpen U) (hSubset : U ⊆ Ω) :
    IsOpen {t : {x // x ∈ Ω} | t.val ∈ U} ∧
    Nonempty (U ≃ₜ {t : {x // x ∈ Ω} | t.val ∈ U}) := by
  let U' : Set {x // x ∈ Ω} := {x | x.val ∈ U}
  let f : U ≃ₜ U' := {
    toFun : U → U' := fun t => ⟨⟨t.val, mem_of_subset_of_mem hSubset t.prop⟩, t.prop⟩,
    invFun : U' → U := fun t => ⟨↑t, t.prop⟩,
    left_inv := fun _ ↦ by simp only [Subtype.coe_eta],
    right_inv := fun _ ↦ by simp only [Subtype.coe_eta],
    continuous_toFun := by fun_prop,
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact Continuous.comp' continuous_induced_dom continuous_induced_dom
  }
  exact ⟨isOpen_mk.mpr ⟨U, hU, rfl⟩, Nonempty.intro f⟩

/- Given two overlapping open sets in a Hausdorff space X, if each open set is
   homeomorphic to ℝ then their union in X is homeomorphic to either ℝ or a circle. -/
lemma union_of_two_real_lines {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hInter : Nonempty (U ∩ V : Set X))
    (hUR : Nonempty (U ≃ₜ ℝ)) (hVR : Nonempty (V ≃ₜ ℝ)) :
    Nonempty ((U ∪ V : Set X) ≃ₜ ℝ) ∨ Nonempty ((U ∪ V : Set X) ≃ₜ Circle) := by
  obtain ⟨hU', hUU'⟩ := open_subtype_homeomorph hU <| subset_union_left (t := V)
  obtain ⟨hV', hVV'⟩ := open_subtype_homeomorph hV <| subset_union_right (s := U)
  let hUniv : {t : {x // x ∈ U ∪ V} | ↑t ∈ U} ∪ {t : {x // x ∈ U ∪ V} | ↑t ∈ V} = univ := by
    apply univ_subset_iff.mp
    intro x _
    rcases (Subtype.coe_prop x) with hx | hx <;>
      simp only [mem_union, mem_setOf_eq, hx, true_or, or_true]
  have : ConnectedSpace {x // x ∈ U ∪ V} := by
    apply isConnected_iff_connectedSpace.mp
    have hConn (W : Set X) : Nonempty (W ≃ₜ ℝ) → IsConnected W := by
      intro hWR
      apply isConnected_iff_connectedSpace.mpr <| connectedSpace_iff_univ.mpr ?_
      exact hWR.some.symm.isConnected_preimage.mp isConnected_univ
    exact IsConnected.union Nonempty.of_subtype (hConn U hUR) (hConn V hVR)
  apply union_of_two_real_lines' hU' hV' hUniv ?_ ?_ <;> apply Nonempty.intro
  · exact hUU'.some.symm.trans hUR.some
  · exact hVV'.some.symm.trans hVR.some
