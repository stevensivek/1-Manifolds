import Mathlib.Tactic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import «OneManifold».RealLemmas

/-!
The main result of this file is `real_charts`, which takes a cover of a 1-manifold
by charts that are homeomorphisms onto open subsets of ℝ and provides one where
the homeomorphisms are onto all of ℝ.
-/

open Set Function Manifold
set_option linter.style.emptyLine false

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/- Let M be a compact connected topological 1-dimensional manifold. -/
variable (M : Type*) [TopologicalSpace M] [ChartedSpace ℝ¹ M]

namespace OpenIntervalHomeomorphReal

private lemma hIoo_shift {a b : ℝ} (hab : a < b) (t : Ioo a b) :
    (t - a) / (b - a) ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨x,⟨hx1,hx2⟩⟩ := t
  have habpos : b - a > 0 := by exact sub_pos.mpr hab
  constructor
  · exact div_pos (sub_pos.mpr hx1) habpos
  · exact (div_lt_one₀ habpos).mpr <| sub_lt_sub_right hx2 a

private lemma hIoo_shift' {a b : ℝ} (hab : a < b) (t : Ioo (0 : ℝ) 1) :
    (b - a) * t + a ∈ Ioo a b := by
  obtain ⟨x,⟨hx1,hx2⟩⟩ := t
  have habpos : b - a > 0 := by exact sub_pos.mpr hab
  constructor
  · exact lt_add_of_pos_left a <| mul_pos habpos hx1
  · exact lt_tsub_iff_right.mp <| mul_lt_of_lt_one_right habpos hx2

private noncomputable def homeomorph_Ioo_Ioo_unit {a b : ℝ} (hab : a < b) :
    Homeomorph (Ioo a b) (Ioo (0 : ℝ) 1) := {
  toFun : Ioo a b → Ioo (0 : ℝ) 1 := fun t ↦ ⟨(t - a) / (b - a), hIoo_shift hab t⟩,
  invFun : Ioo (0 : ℝ) 1 → Ioo a b := fun t ↦ ⟨(b - a) * t + a, hIoo_shift' hab t⟩,
  left_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    simp only [mul_div_cancel₀ (x - a) <| Ne.symm <| ne_of_lt <| sub_pos.mpr hab, sub_add_cancel],
  right_inv := by
    intro x
    apply Subtype.mk_eq_mk.mpr
    simp only [add_sub_cancel_right]
    apply mul_div_cancel_left₀
    exact Ne.symm <| ne_of_lt <| sub_pos.mpr hab,
  continuous_toFun := by fun_prop,
  continuous_invFun := by fun_prop
}

private noncomputable def homeomorph_tan_real : Homeomorph (Ioo (-(Real.pi / 2)) (Real.pi / 2)) ℝ :=
  Real.tanPartialHomeomorph.toHomeomorphSourceTarget.trans <| Homeomorph.Set.univ ℝ

/-- Every bounded open interval in ℝ is homeomorphic to ℝ itself. -/
noncomputable def homeomorph_Ioo_real {a b : ℝ} (hab : a < b) : (Ioo a b) ≃ₜ ℝ := by
  let f : (Ioo a b) ≃ₜ (Ioo (0 : ℝ) 1) := homeomorph_Ioo_Ioo_unit hab
  have : -(Real.pi / 2) < (Real.pi / 2) := by
    simp only [neg_lt_self_iff, Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact Real.pi_pos
  let g : (Ioo (0 : ℝ) 1) ≃ₜ (Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    (homeomorph_Ioo_Ioo_unit this).symm
  exact f.trans (g.trans homeomorph_tan_real)

private noncomputable def homeomorph_Ioi_Ioi (a : ℝ) : Ioi a ≃ₜ Ioi (0 : ℝ) := {
  toFun : Ioi a → Ioi (0 : ℝ) := fun t ↦ ⟨t - a, mem_Ioi.mpr <| sub_pos.mpr t.property⟩,
  invFun : Ioi (0 : ℝ) → Ioi a := fun t ↦ ⟨t + a, mem_Ioi.mpr <| lt_add_of_pos_left a t.property⟩,
  left_inv := fun x => by simp only [sub_add_cancel],
  right_inv := fun x => by simp only [add_sub_cancel_right, Subtype.coe_eta],
  continuous_toFun := by fun_prop,
  continuous_invFun := by fun_prop
}

private noncomputable def homeomorph_neg_Iio (a : ℝ) : Iio a ≃ₜ Ioi (-a) := {
  toFun : Iio a → Ioi (-a) := fun t ↦ ⟨-t, mem_Ioi.mpr <| neg_lt_neg_iff.mpr t.property⟩,
  invFun : Ioi (-a) → Iio a := fun t ↦ ⟨-t, mem_Iio.mpr <| neg_lt_of_neg_lt t.property⟩,
  left_inv := fun x => by simp only [neg_neg, Subtype.coe_eta],
  right_inv := fun x => by simp only [neg_neg, Subtype.coe_eta],
  continuous_toFun := by fun_prop,
  continuous_invFun := by fun_prop
}

/- Any open, connected subset of ℝ is homeomorphic to ℝ. -/
theorem homeomorph_open_real {U : Set ℝ} (hOpen : IsOpen U) (hConn : IsConnected U) :
    Nonempty (U ≃ₜ ℝ) := by
  have expHomeo : Ioi (0 : ℝ) ≃ₜ ℝ := by
    let φ := Real.expPartialHomeomorph.toHomeomorphSourceTarget
    rw [Real.expPartialHomeomorph_source, Real.expPartialHomeomorph_target] at φ
    exact φ.symm.trans <| Homeomorph.Set.univ ℝ
  rcases (open_real_classification U hOpen hConn) with h | h | h | h
  · obtain ⟨a, b, hIoo⟩ := h
    rw [hIoo]
    have hab : a < b := by
      have : Nonempty U := Nonempty.to_subtype hConn.nonempty
      have : (Ioo a b).Nonempty := nonempty_coe_sort.mp (by rwa [hIoo] at this)
      obtain ⟨hat, htb⟩ := mem_Ioo.mp this.some_mem
      exact lt_trans hat htb
    exact Nonempty.intro <| homeomorph_Ioo_real hab
  · obtain ⟨a, hIio⟩ := h
    rw [hIio]
    have φ : Iio a ≃ₜ Ioi (0 : ℝ) := (homeomorph_neg_Iio a).trans (homeomorph_Ioi_Ioi (-a))
    exact Nonempty.intro <| φ.trans expHomeo
  · obtain ⟨a, hIoi⟩ := h
    rw [hIoi]
    exact Nonempty.intro <| (homeomorph_Ioi_Ioi a).trans expHomeo
  · rw [h]
    exact Nonempty.intro <| Homeomorph.Set.univ ℝ

end OpenIntervalHomeomorphReal

private class RealChart (p : M) where
  U : Set M
  contains_x : p ∈ U
  isOpen : IsOpen U
  chartAt : U ≃ₜ ℝ

/-- Every point of a 1-manifold M has an open neighborhood homeomorphic to ℝ. -/
private lemma chart_homeo_real (x : M) : Nonempty (RealChart M x) := by
  let φ : ℝ¹ ≃ₜ ℝ := (PiLp.homeomorph 2 (fun (_ : Fin 1) => ℝ)).trans
                    <| Homeomorph.funUnique (Fin 1) ℝ
  let ψ := (chartAt ℝ¹ x).transHomeomorph φ
  let y : ℝ := ψ x
  have hxψ : x ∈ ψ.source := by
    simp_all only [(chartAt ℝ¹ x).transHomeomorph_source, mem_chart_source, ψ]

  have : ∃ (a : ℝ) (b : ℝ), a < b ∧ y ∈ (Ioo a b) ∧ (Ioo a b) ⊆ ψ.target := by
    have hyTarget : y ∈ ψ.target := ψ.map_source hxψ
    obtain ⟨W, hW, hyW, hWψ⟩ := (Real.isTopologicalBasis_Ioo_rat).exists_subset_of_mem_open
                                 hyTarget ψ.open_target
    simp only [mem_iUnion, mem_singleton_iff, exists_prop] at hW
    obtain ⟨a, b, hab, hWIoo⟩ := hW
    use a, b
    refine ⟨Real.ratCast_lt.mpr hab, by rwa [hWIoo] at hyW, Eq.trans_subset (Eq.symm hWIoo) hWψ⟩

  obtain ⟨a,b,hab,hyab,habV⟩ := this
  let U' := ψ.symm '' (Ioo a b)
  have f : U' ≃ₜ (Ioo a b) := by
    apply ψ.homeomorphOfImageSubsetSource
    · exact MapsTo.image_subset <| fun _ p ↦ ψ.symm_mapsTo (habV p)
    · exact LeftInvOn.image_image <| fun _ ht => ψ.right_inv (habV ht)

  let chart : RealChart M x := {
    U : Set M := U',
    contains_x : x ∈ U' := by
      apply (mem_image ψ.symm (Ioo a b) x).mpr
      use y
      exact ⟨hyab, ψ.left_inv hxψ⟩,
    isOpen : IsOpen U' := ψ.isOpen_image_symm_of_subset_target isOpen_Ioo habV,
    chartAt := f.trans <| OpenIntervalHomeomorphReal.homeomorph_Ioo_real hab
  }
  exact Nonempty.intro chart

/-- Package the homeomorphisms to ℝ at each point into a function -/
lemma real_charts : ∃ U : M → Set M,
    (∀ x, x ∈ U x) ∧ (∀ x, IsOpen (U x)) ∧ (∀ x, Nonempty ((U x) ≃ₜ ℝ)) := by
  let f := fun p => (chart_homeo_real M p).some
  use fun p => (f p).U
  exact ⟨fun x => (f x).contains_x, fun x => (f x).isOpen,
         fun x => Nonempty.intro (f x).chartAt⟩
