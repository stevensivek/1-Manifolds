import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import «OneManifold».OverlapLemmas

/-!
This file contains several theorems about gluing constructions that produce
spaces homeomorphic to a circle.  The spaces X in these theorems are assumed
to be Hausdorff.

## Main results

- `homeomorph_circle_of_glue_icc_icc` : Suppose that X is the union of two
  sets `A ≃ₜ Icc c d` and `B ≃ₜ Icc e f` respectively, and that `A ∩ B`
  consists of the two endpoints of either interval, where `c` is identified
  with `e` and `d` is identified with `f`.  Then X is homeomorphic to a circle.

- `homeomorph_circle_of_glue_icc_icc'` : This is the same theorem as
  `homeomorph_circle_of_glue_icc_icc`, except that now `c` and `d` are
  assumed to be identified with `f` and `e` respectively.

- `homeomorph_circle_of_glue_open_real_real`: If X is connected and the union
  of two open sets `U` and `V`, where both `U` and `V` are homeomorphic to
  ℝ and `U ∩ V` is not connected, then X is homeomorphic to a circle.
-/

open Set Function
set_option linter.style.emptyLine false

section CircleGlueIcc

private lemma mem_union_and_not_mem_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hUnion : A ∪ B = univ) {t : X} (ht : t ∉ A) : t ∈ B := by
  have : t ∈ A ∪ B := hUnion ▸ trivial
  simpa only [mem_union, ht, false_or] using this

noncomputable def icc_glue_circle_map {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ) : X → ℂ :=
  fun t => if h : t ∈ A
              then (circleMap 0 1) (Real.pi * (φ ⟨t, h⟩))
              else (circleMap 0 1) (-Real.pi * (ψ ⟨t, mem_union_and_not_mem_left hUnion h⟩))

lemma icc_glue_circle_map_eval_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {t : X} (hA : t ∈ A) :
    (icc_glue_circle_map φ ψ hUnion) t = (circleMap 0 1) (Real.pi * (φ ⟨t, hA⟩)) := by
  simp only [icc_glue_circle_map, hA, ↓reduceDIte]

private lemma eval_homeomorph_subtype_of_symm_val
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {φ : A ≃ₜ Y} {x : X} {y : Y} (hφ : ↑(φ.symm y) = x) :
    ∀ h : x ∈ A, φ ⟨x, h⟩ = y := by
  subst x
  exact fun _ ↦ by simp only [Subtype.coe_eta, φ.apply_symm_apply]

lemma icc_glue_circle_map_eval_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y}) {t : X} (hB : t ∈ B)
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y) :
    (icc_glue_circle_map φ ψ hUnion) t = (circleMap 0 1) (-Real.pi * (ψ ⟨t, hB⟩)) := by
  by_cases hA : t ∈ A <;> simp only [icc_glue_circle_map, hA, ↓reduceDIte]
  · rcases (show t ∈ {x, y} by exact hInter ▸ mem_inter hA hB) with htx | hty <;> subst t
    · rw [eval_homeomorph_subtype_of_symm_val hφx hA, eval_homeomorph_subtype_of_symm_val hψx hB,
          Icc.coe_zero, mul_zero, mul_zero]
    · rw [eval_homeomorph_subtype_of_symm_val hφy hA, eval_homeomorph_subtype_of_symm_val hψy hB,
          Icc.coe_one, mul_one, mul_one, ← periodic_circleMap 0 1 (- Real.pi)]
      apply congrArg (circleMap 0 1)
      have : (2 : ℝ) - 1 = 1 := by norm_num
      rw [← neg_one_mul Real.pi, ← add_mul, neg_add_eq_sub 1 2, this, one_mul]

lemma icc_glue_circle_map_continuousOn_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ) :
    ContinuousOn (icc_glue_circle_map φ ψ hUnion) A := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : A.restrict (icc_glue_circle_map φ ψ hUnion) =
         fun a => (circleMap 0 1 (Real.pi * φ a)) := by
    ext x
    simp only [restrict_apply]
    exact icc_glue_circle_map_eval_left φ ψ hUnion (Subtype.coe_prop x)
  rw [this]
  fun_prop

lemma icc_glue_circle_map_continuousOn_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y) :
    ContinuousOn (icc_glue_circle_map φ ψ hUnion) B := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : B.restrict (icc_glue_circle_map φ ψ hUnion) =
         fun b => (circleMap 0 1 (-Real.pi * ψ b)) := by
    ext x
    simp only [restrict_apply]
    exact icc_glue_circle_map_eval_right φ ψ hUnion hInter (Subtype.coe_prop x) hφx hψx hφy hψy
  rw [this]
  fun_prop

lemma icc_glue_circle_map_continuous {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y)
    (hAClosed : IsClosed A) (hBClosed : IsClosed B) :
    Continuous (icc_glue_circle_map φ ψ hUnion) := by
  apply continuousOn_univ.mp
  exact hUnion ▸ (continuousOn_union_iff_of_isClosed hAClosed hBClosed).mpr
    ⟨icc_glue_circle_map_continuousOn_left φ ψ hUnion,
     icc_glue_circle_map_continuousOn_right φ ψ hUnion hInter hφx hψx hφy hψy⟩

lemma icc_glue_circle_map_continuous' {X : Type*} [TopologicalSpace X] [T2Space X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y) :
    Continuous (icc_glue_circle_map φ ψ hUnion) := by
  have hA : IsCompact A := isCompact_iff_compactSpace.mpr φ.symm.compactSpace
  have hB : IsCompact B := isCompact_iff_compactSpace.mpr ψ.symm.compactSpace
  exact icc_glue_circle_map_continuous φ ψ hUnion hInter hφx hψx hφy hψy
    hA.isClosed hB.isClosed

private lemma bound_pi_times_unitInterval {Y : Type*} [TopologicalSpace Y]
    (φ : Y ≃ₜ unitInterval) (y : Y) : 0 ≤ Real.pi * (φ y) ∧ Real.pi * (φ y) ≤ Real.pi := by
  constructor
  · exact mul_nonneg Real.pi_nonneg unitInterval.nonneg'
  · nth_rewrite 2 [← mul_one Real.pi]
    exact (mul_le_mul_iff_of_pos_left Real.pi_pos).mpr unitInterval.le_one'

private lemma bound_sub_pi_times_unitInterval {Y : Type*} [TopologicalSpace Y]
    (φ : Y ≃ₜ unitInterval) (y z : Y) :
    |(Real.pi * φ y) - (Real.pi * φ z)| < 2 * Real.pi := by
  obtain ⟨zero_le_y, y_le_pi⟩ := bound_pi_times_unitInterval φ y
  obtain ⟨zero_le_z, z_le_pi⟩ := bound_pi_times_unitInterval φ z
  calc
  |(Real.pi * φ y) - (Real.pi * φ z)| ≤ Real.pi
                  := abs_sub_le_of_nonneg_of_le zero_le_y y_le_pi zero_le_z z_le_pi
  _ < 2 * Real.pi := lt_two_mul_self Real.pi_pos

private lemma inter_two_points_mem_each {X : Type*} [TopologicalSpace X]
    {A B : Set X} {x y : X} (hInter : A ∩ B = {x, y}) :
    x ∈ A ∧ x ∈ B ∧ y ∈ A ∧ y ∈ B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply mem_of_subset_of_mem <| inter_subset_left (t := B)
    exact hInter ▸ mem_insert x {y}
  · apply mem_of_subset_of_mem <| inter_subset_right (s := A)
    exact hInter ▸ mem_insert x {y}
  · apply mem_of_subset_of_mem <| inter_subset_left (t := B)
    exact hInter ▸ mem_insert_of_mem x rfl
  · apply mem_of_subset_of_mem <| inter_subset_right (s := A)
    exact hInter ▸ mem_insert_of_mem x rfl

lemma icc_glue_circle_map_im_nonneg {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y)
    {t : X} : (icc_glue_circle_map φ ψ hUnion t).im ≥ 0 ↔ t ∈ A := by
  obtain ⟨hxA, hxB, hyA, hyB⟩ := inter_two_points_mem_each hInter
  constructor <;> intro h
  · by_contra hA
    have hB : t ∈ B := mem_union_and_not_mem_left hUnion hA
    rw [icc_glue_circle_map_eval_right φ ψ hUnion hInter hB hφx hψx hφy hψy, circleMap_zero] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      one_mul, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im, neg_mul, Real.sin_neg] at h
    apply neg_nonneg.mp at h
    obtain ⟨hnonneg, hle_pi⟩ := bound_pi_times_unitInterval ψ ⟨t, hB⟩
    have hsin_zero : Real.sin (Real.pi * ψ ⟨t, hB⟩) = 0 :=
      eq_of_le_of_ge h <| Real.sin_nonneg_of_nonneg_of_le_pi hnonneg hle_pi
    by_cases hψ : Real.pi * ψ ⟨t, hB⟩ < Real.pi
    · have : -Real.pi < Real.pi * ψ ⟨t, hB⟩ :=
        lt_of_lt_of_le (neg_neg_iff_pos.mpr Real.pi_pos) hnonneg
      have := (Real.sin_eq_zero_iff_of_lt_of_lt this hψ).mp hsin_zero
      apply (mul_eq_zero_iff_left Real.pi_ne_zero).mp at this
      rw [← Icc.coe_eq_zero.mpr <| eval_homeomorph_subtype_of_symm_val hψx hxB] at this
      have : t = x := Subtype.mk_eq_mk.mp <| ψ.injective <| SetCoe.ext this
      exact hA (this ▸ hxA)
    · have : Real.pi * ψ ⟨t, hB⟩ = Real.pi := eq_of_le_of_ge hle_pi <| not_lt.mp hψ
      apply (mul_eq_left₀ Real.pi_ne_zero).mp at this
      rw [← Icc.coe_eq_one.mpr <| eval_homeomorph_subtype_of_symm_val hψy hyB] at this
      have : t = y := Subtype.mk_eq_mk.mp <| ψ.injective <| SetCoe.ext this
      exact hA (this ▸ hyA)
  · rw [icc_glue_circle_map_eval_left φ ψ hUnion h, circleMap_zero]
    simp only [Complex.mul_im, Complex.ofReal_re, one_mul, Complex.ofReal_im, zero_mul, add_zero]
    rw [Complex.exp_ofReal_mul_I_im]
    obtain ⟨hnonneg, hle_pi⟩ := bound_pi_times_unitInterval φ ⟨t, h⟩
    exact Real.sin_nonneg_of_nonneg_of_le_pi hnonneg hle_pi

lemma icc_glue_circle_map_injOn_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ) :
    InjOn (icc_glue_circle_map φ ψ hUnion) A := by
  intro s hs t ht heq
  rw [icc_glue_circle_map_eval_left φ ψ hUnion hs,
      icc_glue_circle_map_eval_left φ ψ hUnion ht] at heq
  have := bound_sub_pi_times_unitInterval φ ⟨s, hs⟩ ⟨t, ht⟩
  have := eq_of_circleMap_eq one_ne_zero this heq
  apply (mul_right_inj' Real.pi_ne_zero).mp at this
  exact Subtype.mk_eq_mk.mp <| φ.injective <| SetCoe.ext this

lemma icc_glue_circle_map_injOn_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y) :
    InjOn (icc_glue_circle_map φ ψ hUnion) B := by
  intro s hs t ht heq
  rw [icc_glue_circle_map_eval_right φ ψ hUnion hInter hs hφx hψx hφy hψy,
      icc_glue_circle_map_eval_right φ ψ hUnion hInter ht hφx hψx hφy hψy] at heq
  have : |(Real.pi * ψ ⟨t, ht⟩) - (Real.pi * ψ ⟨s, hs⟩)| < 2 * Real.pi :=
    bound_sub_pi_times_unitInterval ψ ⟨t, ht⟩ ⟨s, hs⟩
  rw [← neg_sub_neg, neg_mul_eq_neg_mul, neg_mul_eq_neg_mul] at this
  have := eq_of_circleMap_eq one_ne_zero this heq
  apply (mul_right_inj' <| neg_ne_zero.mpr Real.pi_ne_zero).mp at this
  exact Subtype.mk_eq_mk.mp <| ψ.injective <| SetCoe.ext this

lemma icc_glue_circle_map_injective {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y) :
    Injective (icc_glue_circle_map φ ψ hUnion) := by
  intro s t heq
  by_cases hs : s ∈ A <;> by_cases ht : t ∈ A
  · exact icc_glue_circle_map_injOn_left φ ψ hUnion hs ht heq
  · have h₁ := (icc_glue_circle_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy).mpr hs
    have h₂ := (not_iff_not.mpr
                (icc_glue_circle_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy)).mpr ht
    exact False.elim <| h₂ (heq ▸ h₁)
  · have h₁ := (icc_glue_circle_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy).mpr ht
    have h₂ := (not_iff_not.mpr
                (icc_glue_circle_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy)).mpr hs
    exact False.elim <| h₂ (heq ▸ h₁)
  · exact icc_glue_circle_map_injOn_right φ ψ hUnion hInter hφx hψx hφy hψy
      (mem_union_and_not_mem_left hUnion hs) (mem_union_and_not_mem_left hUnion ht) heq

lemma icc_glue_circle_map_range {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y) :
    range (icc_glue_circle_map φ ψ hUnion) = Metric.sphere (0 : ℂ) 1 := by
  apply Subset.antisymm <;> intro t ht
  · obtain ⟨s, hs⟩ := ht
    subst t
    by_cases h : s ∈ A
    · rw [icc_glue_circle_map_eval_left φ ψ hUnion h, Metric.mem_sphere]
      simp only [dist_zero_right, norm_circleMap_zero, abs_one]
    · have h' : s ∈ B := mem_union_and_not_mem_left hUnion h
      rw [icc_glue_circle_map_eval_right φ ψ hUnion hInter h' hφx hψx hφy hψy,
        Metric.mem_sphere]
      simp only [dist_zero_right, norm_circleMap_zero, abs_one]
  · apply mem_range.mpr
    have hnorm : ‖t - 0‖ = 1 := mem_sphere_iff_norm.mp ht
    simp only [sub_zero] at hnorm
    let θ := Complex.arg (t - 0)
    obtain ⟨h_neg_pi, h_pos_pi⟩ := Complex.arg_mem_Ioc (t - 0)
    by_cases hθ : 0 ≤ θ
    · let s : ℝ := θ / Real.pi
      have hπsθ : Real.pi * s = θ := mul_div_cancel₀ θ Real.pi_ne_zero
      have hs0 : 0 ≤ s := by
        apply div_nonneg_iff.mpr
        simp only [hθ, Real.pi_nonneg, true_and, true_or]
      have hs1 : s ≤ 1 := (div_le_one₀ Real.pi_pos).mpr h_pos_pi
      use φ.symm ⟨s, mem_Icc.mpr ⟨hs0, hs1⟩⟩
      rw [icc_glue_circle_map_eval_left φ ψ hUnion (by apply Subtype.coe_prop),
          ← Complex.norm_mul_exp_arg_mul_I t, hnorm]
      simp only [Subtype.coe_eta, φ.apply_symm_apply, circleMap_zero, hπsθ, θ, sub_zero]
    · replace hθ : θ < 0 := not_le.mp hθ
      let s : ℝ := -θ / Real.pi
      have hπsθ : -Real.pi * s = θ := by
        simp only [neg_mul]
        exact neg_eq_iff_eq_neg.mpr <| mul_div_cancel₀ (-θ) Real.pi_ne_zero
      have hs0 : 0 ≤ s := by
        apply div_nonneg_iff.mpr
        simp only [neg_nonneg.mpr <| le_of_lt hθ, Real.pi_nonneg, true_and, true_or]
      have hs1 : s ≤ 1 := by
        apply (div_le_one₀ Real.pi_pos).mpr
        exact le_of_lt <| neg_lt_of_neg_lt h_neg_pi
      use ψ.symm ⟨s, mem_Icc.mpr ⟨hs0, hs1⟩⟩
      rw [icc_glue_circle_map_eval_right φ ψ hUnion hInter
            (by apply Subtype.coe_prop) hφx hψx hφy hψy]
      rw [← Complex.norm_mul_exp_arg_mul_I t, hnorm]
      simp only [Subtype.coe_eta, ψ.apply_symm_apply, circleMap_zero, hπsθ, θ, sub_zero]

lemma glue_intervals_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    {A B : Set X} (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ) :
    CompactSpace X := by
  apply isCompact_univ_iff.mp
  apply hUnion ▸ IsCompact.union ?_ ?_ <;>
    apply isCompact_iff_isCompact_univ.mpr <| isCompact_univ_iff.mpr ?_
  · exact φ.symm.compactSpace
  · exact ψ.symm.compactSpace

lemma glue_unit_intervals_circle₀ {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : Set X) (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval)
    (hUnion : A ∪ B = univ) {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm 0) = x) (hψx : ↑(ψ.symm 0) = x)
    (hφy : ↑(φ.symm 1) = y) (hψy : ↑(ψ.symm 1) = y) :
    Nonempty (X ≃ₜ Circle) := by
  classical -- need membership in A to be decidable
  haveI : CompactSpace X := glue_intervals_compact φ ψ hUnion
  let f : X → ℂ := icc_glue_circle_map φ ψ hUnion
  let g : X → range f := fun t ↦ ⟨f t, mem_range_self t⟩
  have hgCont : Continuous g := by
    apply Continuous.subtype_mk ?_ mem_range_self
    exact icc_glue_circle_map_continuous' φ ψ hUnion hInter hφx hψx hφy hψy
  have hgInj : Injective g := by
    have hfInj : Injective f :=
      icc_glue_circle_map_injective φ ψ hUnion hInter hφx hψx hφy hψy
    exact fun _ _ hst ↦ hfInj <| Subtype.mk_eq_mk.mp hst
  have hgSurj : Surjective g := by
    intro s
    obtain ⟨t, ht⟩ := mem_range.mpr (Subtype.coe_prop s)
    exact ⟨t, SetCoe.ext ht⟩
  have hgHomeomorph : IsHomeomorph g :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨hgCont, ⟨hgInj, hgSurj⟩⟩
  let ι : range f ≃ₜ Circle := by
    rw [icc_glue_circle_map_range φ ψ hUnion hInter hφx hψx hφy hψy]
    exact Homeomorph.refl Circle
  exact Nonempty.intro <| hgHomeomorph.homeomorph.trans ι

private lemma homeo_symm {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set X} {D : Set Y} {α : C ≃ₜ D} {z : X} {y : D}
    (hC : z ∈ C) (hα : (α ⟨z, hC⟩).val = y.val) : ↑(α.symm y) = z :=
  Subtype.coe_eq_iff.mpr ⟨hC, α.symm_apply_eq.mpr <| SetCoe.ext (Eq.symm hα)⟩

theorem homeomorph_circle_of_glue_icc_icc {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : Set X) {c d e f : ℝ} (hcd : c < d) (hef : e < f)
    (φ : A ≃ₜ Icc c d) (ψ : B ≃ₜ Icc e f)
    (hUnion : A ∪ B = univ) {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm ⟨c, left_mem_Icc.mpr (le_of_lt hcd)⟩) = x)
    (hψx : ↑(ψ.symm ⟨e, left_mem_Icc.mpr (le_of_lt hef)⟩) = x)
    (hφy : ↑(φ.symm ⟨d, right_mem_Icc.mpr (le_of_lt hcd)⟩) = y)
    (hψy : ↑(ψ.symm ⟨f, right_mem_Icc.mpr (le_of_lt hef)⟩) = y) :
    Nonempty (X ≃ₜ Circle) := by
  obtain ⟨hAx, hBx, hAy, hBy⟩ := inter_two_points_mem_each hInter
  let φ' : A ≃ₜ unitInterval := φ.trans <| iccHomeoI c d hcd
  obtain ⟨hφ'x, hφ'y⟩ : φ' ⟨x, hAx⟩ = (0 : ℝ) ∧ φ' ⟨y, hAy⟩ = (1 : ℝ) := by
    have (x : Icc c d) : (iccHomeoI c d hcd) x = (x.val - c) / (d - c) := by rfl
    simp only [φ', φ.trans_apply, this,
               eval_homeomorph_subtype_of_symm_val hφx hAx,
               eval_homeomorph_subtype_of_symm_val hφy hAy,
               sub_self, zero_div, div_self_eq_one₀, true_and]
    exact Ne.symm <| ne_of_lt <| sub_pos.mpr hcd
  let ψ' : B ≃ₜ unitInterval := ψ.trans <| iccHomeoI e f hef
  obtain ⟨hψ'x, hψ'y⟩ : ψ' ⟨x, hBx⟩ = (0 : ℝ) ∧ ψ' ⟨y, hBy⟩ = (1 : ℝ) := by
    have (x : Icc e f) : (iccHomeoI e f hef) x = (x.val - e) / (f - e) := by rfl
    simp only [ψ', ψ.trans_apply, this,
               eval_homeomorph_subtype_of_symm_val hψx hBx,
               eval_homeomorph_subtype_of_symm_val hψy hBy,
               sub_self, zero_div, div_self_eq_one₀, true_and]
    exact Ne.symm <| ne_of_lt <| sub_pos.mpr hef
  exact glue_unit_intervals_circle₀ A B φ' ψ' hUnion hInter
        (homeo_symm hAx hφ'x) (homeo_symm hBx hψ'x) (homeo_symm hAy hφ'y) (homeo_symm hBy hψ'y)

theorem homeomorph_circle_of_glue_icc_icc' {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : Set X) {c d e f : ℝ} (hcd : c < d) (hef : e < f)
    (φ : A ≃ₜ Icc c d) (ψ : B ≃ₜ Icc e f)
    (hUnion : A ∪ B = univ) {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ↑(φ.symm ⟨c, left_mem_Icc.mpr (le_of_lt hcd)⟩) = x)
    (hψx : ↑(ψ.symm ⟨f, right_mem_Icc.mpr (le_of_lt hef)⟩) = x)
    (hφy : ↑(φ.symm ⟨d, right_mem_Icc.mpr (le_of_lt hcd)⟩) = y)
    (hψy : ↑(ψ.symm ⟨e, left_mem_Icc.mpr (le_of_lt hef)⟩) = y) :
    Nonempty (X ≃ₜ Circle) := by
  obtain ⟨hAx, hBx, hAy, hBy⟩ := inter_two_points_mem_each hInter
  let ψ' : B ≃ₜ Icc e f := ψ.trans (icc_flip hef)
  have hψ'x : ψ'.symm ⟨e, left_mem_Icc.mpr (le_of_lt hef)⟩ = x := by
    simp only [ψ', ψ.symm_trans_apply, icc_flip_symm, ← hψx]
    exact Subtype.ext_iff.mp <| congrArg ψ.symm <| SetCoe.ext <| icc_flip_left hef
  have hψ'y : ψ'.symm ⟨f, right_mem_Icc.mpr (le_of_lt hef)⟩ = y := by
    simp only [ψ', ψ.symm_trans_apply, icc_flip_symm, ← hψy]
    exact Subtype.ext_iff.mp <| congrArg ψ.symm <| SetCoe.ext <| icc_flip_right hef
  exact homeomorph_circle_of_glue_icc_icc A B hcd hef φ ψ' hUnion hInter hφx hψ'x hφy hψ'y

end CircleGlueIcc

private lemma not_nested_disconnected_intersection {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hNotConn : ¬ IsConnected (U ∩ V))
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    (hVConn : IsConnected V) :
    ¬(U ⊆ V) ∧ ¬ (V ⊆ U) := by
  constructor <;> by_contra h
  · rw [← left_eq_inter.mpr h, ← hφSource] at hNotConn
    exact hNotConn <| partial_homeomorph_IsConnected_source hφTarget
  · rw [← right_eq_inter.mpr h] at hNotConn
    exact hNotConn hVConn

/- If X = U ∪ V where U and V are homeomorphic to ℝ, and if U ∩ V is not
   connected, then the image of U ∩ V inside ℝ has connected components of
   the form Iio a and Ioi b. -/
private lemma glue_real_disconnected_intersection_intervals
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {U V : Set X} (hUniv : U ∪ V = univ) (hNotConn : ¬ IsConnected (U ∩ V))
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    (hV : IsOpen V) (hVConn : IsConnected V) :
    ∃ x y : X, ∃ a b : ℝ, x ∈ U ∩ V ∧ y ∈ U ∩ V ∧ a ≤ b
      ∧ connectedComponentIn (φ '' (U ∩ V)) (φ x) = Iio a
      ∧ connectedComponentIn (φ '' (U ∩ V)) (φ y) = Ioi b := by

  obtain ⟨hNotUV, hNotVU⟩ := not_nested_disconnected_intersection
    hNotConn hφSource hφTarget hVConn

  have hU : IsOpen U := hφSource ▸ φ.open_source
  have hUConn : IsConnected U := hφSource ▸ partial_homeomorph_IsConnected_source hφTarget
  have hNotConn_φ : ¬ IsConnected (φ '' (U ∩ V)) := by
    have : U ∩ V ⊆ φ.source := hφSource ▸ inter_subset_left
    exact fun h ↦ hNotConn <| (partial_homeomorph_image_connected_iff φ this).mpr h

  have hNonempty : Nonempty (U ∩ V : Set X) :=
    nonempty_inter_connected_open_cover hU hV hUniv hNotUV hNotVU

  let x : X := hNonempty.some
  have hx : x ∈ U ∩ V := Subtype.coe_prop hNonempty.some
  have hφx : φ x ∈ φ '' (U ∩ V) := mem_image_of_mem φ hx
  let Cφx : Set ℝ := connectedComponentIn (φ '' (U ∩ V)) (φ x)
  obtain ⟨y, hy, hCφy⟩ : ∃ y : X,
      y ∈ U ∩ V ∧ connectedComponentIn (φ '' (U ∩ V)) (φ y) ≠ Cφx := by
    by_contra! h
    have : φ '' (U ∩ V) = Cφx := by
      apply Subset.antisymm ?_ <| connectedComponentIn_subset (φ '' (U ∩ V)) (φ x)
      intro z ⟨y, hyUV, hφy⟩
      subst z
      have h' := mem_connectedComponentIn <| mem_image_of_mem φ hyUV
      rwa [h y hyUV] at h'
    exact (this ▸ hNotConn_φ) <| isConnected_connectedComponentIn_iff.mpr hφx
  let Cφy : Set ℝ := connectedComponentIn (φ '' (U ∩ V)) (φ y)

  have hDisjoint : Disjoint Cφx Cφy := by
    apply Set.disjoint_iff.mpr
    by_contra h
    obtain ⟨_, ha⟩ := Classical.not_forall_not.mp h
    have hxy := connectedComponentIn_eq <| mem_of_mem_inter_right ha
    rw [← connectedComponentIn_eq <| mem_of_mem_inter_left ha] at hxy
    exact hCφy hxy

  have hφCx := intersection_intervals
    hφSource hφTarget hV hVConn hNotUV hNotVU (mem_image_of_mem φ hx)

  have hφCy := intersection_intervals
    hφSource hφTarget hV hVConn hNotUV hNotVU (mem_image_of_mem φ hy)

  rcases hφCx with hCx | hCx <;> rcases hφCy with hCy | hCy
    <;> (obtain ⟨a, ha⟩ := hCx; obtain ⟨b, hb⟩ := hCy)
  · -- hCx = Iio a, hCy = Iio b contradicts hDisjoint
    obtain ⟨c, hc_lt⟩ := exists_lt (min a b)
    have hc : c ∈ Cφx ∩ Cφy := by
      simp only [Cφx, Cφy, ha, hb]
      apply mem_inter <;> apply lt_of_lt_of_le hc_lt ?_
      · exact min_le_left a b
      · exact min_le_right a b
    have : ¬ Disjoint Cφx Cφy :=
      fun h ↦ (h.notMem_of_mem_left <| mem_of_mem_inter_left hc) <| mem_of_mem_inter_right hc
    exact False.elim <| this hDisjoint
  · -- hCx = Iio a, hCy = Ioi b
    have : a ≤ b := by
      simp only [Cφx, Cφy, ha, hb] at hDisjoint
      exact le_of_not_gt <| Iio_disjoint_Ioi_iff.mp hDisjoint
    use x, y, a, b
  · -- hCx = Ioi a, hCy = Iio b
    have : b ≤ a := by
      simp only [Cφx, Cφy, ha, hb] at hDisjoint
      exact le_of_not_gt <| Ioi_disjoint_Iio_iff.mp hDisjoint
    use y, x, b, a
  · -- hCx = Ioi a, hCy = Ioi b contradicts hDisjoint
    obtain ⟨c, hc_gt⟩ := exists_gt (max a b)
    have hc : c ∈ Cφx ∩ Cφy := by
      simp only [Cφx, Cφy, ha, hb]
      apply mem_inter <;> apply lt_of_le_of_lt ?_ hc_gt
      · exact le_max_left a b
      · exact le_max_right a b
    have : ¬ Disjoint Cφx Cφy :=
      fun h ↦ (h.notMem_of_mem_left <| mem_of_mem_inter_left hc) <| mem_of_mem_inter_right hc
    exact False.elim <| this hDisjoint

/- If X = U ∪ V where U and V are homeomorphic to ℝ, and the image of U ∩ V
   under φ : U ≃ₜ ℝ has connected components of the form Iio a and Ioi b, then
   these are the only connected components of the image. -/
private lemma disconnected_intersection_two_components
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {U V : Set X} (hNotConn : ¬ IsConnected (U ∩ V))
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    (hV : IsOpen V) (hVConn : IsConnected V) {x y : X} {a b : ℝ} :
      connectedComponentIn (φ '' (U ∩ V)) (φ x) = Iio a
      → connectedComponentIn (φ '' (U ∩ V)) (φ y) = Ioi b
      → φ '' (U ∩ V) = connectedComponentIn (φ '' (U ∩ V)) (φ x)
                       ∪ connectedComponentIn (φ '' (U ∩ V)) (φ y) := by
  intro hxa hyb
  by_contra h
  have hsub : connectedComponentIn (φ '' (U ∩ V)) (φ x)
            ∪ connectedComponentIn (φ '' (U ∩ V)) (φ y) ⊆ φ '' (U ∩ V) := by
    apply union_subset <;> apply connectedComponentIn_subset (φ '' (U ∩ V))
  obtain ⟨z, hzφ, hzComp⟩ := exists_of_ssubset
                             <| ssubset_of_subset_of_ne hsub <| Ne.symm h
  apply not_or.mp at hzComp
  obtain ⟨hNotUV, hNotVU⟩ := not_nested_disconnected_intersection
    hNotConn hφSource hφTarget hVConn
  let hzInt := intersection_intervals hφSource hφTarget hV hVConn hNotUV hNotVU hzφ
  have hzComponent : z ∈ connectedComponentIn (φ '' (U ∩ V)) z := mem_connectedComponentIn hzφ

  rcases hzInt with hInt | hInt <;> obtain ⟨c, hc⟩ := hInt
  · obtain ⟨d, hd⟩ := exists_lt (min a c)
    have hdx : d ∈ connectedComponentIn (φ '' (U ∩ V)) (φ x) :=
      hxa ▸ lt_of_le_of_lt' (min_le_left a c) hd
    have hdw : d ∈ connectedComponentIn (φ '' (U ∩ V)) z :=
      hc ▸ lt_of_le_of_lt' (min_le_right a c) hd
    rw [connectedComponentIn_eq hdw, ← connectedComponentIn_eq hdx] at hzComponent
    exact hzComp.1 hzComponent
  · obtain ⟨d, hd⟩ := exists_gt (max b c)
    have hdy : d ∈ connectedComponentIn (φ '' (U ∩ V)) (φ y) :=
      hyb ▸ lt_of_le_of_lt (le_max_left b c) hd
    have hdw : d ∈ connectedComponentIn (φ '' (U ∩ V)) z :=
      hc ▸ lt_of_le_of_lt (le_max_right b c) hd
    rw [connectedComponentIn_eq hdw, ← connectedComponentIn_eq hdy] at hzComponent
    exact hzComp.2 hzComponent

theorem homeomorph_circle_of_glue_open_real_real
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUniv : U ∪ V = @univ X) (hNotConn : ¬ IsConnected (U ∩ V))
    (hUR : Nonempty (U ≃ₜ ℝ)) (hVR : Nonempty (V ≃ₜ ℝ)) : Nonempty (X ≃ₜ Circle) := by

  obtain ⟨φ, hφSource, hφTarget⟩ := real_chart_to_partial_homeomorph hU hUR.some
  obtain ⟨ψ₀, hψ₀Source, hψ₀Target⟩ := real_chart_to_partial_homeomorph hV hVR.some
  obtain ⟨hUConn, hVConn⟩ : IsConnected U ∧ IsConnected V := by
    rw [← hφSource, ← hψ₀Source]
    constructor <;> apply partial_homeomorph_IsConnected_source <;> assumption
  obtain ⟨hNotUV, hNotVU⟩ := not_nested_disconnected_intersection
    hNotConn hφSource hφTarget hVConn

  obtain ⟨x,y,a,b,hx,hy,hab,hxφ,hyφ⟩ := glue_real_disconnected_intersection_intervals
    hUniv hNotConn hφSource hφTarget hV hVConn

  obtain ⟨ψ, hψSource, hψTarget, ⟨d, hxψ⟩⟩ := choose_intersection_component_right
    hψ₀Source hψ₀Target hU hUConn hNotVU hNotUV (show x ∈ V ∩ U by rwa [inter_comm])
  rw [inter_comm] at hxψ

  have hφ_symm_apply_apply {z : X} : z ∈ U ∩ V → φ.symm (φ z) = z :=
    fun _ ↦ by simp_all only [mem_inter_iff, φ.left_inv]
  have hφ_symm_apply_apply_image_UV : φ.symm '' (φ '' (U ∩ V)) = U ∩ V := by
    have : (φ.symm ∘ φ) '' (U ∩ V) = id '' (U ∩ V) :=
      image_congr (fun _ h ↦ hφ_symm_apply_apply h)
    rwa [image_comp, image_id (U ∩ V)] at this
  have hψ_symm_apply_apply {z : X} : z ∈ U ∩ V → ψ.symm (ψ z) = z :=
    fun _ ↦ by simp_all only [mem_inter_iff, ψ.left_inv]

  have hφsymmComponent {z : X} (hz : z ∈ U ∩ V) :
      φ.symm '' connectedComponentIn (φ '' (U ∩ V)) (φ z) ⊆
      connectedComponentIn (U ∩ V) z := by
    have hsubset : φ.symm '' (connectedComponentIn (φ '' (U ∩ V)) (φ z)) ⊆ U ∩ V := by
      nth_rewrite 2 [← hφ_symm_apply_apply_image_UV]
      exact image_mono <| connectedComponentIn_subset (φ '' (U ∩ V)) (φ z)
    have : IsConnected (φ.symm '' (connectedComponentIn (φ '' (U ∩ V)) (φ z))) := by
      apply IsConnected.image ?_ φ.symm ?_
      · exact isConnected_connectedComponentIn_iff.mpr <| mem_image_of_mem φ hz
      · apply φ.symm.continuousOn.mono
        rw [φ.symm_source, hφTarget]
        exact subset_univ _
    refine this.isPreconnected.subset_connectedComponentIn ?_ hsubset
    nth_rewrite 2 [← hφ_symm_apply_apply hz]
    exact mem_image_of_mem φ.symm <| mem_connectedComponentIn <| mem_image_of_mem φ hz

  let f := φ.symm.trans ψ
  have hfSource : φ '' (U ∩ V) ⊆ f.source := by
    rw [φ.symm.trans_source ψ, φ.symm_source, hφTarget, univ_inter, hψSource]
    intro _ ⟨_, hs, hst⟩
    apply mem_preimage.mpr
    rw [← hst, hφ_symm_apply_apply hs]
    exact mem_of_mem_inter_right hs
  have hfContOn : ContinuousOn f (φ '' (U ∩ V)) := f.continuousOn.mono hfSource
  have hfφx : f (φ x) = ψ x := by simp_all only [φ.symm.coe_trans, comp_apply, f]
  have hfφy : f (φ y) = ψ y := by simp_all only [φ.symm.coe_trans, comp_apply, f]
  have hfImage : f '' (φ '' (U ∩ V)) = (ψ '' (U ∩ V)) := by
    apply Subset.antisymm <;> intro t ⟨s,hs,hst⟩
    · rw [← hst]
      simp only [f, φ.symm.trans_apply] at hst
      apply mem_image_of_mem ψ
      have : φ.symm s ∈ U ∩ V := by
        obtain ⟨r, hr, hrs⟩ := hs
        rwa [← congrArg φ.symm hrs, hφ_symm_apply_apply hr]
      rwa [φ.symm_symm]
    · rw [← hst, ← hφ_symm_apply_apply hs]
      simp only [f, φ.symm.trans_apply, mem_image, exists_exists_and_eq_and]
      use s
  have hf_symm_apply_apply {z : ℝ} : z ∈ φ '' (U ∩ V) → f.symm (f z) = z :=
    fun h ↦ by simp_all only [mem_inter_iff, f.left_inv <| hfSource h, image_subset_iff, mem_image]
  have hfsymmImage : f.symm '' (ψ '' (U ∩ V)) = (φ '' (U ∩ V)) := by
    rw [← hfImage]
    apply Subset.antisymm <;> intro t ⟨s, hs, hst⟩
    · obtain ⟨r, hr, hrs⟩ := hs
      rwa [← hst, ← hrs, hf_symm_apply_apply hr]
    · rw [← image_comp, ← hst, ← hf_symm_apply_apply <| mem_image_of_mem φ hs]
      exact mem_image_of_mem (f.symm ∘ f) <| mem_image_of_mem φ hs

  let Cφx := connectedComponentIn (φ '' (U ∩ V)) (φ x)
  let Cφy := connectedComponentIn (φ '' (U ∩ V)) (φ y)
  let Cψx := connectedComponentIn (ψ '' (U ∩ V)) (ψ x)
  let Cψy := connectedComponentIn (ψ '' (U ∩ V)) (ψ y)

  have hψDisjoint : Disjoint Cψx Cψy := by
    have hφDisjoint : Disjoint (Iio a) (Ioi b) := Iio_disjoint_Ioi_of_le hab
    rw [← hxφ, ← hyφ] at hφDisjoint
    have hfsymm_component {z : X} (hz : z ∈ U ∩ V) :
        f.symm '' (connectedComponentIn (ψ '' (U ∩ V)) (ψ z)) ⊆
                   connectedComponentIn (φ '' (U ∩ V)) (φ z) := by
      let Cψz := connectedComponentIn (ψ '' (U ∩ V)) (ψ z)
      have : ContinuousOn f.symm Cψz := by
        apply f.symm.continuousOn.mono
        apply subset_trans (connectedComponentIn_subset (ψ '' (U ∩ V)) (ψ z)) ?_
        rw [f.symm_source, ← hfImage, ← f.image_source_eq_target]
        exact image_mono hfSource
      have hfCψxConn : IsConnected (f.symm '' Cψz) := IsConnected.image
        (isConnected_connectedComponentIn_iff.mpr <| mem_image_of_mem ψ hz) f.symm this
      have hφz_fsymm : φ z ∈ f.symm '' Cψz := by
        have : f (φ z) ∈ Cψz := by
          simp only [f, φ.symm.trans_apply, hφ_symm_apply_apply hz]
          exact mem_connectedComponentIn <| mem_image_of_mem ψ hz
        apply mem_image_of_mem f.symm at this
        rwa [← f.left_inv <| hfSource <| mem_image_of_mem φ hz]
      have : f.symm '' Cψz ⊆ φ '' (U ∩ V) := by
        apply Subset.trans (image_mono <| connectedComponentIn_subset (ψ '' (U ∩ V)) (ψ z))
        exact subset_of_eq_of_subset hfsymmImage (by apply subset_refl)
      exact hfCψxConn.isPreconnected.subset_connectedComponentIn hφz_fsymm this
    by_contra h
    obtain ⟨t, htCψx, htCψy⟩ := not_disjoint_iff.mp h
    have : ¬ Disjoint Cφx Cφy := not_disjoint_iff.mpr ⟨f.symm t,
        hfsymm_component hx <| mem_image_of_mem f.symm htCψx,
        hfsymm_component hy <| mem_image_of_mem f.symm htCψy⟩
    exact this hφDisjoint

  obtain ⟨c, hyψ⟩ : ∃ c, connectedComponentIn (ψ '' (U ∩ V)) (ψ y) = Iio c := by
    have hy' : ψ y ∈ ψ '' (V ∩ U) := mem_image_of_mem ψ (by rwa [inter_comm] at hy)
    have hcc := intersection_intervals hψSource hψTarget hU hUConn hNotVU hNotUV hy'
    by_contra h
    simp only [inter_comm, h, false_or] at hcc
    obtain ⟨e, he⟩ := hcc
    simp only [Cψx, Cψy, hxψ, he] at hψDisjoint
    have : ¬ Disjoint (Ioi d) (Ioi e) := not_disjoint_iff.mpr ⟨max d e + 1,
        lt_of_le_of_lt (le_max_left d e) (lt_add_one (max d e)),
        lt_of_le_of_lt (le_max_right d e) (lt_add_one (max d e))⟩
    exact this hψDisjoint

  have hcd : c ≤ d := by
    simp only [Cψx, Cψy, hxψ, hyψ] at hψDisjoint
    exact le_of_not_gt <| Ioi_disjoint_Iio_iff.mp hψDisjoint

  have hfComponent {z : X} (hz : z ∈ U ∩ V) (hfφz : f (φ z) = ψ z) :
      f '' (connectedComponentIn (φ '' (U ∩ V)) (φ z))
      ⊆ connectedComponentIn (ψ '' (U ∩ V)) (ψ z) := by
    have : ContinuousOn f (connectedComponentIn (φ '' (U ∩ V)) (φ z)) := f.continuousOn.mono
      <| Subset.trans (connectedComponentIn_subset (φ '' (U ∩ V)) (φ z)) hfSource
    have hfCPreconn : IsPreconnected (f '' (connectedComponentIn (φ '' (U ∩ V)) (φ z))) :=
      isPreconnected_connectedComponentIn.image f this
    apply hfCPreconn.subset_connectedComponentIn ?_ ?_
    · exact hfφz ▸ mem_image_of_mem f <| mem_connectedComponentIn <| mem_image_of_mem φ hz
    · exact hfImage ▸ (image_mono <| connectedComponentIn_subset (φ '' (U ∩ V)) (φ z))

  have hMono_a_d : StrictMonoOn f (Iio a) :=
    monotone_iio_to_ioi hφSource hφTarget hψSource hψTarget hx hxφ hxψ
  have hMono_c_b : StrictMonoOn f (Ioi b) := by
    have hfsymm_mono : StrictMonoOn f.symm (Iio c) := by
      rw [inter_comm] at hy hyψ hyφ
      exact monotone_iio_to_ioi hψSource hψTarget hφSource hφTarget hy hyψ hyφ
    intro p hp q hq hpq
    have hpUV : p ∈ φ '' (U ∩ V) :=
      connectedComponentIn_subset (φ '' (U ∩ V)) (φ y) (hyφ ▸ hp)
    have hqUV : q ∈ φ '' (U ∩ V) :=
      connectedComponentIn_subset (φ '' (U ∩ V)) (φ y) (hyφ ▸ hq)
    rw [← hyφ] at hp hq
    obtain ⟨hfp,hfq⟩ : f p ∈ Iio c ∧ f q ∈ Iio c := by
      rw [← hyψ]
      constructor <;> apply hfComponent hy hfφy <| mem_image_of_mem f ?_ <;> assumption
    apply (hfsymm_mono.lt_iff_lt hfp hfq).mp
    rwa [hf_symm_apply_apply hpUV, hf_symm_apply_apply hqUV]

  have hφComponents : φ '' (U ∩ V) = Cφx ∪ Cφy := disconnected_intersection_two_components
    hNotConn hφSource hφTarget hV hVConn hxφ hyφ
  have hψComponents : ψ '' (U ∩ V) = Cψx ∪ Cψy := by
    rw [inter_comm] at ⊢ hNotConn hxψ hyψ
    have hInter := disconnected_intersection_two_components
      hNotConn hψSource hψTarget hU hUConn hyψ hxψ
    rw [union_comm, hInter, show ψ '' (V ∩ U) = ψ '' (U ∩ V) by rw [inter_comm]]

  have hfCφx : f '' Cφx = Cψx := by
    apply Subset.antisymm (hfComponent hx hfφx) ?_
    intro z hz
    obtain ⟨w, hw, hwz⟩ : z ∈ f '' (φ '' (U ∩ V)) := by
      rw [hfImage, hψComponents]
      exact mem_union_left Cψy hz
    rw [← hwz]
    apply mem_image_of_mem f
    rw [hφComponents, mem_union] at hw
    by_contra hyCpt
    simp only [show w ∉ Cφx by exact hyCpt, false_or] at hw
    have : z ∈ Cψy := hwz ▸ ((hfComponent hy hfφy) <| mem_image_of_mem f hw)
    exact disjoint_left.mp hψDisjoint hz this

  have hφxφy : φ x < φ y := calc
    φ x < a := (mem_Iio (b := a)).mp <| hxφ ▸ mem_connectedComponentIn <| mem_image_of_mem φ hx
    _ ≤ b := hab
    _ < φ y := (mem_Ioi (b := b)).mp <| hyφ ▸ mem_connectedComponentIn <| mem_image_of_mem φ hy

  have hψxψy : ψ y < ψ x := calc
    ψ y < c := mem_Iio.mp <| hyψ ▸ mem_connectedComponentIn <| mem_image_of_mem ψ hy
    _ ≤ d := hcd
    _ < ψ x := mem_Ioi.mp <| hxψ ▸ mem_connectedComponentIn <| mem_image_of_mem ψ hx

  let A := φ.symm '' (Icc (φ x) (φ y))
  let B := ψ.symm '' (Icc (ψ y) (ψ x))

  have hAU : A ⊆ U := by
    rw [← hφSource, ← φ.symm_target, ← φ.symm.image_source_eq_target]
    apply image_mono
    rw [φ.symm_source, hφTarget]
    exact subset_univ _

  have hBV : B ⊆ V := by
    rw [← hψSource, ← ψ.symm_target, ← ψ.symm.image_source_eq_target]
    apply image_mono
    rw [ψ.symm_source, hψTarget]
    exact subset_univ _

  obtain ⟨hφxa, hφyb⟩ : φ x ∈ Iio a ∧ φ y ∈ Ioi b := by
    rw [← hxφ, ← hyφ]
    constructor <;> refine mem_connectedComponentIn <| mem_image_of_mem φ ?_ <;> assumption
  obtain ⟨hψxd, hψyc⟩ : ψ x ∈ Ioi d ∧ ψ y ∈ Iio c := by
    rw [← hxψ, ← hyψ]
    constructor <;> refine mem_connectedComponentIn <| mem_image_of_mem ψ ?_ <;> assumption

  have hccI_x_subset_AB : connectedComponentIn (U ∩ V) x ⊆ A ∪ B := by
    rw [connectedComponentIn_split hx hφSource hφTarget hψSource hψTarget hxφ hxψ]
    apply union_subset_union <;> apply image_mono
    · exact fun _ hs ↦ ⟨hs.1, le_of_lt <| lt_trans hs.2 <| lt_of_le_of_lt hab hφyb⟩
    · exact fun _ hs ↦ ⟨le_of_lt <| lt_trans hψyc <| lt_of_le_of_lt hcd hs.1, hs.2⟩

  have hccI_y_subset_AB : connectedComponentIn (U ∩ V) y ⊆ A ∪ B := by
    rw [inter_comm] at ⊢ hy hyψ hyφ
    rw [connectedComponentIn_split hy hψSource hψTarget hφSource hφTarget hyψ hyφ, union_comm]
    apply union_subset_union <;> apply image_mono
    · exact fun _ hs ↦ ⟨le_of_lt <| lt_trans hφxa <| lt_of_le_of_lt hab hs.1, hs.2⟩
    · exact fun _ hs ↦ ⟨hs.1, le_of_lt <| lt_trans hs.2 <| lt_of_le_of_lt hcd hψxd⟩

  have hAB_cover_UV : U ∩ V ⊆ A ∪ B := by
    have : φ.symm '' (φ '' (U ∩ V)) = U ∩ V := hφ_symm_apply_apply_image_UV
    simp_rw [hφComponents, Cφx, hxφ, Cφy, hyφ, image_union] at this
    rw [← this]
    rw [← Iio_union_Ico_eq_Iio <| le_of_lt hφxa, ← Ioc_union_Ioi_eq_Ioi <| le_of_lt hφyb]
    rw [image_union, image_union, ← union_assoc]
    refine union_subset (union_subset (union_subset ?_ ?_) ?_) ?_
    · have : φ.symm '' (Iio (φ x)) ⊆ φ.symm '' (Iio a) :=
        image_mono <| fun _ hs ↦ lt_trans (mem_Iio.mp hs) hφxa
      exact subset_trans (hxφ ▸ this) <| subset_trans (hφsymmComponent hx) hccI_x_subset_AB
    · refine subset_union_of_subset_left (image_mono ?_) B
      exact fun _ hs ↦ ⟨hs.1, le_of_lt <| gt_trans (lt_of_le_of_lt hab hφyb) hs.2⟩
    · refine subset_union_of_subset_left (image_mono ?_) B
      exact fun _ hs ↦ ⟨le_of_lt <| lt_trans (lt_of_lt_of_le hφxa hab) hs.1, hs.2⟩
    · have : φ.symm '' (Ioi (φ y)) ⊆ φ.symm '' (Ioi b) :=
        image_mono <| fun _ hs ↦ lt_trans hφyb (mem_Ioi.mp hs)
      exact subset_trans (hyφ ▸ this) <| subset_trans (hφsymmComponent hy) hccI_y_subset_AB

  have hUV_φsymm : U ∩ V = φ.symm '' ((Iio a) ∪ (Ioi b)) := by
    simp only [Cφx, Cφy, hxφ, hyφ] at hφComponents
    rw [← congrArg (image φ.symm) hφComponents, ← image_comp]
    exact Eq.symm <| EqOn.image_eq_self (fun _ ↦ hφ_symm_apply_apply)

  have hUV_ψsymm : U ∩ V = ψ.symm '' ((Iio c) ∪ (Ioi d)) := by
    simp only [Cψx, Cψy, hxψ, hyψ] at hψComponents
    rw [union_comm, ← congrArg (image ψ.symm) hψComponents, ← image_comp]
    exact Eq.symm <| EqOn.image_eq_self (fun _ ↦ hψ_symm_apply_apply)

  have hUOnly : U \ (U ∩ V) = φ.symm '' (Icc a b) := by
    nth_rewrite 1 [← hφSource, ← φ.symm_image_target_eq_source, hφTarget, hUV_φsymm]
    have : InjOn φ.symm univ := by
      rw [← hφTarget, ← φ.symm_source]
      exact φ.symm.injOn
    rw [← image_diff_of_injOn this (subset_univ _) (t := (Iio a) ∪ (Ioi b))]
    apply congrArg (image φ.symm)
    rw [← compl_eq_univ_diff, ← compl_Icc, compl_compl]

  have hVOnly : V \ (U ∩ V) = ψ.symm '' (Icc c d) := by
    nth_rewrite 1 [← hψSource, ← ψ.symm_image_target_eq_source, hψTarget, hUV_ψsymm]
    have : InjOn ψ.symm univ := by
      rw [← hψTarget, ← ψ.symm_source]
      exact ψ.symm.injOn
    rw [← image_diff_of_injOn this (subset_univ _) (t := (Iio c) ∪ (Ioi d))]
    apply congrArg (image ψ.symm)
    rw [← compl_eq_univ_diff, ← compl_Icc, compl_compl]

  have hABuniv : A ∪ B = univ := by
    apply univ_subset_iff.mp
    rw [← hUniv, union_eq_diff_union_diff_union_inter]
    refine union_subset (union_subset ?_ ?_) hAB_cover_UV
    · rw [← diff_self_inter, hUOnly]
      refine subset_trans (image_mono ?_) subset_union_left
      exact fun _ hs ↦ mem_Icc_of_Ioo ⟨lt_of_lt_of_le hφxa hs.1, lt_of_le_of_lt hs.2 hφyb⟩
    · rw [← diff_self_inter, inter_comm, hVOnly]
      refine subset_trans (image_mono ?_) subset_union_right
      exact fun _ hs ↦ mem_Icc_of_Ioo ⟨lt_of_lt_of_le hψyc hs.1, lt_of_le_of_lt hs.2 hψxd⟩

  obtain ⟨hAx, hBx, hAy, hBy⟩ : x ∈ A ∧ x ∈ B ∧ y ∈ A ∧ y ∈ B := by
    nth_rewrite 1 [← hφ_symm_apply_apply hx, ← hφ_symm_apply_apply hy]
    nth_rewrite 2 [← hψ_symm_apply_apply hx, ← hψ_symm_apply_apply hy]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact mem_image_of_mem φ.symm <| left_mem_Icc.mpr <| le_of_lt hφxφy
    · exact mem_image_of_mem ψ.symm <| right_mem_Icc.mpr <| le_of_lt hψxψy
    · exact mem_image_of_mem φ.symm <| right_mem_Icc.mpr <| le_of_lt hφxφy
    · exact mem_image_of_mem ψ.symm <| left_mem_Icc.mpr <| le_of_lt hψxψy

  have hABinter : A ∩ B = {x, y} := by
    apply Subset.antisymm
    · intro s hs
      have hAB_subset_UV : A ∩ B ⊆ U ∩ V := inter_subset_inter hAU hBV
      have hsUV : s ∈ U ∩ V := hAB_subset_UV hs
      rw [hUV_φsymm, image_union] at hAB_subset_UV
      have := (mem_union s (φ.symm '' Iio a) (φ.symm '' Ioi b)).mp (hAB_subset_UV hs)

      rcases this with hsa | hsb
      · have : s = x := by
          apply overlap_intersection hφSource hφTarget hψSource hψTarget
                hxφ hxψ hx hφxa (hφsymmComponent hx (by rwa [← hxφ] at hsa)) hsUV
          apply mem_inter
          · exact image_mono Icc_subset_Ici_self <| inter_subset_left hs
          · exact image_mono Icc_subset_Iic_self <| inter_subset_right hs
        exact this ▸ mem_insert x {y}
      · have : s = y := by
          have hsCpt : s ∈ connectedComponentIn (U ∩ V) y :=
            hφsymmComponent hy (by rwa [← hyφ] at hsb)
          rw [inter_comm] at hyψ hyφ hy hsCpt hsUV
          apply overlap_intersection hψSource hψTarget hφSource hφTarget
                hyψ hyφ hy hψyc hsCpt hsUV
          apply mem_inter
          · exact image_mono Icc_subset_Ici_self <| inter_subset_right hs
          · exact image_mono Icc_subset_Iic_self <| inter_subset_left hs
        exact mem_insert_of_mem x this
    · exact subset_inter (pair_subset hAx hAy) (pair_subset hBx hBy)

  let symm_subset_homeo {η : OpenPartialHomeomorph X ℝ} (hη : η.target = univ)
      (S : Set ℝ) : η.symm '' S ≃ₜ S := by
    apply (η.symm.homeomorphOfImageSubsetSource ?_ rfl).symm
    rw [η.symm_source, hη]
    exact subset_univ _
  let ηA : A ≃ₜ Icc (φ x) (φ y) := symm_subset_homeo hφTarget (Icc (φ x) (φ y))
  let ηB : B ≃ₜ Icc (ψ y) (ψ x) := symm_subset_homeo hψTarget (Icc (ψ y) (ψ x))
  obtain ⟨hηAx, hηBx, hηAy, hηBy⟩ :
      ηA ⟨x, hAx⟩ = φ x ∧ ηB ⟨x, hBx⟩ = ψ x ∧ ηA ⟨y, hAy⟩ = φ y ∧ ηB ⟨y, hBy⟩ = ψ y := by
    simp_all only [OpenPartialHomeomorph.homeomorphOfImageSubsetSource_symm_apply,
      OpenPartialHomeomorph.symm_symm, MapsTo.val_restrict_apply, A, B, ηA, ηB,
      symm_subset_homeo, and_self]

  exact homeomorph_circle_of_glue_icc_icc'
        A B hφxφy hψxψy ηA ηB hABuniv hABinter
        (homeo_symm hAx hηAx) (homeo_symm hBx hηBx) (homeo_symm hAy hηAy) (homeo_symm hBy hηBy)
