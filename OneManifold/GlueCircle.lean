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

open Set Function ComplexConjugate
set_option linter.style.emptyLine false

lemma mem_union_and_not_mem_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hUnion : A ∪ B = univ) {t : X} (ht : t ∉ A) : t ∈ B := by
  have : t ∈ A ∪ B := hUnion ▸ trivial
  simpa only [mem_union, ht, false_or] using this

noncomputable def glued_interval_map {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ) : X → ℂ :=
  fun t => if h : t ∈ A
              then (circleMap 0 1) (Real.pi * (φ ⟨t, h⟩))
              else (circleMap 0 1) (-Real.pi * (ψ ⟨t, mem_union_and_not_mem_left hUnion h⟩))

lemma glued_interval_map_eval_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {t : X} (hA : t ∈ A) :
    (glued_interval_map φ ψ hUnion) t = (circleMap 0 1) (Real.pi * (φ ⟨t, hA⟩)) := by
  simp only [glued_interval_map, hA, ↓reduceDIte]

lemma glued_interval_map_eval_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y}) {t : X} (hB : t ∈ B)
    (hφx : ∀ h, φ ⟨x, h⟩ = (0 : ℝ)) (hψx : ∀ h, ψ ⟨x, h⟩ = (0 : ℝ))
    (hφy : ∀ h, φ ⟨y, h⟩ = (1 : ℝ)) (hψy : ∀ h, ψ ⟨y, h⟩ = (1 : ℝ)) :
    (glued_interval_map φ ψ hUnion) t = (circleMap 0 1) (-Real.pi * (ψ ⟨t, hB⟩)) := by
  by_cases hA : t ∈ A <;> simp only [glued_interval_map, hA, ↓reduceDIte]
  · rcases (show t ∈ {x, y} by exact hInter ▸ mem_inter hA hB) with htx | hty <;> subst t
    · rw [hφx hA, hψx hB, mul_zero, mul_zero]
    · rw [hφy hA, hψy hB, mul_one, mul_one, ← periodic_circleMap 0 1 (- Real.pi)]
      apply congrArg (circleMap 0 1)
      have : (2 : ℝ) - 1 = 1 := by norm_num
      rw [← neg_one_mul Real.pi, ← add_mul, neg_add_eq_sub 1 2, this, one_mul]

lemma glued_interval_map_continuousOn_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ) :
    ContinuousOn (glued_interval_map φ ψ hUnion) A := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : A.restrict (glued_interval_map φ ψ hUnion) =
         fun a => (circleMap 0 1 (Real.pi * φ a)) := by
    ext x
    simp only [restrict_apply]
    exact glued_interval_map_eval_left φ ψ hUnion (Subtype.coe_prop x)
  rw [this]
  fun_prop

lemma glued_interval_map_continuousOn_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ∀ h, φ ⟨x, h⟩ = (0 : ℝ)) (hψx : ∀ h, ψ ⟨x, h⟩ = (0 : ℝ))
    (hφy : ∀ h, φ ⟨y, h⟩ = (1 : ℝ)) (hψy : ∀ h, ψ ⟨y, h⟩ = (1 : ℝ)) :
    ContinuousOn (glued_interval_map φ ψ hUnion) B := by
  apply continuousOn_iff_continuous_restrict.mpr
  have : B.restrict (glued_interval_map φ ψ hUnion) =
         fun b => (circleMap 0 1 (-Real.pi * ψ b)) := by
    ext x
    simp only [restrict_apply]
    exact glued_interval_map_eval_right φ ψ hUnion hInter (Subtype.coe_prop x) hφx hψx hφy hψy
  rw [this]
  fun_prop

lemma glued_interval_map_continuous {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ∀ h, φ ⟨x, h⟩ = (0 : ℝ)) (hψx : ∀ h, ψ ⟨x, h⟩ = (0 : ℝ))
    (hφy : ∀ h, φ ⟨y, h⟩ = (1 : ℝ)) (hψy : ∀ h, ψ ⟨y, h⟩ = (1 : ℝ))
    (hAClosed : IsClosed A) (hBClosed : IsClosed B) :
    Continuous (glued_interval_map φ ψ hUnion) := by
  apply continuousOn_univ.mp
  exact hUnion ▸ (continuousOn_union_iff_of_isClosed hAClosed hBClosed).mpr
    ⟨glued_interval_map_continuousOn_left φ ψ hUnion,
     glued_interval_map_continuousOn_right φ ψ hUnion hInter hφx hψx hφy hψy⟩

lemma glued_interval_map_continuous' {X : Type*} [TopologicalSpace X] [T2Space X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ∀ h, φ ⟨x, h⟩ = (0 : ℝ)) (hψx : ∀ h, ψ ⟨x, h⟩ = (0 : ℝ))
    (hφy : ∀ h, φ ⟨y, h⟩ = (1 : ℝ)) (hψy : ∀ h, ψ ⟨y, h⟩ = (1 : ℝ)) :
    Continuous (glued_interval_map φ ψ hUnion) := by
  have hA : IsCompact A := isCompact_iff_compactSpace.mpr φ.symm.compactSpace
  have hB : IsCompact B := isCompact_iff_compactSpace.mpr ψ.symm.compactSpace
  exact glued_interval_map_continuous φ ψ hUnion hInter hφx hψx hφy hψy
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

lemma glued_interval_map_im_nonneg {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ∀ h, φ ⟨x, h⟩ = (0 : ℝ)) (hψx : ∀ h, ψ ⟨x, h⟩ = (0 : ℝ))
    (hφy : ∀ h, φ ⟨y, h⟩ = (1 : ℝ)) (hψy : ∀ h, ψ ⟨y, h⟩ = (1 : ℝ))
    {t : X} : (glued_interval_map φ ψ hUnion t).im ≥ 0 ↔ t ∈ A := by
  obtain ⟨hxA, hxB, hyA, hyB⟩ := inter_two_points_mem_each hInter
  constructor <;> intro h
  · by_contra hA
    have hB : t ∈ B := mem_union_and_not_mem_left hUnion hA
    rw [glued_interval_map_eval_right φ ψ hUnion hInter hB hφx hψx hφy hψy, circleMap_zero] at h
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
      rw [← hψx hxB] at this
      have : t = x := Subtype.mk_eq_mk.mp <| ψ.injective <| SetCoe.ext this
      exact hA (this ▸ hxA)
    · have : Real.pi * ψ ⟨t, hB⟩ = Real.pi := eq_of_le_of_ge hle_pi <| not_lt.mp hψ
      apply (mul_eq_left₀ Real.pi_ne_zero).mp at this
      rw [← hψy hyB] at this
      have : t = y := Subtype.mk_eq_mk.mp <| ψ.injective <| SetCoe.ext this
      exact hA (this ▸ hyA)
  · rw [glued_interval_map_eval_left φ ψ hUnion h, circleMap_zero]
    simp only [Complex.mul_im, Complex.ofReal_re, one_mul, Complex.ofReal_im, zero_mul, add_zero]
    rw [Complex.exp_ofReal_mul_I_im]
    obtain ⟨hnonneg, hle_pi⟩ := bound_pi_times_unitInterval φ ⟨t, h⟩
    exact Real.sin_nonneg_of_nonneg_of_le_pi hnonneg hle_pi

lemma glued_interval_map_injOn_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ) :
    InjOn (glued_interval_map φ ψ hUnion) A := by
  intro s hs t ht heq
  rw [glued_interval_map_eval_left φ ψ hUnion hs,
      glued_interval_map_eval_left φ ψ hUnion ht] at heq
  have := bound_sub_pi_times_unitInterval φ ⟨s, hs⟩ ⟨t, ht⟩
  have := eq_of_circleMap_eq one_ne_zero this heq
  apply (mul_right_inj' Real.pi_ne_zero).mp at this
  exact Subtype.mk_eq_mk.mp <| φ.injective <| SetCoe.ext this

lemma glued_interval_map_injOn_right {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ∀ h, φ ⟨x, h⟩ = (0 : ℝ)) (hψx : ∀ h, ψ ⟨x, h⟩ = (0 : ℝ))
    (hφy : ∀ h, φ ⟨y, h⟩ = (1 : ℝ)) (hψy : ∀ h, ψ ⟨y, h⟩ = (1 : ℝ)) :
    InjOn (glued_interval_map φ ψ hUnion) B := by
  intro s hs t ht heq
  rw [glued_interval_map_eval_right φ ψ hUnion hInter hs hφx hψx hφy hψy,
      glued_interval_map_eval_right φ ψ hUnion hInter ht hφx hψx hφy hψy] at heq
  have : |(Real.pi * ψ ⟨t, ht⟩) - (Real.pi * ψ ⟨s, hs⟩)| < 2 * Real.pi :=
    bound_sub_pi_times_unitInterval ψ ⟨t, ht⟩ ⟨s, hs⟩
  rw [← neg_sub_neg, neg_mul_eq_neg_mul, neg_mul_eq_neg_mul] at this
  have := eq_of_circleMap_eq one_ne_zero this heq
  apply (mul_right_inj' <| neg_ne_zero.mpr Real.pi_ne_zero).mp at this
  exact Subtype.mk_eq_mk.mp <| ψ.injective <| SetCoe.ext this

lemma glued_interval_map_injective {X : Type*} [TopologicalSpace X]
    {A B : Set X} [∀ t : X, Decidable (t ∈ A)]
    (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval) (hUnion : A ∪ B = univ)
    {x y : X} (hInter : A ∩ B = {x, y})
    (hφx : ∀ h, φ ⟨x, h⟩ = (0 : ℝ)) (hψx : ∀ h, ψ ⟨x, h⟩ = (0 : ℝ))
    (hφy : ∀ h, φ ⟨y, h⟩ = (1 : ℝ)) (hψy : ∀ h, ψ ⟨y, h⟩ = (1 : ℝ)) :
    Injective (glued_interval_map φ ψ hUnion) := by
  intro s t heq
  by_cases hs : s ∈ A <;> by_cases ht : t ∈ A
  · exact glued_interval_map_injOn_left φ ψ hUnion hs ht heq
  · have h₁ := (glued_interval_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy).mpr hs
    have h₂ := (not_iff_not.mpr
                (glued_interval_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy)).mpr ht
    exact False.elim <| h₂ (heq ▸ h₁)
  · have h₁ := (glued_interval_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy).mpr ht
    have h₂ := (not_iff_not.mpr
                (glued_interval_map_im_nonneg φ ψ hUnion hInter hφx hψx hφy hψy)).mpr hs
    exact False.elim <| h₂ (heq ▸ h₁)
  · exact glued_interval_map_injOn_right φ ψ hUnion hInter hφx hψx hφy hψy
      (mem_union_and_not_mem_left hUnion hs) (mem_union_and_not_mem_left hUnion ht) heq

-- private lemma glue_unit_intervals_circle₀' {X : Type*} [TopologicalSpace X] [T2Space X]
--     (A B : Set X) (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval)
--     {x y : X} (hAx : x ∈ A) (hBx : x ∈ B) (hAy : y ∈ A) (hBy : y ∈ B)
--     (hInter : A ∩ B = {x, y}) (hUnion : A ∪ B = univ)
--     (hφx : φ ⟨x, hAx⟩ = (0 : ℝ)) (hψx : ψ ⟨x, hBx⟩ = (0 : ℝ))
--     (hφy : φ ⟨y, hAy⟩ = (1 : ℝ)) (hψy : ψ ⟨y, hBy⟩ = (1 : ℝ)) :
--     Nonempty (X ≃ₜ Circle) := by
--   classical -- need to know that A, B are decidable
--   let m : ℝ → ℝ := fun t ↦ Real.pi * t
--   let f₀ : unitInterval → ℂ := fun t ↦ Complex.exp ((m t) * Complex.I)
--   have hfCircle : ∀ t : unitInterval, f₀ t ∈ Submonoid.unitSphere ℂ := by
--     intro t
--     rw [show (f₀ t ∈ Submonoid.unitSphere ℂ) = (dist (f₀ t) (0 : ℂ) = 1) by rfl,
--         dist_zero_right, Complex.norm_exp_ofReal_mul_I (m t)]
--   have : (0 : ℝ) ≤ 1 := by exact zero_le_one
--   let f : unitInterval → Circle :=
--     fun t ↦ ⟨circleMap 0 1 (Real.pi * t), circleMap_mem_sphere 0 zero_le_one (Real.pi * t)⟩
--   let g : unitInterval → Circle :=
--     fun t ↦ ⟨circleMap 0 1 (- Real.pi * t), circleMap_mem_sphere 0 zero_le_one (- Real.pi * t)⟩

--   haveI : f 0 = g 0 := by simp only [f, g, Icc.coe_zero, mul_zero]
--   haveI : f 1 = g 1 := by
--     simp only [f, g, Icc.coe_one, mul_one, Circle.ext_iff]
--     rw [← periodic_circleMap 0 1 (- Real.pi)]
--     apply congrArg (circleMap 0 1)
--     have : (2 : ℝ) - 1 = 1 := by norm_num
--     rw [← neg_one_mul Real.pi, ← add_mul, neg_add_eq_sub 1 2, this, one_mul]
--   sorry

private lemma glue_unit_intervals_circle₀ {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : Set X) (φ : A ≃ₜ unitInterval) (ψ : B ≃ₜ unitInterval)
    {x y : X} (hAx : x ∈ A) (hBx : x ∈ B) (hAy : y ∈ A) (hBy : y ∈ B)
    (hInter : A ∩ B = {x, y}) (hUnion : A ∪ B = univ)
    (hφx : φ ⟨x, hAx⟩ = (0 : ℝ)) (hψx : ψ ⟨x, hBx⟩ = (0 : ℝ))
    (hφy : φ ⟨y, hAy⟩ = (1 : ℝ)) (hψy : ψ ⟨y, hBy⟩ = (1 : ℝ)) :
    Nonempty (X ≃ₜ Circle) := by
  classical -- need to know that A, B are decidable
  let m : ℝ → ℝ := fun t ↦ Real.pi * t
  let f₀ : unitInterval → ℂ := fun t ↦ Complex.exp ((m t) * Complex.I)
  have hfCircle : ∀ t : unitInterval, f₀ t ∈ Submonoid.unitSphere ℂ := by
    intro t
    rw [show (f₀ t ∈ Submonoid.unitSphere ℂ) = (dist (f₀ t) (0 : ℂ) = 1) by rfl,
        dist_zero_right, Complex.norm_exp_ofReal_mul_I (m t)]
  let f : unitInterval → Circle := fun t ↦ ⟨f₀ t, hfCircle t⟩

  let g₀ : unitInterval → ℂ := fun t ↦ conj (f₀ t)
  have hgCircle : ∀ t : unitInterval, g₀ t ∈ Submonoid.unitSphere ℂ := by
    intro t
    rw [show (g₀ t ∈ Submonoid.unitSphere ℂ) = (dist (g₀ t) (0 : ℂ) = 1) by rfl,
        dist_zero_right, Complex.norm_conj (f₀ t),
        Complex.norm_exp_ofReal_mul_I (m t)]
  let g : unitInterval → Circle := fun t ↦ ⟨g₀ t, hgCircle t⟩

  haveI : f 0 = g 0 := by
    simp_all only [Complex.ofReal_mul, Icc.coe_zero, Complex.ofReal_zero,
      mul_zero, zero_mul, Complex.exp_zero, map_one, f, f₀, m, g, g₀]

  haveI : f 1 = g 1 := by
    simp_all only [Icc.coe_eq_zero, Icc.coe_eq_one, map_one, Icc.coe_one,
      mul_one, Complex.exp_pi_mul_I, map_neg, f, f₀, m, g, g₀]

  have h_not_A_implies_B {t : X} : t ∉ A → t ∈ B := by
    apply (imp_iff_not_or (b := t ∈ B)).mpr
    simp only [not_not]
    rw [← mem_union, hUnion]
    trivial

  let η : X → Circle :=
    fun t => if h : t ∈ A then f (φ ⟨t, h⟩) else g (ψ ⟨t, h_not_A_implies_B h⟩)
  have hηf {t : X} (ht : t ∈ A) : η t = f (φ ⟨t, ht⟩) := by
    simp_all only [η, ↓reduceDIte]
  have hηg {t : X} (ht : t ∈ B) : η t = g (ψ ⟨t, ht⟩) := by
    simp_all only [η]
    by_cases h : t ∈ A
    · simp_all only [Icc.coe_eq_zero, Icc.coe_eq_one, ↓reduceDIte, implies_true]
      have : t ∈ A ∩ B := by exact mem_inter h ht
      rw [hInter] at this
      have : t = x ∨ t = y := by
        simpa only [↓reduceDIte, implies_true, mem_insert_iff, mem_singleton_iff] using this
      rcases this with htx | hty
      · have hφt : φ ⟨t, h⟩ = 0 := hφx ▸ (congrArg φ <| SetCoe.ext htx)
        have hψt : ψ ⟨t, ht⟩ = 0 := hψx ▸ (congrArg ψ <| SetCoe.ext htx)
        rwa [hφt, hψt]
      · have hφt : φ ⟨t, h⟩ = 1 := hφy ▸ (congrArg φ <| SetCoe.ext hty)
        have hψt : ψ ⟨t, ht⟩ = 1 := hψy ▸ (congrArg ψ <| SetCoe.ext hty)
        rwa [hφt, hψt]
    · simp_all only [Icc.coe_eq_zero, Icc.coe_eq_one, ↓reduceDIte, implies_true]

  have hηContOnA : ContinuousOn η A := by
    refine continuousOn_iff_continuous_restrict.mpr ?_
    have h : A.restrict η = fun a => f (φ a) := by
      ext x
      simp_all only [restrict_apply, Subtype.coe_prop, Subtype.coe_eta]
    have : Continuous fun (a : A) => f (φ a) := by fun_prop
    rwa [← h] at this

  have hηContOnB : ContinuousOn η B := by
    refine continuousOn_iff_continuous_restrict.mpr ?_
    have h : B.restrict η = fun b => g (ψ b) := by
      ext x
      simp_all only [Icc.coe_eq_zero, Icc.coe_eq_one, restrict_apply,
        Subtype.coe_prop, Subtype.coe_eta]

    have : Continuous fun (b : B) => g (ψ b) := by
      apply Continuous.subtype_mk
      apply Continuous.star
      fun_prop
    rwa [← h] at this

  have hACompact : IsCompact A := isCompact_iff_compactSpace.mpr <| φ.symm.compactSpace
  have hBCompact : IsCompact B := isCompact_iff_compactSpace.mpr <| ψ.symm.compactSpace
  have hηCont : Continuous η := by
    apply continuousOn_univ.mp
    rw [← hUnion]
    refine (continuousOn_union_iff_of_isClosed ?_ ?_).mpr ⟨hηContOnA, hηContOnB⟩
    · exact hACompact.isClosed
    · exact hBCompact.isClosed

  have hInjective : Injective η := by
    have mul_pi_in_Icc_0_pi (u : unitInterval) : Real.pi * u.val ∈ Icc 0 Real.pi := by
      constructor
      · exact mul_nonneg Real.pi_nonneg <| unitInterval.nonneg u
      · exact (mul_le_iff_le_one_right Real.pi_pos).mpr <| unitInterval.le_one u

    have divide_pi {a b : unitInterval} (hab : Real.pi * a = Real.pi * b) : a = b := by
      apply mul_eq_mul_left_iff.mp at hab
      simp only [Real.pi_ne_zero, or_false] at hab
      exact SetCoe.ext hab

    have eq_if_same_cos (s t : unitInterval) :
        Real.cos (Real.pi * s) = Real.cos (Real.pi * t) → s = t :=
      fun hcos => divide_pi <| Real.injOn_cos (mul_pi_in_Icc_0_pi s) (mul_pi_in_Icc_0_pi t) hcos

    have hfInj : Injective f := by
      intro s t hf
      have : Real.cos (Real.pi * s) = Real.cos (Real.pi * t) := by calc
        Real.cos (Real.pi * s) = (f s).val.re := Eq.symm <| Complex.exp_ofReal_mul_I_re (m s)
        _ = (f t).val.re := congrArg Complex.re <| congrArg Subtype.val hf
        _ = Real.cos (Real.pi * t) := Complex.exp_ofReal_mul_I_re (m t)
      exact eq_if_same_cos s t this

    have hgInj : Injective g := by
      intro s t hg
      have : Real.cos (Real.pi * s) = Real.cos (Real.pi * t) := by calc
        Real.cos (Real.pi * s) = (g s).val.re := Eq.symm <| Complex.exp_ofReal_mul_I_re (m s)
        _ = (g t).val.re := congrArg Complex.re <| congrArg Subtype.val hg
        _ = Real.cos (Real.pi * t) := Complex.exp_ofReal_mul_I_re (m t)
      exact eq_if_same_cos s t this

    have f_im_nonneg (u : unitInterval) : (f u).val.im ≥ 0 := by calc
      (f u).val.im = Real.sin (Real.pi * u) := Complex.exp_ofReal_mul_I_im (Real.pi * u)
      _ ≥ 0 := Real.sin_nonneg_of_mem_Icc (mul_pi_in_Icc_0_pi u)

    have g_im_nonpos (u : unitInterval) : (g u).val.im ≤ 0 := by
      simp only [g, g₀, Complex.conj_im, neg_nonpos]
      exact f_im_nonneg u

    have hBoundary {s t : unitInterval} : f s = g t → s = 0 ∨ s = 1 := by
      intro hst
      have hfim : (f s).val.im ≥ 0 := f_im_nonneg s
      have hgim : (g t).val.im ≤ 0 := neg_nonpos_of_nonneg (f_im_nonneg t)
      rw [← show (f s).val.im = (g t).val.im by
            exact (Complex.ext_iff.mp <| congrArg Subtype.val hst).2] at hgim
      have hsin_zero : Real.sin (Real.pi * s) = 0 := by
        rw [← Complex.exp_ofReal_mul_I_im (Real.pi * s)]
        exact le_antisymm hgim hfim
      have : (Real.pi * s) ≤ 0 ∨ (Real.pi * s) ≥ Real.pi := by
        by_contra! h
        exact (ne_of_lt <| Real.sin_pos_of_mem_Ioo h) <| Eq.symm hsin_zero
      rcases this with hle0 | hgePi
      · left
        apply divide_pi
        rw [Icc.coe_zero, mul_zero]
        exact le_antisymm hle0 <| mul_nonneg Real.pi_nonneg (unitInterval.nonneg s)
      · right
        apply divide_pi
        nth_rewrite 2 [← mul_one Real.pi] at hgePi
        apply le_antisymm ?_ hgePi
        exact (mul_le_mul_iff_of_pos_left Real.pi_pos).mpr unitInterval.le_one'

    have hη_A_notA {s t : X} (hs : s ∈ A) (ht : t ∉ A) : η s ≠ η t := by
      have ht' : t ∈ B := h_not_A_implies_B ht
      rw [hηf hs, hηg ht']
      by_contra hfsgt
      have hφ_im_nonneg := f_im_nonneg (φ ⟨s,hs⟩)
      rw [hfsgt] at hφ_im_nonneg
      have hg_im_zero : (g (ψ ⟨t,ht'⟩)).val.im = 0 :=
        Eq.symm <| le_antisymm hφ_im_nonneg <| g_im_nonpos (ψ ⟨t,ht'⟩)
      simp only [g, g₀, f₀, m, Complex.conj_im, neg_eq_zero,
                 Complex.exp_ofReal_mul_I_im] at hg_im_zero
      have : ψ ⟨t, ht'⟩ = 0 ∨ ψ ⟨t, ht'⟩ = 1 := by
        by_contra! h'
        have h0 : 0 < ψ ⟨t, ht'⟩ := lt_of_le_of_ne (ψ ⟨t, ht'⟩).property.1 <| Ne.symm h'.1
        have h1 : ψ ⟨t, ht'⟩ < 1 := lt_of_le_of_ne (ψ ⟨t, ht'⟩).property.2 h'.2
        have : Real.pi * ↑(ψ ⟨t, ht'⟩) ∈ Ioo 0 Real.pi := by
          apply mem_Ioo.mpr ⟨mul_pos Real.pi_pos h0, ?_⟩
          nth_rewrite 2 [← mul_one Real.pi]
          exact (mul_lt_mul_iff_of_pos_left Real.pi_pos).mpr h1
        exact (ne_of_lt <| Real.sin_pos_of_mem_Ioo this) <| Eq.symm hg_im_zero
      rcases this with hψ0 | hψ1
      · have : (⟨x, hBx⟩ : B) = ⟨t, ht'⟩ := by
          apply ψ.injective
          rw [hψ0]
          exact divide_pi (congrArg (fun t => Real.pi * t) hψx)
        exact (show x ∉ A by rwa [Subtype.mk_eq_mk.mp this]) hAx
      · have : (⟨y, hBy⟩ : B) = ⟨t, ht'⟩ := by
          apply ψ.injective
          rw [hψ1]
          exact divide_pi (congrArg (fun t => Real.pi * t) hψy)
        rw [← Subtype.mk_eq_mk.mp this] at ht
        exact ht hAy

    intro s t hst
    by_cases hs : s ∈ A <;> by_cases ht : t ∈ A
    · -- s, t ∈ A
      rw [hηf hs, hηf ht] at hst
      exact Subtype.ext_iff.mp <| φ.injective <| hfInj hst
    · -- s ∈ A, t ∉ A
      exact False.elim <| (hη_A_notA hs ht) hst
    · -- s ∉ A, t ∈ A
      exact False.elim <| (Ne.symm <| hη_A_notA ht hs) hst
    · -- s, t ∉ A
      rw [hηg (h_not_A_implies_B hs), hηg (h_not_A_implies_B ht)] at hst
      exact Subtype.ext_iff.mp <| ψ.injective <| hgInj hst

  have hSurjective : Surjective η := by
    intro z
    let t := (Real.arccos z.val.re) / Real.pi

    have htIcc₀ : t ∈ Icc 0 1 := by
      constructor
      · rw [← zero_div Real.pi]
        exact (div_le_div_iff_of_pos_right Real.pi_pos).mpr <| Real.arccos_nonneg z.val.re
      · rw [← (div_eq_one_iff_eq Real.pi_ne_zero).mpr rfl]
        exact (div_le_div_iff_of_pos_right Real.pi_pos).mpr <| Real.arccos_le_pi z.val.re
    have htIcc : Real.pi * t ∈ Icc 0 Real.pi := by
      refine ⟨mul_nonneg Real.pi_nonneg htIcc₀.1, ?_⟩
      nth_rewrite 2 [← mul_one Real.pi]
      exact mul_le_mul_of_nonneg_left htIcc₀.2 Real.pi_nonneg

    have hCos : Real.cos (Real.pi * t) = z.val.re := by
      rw [show t = (Real.arccos z.val.re) / Real.pi by rfl, mul_div_cancel₀]
      · have : |z.val.re| ≤ 1 := by
          rw [← norm_eq_of_mem_sphere z]
          exact Complex.abs_re_le_norm z
        exact Real.cos_arccos (neg_le_of_abs_le this) (le_of_max_le_left this)
      · exact Real.pi_ne_zero

    have hSin_abs: Real.sin (Real.pi * t) = |z.val.im| := by
      rw [← abs_of_nonneg (Real.sin_nonneg_of_mem_Icc htIcc)]
      calc
        |Real.sin (Real.pi * t)| = √(1 - Real.cos (Real.pi * t) ^ 2) := by
          exact Real.abs_sin_eq_sqrt_one_sub_cos_sq (Real.pi * t)
        _ = √(1 ^ 2 - z.val.re ^ 2) := by rw [hCos, one_pow 2]
        _ = √(‖z.val‖ ^ 2 - z.val.re ^ 2) := by rw [norm_eq_of_mem_sphere z]
        _ = √(z.val.im ^ 2) := by
          rw [Complex.sq_norm z.val, pow_two z.val.re, pow_two z.val.im,
              Complex.normSq_apply z.val, add_sub_cancel_left]
        _ = |z.val.im| := by exact Real.sqrt_sq_eq_abs z.val.im

    rw [← Complex.exp_ofReal_mul_I_re (Real.pi * t)] at hCos
    rw [← Complex.exp_ofReal_mul_I_im (Real.pi * t)] at hSin_abs
    by_cases h : z.val.im ≥ 0
    · rw [abs_of_nonneg h] at hSin_abs
      have : Complex.exp ((Real.pi * t : ℝ) * Complex.I) = z :=
        Complex.ext_iff.mpr ⟨hCos, hSin_abs⟩
      use φ.symm ⟨t, htIcc₀⟩
      rw [hηf <| Subtype.coe_prop <| φ.symm ⟨t, htIcc₀⟩]
      simp only [Subtype.coe_eta, Homeomorph.apply_symm_apply, f, f₀, m]
      exact Circle.ext_iff.mpr this
    · rw [abs_of_neg (lt_of_not_ge h)] at hSin_abs
      have : conj Complex.exp ((Real.pi * t : ℝ) * Complex.I) = z := by
        rw [← starRingEnd_self_apply z.val]
        refine congrArg conj <| Complex.ext_iff.mpr ?_
        rw [Complex.conj_re, Complex.conj_im]
        exact ⟨hCos, hSin_abs⟩
      use ψ.symm ⟨t, htIcc₀⟩
      rw [hηg <| Subtype.coe_prop <| ψ.symm ⟨t, htIcc₀⟩]
      simp only [Subtype.coe_eta, Homeomorph.apply_symm_apply, g, g₀]
      exact Circle.ext_iff.mpr this

  haveI : CompactSpace X := by
    apply isCompact_univ_iff.mp
    rw [← hUnion]
    exact IsCompact.union hACompact hBCompact
  haveI : T2Space Circle := instT2SpaceOfR1SpaceOfT0Space
  have hBijective : Bijective η := ⟨hInjective, hSurjective⟩
  exact Nonempty.intro <| hηCont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective η hBijective)

theorem homeomorph_circle_of_glue_icc_icc {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : Set X) {c d e f : ℝ} (hcd : c < d) (hef : e < f)
    (φ : A ≃ₜ Icc c d) (ψ : B ≃ₜ Icc e f)
    {x y : X} (hAx : x ∈ A) (hBx : x ∈ B) (hAy : y ∈ A) (hBy : y ∈ B)
    (hInter : A ∩ B = {x, y}) (hUnion : A ∪ B = univ)
    (hφx : φ ⟨x, hAx⟩ = (c : ℝ)) (hψx : ψ ⟨x, hBx⟩ = (e : ℝ))
    (hφy : φ ⟨y, hAy⟩ = (d : ℝ)) (hψy : ψ ⟨y, hBy⟩ = (f : ℝ)) :
    Nonempty (X ≃ₜ Circle) := by

  let φ' : A ≃ₜ unitInterval := φ.trans <| iccHomeoI c d hcd
  have hφ' : φ' ⟨x, hAx⟩ = (0 : ℝ) ∧ φ' ⟨y, hAy⟩ = (1 : ℝ) := by
    have (x : Icc c d) : (iccHomeoI c d hcd) x = (x.val - c) / (d - c) := by rfl
    simp only [φ.trans_apply, this, hφx, sub_self, zero_div, hφy, div_self_eq_one₀,
      true_and, φ']
    have : d - c ≠ 0 := Ne.symm <| ne_of_lt <| sub_pos.mpr hcd
    exact RCLike.ofReal_ne_zero.mp this

  let ψ' : B ≃ₜ unitInterval := ψ.trans <| iccHomeoI e f hef
  have hψ' : ψ' ⟨x, hBx⟩ = (0 : ℝ) ∧ ψ' ⟨y, hBy⟩ = (1 : ℝ) := by
    have (x : Icc e f) : (iccHomeoI e f hef) x = (x.val - e) / (f - e) := by rfl
    simp only [ψ.trans_apply, this, hψx, sub_self, zero_div, hψy, div_self_eq_one₀,
      true_and, ψ']
    have : f - e ≠ 0 := Ne.symm <| ne_of_lt <| sub_pos.mpr hef
    exact RCLike.ofReal_ne_zero.mp this

  exact glue_unit_intervals_circle₀ A B φ' ψ' hAx hBx hAy hBy hInter hUnion
                                    hφ'.1 hψ'.1 hφ'.2 hψ'.2

theorem homeomorph_circle_of_glue_icc_icc' {X : Type*} [TopologicalSpace X] [T2Space X]
    (A B : Set X) {c d e f : ℝ} (hcd : c < d) (hef : e < f)
    (φ : A ≃ₜ Icc c d) (ψ : B ≃ₜ Icc e f)
    {x y : X} (hAx : x ∈ A) (hBx : x ∈ B) (hAy : y ∈ A) (hBy : y ∈ B)
    (hInter : A ∩ B = {x, y}) (hUnion : A ∪ B = univ)
    (hφx : φ ⟨x, hAx⟩ = (c : ℝ)) (hψx : ψ ⟨x, hBx⟩ = (f : ℝ))
    (hφy : φ ⟨y, hAy⟩ = (d : ℝ)) (hψy : ψ ⟨y, hBy⟩ = (e : ℝ)) :
    Nonempty (X ≃ₜ Circle) := by
  let ψ' : B ≃ₜ Icc e f := ψ.trans (icc_flip hef)
  obtain ⟨hψ'x, hψ'y⟩ : ψ' ⟨x,hBx⟩ = e ∧ ψ' ⟨y,hBy⟩ = f := by
    have := icc_flip_left hef
    have := icc_flip_right hef
    simp_all only [ψ.trans_apply, ψ', icc_flip]
    simp_all only [Homeomorph.trans_apply, unitInterval.symmHomeomorph_apply,
      iccHomeoI_symm_apply_coe, unitInterval.coe_symm_eq, iccHomeoI_apply_coe,
      add_eq_right, mul_eq_zero, and_self]
  exact homeomorph_circle_of_glue_icc_icc A B hcd hef φ ψ' hAx hBx hAy hBy
                                          hInter hUnion hφx hψ'x hφy hψ'y

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
    {U V : Set X}
    (hUniv : U ∪ V = @univ X) (hNotConn : ¬ IsConnected (U ∩ V))
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
  have : ∃ z : ℝ, z ∈ φ '' (U ∩ V) ∧ connectedComponentIn (φ '' (U ∩ V)) z ≠ Cφx := by
    by_contra! h
    have : φ '' (U ∩ V) = Cφx := by
      apply Subset.antisymm ?_ <| connectedComponentIn_subset (φ '' (U ∩ V)) (φ x)
      intro z hz
      have h' := mem_connectedComponentIn hz
      rwa [h z hz] at h'
    exact (this ▸ hNotConn_φ) <| isConnected_connectedComponentIn_iff.mpr hφx
  obtain ⟨z, ⟨y, hy, hφy⟩, hCz⟩ := this
  let Cφy : Set ℝ := connectedComponentIn (φ '' (U ∩ V)) (φ y)

  have hDisjoint : Disjoint Cφx Cφy := by
    apply Set.disjoint_iff.mpr
    by_contra h
    obtain ⟨_,ha⟩ := Classical.not_forall_not.mp h
    have hxy := connectedComponentIn_eq <| mem_of_mem_inter_right ha
    rw [← connectedComponentIn_eq <| mem_of_mem_inter_left ha, hφy] at hxy
    exact hCz hxy

  have hφCx := intersection_intervals
    hφSource hφTarget hV hVConn hNotUV hNotVU (mem_image_of_mem φ hx)

  have hφCy := intersection_intervals
    hφSource hφTarget hV hVConn hNotUV hNotVU (mem_image_of_mem φ hy)

  rcases hφCx with hCx | hCx <;> rcases hφCy with hCy | hCy
    <;> (obtain ⟨a,ha⟩ := hCx; obtain ⟨b,hb⟩ := hCy)
  · -- hCx = Iio a, hCy = Iio b contradicts hDisjoint
    let c := (min a b) - 1
    have hc : c ∈ Cφx ∩ Cφy := by
      simp only [Cφx, Cφy, ha, hb]
      apply mem_inter
      · exact lt_of_lt_of_le (sub_one_lt (min a b)) (min_le_left a b)
      · exact lt_of_lt_of_le (sub_one_lt (min a b)) (min_le_right a b)
    have : ¬ Disjoint Cφx Cφy :=
      fun h ↦ (h.notMem_of_mem_left <| mem_of_mem_inter_left hc) <| mem_of_mem_inter_right hc
    exact False.elim <| this hDisjoint
  · -- hCx = Iio a, hCy = Ioi b
    have : a ≤ b := by
      simp only [Cφx, Cφy, ha, hb] at hDisjoint
      exact le_of_not_gt <| Set.Iio_disjoint_Ioi_iff.mp hDisjoint
    use x, y, a, b
  · -- hCx = Ioi a, hCy = Iio b
    have : b ≤ a := by
      simp only [Cφx, Cφy, ha, hb] at hDisjoint
      exact le_of_not_gt <| Set.Ioi_disjoint_Iio_iff.mp hDisjoint
    use y, x, b, a
  · -- hCx = Ioi a, hCy = Ioi b contradicts hDisjoint
    let c := (max a b) + 1
    have hc : c ∈ Cφx ∩ Cφy := by
      simp only [Cφx, Cφy, ha, hb]
      apply mem_inter
      · exact lt_of_le_of_lt (le_max_left a b) (lt_add_one (max a b))
      · exact lt_of_le_of_lt (le_max_right a b) (lt_add_one (max a b))
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
    apply union_subset
    · exact connectedComponentIn_subset (φ '' (U ∩ V)) (φ x)
    · exact connectedComponentIn_subset (φ '' (U ∩ V)) (φ y)
  obtain ⟨z,hzφ,hzComp⟩ := exists_of_ssubset
                           <| HasSubset.Subset.ssubset_of_ne hsub <| Ne.symm h
  apply not_or.mp at hzComp
  obtain ⟨hNotUV, hNotVU⟩ := not_nested_disconnected_intersection
    hNotConn hφSource hφTarget hVConn
  let hzInt := intersection_intervals hφSource hφTarget hV hVConn hNotUV hNotVU hzφ
  have hzComponent : z ∈ connectedComponentIn (φ '' (U ∩ V)) z := by
      exact mem_connectedComponentIn hzφ

  rcases hzInt with hInt | hInt <;> obtain ⟨c,hc⟩ := hInt
  · let d : ℝ := min a c - 1
    have hdx : d ∈ connectedComponentIn (φ '' (U ∩ V)) (φ x) :=
      hxa ▸ lt_of_le_of_lt' (min_le_left a c) (sub_one_lt (min a c))
    have hdw : d ∈ connectedComponentIn (φ '' (U ∩ V)) z :=
      hc ▸ lt_of_le_of_lt' (min_le_right a c) (sub_one_lt (min a c))
    rw [connectedComponentIn_eq hdw, ← connectedComponentIn_eq hdx] at hzComponent
    exact hzComp.1 hzComponent
  · let d : ℝ := max b c + 1
    have hdy : d ∈ connectedComponentIn (φ '' (U ∩ V)) (φ y) :=
      hyb ▸ lt_of_le_of_lt (le_max_left b c) (lt_add_one (max b c))
    have hdw : d ∈ connectedComponentIn (φ '' (U ∩ V)) z :=
      hc ▸ lt_of_le_of_lt (le_max_right b c) (lt_add_one (max b c))
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
        A B hφxφy hψxψy ηA ηB hAx hBx hAy hBy hABinter hABuniv hηAx hηBx hηAy hηBy
