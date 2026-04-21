import Mathlib.Tactic

open Set Function

lemma homeomorph_real_real_fix_two_points {a b α β : ℝ} (hab : a ≠ b) (hαβ : α ≠ β) :
    ∃ f : ℝ ≃ₜ ℝ, f α = a ∧ f β = b := by
  let c := (a - b) / (α - β)
  let d := (b * α - a * β) / (α - β)
  have hαβ' : α - β ≠ 0 := sub_ne_zero_of_ne hαβ
  have hc : c ≠ 0 := div_ne_zero (sub_ne_zero_of_ne hab) hαβ'
  use affineHomeomorph c d hc
  simp only [affineHomeomorph_apply, c, d]
  field_simp
  constructor <;> ring

lemma homeomorph_open_real_fix_two_points {X : Type*} [TopologicalSpace X]
    {U : Set X} (hReal : Nonempty (U ≃ₜ ℝ)) {x y : U} (hxy : x ≠ y)
    {a b : ℝ} (hab : a ≠ b) :
    ∃ φ : U ≃ₜ ℝ, φ x = a ∧ φ y = b := by
  let ψ := hReal.some
  obtain ⟨f, hfα, hfβ⟩ := homeomorph_real_real_fix_two_points
    hab (fun h => hxy <| ψ.injective h)
  use ψ.trans f
  rw [ψ.trans_apply, ψ.trans_apply, ← hfα, ← hfβ]
  constructor <;> rfl

/- Given a strictly increasing chain f 0 ⊂ f 1 ⊂ f 2 ⊂ of subsets of X, there
   is a function g : ℕ → X such that each g n belongs to f n but not (assuming
   n ≠ 0) to f (n - 1). -/
lemma strictMono_subset_representatives {X : Type*} [TopologicalSpace X]
    (f : ℕ → Set X) (hNE : Nonempty (f 0)) (hfStrictMono : ∀ m n, m < n → f m ⊂ f n) :
    ∃ g : ℕ → X, ∀ n, (g n ∈ f n) ∧ (NeZero n → g n ∉ f (n - 1)) := by
  have nonempty_f_diff (n : ℕ) : n ≠ 0 → Nonempty {x : X | x ∈ f n \ f (n - 1)} := by
    intro hn
    have := hfStrictMono (n - 1) n (Nat.sub_one_lt hn)
    obtain ⟨_, x, hmem, hnotmem⟩ := ssubset_iff_exists.mp this
    exact ⟨x, mem_diff_of_mem hmem hnotmem⟩
  use fun n => if hn : n = 0 then hNE.some else (nonempty_f_diff n hn).some.val
  intro n
  by_cases hn : n = 0
  · simp only [imp_iff_not_or, not_neZero.mpr hn, Or.intro_left _ id, and_true]
    simp only [hn, ↓reduceDIte, Subtype.coe_prop]
  · simp only [setOf_mem_eq, hn, ↓reduceDIte, neZero_iff.mpr hn, true_implies]
    have mem_f_diff := (nonempty_f_diff n hn).some.property
    simp only [setOf_mem_eq] at mem_f_diff
    exact ⟨mem_of_mem_diff mem_f_diff, notMem_of_mem_diff mem_f_diff⟩


theorem homeomorph_real_of_union_real {X : Type*} [TopologicalSpace X]
    (f : ℕ → Set X) (hfOpen : ∀ n, IsOpen (f n)) (hfReal : ∀ n, Nonempty (f n ≃ₜ ℝ))
    (hfStrictMono : ∀ m n, m < n → f m ⊂ f n) :
    Nonempty (⋃ n, f n ≃ₜ ℝ) := by
  let α₀ : ℝ ≃ₜ f 0 := (hfReal 0).some.symm
  obtain ⟨φ₀ : f 0 ≃ₜ ℝ, hφ₀0, hφ₀1⟩ := homeomorph_open_real_fix_two_points
    (hfReal 0) (fun h => zero_ne_one (α₀.injective h)) zero_ne_one
  have hNEf0 : Nonempty (f 0) := Nonempty.intro <| (hfReal 0).some.symm 0
  obtain ⟨p, hp⟩ := strictMono_subset_representatives f hNEf0 hfStrictMono
  sorry
