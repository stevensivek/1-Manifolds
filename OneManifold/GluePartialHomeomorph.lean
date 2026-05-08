import Mathlib.Tactic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
The main result of this file is `openPartialHomeomorph_cut_and_paste`, which
takes as inputs `f g : OpenPartialHomeomorph X Y` and a compact subset
`A ⊆ f.source ∩ g.source` such that `f` and `g` are equal when restricted to
`frontier A` and such that the images `f '' A` and `g '' A` are equal.  It
produces a new `α : OpenPartialHomeomorph X Y` that is equal to `f` on `A`
and to `g` everywhere else, and that has the same source and target as `g`.
-/

open Set Topology

/- If maps f g : X → Y agree on the frontier of a compact set A, and if f is
   continuous on A and g is continuous on B, then we can cut and paste to
   get a new morphism φ : X → Y that (1) agrees with f on A and with g on Aᶜ, and
   (2) is continuous on B. -/
lemma continuous_cut_and_paste {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : X → Y} {A B : Set X} (hAClosed : IsClosed A)
    (hfSource : ContinuousOn f A) (hgSource : ContinuousOn g B)
    (hAB : ∀ x ∈ frontier A, f x = g x) :
    ∃ φ : X → Y, ContinuousOn φ B ∧ EqOn φ f A ∧ EqOn φ g Aᶜ := by
  classical
  let φ : X → Y := piecewise A f g
  have hφCont : ContinuousOn φ B := by
    apply ContinuousOn.piecewise
    · exact fun a ha => hAB a (mem_of_mem_inter_right ha)
    · rw [hAClosed.closure_eq]
      exact hfSource.mono inter_subset_right
    · exact hgSource.mono inter_subset_left
  have hψA : ∀ x ∈ A, φ x = f x := fun _ a ↦ piecewise_eq_of_mem A f g a
  have hψAc : ∀ x ∉ A, φ x = g x := fun _ a ↦ piecewise_eq_of_notMem A f g a
  exact ⟨φ, hφCont, hψA, hψAc⟩

/- Given f g : OpenPartialHomeomorph X Y and a closed set A in the domain of
   each, if f and g are equal on frontier A and have the same image on all of
   A, then we can produce a new α : OpenPartialHomeomorph X Y with the same
   source and target as g, and such that α is equal to f on A and to g on Aᶜ. -/
theorem openPartialHomeomorph_cut_and_paste {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : OpenPartialHomeomorph X Y} {A : Set X}
    (hAClosed : IsClosed A) (hAf : A ⊆ f.source) (hAg : A ⊆ g.source)
    (hAB : ∀ x ∈ frontier A, f x = g x) (hImageA : f '' A = g '' A) :
    ∃ α : OpenPartialHomeomorph X Y,
      (α.source = g.source ∧ α.target = g.target ∧ EqOn α f A ∧ EqOn α g Aᶜ) := by
  have hfAfTarget : f '' A ⊆ f.target := by
    rw [← f.image_source_eq_target]
    exact image_mono hAf
  have hfAgtarget: f '' A ⊆ g.target := by
    rw [hImageA, ← g.image_source_eq_target]
    exact image_mono hAg
  obtain ⟨hfImage, hgImage⟩ : f.IsImage A (f '' A) ∧ g.IsImage A (f '' A):= by
    constructor <;> apply OpenPartialHomeomorph.IsImage.of_image_eq
                <;> rw [inter_eq_self_of_subset_right, inter_eq_self_of_subset_right]
                <;> try assumption
    exact Eq.symm hImageA
  have hfrontier_subset : frontier A ⊆ A := hAClosed.frontier_subset
  have hfSource_frontier : f.source ∩ frontier A = frontier A := by
    rw [inter_eq_self_of_subset_right <| subset_trans hfrontier_subset hAf]
  have hFrontier : f.source ∩ frontier A = g.source ∩ frontier A := by
    rw [hfSource_frontier, inter_eq_self_of_subset_right <| subset_trans hfrontier_subset hAg]
  have hEq : EqOn f g (f.source ∩ frontier A) := by rwa [hfSource_frontier]
  classical
  let φ := OpenPartialHomeomorph.piecewise f g A (f '' A) hfImage hgImage hFrontier hEq
  have hφSource : φ.source = g.source := by
    have : φ.source = f.source ∩ A ∪ g.source \ A := by
      simp only [OpenPartialHomeomorph.piecewise_toPartialEquiv, PartialEquiv.piecewise_source, φ]
      rfl
    rw [inter_eq_self_of_subset_right hAf] at this
    simpa only [union_diff_self, union_eq_self_of_subset_left hAg] using this
  have hφTarget : φ.target = g.target := by
    have : φ.target = f.target ∩ (f '' A) ∪ g.target \ (f '' A) := by
      simp only [OpenPartialHomeomorph.piecewise_toPartialEquiv, PartialEquiv.piecewise_target, φ]
      rfl
    rw [inter_eq_self_of_subset_right hfAfTarget] at this
    simpa only [union_diff_self, union_eq_self_of_subset_left hfAgtarget] using this
  exact ⟨φ, hφSource, hφTarget, piecewise_eqOn A f g,
    fun _ hx => piecewise_eq_of_notMem A f g hx⟩

lemma homeomorph_real_real_fix_two_points {a b α β : ℝ} (hαβ : α ≠ β) (hab : a ≠ b) :
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
    (fun h => hxy <| ψ.injective h) hab
  use ψ.trans f
  rw [ψ.trans_apply, ψ.trans_apply, ← hfα, ← hfβ]
  constructor <;> rfl

lemma homeomorph_real_real_strictMono {a b c d : ℝ} {φ : ℝ ≃ₜ ℝ}
    (hab : a < b) (hcd : c < d) (hφa : φ a = c) (hφb : φ b = d) : StrictMono φ := by
  rcases φ.continuous.strictMono_of_inj φ.injective with hMono | hAnti
  · exact hMono
  · subst c d
    exact False.elim <| (lt_self_iff_false (φ a)).mp <| lt_trans hcd (hAnti hab)

lemma homeomorph_real_real_image_Iic_of_strictMono {f : ℝ ≃ₜ ℝ} {a : ℝ} :
    StrictMono f → f '' (Iic a) = Iic (f a) := by
  intro hMono
  apply Subset.antisymm
  · intro _ ⟨_, hy_le_a, hfy⟩
    rw [← hfy]
    exact hMono.monotone hy_le_a
  · intro x hx
    rw [← f.apply_symm_apply x]
    apply mem_image_of_mem
    have : StrictMono f.symm := by
      have : f.symm (f 0) < f.symm (f 1) := by simp only [f.symm_apply_apply, zero_lt_one]
      exact homeomorph_real_real_strictMono (hMono Real.zero_lt_one) this rfl rfl
    rw [mem_Iic, ← f.symm_apply_apply a]
    exact this.monotone (mem_Iic.mp hx)

lemma homeomorph_real_real_cut_paste {f g : ℝ ≃ₜ ℝ} {a : ℝ}
    (hf : StrictMono f) (hg : StrictMono g) (ha : f a = g a) :
    ∃ φ : ℝ ≃ₜ ℝ, (EqOn φ f (Iic a) ∧ EqOn φ g (Ici a)) := by
  let φ := f.toOpenPartialHomeomorph
  let ψ := g.toOpenPartialHomeomorph
  have haClosed : IsClosed (Iic a) := isClosed_Iic
  have haφSource : Iic a ⊆ φ.source := by
    simp only [φ, f.toOpenPartialHomeomorph_source, subset_univ]
  have haψSource : Iic a ⊆ ψ.source := by
    simp only [ψ, g.toOpenPartialHomeomorph_source, subset_univ]
  have hfg : ∀ x ∈ frontier (Iic a), f x = g x := by
    simp only [nonempty_Ioi, frontier_Iic', mem_singleton_iff, forall_eq, ha]
  have hIm : f '' (Iic a) = g '' (Iic a) := by
    rw [homeomorph_real_real_image_Iic_of_strictMono hf,
        homeomorph_real_real_image_Iic_of_strictMono hg, ha]
  obtain ⟨α, hαSource, hαTarget, hαφ, hαψ⟩ := openPartialHomeomorph_cut_and_paste
    isClosed_Iic haφSource haψSource hfg hIm
  rw [g.toOpenPartialHomeomorph_source] at hαSource
  rw [g.toOpenPartialHomeomorph_target] at hαTarget
  use α.toHomeomorphOfSourceEqUnivTargetEqUniv hαSource hαTarget
  simp only [α.toHomeomorphOfSourceEqUnivTargetEqUniv_apply]
  simp only [φ, ψ, Homeomorph.toOpenPartialHomeomorph_apply] at hαφ hαψ
  constructor
  · exact hαφ
  · intro x hx
    by_cases h : x ∈ (Iic a)ᶜ
    · exact hαψ h
    · simp only [compl_Iic, mem_Ioi, not_lt] at h
      rw [ge_antisymm hx h, ← ha]
      exact hαφ self_mem_Iic

/- Given real numbers p < a < b < q and p < c < d < q, construct a
   homeomorphism ℝ ≃ₜ ℝ sending p, a, b, q to p, c, d, q in that order. -/
lemma real_homeomorph_interpolating_four_points {p q a b c d : ℝ}
    (ha : a ∈ Ioo p q) (hb : b ∈ Ioo p q) (hc : c ∈ Ioo p q) (hd : d ∈ Ioo p q)
    (hab : a < b) (hcd : c < d) :
    ∃ φ : ℝ ≃ₜ ℝ, φ p = p ∧ φ a = c ∧ φ b = d ∧ φ q = q := by
  -- α '' (Icc p a) = (Icc p c)
  have hpa : p < a := (mem_Ioo.mp ha).left
  have hpc : p < c := (mem_Ioo.mp hc).left
  obtain ⟨α, hαp, hαa⟩ := homeomorph_real_real_fix_two_points (ne_of_lt hpa) (ne_of_lt hpc)
  have hαMono : StrictMono α := homeomorph_real_real_strictMono hpa hpc hαp hαa
  -- β '' (Icc a b) = (Icc c d)
  obtain ⟨β, hβa, hβb⟩ := homeomorph_real_real_fix_two_points (ne_of_lt hab) (ne_of_lt hcd)
  have hβMono : StrictMono β := homeomorph_real_real_strictMono hab hcd hβa hβb
  -- γ '' (Icc b q) = (Icc d q)
  have hbq : b < q := (mem_Ioo.mp hb).right
  have hdq : d < q := (mem_Ioo.mp hd).right
  obtain ⟨γ, hγb, hγq⟩ := homeomorph_real_real_fix_two_points (ne_of_lt hbq) (ne_of_lt hdq)
  have hγMono : StrictMono γ := homeomorph_real_real_strictMono hbq hdq hγb hγq
  -- Record some facts about the identity homeomorphism ℝ ≃ₜ ℝ
  have hIdMono : StrictMono (Homeomorph.refl ℝ) :=
    homeomorph_real_real_strictMono hab hab rfl rfl
  obtain ⟨hidα_p, hγid_q⟩ : (Homeomorph.refl ℝ) p = α p ∧ γ q = (Homeomorph.refl ℝ) q := by
    simp only [Homeomorph.refl_apply, id_eq, hαp, hγq, true_and]
  -- Now get φ₁ by gluing id on (Iic p) to α on (Ici p)
  obtain ⟨φ₁, hφ₁id, hφ₁α⟩ :=
    homeomorph_real_real_cut_paste hIdMono hαMono hidα_p
  have hφ₁p : φ₁ p = p := by rw [hφ₁id self_mem_Iic, Homeomorph.refl_apply, id_eq]
  have hφ₁a : φ₁ a = c := by rw [hφ₁α <| mem_Ici_of_Ioi hpa, hαa]
  have hφ₁Mono : StrictMono φ₁ := homeomorph_real_real_strictMono hpa hpc hφ₁p hφ₁a
  -- Get φ₂ by gluing φ₁ on (Iic a) to β on (Ici a)
  obtain ⟨φ₂, hφ₂φ₁, hφ₂β⟩ :=
    homeomorph_real_real_cut_paste hφ₁Mono hβMono (by rwa [← hβa] at hφ₁a)
  have hφ₂a : φ₂ a = c := by rw [hφ₂φ₁ self_mem_Ici, hφ₁a]
  have hφ₂b : φ₂ b = d := by rw [hφ₂β <| mem_Ici_of_Ioi hab, hβb]
  have hφ₂Mono : StrictMono φ₂ := homeomorph_real_real_strictMono hab hcd hφ₂a hφ₂b
  -- Get φ₃ by gluing φ₂ on (Iic b) to id on (Ici b)
  obtain ⟨φ₃, hφ₃φ₂, hφ₃γ⟩ :=
    homeomorph_real_real_cut_paste hφ₂Mono hγMono (by rwa [← hγb] at hφ₂b)
  have hφ₃b : φ₃ b = d := by rw [hφ₃γ <| self_mem_Ici, hγb]
  have hφ₃q : φ₃ q = q := by rw [hφ₃γ <| mem_Ici_of_Ioi hbq, hγq]
  refine ⟨φ₃, ?_, ?_, hφ₃b, hφ₃q⟩ <;> rw [hφ₃φ₂] <;> try rw [hφ₂φ₁]
  · exact hφ₁p
  · exact mem_Iic_of_Iio hpa
  · exact mem_Iic_of_Iio <| lt_trans hpa hab
  · exact hφ₁a
  · exact self_mem_Iic
  · exact mem_Iic_of_Iio hab
