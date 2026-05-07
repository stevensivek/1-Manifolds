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
