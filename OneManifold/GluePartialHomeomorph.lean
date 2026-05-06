import Mathlib.Tactic

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

/- Given f g : OpenPartialHomeomorph X Y and a compact set A in the domain of
   each, if f and g are equal on frontier A and have the same image on all of
   A, then we can produce a new α : OpenPartialHomeomorph X Y with the same
   source and target as g, and such that α is equal to f on A and to g on Aᶜ. -/
theorem openPartialHomeomorph_cut_and_paste {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] {f g : OpenPartialHomeomorph X Y} {A : Set X}
    (hACompact : IsCompact A) (hAf : A ⊆ f.source) (hAg : A ⊆ g.source)
    (hAB : ∀ x ∈ frontier A, f x = g x) (hImageA : f '' A = g '' A) :
    ∃ α : OpenPartialHomeomorph X Y,
      (α.source = g.source ∧ α.target = g.target ∧ EqOn α f A ∧ EqOn α g Aᶜ) := by
  obtain ⟨φ, hφCont, hφA, hφAc⟩ := continuous_cut_and_paste
    hACompact.isClosed (f.continuousOn.mono hAf) g.continuousOn hAB
  have hfAClosed : IsClosed (f '' A) :=
    IsCompact.isClosed <| hACompact.image_of_continuousOn <| f.continuousOn.mono hAf
  have hsymm_Frontier : ∀ y ∈ frontier (f '' A), f.symm y = g.symm y := by
    intro y hy
    have hyfA : y ∈ f '' A := by
      rw [← hfAClosed.closure_eq]
      exact mem_of_mem_inter_left hy
    refine (g.eq_symm_apply ?_ ?_).mpr ?_
    · obtain ⟨z, hzA, hfzy⟩ := hyfA
      rw [← hfzy, f.left_inv <| hAf hzA]
      exact hAg hzA
    · rw [← g.image_source_eq_target]
      exact image_mono hAg (by rwa [hImageA] at hyfA)
    · have hFrontierA_subset_A : frontier A ⊆ A := hACompact.isClosed.frontier_subset
      have : f.IsImage A (f '' A) := by
        refine OpenPartialHomeomorph.IsImage.of_image_eq ?_
        rw [inter_eq_self_of_subset_right hAf, ← f.image_source_eq_target]
        exact Eq.symm <| inter_eq_self_of_subset_right <| image_mono hAf
      have : f '' (frontier A) = frontier (f '' A) := by
        have hfImage := this.frontier.image_eq
        have : frontier (f '' A) ⊆ f.target := by
          rw [← f.image_source_eq_target]
          exact subset_trans hfAClosed.frontier_subset <| image_mono hAf
        rwa [inter_eq_self_of_subset_right <| subset_trans hFrontierA_subset_A hAf,
             inter_eq_self_of_subset_right this] at hfImage
      obtain ⟨z, hzF, hzy⟩ : y ∈ f '' (frontier A) := by rwa [this]
      have : f.symm y = z := by
        rw [← hzy]
        exact f.left_inv <| hAf <| hFrontierA_subset_A hzF
      rw [this, ← hzy]
      exact Eq.symm <| hAB z hzF
  have hfA_symm_source: f '' A ⊆ f.symm.source := by
    apply subset_trans (image_mono hAf) ?_
    rw [f.symm_source]
    exact f.map_source''
  obtain ⟨ψ, hψCont, hψ_fsymm, hψ_gsymm⟩ := continuous_cut_and_paste hfAClosed
    (f.symm.continuousOn.mono hfA_symm_source) g.symm.continuousOn hsymm_Frontier
  rw [g.symm_source] at hψCont
  -- Now package φ and ψ into a PartialEquiv
  let e : PartialEquiv X Y := {
    toFun := φ,
    invFun := ψ,
    source := g.source,
    target := g.target,
    map_source' := by
      intro x hx
      by_cases h : x ∈ A <;> rw [← g.image_source_eq_target]
      · apply mem_of_subset_of_mem (image_mono hAg) ?_
        rw [hφA h, ← hImageA]
        exact mem_image_of_mem f h
      · rw [hφAc h]
        exact mem_image_of_mem g hx,
    map_target' := by
      intro x hx
      rw [← g.symm_source] at hx
      by_cases h : x ∈ f '' A
      · apply mem_of_subset_of_mem hAg ?_
        obtain ⟨y, hyA, hgyx⟩ := h
        rwa [hψ_fsymm ⟨y, hyA, hgyx⟩, ← hgyx, f.left_inv (hAf hyA)]
      · rw [hψ_gsymm h, ← g.symm_target]
        exact g.symm.map_source hx
    left_inv' := by
      intro x hx
      by_cases h : x ∈ A
      · rw [hφA h, hψ_fsymm <| mem_image_of_mem f h]
        exact f.left_inv (hAf h)
      · have : g x ∈ (f '' A)ᶜ := by
          rw [hImageA]
          by_contra hg
          obtain ⟨y, hyA, hgy⟩ := not_notMem.mp hg
          have : x = y := Eq.symm <| g.injOn (hAg hyA) hx hgy
          exact h <| mem_of_eq_of_mem this hyA
        rw [hφAc h, hψ_gsymm this]
        exact g.left_inv hx
    right_inv' := by
      intro x hx
      by_cases h : x ∈ f '' A
      · have : f.symm x ∈ A := by
          obtain ⟨y, hyA, hgy⟩ := h
          rwa [← hgy, f.left_inv (hAf hyA)]
        rw [hψ_fsymm h, hφA this]
        exact f.right_inv (hfA_symm_source h)
      · have : g.symm x ∉ A := by
          rw [hImageA] at h
          by_contra hgsymm_x
          have : g (g.symm x) ∈ g '' A := mem_image_of_mem g hgsymm_x
          exact h <| by rwa [g.right_inv hx] at this
        rw [hψ_gsymm h, hφAc this]
        exact g.right_inv hx
  }
  let α : OpenPartialHomeomorph X Y :=
    OpenPartialHomeomorph.mk e g.open_source g.open_target hφCont hψCont
  exact ⟨α, rfl, rfl, hφA, hφAc⟩
