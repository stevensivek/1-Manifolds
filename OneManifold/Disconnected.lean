import Mathlib.Tactic

/-!
The main result of this file is `homeomorph_sigma_components`, which says that
a locally connected space is homeomorphic to the disjoint union of its
connected components.
-/

open Set Topology Function

variable (X : Type*) [TopologicalSpace X] [LocallyConnectedSpace X]

private def CCM (c : ConnectedComponents X) : Set X := ConnectedComponents.mk ⁻¹' {c}

private noncomputable def homeomorph_of_sigma_component_subtypes :
    (c : ConnectedComponents X) × { x // x ∈ CCM X c } ≃ₜ X := by
  let f : (Σ c : ConnectedComponents X, {x // x ∈ CCM X c}) → X := fun ⟨c, x⟩ => ↑x
  have hfContinuous : Continuous f := by
    exact continuous_sigma <| fun _ => continuous_subtype_val
  have hfInjective : Injective f := by
    intro x y hxy
    simp only [f] at hxy
    refine Sigma.subtype_ext_iff.mpr ⟨?_, hxy⟩
    have (t : (c : ConnectedComponents X) × { x // x ∈ CCM X c }) :
      t.fst = ConnectedComponents.mk t.snd.val := by rw [t.snd.property]
    rw [this x, this y, hxy]
  have hfBijective : Bijective f := by
    refine ⟨hfInjective, ?_⟩
    exact fun b => by use ⟨ConnectedComponents.mk b, ⟨b, mem_preimage.mp rfl⟩⟩
  have hfOpenMap : IsOpenMap f := by
    apply isOpenMap_sigma.mpr
    exact fun c => IsOpen.isOpenMap_subtype_val <| isOpen_mk.mpr <| isOpen_discrete {c}
  exact (IsHomeomorph.mk hfContinuous hfOpenMap hfBijective).homeomorph

private noncomputable def homeomorph_component_subtype :
    (c : ConnectedComponents X) × { x // x ∈ CCM X c } ≃ₜ
    (c : ConnectedComponents X) × (CCM X c) := by
  let g : (c : ConnectedComponents X) → ({ x // x ∈ CCM X c } → (CCM X (id c))) :=
    fun c => (fun (x : { x // x ∈ CCM X c }) => x)
  have hg : ∀ c : ConnectedComponents X, IsHomeomorph (g c) := by
    simp only [id_eq, g]
    exact fun c => (Homeomorph.refl { x // x ∈ CCM X c }).isHomeomorph
  let ψ := Sigma.map
                (id (α := ConnectedComponents X))
                g (β₁ := fun c => {x // x ∈ CCM X c}) (β₂ := fun c => CCM X c)
  exact (IsHomeomorph.sigmaMap bijective_id hg).homeomorph

theorem homeomorph_sigma_components :
    Nonempty (X ≃ₜ Σ (c : ConnectedComponents X), (ConnectedComponents.mk ⁻¹' {c})) :=
  Nonempty.intro <| (homeomorph_of_sigma_component_subtypes X).symm.trans
                    (homeomorph_component_subtype X)
