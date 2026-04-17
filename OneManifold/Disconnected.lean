import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
The main result of this file is `homeomorph_sigma_components`, which says that
a locally connected space is homeomorphic to the disjoint union of its
connected components.
-/

open Function Set

theorem homeomorph_sigma_components (X : Type*) [TopologicalSpace X] [LocallyConnectedSpace X] :
    Nonempty (X ≃ₜ (c : ConnectedComponents X) × (ConnectedComponents.mk ⁻¹' {c})) := by
  let CCM (c : ConnectedComponents X) : Set X := ConnectedComponents.mk ⁻¹' {c}
  let f : (Σ c : ConnectedComponents X, (CCM c)) → X := fun ⟨c, x⟩ => ↑x
  have hfContinuous : Continuous f := by
    exact continuous_sigma <| fun _ => continuous_subtype_val
  have hfBijective : Bijective f := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      simp only [f] at hxy
      refine Sigma.subtype_ext_iff.mpr ⟨?_, hxy⟩
      have (t : (c : ConnectedComponents X) × { x // x ∈ CCM c }) :
        t.fst = ConnectedComponents.mk t.snd.val := by rw [t.snd.property]
      rw [this x, this y, hxy]
    · exact fun b => by use ⟨ConnectedComponents.mk b, ⟨b, mem_preimage.mp rfl⟩⟩
  have hfOpenMap : IsOpenMap f := by
    apply isOpenMap_sigma.mpr
    exact fun c => IsOpen.isOpenMap_subtype_val <| isOpen_mk.mpr <| isOpen_discrete {c}
  exact Nonempty.intro (IsHomeomorph.mk hfContinuous hfOpenMap hfBijective).homeomorph.symm

theorem card_components {ι : Type*} {σ : ι → Type*} [(i : ι) → TopologicalSpace (σ i)]
    [hConn : (i : ι) → ConnectedSpace (σ i)] :
    Nat.card (ConnectedComponents (Σ i, σ i)) = Nat.card ι := by
  let f : ι → ConnectedComponents (Σ i, σ i) :=
    fun i => ConnectedComponents.mk <| Sigma.mk i (hConn i).toNonempty.some
  have hInjective : Injective f := by
    intro c d hcd
    obtain ⟨a,s,⟨hs,h⟩⟩ := Sigma.isConnected_iff.mp <| isConnected_connectedComponent
                           (x := Sigma.mk d (hConn d).toNonempty.some)
    apply ConnectedComponents.coe_eq_coe'.mp at hcd
    obtain ⟨_, _, hmk_ac⟩ := by simpa only [h] using hcd
    obtain ⟨_, _, hmk_ad⟩ : Sigma.mk d (hConn d).toNonempty.some ∈ Sigma.mk a '' s := by
      rw [← h]
      exact mem_connectedComponent
    have hac : a = c := (Sigma.mk.inj_iff.mp hmk_ac).left
    have had : a = d := (Sigma.mk.inj_iff.mp hmk_ad).left
    exact Eq.trans (Eq.symm hac) had
  have hSurjective : Surjective f := by
    intro c
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
    use x.fst
    rw [← hx]
    refine ConnectedComponents.coe_eq_coe'.mpr ?_
    have hconn_sigma_mk (i : ι) : IsConnected (Sigma.fst (β := σ) ⁻¹' {i}) := by
      rw [← Set.range_sigmaMk i]
      exact isConnected_range <| continuous_sigmaMk
    apply (hconn_sigma_mk x.fst).subset_connectedComponent <;>
      exact mem_preimage.mpr <| mem_singleton x.fst
  exact Eq.symm <| Nat.card_eq_of_bijective f ⟨hInjective, hSurjective⟩

theorem card_fin_product (X : Type*) [TopologicalSpace X] [h : ConnectedSpace X] (n : ℕ) :
    Nat.card (ConnectedComponents ((_ : Fin n) × X)) = n := by
  rw [card_components (hConn := fun _ => h)]
  exact Nat.card_fin n

theorem Homeomorph.connectedComponentsMap_bijective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {φ : X ≃ₜ Y} :
    Bijective φ.continuous.connectedComponentsMap := by
  let hf := φ.continuous
  let hg := φ.symm.continuous
  refine bijective_iff_has_inverse.mpr ?_
  use hg.connectedComponentsMap
  have hcomp_f {c : X} : hf.connectedComponentsMap (ConnectedComponents.mk c)
      = ConnectedComponents.mk (φ c) := rfl
  have hcomp_g {c : Y} : hg.connectedComponentsMap (ConnectedComponents.mk c)
      = ConnectedComponents.mk (φ.symm c) := rfl
  constructor <;> intro c <;> obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  · rw [← hx, hcomp_f, hcomp_g, symm_apply_apply φ x]
  · rw [← hx, hcomp_g, hcomp_f, apply_symm_apply φ x]

instance connectedSpace_Circle : ConnectedSpace Circle := by
  apply connectedSpace_iff_univ.mpr
  apply AddCircle.homeomorphCircle'.isConnected_preimage.mp
  rw [preimage_univ]
  exact isConnected_univ
