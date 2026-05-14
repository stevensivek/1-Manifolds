import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Connected.TotallyDisconnected
import «OneManifold».Disconnected
import «OneManifold».Noncompact
import «OneManifold».RealOrCircle

/-!
This file contains several theorems about the classification of 1-manifolds.
A 1-manifold is a second-countable Hausdorff space covered by charts to ℝ¹.
(If it is compact then we can omit the second-countable hypothesis.)

## Main results

- `circle_homeomorph_of_closed_one_manifold` : A compact, connected 1-manifold
  is homeomorphic to a circle.

- `real_or_circle_homeomorph_of_one_manifold` : A connected 1-manifold is
  homeomorphic to either ℝ or a circle.

- `sigma_circle_homeomorph` : If `M` is a compact 1-manifold, then there is
  a unique `n ∈ ℕ` such that `M` is homeomorphic to a disjoint union
  `(_ : Fin n) × Circle` of circles.
-/

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Set Topology Function

/- A connected, compact, Hausdorff space covered by charts to ℝ¹ (i.e., a
   closed, connected 1-manifold) is homeomorphic to a circle. -/
theorem circle_homeomorph_of_closed_one_manifold (M : Type*) [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [CompactSpace M] [ChartedSpace ℝ¹ M] :
    Nonempty (M ≃ₜ Circle) := by
  obtain ⟨U, hUmem, hUOpen, hUReal, _⟩ := real_charts M
  have hCover : @univ M ⊆ ⋃ p : M, U p := fun x _ => mem_iUnion_of_mem x (hUmem x)
  have hFinite := CompactSpace.isCompact_univ.elim_finite_subcover U hUOpen hCover
  have hRealCircle := real_or_circle_of_finitely_covered_one_manifold M U hUOpen hUReal hFinite
  have : ¬ Nonempty (M ≃ₜ ℝ) :=
    fun h => (not_compactSpace_iff.mpr instNoncompactSpaceReal) h.some.compactSpace
  simpa only [this, false_or] using hRealCircle

/- A connected, second countable, Hausdorff space covered by charts to ℝ¹
   (i.e., a connected 1-manifold) is homeomorphic to either ℝ or a circle. -/
theorem real_or_circle_homeomorph_of_one_manifold (M : Type*) [TopologicalSpace M]
    [SecondCountableTopology M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℝ¹ M] :
    Nonempty (M ≃ₜ ℝ) ∨ Nonempty (M ≃ₜ Circle) := real_or_circle_of_one_manifold M

/- Every compact, connected component of a 1-manifold is homeomorphic to a circle. -/
lemma circle_homeomorph_of_compact_component (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℝ¹ M] : ∀ x : M,
      IsCompact (connectedComponent x) → Nonempty (connectedComponent x ≃ₜ Circle) := by
  intro x hx
  haveI : ConnectedSpace (connectedComponent x) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  haveI : CompactSpace (connectedComponent x) := isCompact_iff_compactSpace.mp hx
  haveI : ChartedSpace ℝ¹ (connectedComponent x) := by
    refine TopologicalSpace.Opens.instChartedSpace ⟨connectedComponent x, ?_⟩
    haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℝ¹ M
    exact isOpen_connectedComponent
  exact circle_homeomorph_of_closed_one_manifold (connectedComponent x)

/- Every connected component of a 1-manifold is homeomorphic to ℝ or a circle. -/
lemma real_or_circle_homeomorph_of_component (M : Type*) [TopologicalSpace M]
    [SecondCountableTopology M] [T2Space M] [ChartedSpace ℝ¹ M] : ∀ x : M,
      Nonempty (connectedComponent x ≃ₜ ℝ) ∨ Nonempty (connectedComponent x ≃ₜ Circle) := by
  intro x
  haveI : ConnectedSpace (connectedComponent x) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  haveI : ChartedSpace ℝ¹ (connectedComponent x) := by
    refine TopologicalSpace.Opens.instChartedSpace ⟨connectedComponent x, ?_⟩
    haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℝ¹ M
    exact isOpen_connectedComponent
  exact real_or_circle_homeomorph_of_one_manifold (connectedComponent x)

/- Every connected component of a compact 1-manifold is homeomorphic to a circle. -/
lemma circle_homeomorph_component_of_compact (M : Type*) [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace ℝ¹ M] :
    ∀ x : M, Nonempty (connectedComponent x ≃ₜ Circle) :=
  fun x => circle_homeomorph_of_compact_component M x isClosed_connectedComponent.isCompact

lemma circle_homeomorph_preimage_connectedComponents (M : Type*) [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace ℝ¹ M] :
    ∀ c : ConnectedComponents M,
      Nonempty (ConnectedComponents.mk ⁻¹' {c} ≃ₜ Circle) := by
  intro c
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  rw [← hx, connectedComponents_preimage_singleton]
  exact circle_homeomorph_component_of_compact M x

lemma real_or_circle_homeomorph_preimage_connectedComponents (M : Type*) [TopologicalSpace M]
    [SecondCountableTopology M] [T2Space M] [ChartedSpace ℝ¹ M] :
    ∀ c : ConnectedComponents M,
      Nonempty (ConnectedComponents.mk ⁻¹' {c} ≃ₜ ℝ) ∨
      Nonempty ((ConnectedComponents.mk) ⁻¹' {c} ≃ₜ Circle) := by
  intro c
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  rw [← hx, connectedComponents_preimage_singleton]
  exact real_or_circle_homeomorph_of_component M x

/- A compact Hausdorff space covered by charts to ℝ¹ is homeomorphic to a
   disjoint union of `n` circles, for exactly one value of `n ∈ ℕ`. -/
theorem sigma_circle_homeomorph (M : Type*) [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace ℝ¹ M] :
    ∃! n : ℕ, Nonempty (M ≃ₜ (_ : Fin n) × Circle) := by
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℝ¹ M
  apply existsUnique_of_exists_of_unique
  · obtain ⟨n, hn⟩ := finite_iff_exists_equiv_fin.mp <|
      instFiniteConnectedComponentsOfLocallyConnectedSpaceOfCompactSpace (α := M)
    use n
    let α : ConnectedComponents M ≃ Fin n := hn.some
    have f₁ : M ≃ₜ Σ (c : ConnectedComponents M), ConnectedComponents.mk ⁻¹' {c} :=
      (homeomorph_sigma_components M).some
    have f₂ : (Σ (c : ConnectedComponents M), (ConnectedComponents.mk ⁻¹' {c}))
        ≃ₜ Σ (_ : Fin n), Circle := by
      let β := fun (c : ConnectedComponents M) ↦ (ConnectedComponents.mk ⁻¹' {c})
      let φ : (c : ConnectedComponents M) → (β c ≃ₜ Circle) :=
        fun c ↦ (circle_homeomorph_preimage_connectedComponents M c).some
      exact (IsHomeomorph.sigmaMap α.bijective <| fun c ↦ (φ c).isHomeomorph).homeomorph
    exact Nonempty.intro (f₁.trans f₂)
  · intro m n hm hn
    let φ : (_ : Fin m) × Circle ≃ₜ (_ : Fin n) × Circle := hm.some.symm.trans hn.some
    rw [← card_fin_product Circle m, ← card_fin_product Circle n]
    exact Nat.card_eq_of_bijective φ.continuous.connectedComponentsMap
          φ.connectedComponentsMap_bijective
