import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import «OneManifold».RealOrCircle

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Set Topology Manifold

/- A connected, compact, Hausdorff space covered by charts to ℝ (i.e., a
   closed, connected 1-manifold) is homeomorphic to a circle. -/
theorem circle_homeomorph_of_closed_one_manifold (M : Type*) [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [CompactSpace M] [ChartedSpace ℝ¹ M] :
    Nonempty (M ≃ₜ Circle) := by
  obtain ⟨U, hU⟩ := real_charts M
  have hUOpen : ∀ p : M, IsOpen (U p) := fun p => (hU p).2.1
  have hCover : @univ M ⊆ ⋃ p : M, U p := fun x _ => mem_iUnion_of_mem x (hU x).1
  have hFinite := CompactSpace.isCompact_univ.elim_finite_subcover U hUOpen hCover
  have hRealCircle := Xor'.or <| real_or_circle_of_finitely_covered_one_manifold
                                 M U (fun p => (hU p).2) hFinite
  have : ¬ Nonempty (M ≃ₜ ℝ) := by
    exact fun h => (not_compactSpace_iff.mpr instNoncompactSpaceReal) h.some.compactSpace
  simpa only [this, false_or] using hRealCircle

theorem circle_homeomorph_of_closed_one_manifold' (M : Type*) [TopologicalSpace M]
    [T2Space M] [ConnectedSpace M] [CompactSpace M] [ChartedSpace ℝ¹ M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : ℂ) 1) := by
  exact circle_homeomorph_of_closed_one_manifold M

/- Every compact, connected component of a 1-manifold is homeomorphic to a circle. -/
lemma circle_homeomorph_of_compact_component (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℝ¹ M] : ∀ x : M,
      IsCompact (connectedComponent x) → Nonempty (connectedComponent x ≃ₜ Circle) := by
  intro x hx
  haveI : ConnectedSpace (connectedComponent x) := by
    exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  haveI : CompactSpace (connectedComponent x) := isCompact_iff_compactSpace.mp hx
  haveI : ChartedSpace ℝ¹ (connectedComponent x) := by
    refine TopologicalSpace.Opens.instChartedSpace ⟨connectedComponent x, ?_⟩
    haveI : LocallyConnectedSpace M := by exact ChartedSpace.locallyConnectedSpace ℝ¹ M
    exact isOpen_connectedComponent
  exact circle_homeomorph_of_closed_one_manifold (connectedComponent x)

/- Every connected component of a compact 1-manifold is homeomorphic to a circle. -/
lemma circle_homeomorph_component_of_compact (M : Type*) [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace ℝ¹ M] :
    ∀ x : M, Nonempty (connectedComponent x ≃ₜ Circle) := by
  exact fun x => circle_homeomorph_of_compact_component M x
                 isClosed_connectedComponent.isCompact
