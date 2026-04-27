import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import «OneManifold».RealCover
import «OneManifold».RealLemmas
import «OneManifold».RealOrCircle
import «OneManifold».SecondCountable
import «OneManifold».TwoCharts

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Set Function Topology
set_option linter.style.emptyLine false

variable (M : Type*)
  [TopologicalSpace M] [SecondCountableTopology M] [T2Space M] [ChartedSpace ℝ¹ M]

/- A 1-manifold M admits a covering by open sets homeomorphic to ℝ such that
   every proper subset of the cover is not a cover of M. -/
lemma minimal_real_cover : ∃ (C : Set (Set M)),
    (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧ (∀ s ∈ C, Nonempty (s ≃ₜ ℝ)) ∧
    (∀ C' ⊂ C, ⋃₀ C' ≠ univ) := by
  obtain ⟨U, hUmem, hUOpen, hUReal⟩ := real_charts M
  let C₀ := {U x | x : M}
  have hC₀Prop {p : Set M → Prop} : (∀ x : M, p (U x)) → (∀ Ω ∈ C₀, p Ω) := by
    intro hWp _ hΩ
    obtain ⟨x, hx⟩ := mem_range.mp hΩ
    rw [← hx]
    exact hWp x
  have hC₀Open : ∀ s ∈ C₀, IsOpen s := hC₀Prop hUOpen
  have hC₀Real : ∀ s ∈ C₀, Nonempty (s ≃ₜ ℝ) := hC₀Prop hUReal
  have hC₀Cover : ⋃₀ C₀ = univ := by
    apply univ_subset_iff.mp
    exact fun x _ => mem_sUnion.mpr ⟨U x, mem_setOf.mpr ⟨x, rfl⟩, hUmem x⟩
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℝ¹ M
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℝ¹ M
  obtain ⟨C, hCOpen, hCCover, hCConn, hCMinimal, hCRefinement⟩ :=
    minimal_connected_refinement hC₀Open hC₀Cover
  have hCReal : ∀ s ∈ C, Nonempty (s ≃ₜ ℝ) := by
    intro s hs
    obtain ⟨t, htC₀, hst⟩ := hCRefinement s hs
    let φ : t ≃ₜ ℝ := (hC₀Real t htC₀).some
    have hMapsTo (x : M) : x ∈ s → x ∈ t := fun hx => mem_of_subset_of_mem hst hx
    let j : {x // x ∈ s} → {x // x ∈ t} := Subtype.map id hMapsTo
    have hj : IsOpenEmbedding j := by
      apply IsOpenEmbedding.of_continuous_injective_isOpenMap
      · exact Continuous.subtype_map continuous_id hMapsTo
      · exact Subtype.map_injective hMapsTo fun _ _ t ↦ t
      · exact IsOpenMap.subtype_map IsOpenMap.id (hCOpen s hs) hMapsTo
    have hjConn: IsConnected (range j) := by
      have := isConnected_iff_connectedSpace.mp (hCConn s hs)
      exact isConnected_range <| Continuous.subtype_map continuous_id' hMapsTo
    let X := φ '' (range j)
    have hXOpen : IsOpen X := φ.isOpen_image.mpr hj.isOpenMap.isOpen_range
    have hXConn : IsConnected X := φ.isConnected_image.mpr hjConn
    have α : X ≃ₜ ℝ := (OpenIntervalHomeomorphReal.homeomorph_open_real hXOpen hXConn).some
    exact Nonempty.intro <| hj.toIsEmbedding.toHomeomorph.trans <| (φ.image <| range j).trans α
  use C

/- Given a sequence f : ℕ → Set X of open sets homeomorphic to ℝ in the
   connected, non-compact, Hausdorff space X, if the union of the first n
   sets is connected then it's homeomorphic to ℝ. -/
lemma real_homeomorph_of_finite_connected_union_of_real_homeomorphs {X : Type*}
    [TopologicalSpace X] [ConnectedSpace X] [T2Space X]
    (hNotCompact : ¬ CompactSpace X)
    {f : ℕ → Set X} (hReal : ∀ i, Nonempty (f i ≃ₜ ℝ)) (hOpen : ∀ i, IsOpen (f i))
    {n : ℕ} : IsConnected (⋃ i ≤ n, f i) → Nonempty (⋃ i ≤ n, f i ≃ₜ ℝ) := by
  intro hConn
  let t : Finset ℕ := {i | i ≤ n}.toFinset
  have htOpen : ∀ i ∈ t, IsOpen (f i) := fun i _ => hOpen i
  have htReal : ∀ i ∈ t, Nonempty (f i ≃ₜ ℝ) := fun i _ => hReal i
  have htSubset : ∀ i ∈ t, f i ⊆ ⋃ j ≤ n, f j := by
    intro i hi
    apply subset_biUnion_of_mem
    simp_all only [Nat.le_eq, mem_toFinset, mem_setOf_eq, t]
    exact hi
  have htEq : ⋃ i ∈ t, f i = ⋃ i ≤ n, f i := by
    simp_all only [mem_toFinset, mem_setOf_eq, t]
  have htConn : IsConnected (⋃ i ∈ t, f i) := by
    rw [htEq]
    exact hConn
  have := real_or_circle_of_finitely_covered_one_submanifold X f
          htOpen htReal htSubset htEq hConn
  rcases this with hR | hS
  · exact hR
  · exact False.elim <| hNotCompact hS.some.symm.compactSpace

/- A 1-manifold with an infinite minimal cover by open copies of ℝ admits an
   exhaustion by open sets homeomorphic to ℝ. -/
omit [ChartedSpace ℝ¹ M] in
lemma exhaustion_of_one_manifold [ConnectedSpace M] {C : Set (Set M)}
    (hC : ⋃₀ C = univ) (hInf : Infinite C) (hOpen : ∀ U ∈ C, IsOpen U)
    (hReal : ∀ U ∈ C, Nonempty (U ≃ₜ ℝ)) (hMinimal : ∀ C' ⊂ C, ⋃₀ C' ≠ univ) :
    ∃ V : ℕ → Set M, ⋃ n, V n = univ ∧ (∀ n, IsOpen (V n))
      ∧ (∀ n, Nonempty (V n ≃ₜ ℝ)) ∧ (∀ n, V n ⊂ V (n + 1)) := by
  have hConn : ∀ U ∈ C, IsConnected U := by
    intro U hU
    rw [← Subtype.coe_image_univ U]
    have hConnUnivU : IsConnected (@univ U) :=
      (hReal U hU).some.symm.isConnected_preimage.mp isConnected_univ
    exact IsConnected.image hConnUnivU Subtype.val
      (Continuous.continuousOn continuous_subtype_val)
  obtain ⟨f, hf⟩ := connected_enumeration_of_minimal_open_cover hC hInf hOpen hConn hMinimal
  let V : ℕ → Set M := fun n => ⋃ i ≤ n, f i
  have hVCover : ⋃ n, V n = univ := by
    apply univ_subset_iff.mp
    intro x hx
    apply mem_iUnion.mpr
    obtain ⟨U, hUC, hxU⟩ : ∃ U ∈ C, x ∈ U := mem_sUnion.mp (by rwa [hC])
    let n := f.symm ⟨U, hUC⟩
    use n
    apply mem_iUnion.mpr
    simp only [mem_iUnion, exists_prop]
    exact ⟨n, le_refl n, by simpa only [n, f.apply_symm_apply]⟩
  have hVOpen : ∀ n, IsOpen (V n) :=
    fun n => isOpen_biUnion fun i _ => hOpen (f i).val (f i).property
  have hVReal : ∀ n, Nonempty (V n ≃ₜ ℝ) :=
    fun n => real_homeomorph_of_finite_connected_union_of_real_homeomorphs
      (notCompact_of_infinite_minimal_cover hC hInf hOpen hMinimal)
      (fun i => hReal (f i) <| Subtype.coe_prop (f i))
      (fun i => hOpen (f i) <| Subtype.coe_prop (f i)) (hf n)
  have hVSsubset : ∀ n, V n ⊂ V (n + 1) := by
    intro n
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · apply biUnion_subset_biUnion_left
      exact fun t ht => Nat.le_add_right_of_le ht
    · obtain ⟨p, hp⟩ := minimal_cover_choose_points hC hMinimal
      obtain ⟨hpfnMem_f, hpnUnique⟩ := hp (f (n + 1))
      have hpfnMem_V : p (f (n + 1)) ∈ V (n + 1) := by
        apply mem_of_subset_of_mem ?_ hpfnMem_f
        exact fun y hy => mem_iUnion₂.mpr ⟨n + 1, le_refl (n + 1), hy⟩
      refine Ne.symm <| ne_of_mem_of_not_mem' hpfnMem_V ?_
      by_contra h -- need to show: p (f (n + 1)) ∉ V n
      obtain ⟨k, hkn, hpfMem_fk⟩ := mem_iUnion₂.mp h
      have h_succn_k := f.injective <| hpnUnique (f k) hpfMem_fk
      exact (lt_self_iff_false n).mp
        <| lt_of_lt_of_le (lt_add_one n) (le_of_eq_of_le h_succn_k hkn)
  exact ⟨V, hVCover, hVOpen, hVReal, hVSsubset⟩

lemma real_or_circle_or_exhaustion_of_one_manifold [ConnectedSpace M] :
  (Nonempty (M ≃ₜ ℝ) ∨ Nonempty (M ≃ₜ Circle)) ∨
  (∃ V : ℕ → Set M, ⋃ n, V n = univ ∧ (∀ n, IsOpen (V n))
      ∧ (∀ n, Nonempty (V n ≃ₜ ℝ)) ∧ (∀ n, V n ⊂ V (n + 1))) := by
  obtain ⟨C, hCOpen, hC, hCReal, hCMinimal⟩ := minimal_real_cover M
  by_cases hCInf : Infinite C
  · right
    exact exhaustion_of_one_manifold M hC hCInf hCOpen hCReal hCMinimal
  · left
    let U : {s // s ∈ C} → Set M := Subtype.val
    haveI : Finite C := Finite.of_not_infinite hCInf
    haveI : Fintype (@univ {s // s ∈ C}) := fintypeUniv
    have hFiniteSubcover : ∃ t : Finset {s // s ∈ C}, univ ⊆ ⋃ i ∈ t, U i := by
      use univ.toFinset
      apply univ_subset_iff.mpr
      simp_rw [← hC, toFinset_univ, Finset.mem_univ, iUnion_true, sUnion_eq_iUnion]
      rfl
    exact real_or_circle_of_finitely_covered_one_manifold M U
            (fun i => hCOpen (U i) (Subtype.coe_prop i))
            (fun i => hCReal (U i) (Subtype.coe_prop i))
            hFiniteSubcover
