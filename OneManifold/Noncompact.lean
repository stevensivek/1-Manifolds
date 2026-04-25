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
  obtain ⟨U, hU⟩ := real_charts M
  let C₀ := {U x | x : M}
  have hC₀Prop {p : Set M → Prop} : (∀ x : M, p (U x)) → (∀ Ω ∈ C₀, p Ω) := by
    intro hWp _ hΩ
    obtain ⟨x, hx⟩ := mem_range.mp hΩ
    rw [← hx]
    exact hWp x
  have hC₀Open : ∀ s ∈ C₀, IsOpen s := hC₀Prop (fun t => (hU t).2.1)
  have hC₀Real : ∀ s ∈ C₀, Nonempty (s ≃ₜ ℝ) := hC₀Prop (fun t => (hU t).2.2)
  have hC₀Cover : ⋃₀ C₀ = univ := by
    apply univ_subset_iff.mp
    exact fun x _ => mem_sUnion.mpr ⟨U x, mem_setOf.mpr ⟨x, rfl⟩, (hU x).1⟩
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

lemma real_homeomorph_of_finite_connected_union_of_real_homeomorphs {X : Type*}
    [TopologicalSpace X] [ConnectedSpace X] [T2Space X] (hNotCompact : ¬ CompactSpace X)
    {f : ℕ → Set X} (hReal : ∀ i, Nonempty (f i ≃ₜ ℝ)) (hOpen : ∀ i, IsOpen (f i))
    (hConn : ∀ n : ℕ, IsConnected (⋃ i ≤ n, f i)) :
    ∀ n, Nonempty (⋃ i ≤ n, f i ≃ₜ ℝ) := by
  intro n
  induction n with
  | zero =>
    have : (⋃ i, ⋃ (_ : i ≤ 0), f i) = f 0 := by
      simp only [nonpos_iff_eq_zero, iUnion_iUnion_eq_left]
    rw [this]
    exact hReal 0
  | succ n hn =>
    have hIic_split : {i | i ≤ n + 1} = {i | i ≤ n} ∪ {n + 1} := by
      have hUnion := Eq.symm <| Iic_union_Ioc_eq_Iic <| Nat.le_add_right n 1
      have : Ioc n (n + 1) = {n + 1} := by
        rw [← Finset.coe_Ioc n (n + 1)]
        exact Finset.coe_eq_singleton.mpr <| Nat.Ioc_succ_singleton n
      rwa [this] at hUnion
    have hSplit : (⋃ i ≤ n + 1, f i) = (⋃ i ≤ n, f i) ∪ (f (n + 1)) := by
      rw [show ⋃ i ≤ n, f i = ⋃ i ∈ {i | i ≤ n}, f i by simp only [mem_setOf_eq]]
      have : f (n + 1) = ⋃ i ∈ ({n + 1} : Set ℕ), f i := by
        simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
      rw [this, ← biUnion_union, ← hIic_split]
      simp only [mem_setOf_eq]
    have hUOpen : IsOpen (⋃ i ≤ n, f i) := isOpen_biUnion (fun i _ ↦ hOpen i)

    have hPreconn := (hConn (n + 1)).isPreconnected
    rw [hSplit] at hPreconn
    have := isPreconnected_iff_subset_of_disjoint.mp hPreconn (⋃ i ≤ n, f i) (f (n + 1))
      hUOpen (hOpen (n + 1)) (by apply subset_refl)

    by_cases hInter : Nonempty ((⋃ i ≤ n, f i) ∩ (f (n + 1)) : Set X)
    · have := union_of_two_real_lines hUOpen (hOpen (n + 1)) hInter hn (hReal (n + 1))
      rcases this with hRealHomeo | hCircleHomeo
      · rwa [hSplit]
      · have hMCircle := contains_open_circle X (hUOpen.union (hOpen (n + 1))) hCircleHomeo.some
        exact False.elim <| hNotCompact hMCircle.some.symm.compactSpace
    · by_contra h
      have hSubset := isPreconnected_iff_subset_of_disjoint.mp (hConn (n + 1)).isPreconnected
        (⋃ i ≤ n, f i) (f (n + 1)) hUOpen (hOpen (n + 1))
        (by simp only [hSplit, subset_refl])
        (by simp only [not_nonempty_iff_eq_empty'.mp hInter, inter_empty])
      rw [hSplit] at hSubset
      rcases hSubset with hh | hh
      · replace hh := subset_trans subset_union_right hh
        have : (⋃ i ≤ n, f i) ∪ f (n + 1) = ⋃ i ≤ n, f i :=
          Subset.antisymm (union_subset (by apply subset_refl) hh) subset_union_left
        rw [hSplit, this] at h
        exact h hn
      · replace hh := subset_trans subset_union_left hh
        have : (⋃ i ≤ n, f i) ∪ f (n + 1) = f (n + 1) :=
          Subset.antisymm (union_subset hh (by apply subset_refl)) subset_union_right
        rw [hSplit, this] at h
        exact h (hReal (n + 1))

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
    real_homeomorph_of_finite_connected_union_of_real_homeomorphs
      (notCompact_of_infinite_minimal_cover hC hInf hOpen hMinimal)
      (fun i => hReal (f i) <| Subtype.coe_prop (f i))
      (fun i => hOpen (f i) <| Subtype.coe_prop (f i)) (fun n => hf n)
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
  Nonempty (M ≃ₜ ℝ) ∨ Nonempty (M ≃ₜ Circle) ∨
  (∃ V : ℕ → Set M, ⋃ n, V n = univ ∧ (∀ n, IsOpen (V n))
      ∧ (∀ n, Nonempty (V n ≃ₜ ℝ)) ∧ (∀ n, V n ⊂ V (n + 1))) := by
  obtain ⟨C, hCOpen, hC, hCReal, hCMinimal⟩ := minimal_real_cover M
  rw [← or_assoc]
  by_cases hCInf : Infinite C
  · right
    exact exhaustion_of_one_manifold M hC hCInf hCOpen hCReal hCMinimal
  · left
    let U : {s // s ∈ C} → Set M := Subtype.val
    have hUOpenNonempty : ∀ i, IsOpen (U i) ∧ Nonempty ((U i) ≃ₜ ℝ) := by
      exact fun i => ⟨hCOpen (U i) (Subtype.coe_prop i), hCReal (U i) (Subtype.coe_prop i)⟩
    have : Finite C := Finite.of_not_infinite hCInf
    have : Fintype (@univ {s // s ∈ C}) := fintypeUniv
    have hFiniteSubcover : ∃ t : Finset {s // s ∈ C}, univ ⊆ ⋃ i ∈ t, U i := by
      use univ.toFinset
      apply univ_subset_iff.mpr
      simp_rw [← hC, toFinset_univ, Finset.mem_univ, iUnion_true, sUnion_eq_iUnion]
      rfl
    exact (real_or_circle_of_finitely_covered_one_manifold
           M U hUOpenNonempty hFiniteSubcover).or
