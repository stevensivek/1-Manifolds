import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Paracompact
import «OneManifold».RealCover
import «OneManifold».RealLemmas

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Set Function Topology

variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [T2Space M]
  [ChartedSpace ℝ¹ M]

instance paracompact_ChartedSpaceR1 : ParacompactSpace M := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℝ¹ M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  exact paracompact_of_locallyCompact_sigmaCompact

lemma countable_of_open_disjoint {X : Type*} [t : TopologicalSpace X]
    [hSC : SecondCountableTopology X] {ι : Type*} {U : ι → Set X} {s : Set ι}
    (hU : ∀ i : ι, IsOpen (U i)) (hNE : ∀ i : ι, Nonempty (U i))
    (hDisjoint : PairwiseDisjoint s U) : Countable s := by
  obtain ⟨b, hbCountable, hbNE, hBasis⟩ := TopologicalSpace.exists_countable_basis X
  haveI : Countable ↑b := Countable.to_subtype hbCountable
  have bsub : ∀ i : s, ∃ Ω, Ω ∈ b ∧ Ω ⊆ U i := by
    intro i
    obtain ⟨v, hv, _, hvU⟩ := hBasis.exists_subset_of_mem_open
                              (Subtype.coe_prop (hNE i).some) (hU i)
    refine ⟨v, hv, hvU⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice bsub
  let g : s → b := fun i => ⟨f i, (hf i).1⟩
  have hfInjective : Injective f := by
    intro i j hij
    by_contra h
    have hD : Disjoint (U i) (U j) := by
      have := pairwiseDisjoint_iff.mp hDisjoint (Subtype.coe_prop i) (Subtype.coe_prop j)
      have hNotNE : ¬ (U ↑i ∩ U ↑j).Nonempty := Not.imp (Subtype.coe_ne_coe.mpr h) this
      refine Set.disjoint_iff.mpr ?_
      exact subset_empty_iff.mpr <| not_nonempty_iff_eq_empty.mp hNotNE
    have : ∅ ∈ b := by
      rw [← subset_eq_empty (hD (hf i).2 (subset_of_eq_of_subset hij (hf j).2)) rfl]
      exact (hf i).1
    exact hbNE this
  have : Injective g := by
    apply Injective.of_comp (f := Subtype.val)
    rwa [← show f = Subtype.val ∘ g by exact List.map_inj.mp rfl]
  exact this.countable

lemma real_intervals_countable {ι : Type*} {U : ι → Set ℝ} {s : Set ι}
    (hU : ∀ i : ι, IsOpen (U i)) (hNE : ∀ i : ι, Nonempty (U i))
    (hDisjoint : PairwiseDisjoint s U) : Countable s := by
  exact countable_of_open_disjoint hU hNE hDisjoint

/- An open set can be written as the union of a pairwise disjoint collection
  of open, connected sets. -/
lemma disjoint_union_of_opens {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) :
    ∃ (S : ConnectedComponents U → Set X), (∀ c, IsOpen (S c)) ∧
    (∀ c, IsConnected (S c)) ∧ PairwiseDisjoint univ S ∧ (⋃ c, S c = U) := by
  let S : ConnectedComponents U → Set X :=
    fun c => Subtype.val '' (ConnectedComponents.mk ⁻¹' {c})
  have hcOpen : ∀ c, IsOpen (S c) := by
    intro c
    have hcOpen : IsOpen (ConnectedComponents.mk ⁻¹' {c}) := by
      refine IsOpen.preimage ConnectedComponents.continuous_coe ?_
      have : DiscreteTopology (ConnectedComponents U) := by
        have : LocallyConnectedSpace U := hU.locallyConnectedSpace
        exact instDiscreteTopologyConnectedComponentsOfLocallyConnectedSpace
      exact isOpen_discrete {c}
    exact hcOpen.trans hU
  have hcConn : ∀ c, IsConnected (S c) := by
    intro c
    refine IsConnected.image ?_ Subtype.val <| Continuous.continuousOn continuous_subtype_val
    obtain ⟨_, hx⟩ := ConnectedComponents.surjective_coe c
    rw [← hx, connectedComponents_preimage_singleton]
    exact isConnected_connectedComponent
  have hUnion : ⋃ c, S c = U := by
    apply Subset.antisymm
    · exact iUnion_subset <| fun c => Subtype.coe_image_subset U (ConnectedComponents.mk ⁻¹' {c})
    · exact fun x hb => mem_iUnion_of_mem (ConnectedComponents.mk (⟨x, hb⟩ : U))
                        <| mem_image_val_of_mem hb rfl
  have hDisjoint : PairwiseDisjoint univ S := by
    apply pairwiseDisjoint_iff.mpr
    intro i _ j _ hij
    obtain ⟨x, ⟨hxi, hxj⟩⟩ := nonempty_def.mp hij
    rw [← mem_preimage.mp <| mem_of_mem_image_val hxj,
          mem_preimage.mp <| mem_of_mem_image_val hxi]
  refine ⟨S, hcOpen, hcConn, hDisjoint, hUnion⟩

lemma pointFinite_real_cover : ∃ (C : Set (Set M)),
    (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧
    (∀ x : M, {s ∈ C | x ∈ s}.Finite) ∧
    (∀ s ∈ C, Nonempty (s ≃ₜ ℝ)) := by
  obtain ⟨U, hU⟩ := real_charts M
  have hUCover : ⋃ x : M, U x = univ := by
    apply univ_subset_iff.mp
    have (t : M) : t ∈ ⋃ x, U x := by
      apply mem_iUnion.mpr
      refine ⟨t, (hU t).1⟩
    exact fun x => by simp only [mem_univ, forall_const, this x]

  obtain ⟨β, V, hVOpen, hVCover, hVLocallyFinite, hRefinement⟩ :=
    ParacompactSpace.locallyFinite_refinement M U (by exact fun i => (hU i).2.1) hUCover

  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace ℝ¹ M
  obtain ⟨compVb, hcompVb⟩ := Classical.axiom_of_choice
      <| fun b => disjoint_union_of_opens (hVOpen b)
  let bSets := fun (b : β) => {compVb b c | c}
  let ι := Σ b : β, ConnectedComponents (V b)
  let W : ι → Set M := fun ⟨b, c⟩ => compVb b c
  have hWV (i : ι) : W i ⊆ V i.fst := by
    rw [← (hcompVb i.fst).2.2.2]
    exact subset_iUnion_of_subset i.snd fun _ t => t

  have hWOpen : ∀ i : ι, IsOpen (W i) := fun i => (hcompVb i.fst).1 i.snd
  have hWConn : ∀ i : ι, IsConnected (W i) := fun i => (hcompVb i.fst).2.1 i.snd

  have hWCover : ⋃ i, W i = @univ M := by
    ext x
    constructor <;> intro hx
    · exact mem_univ x
    · have : x ∈ ⋃ b, V b := by rwa [hVCover]
      obtain ⟨b, hb⟩ := mem_iUnion.mp this
      obtain ⟨c, hc⟩ := mem_iUnion.mp (by rwa [← (hcompVb b).2.2.2] at hb)
      apply mem_iUnion.mpr
      use ⟨b, c⟩

  have hWReal : ∀ i : ι, Nonempty (W i ≃ₜ ℝ) := by
    intro i
    obtain ⟨a, ha⟩ := hRefinement i.fst
    let φ : U a ≃ₜ ℝ := (hU a).2.2.some
    have hWU (x : M) : x ∈ W i → x ∈ U a := fun hx => mem_of_subset_of_mem ha (hWV i hx)
    let j : {x // x ∈ W i} → {x // x ∈ U a} := Subtype.map id hWU
    let Wi' := range j
    have hOM : IsOpenMap j := IsOpenMap.subtype_map IsOpenMap.id (hWOpen i) hWU
    have hW'Open : IsOpen Wi' := IsOpenMap.isOpen_range hOM
    have hW'Conn: IsConnected Wi' := by
      have := isConnected_iff_connectedSpace.mp (hWConn i)
      exact isConnected_range <| Continuous.subtype_map continuous_id' hWU
    let X := φ '' Wi'
    have hXOpen : IsOpen X := φ.isOpen_image.mpr hW'Open
    have hXConn : IsConnected X := φ.isConnected_image.mpr hW'Conn
    rcases (open_real_classification X hXOpen hXConn) with h | h | h | h
    · obtain ⟨a, b, hx⟩ := h -- X = Ioo a b
      have hab : a < b := by
        have : Nonempty X := Nonempty.to_subtype hXConn.nonempty
        have : (Ioo a b).Nonempty := nonempty_coe_sort.mp (by rwa [hx] at this)
        obtain ⟨hat, htb⟩ := mem_Ioo.mp this.some_mem
        exact lt_trans hat htb
      have ψ : Ioo a b ≃ₜ ℝ :=
        OpenIntervalHomeomorphReal.homeomorph_Ioo_real hab
      sorry
    · obtain ⟨a, ha⟩ := h -- X = Iio a
      sorry
    · obtain ⟨a, ha⟩ := h -- X = Ioi a
      sorry
    · -- X = univ
      sorry

  have hW_point_finite : ∀ x : M, {i | x ∈ W i}.Finite := by
    intro x
    have : Finite {b | x ∈ V b} := finite_coe_iff.mpr <| hVLocallyFinite.point_finite x
    by_contra h
    replace h : Infinite {i | x ∈ W i} := infinite_coe_iff.mpr h
    let π : {i | x ∈ W i} → {b | x ∈ V b} :=
      fun i => ⟨i.val.fst, show x ∈ V i.val.fst
                by exact mem_of_subset_of_mem (hWV i.val) i.property⟩
    obtain ⟨⟨b, hb⟩, _⟩ := Finite.exists_infinite_fiber π
    obtain ⟨⟨⟨y, hWy⟩, hyb⟩, ⟨⟨z, hWz⟩, hzb⟩, hyz⟩ :=
      nontrivial_iff.mp <| Infinite.instNontrivial (π ⁻¹' {⟨b, hb⟩})
    replace hyz : y ≠ z := by exact fun h_eq => hyz <| SetCoe.ext <| SetCoe.ext h_eq
    have hπy : π ⟨y, hWy⟩ = b := by rw [congrArg Subtype.val hyb]
    have hπz : π ⟨z, hWz⟩ = b := by rw [congrArg Subtype.val hzb]
    have hy₁ : y.fst = b := by simp_all only [coe_setOf, mem_setOf_eq, ne_eq, π]
    have hz₁ : z.fst = b := by simp_all only [coe_setOf, mem_setOf_eq, ne_eq, π]
    obtain ⟨cy, hcy⟩ : ∃ c, y = Sigma.mk b c := by rw [← hy₁]; use y.snd
    obtain ⟨cz, hcz⟩ : ∃ c, z = Sigma.mk b c := by rw [← hz₁]; use z.snd
    have hyz_empty : (compVb b cy) ∩ (compVb b cz) = ∅ := by
      obtain ⟨_, _, hPD, _⟩ := hcompVb b
      have hcyz : cy ≠ cz := fun hcycz => hyz (by rwa [hcycz, ← hcz] at hcy)
      exact Disjoint.inter_eq (hPD trivial trivial hcyz)
    have : x ∈ (compVb b cy) ∩ (compVb b cz) := by
      apply mem_inter
      · rw [hcy] at hWy
        exact mem_of_subset_of_mem (fun _ t ↦ t) hWy
      · rw [hcz] at hWz
        exact mem_of_subset_of_mem (fun _ t ↦ t) hWz
    rw [hyz_empty] at this
    exact (mem_empty_iff_false x).mp this

  let C : Set (Set M) := {W i | i : ι}
  have hCOpen : ∀ Ω ∈ C, IsOpen Ω := by
    intro Ω hΩ
    obtain ⟨i, hi⟩ := mem_range.mp hΩ
    rw [← hi]
    exact hWOpen i
  have hCFinite : ∀ x : M, {s ∈ C | x ∈ s}.Finite := by
    intro x
    have := hW_point_finite x
    sorry
  have hCConn : ∀ Ω ∈ C, IsConnected Ω := by
    intro Ω hΩ
    obtain ⟨i, hi⟩ := mem_range.mp hΩ
    rw [← hi]
    exact hWConn i
  have hCCover : ⋃₀ C = univ := eq_univ_of_subset (fun _ t ↦ t) hWCover

  refine ⟨C, hCOpen, hCCover, hCFinite, ?_⟩
  sorry


  -- let PSubcover := fun (A : Set M) => (univ ⊆ ⋃ i ∈ A, U i)
  -- have hUCover : PSubcover univ := by
  --   intro x
  --   simp only [mem_univ, forall_const, iUnion_true, mem_iUnion]
  --   refine ⟨x, (hU x).1⟩
  -- let S := {A : Set M | PSubcover A}
  -- have hLB : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
  --   intro c hcS hChain hNE
  --   unfold IsChain at hChain
  --   let α := ⋂ A ∈ c, A
  --   use α
  --   --use (⋂ A ∈ c, A)
  --   constructor
  --   · have : PSubcover α := by
  --       intro x _
  --       sorry
  --     exact this
  --   · exact fun _ h => biInter_subset_of_mem h

  -- -- obtain ⟨β, V, hVOpen, hVCover, hVLocallyFinite, hRefinement⟩ :=
  -- --   ParacompactSpace.locallyFinite_refinement M U (by exact fun i => (hU i).2.1) hUCover
  -- sorry
