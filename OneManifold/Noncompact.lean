import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Paracompact
import «OneManifold».RealCover
import «OneManifold».RealLemmas

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Set Function Topology
set_option linter.style.emptyLine false

variable (M : Type*)
  [TopologicalSpace M] [SecondCountableTopology M] [T2Space M] [ChartedSpace ℝ¹ M]

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
    (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧ (∀ x : M, {s ∈ C | x ∈ s}.Finite) ∧
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
    have hj : IsOpenEmbedding j := by
      apply IsOpenEmbedding.of_continuous_injective_isOpenMap
      · exact Continuous.subtype_map continuous_id hWU
      · exact Subtype.map_injective hWU fun _ _ t ↦ t
      · exact IsOpenMap.subtype_map IsOpenMap.id (hWOpen i) hWU
    have hW'Conn: IsConnected (range j) := by
      have := isConnected_iff_connectedSpace.mp (hWConn i)
      exact isConnected_range <| Continuous.subtype_map continuous_id' hWU
    let X := φ '' (range j)
    have hXOpen : IsOpen X := φ.isOpen_image.mpr hj.isOpenMap.isOpen_range
    have hXConn : IsConnected X := φ.isConnected_image.mpr hW'Conn
    have α : X ≃ₜ ℝ := (OpenIntervalHomeomorphReal.homeomorph_open_real hXOpen hXConn).some
    exact Nonempty.intro <| hj.toIsEmbedding.toHomeomorph.trans <| (φ.image <| range j).trans α
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
  have hCProp {p : Set M → Prop} : (∀ i : ι, p (W i)) → (∀ Ω ∈ C, p Ω) := by
    intro hWp _ hΩ
    obtain ⟨i, hi⟩ := mem_range.mp hΩ
    rw [← hi]
    exact hWp i
  have hCFinite : ∀ x : M, {s ∈ C | x ∈ s}.Finite := by
    intro x
    let f : {i | x ∈ W i} → {s ∈ C | x ∈ s} :=
      fun i => ⟨W i, mem_setOf.mpr ⟨(by use i), i.property⟩⟩
    have hf : Surjective f := by
      intro s
      obtain ⟨hsc, hx⟩ := s.property
      obtain ⟨i, hi⟩ := mem_range.mp hsc
      rw [← hi] at hx
      use ⟨i, hx⟩
      exact SetCoe.ext hi
    have : Finite {i | x ∈ W i} := finite_coe_iff.mpr (hW_point_finite x)
    exact finite_coe_iff.mp <| Finite.of_surjective f hf
  have hCCover : ⋃₀ C = univ := eq_univ_of_subset (fun _ t ↦ t) hWCover
  exact ⟨C, hCProp hWOpen, hCCover, hCFinite, hCProp hWReal⟩

lemma minimal_real_cover : ∃ (C : Set (Set M)),
    (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧ (∀ x : M, {s ∈ C | x ∈ s}.Finite) ∧
    (∀ s ∈ C, Nonempty (s ≃ₜ ℝ)) := by

  let PLFCover := fun (C : Set (Set M)) =>
    (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧ (∀ x : M, {s ∈ C | x ∈ s}.Finite) ∧
    (∀ s ∈ C, Nonempty (s ≃ₜ ℝ))

  obtain ⟨C₀, hC₀⟩ := pointFinite_real_cover M
  have hPC₀ : PLFCover C₀ := hC₀
  let S := {C : Set (Set M) | PLFCover C}
  have hLB : ∀ ch ⊆ S, IsChain (· ⊆ ·) ch → ch.Nonempty → ∃ lb ∈ S, ∀ s ∈ ch, lb ⊆ s := by
    intro ch hchS hChain hNE
    unfold IsChain at hChain
    let α := ⋂ A ∈ ch, A
    let csome := hNE.some
    have hcsome : csome ∈ ch := Nonempty.some_mem hNE
    have hPsome : PLFCover csome := hchS hcsome
    obtain ⟨hcsOpen, hcsCover, hcsFinite, hcsReal⟩ := hPsome
    refine ⟨α, mem_setOf.mpr ?_, fun _ hs => biInter_subset_of_mem hs⟩
    have hαSubset : α ⊆ csome := biInter_subset_of_mem hcsome
    refine ⟨?_, ?_, ?_, ?_⟩ -- now need to prove that PLFCover α
    · exact fun s hs => hcsOpen s <| mem_iInter₂.mp hs csome hcsome
    · -- The hard part: prove that ⋃₀ α = univ
      apply univ_subset_iff.mp
      intro x hx
      by_contra hx_mem_sUnion
      let Sx := {s | s ∈ csome ∧ x ∈ s}
      obtain ⟨mem_Sx, hmem_Sx, hx_mem_Sx⟩ : ∃ s ∈ Sx, x ∈ s := by
        have := mem_univ x
        rw [← hcsCover] at this
        obtain ⟨s, hscsome, hxs⟩ := mem_sUnion.mpr this
        exact ⟨s, mem_sep hscsome hxs, hxs⟩
      --have hxFinite : Sx.Finite := hcsFinite x
      have hxFinite' : Finite Sx := finite_coe_iff.mpr <| hcsFinite x
      have hhh : Nonempty Sx := by
        exact Nonempty.intro ⟨mem_Sx, hmem_Sx⟩
      have : (@univ Sx).Nonempty := by exact nonempty_iff_univ_nonempty.mp hhh
      have : ∀ s : Sx, ∃ t ∈ ch, s.val ∉ t := by
        intro s
        obtain ⟨hs_csome, hxs⟩ := mem_setOf.mp s.property
        by_contra! hsα
        exact hx_mem_sUnion <| mem_sUnion_of_mem hxs <| mem_iInter₂_of_mem hsα
      obtain ⟨f, hf⟩ := Classical.axiom_of_choice this
      obtain ⟨t₀, ht₀⟩ := Finite.exists_minimalFor f (@univ Sx) finite_univ
        (nonempty_iff_univ_nonempty.mp <| Nonempty.intro ⟨mem_Sx, hmem_Sx⟩)
      obtain ⟨ht₀_Sx, hfMin⟩ := ht₀
      have hSx_disjoint_ft₀ : ∀ s : Sx, ↑s ∉ f t₀ := by
        intro s
        by_contra h
        have := imp_iff_not_or.mp <| hChain (hf t₀).1 (hf s).1
        simp only [not_not] at this
        have hft₀fs : f t₀ ⊆ f s := by
          apply le_iff_subset.mp
          rcases this with h | h | h
          · exact le_of_eq h
          · exact le_iff_subset.mpr h
          · exact le_iff_subset.mpr (hfMin hx h)
        exact ((mem_compl_iff (f t₀) ↑s).mp fun a ↦ (hf s).2 (hft₀fs a)) h

      have := imp_iff_not_or.mp <| hChain (hf t₀).1 hcsome
      simp only [not_not] at this
      rcases this with h | h | h
      · -- f t₀ = csome
        rw [h] at hSx_disjoint_ft₀
        exact False.elim <| (hSx_disjoint_ft₀ ⟨mem_Sx, hmem_Sx⟩) (mem_of_mem_inter_left hmem_Sx)
      · -- f t₀ ⊆ csome
        have h'' : ∀ (s : ↑Sx), ↑s ∉ f t₀ := by
          exact fun s => (mem_compl_iff (f t₀) ↑s).mp (hSx_disjoint_ft₀ s)
        --rw [h] at hSx_disjoint_ft₀
        --exact False.elim <| (hSx_disjoint_ft₀ ⟨mem_Sx, hmem_Sx⟩) (mem_of_mem_inter_left hmem_Sx)
        sorry
      · -- csome ⊆ f t₀
        sorry
      -- have hSx_disjoint_α : ∀ s ∈ Sx, s ∉ α := by
      --   by_contra! h
      --   obtain ⟨s, hSx, hsα⟩ := h
      --   have hs_not_mem_ft₀ : s ∉ f t₀ := this ⟨s, hSx⟩
      --   have : s ∉ α := by
      --     by_contra hs_mem_α
      --     haveI : Nonempty (f t₀ ∈ ch) := Nonempty.intro (hf t₀).1
      --     have := mem_iInter.mp hs_mem_α (f t₀)
      --     have hI : ⋂ (_ : f t₀ ∈ ch), f t₀ = f t₀ := by
      --       exact iInter_eq_const <| fun _ => by simp only
      --     rw [hI] at this
      --     exact hs_not_mem_ft₀ this
      --   exact this hsα
      -- have := hSx_disjoint_α mem_Sx hmem_Sx
      -- have : ∀ s ∈ f t₀, x ∉ s := by
      --   intro s hs
      --   by_cases hx : s ∈ Sx
      --   · have : s ∈
      --     exact False.elim <| (hSx_disjoint_α s hx) hs
      --   · exact fun hxs => (hSx_disjoint_α s ⟨mem_of_subset_of_mem hαSubset hs, hxs⟩) hs
    · intro x
      apply Finite.subset (hcsFinite x) <| setOf_subset_setOf_of_imp ?_
      exact fun s => And.imp_left <| fun t ↦ mem_of_subset_of_mem hαSubset t
    · exact fun s hs => hcsReal s <| mem_iInter₂.mp hs csome hcsome

  obtain ⟨m, hmC₀, hmMinimal⟩ := zorn_superset_nonempty _ hLB C₀ hPC₀
  have : PLFCover m := hmMinimal.prop
  -- -- obtain ⟨β, V, hVOpen, hVCover, hVLocallyFinite, hRefinement⟩ :=
  -- --   ParacompactSpace.locallyFinite_refinement M U (by exact fun i => (hU i).2.1) hUCover
  -- sorry
  sorry
