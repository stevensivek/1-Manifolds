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

/- A 1-manifold M admits an open cover by sets homeomorphic to ℝ such that
   every point x ∈ M belongs to only finitely many elements of the cover. -/
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
  /- Note that this refinement of the open cover U may not be what we want:
     it's locally finite, but its elements are only homeomorphic to subsets
     of ℝ (i.e., to subsets of the elements of U) rather than to ℝ itself. -/

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
    haveI : π ⟨y, hWy⟩ = b := by rw [congrArg Subtype.val hyb]
    haveI : π ⟨z, hWz⟩ = b := by rw [congrArg Subtype.val hzb]
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
      use ⟨i, by rwa [← hi] at hx⟩
      exact SetCoe.ext hi
    haveI : Finite {i | x ∈ W i} := finite_coe_iff.mpr (hW_point_finite x)
    exact finite_coe_iff.mp <| Finite.of_surjective f hf
  have hCCover : ⋃₀ C = univ := eq_univ_of_subset (fun _ t ↦ t) hWCover
  exact ⟨C, hCProp hWOpen, hCCover, hCFinite, hCProp hWReal⟩

/- A 1-manifold M admits an open cover by sets homeomorphic to ℝ such that
   (1) every point x ∈ M belongs to at most finitely many sets in the cover;
   (2) this cover is minimal with respect to inclusion, meaning that every
       proper subset of the cover is not a cover of M. -/
lemma minimal_real_cover : ∃ (C : Set (Set M)),
    (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧ (∀ x : M, {s ∈ C | x ∈ s}.Finite) ∧
    (∀ s ∈ C, Nonempty (s ≃ₜ ℝ)) ∧
    (∀ C' ⊂ C, ⋃₀ C' ≠ univ) := by

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
        have : f t₀ ∈ S := by exact mem_sep_iff.mpr <| hchS (hf t₀).1
        have : univ ⊆ ⋃₀ (f t₀) := univ_subset_iff.mpr this.2.1
        have hx_ft₀ : x ∈ ⋃₀ (f t₀) := mem_sUnion.mpr (this hx)
        have : ∀ s ∈ f t₀, x ∉ s :=
          fun s hs hxs => (hSx_disjoint_ft₀ <| Subtype.mk s ⟨mem_of_subset_of_mem h hs, hxs⟩) hs
        have : x ∉ ⋃₀ (f t₀) := by
          by_contra hx
          obtain ⟨s, hsf, hxs⟩ := mem_sUnion.mp hx
          exact (this s hsf) hxs
        exact this hx_ft₀
      · -- csome ⊆ f t₀
        obtain ⟨t, htc, hxt⟩ := mem_sUnion.mp <| univ_subset_iff.mpr hcsCover (mem_univ x)
        have : x ∉ t := by
          by_cases ht_Sx : t ∈ Sx
          · exact False.elim <| (hSx_disjoint_ft₀ <| Subtype.mk t ht_Sx)
                                (mem_of_subset_of_mem h htc)
          · exact fun hxt => ht_Sx ⟨htc, hxt⟩
        exact this hxt
    · intro x
      apply Finite.subset (hcsFinite x) <| setOf_subset_setOf_of_imp ?_
      exact fun s => And.imp_left <| fun t ↦ mem_of_subset_of_mem hαSubset t
    · exact fun s hs => hcsReal s <| mem_iInter₂.mp hs csome hcsome

  obtain ⟨m, hmC₀, hmMinimal⟩ := zorn_superset_nonempty _ hLB C₀ hPC₀
  have : PLFCover m := hmMinimal.prop
  unfold PLFCover at this
  obtain ⟨hmOpen, hmCover, hmFinite, hmReal⟩ := hmMinimal.prop

  have hssubset {s : Set (Set M)} : s ⊂ m → ⋃₀ s ≠ univ := by
    intro hsm
    have hNotCover : ¬ PLFCover s := MinimalFor.not_prop_of_lt hmMinimal hsm
    unfold PLFCover at hNotCover
    push Not at hNotCover
    have hopen : ∀ Ω ∈ s, IsOpen Ω :=
      fun Ω hΩ => hmOpen Ω <| mem_of_subset_of_mem (subset_of_ssubset hsm) hΩ
    have hreal : ¬ ∃ Ω ∈ s, IsEmpty (Ω ≃ₜ ℝ) := by
      push Not
      exact fun Ω hΩ => hmReal Ω <| mem_of_subset_of_mem (subset_of_ssubset hsm) hΩ
    have hfin: ∀ x : M, {Ω | Ω ∈ s ∧ x ∈ Ω}.Finite := by
      apply fun x => Finite.subset (hmFinite x) ?_
      exact fun _ ht => ⟨mem_of_subset_of_mem (subset_of_ssubset hsm) ht.1, ht.2⟩
    by_contra hCover
    exact hreal <| hNotCover hopen hCover hfin

  use m

/- If a cover of X has no proper subcover, then every set U in the cover
   contains some point that is in U but not in any other set in the cover. -/
lemma minimal_cover_choose_points {X : Type*} [TopologicalSpace X]
    {C : Set (Set X)} (hC : ⋃₀ C = univ) :
    (∀ C' ⊂ C, ⋃₀ C' ≠ univ) →
    (∃ f : C → X, ∀ U : C, f U ∈ U.val ∧ (∀ V : C, f U ∈ V.val → U = V)) := by
  intro hC'
  have hUniquePoint : ∀ Ω : C, ∃ p ∈ Ω.val, (∀ Ω' ∈ C, p ∈ Ω' → Ω' = Ω) := by
    intro ⟨Ω, hΩ⟩
    let C' := C \ {Ω}
    have hnotUniv : ⋃₀ C' ≠ univ := hC' C' <| diff_singleton_ssubset.mpr hΩ
    obtain ⟨p, hp⟩ : ∃ p, p ∉ ⋃₀ C' := (ne_univ_iff_exists_notMem (⋃₀ C')).mp hnotUniv
    use p
    have hpΩ : ∀ Ω' ∈ C, p ∈ Ω' → Ω' = Ω := by
      intro Ω' hΩ' hp'
      have : Ω' ∉ C' := fun h => hp (mem_sUnion_of_mem hp' h)
      have : Ω' ∈ C \ C' := by exact mem_diff_of_mem hΩ' this
      rw [diff_diff_cancel_left <| singleton_subset_iff.mpr hΩ] at this
      exact mem_singleton_iff.mp this
    have : p ∈ ⋃₀ C := by rw [hC]; exact mem_univ p
    obtain ⟨ω, hωC, hpω⟩ := mem_sUnion.mp this
    rw [hpΩ ω hωC hpω] at hpω
    exact ⟨hpω, hpΩ⟩
  obtain ⟨f, hf⟩ := Classical.axiom_of_choice hUniquePoint
  use f
  exact fun U => ⟨(hf U).1, fun V hV => Eq.symm <| SetCoe.ext <| (hf U).2 V V.property hV⟩

/- A minimal open cover of a second countable space must be countable. -/
lemma countable_of_minimal_open_cover {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {C : Set (Set X)} (hC : ⋃₀ C = univ)
    (hOpen : ∀ U ∈ C, IsOpen U) (hMinimal : ∀ C' ⊂ C, ⋃₀ C' ≠ univ) :
    Countable C := by
  obtain ⟨f, hf⟩ := minimal_cover_choose_points hC hMinimal
  obtain ⟨b, hbCountable, _, hBasis⟩ := TopologicalSpace.exists_countable_basis X
  have : ∀ U : C, ∃ Ω : b, f U ∈ Ω.val ∧ Ω.val ⊆ U := by
    intro U
    obtain ⟨v, hvb, _⟩ := hBasis.exists_subset_of_mem_open
      (hf U).1 (hOpen U.val U.property)
    use ⟨v, hvb⟩
  obtain ⟨g, hg⟩ := Classical.axiom_of_choice this
  have hgInj : Injective g := by
    intro U V hUV
    apply (hf U).2 V
    apply mem_of_subset_of_mem (hg V).2
    rw [← hUV]
    exact (hg U).1
  have : Countable b := hbCountable
  exact hgInj.countable

/- Given a countably infinite set S and an element x ∈ S, find an equivalence
   ℕ ≃ S sending 0 to x. -/
lemma enumeration_fixed_zeroth {S : Type*} (hCount : Countable S) (hInf : Infinite S)
    (x : S) : ∃ f : ℕ ≃ S, f 0 = x := by
  let d : S ≃ ℕ := (nonempty_denumerable_iff.mpr ⟨hCount, hInf⟩).some.eqv
  use (d.trans (Equiv.swap 0 (d x))).symm
  simp only [Equiv.symm_apply_eq, Equiv.trans_apply]
  exact Equiv.swap_apply_eq_iff.mp rfl

/- Given an infinite open cover C of a connected space, and a finite subset
   s ⊆ U whose union is preconnected, there is another set U ∈ C \ s whose
   union with ⋃₀ s is connected. -/
lemma exists_open_intersecting_finite_union {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] {C : Set (Set X)} {s : Set (Set X)}
    (hC : ⋃₀ C = univ) (hInf : Infinite C) (hOpen : ∀ U ∈ C, IsOpen U)
    (hFin : Finite s) (hsub : s ⊆ C) (hs : IsConnected (⋃₀ s))
    (hConn : ∀ U ∈ C, IsConnected U) :
    ∃ U ∈ C \ s, IsConnected (U ∪ (⋃₀ s)) := by
  have hNE_C : ∀ U ∈ C, U.Nonempty := fun U hU => (hConn U hU).nonempty
  let C' := C \ s
  have hNE_UC' : (⋃₀ C').Nonempty := by
    obtain ⟨c₀, hc₀C, hc₀s⟩ := (infinite_coe_iff.mp hInf).exists_notMem_finite
                               (not_infinite.mp fun a ↦ a hFin)
    exact nonempty_sUnion.mpr ⟨c₀, mem_diff_of_mem hc₀C hc₀s, hNE_C c₀ hc₀C⟩
  have hOpen_UC' : IsOpen (⋃₀ C') :=
    isOpen_sUnion <| fun t ht => hOpen t (mem_of_mem_inter_left ht)
  have hOpen_Us : IsOpen (⋃₀ s) :=
    isOpen_sUnion <| fun t ht => hOpen t (hsub ht)
  have hCover : (⋃₀ C') ∪ (⋃₀ s) = univ := by
    simp_rw [← sUnion_union, ← hC, C']
    apply congrArg sUnion
    exact diff_union_of_subset hsub
  have hsNE : Nonempty s := by
    obtain ⟨U, hUs, _⟩ := nonempty_sUnion.mp hs.nonempty
    exact Nonempty.intro <| codRestrict (fun x ↦ U) s (fun x ↦ hUs) X
  have hNE_Us : (⋃₀ s).Nonempty := by
    let s₀ := hsNE.some
    refine nonempty_sUnion.mpr ⟨↑s₀, Subtype.coe_prop s₀, ?_⟩
    exact hNE_C ↑s₀ <| mem_of_subset_of_mem hsub (Subtype.coe_prop s₀)
  have hNE_inter := nonempty_inter hOpen_UC' hOpen_Us hCover hNE_UC' hNE_Us
  let x := hNE_inter.some -- x ∈ (⋃₀ C') ∩ (⋃₀ s)
  obtain ⟨hxC', hxs⟩ := (mem_inter_iff x (⋃₀ C') (⋃₀ s)).mp hNE_inter.some_mem
  obtain ⟨t, htC', hxt⟩ := mem_sUnion.mp hxC'
  refine ⟨t, htC', IsConnected.union (nonempty_def.mpr ⟨x, ?_⟩) ?_ hs⟩
  · simp only [mem_inter_iff, hxt, hxs, true_and]
  · exact hConn t <| mem_of_mem_inter_left htC'

/- Given an infinite minimal cover of a connected, second countable space
   X by connected open sets, and given a set U in the cover, we can find an
   enumeration f : ℕ → C of the cover so that f 0 = U, and so that for each
   n > 0 the union of the first n sets is connected. -/
lemma connected_enumeration_of_minimal_open_cover {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [ConnectedSpace X] {C : Set (Set X)}
    (hC : ⋃₀ C = univ) (hInf : Infinite C) (hOpen : ∀ U ∈ C, IsOpen U)
    (hConn : ∀ U ∈ C, IsConnected U)
    (hMinimal : ∀ C' ⊂ C, ⋃₀ C' ≠ univ) (U₀ : C) :
    ∃ f : ℕ → C, (f 0 = U₀ ∧ Injective f ∧
                 (∀ n, IsConnected ((⋃ j : Fin n, f j) : Set X))) := by
  have hCountable : Countable C := countable_of_minimal_open_cover hC hOpen hMinimal
  obtain ⟨f₀ : ℕ ≃ C, hf₀⟩ := enumeration_fixed_zeroth hCountable hInf U₀

  /- Every nonempty, finite subset of C with connected sUnion can be enlarged to
     another such subset by adding one element of C -/
  let Csub : Set (Set (Set X)) := {S ⊆ C | Nonempty S ∧ Finite S ∧ IsConnected (⋃₀ S)}
  have hU₀ : {U₀.val} ∈ Csub := by
    refine ⟨?_, instNonemptyOfInhabited, Finite.of_subsingleton, ?_⟩
    · exact singleton_subset_iff.mpr (Subtype.coe_prop U₀)
    · simp only [sUnion_singleton, hConn U₀.val (Subtype.coe_prop U₀)]
  have : ∀ S : Csub, ∃ S' : Csub, S.val ⊆ S'.val ∧ ∃ a ∈ C, S'.val \ S.val = {a} := by
    intro ⟨S, hS⟩
    obtain ⟨hSC, hSNE, hSFinite, hSConn⟩ := mem_setOf.mp hS
    obtain ⟨U, hUCS, hUConn⟩ := exists_open_intersecting_finite_union
      hC hInf hOpen hSFinite hSC hSConn hConn
    have hUS : {U} ∪ S ∈ Csub := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact union_subset (singleton_subset_iff.mpr <| mem_of_mem_inter_left hUCS) hSC
      · exact Nonempty.intro <| codRestrict (fun x ↦ U) ({U} ∪ S) (fun x ↦ mem_union_left S rfl) X
      · exact Finite.Set.finite_union {U} S
      · rwa [sUnion_union, sUnion_singleton]
    use Subtype.mk ({U} ∪ S) hUS
    constructor
    · exact subset_union_right
    · refine ⟨U, mem_of_mem_inter_left hUCS, union_diff_cancel_right ?_⟩
      exact subset_empty_iff.mpr <| singleton_inter_eq_empty.mpr <| notMem_of_mem_diff hUCS
  obtain ⟨g, hg⟩ := Classical.axiom_of_choice this
  /- Now we iterate this action n times, starting with {U₀}, to get a sequence
     i : ℕ → Csub so that each i (n + 1) is built by adding a single element
     of the cover C to (i n) -/
  let i : ℕ → Csub := fun n => Nat.iterate g n ⟨{U₀.val}, hU₀⟩
  have hg_iterate : ∀ n : ℕ, i (n + 1) = g (i n) := by
    exact fun n => iterate_succ_apply' g n ⟨{↑U₀}, hU₀⟩
  have hi_subset : ∀ n : ℕ, (i n).val ⊆ (i (n + 1)).val := by
    intro n
    rw [hg_iterate n]
    exact (hg (i n)).1
  have hi_diff_singleton : ∀ n : ℕ, ∃ a : C, (i (n + 1)).val \ (i n).val = {↑a} := by
    intro n
    obtain ⟨hSubset, a, haC, hdiff⟩ := hg (i n)
    rw [← hg_iterate n] at hdiff
    exact ⟨⟨a, haC⟩, hdiff⟩
  obtain ⟨new_elt, hnew⟩ := Classical.axiom_of_choice hi_diff_singleton
  /- Finally, we produce a function from the elements of each i (n+1) \ i n -/
  let f : ℕ → C := fun n => if n = 0 then ↑U₀ else new_elt (n - 1)
  have hf0 : f 0 = U₀ := by rfl
  have : ∀ n, {↑(f j) | j ≤ n} ∈ Csub := by
    sorry

  sorry
