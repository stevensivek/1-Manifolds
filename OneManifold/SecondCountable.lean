import Mathlib.Tactic
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Paracompact

/-!
This file contains several results about open covers of second countable
spaces.  Here X is always assumed to be a second countable space.

## Main results

- `minimal_connected_refinement` : If X is locally compact, locally connected,
  and Hausdorff, then any open cover can be refined to a covering by connected
  open sets that has no proper subcover.

- `connected_enumeration_of_minimal_open_cover` : Given an infinite open
  covering C of X by connected sets, with no proper subcover, there is an
  enumeration `ℕ ≃ C` such that for all n, the union of the first n sets
  is connected.
-/

open Set Function Topology
set_option linter.style.emptyLine false

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

/- A pairwise disjoint collection of nonempty open sets in a second countable
   space must be countable. -/
lemma countable_of_open_disjoint {ι : Type*} {U : ι → Set X} {s : Set ι}
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

/- An open set can be written as the union of a pairwise disjoint collection
   of open, connected sets. -/
omit [SecondCountableTopology X] in
lemma disjoint_union_of_opens [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) :
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

/- Given an open cover of a locally compact, locally connected, second
   countable Hausdorff space, there is a refinement of this cover by connected
   sets such that every point belongs to only finitely many elements of the
   refined cover. -/
lemma pointFinite_connected_refinement_of_cover
    [LocallyCompactSpace X] [T2Space X] [LocallyConnectedSpace X]
    {C : Set (Set X)} (hC : ⋃₀ C = univ) (hCOpen : ∀ s ∈ C, IsOpen s) :
    ∃ C' : Set (Set X), (∀ s ∈ C', IsOpen s) ∧ (⋃₀ C' = univ) ∧ (∀ s ∈ C', IsConnected s) ∧
      (∀ x : X, {s ∈ C' | x ∈ s}.Finite) ∧ (∀ s ∈ C', ∃ t ∈ C, s ⊆ t) := by
  let ι₀ := {U // U ∈ C}
  let U : ι₀ → Set X := fun U => U.val
  have hUCover : ⋃ i, U i = univ := by
    rw [← hC]
    exact Eq.symm sUnion_eq_iUnion
  have hUOpen : ∀ i, IsOpen (U i) := by exact fun i => hCOpen (U i) i.property
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : ParacompactSpace X := by exact paracompact_of_locallyCompact_sigmaCompact

  obtain ⟨β, V, hVOpen, hVCover, hVLocallyFinite, hRefinement⟩ :=
    ParacompactSpace.locallyFinite_refinement ι₀ U hUOpen hUCover
  /- Note that this refinement of the open cover U may not be what we want:
     it's locally finite, but its elements are only homeomorphic to subsets
     of ℝ (i.e., to subsets of the elements of U) rather than to ℝ itself. -/

  obtain ⟨compVb, hcompVb⟩ := Classical.axiom_of_choice
      <| fun b => disjoint_union_of_opens (hVOpen b)
  let bSets := fun (b : β) => {compVb b c | c}
  let ι := Σ b : β, ConnectedComponents (V b)
  let W : ι → Set X := fun ⟨b, c⟩ => compVb b c
  have hWV (i : ι) : W i ⊆ V i.fst := by
    rw [← (hcompVb i.fst).2.2.2]
    exact subset_iUnion_of_subset i.snd fun _ t => t

  have hWOpen : ∀ i : ι, IsOpen (W i) := fun i => (hcompVb i.fst).1 i.snd
  have hWConn : ∀ i : ι, IsConnected (W i) := fun i => (hcompVb i.fst).2.1 i.snd
  have hWCover : ⋃ i, W i = @univ X := by
    ext x
    constructor <;> intro hx
    · exact mem_univ x
    · have : x ∈ ⋃ b, V b := by rwa [hVCover]
      obtain ⟨b, hb⟩ := mem_iUnion.mp this
      obtain ⟨c, hc⟩ := mem_iUnion.mp (by rwa [← (hcompVb b).2.2.2] at hb)
      apply mem_iUnion.mpr
      use ⟨b, c⟩
  have hWRefine : ∀ i : ι, ∃ t ∈ C, W i ⊆ t := by
    intro i
    obtain ⟨a, ha⟩ := hRefinement i.fst
    exact ⟨U a, Subtype.coe_prop a, fun x hx => mem_of_subset_of_mem ha (hWV i hx)⟩
  have hW_point_finite : ∀ x : X, {i | x ∈ W i}.Finite := by
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

  let C' : Set (Set X) := {W i | i : ι}
  have hC'Prop {p : Set X → Prop} : (∀ i : ι, p (W i)) → (∀ Ω ∈ C', p Ω) := by
    intro hWp _ hΩ
    obtain ⟨i, hi⟩ := mem_range.mp hΩ
    rw [← hi]
    exact hWp i
  have hC'Finite : ∀ x : X, {s ∈ C' | x ∈ s}.Finite := by
    intro x
    let f : {i | x ∈ W i} → {s ∈ C' | x ∈ s} :=
      fun i => ⟨W i, mem_setOf.mpr ⟨(by use i), i.property⟩⟩
    have hf : Surjective f := by
      intro s
      obtain ⟨hsc, hx⟩ := s.property
      obtain ⟨i, hi⟩ := mem_range.mp hsc
      use ⟨i, by rwa [← hi] at hx⟩
      exact SetCoe.ext hi
    haveI : Finite {i | x ∈ W i} := finite_coe_iff.mpr (hW_point_finite x)
    exact finite_coe_iff.mp <| Finite.of_surjective f hf
  have hC'Cover : ⋃₀ C' = univ := eq_univ_of_subset (fun _ t ↦ t) hWCover
  exact ⟨C', hC'Prop hWOpen, hC'Cover, hC'Prop hWConn, hC'Finite, hC'Prop hWRefine⟩

/- Any open covering of a locally compact, locally connected, Hausdorff, second
   countable space admits a refinement to a covering by connected open sets
   with no proper subcover. -/
lemma minimal_connected_refinement
    [LocallyCompactSpace X] [LocallyConnectedSpace X] [T2Space X]
    {C₀ : Set (Set X)} (hC₀Open : ∀ s ∈ C₀, IsOpen s) (hC₀ : ⋃₀ C₀ = univ) :
    ∃ (C : Set (Set X)), (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧ (∀ s ∈ C, IsConnected s) ∧
    (∀ C' ⊂ C, ⋃₀ C' ≠ univ) ∧ (∀ s ∈ C, ∃ t ∈ C₀, s ⊆ t) := by

  let PLFCover := fun (C : Set (Set X)) =>
    (∀ s ∈ C, IsOpen s) ∧ (⋃₀ C = univ) ∧ (∀ x : X, {s ∈ C | x ∈ s}.Finite) ∧
    (∀ s ∈ C, IsConnected s)

  obtain ⟨C₁, hC₁Open, hC₁Cover, hC₁Conn, hC₁Finite, hC₁Refinement⟩ :=
    pointFinite_connected_refinement_of_cover hC₀ hC₀Open
  have hPC₁ : PLFCover C₁ := ⟨hC₁Open, hC₁Cover, hC₁Finite, hC₁Conn⟩
  let S := {C : Set (Set X) | PLFCover C}
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

  obtain ⟨m, hmC₀, hmMinimal⟩ := zorn_superset_nonempty _ hLB C₁ hPC₁
  have : PLFCover m := hmMinimal.prop
  unfold PLFCover at this
  obtain ⟨hmOpen, hmCover, hmFinite, hmConn⟩ := hmMinimal.prop
  have hmRefinement : ∀ s ∈ m, ∃ t ∈ C₀, s ⊆ t := by
    exact fun s hs => hC₁Refinement s (hmC₀ hs)

  have hssubset {s : Set (Set X)} : s ⊂ m → ⋃₀ s ≠ univ := by
    intro hsm
    have hNotCover : ¬ PLFCover s := MinimalFor.not_prop_of_lt hmMinimal hsm
    have hopen : ∀ Ω ∈ s, IsOpen Ω :=
      fun Ω hΩ => hmOpen Ω <| mem_of_subset_of_mem (subset_of_ssubset hsm) hΩ
    have hconn : ∀ Ω ∈ s, IsConnected Ω :=
      fun Ω hΩ => hmConn Ω <| mem_of_subset_of_mem (subset_of_ssubset hsm) hΩ
    have hfin: ∀ x : X, {Ω | Ω ∈ s ∧ x ∈ Ω}.Finite := by
      apply fun x => Finite.subset (hmFinite x) ?_
      exact fun _ ht => ⟨mem_of_subset_of_mem (subset_of_ssubset hsm) ht.1, ht.2⟩
    by_contra hCover
    exact hNotCover ⟨hopen, hCover, hfin, hconn⟩

  use m

/- If a minimal open cover of X is infinite, then X is not compact. -/
omit [SecondCountableTopology X] in
lemma notCompact_of_infinite_minimal_cover
    {C : Set (Set X)} (hC : ⋃₀ C = univ) (hInfinite : Infinite C)
    (hOpen : ∀ s ∈ C, IsOpen s) (hMinimal : ∀ C' ⊂ C, ⋃₀ C' ≠ univ) :
    ¬ CompactSpace X := by
  by_contra hCompact
  let ι := {U // U ∈ C}
  let U : ι → Set X := fun U => U.val
  have hCover : univ ⊆ ⋃ i, U i := by
    rw [← hC]
    exact sUnion_subset <| fun t ht => subset_iUnion U ⟨t, ht⟩
  obtain ⟨t, ht⟩ := hCompact.isCompact_univ.elim_finite_subcover
                    U (fun i => hOpen (U i) i.property) hCover
  let C' : Set (Set X) := {Subtype.val U | U ∈ t}
  have hFin' : C'.Finite := Finite.of_surjOn Subtype.val (fun _ a ↦ a) (finite_mem_finset t)
  have hC' : ⋃₀ C' = univ := by
    apply univ_subset_iff.mp <| subset_trans ht <| iUnion_subset ?_
    simp only [iUnion_subset_iff]
    intro Ω hΩ
    apply subset_sUnion_of_subset C' (U Ω) (Subset.refl (U Ω)) <| mem_setOf.mpr ?_
    use Ω
  have hSub : C' ⊆ C := by
    intro _ hs
    obtain ⟨U, _, hUs⟩ := mem_setOf.mp hs
    exact mem_of_eq_of_mem (Eq.symm hUs) (Subtype.coe_prop U)
  have hSsub : C' ⊂ C := by
    refine (ssubset_iff_of_subset hSub).mpr ?_
    by_contra! h
    have : Finite C := finite_coe_iff.mpr <| Finite.subset hFin' <| subset_setOf.mpr h
    exact not_finite C
  exact (hMinimal C' hSsub) hC'

/- If a cover of X has no proper subcover, then every set U in the cover
   contains some point that is in U but not in any other set in the cover. -/
lemma minimal_cover_choose_points {X : Type*} {C : Set (Set X)} (hC : ⋃₀ C = univ) :
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
lemma countable_of_minimal_open_cover {C : Set (Set X)} (hC : ⋃₀ C = univ)
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

/- Given an infinite open cover C of a connected space, and a finite subset
   s ⊆ U whose union is preconnected, there is another set U ∈ C \ s whose
   union with ⋃₀ s is connected. -/
omit [SecondCountableTopology X] in
lemma exists_open_intersecting_finite_union [ConnectedSpace X]
    {C : Set (Set X)} (hC : ⋃₀ C = univ) (hInf : Infinite C) (hOpen : ∀ U ∈ C, IsOpen U)
    {s : Set (Set X)} (hFin : Finite s) (hsub : s ⊆ C) (hs : IsConnected (⋃₀ s))
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

/- A function f : ℕ → ℕ that is bounded above cannot be injective. -/
lemma notInjective_of_eventually_bounded {f : ℕ → ℕ} {a b : ℕ} :
    (∀ n > a, f n ≤ b) → ¬ Injective f := by
  intro hfBound
  have hFin : (f '' {k | k > a}).Finite := by
    apply Finite.subset (finite_le_nat b)
    intro l ⟨k, hk, hjk⟩
    rw [← hjk]
    exact hfBound k (mem_setOf.mp hk)
  have hInf : {k | k > a}.Infinite := by
    apply infinite_iff_exists_gt.mpr
    exact fun i => ⟨i + a + 1, Nat.le_add_left (a + 1) i,
      lt_of_le_of_lt (Nat.le_add_right i a) (lt_add_one (i + a))⟩
  have hNotInjOn := Set.not_injOn_infinite_finite_image hInf hFin
  unfold InjOn at hNotInjOn
  push Not at hNotInjOn
  obtain ⟨x, hx, y, hy, hjxy, hxy⟩ := hNotInjOn
  exact not_injective_iff.mpr ⟨x, y, hjxy, hxy⟩

/- Given an infinite minimal cover of a connected, second countable space
   X by connected open sets, and given a set U in the cover, we can find an
   enumeration f : ℕ ≃ C of the cover such that for each n > 0 the union of
   the first n sets is connected. -/
lemma connected_enumeration_of_minimal_open_cover [ConnectedSpace X]
    {C : Set (Set X)} (hC : ⋃₀ C = univ) (hInf : Infinite C) (hOpen : ∀ U ∈ C, IsOpen U)
    (hConn : ∀ U ∈ C, IsConnected U) (hMinimal : ∀ C' ⊂ C, ⋃₀ C' ≠ univ) :
    ∃ f : ℕ ≃ C, ∀ n, IsConnected ((⋃ j ≤ n, f j) : Set X) := by
  classical -- need to know DecidablePred
  have hCountable : Countable C := countable_of_minimal_open_cover hC hOpen hMinimal
  let U : ℕ ≃ C := (nonempty_denumerable_iff.mpr ⟨hCountable, hInf⟩).some.eqv.symm

  /- Every nonempty, finite subset of C with connected sUnion can be enlarged to
     another such subset by adding one element of C -/
  let Csub : Set (Set ℕ) := {S | Nonempty S ∧ Finite S ∧ IsConnected (⋃ i ∈ S, (U i) : Set X)}
  have hU₀ : {0} ∈ Csub := by
    refine ⟨instNonemptyOfInhabited, Finite.of_subsingleton, ?_⟩
    simp_all only [ne_eq, mem_singleton_iff, iUnion_iUnion_eq_left, Subtype.coe_prop]
  have extend_Csub : ∀ S : Csub, ∃ n : ℕ, n ∉ S.val ∧ {n} ∪ S.val ∈ Csub := by
    intro ⟨S, hS⟩
    obtain ⟨hSNE, hSFinite, hSConn⟩ := mem_setOf.mp hS
    let Ω : Set (Set X) := (fun i => ↑(U i)) '' S
    have hΩFin : Finite Ω := by apply Finite.Set.finite_image
    have hΩC : Ω ⊆ C := fun _ ⟨n, _, hnω⟩ => by simp_rw [← hnω, Subtype.coe_prop]
    have hΩConn : IsConnected (⋃₀ Ω) := by
      simp only [Ω, sUnion_image]
      exact hSConn
    obtain ⟨V, hVCS, hVConn⟩ := exists_open_intersecting_finite_union
      hC hInf hOpen hΩFin hΩC hΩConn hConn
    let n := U.symm ⟨V, mem_of_mem_inter_left hVCS⟩
    have hUn : ↑(U n) = V := by simp only [Equiv.symm_symm, Equiv.symm_apply_apply, U, n]
    have hnS : n ∉ S := by
      by_contra h
      have : V ∈ Ω := by
        simp_rw [← hUn, Ω, mem_image]
        use n
      exact (notMem_of_mem_diff hVCS) this
    have hVS : {n} ∪ S ∈ Csub := by
      refine ⟨?_, ?_, ?_⟩
      · exact Nonempty.intro <| codRestrict (fun x ↦ n) ({n} ∪ S) (fun x ↦ mem_union_left S rfl) X
      · exact Finite.Set.finite_union {n} S
      · simp only [singleton_union, mem_insert_iff, iUnion_iUnion_eq_or_left, hUn]
        simpa only [Ω, sUnion_image] using hVConn
    use n
  /- Given any S ∈ Csub, g S is the smallest n ∉ S so that {n} ∪ S is also in Csub -/
  let g : Csub → ℕ := fun S => Nat.find (extend_Csub S)
  have hg_notMem : ∀ S : Csub, g S ∉ S.val := fun S => (Nat.find_spec (extend_Csub S)).1
  have hg_extend : ∀ S : Csub, {g S} ∪ S.val ∈ Csub := fun S => (Nat.find_spec (extend_Csub S)).2
  have hg_min : ∀ S : Csub, ∀ m : ℕ, m < g S →
      (m ∈ S.val ∨ ¬ IsConnected (⋃ i ∈ {m} ∪ S.val, (U i) : Set X)) := by
    intro S m hm_lt
    have hm_options : m ∈ S.val ∨ {m} ∪ ↑S ∉ Csub := by
      have := Nat.find_min (extend_Csub S) hm_lt
      push Not at this
      have := imp_iff_not_or.mp this
      simpa only [not_not] using this
    apply Or.imp_right ?_ hm_options
    intro hmsC
    have hNotCsub := notMem_setOf_iff.mp hmsC
    push Not at hNotCsub
    have hmS_NE : Nonempty ↑({m} ∪ S.val) := by
      exact Nonempty.intro ⟨m, mem_union_left S.val <| mem_singleton m⟩
    have hmS_Fin : Finite ↑({m} ∪ S.val) := by
      refine finite_union.mpr ⟨finite_singleton m, ?_⟩
      exact (mem_setOf.mp <| Subtype.coe_prop S).2.1
    exact hNotCsub hmS_NE hmS_Fin
  let gSet : Csub → Csub := fun S => ⟨{g S} ∪ S.val, hg_extend S⟩
  /- Now we iterate this action n times, starting with {U₀}, to get a sequence
     i : ℕ → Csub so that each i n is built by adding a single element j n
     of the cover C to i (n - 1) -/
  let i : ℕ → Csub := fun n => Nat.iterate gSet n ⟨{0}, hU₀⟩
  have hg_iterate : ∀ n : ℕ, i (n + 1) = gSet (i n) := by
    exact fun n => iterate_succ_apply' gSet n ⟨{0}, hU₀⟩
  have hiConn (n : ℕ) : IsConnected (⋃ s ∈ (i n).val, U s : Set X) := by
    obtain ⟨_, _, hC⟩ := mem_setOf.mp <| Subtype.coe_prop (i n)
    exact hC
  let j : ℕ → ℕ := fun n => if n = 0 then 0 else g (i (n - 1))
  have hi_diff_eq_j : ∀ n : ℕ, (i (n + 1)).val \ (i n).val = {j (n + 1)} := by
    intro n
    simp_rw [hg_iterate n, gSet, singleton_union, j]
    exact insert_diff_eq_singleton <| hg_notMem (i n)
  have hj_mem_i : ∀ n : ℕ, j n ∈ (i n).val := by
    intro n
    by_cases h : n = 0 <;> simp only [j, h, ↓reduceIte]
    · rfl
    · nth_rewrite 1 [← show (n - 1) + 1 = n by exact Nat.succ_pred h]
      rw [hg_iterate (n - 1)]
      exact mem_union_left _ <| mem_singleton _
  have hj_notMem_i_pred {n : ℕ} : n ≠ 0 → j n ∉ (i (n - 1)).val := by
    intro hn
    apply notMem_of_mem_diff (s := (i n).val)
    have h1 : n - 1 + 1 = n := Nat.succ_pred hn
    nth_rewrite 1 [← h1, hi_diff_eq_j (n - 1), h1]
    exact mem_singleton (j n)
  have hi_eq_image_j (n : ℕ) : (i n).val = j '' {k | k ≤ n} := by
    induction n with
    | zero => simp only [nonpos_iff_eq_zero, setOf_eq_eq_singleton, image_singleton,
                         i, j, iterate_zero, id_eq, ↓reduceIte]
    | succ n hn =>
        have : {k | k ≤ n + 1} = {k | k ≤ n} ∪ {n + 1} := by
          apply Subset.antisymm
          · intro k hk
            simp only [mem_union, mem_setOf, mem_singleton_iff]
            exact Nat.le_succ_iff.mp <| mem_setOf.mp hk
          · apply union_subset <;> intro k hk <;> apply mem_setOf.mpr
            · exact Nat.le_add_right_of_le hk
            · exact Nat.le_of_eq hk
        simp_rw [hg_iterate n, gSet, this, image_union, ← hn]
        nth_rewrite 1 [union_comm]
        apply Subset.antisymm <;> refine union_subset subset_union_left ?_
          <;> apply subset_union_of_subset_right <;> simp [j]

  have hi_ssubset : ∀ n : ℕ, (i n).val ⊂ (i (n + 1)).val := by
    intro n
    rw [hg_iterate n]
    refine (ssubset_iff_of_subset subset_union_right).mpr ?_
    refine ⟨j (n + 1), ?_, (mem_compl_iff (↑(i n)) (j (n + 1))).mp (hg_notMem (i n))⟩
    simp only [singleton_union, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      add_tsub_cancel_right, mem_insert_iff, true_or, j]
  have hi_ssubset' : ∀ m n : ℕ, m < n → (i m).val ⊂ (i n).val := by
    let r : ℕ → ℕ → Prop := fun m n => ↑(i m).val ⊂ ↑(i n).val
    have : IsTrans ℕ r := { trans _ _ _ := ssubset_trans }
    exact fun m n hmn => Nat.rel_of_forall_rel_succ_of_lt r hi_ssubset hmn
  have hi_subset_of_lt {m n : ℕ} : m < n → (i m).val ⊆ (i (n - 1)).val := by
    intro h
    rcases (Nat.eq_or_lt_of_le <| Nat.le_sub_one_of_lt h) with heq | hlt
    · rw [heq]
    · exact subset_of_ssubset <| hi_ssubset' m (n - 1) hlt
  -- Need to prove : j is bijective
  have hjInjective : Injective j := by
    intro m n hjmn
    rcases Nat.lt_trichotomy m n with h | h | h
    · apply False.elim <| (hj_notMem_i_pred <| Nat.ne_zero_of_lt h) ?_
      rw [← hjmn]
      exact mem_of_subset_of_mem (hi_subset_of_lt h) (hj_mem_i m)
    · exact h
    · apply False.elim <| (hj_notMem_i_pred <| Nat.ne_zero_of_lt h) ?_
      rw [hjmn]
      exact mem_of_subset_of_mem (hi_subset_of_lt h) (hj_mem_i n)
  have hjSurjective : Surjective j := by
    by_contra! h
    let C' : Set (Set X) := Subtype.val '' (U '' (range j))
    have hC'_ssubset_C : C' ⊂ C := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k ∉ range j := by
        by_contra! hh
        exact h hh
      apply HasSubset.Subset.ssubset_of_mem_notMem
      · exact Subtype.coe_image_subset C (⇑U '' range j)
      · exact Subtype.coe_prop (U k)
      · by_contra hh
        have : U k ∈ U '' (range j) := by
          obtain ⟨_, _, haVal⟩ := hh
          rwa [← SetCoe.ext haVal]
        exact (Iff.not U.injective.mem_set_image).mpr hk this
    have hC'_sUnion_proper : ⋃₀ C' ≠ univ := hMinimal C' hC'_ssubset_C
    have hC'_sUnion_open : IsOpen (⋃₀ C') := by
      apply isOpen_sUnion
      intro t ⟨⟨s, hsC⟩, _, hst⟩
      rw [← hst]
      exact hOpen s hsC
    have hFrontier : (frontier (⋃₀ C')).Nonempty := by
      apply nonempty_frontier_iff.mpr ⟨?_, hC'_sUnion_proper⟩
      apply nonempty_sUnion.mpr
      use (U (j 0)).val
      constructor
      · apply mem_image_of_mem Subtype.val
        apply mem_image_of_mem U
        exact mem_range_self 0
      · exact (hConn (U (j 0)) <| Subtype.coe_prop (U (j 0))).nonempty
    /- Since ⋃₀ C' has nonempty frontier, we can take a point x in that
       frontier and find a set Ω = U n ∈ C containing it; note that Ω ∉ C' -/
    obtain ⟨x, hx⟩ := nonempty_def.mp hFrontier
    obtain ⟨Ω, hΩ, hxΩ⟩ : ∃ Ω ∈ C, x ∈ Ω := by
      apply mem_sUnion.mp
      rw [hC]
      exact mem_univ x
    let n : ℕ := U.symm ⟨Ω, hΩ⟩
    have hUn : (U n).val = Ω := by simp only [n, U.apply_symm_apply]
    have hnj : n ∉ range j := by
      by_contra h
      obtain ⟨a, ha⟩ := mem_range.mp h
      have hΩC' : Ω ∈ C' := by
        rw [← hUn, ← ha]
        apply mem_image_of_mem Subtype.val
        apply mem_image_of_mem U
        exact mem_range_self a
      have hxMem : x ∈ ⋃₀ C' := subset_sUnion_of_subset C' Ω (Subset.refl Ω) hΩC' hxΩ
      have hx_notMem : x ∉ ⋃₀ C' := by
        rw [hC'_sUnion_open.frontier_eq] at hx
        exact notMem_of_mem_diff hx
      exact hx_notMem hxMem
    /- Now we find a set t = U (j μ) in C' that intersects Ω = U n -/
    have hΩC' : (Ω ∩ (⋃₀ C')).Nonempty := mem_closure_iff.mp
      (mem_of_mem_inter_left hx) Ω (hOpen Ω hΩ) hxΩ
    obtain ⟨y, hyΩ, hyC⟩ := nonempty_def.mp hΩC'
    obtain ⟨t, ht', hyt⟩ := mem_sUnion.mp hyC
    have ht : t ∈ C := mem_of_subset_of_mem (subset_of_ssubset hC'_ssubset_C) ht'
    let m : ℕ := U.symm ⟨t, ht⟩
    have hUm : (U m).val = t := by simp only [m, U.apply_symm_apply]
    obtain ⟨μ, hμ⟩ : ∃ μ, j μ = m := by
      apply mem_range.mpr
      obtain ⟨k, ⟨a, haj, hUak⟩, hkt⟩ := mem_setOf.mp ht'
      apply mem_of_eq_of_mem ?_ haj
      subst k
      have : U a = ⟨t, ht⟩ := SetCoe.ext hkt
      rw [← U.symm_apply_apply a, congrArg U.symm this]
    have hΩConn : ∀ k ≥ μ, IsConnected (Ω ∪ (⋃ s ∈ (i k).val, (U s).val)) := by
      intro k hk
      refine IsConnected.union ⟨y, hyΩ, ?_⟩ (hConn Ω hΩ) (hiConn k)
      simp only [mem_iUnion, exists_prop]
      refine ⟨j μ, ?_, by rwa [hμ, hUm]⟩
      rw [hi_eq_image_j k]
      exact mem_image_of_mem j <| mem_setOf.mpr hk
    /- Now for every k ≥ μ we construct i (k + 1) by inserting j (k + 1)
       into i k, but we never insert n = U.symm Ω, so it must be the case
       that j (k + 1) < n for all k ≥ μ. -/
    have hjBound : ∀ k > μ, j k ≤ n := by
      intro k hk
      simp only [j, Nat.ne_zero_of_lt hk, ↓reduceIte]
      by_contra hg
      replace hg : g (i (k - 1)) > n := by exact Nat.lt_of_not_le hg
      have hg_min' := hg_min (i (k - 1)) n hg
      have : n ∉ (i (k - 1)).val := by
        by_contra h
        rw [hi_eq_image_j (k - 1)] at h
        obtain ⟨l, _, hjl⟩ := h
        rw [← hjl] at hnj
        exact hnj (mem_range_self l)
      simp only [this, false_or, singleton_union, mem_insert_iff,
        iUnion_iUnion_eq_or_left, hUn] at hg_min'
      exact hg_min' <| hΩConn (k - 1) (Nat.le_sub_one_of_lt hk)
    /- If j : ℕ → ℕ is bounded above then it can't be injective, contradiction. -/
    exact (notInjective_of_eventually_bounded hjBound) hjInjective
  use (Equiv.ofBijective j ⟨hjInjective, hjSurjective⟩).trans U
  intro n
  simp only [Equiv.trans_apply, Equiv.ofBijective_apply]
  have : IsConnected (⋃ s ∈ (i n).val, (U s).val) := hiConn n
  rw [hi_eq_image_j n] at this
  simpa only [mem_image, mem_setOf_eq, iUnion_exists, biUnion_and',
    iUnion_iUnion_eq_right] using this
