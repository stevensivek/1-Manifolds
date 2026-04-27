import Mathlib.Tactic
import «OneManifold».RealCover
import «OneManifold».TwoCharts

/-!
The main result of this file is `real_or_circle_of_finitely_covered_one_manifold`,
which asserts that if a connected 1-manifold (Hausdorff, covered by charts to ℝ¹)
is covered by finitely many open sets homeomorphic to ℝ, then the manifold must be
homeomorphic to either ℝ or a circle.
-/

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

open Set Topology
set_option linter.style.emptyLine false

/- M is a connected Hausdorff space. -/
variable (M : Type*) [TopologicalSpace M] [ConnectedSpace M] [T2Space M]

/- If M contains an open set homeomorphic to a circle, then M is a circle. -/
lemma contains_open_circle {U : Set M} (hU : IsOpen U) (φ : U ≃ₜ Circle) :
    Nonempty (M ≃ₜ Circle) := by
  have hClosed : IsClosed U := by exact
    IsCompact.isClosed <| isCompact_iff_compactSpace.mpr φ.symm.compactSpace
  have h := by exact isClopen_iff.mp ⟨hClosed, hU⟩
  have : Nonempty U := by exact Nonempty.intro (φ.symm One.instNonempty.some)
  simp_all only [nonempty_iff_ne_empty', false_or]
  have : U ≃ₜ M := by
    rw [h]
    exact Homeomorph.Set.univ M
  exact Nonempty.intro (this.symm.trans φ)

/- If M has two overlapping open sets homeomorphic to ℝ, and their union is
   not homeomorphic to ℝ, then M must be a circle. -/
lemma circle_union {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hOverlap : Nonempty (U ∩ V : Set M)) (φ : U ≃ₜ ℝ) (ψ : V ≃ₜ ℝ)
    (hNotR : IsEmpty ((U ∪ V : Set M) ≃ₜ ℝ)) : Nonempty (M ≃ₜ Circle) := by
  obtain h := union_of_two_real_lines hU hV hOverlap (Nonempty.intro φ) (Nonempty.intro ψ)
  have : ¬ Nonempty ({x : M // x ∈ U ∪ V} ≃ₜ ℝ) := not_nonempty_iff.mpr hNotR
  simp_all only [nonempty_subtype, mem_inter_iff, false_or]
  exact contains_open_circle M (IsOpen.union hU hV) h.some

/- A space cannot be homeomorphic to both ℝ and a circle. -/
lemma not_homeomorph_real_homeomorph_circle (X : Type*) [TopologicalSpace X] :
    ¬ ((Nonempty (X ≃ₜ ℝ)) ∧ (Nonempty (X ≃ₜ Circle))) := by
  intro ⟨hR,hS⟩
  let φ : Circle ≃ₜ ℝ := hS.some.symm.trans hR.some
  exact (not_compactSpace_iff.mpr instNoncompactSpaceReal) φ.compactSpace

/- If M is covered by finitely many open sets homeomorphic to ℝ, then M is
   homeomorphic to either ℝ or a circle. -/
theorem real_or_circle_of_finitely_covered_one_manifold [ChartedSpace ℝ¹ M]
    {ι : Type*} (U : ι → Set M)
    (hUOpen : ∀ i, IsOpen (U i) ∧ Nonempty ((U i) ≃ₜ ℝ))
    (hFiniteCover : ∃ t : Finset ι, univ ⊆ ⋃ i ∈ t, U i) :
    Xor' (Nonempty (M ≃ₜ ℝ)) (Nonempty (M ≃ₜ Circle)) := by
  -- Reduce the theorem statement from Xor' to or
  apply (xor_iff_or_and_not_and (Nonempty (M ≃ₜ ℝ)) (Nonempty (M ≃ₜ Circle))).mpr
  simp only [not_homeomorph_real_homeomorph_circle M, not_false_eq_true, and_true]

  classical
  -- There is a minimal cover of M by open sets homeomorphic to ℝ
  let PCover := fun (s : Finset ι) (V : ι → Set M) =>
    (∀ i, (IsOpen (V i) ∧ Nonempty (V i ≃ₜ ℝ))) ∧ (@univ M ⊆ ⋃ i ∈ s, V i)
  obtain ⟨t, U, hUPCover, htMin⟩ : ∃ (s : Finset ι), ∃ V : ι → Set M, PCover s V ∧
      (∀ (s' : Finset ι), ∀ V' : ι → Set M, s'.card < s.card → ¬ PCover s' V') := by
    have hPexists : ∃ n, ∃ s, ∃ V, s.card = n ∧ PCover s V := by
      obtain ⟨t, htCover⟩ := hFiniteCover
      use t.card, t, U
    let n := Nat.find hPexists
    obtain ⟨s, V, hs_card, hsPCover⟩ := Nat.find_spec hPexists
    use s, V
    constructor
    · exact hsPCover
    · intro s' V' hcard
      rw [hs_card] at hcard
      have hNoSmallerPCover := Nat.find_min hPexists hcard
      push Not at hNoSmallerPCover
      exact hNoSmallerPCover s' V' rfl

  -- If the minimal cover has one set then M is homeomorphic to that set
  have ht_at_most_one : t.card < 2 → Nonempty (M ≃ₜ ℝ) := by
    intro htCard2
    have htCard1 : t.card = 1 := by
      apply Nat.eq_of_le_of_lt_succ ?_ htCard2
      apply Finset.card_pos.mpr <| Finset.nonempty_coe_sort.mp ?_
      obtain ⟨x, hx⟩ := exists_mem_of_nonempty M
      have hx_cover : x ∈ ⋃ i ∈ t, U i := hUPCover.right hx
      obtain ⟨i, _, ⟨hit, _⟩, _⟩ := by rwa [mem_iUnion] at hx_cover
      exact Nonempty.intro ⟨i, hit⟩
    obtain ⟨i, hi, hiUniv⟩ : ∃ i ∈ t, univ ⊆ U i := by
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp htCard1
      subst hi
      use i
      constructor
      · exact Finset.mem_singleton.mpr rfl
      · intro y hy
        obtain ⟨z, hz⟩ := mem_iUnion.mp <| hUPCover.right hy
        simp only [Finset.mem_singleton, mem_iUnion, exists_prop] at hz
        obtain ⟨hzi, hyUz⟩ := hz
        rwa [hzi] at hyUz
    have hi' : Nonempty (U i ≃ₜ ℝ) := (hUPCover.left i).2
    let φ₁ : M ≃ₜ (@univ M) := (Homeomorph.Set.univ M).symm
    let φ₂ : (@univ M) ≃ₜ U i := by
      rw [eq_univ_of_univ_subset hiUniv]
      exact Homeomorph.refl univ
    exact Nonempty.intro <| φ₁.trans (φ₂.trans hi'.some)

  have ht_at_least_two : t.card ≥ 2 → Nonempty (M ≃ₜ Circle) := by
    intro ht
    obtain ⟨hUOpenR, hUCover⟩ := hUPCover
    have hUNonempty (i : ι) : (U i).Nonempty := by
      haveI : Nonempty (U i) := Nonempty.intro <| (hUOpenR i).2.some.symm 0
      exact Nonempty.of_subtype

    -- Pick an open set `U a` in the cover
    have htNE : t.Nonempty := Finset.card_pos.mp <| Nat.zero_lt_of_lt ht
    obtain ⟨a₀, ha₀⟩ := htNE.exists_mem
    let a : t := ⟨a₀, ha₀⟩

    -- Consider the sets in the finite cover other than `U a`
    let t' : Finset ι := t.erase a
    have ht'NE : t'.Nonempty := by
      apply Finset.card_pos.mp
      exact le_of_le_of_eq (Nat.sub_le_sub_right ht 1)
            <| Eq.symm <| Finset.card_erase_of_mem <| Finset.coe_mem a

    -- `U a` and the sets indexed by t' cover M
    have hUVCover : univ = (U a) ∪ (⋃ j ∈ t', U j) := by
      apply Eq.symm <| eq_univ_of_univ_subset ?_
      intro x _
      by_cases hxa : x ∈ U a
      · exact mem_union_left (⋃ j ∈ t', U j) hxa
      · apply mem_union_right (U a)
        apply mem_iUnion.mpr
        obtain ⟨j, Uj, ⟨⟨hjt, hij⟩, hxUj⟩⟩ := mem_iUnion.mp <| hUCover (mem_univ x)
        simp only at hij
        use j
        refine mem_iUnion_of_mem ?_ (by rwa [hij])
        by_contra hjt'
        have : j = a := by
          apply Finset.mem_singleton.mp
          rw [← Finset.sdiff_erase_self ha₀]
          exact Finset.mem_sdiff.mpr ⟨hjt, hjt'⟩
        subst Uj j
        exact hxa hxUj

    -- Find an index b ∈ t' such that `U a` intersects `U b`
    obtain ⟨b, hab, hUaUb⟩ : ∃ b : t, a ≠ b ∧ Nonempty (U a ∩ U b : Set M) := by
      let V₀ : Set M := ⋃ j ∈ t', U j
      have hV₀Open : IsOpen V₀ := by
        apply isOpen_iUnion
        exact fun j => isOpen_iUnion <| fun _ ↦ (hUOpenR j).1
      have : V₀.Nonempty := by
        apply nonempty_iUnion.mpr
        obtain ⟨j₀, hj₀⟩ := ht'NE.exists_mem
        use j₀
        apply nonempty_coe_sort.mp ?_
        simp only [nonempty_subtype, mem_iUnion, exists_prop, exists_and_left]
        exact ⟨hj₀, hUNonempty j₀⟩
      have hUV₀UnionUniv : (U a) ∪ V₀ = univ := by rw [← hUVCover]

      obtain ⟨y,hy⟩ := nonempty_inter (hUOpenR a).1 hV₀Open hUV₀UnionUniv (hUNonempty a) this
      obtain ⟨hyU, hyV⟩ := (mem_inter_iff y (U a) V₀).mp hy
      obtain ⟨j₀, hj₀⟩ := mem_iUnion.mp hyV
      obtain ⟨hj₀t', hyUj₀⟩ := by simpa only [mem_iUnion, exists_prop] using hj₀
      use ⟨j₀, Finset.mem_of_mem_erase hj₀t'⟩
      constructor
      · apply Subtype.coe_ne_coe.mp
        exact Ne.symm <| ne_of_mem_of_not_mem hj₀t' (t.notMem_erase ↑a)
      · apply nonempty_subtype.mpr
        use y
        exact ⟨hyU, hyUj₀⟩

    -- Since `U a` and `U b` overlap and are homeomorphic to ℝ, their union
    -- must be homeomorphic to either ℝ or a circle.
    let C : Set M := U a ∪ U b
    have hCOpen : IsOpen C := by
      exact IsOpen.union (hUOpenR a).1 (hUOpenR b).1
    have hC : Nonempty (C ≃ₜ ℝ) ∨ Nonempty (C ≃ₜ Circle) :=
      union_of_two_real_lines (hUOpenR a).1 (hUOpenR b).1 hUaUb (hUOpenR a).2 (hUOpenR b).2

    -- If their union is a circle, then we're done.
    rcases (or_comm.mp hC) with (hCCircle | hCReal)
    · exact contains_open_circle M hCOpen hCCircle.some

    -- From now on, we must have (U a) ∪ (U b) ≃ₜ ℝ.  We use this to construct
    -- a cover V indexed by t', equal to U except for V b = (U a) ∪ (U b)
    let V : ι → Set M := fun j ↦ if j = b then (U a) ∪ (U b) else U j
    have hVb : V b = (U a) ∪ (U b) := by simp only [V, ↓reduceIte]
    have hVNotb {j : ι} : j ≠ b → V j = U j := by
      exact fun h ↦ by simp only [V, ite_eq_right_iff, h, false_implies]

    have hVOpenReal : ∀ j : ι, IsOpen (V j) ∧ Nonempty (V j ≃ₜ ℝ) := by
      intro j
      by_cases h : j = b
      · rw [h, hVb]
        exact ⟨hCOpen, hCReal⟩
      · rw [hVNotb h]
        exact hUOpenR j

    have hVCover : univ ⊆ ⋃ j ∈ t', V j := by
      rw [hUVCover]
      refine union_subset_iff.mpr ⟨?_, ?_⟩
      · have hUaVb : U a ⊆ V b := by
          rw [hVb]
          exact subset_union_left
        have hbt' : ↑b ∈ t' := by
          refine Finset.mem_erase.mpr ⟨Ne.symm (Ne.intro ?_), Finset.coe_mem b⟩
          simp only [SetLike.coe_eq_coe, hab, false_implies]
        exact subset_trans hUaVb <| subset_biUnion_of_mem hbt'
      · refine iUnion₂_mono ?_
        intro j _
        by_cases h : j = b
        · rw [h, hVb]
          exact subset_union_right
        · rw [hVNotb h]

    -- (V,t') is a smaller cover than the minimal (U,t), contradicting hιMin.
    have hPCoverV : PCover t' V := ⟨hVOpenReal, hVCover⟩
    exact False.elim <| (htMin t' V <| Finset.card_erase_lt_of_mem ha₀) hPCoverV

  by_cases htCard : t.card < 2
  · left
    exact ht_at_most_one htCard
  · right
    exact ht_at_least_two <| Nat.le_of_not_lt htCard

-- /- If a connected set Ω ⊆ M is the union of finitely many open sets
--    homeomorphic to ℝ, then either Ω is homeomorphic to ℝ or M is a circle. -/
-- theorem real_or_circle_of_finitely_covered_one_submanifold [ChartedSpace ℝ¹ M]
--     {ι : Type*} (U : ι → Set M) {Ω : Set M} {t : Finset ι}
--     (hUOpen : ∀ i ∈ t, IsOpen (U i) ∧ Nonempty ((U i) ≃ₜ ℝ))
--     (hSubset : ∀ i ∈ t, U i ⊆ Ω) (hUnion : ⋃ i ∈ t, U i = Ω)
--     (hConn : IsConnected Ω) :
--     (Nonempty (Ω ≃ₜ ℝ)) ∨ (Nonempty (M ≃ₜ Circle)) := by
--   let Ω' := {t // t ∈ Ω}
--   let ι' := {i // i ∈ t}
--   let U' : ι' → Set Ω := fun i => {x : Ω' | ↑x ∈ U i}
--   have hU'OpenReal : ∀ i, (IsOpen (U' i) ∧ Nonempty (U' i ≃ₜ ℝ)) := by
--     intro i
--     have hi := Subtype.coe_prop i
--     obtain ⟨hOpen, hReal⟩ := open_subtype_homeomorph (hUOpen i hi).1 (hSubset i hi)
--     exact ⟨hOpen, Nonempty.intro <| hReal.some.symm.trans (hUOpen i hi).2.some⟩
--   haveI : ConnectedSpace Ω' := isConnected_iff_connectedSpace.mp hConn
--   have φ : Ω ≃ₜ Ω' := by
--     sorry
--   have hΩOpen : IsOpen Ω := by
--     rw [← hUnion]
--     exact isOpen_biUnion <| fun i hi => (hUOpen i hi).1
--   haveI : ChartedSpace ℝ¹ Ω' := by
--     have : ChartedSpace ℝ¹ Ω := TopologicalSpace.Opens.instChartedSpace ⟨Ω, hΩOpen⟩
--     sorry
--   have ht' : ∃ t' : Finset ι', univ ⊆ ⋃ i ∈ t', U' i := by
--     use Finset.univ
--     intro x hx
--     have : x.val ∈ ⋃ i ∈ t, U i := by
--       rw [hUnion]
--       exact Subtype.coe_prop x
--     obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp this
--     apply mem_iUnion.mpr
--     use ⟨i, hit⟩
--     simp only [Finset.mem_univ, iUnion_true]
--     exact mem_setOf.mpr hxi
--   have := real_or_circle_of_finitely_covered_one_manifold Ω' U' hU'OpenReal ht'
--   rcases this.or with hReal | hCircle
--   · left; exact Nonempty.intro <| φ.trans hReal.some
--   · right; exact contains_open_circle M hΩOpen (φ.trans hCircle.some)
