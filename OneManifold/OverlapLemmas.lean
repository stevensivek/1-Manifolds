import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import «OneManifold».RealLemmas

open Set Function
set_option linter.style.emptyLine false

/- X is a Hausdorff space -/
variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
/- Given a homeomorphism from an open subset of X to ℝ, produce a partial homeomorphism
   from X to ℝ with source U and target univ. -/
lemma real_chart_to_partial_homeomorph {U : Set X} (hU : IsOpen U) (φ : U ≃ₜ ℝ) :
    ∃ ψ : OpenPartialHomeomorph X ℝ, ψ.source = U ∧ ψ.target = @univ ℝ := by
  let U' : TopologicalSpace.Opens X := TopologicalSpace.Opens.mk U hU
  let f := TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe U' <| Nonempty.intro (φ.symm 0)
  use f.symm.transHomeomorph φ
  rw [f.symm.transHomeomorph_source, f.symm.transHomeomorph_target, f.symm_source, f.symm_target,
      U'.openPartialHomeomorphSubtypeCoe_source, U'.openPartialHomeomorphSubtypeCoe_target,
      preimage_univ]
  simp only [and_true]
  rfl

lemma partial_homeomorph_IsConnected_source {Y : Type*} [TopologicalSpace Y]
    {φ : OpenPartialHomeomorph Y ℝ} (hφTarget : φ.target = univ) :
    IsConnected φ.source := by
  rw [← φ.symm_image_target_eq_source]
  refine IsConnected.image ?_ φ.symm φ.continuousOn_symm
  simp only [hφTarget, isConnected_univ]

/- Given φ : U ≃ₜ ℝ and ψ : V ≃ₜ ℝ, both presented as partial homeomorphisms
   from X to ℝ, if neither U ⊆ V nor V ⊆ U then each connected component of
   the image φ '' (U ∩ V) is a half-infinite interval. -/
lemma intersection_intervals {U V : Set X}
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    (hV : IsOpen V) (hVConn : IsConnected V)
    (hNotUV : ¬U ⊆ V) (hNotVU : ¬V ⊆ U) {x : ℝ} (hx : x ∈ φ '' (U ∩ V)) :
    (∃ a : ℝ, connectedComponentIn (φ '' (U ∩ V)) x = Iio a)
    ∨ (∃ a : ℝ, connectedComponentIn (φ '' (U ∩ V)) x = Ioi a) := by
  have hU : IsOpen U := hφSource ▸ φ.open_source
  have hUV : IsOpen (U ∩ V) := IsOpen.inter hU hV
  let I : Set ℝ := φ '' (U ∩ V)
  have hφInter_open : IsOpen I := by
    apply φ.isOpen_image_of_subset_source hUV
    exact hφSource ▸ inter_subset_left
  have hφInter_proper : I ≠ univ := by
    by_contra! hI
    rw [← hφTarget, ← φ.image_source_eq_target] at hI
    have hUVφ : U ∩ V ⊆ φ.source :=
      subset_of_subset_of_eq inter_subset_left (Eq.symm hφSource)
    obtain h := (InjOn.image_subset_image_iff φ.injOn (fun _ a ↦ a) hUVφ).mp
                <| Eq.subset (Eq.symm hI)
    rw [hφSource] at h
    exact hNotUV <| fun _ a ↦ inter_subset_right (h a)

  have hInterval : ∀ (t a b : ℝ), a < b → connectedComponentIn I t ≠ Ioo a b := by
    intro x a b hab
    by_contra hx

    by_cases hxI : x ∉ I
    · rw [connectedComponentIn_eq_empty hxI] at hx
      exact (Ioo_eq_empty_iff.mp (Eq.symm hx)) hab
    replace hxI : x ∈ I := not_notMem.mp hxI

    let S := φ.source ∩ φ ⁻¹' (Ioo a b)
    have hSOpen : IsOpen S := φ.isOpen_inter_preimage isOpen_Ioo
    have hSNonempty : Nonempty S := by
      have hIoo : Nonempty (Ioo a b) := nonempty_Ioo_subtype hab
      let c : ℝ := hIoo.some
      let s := φ.symm c
      have h1 : s ∈ φ.source := by
        rw [← φ.symm_target]
        apply φ.symm.map_source
        simp only [φ.symm_source, hφTarget, mem_univ]
      have h2 : s ∈ φ ⁻¹' (Ioo a b) := by
        have : φ s = c := by
          apply φ.right_inv
          simp only [hφTarget, mem_univ]
        simp only [mem_preimage, mem_Ioo, this]
        exact Subtype.coe_prop hIoo.some
      exact Nonempty.intro ⟨s, mem_inter h1 h2⟩

    have hIcc : S = U ∩ V ∩ (φ ⁻¹' (Icc a b)) := by
      have haI : a ∉ I := by
        by_contra! ha
        have hIcoSubset : Ico a b ⊆ I := by
          rw [← Ioo_union_left hab, ← hx]
          apply union_subset_iff.mpr
          exact ⟨connectedComponentIn_subset I x, singleton_subset_iff.mpr ha⟩
        have : x ∈ Ico a b := mem_Ico_of_Ioo <| hx ▸ mem_connectedComponentIn hxI
        have hIcoIoo : Ico a b ⊆ connectedComponentIn I x :=
          isPreconnected_Ico.subset_connectedComponentIn this hIcoSubset
        exact (notMem_Ioo_of_le <| le_refl a) (hx ▸ hIcoIoo <| left_mem_Ico.mpr hab)

      have hbI : b ∉ I := by
        by_contra! hb
        have hIocSubset : Ioc a b ⊆ I := by
          rw [← Ioo_union_right hab, ← hx]
          apply union_subset_iff.mpr
          exact ⟨connectedComponentIn_subset I x, singleton_subset_iff.mpr hb⟩
        have : x ∈ Ioc a b := mem_Ioc_of_Ioo <| hx ▸ mem_connectedComponentIn hxI
        have hIcoIoo : Ioc a b ⊆ connectedComponentIn I x :=
          isPreconnected_Ioc.subset_connectedComponentIn this hIocSubset
        exact (notMem_Ioo_of_ge <| le_refl b) (hx ▸ hIcoIoo <| right_mem_Ioc.mpr hab)

      have hφ_neq_val {y : X} {c : ℝ} (hc : c ∉ I) : y ∈ φ.source → φ y = c → y ∉ V := by
        intro hysource hφy
        by_contra hyV
        have hyUV : y ∈ U ∩ V := by apply mem_inter (by rwa [← hφSource]) hyV
        subst c
        exact hc <| mem_image_of_mem φ hyUV

      have : φ.source ∩ V ∩ φ ⁻¹' (Icc a b) = φ.source ∩ V ∩ φ ⁻¹' (Ioo a b) := by
        apply Subset.antisymm_iff.mpr
        constructor
        · rintro t ⟨htUV, htφ⟩
          apply mem_inter htUV <| mem_preimage.mpr ?_
          have heq := eq_endpoints_or_mem_Ioo_of_mem_Icc <| mem_preimage.mp htφ
          obtain ⟨htU, htV⟩ := (mem_inter_iff t φ.source V).mp htUV
          have hta : φ t ≠ a := fun s ↦ hφ_neq_val haI htU s htV
          have htb : φ t ≠ b := fun s ↦ hφ_neq_val hbI htU s htV
          simpa only [hta, htb, false_or] using heq
        · exact inter_subset_inter (Subset.refl _) <| preimage_mono Ioo_subset_Icc_self

      rw [← hφSource, this]
      unfold S
      nth_rewrite 3 [inter_comm]
      apply inter_congr_right
      · rw [inter_comm, ← inter_assoc]
        exact inter_subset_right
      · have habImg : Ioo a b ⊆ φ '' (U ∩ V) := hx ▸ connectedComponentIn_subset I x
        have hφinv : φ.source ∩ φ ⁻¹' (Ioo a b) ⊆ φ.source ∩ (U ∩ V) := by
          apply subset_inter inter_subset_left
          rintro y ⟨hyU, hyφ⟩
          constructor
          · rwa [← hφSource]
          · obtain ⟨w, hwUV, hφw⟩ := (mem_image φ (U ∩ V) (φ y)).mp <| habImg hyφ
            have hwSource : w ∈ φ.source := hφSource ▸ mem_of_mem_inter_left hwUV
            rw [← φ.injOn hwSource hyU hφw]
            exact mem_of_mem_inter_right hwUV
        have : φ.source ∩ (U ∩ V) ⊆ V ∩ φ.source := by
          intro t ht
          apply mem_inter
          · exact mem_of_mem_inter_right <| mem_of_mem_inter_right ht
          · exact mem_of_mem_inter_left ht
        exact fun _ t ↦ this (hφinv t)

    have hS_V_inter_Ω : S = V ∩ S := by
      apply Eq.symm <| inter_eq_self_of_subset_right ?_
      rw [hIcc, inter_comm]
      exact subset_trans inter_subset_right <| inter_subset_right (s := U)
    have hOpen_V : ∃ Ω : Set X, IsOpen Ω ∧ S = V ∩ Ω := ⟨S, hSOpen, hS_V_inter_Ω⟩

    have hIccTarget : Icc a b ⊆ φ.target := by
      rw [hφTarget]
      exact fun _ _ ↦ trivial
    have hWCompact : IsCompact (U ∩ (φ ⁻¹' (Icc a b))) := by
      rw [← hφSource, ← φ.symm_image_eq_source_inter_preimage hIccTarget]
      apply IsCompact.image_of_continuousOn isCompact_Icc
      exact ContinuousOn.mono φ.continuousOn_symm hIccTarget
    have hClosed_V: ∃ W : Set X, IsClosed W ∧ S = V ∩ W := by
      use U ∩ φ ⁻¹' (Icc a b)
      constructor
      · exact hWCompact.isClosed -- this requires [T2Space X]
      · rw [hIcc]
        nth_rewrite 2 [inter_comm]
        nth_rewrite 1 [← inter_assoc]
        rfl

    obtain ⟨Ω, hΩ, hSΩ⟩ := hOpen_V
    obtain ⟨W, hW, hSW⟩ := hClosed_V

    have hVΩOpen : IsOpen (V ∩ Ω) := IsOpen.inter hV hΩ
    have hVWOpen : IsOpen (V ∩ Wᶜ) := IsOpen.inter hV IsClosed.isOpen_compl
    have hDisjoint : Disjoint (V ∩ Ω) (V ∩ Wᶜ) := by
      have hSc : V ∩ Wᶜ ⊆ Sᶜ := by
        rw [hSW, compl_inter V W]
        exact subset_union_of_subset_right inter_subset_right Vᶜ
      have hS : V ∩ Ω ⊆ S := Eq.subset (Eq.symm hSΩ)
      have : Disjoint S Sᶜ := disjoint_compl_right_iff_subset.mpr fun _ t ↦ t
      exact fun s hsΩ hsW ↦ this (fun _ t ↦ hS (hsΩ t)) (fun _ t ↦ hSc (hsW t))

    have hVCover : V ⊆ (V ∩ Ω) ∪ (V ∩ Wᶜ) := by
      rw [← inter_union_distrib_left V Ω Wᶜ]
      apply subset_inter (Subset.refl V)
      intro v hv
      apply (mem_union v Ω Wᶜ).mpr
      by_cases hs : v ∈ S
      · left
        exact mem_of_mem_inter_right (by rwa [hSΩ] at hs)
      · right
        have := Classical.not_and_iff_not_or_not.mp (by rwa [hSW] at hs)
        simpa only [hv, not_true, false_or] using this

    have : V ⊆ S := by
      rw [hSΩ]
      apply hVConn.isPreconnected.subset_left_of_subset_union hVΩOpen hVWOpen hDisjoint hVCover
      rw [inter_eq_self_of_subset_right, ← hSΩ]
      · exact Set.Nonempty.of_subtype
      · exact inter_subset_left
    have : V ⊆ U := hφSource ▸ (subset_inter_iff.mp this).1
    exact hNotVU this

  let C := connectedComponentIn I x
  obtain h := open_real_classification hφInter_open.connectedComponentIn
                                    <| isConnected_connectedComponentIn_iff.mpr hx
  have hCNotIoo : ¬(∃ a b : ℝ, C = Ioo a b) := by
    by_contra! h
    obtain ⟨a, b, hCab⟩ := h
    by_cases hab : a < b
    · exact (hInterval x a b hab) hCab
    · apply (mem_empty_iff_false x).mp
      rw [← Ioo_eq_empty_of_le <| le_of_not_gt hab, ← hCab]
      exact mem_connectedComponentIn hx
  have hCNotUniv : ¬(C = univ) := by
    by_contra! h
    apply hφInter_proper (univ_subset_iff.mp ?_)
    exact subset_trans (univ_subset_iff.mpr h) (connectedComponentIn_subset I x)
  simpa only [C, hCNotIoo, hCNotUniv, false_or, or_false] using h

/- If φ : U → ℝ and ψ : V → ℝ cover X, then the component of φ '' (U ∩ V)
   containing some fixed point φ y is a half-infinite interval.  We can ensure
   that this interval is (-∞, a), by replacing φ with - φ as needed. -/
lemma choose_intersection_component_left {U V : Set X}
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    (hV : IsOpen V) (hVConn : IsConnected V)
    (hNotUV : ¬U ⊆ V) (hNotVU : ¬V ⊆ U) {y : X} (hy : y ∈ U ∩ V) :
    ∃ φ' : OpenPartialHomeomorph X ℝ, φ'.source = U ∧ φ'.target = univ ∧
      (∃ a : ℝ, connectedComponentIn (φ' '' (U ∩ V)) (φ' y) = Iio a) := by
  have hφy : φ y ∈ φ '' (U ∩ V) := mem_image_of_mem φ hy
  obtain hLR := intersection_intervals
                hφSource hφTarget hV hVConn hNotUV hNotVU hφy

  by_cases h : ∃ a : ℝ, connectedComponentIn (φ '' (U ∩ V)) (φ y) = Iio a
  · use φ
  · simp only [h, false_or] at hLR
    obtain ⟨a, ha⟩ := hLR
    let mneg1 : ℝ ≃ₜ ℝ := Homeomorph.neg ℝ
    let φ' := φ.transHomeomorph mneg1
    have hφ'Source : φ'.source = U := by rw [← hφSource]; rfl
    have hφ'Target : φ'.target = univ := by
      rw [← hφTarget]
      simp_all only [φ.transHomeomorph_target, preimage_univ, φ']
    refine ⟨φ', hφ'Source, hφ'Target, - a, ?_⟩

    have : connectedComponentIn (φ' '' (U ∩ V)) (φ' y) =
          mneg1 '' connectedComponentIn (φ '' (U ∩ V)) (φ y) := by
      rw [show φ' y = mneg1 (φ y) by simp_all [φ']]
      have : mneg1 '' (φ '' (U ∩ V)) = φ' '' (U ∩ V) := by
        simp only [φ', φ.transHomeomorph_apply, comp_apply]
        exact image_image mneg1 φ (U ∩ V)
      rw [← this, mneg1.image_connectedComponentIn hφy]
    rw [this]
    have : mneg1 '' (Ioi a) = Iio (- a) := by
      simp_all only [Homeomorph.coe_neg, image_neg_eq_neg, neg_Ioi, mneg1]
    exact this ▸ congrArg (image mneg1) ha

/- If φ : U → ℝ and ψ : V → ℝ cover X, then the component of φ '' (U ∩ V)
   containing some fixed point φ y is a half-infinite interval.  We can ensure
   that this interval is (a, ∞), by replacing φ with - φ as needed. -/
lemma choose_intersection_component_right {U V : Set X}
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    (hV : IsOpen V) (hVConn : IsConnected V)
    (hNotUV : ¬U ⊆ V) (hNotVU : ¬V ⊆ U) {y : X} (hy : y ∈ U ∩ V) :
    ∃ φ' : OpenPartialHomeomorph X ℝ, φ'.source = U ∧ φ'.target = univ ∧
      (∃ a : ℝ, connectedComponentIn (φ' '' (U ∩ V)) (φ' y) = Ioi a) := by
  have hφy : φ y ∈ φ '' (U ∩ V) := mem_image_of_mem φ hy
  obtain hLR := intersection_intervals
                hφSource hφTarget hV hVConn hNotUV hNotVU hφy

  by_cases h : ∃ a : ℝ, connectedComponentIn (φ '' (U ∩ V)) (φ y) = Ioi a
  · use φ
  · simp only [h, or_false] at hLR
    obtain ⟨a, ha⟩ := hLR
    let mneg1 : ℝ ≃ₜ ℝ := Homeomorph.neg ℝ
    let φ' := φ.transHomeomorph mneg1
    have hφ'Source : φ'.source = U := by rw [← hφSource]; rfl
    have hφ'Target : φ'.target = univ := by
      rw [← hφTarget]
      simp_all only [φ.transHomeomorph_target, preimage_univ, φ']
    refine ⟨φ', hφ'Source, hφ'Target, - a, ?_⟩

    have : connectedComponentIn (φ' '' (U ∩ V)) (φ' y) =
          mneg1 '' connectedComponentIn (φ '' (U ∩ V)) (φ y) := by
      rw [show φ' y = mneg1 (φ y) by simp_all [φ']]
      have : mneg1 '' (φ '' (U ∩ V)) = φ' '' (U ∩ V) := by
        simp only [φ', φ.transHomeomorph_apply, comp_apply]
        exact image_image mneg1 φ (U ∩ V)
      rw [← this, mneg1.image_connectedComponentIn hφy]
    rw [this]
    have : mneg1 '' (Iio a) = Ioi (- a) := by
      simp_all only [Homeomorph.coe_neg, image_neg_eq_neg, neg_Iio, mneg1]
    exact this ▸ congrArg (image mneg1) ha

/- If a connected space is covered by two open sets, neither of which is
   contained in the other, then these open sets have nonempty intersection. -/
lemma nonempty_inter_connected_open_cover {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
    {U V : Set Y} (hU : IsOpen U) (hV : IsOpen V) (hUniv : U ∪ V = univ)
    (hNotUV : ¬(U ⊆ V)) (hNotVU : ¬(V ⊆ U)) : Nonempty (U ∩ V : Set Y) := by
  by_contra! h
  have hDisjoint : Disjoint U V :=
    fun _ hxU hxV ↦ le_bot_iff.mpr <| subset_eq_empty (subset_inter hxU hxV)
                                   <| isEmpty_coe_sort.mp h
  have hUNonempty : (univ ∩ U).Nonempty := by
    by_contra! _
    simp_all only [univ_inter, empty_subset, not_true_eq_false]
  obtain h := isPreconnected_univ.subset_left_of_subset_union
              hU hV hDisjoint (univ_subset_iff.mpr hUniv) hUNonempty
  exact hNotVU <| subset_trans (subset_univ V) h

/- Given two sets, either one is contained in the other or neither is. -/
lemma cover_nested_or_not {Y : Type*} (U V : Set Y) :
    U ⊆ V ∨ V ⊆ U ∨ (¬(U ⊆ V) ∧ ¬(V ⊆ U)) := by
  by_contra! ⟨_, _, _⟩
  simp_all only [not_false_eq_true, not_true_eq_false]

/- The series of lemmas below are aimed at establishing `monotone_iio_to_ioi`,
   which is the key result needed to show that if two overlapping open sets in
   a Hausdorff space are homeomorphic to ℝ, then their union is homeomorphic
   to either ℝ or a circle. -/

lemma partial_homeomorph_connected_component_subset {Y Z : Type*}
  [TopologicalSpace Y] [TopologicalSpace Z]
    {φ : OpenPartialHomeomorph Y Z} {y : Y} (hy : y ∈ φ.source) :
    φ '' (connectedComponentIn φ.source y) ⊆ connectedComponentIn φ.target (φ y) := by
  have hconn : IsConnected (φ '' connectedComponentIn φ.source y) := by
    refine IsConnected.image ?_ φ ?_
    · exact isConnected_connectedComponentIn_iff.mpr hy
    · exact φ.continuousOn.mono <| connectedComponentIn_subset φ.source y
  apply hconn.isPreconnected.subset_connectedComponentIn
  · apply mem_image_of_mem φ <| mem_connectedComponentIn hy
  · apply MapsTo.image_subset
    exact fun _ t ↦ φ.mapsTo <| connectedComponentIn_subset φ.source y t

lemma image_connectedComponentIn {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {φ : OpenPartialHomeomorph Y Z} {y : Y} (hy : y ∈ φ.source) :
    φ '' (connectedComponentIn φ.source y) = connectedComponentIn φ.target (φ y) := by
  apply Set.Subset.antisymm
  · exact partial_homeomorph_connected_component_subset hy
  · have {A : Set Z} (hA : A ⊆ φ.target) : φ '' (φ.symm '' A) = A :=
      LeftInvOn.image_image <| fun _ t ↦ φ.rightInvOn (hA t)
    rw [← this <| connectedComponentIn_subset φ.target (φ y)]
    apply image_mono
    have hφy : φ y ∈ φ.symm.source := by simp_all
    obtain h := partial_homeomorph_connected_component_subset hφy
    rwa [φ.symm_source, φ.symm_target, φ.left_inv hy] at h

lemma transition_iio_to_ioi {Y : Type*} [TopologicalSpace Y] [T2Space Y] {U V : Set Y}
    {φ ψ : OpenPartialHomeomorph Y ℝ} (hφSource : φ.source = U) (hψSource : ψ.source = V)
    {y : Y} (hy : y ∈ U ∩ V) {a b : ℝ}
    (hφInter : connectedComponentIn (φ '' (U ∩ V)) (φ y) = Iio a)
    (hψInter : connectedComponentIn (ψ '' (U ∩ V)) (ψ y) = Ioi b) :
    (φ.symm.trans ψ) '' (Iio a) = (Ioi b) := by
  let f : OpenPartialHomeomorph ℝ ℝ := φ.symm.trans ψ
  have hfSource : f.source = φ '' (U ∩ V) := by
    simp only [f, φ.symm.trans_source, φ.symm_source, hψSource,
               ← φ.image_source_inter_eq', hφSource]
  have hfTarget : f.target = ψ '' (U ∩ V) := by
    simp only [f, φ.symm.trans_target, φ.symm_target, hφSource, ← hψSource]
    nth_rewrite 2 [inter_comm]
    exact Eq.symm <| ψ.image_source_inter_eq' U
  have hfφy : f (φ y) = ψ y := by simp_all [f]
  rw [← hφInter, ← hψInter, ← hfφy, ← hfSource, ← hfTarget]
  apply image_connectedComponentIn
  simp_all

private lemma nhd_real_contains_interval {t : ℝ} {s : Set ℝ} (hs : s ∈ nhds t) :
    ∃ ε : ℝ, ε > 0 ∧ Ioo (t - ε) (t + ε) ⊆ s := by
  obtain ⟨α, β, ht, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp hs
  let ε : ℝ := min (t - α) (β - t)
  use ε
  constructor
  · exact lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
  · have : Ioo (t - ε) (t + ε) ⊆ Ioo α β := by
      apply Ioo_subset_Ioo
      · exact le_sub_comm.mp <| min_le_left (t - α) (β - t)
      · exact le_sub_iff_add_le'.mp <| min_le_right (t - ↑α) (↑β - t)
    exact fun _ τ ↦ hIoo <| this τ

lemma image_intersection_subset_transition_source {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {U V : Set X} {φ ψ : OpenPartialHomeomorph X Y}
    (hφSource : φ.source = U) (hφTarget : φ.target = univ) (hψSource : ψ.source = V) :
    (φ '' (U ∩ V)) ⊆ (φ.symm.trans ψ).source := by
  rw [φ.symm.trans_source, φ.symm_source, hφTarget, hψSource, univ_inter]
  have : φ '' (U ∩ V) ⊆ φ.symm ⁻¹' (U ∩ V) := by
    intro t ⟨s, hsUV, _⟩
    subst t
    apply mem_preimage.mpr
    rwa [φ.left_inv <| (subset_of_subset_of_eq inter_subset_left (Eq.symm hφSource)) hsUV]
  apply Subset.trans this <| preimage_mono inter_subset_right

/- Let U and V be subsets of the Hausdorff space Y, with U ≃ₜ ℝ and V ≃ₜ ℝ,
   and let C be a component of their intersection.  If C is identified with
   (-∞,a) in U and with (b,∞) in V, then the corresponding transition map
   (-∞,a) → (b,∞) is strictly monotone increasing. -/
lemma monotone_iio_to_ioi {Y : Type*} [TopologicalSpace Y] [instT2 : T2Space Y]
    {U V : Set Y} {φ ψ : OpenPartialHomeomorph Y ℝ} {a b : ℝ}
    (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    (hψSource : ψ.source = V) (hψTarget : ψ.target = univ)
    {y : Y} (hy : y ∈ U ∩ V)
    (hφInter : connectedComponentIn (φ '' (U ∩ V)) (φ y) = Iio a)
    (hψInter : connectedComponentIn (ψ '' (U ∩ V)) (ψ y) = Ioi b) :
    StrictMonoOn (φ.symm.trans ψ) (Iio a) := by
  let f : OpenPartialHomeomorph ℝ ℝ := φ.symm.trans ψ
  have hf_Iio_image : f '' (Iio a) = (Ioi b) :=
    transition_iio_to_ioi hφSource hψSource hy hφInter hψInter
  have hf_MapsTo : MapsTo f (Iio a) (Ioi b) := by
    rw [← hf_Iio_image]
    exact fun _ ht ↦ mem_image_of_mem f ht

  have ha : a ∉ φ '' (U ∩ V) :=
    right_notMem_of_connectedComponentIn_Iio (mem_image_of_mem φ hy) hφInter
  have hb : b ∉ ψ '' (U ∩ V) :=
    left_notMem_of_connectedComponentIn_Ioi (mem_image_of_mem ψ hy) hψInter

  have : Iio a ⊆ f.source := by
    rw [← hφInter]
    apply subset_trans (connectedComponentIn_subset (φ '' (U ∩ V)) (φ y)) ?_
    exact image_intersection_subset_transition_source hφSource hφTarget hψSource
  have hfInj : InjOn f (Iio a) := InjOn.mono this f.injOn
  have hfCont : ContinuousOn f (Iio a) := f.continuousOn.mono this

  have hf'Cont (c : ℝ) : ContinuousOn f (Ioo c a) := hfCont.mono Ioo_subset_Iio_self
  have hf'Inj (c : ℝ) : InjOn f (Ioo c a) := hfInj.mono Ioo_subset_Iio_self
  have hMonoAnti {c : ℝ} (hc : c < a) : StrictMonoOn f (Ioo c a) ∨ StrictAntiOn f (Ioo c a) :=
    (hf'Cont c).strictMonoOn_of_injOn_Ioo hc (hf'Inj c)

  -- If f : (-∞,a) → (b,∞) is strictly decreasing, then φ.symm a and ψ.symm b
  -- are distinct points without disjoint neighborhoods, contradicting `T2Space Y`.
  have antiOn_sup_ge_b {c : ℝ} : c < a → StrictAntiOn f (Ioo (c - 1) a) →
      ∃ δ > 0, MapsTo f (Ioo (c - 1) a) (Ici (b + δ)) := by
    intro hc h
    let α : Y := φ.symm a
    let β : Y := ψ.symm b
    have hαβ : α ≠ β := by
      have hCnotUV : α ∉ U ∩ V := by
        have : φ α = a := by simp_all [α]
        have : φ α ∉ φ '' (U ∩ V) := this ▸ ha
        exact fun hα => this <| mem_image_of_mem φ hα
      have : α ∈ U := by
        simp only [← hφSource, α]
        apply φ.map_target
        simp only [hφTarget, mem_univ]
      have hαV : α ∉ V := fun hαV' => hCnotUV <| mem_inter this hαV'
      have hβV : β ∈ V := by
        simp only [← hψSource, β]
        apply ψ.map_target
        simp only [hψTarget, mem_univ]
      exact Ne.symm <| ne_of_mem_of_not_mem hβV hαV

    obtain ⟨Uα₀, Uβ₀, hUα₀Open, hUβ₀Open, hα₀u, hβ₀u, hDisjoint₀⟩ :=
      ((t2Space_iff Y).mp instT2) hαβ

    let Uα := Uα₀ ∩ φ.source
    have hUαOpen : IsOpen Uα := hUα₀Open.inter φ.open_source
    have hαu : α ∈ Uα := by
      apply mem_inter hα₀u
      subst hφSource
      simp_all only [mem_univ, φ.map_target, α, Uα]
    let Uβ := Uβ₀ ∩ ψ.source
    have hUβOpen : IsOpen Uβ := hUβ₀Open.inter ψ.open_source
    have hβu : β ∈ Uβ := by
      apply mem_inter hβ₀u
      subst hψSource
      simp_all only [mem_univ, ψ.map_target, β, Uβ]
    have hDisjoint : Disjoint Uα Uβ :=
      fun s hsα hsβ ↦ hDisjoint₀ (fun _ hs ↦ mem_of_mem_inter_left (hsα hs))
                                 (fun _ hs ↦ mem_of_mem_inter_left (hsβ hs))

    -- every neighborhood of φ⁻¹(x) contains φ⁻¹( (x-ε,x+ε) ) for some ε > 0
    have {W : Set Y} {x : ℝ} {η : OpenPartialHomeomorph Y ℝ} (hη : η.target = univ) :
        W ∈ nhds (η.symm x) → ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ η '' W := by
      intro hW
      have hx_source : η.symm x ∈ η.source := η.map_target <| by simp_all only [mem_univ]
      have hx_target : x ∈ η.target := by simp only [hη, mem_univ]
      have : η.source ∈ nhds (η.symm x) := η.open_source.mem_nhds_iff.mpr hx_source
      have : η '' (η.source ∩ W) ∈ nhds x := by
        rw [show x = η (η.symm x) by simp_all]
        exact η.image_mem_nhds hx_source <| Filter.inter_mem this hW
      obtain ⟨ε, hε, hηW'⟩ := nhd_real_contains_interval this
      refine ⟨ε, hε, ?_⟩
      intro t ht
      obtain ⟨y, hηW, hηx⟩ := hηW' ht
      exact (mem_image η W t).mpr ⟨y, mem_of_mem_inter_right hηW, hηx⟩
    -- some ε-neighborhood of a is contained in φ '' Uα
    obtain ⟨ε, hε, haε⟩ := this hφTarget <| hUαOpen.mem_nhds hαu
    -- some ε'-neighborhood of b is contained in φ '' Uβ
    obtain ⟨ε', hε', hbε'⟩ := this hψTarget <| hUβOpen.mem_nhds hβu

    have hc_nhd : φ.symm '' (Ioo (a - ε) (a + ε)) ∈ nhds α := by
      apply φ.symm.image_mem_nhds
      · simp only [φ.symm_source, hφTarget, mem_univ]
      · exact Ioo_mem_nhds (sub_lt_self a hε) (lt_add_of_pos_right a hε)

    have nhd_in_source {η : OpenPartialHomeomorph Y ℝ} (c δ : ℝ)
        (U : Set Y) (hcδ : Ioo (c - δ) (c + δ) ⊆ η '' (U ∩ η.source)):
        η.symm '' (Ioo (c - δ) (c + δ)) ⊆ U ∩ η.source := by
      let Uη := U ∩ η.source
      have : η.symm '' (η '' Uη) ⊆ Uη := by
        have hUη_ηSource : Uη ⊆ η.source := inter_subset_right
        intro x ⟨t, htη, htx⟩
        have : t ∈ η.target := by
          rw [← η.image_source_eq_target]
          exact (image_mono inter_subset_right) htη
        have hηSymm_t : η.symm t ∈ η.source := η.map_target this
        refine mem_inter ?_ (by rwa [← htx])
        obtain ⟨s, hsUη, hst⟩ := (mem_image η Uη t).mp htη
        have : t = η x := by
          apply congrArg η at htx
          rwa [show η (η.symm t) = t by simp_all] at htx
        rw [this] at hst
        rw [η.injOn (hUη_ηSource hsUη) (mem_of_eq_of_mem (Eq.symm htx) hηSymm_t) hst] at hsUη
        exact inter_subset_left hsUη
      intro _ ⟨_, htη, htx⟩
      exact htx ▸ (this <| mem_image_of_mem η.symm (hcδ htη))

    have hc_nhd : φ.symm '' (Ioo (a - ε) a) ⊆ Uα := by
      have : Ioo (a - ε) a ⊆ Ioo (a - ε) (a + ε) :=
        Ioo_subset_Ioo (le_refl _) (le_of_lt <| lt_add_of_pos_right a hε)
      apply Subset.trans <| image_mono this
      exact nhd_in_source a ε Uα₀ haε

    have hd_nhd : ψ.symm '' (Ioo b (b + ε')) ⊆ Uβ := by
      have : Ioo b (b + ε') ⊆ Ioo (b - ε') (b + ε') :=
        Ioo_subset_Ioo (le_of_lt <| sub_lt_self b hε') (le_refl _)
      apply Subset.trans <| image_mono this
      exact nhd_in_source b ε' Uβ₀ hbε'

    clear this nhd_in_source hUα₀Open hUβ₀Open hα₀u hβ₀u hDisjoint₀

    have hfaε' : f '' (Ioo (a - ε) a) ⊆ ψ '' Uα := by
      have := image_mono hc_nhd (f := ψ)
      simp_all [f, ← image_comp]

    have hfIoo : f '' (Ioo (a - ε) a) ⊆ ψ '' (U ∩ V) := by
      have hM : MapsTo f (Ioo (a - ε) a) (Ioi b) := fun _ hx ↦ hf_MapsTo hx.2
      have : Ioi b ⊆ ψ '' (U ∩ V) :=
        hψInter ▸ connectedComponentIn_subset (ψ '' (U ∩ V)) (ψ y)
      exact image_subset_iff.mpr fun _ t ↦ this (hM t)

    have : φ.symm '' (Iio a) ⊆ U ∩ V := by
      have hIio_φ : Iio a ⊆ φ '' (U ∩ V) :=
        hφInter ▸ connectedComponentIn_subset (φ '' (U ∩ V)) (φ y)
      have {t : ℝ} : t ∈ Iio a → φ.symm t ∈ U ∩ V := by
        intro ht
        obtain ⟨s, hsUV, hφs⟩ := hIio_φ ht
        rwa [← hφs, φ.left_inv <| hφSource ▸ inter_subset_left hsUV]
      intro t ⟨s, hs, hs'⟩
      exact hs' ▸ this hs

    have hφsymmIio_source : φ.symm '' (Iio a) ⊆ ψ.source :=
      hψSource ▸ fun _ t ↦ inter_subset_right (this t)

    have hDisjoint' {s t : Y} :
        s ∈ φ.symm '' (Ioo (a - ε) a) → t ∈ ψ.symm '' (Ioo b (b + ε')) → ψ s ≠ ψ t := by
      intro hs ht
      have hsSource : s ∈ ψ.source := hφsymmIio_source <| image_mono Ioo_subset_Iio_self hs
      have htSource : t ∈ ψ.source := by
        have : t ∈ ψ.symm '' ψ.symm.source := by
          apply (image_mono ?_) ht
          simp only [ψ.symm_source, hψTarget, subset_univ]
        rwa [ψ.symm.image_source_eq_target, ψ.symm_target] at this
      apply ψ.injOn.ne hsSource htSource
      exact disjoint_iff_forall_ne.mp hDisjoint (hc_nhd hs) (hd_nhd ht)

    have hf_intervals_disjoint {x y : ℝ} :
        x ∈ Ioo (a - ε) a → y ∈ Ioo b (b + ε') → f x ≠ y := by
      intro hx hy
      have hψ := hDisjoint' (mem_image_of_mem φ.symm hx) (mem_image_of_mem ψ.symm hy)
      have : ψ (ψ.symm y) = y := ψ.right_inv (by simp only [hψTarget, mem_univ])
      rwa [this] at hψ

    have {x : ℝ} : x ∈ Ioo (c - 1) a → f x ≥ b + ε' := by
      intro hx
      by_contra hf
      have hfx : f x ∈ Ioo b (b + ε') := mem_Ioo.mpr ⟨hf_MapsTo hx.2, lt_of_not_ge hf⟩
      by_cases hx' : x > a - ε
      · exact (hf_intervals_disjoint ⟨hx', hx.2⟩ hfx) rfl
      · let a' := max (a - ε) (c - 1)
        have : a' < a := max_lt_iff.mpr ⟨sub_lt_self a hε, LT.lt.trans hx.1 hx.2⟩
        have : Nonempty (Ioo a' a) := nonempty_Ioo_subtype this
        let y : ℝ := this.some.val
        have hy : y ∈ Ioo a' a := this.some.coe_prop
        have hxy : x < y := by
          apply lt_of_le_of_lt (le_of_not_gt hx')
          exact lt_of_le_of_lt (le_max_left (a - ε) (c - 1)) hy.1
        have hfxy : f x > f y := h hx ⟨lt_trans hx.1 hxy, hy.2⟩ hxy
        have hy' : y ∈ Ioo (a - ε) a :=
          ⟨lt_of_le_of_lt (le_max_left (a - ε) (c - 1)) hy.1, hy.2⟩
        have hfy' : f y ∈ Ioo b (b + ε') := ⟨hf_MapsTo hy.2, LT.lt.trans hfxy hfx.2⟩
        exact hf_intervals_disjoint hy' hfy' rfl

    exact ⟨ε', hε', fun _ ht ↦ this ht⟩

  -- Now we can prove that f is strictly monotone on (-∞, a)
  by_contra h
  unfold StrictMonoOn at h
  push Not at h

  -- If not, there is some c < d < a such that f d ≤ f c
  obtain ⟨c, hc, d, hd, hcd, hfcd⟩ := h
  let hMA := hMonoAnti <| LT.lt.trans (sub_one_lt c) hc
  have hMca : ¬ StrictMonoOn f (Ioo (c - 1) a) := by
    unfold StrictMonoOn
    push Not
    refine ⟨c, mem_Ioo.mpr ⟨sub_one_lt c, hc⟩, d, ?_, hcd, hfcd⟩
    exact mem_Ioo.mpr ⟨lt_trans (sub_one_lt c) hcd, hd⟩
  -- f isn't strictly monotone on (c - 1, a), so it must be strictly antitone.
  simp only [hMca, false_or] at hMA
  -- We've seen that this means f sends (c - 1, a) into [b + δ, ∞) where δ > 0
  obtain ⟨δ, hδ, hmaps⟩ := antiOn_sup_ge_b hc hMA

  obtain ⟨w, hw, hfwbδ⟩ : ∃ w ∈ Iio a, f w < b + δ := by
    have : Nonempty (Ioo b (b + δ)) := nonempty_Ioo_subtype <| lt_add_of_pos_right b hδ
    let z := this.some.val
    have hz : z ∈ Ioo b (b + δ) := this.some.coe_prop
    have : ∃ w ∈ Iio a, f w = z := by
      have : z ∈ Ioi b := hz.1
      rwa [← hf_Iio_image] at this
    obtain ⟨w, hw, hfw⟩ := this
    exact ⟨w, hw, lt_of_le_of_lt (le_of_eq hfw) hz.2⟩

  -- Now f w < b + δ, but f ≥ b + δ on all of (c - 1,a) by hmaps, so w ≤ c - 1.
  -- Thus w < c < d, and f w < f d ≤ f c implies that f is neither
  -- strictly monotone nor strictly antitone on (w - 1, a).

  have hwc1 : w ≤ c - 1 := by
    by_contra hw_gt
    exact (not_lt_of_ge <| hmaps ⟨lt_of_not_ge hw_gt, hw⟩) hfwbδ
  have hw1c : w - 1 < c := lt_trans (sub_one_lt w) <| lt_of_le_of_lt hwc1 (sub_one_lt c)

  -- f is either strictly monotone or strictly antitone on (w - 1, a)
  obtain hMA' := hMonoAnti <| lt_trans (sub_one_lt w) hw

  -- Not strictly monotone, because c < d but f d ≤ f c
  have hNotMono : ¬ StrictMonoOn f (Ioo (w - 1) a) := by
    unfold StrictMonoOn
    push Not
    exact ⟨c, mem_Ioo.mpr ⟨hw1c, hc⟩, d, mem_Ioo.mpr ⟨lt_trans hw1c hcd, hd⟩, hcd, hfcd⟩

  -- Not strictly antitone, because w < d but f w ≤ f d
  have hNotAnti : ¬ StrictAntiOn f (Ioo (w - 1) a) := by
    unfold StrictAntiOn
    push Not
    refine ⟨w, mem_Ioo.mpr ⟨sub_one_lt w, hw⟩, c, mem_Ioo.mpr ⟨hw1c, hc⟩, ?_, ?_⟩
    · exact lt_of_le_of_lt hwc1 (sub_one_lt c)
    · exact le_trans (le_of_lt hfwbδ) <| hmaps ⟨sub_one_lt c, hc⟩

  simp only [hNotMono, hNotAnti, false_or] at hMA'

lemma image_connectedComponentIn_subset_connectedComponentIn {Y : Type*} [TopologicalSpace Y]
    {φ : OpenPartialHomeomorph Y ℝ} {U : Set Y} {t : Y} (ht : t ∈ U) (hφSource : U ⊆ φ.source) :
    φ '' (connectedComponentIn U t) ⊆ connectedComponentIn (φ '' U) (φ t) := by
  have hConn : IsConnected (φ '' (connectedComponentIn U t)) := by
    apply (isConnected_connectedComponentIn_iff.mpr ht).image φ <| φ.continuousOn.mono ?_
    exact subset_trans (connectedComponentIn_subset U t) hφSource
  apply hConn.isPreconnected.subset_connectedComponentIn
    (mem_image_of_mem φ <| mem_connectedComponentIn ht)
  exact image_mono <| connectedComponentIn_subset U t

/- Given a component of an overlap U ∩ V between two real charts, write it as
   the union of two subintervals, one parametrized by each chart, with common
   boundary at a specified point. -/
lemma connectedComponentIn_split {t : X} {U V : Set X} (ht : t ∈ U ∩ V)
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    {ψ : OpenPartialHomeomorph X ℝ} (hψSource : ψ.source = V) (hψTarget : ψ.target = univ)
    {a : ℝ} (hφ : connectedComponentIn (φ '' (U ∩ V)) (φ t) = Iio a)
    {b : ℝ} (hψ : connectedComponentIn (ψ '' (U ∩ V)) (ψ t) = Ioi b) :
    connectedComponentIn (U ∩ V) t = φ.symm '' (Ico (φ t) a) ∪ ψ.symm '' (Ioc b (ψ t)) := by
  let Cφ := connectedComponentIn (φ '' (U ∩ V)) (φ t)
  let Cψ := connectedComponentIn (ψ '' (U ∩ V)) (ψ t)
  have hφ_symm_apply_apply {z : X} : z ∈ U ∩ V → φ.symm (φ z) = z :=
    fun _ ↦ by simp_all only [mem_inter_iff, φ.left_inv]
  have hψ_symm_apply_apply {z : X} : z ∈ U ∩ V → ψ.symm (ψ z) = z :=
    fun _ ↦ by simp_all only [mem_inter_iff, ψ.left_inv]
  have hφta : φ t ∈ Iio a := hφ ▸ mem_connectedComponentIn <| mem_image_of_mem φ ht
  have hψtb : ψ t ∈ Ioi b := hψ ▸ mem_connectedComponentIn <| mem_image_of_mem ψ ht
  ext s
  constructor <;> intro hs
  · have hsUV : s ∈ U ∩ V := by
      apply connectedComponentIn_nonempty_iff.mp
      exact connectedComponentIn_eq hs ▸ connectedComponentIn_nonempty_iff.mpr ht
    have hφ_ccI : φ '' (connectedComponentIn (U ∩ V) t) ⊆ Cφ := by
      apply image_connectedComponentIn_subset_connectedComponentIn ht ?_
      exact hφSource ▸ inter_subset_left
    have hψ_ccI : ψ '' (connectedComponentIn (U ∩ V) t) ⊆ Cψ := by
      apply image_connectedComponentIn_subset_connectedComponentIn ht ?_
      exact hψSource ▸ inter_subset_right
    have hφs_a : φ s ∈ Cφ := hφ_ccI <| mem_image_of_mem φ hs
    simp only [Cφ, hφ, mem_union] at hφs_a ⊢
    by_cases hφs : φ s ≥ φ t
    · left
      exact hφ_symm_apply_apply hsUV ▸ mem_image_of_mem φ.symm <| mem_Ico.mpr ⟨hφs, hφs_a⟩
    · right
      rw [← hψ_symm_apply_apply hsUV]
      apply mem_image_of_mem ψ.symm <| mem_Ioc.mpr ⟨?_, le_of_lt ?_⟩
      · exact mem_Ioi.mp <| hψ ▸ (hψ_ccI <| mem_image_of_mem ψ hs)
      · have hψst : (φ.symm.trans ψ) (φ s) < (φ.symm.trans ψ) (φ t) :=
          (monotone_iio_to_ioi hφSource hφTarget hψSource hψTarget ht hφ hψ)
          hφs_a hφta (lt_of_not_ge hφs)
        rwa [φ.symm.trans_apply, hφ_symm_apply_apply hsUV,
             φ.symm.trans_apply, hφ_symm_apply_apply ht] at hψst
  · simp only [mem_union] at hs
    rcases hs with h | h <;> obtain ⟨r, hr, hrs⟩ := h
    · have hconn : IsConnected (φ.symm '' (Ico (φ t) a)) := by
        apply (isConnected_Ico hφta).image φ.symm <| φ.symm.continuousOn.mono ?_
        simp only [φ.symm_source, hφTarget, subset_univ]
      have hs_mem : s ∈ (φ.symm '' (Ico (φ t) a)) := hrs ▸ mem_image_of_mem φ.symm hr
      have ht_mem : t ∈ (φ.symm '' (Ico (φ t) a)) := by
        nth_rewrite 2 [← hφ_symm_apply_apply ht]
        exact mem_image_of_mem φ.symm <| left_mem_Ico.mpr hφta
      have : φ.symm '' (Ico (φ t) a) ⊆ U ∩ V := by
        apply subset_trans <| image_mono <| fun _ h ↦ mem_Iio.mpr h.2
        rw [← hφ]
        apply subset_trans <| image_mono <| connectedComponentIn_subset (φ '' (U ∩ V)) (φ t)
        rw [← image_comp]
        exact fun _ ⟨_, hq, hqr⟩ ↦ by rwa [← hqr, comp_apply, hφ_symm_apply_apply hq]
      exact (hconn.isPreconnected.subset_connectedComponentIn ht_mem this) hs_mem

    · have hconn : IsConnected (ψ.symm '' (Ioc b (ψ t))) := by
        apply (isConnected_Ioc hψtb).image ψ.symm <| ψ.symm.continuousOn.mono ?_
        simp only [ψ.symm_source, hψTarget, subset_univ]
      have hs_mem : s ∈ (ψ.symm '' (Ioc b (ψ t))) := hrs ▸ mem_image_of_mem ψ.symm hr
      have ht_mem : t ∈ (ψ.symm '' (Ioc b (ψ t))) := by
        nth_rewrite 2 [← hψ_symm_apply_apply ht]
        exact mem_image_of_mem ψ.symm <| right_mem_Ioc.mpr hψtb
      have : ψ.symm '' (Ioc b (ψ t)) ⊆ U ∩ V := by
        apply subset_trans <| image_mono <| fun _ h ↦ mem_Ioi.mpr h.1
        rw [← hψ]
        apply subset_trans <| image_mono <| connectedComponentIn_subset (ψ '' (U ∩ V)) (ψ t)
        rw [← image_comp]
        exact fun _ ⟨_, hq, hqr⟩ ↦ by rwa [← hqr, comp_apply, hψ_symm_apply_apply hq]
      exact (hconn.isPreconnected.subset_connectedComponentIn ht_mem this) hs_mem

/- Given a point t in some component of the intersection of two real charts
   φ and ψ, the intersection of the subsets `φ.symm '' (Ici (φ t))` and
   `ψ.symm '' (Iic (ψ t))` in this component is just the point t itself. -/
lemma overlap_intersection {s t : X} {U V : Set X} {a b : ℝ}
    {φ : OpenPartialHomeomorph X ℝ} (hφSource : φ.source = U) (hφTarget : φ.target = univ)
    {ψ : OpenPartialHomeomorph X ℝ} (hψSource : ψ.source = V) (hψTarget : ψ.target = univ)
    (htφ : connectedComponentIn (φ '' (U ∩ V)) (φ t) = Iio a)
    (htψ : connectedComponentIn (ψ '' (U ∩ V)) (ψ t) = Ioi b)
    (ht : t ∈ U ∩ V) (hφta : φ t ∈ Iio a)
    (hsCpt : s ∈ connectedComponentIn (U ∩ V) t)
    (hsUV : s ∈ U ∩ V) (hs : s ∈ φ.symm '' (Ici (φ t)) ∩ ψ.symm '' (Iic (ψ t))) :
    s = t := by
  have hφ_symm_apply_apply {z : X} : z ∈ U ∩ V → φ.symm (φ z) = z :=
    fun _ ↦ by simp_all only [mem_inter_iff, φ.left_inv]
  have hψ_symm_apply_apply {z : X} : z ∈ U ∩ V → ψ.symm (ψ z) = z :=
    fun _ ↦ by simp_all only [mem_inter_iff, ψ.left_inv]
  have hφsymm_inj : Injective φ.symm := φ.injective_symm_of_target_eq_univ hφTarget
  have hψsymm_inj : Injective ψ.symm := ψ.injective_symm_of_target_eq_univ hψTarget

  have hfφt : (φ.symm.trans ψ) (φ t) = (ψ t) := by
    simp only [φ.symm.trans_apply, hφ_symm_apply_apply ht]
  have hsa : s ∈ φ.symm '' Iio a := by
    rw [← htφ, ← hφ_symm_apply_apply hsUV]
    apply mem_image_of_mem φ.symm
    apply mem_image_of_mem φ at hsCpt
    have : U ∩ V ⊆ φ.source := hφSource ▸ inter_subset_left
    exact (image_connectedComponentIn_subset_connectedComponentIn ht this) hsCpt

  by_contra hst
  have hψs_le_ψx : ψ s ≤ ψ t := by
    apply mem_Iic.mp <| hψsymm_inj.mem_set_image.mp ?_
    rw [hψ_symm_apply_apply hsUV]
    exact mem_of_mem_inter_right hs

  obtain ⟨r, hr, hrs⟩ := mem_of_mem_inter_left hs
  have : φ t < r := by
    apply lt_of_le_of_ne hr <| Ne.symm ?_
    by_contra hrφx
    exact hst <| Eq.trans (Eq.trans (Eq.symm hrs) (congrArg φ.symm hrφx)) (hφ_symm_apply_apply ht)
  have : ψ t < (φ.symm.trans ψ) r := by
    rw [← hfφt]
    have hMono : StrictMonoOn (φ.symm.trans ψ) (Iio a) :=
      monotone_iio_to_ioi hφSource hφTarget hψSource hψTarget ht htφ htψ
    apply hMono hφta ?_ this
    apply hφsymm_inj.mem_set_image.mp
    apply mem_image_of_mem φ.symm
    exact hφsymm_inj.mem_set_image.mp (by rwa [← hrs] at hsa)
  simp only [φ.symm.trans_apply, hrs] at this
  exact (not_le_of_gt this) hψs_le_ψx

lemma partial_homeomorph_image_connected_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (φ : OpenPartialHomeomorph X Y) {U : Set X} (hφSource : U ⊆ φ.source) :
    IsConnected U ↔ IsConnected (φ '' U) := by
  constructor
  · exact fun hConn ↦ hConn.image φ <| φ.continuousOn.mono hφSource
  · intro hConn
    have {t : X} : t ∈ U → (φ.symm ∘ φ) t = t := by
      rw [comp_apply]
      exact fun htU ↦ φ.left_inv <| mem_of_subset_of_mem hφSource htU
    have hφ_symm_apply_apply : (φ.symm ∘ φ) '' U = U := by
      apply Subset.antisymm
      · exact fun _ ⟨_, hs, hst⟩ ↦ by rwa [← hst, this hs]
      · exact fun _ ht ↦ this ht ▸ mem_image_of_mem (φ.symm ∘ φ) ht
    rw [← hφ_symm_apply_apply, image_comp]
    apply hConn.image φ.symm <| φ.symm.continuousOn.mono ?_
    rw [φ.symm_source]
    exact image_subset_iff.mpr <| subset_trans hφSource φ.source_preimage_target
