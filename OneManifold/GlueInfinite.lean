import Mathlib.Tactic
import «OneManifold».GluePartialHomeomorph
import «OneManifold».RealCover
import «OneManifold».RealLemmas

open Set Function Topology
set_option linter.style.emptyLine false

lemma incl_mk {X : Type*} [TopologicalSpace X] {U : Set X} [Nonempty U] (hUOpen : IsOpen U) :
    ∃ i : OpenPartialHomeomorph U X, i.source = @univ U ∧ i.target = U
      ∧ (∀ x : U, i x = Subtype.val x) := by
  refine ⟨hUOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph, ?_, ?_, ?_⟩
  · rw [IsOpenEmbedding.toOpenPartialHomeomorph_source]
  · rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact Subtype.range_coe_subtype
  · simp only [IsOpenEmbedding.toOpenPartialHomeomorph_apply, implies_true]

/- Given (1) open sets U, V ⊆ X, with U connected and V homeomorphic to ℝ and
   with (closure U) a compact subset of V, and (2) intervals [a, b] ⊆ (c, d)
   with a < b, there is an OpenPartialHomeomorphism X ℝ sending (closure U) to
   [a, b] and V to (c, d). -/
lemma openPartialHomeomorph_real_fix_compact_Icc {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hPrecompact : IsCompact (closure U)) (hConnected : IsConnected U)
    (hSubset : closure U ⊆ V) (hVReal : Nonempty (V ≃ₜ ℝ))
    {a b c d : ℝ} (hab : a < b) (hInterval : Icc a b ⊆ Ioo c d) :
    ∃ φ : OpenPartialHomeomorph X ℝ, (φ.source = V ∧ φ.target = Ioo c d ∧
      φ '' (closure U) = Icc a b) := by
  -- Construct f : OpenPartialHomeomorph X ℝ sending V to univ
  haveI : Nonempty V := Nonempty.intro <| hVReal.some.symm 0
  obtain ⟨inclV, hInclSource, hInclTarget, hIncl_apply⟩ := incl_mk hVOpen
  let f : OpenPartialHomeomorph X ℝ := by
    apply inclV.symm.trans' hVReal.some.toOpenPartialHomeomorph
    rw [inclV.symm_target, hInclSource, hVReal.some.toOpenPartialHomeomorph_source]
  have hfSource : f.source = V := by
    simp only [f, inclV.symm.trans'_source, inclV.symm_source, hInclTarget]
  have hfTarget : f.target = univ := by
    simp only [f, inclV.symm.trans'_target, hVReal.some.toOpenPartialHomeomorph_target]
  -- Show that f '' U = Ioo x y and f '' (closure U) = Icc x y for some x < y
  have hfContOn' : ContinuousOn f (closure U) := by
    apply f.continuousOn.mono
    rwa [hfSource]
  have hfU'Compact : IsCompact (f '' (closure U)) := hPrecompact.image_of_continuousOn hfContOn'
  have hfU'Connected : IsConnected (f '' (closure U)) := hConnected.closure.image f hfContOn'
  obtain ⟨x, y, hxy, hIcc⟩ := compact_real_classification hfU'Compact hfU'Connected
  have hClosure_f : closure (f '' U) = Icc x y := by
    rwa [← image_closure_of_isCompact hPrecompact hfContOn']
  have hfUOpen : IsOpen (f '' U) := by
    apply f.isOpen_image_of_subset_source hUOpen
    exact subset_trans subset_closure (by rwa [hfSource])
  have hfUConnected : IsConnected (f '' U) := by
    apply IsConnected.image hConnected f
    exact f.continuousOn.mono <| subset_trans subset_closure (by rwa [hfSource])
  have hfU_Ioo : f '' U = Ioo x y := (closure_eq_Icc_iff hfUOpen hfUConnected).mp hClosure_f
  have hxy' : x < y := by
    apply nonempty_Ioo.mp <| closure_nonempty_iff.mp ?_
    by_cases h : x = y
    · rw [show Ioo x y = ∅ by rw [h]; exact Ioo_self y] at hfU_Ioo
      exact False.elim <| (not_nonempty_iff_eq_empty.mpr hfU_Ioo) hfUConnected.nonempty
    · rw [closure_Ioo h]
      exact nonempty_Icc.mpr hxy
  -- Construct some β : OpenPartialHomeomorph ℝ ℝ sending univ to Ioo c d,
  -- and determine p ≠ q such that β p = a and β q = b
  have hcd : c < d :=
    nonempty_Ioo.mp <| nonempty_of_mem <| hInterval <| mem_Icc.mpr ⟨le_refl a, le_of_lt hab⟩
  haveI : Nonempty (Ioo c d) := nonempty_Ioo_subtype hcd
  let g : Ioo c d ≃ₜ ℝ := OpenIntervalHomeomorphReal.homeomorph_Ioo_real hcd
  obtain ⟨j, hjSource, hjTarget, hj_apply⟩ := incl_mk <| isOpen_Ioo (a := c) (b := d)
  let β : OpenPartialHomeomorph ℝ ℝ := by
    apply g.symm.toOpenPartialHomeomorph.trans' j
    rw [g.symm_toOpenPartialHomeomorph, OpenPartialHomeomorph.symm_target,
        g.toOpenPartialHomeomorph_source, hjSource]
  have hβSource : β.source = @univ ℝ := by
    simp only [β, OpenPartialHomeomorph.trans'_source, g.symm.toOpenPartialHomeomorph_source]
  have hβTarget : β.target = Ioo c d := by
    simp only [β, OpenPartialHomeomorph.trans'_target, hjTarget]
  have ha_cd : a ∈ Ioo c d :=
    mem_of_subset_of_mem hInterval <| mem_Icc.mpr ⟨le_refl a, le_of_lt hab⟩
  have hb_cd : b ∈ Ioo c d :=
    mem_of_subset_of_mem hInterval <| mem_Icc.mpr ⟨le_of_lt hab, le_refl b⟩
  let p : ℝ := β.symm a
  let q : ℝ := β.symm b
  have hpq : p ≠ q := by
    rw [← hβTarget] at ha_cd hb_cd
    exact β.symm.injOn.ne ha_cd hb_cd (ne_of_lt hab)
  -- f sends V → univ, and f '' closure U = Icc x y.  We want to find
  -- ψ : ℝ ≃ₜ ℝ with ψ x = p and ψ y = q, and then the composition
  -- β ∘ ψ ∘ f will send closure U to Icc a b
  obtain ⟨ψ, hψx, hψy⟩ := homeomorph_real_real_fix_two_points (ne_of_lt hxy') hpq
  let α : OpenPartialHomeomorph ℝ ℝ := by
    apply ψ.toOpenPartialHomeomorph.trans' β
    rw [ψ.toOpenPartialHomeomorph_target, hβSource]
  have hαSource : α.source = univ := by
    simp only [α, ψ.toOpenPartialHomeomorph.trans'_source, ψ.toOpenPartialHomeomorph_source]
  have hαTarget : α.target = Ioo c d := by
    simp only [α, ψ.toOpenPartialHomeomorph.trans'_target, hβTarget]
  obtain ⟨hαx, hαy⟩ : α x = a ∧ α y = b := by
    obtain ⟨hβpa, hβqb⟩ : β p = a ∧ β q = b := by
      constructor <;> exact β.right_inv (by rwa [hβTarget])
    simp only [OpenPartialHomeomorph.trans'_apply, ψ.toOpenPartialHomeomorph_apply, α]
    simp only [hψx, hψy, hβpa, hβqb, true_and]
  -- Now put it all together
  refine ⟨f.trans' α (by rw [hfTarget, hαSource]), ?_, ?_, ?_⟩
  · simp only [f.trans'_source, hfSource]
  · simp only [f.trans'_target, hαTarget]
  · simp_rw [f.trans'_apply, ← image_image, hIcc] -- goal: α '' Icc x y = Icc a b
    have hαIcc_source : Icc x y ⊆ α.source := by simp only [hαSource, subset_univ]
    have hαCont : ContinuousOn α (Icc x y) := α.continuousOn.mono hαIcc_source
    have hαInj : InjOn α (Icc x y) := α.injOn.mono hαIcc_source
    have hαx_le_αy : α x ≤ α y := by
      rw [hαx, hαy]
      exact le_of_lt hab
    apply Subset.antisymm
    · intro _ ⟨t, ht, hst⟩
      have hαMono : StrictMonoOn α (Icc x y) :=
        hαCont.strictMonoOn_of_injOn_Icc hxy hαx_le_αy hαInj
      have hαxt : α x ≤ α t := hαMono.monotoneOn (left_mem_Icc.mpr hxy) ht ht.1
      have hαty : α t ≤ α y := hαMono.monotoneOn ht (right_mem_Icc.mpr hxy) ht.2
      rw [← hst, ← hαx, ← hαy]
      exact mem_Icc.mpr ⟨hαxt, hαty⟩
    · exact fun _ hs => intermediate_value_Icc hxy hαCont (by rwa [hαx, hαy])

lemma openPartialHomeomorph_to_Ioo {X : Type*} [TopologicalSpace X]
    {U : Set X} (hUOpen : IsOpen U) (hUReal : Nonempty (U ≃ₜ ℝ))
    {a b : ℝ} (hab : a < b) :
    ∃ φ : OpenPartialHomeomorph X ℝ, φ.source = U ∧ φ.target = Ioo a b := by
  haveI : Nonempty U := Nonempty.intro <| hUReal.some.symm 0
  obtain ⟨α, hαSource, hαTarget, _⟩ := incl_mk hUOpen
  let β : OpenPartialHomeomorph X ℝ := α.symm.transHomeomorph hUReal.some
  have hβSource : β.source = U := by
    simp only [β, α.symm.transHomeomorph_source, α.symm_source, hαTarget]
  have hβTarget : β.target = univ := by
    simp only [β, α.symm.transHomeomorph_target, α.symm_target, hαSource, preimage_univ]
  let γ : Ioo a b ≃ₜ ℝ :=
    OpenIntervalHomeomorphReal.homeomorph_Ioo_real hab
  haveI : Nonempty (Ioo a b) := nonempty_Ioo_subtype hab
  have : IsOpen (Ioo a b) := isOpen_Ioo
  obtain ⟨δ, hδSource, hδTarget, hδ_apply⟩ := incl_mk this
  have : β.target = (δ.symm.transHomeomorph γ).symm.source := by
    simp only [hβTarget, OpenPartialHomeomorph.symm_source, δ.symm.transHomeomorph_target,
      δ.symm_target, hδSource, preimage_univ]
  let φ : OpenPartialHomeomorph X ℝ :=
    β.trans' (δ.symm.transHomeomorph γ).symm this
  have hφSource : φ.source = U := by
    simp only [φ, β.trans'_source, hβSource]
  have hφTarget : φ.target = Ioo a b := by
    simp only [φ, β.trans'_target, OpenPartialHomeomorph.symm_target,
      δ.symm.transHomeomorph_source, δ.symm_source, hδTarget]
  use φ

lemma mem_lt_mem_of_Ioo {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, ∃ d ∈ Ioo a b, c < d := by
  have hIoo {p q : ℝ} (hpq : p < q) : ∃ t : ℝ, t ∈ Ioo p q := by
    have : (Ioo p q).Nonempty := nonempty_Ioo.mpr hpq
    exact ⟨this.some, this.some_mem⟩
  obtain ⟨_, hat, htb⟩ := hIoo hab
  obtain ⟨c, hac, hct⟩ := hIoo hat
  obtain ⟨d, htd, hdb⟩ := hIoo htb
  refine ⟨c, ?_, d, ?_, lt_trans hct htd⟩
  · exact mem_Ioo.mpr ⟨hac, lt_trans hct htb⟩
  · exact mem_Ioo.mpr ⟨lt_trans hat htd, hdb⟩

/- Find a sequence of homeomorphisms ψ n : U n ≃ₜ Ioo -(n+1) (n+1), expressed
   as OpenPartialHomeomorph X ℝ, so that ψ n sends closure (U (n - 1)) to
   Icc -n n for each n > 0. -/
lemma increasing_interval_homeos {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hOpen : ∀ n, IsOpen (U n)) (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∃ ψ : ℕ → OpenPartialHomeomorph X ℝ, ∀ n,
      (ψ n).source = U n ∧ (ψ n).target = Ioo (- (n + 1) : ℝ) (n + 1) ∧
      (n > 0 → (ψ n) '' (closure (U (n - 1))) = Icc (- n : ℝ) n) := by
  have hConn : ∀ n, IsConnected (U n) := by
    intro n
    apply isConnected_iff_connectedSpace.mpr <| connectedSpace_iff_univ.mpr ?_
    exact (hReal n).some.symm.isConnected_preimage.mp <| isConnected_univ
  haveI : ∀ n, Nonempty (U n) := fun n => (hConn n).nonempty.to_subtype
  -- Start with U 0
  obtain ⟨φ₀, hφ₀Source, hφ₀Target⟩ :=
    openPartialHomeomorph_to_Ioo (hOpen 0) (hReal 0) <| neg_lt_self Real.zero_lt_one
  -- Now U n for n > 0
  have hSubset : ∀ n > 0, closure (U (n - 1)) ⊆ U n := by
    intro n hn
    have := hExhaustion (n - 1)
    rwa [Nat.sub_add_cancel hn] at this
  have hInterval {n : ℕ} (hn : n > 0) :
      Icc (- (n : ℝ)) n ⊆ Ioo (- ((n + 1) : ℝ)) (n + 1) := by
    refine Icc_subset_Ioo ?_ ?_
    · simp only [neg_add_rev, add_lt_iff_neg_right, Left.neg_neg_iff, zero_lt_one]
    · exact lt_add_one (n : ℝ)
  have hHomeo : ∀ n > 0, ∃ α : OpenPartialHomeomorph X ℝ,
      α.source = U n ∧ α.target = Ioo (- ((n + 1) : ℝ)) (n + 1) ∧
      α '' (closure (U (n - 1))) = Icc (- n : ℝ) n := by
    intro n hn
    obtain ⟨α, hαSource, hαTarget, hαImage⟩ := openPartialHomeomorph_real_fix_compact_Icc
        (hOpen (n - 1)) (hOpen n) (hPrecompact (n - 1)) (hConn (n - 1))
        (hSubset n hn) (hReal n)
        (neg_lt_self <| Nat.cast_pos'.mpr hn) (hInterval hn)
    use α
  use fun n => if hn : n > 0 then (hHomeo n hn).choose else φ₀
  intro n
  by_cases hn : n > 0
  · simp only [hn, ↓reduceDIte, true_implies]
    exact (hHomeo n hn).choose_spec
  · simp only [Nat.eq_zero_of_not_pos hn, lt_self_iff_false, false_implies, and_true,
      CharP.cast_eq_zero ℝ 0, zero_add]
    exact ⟨hφ₀Source, hφ₀Target⟩

/- Find a sequence of homeomorphisms ψ n : U n ≃ₜ Ioo -(n+1) (n+1), expressed
   as OpenPartialHomeomorph X ℝ, so that ψ n sends closure (U (n - 1)) to
   Icc -n n for each n > 0, and it sends closure (U (n - 2)) to
   Icc (-(n - 1)) (n - 1) for each n > 1. -/
lemma increasing_interval_homeos' {X : Type*} [TopologicalSpace X]
    {U : ℕ → Set X} (hOpen : ∀ n, IsOpen (U n)) (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∃ ψ : ℕ → OpenPartialHomeomorph X ℝ, ∀ n,
      (ψ n).source = U n ∧ (ψ n).target = Ioo (- ((n + 1) : ℝ)) (n + 1) ∧
      (n > 0 → (ψ n) '' (closure (U (n - 1))) = Icc (- n : ℝ) n) ∧
      (n > 1 → (ψ n) '' (closure (U (n - 2))) = Icc (- (n - 1) : ℝ) (n - 1)) := by
  obtain ⟨φ, hφ⟩ := increasing_interval_homeos hOpen hReal hPrecompact hExhaustion
  have find_α : ∀ (n : ℕ), n > 1 → ∃ α : OpenPartialHomeomorph X ℝ,
      (α.source = U n ∧ α.target = Ioo (- (n + 1) : ℝ) (n + 1) ∧
      α '' (closure (U (n - 1))) = Icc (-n : ℝ) n ∧
      α '' (closure (U (n - 2))) = Icc (-(n - 1) : ℝ) (n - 1)) := by
    intro n hn
    obtain ⟨_, _, hClosure₁⟩ := hφ (n - 1)
    specialize hClosure₁ (Nat.zero_lt_sub_of_lt hn)
    rw [← show n - 2 = n - 1 - 1 by exact Nat.sub_succ' n 1] at hClosure₁
    obtain ⟨hSource₀, hTarget₀, hClosure₀⟩ := hφ n
    specialize hClosure₀ (Nat.zero_lt_of_lt hn)
    have hClosure_subset : closure (U (n - 1)) ⊆ U n := by
      nth_rewrite 2 [← Nat.sub_add_cancel <| le_of_lt hn]
      exact hExhaustion (n - 1)
    have hContOn_closure : ContinuousOn (φ n) (closure (U (n - 1))) := by
      apply (φ n).continuousOn.mono
      rwa [hSource₀]
    have hImage_Ioo : (φ n) '' (U (n - 1)) = Ioo (- n : ℝ) n := by
      have : closure ((φ n) '' (U (n - 1))) = Icc (- n : ℝ) n := by
        rw [← hClosure₀]
        exact Eq.symm <| image_closure_of_isCompact (hPrecompact (n - 1)) hContOn_closure
      apply (closure_eq_Icc_iff ?_ ?_).mp this
      · apply (φ n).isOpen_image_of_subset_source (hOpen (n - 1)) ?_
        apply subset_trans subset_closure ?_
        rwa [hSource₀]
      · refine IsConnected.image ?_ ↑(φ n) ?_
        · apply isConnected_iff_connectedSpace.mpr <| connectedSpace_iff_univ.mpr ?_
          exact (hReal (n - 1)).some.symm.isConnected_preimage.mp isConnected_univ
        · exact hContOn_closure.mono subset_closure
    have hnsub2succ : n - 1 = n - 2 + 1 := Nat.eq_add_of_sub_eq (Nat.le_sub_one_of_lt hn) rfl
    obtain ⟨a, b, hab, hφIcc⟩ : ∃ a b : ℝ, a < b ∧ (φ n) '' (closure (U (n - 2))) = Icc a b := by
      have hsubSource : closure (U (n - 2)) ⊆ (φ n).source := by
        apply subset_trans (hExhaustion (n - 2)) ?_
        rw [← hnsub2succ, hSource₀]
        exact subset_trans subset_closure hClosure_subset
      have hCpct : IsCompact <| (φ n) '' (closure (U (n - 2))) :=
        (hPrecompact (n - 2)).image_of_continuousOn <| (φ n).continuousOn.mono hsubSource
      have hConn : IsConnected <| (φ n) '' (closure (U (n - 2))) := by
        refine IsConnected.image ?_ (φ n) ?_
        · refine IsConnected.closure ?_
          apply isConnected_iff_connectedSpace.mpr <| connectedSpace_iff_univ.mpr ?_
          exact (hReal (n - 2)).some.symm.isConnected_preimage.mp isConnected_univ
        · exact (φ n).continuousOn.mono hsubSource
      obtain ⟨a, b, hab, hφClosure⟩ := compact_real_classification hCpct hConn
      refine ⟨a, b, ?_, hφClosure⟩
      by_contra h
      replace hab : a = b := le_antisymm_iff.mpr ⟨hab, not_lt.mp h⟩
      rw [hab, Icc_self b] at hφClosure
      have hφb {x : X} : x ∈ U (n - 2) → (φ n) x = b := by
        intro hx
        apply mem_singleton_iff.mp
        rw [← hφClosure]
        exact mem_image_of_mem (φ n) <| subset_closure hx
      let f : ℝ ≃ₜ U (n - 2) := (hReal (n - 2)).some.symm
      have hfU (t : ℝ) : (f t).val ∈ U (n - 2) := Subtype.coe_prop (f t)
      have hf0_ne_f1 := hφb (hfU 0)
      rw [← hφb (hfU 1)] at hf0_ne_f1
      have hf0f1 : (f 0).val ≠ (f 1).val :=
        Subtype.coe_ne_coe.mpr <| f.injective.ne <| zero_ne_one' ℝ
      have : InjOn (φ n) (U (n - 2)) :=
        (φ n).injOn.mono <| subset_trans subset_closure hsubSource
      exact ((this.ne_iff (hfU 0) (hfU 1)).mpr hf0f1) hf0_ne_f1
    obtain ⟨han, hbn⟩ : a ∈ Ioo (- n : ℝ) n ∧ b ∈ Ioo (- n : ℝ) n := by
      have := image_mono (f := φ n) (hExhaustion (n - 2))
      rw [hφIcc, ← hnsub2succ, hImage_Ioo] at this
      constructor <;> apply mem_of_subset_of_mem this
      · exact left_mem_Icc.mpr <| le_of_lt hab
      · exact right_mem_Icc.mpr <| le_of_lt hab
    have h_neg_lt_self_nprec : - (n - 1 : ℝ) < n - 1 :=
      neg_lt_self <| sub_pos_of_lt <| Nat.one_lt_cast.mpr hn
    have h_nprec_neg_Ioo : - (n - 1 : ℝ) ∈ Ioo (- n : ℝ) n := by
      apply mem_Ioo.mpr ⟨?_, ?_⟩
      · simp only [neg_sub, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right, zero_lt_one]
      · exact lt_trans h_neg_lt_self_nprec (sub_one_lt (n : ℝ))
    have h_nprec_pos_Ioo : (n - 1 : ℝ) ∈ Ioo (- n : ℝ) n := by
      apply mem_Ioo.mpr ⟨neg_lt_sub_iff_lt_add.mpr ?_, sub_one_lt (n : ℝ)⟩
      have : 1 < (n : ℝ) := Nat.one_lt_cast.mpr hn
      exact lt_trans (lt_one_add 1) (add_lt_add this this)
    obtain ⟨g, hg_negn, hga, hgb, hb_posn, hg_Image, hg_id_compl⟩ :=
      real_homeomorph_interpolating_four_points
        han hbn h_nprec_neg_Ioo h_nprec_pos_Ioo hab h_neg_lt_self_nprec
    have hgMono : StrictMono g :=
      homeomorph_real_real_strictMono hab h_neg_lt_self_nprec hga hgb
    let φ' := (φ n).transHomeomorph g
    have hφ'Source : φ'.source = U n := by
      simp only [φ', (φ n).transHomeomorph_source, hSource₀]
    have hφ'Target : φ'.target = Ioo (- (n + 1) : ℝ) (n + 1) := by
      simp only [φ', (φ n).transHomeomorph_target, g.preimage_symm, hTarget₀]
      obtain ⟨hg_neg, hg_pos⟩ : g (- (n + 1 : ℝ)) = - (n + 1) ∧ g (n + 1 : ℝ) = n + 1 := by
        constructor <;> apply hg_id_compl <;> simp [mem_compl_iff, mem_Icc]
      rw [homeomorph_real_real_image_Ioo_of_strictMono hgMono, hg_neg, hg_pos]
    have hφ'Image₁ : φ' '' (closure (U (n - 1))) = Icc (- n : ℝ) n := by
      simp only [φ', (φ n).transHomeomorph_apply, image_comp, hClosure₀]
      exact hg_Image
    have hφ'Image₂ : φ' '' (closure (U (n - 2))) = Icc (- (n - 1) : ℝ) (n - 1) := by
      simp only [φ', (φ n).transHomeomorph_apply, image_comp, hφIcc]
      rw [homeomorph_real_real_image_Icc_of_strictMono hgMono, hga, hgb]
    use φ'
  use fun n => if h : n > 1 then (find_α n h).choose else φ n
  intro n
  by_cases h : n > 1 <;> simp only [h, ↓reduceDIte]
  · obtain ⟨_, _, _, _⟩ := (find_α n h).choose_spec
    refine ⟨?_, ?_, ?_, ?_⟩ <;> try assumption
    · simpa only [lt_trans Nat.one_pos h, true_implies]
    · simpa only [true_implies]
  · obtain ⟨_, _, _⟩ := hφ n
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (try assumption); simp only [false_implies]

lemma subset_of_increasing_chain {X : Type*} [TopologicalSpace X]
    {U : ℕ → Set X} (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∀ m n, m ≤ n → U m ⊆ U n := by
  have hInc : ∀ m n : ℕ, m < n → U m ⊆ U n := by
    let r : ℕ → ℕ → Prop := fun m n => U m ⊆ U n
    have : IsTrans ℕ r := { trans _ _ _ := subset_trans }
    exact fun m n hmn => Nat.rel_of_forall_rel_succ_of_lt
      r (fun n => subset_trans subset_closure <| hExhaustion n) hmn
  intro m n hmn
  by_cases h : m < n
  · exact hInc m n h
  · rcases not_lt_iff_eq_or_lt.mp h with heq | hle
    · simp only [heq, Subset.refl]
    · exact False.elim <| (lt_self_iff_false m).mp <| lt_of_le_of_lt hmn hle

/- Find a sequence of homeomorphisms ψ n : U n ≃ₜ Ioo -(n + 1) (n + 1),
   expressed as OpenPartialHomeomorph X ℝ, so that ψ n sends
   closure (U (n - 1)) to Icc -n n for each n > 0 and closure (U (n - 2)) to
   Icc -(n + 1) (n + 1) for each n > 1, and so that all ψ are compatibly
   oriented: there are points x y ∈ U 0 such that (ψ n) x < (ψ n) y for all n. -/
lemma increasing_oriented_interval_homeos {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hOpen : ∀ n, IsOpen (U n)) (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∃ ψ : ℕ → OpenPartialHomeomorph X ℝ, ∃ x ∈ U 0, ∃ y ∈ U 0, ∀ n,
      (ψ n) x < (ψ n) y ∧
      (ψ n).source = U n ∧ (ψ n).target = Ioo (- ((n + 1) : ℝ)) (n + 1) ∧
      (n > 0 → (ψ n) '' (closure (U (n - 1))) = Icc (- n : ℝ) n) ∧
      (n > 1 → (ψ n) '' (closure (U (n - 2))) = Icc (- (n - 1) : ℝ) (n - 1)) := by
  let α₀ := (hReal 0).some
  let x : X := (α₀.symm 0).val
  let y : X := (α₀.symm 1).val
  have hx : x ∈ U 0 := Subtype.coe_prop (α₀.symm 0)
  have hy : y ∈ U 0 := Subtype.coe_prop (α₀.symm 1)
  have hxy : x ≠ y := Subtype.coe_ne_coe.mpr <| α₀.symm.injective.ne <| zero_ne_one' ℝ
  obtain ⟨φ, hφ⟩ := increasing_interval_homeos' hOpen hReal hPrecompact hExhaustion
  use fun n => if (φ n) x < (φ n) y then φ n else (φ n).transHomeomorph (Homeomorph.neg ℝ)
  refine ⟨x, hx, y, hy, ?_⟩
  intro n
  by_cases hφn : (φ n) x < (φ n) y <;> simp_all only [↓reduceIte]
  · simp only [true_and, implies_true]
  · obtain ⟨hφSource, hφTarget, hφClosure, hφClosure₂⟩ := hφ n
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases not_lt_iff_eq_or_lt.mp hφn with h | h
      · obtain ⟨hx', hy'⟩ : x ∈ (φ n).source ∧ y ∈ (φ n).source := by
          rw [hφSource]
          have : U 0 ⊆ U n := subset_of_increasing_chain hExhaustion 0 n (Nat.zero_le n)
          exact ⟨this hx, this hy⟩
        exact False.elim <| hxy <| (φ n).injOn hx' hy' h
      · simpa only [(φ n).transHomeomorph_apply, comp_apply,
          Homeomorph.coe_neg, neg_lt_neg_iff] using h
    · simpa only [(φ n).transHomeomorph_source] using hφSource
    · simp only [(φ n).transHomeomorph_target, hφTarget, Homeomorph.symm_neg,
        Homeomorph.coe_neg, neg_add_rev, neg_preimage, neg_Ioo, neg_neg]
    · exact fun hn => by simp_rw [(φ n).transHomeomorph_apply, Homeomorph.coe_neg,
        comp_apply, ← image_image, hφClosure hn, image_neg_eq_neg, neg_Icc, neg_neg]
    · exact fun hn => by simp only [(φ n).transHomeomorph_apply, Homeomorph.coe_neg,
        image_comp, hφClosure₂ hn, neg_sub, image_neg_eq_neg, neg_Icc]

/- Given `φ ψ : OpenPartialHomeomorph X ℝ` which send a given closed set A in
   each source to the same interval `Icc a b`, if there are points x and y in
   A such that both `φ x < φ y` and `ψ x < ψ y` hold, then φ and ψ are equal
   on `frontier A`. -/
lemma openPartialHomeomorph_eqOn_frontier {X : Type*} [TopologicalSpace X]
    {A : Set X} (hAClosed : IsClosed A)
    {φ ψ : OpenPartialHomeomorph X ℝ} (hφA : A ⊆ φ.source) (hψA : A ⊆ ψ.source)
    {a b : ℝ} (hab : a ≤ b) (hφImage : φ '' A = Icc a b) (hψImage : ψ '' A = Icc a b)
    {x y : X} (hxA : x ∈ A) (hyA : y ∈ A) (hφxy : φ x < φ y) (hψxy : ψ x < ψ y) :
    EqOn φ ψ (frontier A) := by
  let β : OpenPartialHomeomorph ℝ ℝ := φ.symm.trans ψ
  let B := φ '' A
  have hB_βsource : B ⊆ β.source := by
    simp only [β, φ.symm.trans_source, φ.symm_source]
    have hB_target : B ⊆ φ.target := by
      rw [← φ.image_source_eq_target]
      apply image_mono hφA
    apply subset_inter hB_target ?_
    · refine image_subset_iff.mp ?_
      intro t ⟨s, hsV, hφs⟩
      subst t
      have htSource : φ.symm s ∈ φ.source := by
        rw [← φ.symm_target]
        exact φ.symm.map_source (hB_target hsV)
      have hφt : φ (φ.symm s) = s := φ.right_inv (hB_target hsV)
      apply mem_of_subset_of_mem hψA
      obtain ⟨_, hrU, hφr⟩ := hsV
      nth_rewrite 2 [← hφr] at hφt
      rwa [φ.injOn htSource (hφA hrU) hφt]
  have hMono : StrictMonoOn β (Icc a b) := by
    have hβCont : ContinuousOn β B := β.continuousOn.mono hB_βsource
    have hβInj : InjOn β B := β.injOn.mono hB_βsource
    simp_rw [B, hφImage] at hβCont hβInj
    have hMonoOn := ContinuousOn.strictMonoOn_of_injOn_Icc' hab hβCont hβInj
    have : ¬ StrictAntiOn β (Icc a b) := by
      let p : ℝ := φ x
      let q : ℝ := φ y
      obtain ⟨hpImage, hqImage⟩ : p ∈ φ '' A ∧ q ∈ φ '' A := by
        constructor <;> apply mem_image_of_mem <;> assumption
      obtain ⟨hxφ, hyφ⟩ : x ∈ φ.source ∧ y ∈ φ.source := by
        constructor <;> apply mem_of_subset_of_mem hφA <;> assumption
      obtain ⟨hβp, hβq⟩ : β p = ψ x ∧ β q = ψ y := by
        simp only [β, p, q, φ.symm.trans_apply, φ.left_inv hxφ, φ.left_inv hyφ, true_and]
      have hβpβq : β p < β q := by rwa [hβp, hβq]
      by_contra hAnti
      rw [← hφImage] at hAnti
      specialize hAnti hpImage hqImage hφxy
      exact (lt_self_iff_false (β p)).mp <| lt_trans hβpβq hAnti
    simpa only [this, or_false] using hMonoOn
  have ⟨hβa, hβb⟩ : β a = a ∧ β b = b := by
    have hβB : β '' B = B := by
      simp only [φ.symm.coe_trans, comp_apply, β]
      rw [← image_image ψ φ.symm B, φ.leftInvOn.image_image' hφA]
      simp only [B, hφImage, hψImage]
    have hBIcc : B = Icc a b := by simp only [B, hφImage]
    have hβB' : β '' (Icc a b) = Icc a b := by rwa [← hBIcc]
    have ⟨haβB, hbβB⟩ : a ∈ β '' B ∧ b ∈ β '' B := by
      rw [hBIcc, hβB']
      exact ⟨left_mem_Icc.mpr hab, right_mem_Icc.mpr hab⟩
    have hβImage {t : ℝ} : t ∈ Icc a b → β t ∈ Icc (β a) (β b) := by
      intro ht
      apply mem_Icc.mp ⟨?_, ?_⟩
      · exact hMono.monotoneOn (left_mem_Icc.mpr hab) ht ht.left
      · exact hMono.monotoneOn ht (right_mem_Icc.mpr hab) ht.right
    obtain ⟨r, hrB, hβr⟩ := haβB
    obtain ⟨s, hsB, hβs⟩ := hbβB
    rw [hBIcc] at hrB hsB
    obtain ⟨hβ_le_a, _⟩ := hβImage hrB
    obtain ⟨_, hβ_ge_b⟩ := hβImage hsB
    rw [hβr] at hβ_le_a
    rw [hβs] at hβ_ge_b
    obtain ⟨hβa_mem, hβb_mem⟩ : β a ∈ Icc a b ∧ β b ∈ Icc a b := by
      constructor <;> rw [← hβB'] <;> apply mem_image_of_mem β
      · exact left_mem_Icc.mpr hab
      · exact right_mem_Icc.mpr hab
    constructor
    · exact le_antisymm hβ_le_a hβa_mem.left
    · exact le_antisymm hβb_mem.right hβ_ge_b
  have hφIsImage : φ.IsImage A (Icc a b) := by
    rw [← hφImage]
    intro t ht
    constructor
    · exact fun ⟨_, hsA, hφs⟩ => by rwa [φ.injOn (hφA hsA) ht hφs] at hsA
    · exact fun h => mem_image_of_mem φ h
  have hsymm_EqOn : EqOn φ.symm ψ.symm (frontier (Icc a b)) := by
    rw [frontier_Icc hab]
    have hφsymm_ψ {c : ℝ} (hc : c ∈ Icc a b) : φ.symm c ∈ ψ.source := by
      apply mem_of_subset_of_mem hψA
      apply (hφIsImage.symm_apply_mem_iff ?_).mpr hc
      rw [← φ.image_source_eq_target]
      apply mem_of_subset_of_mem <| image_mono hφA
      rwa [hφImage]
    have hφψa := congrArg ψ.symm hβa
    have hφψb := congrArg ψ.symm hβb
    simp only [β, φ.symm.trans_apply, ψ.left_inv <| hφsymm_ψ <| left_mem_Icc.mpr hab] at hφψa
    simp only [β, φ.symm.trans_apply, ψ.left_inv <| hφsymm_ψ <| right_mem_Icc.mpr hab] at hφψb
    intro x hx
    by_cases h : x = a
    · rwa [h]
    · rwa [mem_singleton_iff.mp <| mem_of_mem_insert_of_ne hx h]
  intro t ht
  have htφSource : t ∈ φ.source :=
    mem_of_subset_of_mem (subset_trans hAClosed.frontier_subset hφA) ht
  have : φ t ∈ frontier (Icc a b) :=
    (hφIsImage.frontier.apply_mem_iff htφSource).mpr ht
  have htEq : ψ.symm (φ t) = φ.symm (φ t) := Eq.symm <| hsymm_EqOn this
  apply congrArg ψ at htEq
  simp only [φ.left_inv htφSource] at htEq
  have : φ t ∈ ψ.target := by
    rw [← ψ.image_source_eq_target]
    apply mem_of_subset_of_mem <| image_mono hψA
    rw [hψImage, ← hφImage]
    exact mem_image_of_mem φ (hAClosed.frontier_subset ht)
  simpa only [ψ.right_inv this] using htEq

private class homeoUn (X : Type*) [TopologicalSpace X] (U : ℕ → Set X) (n : ℕ) where
  φ : OpenPartialHomeomorph X ℝ
  hSource : φ.source = U n
  hTarget : φ.target = Ioo (- ((n + 1)) : ℝ) (n + 1)
  x : X
  y : X
  hx : x ∈ U 0
  hy : y ∈ U 0
  hxy : φ x < φ y
  hClosure₁ : n > 0 → φ '' (closure (U (n - 1))) = Icc (- n : ℝ) n
  hClosure₂ : n > 1 → φ '' (closure (U (n - 2))) = Icc (- (n - 1) : ℝ) (n - 1)

private instance homeoUn_mk {X : Type*} [TopologicalSpace X] (U : ℕ → Set X)
  (n : ℕ) (φ : OpenPartialHomeomorph X ℝ) (hSource : φ.source = U n)
  (hTarget : φ.target = Ioo (-((n + 1)) : ℝ) (n + 1))
  {x y : X} (hx : x ∈ U 0) (hy : y ∈ U 0) (hxy : φ x < φ y)
  (hClosure₁ : n > 0 → φ '' (closure (U (n - 1))) = Icc (-n : ℝ) n)
  (hClosure₂ : n > 1 → φ '' (closure (U (n - 2))) = Icc (-(n - 1) : ℝ) (n - 1)) :
  homeoUn X U n := {φ, hSource, hTarget, x, y, hx, hy, hxy, hClosure₁, hClosure₂}

/- Given an exhaustion of X by U : ℕ → Set X and OpenPartialHomeomorphs
   f : U n → (-n - 1, n + 1) and g : U (n - 1) → (-n, n) which both send
   closure (U (n - 2)) to [-(n-1), n-1], cut and paste to produce a new
   f' that agrees with g on closure (U (n - 2)) and with f everywhere else -/
lemma homeoUn_cut_and_paste {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    {n : ℕ} (hn : n > 1) (f : homeoUn X U n) (g : homeoUn X U (n - 1))
    (hx : f.x = g.x) (hy : f.y = g.y) (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∃ a : homeoUn X U n,
      EqOn a.φ g.φ (closure (U (n - 2))) ∧ EqOn a.φ f.φ (closure (U (n - 2)))ᶜ ∧
      a.x = f.x ∧ a.y = f.y := by
  have hImage₁ : f.φ '' (closure (U (n - 2))) = Icc (- (n - 1) : ℝ) (n - 1) := f.hClosure₂ hn
  have hImage₂ : g.φ '' (closure (U (n - 2))) = Icc (- (n - 1) : ℝ) (n - 1) := by
    have h := g.hClosure₁ <| Nat.zero_lt_sub_of_lt hn
    simp only [Nat.sub_succ' n 1, h, Nat.cast_pred <| Nat.zero_lt_of_lt hn]
  have hImageEq : f.φ '' (closure (U (n - 2))) = g.φ '' (closure (U (n - 2))) := by
    rw [hImage₁, hImage₂]
  have hclosure_Upred : closure (U (n - 2)) ⊆ U (n - 1) := by
    rw [show n - 1 = n - 2 + 1 by exact Nat.eq_add_of_sub_eq (Nat.le_sub_one_of_lt hn) rfl]
    exact hExhaustion (n - 2)
  have hUMonotone := subset_of_increasing_chain hExhaustion
  have hA₁ : closure (U (n - 2)) ⊆ f.φ.source := by
    apply subset_trans hclosure_Upred ?_
    rw [f.hSource]
    exact hUMonotone (n - 1) n <| Nat.sub_le n 1
  have hA₂ : closure (U (n - 2)) ⊆ g.φ.source := by rwa [g.hSource]
  have hFrontier : EqOn f.φ g.φ (frontier (closure (U (n - 2)))) := by
    have hIcc_le : - ((n : ℝ) - 1) ≤ (n : ℝ) - 1 := by
      apply neg_le_self
      simp only [sub_nonneg, Nat.one_le_cast, le_of_lt hn]
    obtain ⟨hxA, hyA⟩ : f.x ∈ closure (U (n - 2)) ∧ f.y ∈ closure (U (n - 2)):= by
      have := subset_trans (hUMonotone 0 (n - 2) <| Nat.le_sub_of_add_le hn) subset_closure
      exact ⟨this f.hx, this f.hy⟩
    have hgxy : g.φ f.x < g.φ f.y := by
      rw [hx, hy]
      exact g.hxy
    exact openPartialHomeomorph_eqOn_frontier isClosed_closure hA₁ hA₂
      hIcc_le hImage₁ hImage₂ hxA hyA f.hxy hgxy
  -- Cut and paste, then simplify the corresponding source and target info
  obtain ⟨ψ, hψSource, hψTarget, hEq₁, hEq₂⟩ :=
    openPartialHomeomorph_cut_and_paste isClosed_closure hA₂ hA₁ hFrontier.symm hImageEq.symm
  rw [f.hSource] at hψSource
  rw [f.hTarget] at hψTarget
  have hψxy : ψ f.x < ψ f.y := by
    obtain ⟨hgx, hgy⟩ : g.x ∈ closure (U (n - 2)) ∧ g.y ∈ closure (U (n - 2)) := by
      have hU := subset_trans (hUMonotone 0 (n - 2) <| Nat.le_sub_of_add_le hn) subset_closure
      have ⟨_, _⟩ : g.x ∈ U 0 ∧ g.y ∈ U 0 := ⟨g.hx, g.hy⟩
      constructor <;> apply mem_of_subset_of_mem hU <;> assumption
    rw [hx, hy, hEq₁ hgx, hEq₁ hgy]
    exact g.hxy
  have hClosure₂ : n > 1 → ψ '' closure (U (n - 2)) = Icc (-(n - 1 : ℝ)) (n - 1) := by
    intro _
    rw [image_congr hEq₁, Nat.sub_succ' n 1, g.hClosure₁ <| Nat.zero_lt_sub_of_lt hn]
    haveI : 1 ≤ n := Nat.one_le_of_lt hn
    simp_all only [Nat.cast_sub, Nat.cast_one]
  have hClosure₁ : n > 0 → ψ '' closure (U (n - 1)) = Icc (- (n : ℝ)) n := by
    intro _
    apply Subset.antisymm
    · intro t ⟨s, hsClosure, hst⟩
      by_cases h : s ∈ closure (U (n - 2))
      · have := mem_image_of_mem ψ h
        rw [hst, hClosure₂ hn] at this
        apply mem_of_subset_of_mem (Icc_subset_Icc ?_ ?_) this
        · simp only [neg_sub, neg_le_sub_iff_le_add, le_add_iff_nonneg_left, zero_le_one]
        · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le_one]
      · have := mem_image_of_mem f.φ hsClosure
        rwa [← hEq₂ h, hst, f.hClosure₁ (Nat.zero_lt_of_lt hn)] at this
    · intro t ht
      by_cases h : t ∈ Icc (-((n : ℝ) - 1)) (n - 1)
      · rw [← hClosure₂ hn] at h
        apply mem_of_subset_of_mem (image_mono ?_) h
        exact subset_trans hclosure_Upred subset_closure
      · obtain ⟨s, hs_ψSource, hψst⟩ : t ∈ ψ '' ψ.source := by
          rw [ψ.image_source_eq_target, hψTarget]
          apply mem_of_subset_of_mem (Icc_subset_Ioo ?_ ?_) ht
          · simp only [neg_add_rev, add_lt_iff_neg_right, Left.neg_neg_iff, zero_lt_one]
          · simp only [lt_add_iff_pos_right, zero_lt_one]
        rw [← hψst]
        apply mem_image_of_mem ψ
        by_contra hh
        have : s ∉ closure (U (n - 2)) := by
          have : closure (U (n - 2)) ⊆ closure (U (n - 1)) :=
            subset_trans hclosure_Upred subset_closure
          exact (mem_compl_iff (closure (U (n - 2))) s).mp fun a ↦ hh (this a)
        have hψs_eq_fs : ψ s = f.φ s := hEq₂ this
        have : f.φ s ∉ f.φ '' closure (U (n - 1)) := by
          by_contra hfs
          obtain ⟨r, hrClosure, hfrs⟩ := hfs
          have hr_φSource: r ∈ f.φ.source := by
            rw [f.hSource]
            apply mem_of_subset_of_mem (subset_trans (hExhaustion (n - 1)) ?_) hrClosure
            rw [Nat.sub_add_cancel <| Nat.zero_lt_of_lt hn]
          have hs_φSource : s ∈ f.φ.source := by rwa [f.hSource, ← hψSource]
          rw [f.φ.injOn hr_φSource hs_φSource hfrs] at hrClosure
          exact hh hrClosure
        rw [← hψs_eq_fs, hψst, f.hClosure₁ <| Nat.zero_lt_of_lt hn] at this
        exact this ht
  let f' := homeoUn_mk U n ψ hψSource hψTarget f.hx f.hy hψxy hClosure₁ hClosure₂
  rw [show ψ = f'.φ by rfl] at hEq₁ hEq₂
  exact ⟨f', hEq₁, hEq₂, rfl, rfl⟩

lemma stabilizing_interval_homeos {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hOpen : ∀ n, IsOpen (U n)) (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∃ ψ : ℕ → OpenPartialHomeomorph X ℝ, --∃ x ∈ U 0, ∃ y ∈ U 0,
      ∀ n, --(ψ n) x < (ψ n) y ∧
      (ψ n).source = U n ∧ (ψ n).target = Ioo (- ((n + 1) : ℝ)) (n + 1) ∧
      --(n > 0 → (ψ n) '' (closure (U (n - 1))) = Icc (- n : ℝ) n) ∧
      (n > 1 → EqOn (ψ n) (ψ (n - 1)) (closure (U (n - 2)))) := by
  obtain ⟨φ, x, hx, y, hy, hφ⟩ :=
    increasing_oriented_interval_homeos hOpen hReal hPrecompact hExhaustion
  have φClass : (n : ℕ) → homeoUn X U n := by
    intro n
    obtain ⟨hxy, hSource, hTarget, hClosure₁, hClosure₂⟩ := hφ n
    exact homeoUn_mk U n (φ n) hSource hTarget hx hy hxy hClosure₁ hClosure₂
  -- -- have {n n' : ℕ} (h1 : n > 1) (hn : n = n' + 1) : n > 1 := by
  -- --   exact Nat.lt_of_succ_le h1
  -- have stableHomeo (n : ℕ) : homeoUn X U n :=
  --   match n with
  --   | 0 => φClass 0
  --   | 1 => φClass 1
  --   | n' + 1 =>
  --     homeoUn_cut_and_paste (Nat.lt_of_succ_le _) (φClass n) (stableHomeo n')
  sorry

/- Given a strictly increasing chain f 0 ⊂ f 1 ⊂ f 2 ⊂ of subsets of X, there
   is a function g : ℕ → X such that each g n belongs to f n but not (assuming
   n ≠ 0) to f (n - 1). -/
lemma strictMono_subset_representatives {X : Type*} [TopologicalSpace X]
    (f : ℕ → Set X) (hNE : Nonempty (f 0)) (hfStrictMono : ∀ m n, m < n → f m ⊂ f n) :
    ∃ g : ℕ → X, ∀ n, (g n ∈ f n) ∧ (NeZero n → g n ∉ f (n - 1)) := by
  have nonempty_f_diff (n : ℕ) : n ≠ 0 → Nonempty {x : X | x ∈ f n \ f (n - 1)} := by
    intro hn
    have := hfStrictMono (n - 1) n (Nat.sub_one_lt hn)
    obtain ⟨_, x, hmem, hnotmem⟩ := ssubset_iff_exists.mp this
    exact ⟨x, mem_diff_of_mem hmem hnotmem⟩
  use fun n => if hn : n = 0 then hNE.some else (nonempty_f_diff n hn).some.val
  intro n
  by_cases hn : n = 0
  · simp only [imp_iff_not_or, not_neZero.mpr hn, Or.intro_left _ id, and_true]
    simp only [hn, ↓reduceDIte, Subtype.coe_prop]
  · simp only [setOf_mem_eq, hn, ↓reduceDIte, neZero_iff.mpr hn, true_implies]
    have mem_f_diff := (nonempty_f_diff n hn).some.property
    simp only [setOf_mem_eq] at mem_f_diff
    exact ⟨mem_of_mem_diff mem_f_diff, notMem_of_mem_diff mem_f_diff⟩

theorem homeomorph_real_of_union_real {X : Type*} [TopologicalSpace X]
    {U : ℕ → Set X} (hUnion : ⋃ n, U n = univ) (hOpen : ∀ n, IsOpen (U n))
    (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ)) (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    Nonempty (X ≃ₜ ℝ) := by
  apply Nonempty.intro <| (Homeomorph.Set.univ X).symm.trans ?_
  rw [← hUnion]

  -- let α₀ : ℝ ≃ₜ U 0 := (hReal 0).some.symm
  -- obtain ⟨φ₀ : U 0 ≃ₜ ℝ, hφ₀0, hφ₀1⟩ := homeomorph_open_real_fix_two_points
  --   (hReal 0) (fun h => zero_ne_one (α₀.injective h)) zero_ne_one
  -- have hNEf0 : Nonempty (U 0) := Nonempty.intro <| (hReal 0).some.symm 0
  -- obtain ⟨p, hp⟩ := strictMono_subset_representatives f hNEf0 hfStrictMono
  sorry
