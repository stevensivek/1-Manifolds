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
   as OpenPartialHomeomorph X ℝ, so that ψ n sends closure (U (n-1)) to
   Icc -n n for each n > 0. -/
lemma increasing_interval_homeos {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hOpen : ∀ n, IsOpen (U n)) (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∃ ψ : ℕ → OpenPartialHomeomorph X ℝ, ∀ n,
      (ψ n).source = U n ∧ (ψ n).target = Ioo (- ((n + 1) : ℝ)) (n + 1) ∧
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

/- Find a sequence of homeomorphisms ψ n : U n ≃ₜ Ioo -(n+1) (n+1), expressed
   as OpenPartialHomeomorph X ℝ, so that ψ n sends closure (U (n-1)) to
   Icc -n n for each n > 0, and so that all ψ are compatibly oriented: there
   are points x y ∈ U 0 such that (ψ n) x < (ψ n) y for all n. -/
lemma increasing_oriented_interval_homeos {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hOpen : ∀ n, IsOpen (U n)) (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1)) :
    ∃ ψ : ℕ → OpenPartialHomeomorph X ℝ, ∃ x ∈ U 0, ∃ y ∈ U 0, ∀ n,
      (ψ n) x < (ψ n) y ∧
      (ψ n).source = U n ∧ (ψ n).target = Ioo (- ((n + 1) : ℝ)) (n + 1) ∧
      (n > 0 → (ψ n) '' (closure (U (n - 1))) = Icc (- n : ℝ) n) := by
  let α₀ := (hReal 0).some
  let x : X := (α₀.symm (-1)).val
  let y : X := (α₀.symm 1).val
  have hx : x ∈ U 0 := Subtype.coe_prop (α₀.symm (-1))
  have hy : y ∈ U 0 := Subtype.coe_prop (α₀.symm 1)
  have hxy : x ≠ y := by
    apply Subtype.coe_ne_coe.mpr <| α₀.symm.injective.ne ?_
    exact ne_of_lt <| neg_lt_self Real.zero_lt_one
  obtain ⟨φ, hφ⟩ := increasing_interval_homeos hOpen hReal hPrecompact hExhaustion
  use fun n => if (φ n) x < (φ n) y then φ n else (φ n).transHomeomorph (Homeomorph.neg ℝ)
  refine ⟨x, hx, y, hy, ?_⟩
  intro n
  by_cases hφn : (φ n) x < (φ n) y <;> simp_all only [↓reduceIte]
  · simp only [true_and, implies_true]
  · obtain ⟨hφSource, hφTarget, hφClosure⟩ := hφ n
    refine ⟨?_, ?_, ?_, ?_⟩
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

lemma stabilizing_interval_homeos {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : ℕ → Set X} (hOpen : ∀ n, IsOpen (U n)) (hReal : ∀ n, Nonempty (U n ≃ₜ ℝ))
    (hPrecompact : ∀ n, IsCompact (closure (U n)))
    (hExhaustion : ∀ n, closure (U n) ⊆ U (n + 1))
    {n : ℕ} : n > 1 → False := by
  obtain ⟨φ, x, hx, y, hy, hφ⟩ := increasing_oriented_interval_homeos
    hOpen hReal hPrecompact hExhaustion
  replace hx : ∀ n, x ∈ U n :=
    fun n => subset_of_increasing_chain hExhaustion 0 n (Nat.zero_le n) hx
  replace hy : ∀ n, y ∈ U n :=
    fun n => subset_of_increasing_chain hExhaustion 0 n (Nat.zero_le n) hy
  --
  intro hn
  obtain ⟨_, _, _, hClosure₁⟩ := hφ (n - 1)
  specialize hClosure₁ (Nat.zero_lt_sub_of_lt hn)
  rw [← show n - 2 = n - 1 - 1 by exact Nat.sub_succ' n 1] at hClosure₁
  obtain ⟨_, hSource₀, hTarget₀, hClosure₀⟩ := hφ n
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
    have : 1 < (n : ℝ) := by exact Nat.one_lt_cast.mpr hn
    exact lt_trans (lt_one_add 1) (add_lt_add this this)
  obtain ⟨g, hg_negn, hga, hgb, hb_posn, hg_Image, hg_id_compl⟩ :=
    real_homeomorph_interpolating_four_points
      han hbn h_nprec_neg_Ioo h_nprec_pos_Ioo hab h_neg_lt_self_nprec
  let φ' := (φ n).transHomeomorph g
  have : φ'.source = U n := by simp only [φ', (φ n).transHomeomorph_source, hSource₀]
  have : φ'.target = (φ n).target := by
    simp only [φ', (φ n).transHomeomorph_target, g.preimage_symm, hTarget₀]
    apply Subset.antisymm
    · intro t ⟨s, hsIoo, hgs⟩
      by_cases h : s ∈ Icc (- n : ℝ) n
      · sorry
      · rwa [← hgs, hg_id_compl s h]
    · sorry

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
