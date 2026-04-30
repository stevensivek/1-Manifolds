import Mathlib.Tactic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import «OneManifold».RealLemmas

open Set Function Topology
set_option linter.style.emptyLine false

lemma homeomorph_real_real_fix_two_points {a b α β : ℝ} (hab : a ≠ b) (hαβ : α ≠ β) :
    ∃ f : ℝ ≃ₜ ℝ, f α = a ∧ f β = b := by
  let c := (a - b) / (α - β)
  let d := (b * α - a * β) / (α - β)
  have hαβ' : α - β ≠ 0 := sub_ne_zero_of_ne hαβ
  have hc : c ≠ 0 := div_ne_zero (sub_ne_zero_of_ne hab) hαβ'
  use affineHomeomorph c d hc
  simp only [affineHomeomorph_apply, c, d]
  field_simp
  constructor <;> ring

lemma homeomorph_open_real_fix_two_points {X : Type*} [TopologicalSpace X]
    {U : Set X} (hReal : Nonempty (U ≃ₜ ℝ)) {x y : U} (hxy : x ≠ y)
    {a b : ℝ} (hab : a ≠ b) :
    ∃ φ : U ≃ₜ ℝ, φ x = a ∧ φ y = b := by
  let ψ := hReal.some
  obtain ⟨f, hfα, hfβ⟩ := homeomorph_real_real_fix_two_points
    hab (fun h => hxy <| ψ.injective h)
  use ψ.trans f
  rw [ψ.trans_apply, ψ.trans_apply, ← hfα, ← hfβ]
  constructor <;> rfl

lemma choose_homeo {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUOpen : IsOpen U) (hVOpen : IsOpen V)
    (hUReal : Nonempty (U ≃ₜ ℝ)) (hVReal : Nonempty (V ≃ₜ ℝ))
    (hCompact : IsCompact (closure U)) (hSubset : closure U ⊆ V)
    {a b : ℝ} (hab : a < b) : ∃ φ : OpenPartialHomeomorph X ℝ,
      V ⊆ φ.source ∧ φ '' (closure U) = Icc a b := by
  haveI : Nonempty V := Nonempty.intro <| hVReal.some.symm 0
  have hUConn : IsConnected U := by
    apply isConnected_iff_connectedSpace.mpr <| connectedSpace_iff_univ.mpr ?_
    haveI : ConnectedSpace ℝ := Real.instPathConnectedSpace.connectedSpace
    let α : ℝ ≃ₜ U := hUReal.some.symm
    rw [← α.range_coe]
    exact isConnected_range α.continuous
  have hU'Conn : IsConnected (closure U) := hUConn.closure

  let α : V ≃ₜ ℝ := hVReal.some
  let inclV : OpenPartialHomeomorph V X :=
    hVOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  have hInclSource : inclV.source = @univ V := by
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_source]
  have hInclTarget : inclV.target = V := by
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact Subtype.range_coe_subtype
  have h : inclV.symm.target = α.toOpenPartialHomeomorph.source := by
    rw [inclV.symm_target, hInclSource, α.toOpenPartialHomeomorph_source]
  let f : OpenPartialHomeomorph X ℝ :=
    OpenPartialHomeomorph.trans' inclV.symm α.toOpenPartialHomeomorph h
  have hfSource : f.source = V := by
    rw [OpenPartialHomeomorph.trans'_source, inclV.symm_source, hInclTarget]

  have hfCont : ContinuousOn f (closure U) := by
    apply f.continuousOn.mono
    rwa [OpenPartialHomeomorph.trans'_source, inclV.symm_source, hInclTarget]
  have hfU'Compact : IsCompact (f '' (closure U)) := hCompact.image_of_continuousOn hfCont
  have hfU'Connected : IsConnected (f '' (closure U)) := hU'Conn.image f hfCont
  obtain ⟨c, d, hcd, hIcc⟩ := compact_real_classification hfU'Compact hfU'Connected
  have hfUOpen : IsOpen (f '' U) := by
    refine f.isOpen_image_of_subset_source hUOpen ?_
    rw [hfSource]
    exact Subset.trans subset_closure hSubset
  have hfUConnected : IsConnected (f '' U) := hUConn.image f (hfCont.mono subset_closure)
  have hClosure_f : closure (f '' U) = Icc c d := by
    rwa [← image_closure_of_isCompact hCompact hfCont]
  have hfU_Ioo : f '' U = Ioo c d := (closure_eq_Icc_iff hfUOpen hfUConnected).mp hClosure_f
  have hcd' : c < d := by
    apply nonempty_Ioo.mp
    rw [← hfU_Ioo]
    exact nonempty_of_mem <| mem_image_of_mem f <| Subtype.coe_prop (hUReal.some.symm 0)

  -- Now f '' U = Ioo c d.  We want φ : X → ℝ defined on V to send
  -- closure U to Icc a b.  We already have f : X → ℝ, so we want to
  -- postcompose with ψ such that ψ c = a and ψ d = b
  obtain ⟨ψ, hψc, hψd⟩ := homeomorph_real_real_fix_two_points (ne_of_lt hab) (ne_of_lt hcd')
  use f.trans ψ.toOpenPartialHomeomorph
  constructor
  · simp only [f.trans_source, ψ.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    rw [hfSource]
  · simp only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
      comp_apply, ← image_image, hIcc]
    rw [← hψc, ← hψd]
    rcases ψ.continuous.strictMono_of_inj ψ.injective with hMono | hAnti
    · apply Subset.antisymm
      · exact fun _ ⟨_, ht, hψt⟩ => mem_of_eq_of_mem (Eq.symm hψt)
          <| mem_Icc.mpr ⟨hMono.monotone ht.1, hMono.monotone ht.2⟩
      · exact intermediate_value_Icc hcd
          <| (continuousOn_univ.mpr ψ.continuous).mono (by apply subset_univ)
    · apply False.elim <| (lt_self_iff_false a).mp <| lt_trans hab ?_
      rw [← hψc, ← hψd]
      exact hAnti hcd'

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
    (f : ℕ → Set X) (hfOpen : ∀ n, IsOpen (f n)) (hfReal : ∀ n, Nonempty (f n ≃ₜ ℝ))
    (hfStrictMono : ∀ m n, m < n → f m ⊂ f n) :
    Nonempty (⋃ n, f n ≃ₜ ℝ) := by
  let α₀ : ℝ ≃ₜ f 0 := (hfReal 0).some.symm
  obtain ⟨φ₀ : f 0 ≃ₜ ℝ, hφ₀0, hφ₀1⟩ := homeomorph_open_real_fix_two_points
    (hfReal 0) (fun h => zero_ne_one (α₀.injective h)) zero_ne_one
  have hNEf0 : Nonempty (f 0) := Nonempty.intro <| (hfReal 0).some.symm 0
  obtain ⟨p, hp⟩ := strictMono_subset_representatives f hNEf0 hfStrictMono
  sorry
