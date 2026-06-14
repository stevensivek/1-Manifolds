import Mathlib.Tactic -- import all the tactics

open Set

/- If x lies in an open set s of a densely ordered space with no minimal
   elements, then s contains an element y < x. -/
lemma exists_mem_lt_of_mem_of_open {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMinOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) {x : α} (hx : x ∈ s) :
    ∃ y ∈ s, y < x := by
  obtain ⟨t, htx, hIoc⟩ := exists_Ioc_subset_of_mem_nhds (hsOpen.mem_nhds hx) (exists_lt x)
  obtain ⟨a, hta, hax⟩ := exists_between htx
  exact ⟨a, mem_of_subset_of_mem hIoc <| mem_Ioc.mpr ⟨hta, le_of_lt hax⟩, hax⟩

/- If x lies in an open set s of a densely ordered space with no maximal
   elements, then s contains an element z > x. -/
lemma exists_mem_gt_of_mem_of_open {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMaxOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) {x : α} (hx : x ∈ s) :
    ∃ z ∈ s, x < z := by
  obtain ⟨t, htx, hIco⟩ := exists_Ico_subset_of_mem_nhds (hsOpen.mem_nhds hx) (exists_gt x)
  obtain ⟨a, hxa, hat⟩ := exists_between htx
  exact ⟨a, mem_of_subset_of_mem hIco <| mem_Ico.mpr ⟨le_of_lt hxa, hat⟩, hxa⟩

/- If x lies in an open set s of a densely ordered space with no maximal or
   minimal elements, then there are y, z ∈ s with y < x < z. -/
lemma lt_gt_of_open_interval {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMinOrder α] [NoMaxOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) {x : α} (hx : x ∈ s) :
    (∃ y ∈ s, y < x) ∧ (∃ z ∈ s, x < z) :=
  ⟨exists_mem_lt_of_mem_of_open hsOpen hx, exists_mem_gt_of_mem_of_open hsOpen hx⟩

/- An open set in a densely ordered space with no minimal elements cannot be
   of the form [a, ∞). -/
lemma not_Ici_of_open {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMinOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) : ∀ a : α, s ≠ Ici a := by
  intro a _
  subst s
  obtain ⟨_, hyIci, hya⟩ := exists_mem_lt_of_mem_of_open hsOpen self_mem_Ici
  exact (lt_self_iff_false a).mp <| lt_of_le_of_lt hyIci hya

/- An open set in a densely ordered space with no maximal elements cannot be
   of the form (-∞, a]. -/
lemma not_Iic_of_open {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMaxOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) : ∀ a : α, s ≠ Iic a := by
  intro a _
  subst s
  obtain ⟨_, hzIic, hza⟩ := exists_mem_gt_of_mem_of_open hsOpen self_mem_Iic
  exact (lt_self_iff_false a).mp <| lt_of_lt_of_le hza hzIic

/- A nonempty open set in a densely ordered space with no maximal elements
   cannot be of the form (a, b]. -/
lemma not_Ioc_of_open {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMaxOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) (hNE : s.Nonempty) : ∀ a b : α, s ≠ Ioc a b := by
  intro a b _
  subst s
  obtain ⟨y, hyIoc, hyb⟩ := exists_mem_gt_of_mem_of_open hsOpen
                            <| right_mem_Ioc.mpr (nonempty_Ioc.mp hNE)
  exact (lt_self_iff_false y).mp <| lt_of_le_of_lt hyIoc.right hyb

/- A nonempty open set in a densely ordered space with no minimal elements
   cannot be of the form [a, b). -/
lemma not_Ico_of_open {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMinOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) (hNE : s.Nonempty) : ∀ a b : α, s ≠ Ico a b := by
  intro a b _
  subst s
  obtain ⟨y, hyIco, hya⟩ := exists_mem_lt_of_mem_of_open hsOpen
                            <| left_mem_Ico.mpr (nonempty_Ico.mp hNE)
  exact (lt_self_iff_false a).mp <| lt_of_le_of_lt hyIco.left hya

/- A nonempty open set in a densely ordered space with no maximal elements
   cannot be of the form [a, b]. -/
lemma not_Icc_of_open {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMaxOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) (hNE : s.Nonempty) : ∀ a b : α, s ≠ Icc a b := by
  intro a b _
  subst s
  obtain ⟨y, hyIoc, hyb⟩ := exists_mem_gt_of_mem_of_open hsOpen
                            <| right_mem_Icc.mpr (nonempty_Icc.mp hNE)
  exact (lt_self_iff_false y).mp <| lt_of_le_of_lt hyIoc.right hyb

/- An open, connected subset of a conditionally complete, densely ordered space
   with no minimal or maximal elements must have one of the following forms:
   (a, b), (-∞, a), (b, ∞), or univ. -/
lemma open_interval_classification {α : Type*}
    [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
    [NoMinOrder α] [NoMaxOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hsOpen : IsOpen s) (hsConn : IsConnected s) :
    (∃ a b, s = Ioo a b) ∨ (∃ a, s = Iio a) ∨ (∃ b, s = Ioi b) ∨ (s = univ) := by
  have hRC := hsConn.isPreconnected.mem_intervals
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
             not_Icc_of_open hsOpen hsConn.nonempty (sInf s) (sSup s),
             not_Ico_of_open hsOpen hsConn.nonempty (sInf s) (sSup s),
             not_Ioc_of_open hsOpen hsConn.nonempty (sInf s) (sSup s),
             not_Ici_of_open hsOpen (sInf s),
             not_Iic_of_open hsOpen (sSup s),
             nonempty_iff_ne_empty.mp hsConn.nonempty, false_or, or_false] at hRC
  rcases hRC with h | h | h | h <;> rw [h]
  · simp only [exists_apply_eq_apply2', true_or]
  · simp only [exists_apply_eq_apply', true_or, or_true]
  · simp only [exists_apply_eq_apply', true_or, or_true]
  · simp only [or_true]

/- A nonempty, open, connected set in ℝ must have one of the following forms:
   (a, b), (-∞, a), (b, ∞), or ℝ. -/
lemma open_real_classification {U : Set ℝ} (hUOpen : IsOpen U) (hUConn : IsConnected U) :
    (∃ a b, U = Ioo a b) ∨ (∃ a, U = Iio a) ∨ (∃ b, U = Ioi b) ∨ (U = univ) :=
  open_interval_classification hUOpen hUConn

lemma isIcc_of_compact_ordConnected {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {s : Set α}
    (hsCompact : IsCompact s) (hsConn : s.OrdConnected) (hsNE : s.Nonempty) :
    ∃ a b : α, (a ≤ b ∧ s = Icc a b) := by
  refine ⟨sInf s, sSup s, ?_, Subset.antisymm ?_ ?_⟩
  · exact csInf_le hsCompact.bddBelow (hsCompact.sSup_mem hsNE)
  · exact subset_Icc_csInf_csSup hsCompact.bddBelow hsCompact.bddAbove
  · exact OrdConnected.out' (hsCompact.sInf_mem hsNE) (hsCompact.sSup_mem hsNE)

lemma compact_real_classification {U : Set ℝ}
    (hUCompact : IsCompact U) (hUConn : IsConnected U) :
    ∃ a b : ℝ, (a ≤ b ∧ U = Icc a b) := by
  apply isIcc_of_compact_ordConnected hUCompact ?_ hUConn.nonempty
  exact isPreconnected_iff_ordConnected.mp hUConn.isPreconnected

lemma Iic_ne_Icc {a b c : ℝ} : Iic a ≠ Icc b c := by
  let d : ℝ := min a b - 1
  have : d ∈ Iic a := by
    apply mem_Iic.mpr <| le_of_lt ?_
    exact lt_of_le_of_lt (tsub_le_tsub_right (min_le_left a b) 1) (sub_one_lt a)
  apply Membership.mem.ne_of_notMem' this <| notMem_Icc_of_lt ?_
  exact lt_of_le_of_lt (tsub_le_tsub_right (min_le_right a b) 1) (sub_one_lt b)

lemma Ici_ne_Icc {a b c : ℝ} : Ici a ≠ Icc b c := by
  let d : ℝ := max a c + 1
  have : d ∈ Ici a := by
    apply mem_Ici.mpr <| le_of_lt ?_
    exact lt_of_lt_of_le (lt_add_one a) (add_le_add_left (le_max_left a c) 1)
  apply Membership.mem.ne_of_notMem' this <| notMem_Icc_of_gt ?_
  exact lt_of_lt_of_le (lt_add_one c) <| add_le_add_left (le_max_right a c) 1

lemma Icc_ne_univ {a b : ℝ} : Icc a b ≠ univ := by
  have : b + 1 ∉ Icc a b := notMem_Icc_of_gt <| lt_add_one b
  exact Ne.symm <| Membership.mem.ne_of_notMem' (mem_univ (b + 1)) this

lemma closure_eq_Icc_iff {U : Set ℝ} (hOpen : IsOpen U) (hConnected : IsConnected U)
    {a b : ℝ} : closure U = Icc a b ↔ U = Ioo a b := by
  constructor <;> intro hU
  · rcases open_real_classification hOpen hConnected with h | h | h | h
    · obtain ⟨c, d, hIoo⟩ := h
      by_cases hcd : c < d
      · rw [hIoo, closure_Ioo <| ne_of_lt hcd] at hU
        obtain ⟨hca, hdb⟩ := (Icc_eq_Icc_iff <| le_of_lt hcd).mp hU
        rwa [← hca, ← hdb]
      · rw [Ioo_eq_empty_of_le <| not_lt.mp hcd] at hIoo
        apply False.elim <| (not_nonempty_iff_eq_empty.mpr hIoo) hConnected.nonempty
    · obtain ⟨a, hIio⟩ := h
      rw [hIio, closure_Iio] at hU
      exact False.elim <| Iic_ne_Icc hU
    · obtain ⟨b, hIoi⟩ := h
      rw [hIoi, closure_Ioi] at hU
      exact False.elim <| Ici_ne_Icc hU
    · rw [h, closure_univ] at hU
      exact False.elim <| (Ne.symm Icc_ne_univ) hU
  · rw [hU] at hConnected ⊢
    exact closure_Ioo <| ne_of_lt <| nonempty_Ioo.mp hConnected.nonempty

lemma compl_Icc {α : Type*} [LinearOrder α] {s t : α} : (Icc s t)ᶜ = (Iio s) ∪ (Ioi t) := by
  apply compl_inj_iff.mp
  rw [compl_compl, compl_union, compl_Iio, compl_Ioi]
  rfl

variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
                     [Preorder 𝕜] [OrderedSub 𝕜] [AddRightMono 𝕜]

def iicHomeo_iic0 (t : 𝕜) : Iic t ≃ₜ Iic (0 : 𝕜) := {
    toFun := fun x => ⟨x.val - t, (tsub_nonpos (b := t)).mpr x.property⟩,
    invFun := fun x => ⟨x.val + t, add_le_of_nonpos_left x.property (a := t)⟩,
    left_inv := fun _ => by simp_all only [sub_add_cancel],
    right_inv := fun _ => by simp_all only [add_sub_cancel_right],
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact Continuous.sub continuous_subtype_val continuous_const,
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact Continuous.add continuous_subtype_val continuous_const
  }

def iciHomeo_ici0 (t : 𝕜) : Ici t ≃ₜ Ici (0 : 𝕜) := {
    toFun := fun x => ⟨x.val - t, sub_nonneg_of_le (b := t) x.property⟩,
    invFun := fun x => ⟨x.val + t, le_add_of_nonneg_left x.property (a := t)⟩,
    left_inv := fun _ => by simp_all only [sub_add_cancel],
    right_inv := fun _ => by simp_all only [add_sub_cancel_right],
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact Continuous.sub continuous_subtype_val continuous_const,
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact Continuous.add continuous_subtype_val continuous_const
  }

noncomputable def icc_flip {a b : ℝ} (h : a < b) : Icc a b ≃ₜ Icc a b := by
  exact ((iccHomeoI a b h).trans unitInterval.symmHomeomorph).trans (iccHomeoI a b h).symm

lemma iccHomeoI_left {a b : ℝ} (h : a < b) :
    (iccHomeoI a b h) ⟨a, left_mem_Icc.mpr <| le_of_lt h⟩ = 0 := by
  simp_all only [iccHomeoI, Homeomorph.symm_trans_apply]
  apply Icc.coe_eq_zero.mp
  simp_all only [Homeomorph.image_symm_apply_coe, affineHomeomorph_symm_apply, div_eq_zero_iff]
  simp only [Ne.symm <| ne_of_lt <| sub_pos.mpr h, or_false]
  apply sub_self

lemma iccHomeoI_right {a b : ℝ} (h : a < b) :
    (iccHomeoI a b h) ⟨b, right_mem_Icc.mpr <| le_of_lt h⟩ = 1 := by
  simp_all only [iccHomeoI, Homeomorph.symm_trans_apply]
  apply Icc.coe_eq_one.mp
  simp_all only [Homeomorph.image_symm_apply_coe, affineHomeomorph_symm_apply]
  apply (div_eq_one_iff_eq <| Ne.symm <| ne_of_lt <| sub_pos.mpr h).mpr
  exact sub_left_inj.mpr rfl

lemma icc_flip_symm {a b : ℝ} (h : a < b) : (icc_flip h).symm = icc_flip h := by ext; rfl

lemma icc_flip_left {a b : ℝ} (h : a < b) :
    (icc_flip h) ⟨a, left_mem_Icc.mpr <| le_of_lt h⟩ = b := by
  simp_all only [icc_flip, Homeomorph.trans_apply, iccHomeoI_symm_apply_coe]
  apply add_eq_of_eq_sub
  nth_rewrite 2 [← MulOneClass.mul_one (b - a)]
  apply (mul_left_cancel_iff_of_pos <| sub_pos.mpr h).mpr
  simp only [Icc.coe_eq_one]
  exact unitInterval.symm_eq_one.mpr <| iccHomeoI_left h

lemma icc_flip_right {a b : ℝ} (h : a < b) :
    (icc_flip h) ⟨b, right_mem_Icc.mpr <| le_of_lt h⟩ = a := by
  simp_all only [icc_flip, Homeomorph.trans_apply, iccHomeoI_symm_apply_coe]
  apply Eq.symm
  apply right_eq_add.mpr
  apply (mul_eq_zero_iff_left <| Ne.symm <| ne_of_lt <| sub_pos.mpr h).mpr
  simp only [Icc.coe_eq_zero]
  exact unitInterval.symm_eq_zero.mpr <| iccHomeoI_right h
