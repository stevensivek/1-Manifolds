import Mathlib.Tactic -- import all the tactics

open Set

/- If x lies in an open set U ⊆ ℝ, then there are y, z ∈ U with y < x < z. -/
lemma lt_gt_of_open_interval {U : Set ℝ} (hUOpen : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    (∃ y ∈ U, y < x) ∧ (∃ z ∈ U, x < z) := by
  have hBasis := Real.isTopologicalBasis_Ioo_rat
  obtain ⟨V, hV, ⟨hxV, hVA⟩⟩ := hBasis.exists_subset_of_mem_open hx hUOpen
  simp only [mem_iUnion, mem_singleton_iff, exists_prop] at hV
  obtain ⟨a, b, _, _⟩ := hV
  subst V
  constructor
  · have hNE := nonempty_Ioo_subtype hxV.left
    have hyax : ↑hNE.some ∈ Ioo ↑a x := Subtype.coe_prop hNE.some
    use (hNE.some : ℝ)
    exact ⟨hVA <| (Ioo_subset_Ioo_right <| le_of_lt hxV.right) hyax, hyax.right⟩
  · have hNE := nonempty_Ioo_subtype hxV.right
    have hyxb : ↑hNE.some ∈ Ioo x ↑b := Subtype.coe_prop hNE.some
    use (hNE.some : ℝ)
    exact ⟨hVA <| (Ioo_subset_Ioo_left <| le_of_lt hxV.left) hyxb, hyxb.left⟩

/- An open set in ℝ cannot be of the form [a, ∞). -/
lemma not_Ici_of_open {U : Set ℝ} (hUOpen : IsOpen U) : ∀ a : ℝ, U ≠ Ici a := by
  intro a _
  subst U
  obtain ⟨⟨y, hyIci, hya⟩, _⟩ := lt_gt_of_open_interval hUOpen self_mem_Ici
  exact (lt_self_iff_false a).mp <| lt_of_le_of_lt hyIci hya

/- An open set in ℝ cannot be of the form (-∞, a]. -/
lemma not_Iic_of_open {U : Set ℝ} (hUOpen : IsOpen U) : ∀ a : ℝ, U ≠ Iic a := by
  intro a _
  subst U
  obtain ⟨_, ⟨z, hzIic, hza⟩⟩ := lt_gt_of_open_interval hUOpen self_mem_Iic
  exact (lt_self_iff_false a).mp <| lt_of_lt_of_le hza hzIic

/- A nonempty open set in ℝ cannot be of the form (a, b]. -/
lemma not_Ioc_of_open {U : Set ℝ} (hUOpen : IsOpen U) (hANonempty : U.Nonempty) :
    ∀ a b : ℝ, U ≠ Ioc a b := by
  intro a b _
  subst U
  have hab : a < b := nonempty_Ioc.mp hANonempty
  obtain ⟨_, ⟨z, hzIoc, hzb⟩⟩ := lt_gt_of_open_interval hUOpen <| right_mem_Ioc.mpr hab
  exact (lt_self_iff_false z).mp <| lt_of_le_of_lt hzIoc.right hzb

/- A nonempty open set in ℝ cannot be of the form [a, b). -/
lemma not_Ico_of_open {U : Set ℝ} (hUOpen : IsOpen U) (hUNonempty : U.Nonempty) :
    ∀ a b : ℝ, U ≠ Ico a b := by
  intro a b _
  subst U
  have hab : a < b := nonempty_Ico.mp hUNonempty
  obtain ⟨⟨y, hyIco, hya⟩, _⟩ := lt_gt_of_open_interval hUOpen <| left_mem_Ico.mpr hab
  exact (lt_self_iff_false a).mp <| lt_of_le_of_lt hyIco.left hya

/- A nonempty open set in ℝ cannot be of the form [a, b]. -/
lemma not_Icc_of_open {U : Set ℝ} (hUOpen : IsOpen U) (hANonempty : U.Nonempty) :
    ∀ a b : ℝ, U ≠ Icc a b := by
  intro a b _
  subst U
  have hab : a ≤ b := nonempty_Icc.mp hANonempty
  obtain ⟨⟨y, hyIcc, hya⟩, _⟩ := lt_gt_of_open_interval hUOpen <| left_mem_Icc.mpr hab
  exact (lt_self_iff_false y).mp <| lt_of_lt_of_le hya hyIcc.left

/- An nonempty, open, connected set in ℝ must have one of the following forms:
   (a, b), (-∞, a), (b, ∞), or ℝ. -/
lemma open_real_classification (U : Set ℝ) (hUOpen : IsOpen U) (hUConn : IsConnected U) :
    (∃ a b, U = Ioo a b) ∨ (∃ a, U = Iio a) ∨ (∃ b, U = Ioi b) ∨ (U = univ) := by
  have hRC := hUConn.isPreconnected.mem_intervals
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
             not_Icc_of_open hUOpen hUConn.nonempty (sInf U) (sSup U),
             not_Ico_of_open hUOpen hUConn.nonempty (sInf U) (sSup U),
             not_Ioc_of_open hUOpen hUConn.nonempty (sInf U) (sSup U),
             not_Ici_of_open hUOpen (sInf U),
             not_Iic_of_open hUOpen (sSup U),
             nonempty_iff_ne_empty.mp hUConn.nonempty, false_or, or_false] at hRC
  rcases hRC with h | h | h | h <;> rw [h]
  · simp only [exists_apply_eq_apply2', true_or]
  · simp only [exists_apply_eq_apply', true_or, or_true]
  · simp only [exists_apply_eq_apply', true_or, or_true]
  · simp only [or_true]

lemma compl_Icc {𝕜 : Type*} [LinearOrder 𝕜] {s t : 𝕜} : (Icc s t)ᶜ = (Iio s) ∪ (Ioi t) := by
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
