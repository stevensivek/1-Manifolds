import Mathlib.Tactic

open Set Topology Function

variable (X : Type*) [TopologicalSpace X] [LocallyConnectedSpace X]

def CCM (c : ConnectedComponents X) : Set X := ConnectedComponents.mk ⁻¹' {c}

lemma isOpen_iff_IsOpen_in_components : ∀ U : Set X, (IsOpen U ↔
      ∀ c : ConnectedComponents X, IsOpen (U ∩ ConnectedComponents.mk ⁻¹' {c})) := by
  intro U
  constructor <;> intro h
  · exact fun c ↦ h.inter <| isOpen_coinduced.mp <| isOpen_discrete {c}
  · have : U = ⋃ c : ConnectedComponents X, U ∩ (ConnectedComponents.mk ⁻¹' {c}) := by
      rw [← inter_iUnion, ← preimage_iUnion, iUnion_of_singleton, preimage_univ, inter_univ]
    rw [this]
    exact isOpen_iUnion h

omit [LocallyConnectedSpace X] in
lemma pairwise_disjoint_components : Pairwise
    (Disjoint on (fun (c : ConnectedComponents X) => ConnectedComponents.mk ⁻¹' {c})) := by
  unfold Pairwise
  intro _ _ hcd _ hsc hsd x hx
  have hmk_x {α : ConnectedComponents X} : x ∈ ConnectedComponents.mk ⁻¹' {α} →
      ConnectedComponents.mk x = α := by
    exact fun hx => mem_singleton_iff.mp <| mem_preimage.mp hx
  have := hmk_x (hsd hx)
  exact hcd (by rwa [hmk_x (hsc hx)] at this)

noncomputable def equiv_univ_union :
    (@univ X) ≃ₜ ⋃ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} := by
  have : ⋃ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} = univ := by
    apply univ_subset_iff.mp
    intro x ?_
    apply mem_iUnion.mpr
    use ConnectedComponents.mk x
    exact Setoid.ker_iff_mem_preimage.mp rfl
  rw [this]
  exact Homeomorph.refl univ

noncomputable def f : ⋃ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} ≃
    Σ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} :=
  unionEqSigmaOfDisjoint <| pairwise_disjoint_components X

-- omit [LocallyConnectedSpace X] in
-- lemma lf (U : Set (Σ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c})) :
--     IsOpen U ↔ ∀ (c : ConnectedComponents X), IsOpen (Sigma.mk c ⁻¹' U) := by
--   exact isOpen_sigma_iff
-- lemma lf' (U : Set (Σ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c})) :
--     IsOpen U ↔ IsOpen ((f X) ⁻¹' U) := by
--   apply Iff.trans isOpen_sigma_iff ?_
--   constructor
--   · intro hi
--     sorry
--   · intro hf c
--     let t : ConnectedComponents X → Set X := fun c => (Sigma.mk c (β := CCM X c)) ⁻¹' U
--     have : Sigma.mk c ⁻¹' U = {x : CCM X c} := by
--     --have : U = ⋃ (c : ConnectedComponents X), (Sigma.mk c) '' {x : CCM X c | ↑x ∈ U}



-- noncomputable def equiv_univ_sum_components :
--     (@univ X) ≃ Σ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} := by
--   exact (equiv_univ_union X).toEquiv.trans
--         (unionEqSigmaOfDisjoint <| pairwise_disjoint_components X)

-- lemma LL : Continuous (equiv_univ_sum_components X) := by
--   simp only [equiv_univ_sum_components]
--   -- have : Continuous (equiv_univ_union X).toEquiv := by
--   --   exact (continuous_congr (congrFun rfl)).mp (equiv_univ_union X).continuous
--   simp only [Equiv.coe_trans, Homeomorph.coe_toEquiv, Homeomorph.comp_continuous_iff']
--   apply continuous_def.mpr
--   intro s hs
--   sorry



-- noncomputable def equiv_sum_components :
--     X ≃ Σ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} := by
--   exact (Homeomorph.Set.univ X).symm.toEquiv.trans <| (equiv_univ_sum_components X)

-- private noncomputable def φ := equiv_univ_sum_components
-- private noncomputable def CCM (c : ConnectedComponents X) : Set X :=
--   ConnectedComponents.mk ⁻¹' {c}
-- private def Smk {c : ConnectedComponents X} := (Sigma.mk c (β := fun c => CCM X c))

-- private lemma hφ_fst (x : X) : (φ X ⟨x, mem_univ x⟩).fst = ConnectedComponents.mk x := by
--   have hx : x ∈ ⋃ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} := by
--     exact mem_iUnion_of_mem (ConnectedComponents.mk x) rfl
--   let c := ConnectedComponents.mk x
--   have hc : x ∈ CCM X c := mem_preimage.mp rfl
--   have hφ_apply : (φ X) ⟨x, mem_univ x⟩ = Sigma.mk c ⟨x, hc⟩ := by
--     simp only [φ, equiv_univ_sum_components]

--     exact (Equiv.apply_eq_iff_eq_symm_apply
--                 (unionEqSigmaOfDisjoint (pairwise_disjoint_components X))).mpr rfl
--   have : (φ ⟨x, hx⟩).fst = c := by rw [hψ_apply]
--   have : ↑(φ ⟨x, hx⟩).snd = x := by rw [hψ_apply]
--   sorry

-- -- private lemma hφsymm_apply_fst (x : X) : (φ X x).fst = ConnectedComponents.mk x := by
-- --   let c := ConnectedComponents.mk x
-- --   have := coe_unionEqSigmaOfDisjoint_symm_apply (pairwise_disjoint_components X)
-- --   simp only [φ, equiv_sum_components]
-- --   apply (unionEqSigmaOfDisjoint (pairwise_disjoint_components X)).symm_apply_eq.mp

-- --   apply (Homeomorph.Set.univ X).symm_apply_eq.mpr
-- --   simp only [φ, equiv_sum_components, Equiv.trans_apply, Homeomorph.coe_toEquiv]


-- --   sorry

-- --   exact Equiv.sigmaPreimageEquiv_symm_apply_fst ConnectedComponents.mk x
-- -- have hψsymm_apply_snd_coe (x : M) : ↑(ψ.symm x).snd = x := by
-- --   exact Equiv.sigmaPreimageEquiv_symm_apply_snd_coe ConnectedComponents.mk x

-- private lemma hφ_fst (x : X) : (φ X x).fst = ConnectedComponents.mk x := by
--   let ψ := unionEqSigmaOfDisjoint <| pairwise_disjoint_components X
--   have hx : x ∈ ⋃ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} := by
--     exact mem_iUnion_of_mem (ConnectedComponents.mk x) rfl
--   let c := ConnectedComponents.mk x
--   have hc : x ∈ CCM X c := mem_preimage.mp rfl
--   have hψ_apply : ψ ⟨x, hx⟩ = Sigma.mk c ⟨x, hc⟩ :=
--     (Equiv.apply_eq_iff_eq_symm_apply
--           (unionEqSigmaOfDisjoint (pairwise_disjoint_components X))).mpr rfl
--   have : (ψ ⟨x, hx⟩).fst = c := by rw [hψ_apply]
--   have : ↑(ψ ⟨x, hx⟩).snd = x := by rw [hψ_apply]

--   simp only [φ, equiv_sum_components, eq_mpr_eq_cast, Equiv.trans_apply, Homeomorph.coe_toEquiv]

--   --have : (Homeomorph.Set.univ X).symm x = x := by exact Homeomorph.Set.univ_symm_apply_coe X x
--   obtain ⟨_, huniv_x⟩ := Subtype.coe_eq_iff.mp <| Homeomorph.Set.univ_symm_apply_coe X x
--   rw [huniv_x]
--   simp_all only




--   sorry

-- private lemma hφ_snd (x : X) : (φ X x).snd = x := by
--   simp_all only [φ]
--   let pdc := pairwise_disjoint_components X
--   have := coe_unionEqSigmaOfDisjoint_symm_apply pdc
--   let c := ConnectedComponents.mk x
--   have hc : x ∈ CCM X c := mem_preimage.mp rfl
--   have := coe_unionEqSigmaOfDisjoint_symm_apply pdc (Sigma.mk c ⟨x, hc⟩)
--   refine exists_eq_subtype_mk_iff.mp ?_


--   simp only [equiv_sum_components, Equiv.trans_apply, Homeomorph.Set.univ_symm_apply_coe]
--   simp only [Homeomorph.Set.univ_symm_apply_coe]




-- lemma set_eq_union_in_each_component (s : Set X) : (φ X) '' s =
--     ⋃ c : ConnectedComponents X, (Sigma.mk c) '' {x : CCM X c | ↑x ∈ s} := by
--   ext x
--   constructor <;> intro hx
--   · obtain ⟨y, hyU, hψy⟩ := hx
--     apply mem_iUnion.mpr
--     let c := ConnectedComponents.mk y
--     use c
--     obtain ⟨hxc, hxy⟩ : c = x.fst ∧ y = ↑x.snd := by
--       rw [← hψy]
--       constructor <;> apply Eq.symm
--       · sorry -- have : x.fst = c := by s
--       · simp_all only [φ, equiv_sum_components]
--       --exact ⟨Eq.symm <| hψsymm_apply_fst y, Eq.symm <| hψsymm_apply_snd_coe y⟩
--     use ⟨y, mem_preimage.mpr <| mem_singleton c⟩
--     exact ⟨mem_setOf.mpr hyU, Sigma.subtype_ext hxc hxy⟩
--   · obtain ⟨c, ⟨t, htU, hxct⟩⟩ := mem_iUnion.mp hx
--     use ↑t
--     constructor
--     · exact mem_preimage.mp htU
--     · rw [← hxct]
--       exact (Equiv.symm_apply_eq ψ).mpr (hψsymm_apply_snd_coe ↑t)


--   sorry

-- noncomputable def homeomorph_univ_sum_components :
--     X ≃ₜ Σ (c : ConnectedComponents X), ConnectedComponents.mk ⁻¹' {c} := by
--   let φ := equiv_univ_sum_components X
--   intro s
--   rw [← φ.image_symm_eq_preimage s]

--   constructor <;> intro hs
--   ·


-- ----- Old text follows
-- let CCM (c : ConnectedComponents M) : Set M := ConnectedComponents.mk ⁻¹' {c}
--   have f₁ : M ≃ₜ Σ (c : ConnectedComponents M), CCM c := by
--     let ψ : (Σ (c : ConnectedComponents M), CCM c) ≃ M :=
--       Equiv.sigmaPreimageEquiv ConnectedComponents.mk
--     have hψsymm_apply_fst (x : M) : (ψ.symm x).fst = ConnectedComponents.mk x := by
--       exact Equiv.sigmaPreimageEquiv_symm_apply_fst ConnectedComponents.mk x
--     have hψsymm_apply_snd_coe (x : M) : ↑(ψ.symm x).snd = x := by
--       exact Equiv.sigmaPreimageEquiv_symm_apply_snd_coe ConnectedComponents.mk x

--     have hψsymm_image (U : Set M) : ψ.symm '' U =
--         ⋃ c : ConnectedComponents M, (Sigma.mk c) '' {x : CCM c | ↑x ∈ U} := by
--       ext x
--       constructor <;> intro hx
--       · obtain ⟨y, hyU, hψy⟩ := hx
--         apply mem_iUnion.mpr
--         let c := ConnectedComponents.mk y
--         use c
--         obtain ⟨hxc, hxy⟩ : c = x.fst ∧ y = ↑x.snd := by
--           rw [← hψy]
--           exact ⟨Eq.symm <| hψsymm_apply_fst y, Eq.symm <| hψsymm_apply_snd_coe y⟩
--         use ⟨y, mem_preimage.mpr <| mem_singleton c⟩
--         exact ⟨mem_setOf.mpr hyU, Sigma.subtype_ext hxc hxy⟩
--       · obtain ⟨c, ⟨t, htU, hxct⟩⟩ := mem_iUnion.mp hx
--         use ↑t
--         constructor
--         · exact mem_preimage.mp htU
--         · rw [← hxct]
--           exact (Equiv.symm_apply_eq ψ).mpr (hψsymm_apply_snd_coe ↑t)

--     have hψ : ∀ U : Set M, IsOpen (ψ ⁻¹' U) ↔ IsOpen U := by
--       intro U
--       apply Iff.trans (isOpen_sigma_iff (s := ψ ⁻¹' U)) ?_
--       apply Iff.trans ?_ (isOpen_iff_IsOpen_in_components U).symm
--       rw [← ψ.image_symm_eq_preimage U]

--       have hmk_preimage : ∀ V : Set M, ∀ c : ConnectedComponents M,
--           Sigma.mk c ⁻¹' (ψ.symm '' V) = V ∩ CCM c := by
--         intro V c
--         ext x
--         constructor <;> intro hx
--         · obtain ⟨y, hy, hyx⟩ := hx
--           rw [← hyx]
--           refine mem_inter ?_ (Subtype.coe_prop y)
--           obtain ⟨z, hzU, hzcy⟩ := mem_preimage.mp hy
--           have : ψ ⟨c, y⟩ = z := by exact
--             (Equiv.apply_eq_iff_eq_symm_apply ψ).mpr (Eq.symm hzcy)
--           exact mem_of_eq_of_mem this hzU
--         · obtain ⟨hxV, hxc⟩ := (mem_inter_iff x V (CCM c)).mp hx
--           have : ConnectedComponents.mk x = c := by
--             exact mem_singleton_iff.mp <| mem_preimage.mp hxc
--           simp only [mem_image, mem_preimage]
--           use ⟨x, hxc⟩
--           constructor
--           · use x
--             exact ⟨hxV, (Equiv.symm_apply_eq ψ).mpr (hψsymm_apply_snd_coe x)⟩
--           · simp only

--       -- have {c c' : ConnectedComponents M} (s : CCM c') :
--       --     c ≠ c' → (Sigma.mk c) ⁻¹' ((Sigma.mk c') '' s) = ∅ := by

--       constructor <;> intro h c
--       · specialize h c
--         rw [hψsymm_image U, preimage_iUnion] at h

--         rw [← hmk_preimage U c]

--         --rw [hmk_preimage] at h
--         have {c c' : ConnectedComponents M} (s : CCM c') :
--           c ≠ c' → (Sigma.mk c) ⁻¹' ((Sigma.mk c') '' s) = ∅ := by


--         refine ContinuousOn.isOpen_inter_preimage ?_ ?_ ?_
--         · exact ConnectedComponents.continuous_coe.continuousOn
--         · sorry -- it's the original goal
--         · exact isOpen_discrete {c}



--       rw [← ψ.image_symm_eq_preimage U]
--       constructor <;> intro hU
--       · intro c
--         have : U ∩ (ConnectedComponents.mk ⁻¹' {c}) = {x ∈ U | (ψ.symm x).fst = c} := by rfl
--         rw [this]
--         apply IsOpen.inter
--         ·
--         ·
--         sorry
--       · sorry
--     exact (ψ.toHomeomorph hψ).symm
--   have f₂ : (Σ (c : ConnectedComponents M), (ConnectedComponents.mk ⁻¹' {c}))
--       ≃ₜ Σ (_ : Fin n), Circle := by
--     let β := fun (c : ConnectedComponents M) ↦ (ConnectedComponents.mk ⁻¹' {c})
--     let φ : (c : ConnectedComponents M) → (β c ≃ₜ Circle) :=
--       fun c ↦ (circle_homeomorph_preimage_connectedComponents M c).some
--     exact (IsHomeomorph.sigmaMap α.bijective <| fun c ↦ (φ c).isHomeomorph).homeomorph
--   exact Nonempty.intro (f₁.trans f₂)
