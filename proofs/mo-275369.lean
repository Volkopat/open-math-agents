import OMAStatements.S_mo_275369
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.GroupTheory.QuotientGroup.Basic

-- Problem: Isospectrality, Gassmann-Sunada triples, and tensor products
-- Upstream: formal-conjectures statements/mo-275369.lean:0 (declaration OMA.S_mo_275369.main)
-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof: the linear equivalence sends x ⊗ y to the function q ↦ x (q.1) * y (q.2), read through
-- QuotientGroup.prodEquiv; it intertwines the two actions because that bijection is equivariant.
-- Conjugacy in a product is componentwise, so the counted sets are products and their sizes
-- multiply.

namespace OMA.P_mo_275369

open OMA.S_mo_275369
open scoped TensorProduct

lemma isConj_prod {G H : Type*} [Group G] [Group H] (a b : G × H) :
    IsConj a b ↔ IsConj a.1 b.1 ∧ IsConj a.2 b.2 := by
  simp only [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨c.1, ?_⟩, ⟨c.2, ?_⟩⟩
    · rw [← hc]; rfl
    · rw [← hc]; rfl
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨(c, d), Prod.ext hc hd⟩

open Classical in
lemma card_prod_filter (U U' : Type) [Group U] [Group U'] [Fintype U] [Fintype U']
    (A : Subgroup U) (A' : Subgroup U') (g : U × U') :
    (Finset.univ.filter (fun u : U × U' => u ∈ A.prod A' ∧ IsConj u g)).card =
      (Finset.univ.filter (fun u : U => u ∈ A ∧ IsConj u g.1)).card *
      (Finset.univ.filter (fun u : U' => u ∈ A' ∧ IsConj u g.2)).card := by
  classical
  rw [← Finset.card_product]
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    Subgroup.mem_prod, isConj_prod]
  tauto

lemma gs_prod (U U' : Type) [Group U] [Group U'] [Fintype U] [Fintype U']
    (V W : Subgroup U) (V' W' : Subgroup U')
    (h : IsGassmannSunadaTriple U V W) (h' : IsGassmannSunadaTriple U' V' W') :
    IsGassmannSunadaTriple (U × U') (V.prod V') (W.prod W') := by
  classical
  intro g
  have e1 := card_prod_filter U U' V V' g
  have e2 := card_prod_filter U U' W W' g
  have h1 := h g.1
  have h2 := h' g.2
  convert e1.trans ((congrArg₂ (· * ·) h1 h2).trans e2.symm) using 0

noncomputable def eqv (U U' : Type) [Group U] [Group U'] [Fintype U] [Fintype U']
    (V : Subgroup U) (V' : Subgroup U') :
    ((U ⧸ V → ℂ) ⊗[ℂ] (U' ⧸ V' → ℂ)) ≃ₗ[ℂ] ((U × U') ⧸ (V.prod V') → ℂ) := by
  classical
  haveI : Finite (U' ⧸ V') :=
    Finite.of_surjective (QuotientGroup.mk : U' → U' ⧸ V') QuotientGroup.mk_surjective
  letI : Fintype (U' ⧸ V') := Fintype.ofFinite _
  exact (TensorProduct.piScalarRight ℂ ℂ (U ⧸ V → ℂ) (U' ⧸ V')) ≪≫ₗ
    (LinearEquiv.curry ℂ ℂ (U' ⧸ V') (U ⧸ V)).symm ≪≫ₗ
    LinearEquiv.funCongrLeft ℂ ℂ ((QuotientGroup.prodEquiv V V').trans (Equiv.prodComm _ _))

lemma eqv_tmul (U U' : Type) [Group U] [Group U'] [Fintype U] [Fintype U']
    (V : Subgroup U) (V' : Subgroup U') (x : U ⧸ V → ℂ) (y : U' ⧸ V' → ℂ)
    (q : (U × U') ⧸ (V.prod V')) :
    eqv U U' V V' (x ⊗ₜ y) q =
      y (QuotientGroup.prodEquiv V V' q).2 * x (QuotientGroup.prodEquiv V V' q).1 := by
  classical
  simp only [eqv, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    LinearEquiv.coe_curry_symm, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  rfl

lemma prodEquiv_smul (U U' : Type) [Group U] [Group U']
    (V : Subgroup U) (V' : Subgroup U') (g : U × U') (q : (U × U') ⧸ (V.prod V')) :
    QuotientGroup.prodEquiv V V' (g • q) =
      (g.1 • (QuotientGroup.prodEquiv V V' q).1, g.2 • (QuotientGroup.prodEquiv V V' q).2) := by
  induction q using QuotientGroup.induction_on with
  | H x => rfl

end OMA.P_mo_275369

open OMA.S_mo_275369 OMA.P_mo_275369 in
theorem OMA.solution : type_of% @OMA.S_mo_275369.main := by
  intro U U' _ _ _ _ V W V' W' h h'
  refine ⟨⟨eqv U U' V V', ?_⟩, gs_prod U U' V W V' W' h h'⟩
  intro g t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    funext q
    simp only [extTensorPermRep, Representation.tprod_apply, TensorProduct.map_tmul]
    rw [eqv_tmul]
    show _ = eqv U U' V V' (x ⊗ₜ y) (g⁻¹ • q)
    rw [eqv_tmul, prodEquiv_smul]
    rfl
  | add a b ha hb => simp only [map_add, ha, hb]
