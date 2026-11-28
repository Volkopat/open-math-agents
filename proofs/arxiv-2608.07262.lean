import OMAStatements.S_arxiv_2608_07262
import Mathlib

namespace OMA.P_arxiv_2608_07262

open OMA.S_arxiv_2608_07262 Polynomial

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The irreducible quadratic `X^2 + 1` over `ZMod 3` defining `𝔽_9`. -/
noncomputable def Q3 : Polynomial (ZMod 3) := X ^ 2 + 1

lemma Q3_natDegree : Q3.natDegree = 2 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (by unfold Q3; compute_degree!) ?_
  simp [Q3, coeff_X_pow, coeff_one]

lemma Q3_monic : Q3.Monic := by
  rw [Monic, leadingCoeff, Q3_natDegree]
  simp [Q3, coeff_X_pow, coeff_one]

lemma Q3_no_root : ∀ x : ZMod 3, Q3.eval x ≠ 0 := by
  have hd : ∀ x : ZMod 3, x ^ 2 + 1 ≠ 0 := by decide
  intro x
  simpa [Q3, eval_add, eval_pow, eval_X, eval_one] using hd x

lemma exists_root_of_natDegree_eq_one {F : Type*} [Field F] {f : Polynomial F}
    (hf : f.natDegree = 1) : ∃ x : F, f.eval x = 0 := by
  have hne : f.leadingCoeff ≠ 0 := by
    intro h0; rw [leadingCoeff_eq_zero] at h0; simp [h0] at hf
  have h1 : f.coeff 1 = f.leadingCoeff := by rw [← hf]; rfl
  have heq : f = C (f.coeff 1) * X + C (f.coeff 0) := eq_X_add_C_of_natDegree_le_one (le_of_eq hf)
  set r : F := -(f.coeff 0) / f.leadingCoeff
  refine ⟨r, ?_⟩
  rw [heq]; simp only [eval_add, eval_mul, eval_X, eval_C]; rw [h1]; dsimp [r]
  field_simp [hne]; ring

lemma Q3_irred : Irreducible Q3 := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu; rw [Q3_natDegree] at this; omega
  · have hQne : Q3 ≠ 0 := Q3_monic.ne_zero
    have ha0 : a ≠ 0 := fun h => hQne (by simp [hab, h])
    have hb0 : b ≠ 0 := fun h => hQne (by simp [hab, h])
    have hdeg : a.natDegree + b.natDegree = 2 := by
      rw [← natDegree_mul ha0 hb0, ← hab, Q3_natDegree]
    by_cases ha : a.natDegree = 0
    · left
      have hac : a = C (a.coeff 0) := eq_C_of_natDegree_eq_zero ha
      rw [hac]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => ha0 (by rw [hac, h0, map_zero])))
    · by_cases hb : b.natDegree = 0
      · right
        have hbc : b = C (b.coeff 0) := eq_C_of_natDegree_eq_zero hb
        rw [hbc]
        exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun h0 => hb0 (by rw [hbc, h0, map_zero])))
      · exfalso
        have h1 : a.natDegree = 1 := by omega
        obtain ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h1
        exact Q3_no_root x (by rw [hab, eval_mul, hx, zero_mul])

abbrev K9 := AdjoinRoot Q3

instance : Fact (Irreducible Q3) := ⟨Q3_irred⟩
noncomputable instance instFieldK9 : Field K9 := AdjoinRoot.instField

lemma finrank_K9 : Module.finrank (ZMod 3) K9 = 2 := by
  rw [(AdjoinRoot.powerBasis Q3_monic.ne_zero).finrank, AdjoinRoot.powerBasis_dim, Q3_natDegree]

noncomputable instance instFintypeK9 : Fintype K9 := by
  have : FiniteDimensional (ZMod 3) K9 :=
    Module.finite_of_finrank_pos (by rw [finrank_K9]; omega)
  have : Finite K9 := Module.finite_of_finite (ZMod 3)
  exact Fintype.ofFinite K9

lemma card_K9 : Fintype.card K9 = (3 ^ 1) ^ 2 := by
  have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := K9)
  rw [ZMod.card, finrank_K9] at h
  simpa using h

noncomputable abbrev ii : K9 := AdjoinRoot.root Q3

lemma ii_sq : ii ^ 2 = -1 := by
  have h0 : Polynomial.aeval ii Q3 = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  simp only [Q3, map_add, map_pow, map_one, aeval_X] at h0
  exact eq_neg_of_add_eq_zero_left h0

lemma three_eq_zero_K9 : (3 : K9) = 0 := by
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := by decide
  have h := congrArg (algebraMap (ZMod 3) K9) h3
  rw [map_natCast, map_zero] at h
  exact h

/-- Every element of `K9` is of the form `a + b * ii` with `a, b ∈ {0, 1, -1}`. -/
lemma K9_decomp (α : K9) :
    ∃ a b : ZMod 3, α = algebraMap (ZMod 3) K9 a + algebraMap (ZMod 3) K9 b * ii := by
  let pb := AdjoinRoot.powerBasis Q3_monic.ne_zero
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis_dim, Q3_natDegree]
  have hsum := pb.basis.sum_repr α
  refine ⟨pb.basis.repr α ⟨0, by omega⟩, pb.basis.repr α ⟨1, by omega⟩, ?_⟩
  conv_lhs => rw [← hsum]
  have hfin2 : ∀ f : Fin pb.dim → K9,
      ∑ k : Fin pb.dim, f k = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
    intro f
    have heq : (Finset.univ : Finset (Fin pb.dim)) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hk : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk with h0 | h1
      · left; exact Fin.ext h0
      · right; exact Fin.ext h1
    rw [heq, Finset.sum_pair (by intro h; have := congrArg Fin.val h; simp at this)]
  rw [hfin2]
  simp only [PowerBasis.basis_eq_pow, pow_zero, pow_one, Algebra.smul_def, mul_one]
  rfl

/-- A monic cubic polynomial over a field with a root is NOT irreducible. -/
lemma not_irred_cubic_of_root {F : Type*} [Field F] {α r : F}
    (hr : r ^ 3 + r ^ 2 + r + α = 0) :
    ¬ Irreducible (X ^ 3 + X ^ 2 + X + C α) := by
  intro hirr
  set f : Polynomial F := X ^ 3 + X ^ 2 + X + C α
  have hroot : f.IsRoot r := by
    simp [f, IsRoot, eval_add, eval_pow, eval_X, eval_C, hr]
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hroot
  have hdegf : f.natDegree = 3 := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (by unfold f; compute_degree!) ?_
    simp [f, coeff_X_pow, coeff_X]
  have hne0 : f ≠ 0 := fun h0 => by simp [h0] at hdegf
  have hq0 : q ≠ 0 := fun h0 => hne0 (by simp [hq, h0])
  have hx0 : X - C r ≠ 0 := X_sub_C_ne_zero r
  have hdegq : q.natDegree = 2 := by
    have := natDegree_mul hx0 hq0
    rw [← hq, hdegf, natDegree_X_sub_C] at this
    omega
  rcases hirr.isUnit_or_isUnit hq with hu | hu
  · have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at this; omega
  · have := natDegree_eq_zero_of_isUnit hu
    rw [hdegq] at this; omega

lemma orderOf_ne_eight_of_pow_four {α : K9} (h4 : α ^ 4 = 1) : orderOf α ≠ 8 := by
  intro h8
  have hdvd : orderOf α ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rw [h8] at hdvd
  norm_num at hdvd

lemma K9_no_cubic_primitive (α : K9) (hord : orderOf α = Fintype.card K9 - 1) :
    ¬ IsPrimitivePoly (X ^ 3 + X ^ 2 + X + C α) := by
  intro hprim
  have h8 : orderOf α = 8 := by rw [hord, card_K9]; norm_num
  obtain ⟨a, b, hα⟩ := K9_decomp α
  have h3cases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have ha := h3cases a
  have hb := h3cases b
  have h3 := three_eq_zero_K9
  have hi2 := ii_sq
  have h2 : algebraMap (ZMod 3) K9 2 = -1 := by
    have : (2 : ZMod 3) = -1 := by decide
    rw [this, map_neg, map_one]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · -- (0, 0): α = 0
    simp only [map_zero, zero_mul, add_zero] at hα
    rw [hα, orderOf_zero] at h8; norm_num at h8
  · -- (0, 1): α = ii, α^4 = 1
    simp only [map_zero, map_one, one_mul, zero_add] at hα
    exact orderOf_ne_eight_of_pow_four (by rw [hα]; linear_combination (ii ^ 2 - 1) * hi2) h8
  · -- (0, 2): α = -ii, α^4 = 1
    simp only [map_zero, h2, zero_add] at hα
    exact orderOf_ne_eight_of_pow_four (by rw [hα]; linear_combination (ii ^ 2 - 1) * hi2) h8
  · -- (1, 0): α = 1, α^4 = 1
    simp only [map_one, map_zero, zero_mul, add_zero] at hα
    exact orderOf_ne_eight_of_pow_four (by rw [hα]; ring) h8
  · -- (1, 1): α = 1 + ii, root r = 1 + ii
    simp only [map_one, one_mul] at hα
    refine not_irred_cubic_of_root (r := 1 + ii) ?_ hprim.2.1
    rw [hα]
    linear_combination (ii + 4) * hi2 + (2 * ii) * h3
  · -- (1, 2): α = 1 - ii, root r = 1 - ii
    simp only [map_one, h2] at hα
    refine not_irred_cubic_of_root (r := 1 - ii) ?_ hprim.2.1
    rw [hα]
    linear_combination (-ii + 4) * hi2 + (-2 * ii) * h3
  · -- (2, 0): α = -1, α^4 = 1
    simp only [h2, map_zero, zero_mul, add_zero] at hα
    exact orderOf_ne_eight_of_pow_four (by rw [hα]; ring) h8
  · -- (2, 1): α = -1 + ii, root r = -1 - ii
    simp only [h2, map_one, one_mul] at hα
    refine not_irred_cubic_of_root (r := -1 - ii) ?_ hprim.2.1
    rw [hα]
    linear_combination (-ii - 2) * hi2
  · -- (2, 2): α = -1 - ii, root r = -1 + ii
    simp only [h2] at hα
    refine not_irred_cubic_of_root (r := -1 + ii) ?_ hprim.2.1
    rw [hα]
    linear_combination (ii - 2) * hi2

end OMA.P_arxiv_2608_07262

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2608_07262.main) := by
  intro h
  obtain ⟨α, hord, hprim⟩ :=
    h OMA.P_arxiv_2608_07262.K9 3 1 (by decide) (by omega) OMA.P_arxiv_2608_07262.card_K9
  exact OMA.P_arxiv_2608_07262.K9_no_cubic_primitive α hord hprim
