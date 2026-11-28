import OMAStatements.S_oeis_a397445


open Matrix Finset Equiv

namespace OMA.R_oeis_a397445_R1

lemma permanent_scale_rows {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℤ) (c : α → ℤ) :
    (Matrix.of fun i j => c i * M i j).permanent =
      (∏ i, c i) * M.permanent := by
  rw [← Matrix.permanent_transpose (Matrix.of fun i j => c i * M i j),
      ← Matrix.permanent_transpose M]
  unfold Matrix.permanent
  simp only [Matrix.transpose_apply, Matrix.of_apply, Finset.prod_mul_distrib,
    Finset.mul_sum]

lemma permanent_zero_of_signed_col_symmetry {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℤ) (σ : Equiv.Perm α) (c : α → ℤ)
    (h : ∀ i j, M i (σ j) = c i * M i j) (hc : ∏ i, c i = -1) :
    M.permanent = 0 := by
  have hM : M.submatrix id σ = Matrix.of (fun i j => c i * M i j) := by
    ext i j
    exact h i j
  have hs := Matrix.permanent_permute_rows σ M
  rw [hM, permanent_scale_rows, hc] at hs
  omega

open Polynomial

lemma coeff_negX_sign (p : ℤ[X]) (n : ℕ) : (p.comp (-X)).coeff n = (-1 : ℤ)^n * p.coeff n := by
  have h : (-X : ℤ[X]) = C (-1 : ℤ) * X := by simp
  rw [h, Polynomial.comp_C_mul_X_coeff, mul_comm]

lemma poly_rev (a b : ℕ) :
    (((1 + X : ℤ[X]) ^ a) * ((1 - X) ^ b)).comp (-X) =
      (1 + X) ^ b * (1 - X) ^ a := by
  simp [Polynomial.mul_comp, Polynomial.pow_comp, sub_eq_add_neg, mul_comm]

lemma coeff_rev (a b n : ℕ) :
    (((1 + X : ℤ[X]) ^ b) * ((1 - X) ^ a)).coeff n =
    (-1 : ℤ)^n * (((1 + X : ℤ[X]) ^ a) * ((1 - X) ^ b)).coeff n := by
  rw [← poly_rev, coeff_negX_sign]

lemma coeff_one_sub_X (b k : ℕ) : ((1-X : ℤ[X])^b).coeff k = (-1 : ℤ)^k * (b.choose k : ℤ) := by
  have hp : ((1-X : ℤ[X])^b) = (((1+X : ℤ[X])^b).comp (-X)) := by
    simp [Polynomial.pow_comp, sub_eq_add_neg]
  rw [hp, coeff_negX_sign, Polynomial.coeff_one_add_X_pow]

lemma coeff_explicit (a b k : ℕ) :
    (((1+X : ℤ[X])^a) * ((1-X)^b)).coeff k =
      ∑ t ∈ Finset.range (min k b + 1), (-1 : ℤ)^t * (b.choose t : ℤ) * (a.choose (k-t) : ℤ) := by
  rw [mul_comm, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [coeff_one_sub_X, Polynomial.coeff_one_add_X_pow]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : min k b + 1 ≤ k + 1))
  intro t ht ht'
  have ht1 : t ≤ k := by simp only [Finset.mem_range] at ht; omega
  have ht2 : b < t := by simp only [Finset.mem_range, not_lt] at ht'; omega
  simp [Nat.choose_eq_zero_of_lt ht2]

lemma K_rev (n : ℕ) (i j : Fin n) :
    OMA.S_oeis_a397445.krawtchouk n i j.rev = (-1 : ℤ)^i.val * OMA.S_oeis_a397445.krawtchouk n i j := by
  unfold OMA.S_oeis_a397445.krawtchouk
  rw [← coeff_explicit, ← coeff_explicit]
  have h : n - 1 - j.rev.val = j.val := by simp [Fin.val_rev]; omega
  rw [h]
  simpa only [Fin.val_rev, Nat.sub_sub, Nat.add_comm] using coeff_rev (n - 1 - j.val) j.val i.val


open Finset

lemma sign_sum_parity (n : ℕ) : (∑ i ∈ range n, i) % 2 = if n % 4 = 2 ∨ n % 4 = 3 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 4
    · interval_cases n <;> norm_num [Finset.sum_range_succ]
    · have h4 : 4 ≤ n := by omega
      have heq : n - 4 + 4 = n := Nat.sub_add_cancel h4
      have ih' := ih (n - 4) (by omega)
      have hs : (∑ i ∈ range n, i) = (∑ i ∈ range (n - 4), i) + 4 * (n - 4) + 6 := by
        conv_lhs => rw [← heq]
        rw [Finset.sum_range_add]
        simp [Finset.sum_range_succ]
        omega
      rw [hs]
      split_ifs at ih' ⊢ <;> omega

lemma row_sign_product (n : ℕ) (h : n % 4 = 2 ∨ n % 4 = 3) :
    (∏ i : Fin n, (-1 : ℤ) ^ i.val) = -1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have he : (∑ i : Fin n, i.val) = ∑ i ∈ range n, i := Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n
  rw [he]
  have hs := sign_sum_parity n
  simp only [h, ↓reduceIte] at hs
  have ho : Odd (∑ i ∈ range n, i) := Nat.odd_iff.mpr hs
  exact ho.neg_one_pow
lemma krawtchouk_zero_mod_four (n : ℕ) (h : n % 4 = 2 ∨ n % 4 = 3) : (OMA.S_oeis_a397445.krawtchouk n).permanent = 0 := by
  apply permanent_zero_of_signed_col_symmetry (OMA.S_oeis_a397445.krawtchouk n) Fin.revPerm (fun i => (-1 : ℤ) ^ i.val)
  · intro i j
    simpa only [Fin.revPerm_apply] using K_rev n i j
  · exact row_sign_product n h


/-- Nonvanishing in the first allowed residue class. -/
def H1 : Prop := ∀ n : ℕ, n % 4 = 0 → (OMA.S_oeis_a397445.krawtchouk n).permanent ≠ 0

/-- Nonvanishing in the second allowed residue class. -/
def H2 : Prop := ∀ n : ℕ, n % 4 = 1 → (OMA.S_oeis_a397445.krawtchouk n).permanent ≠ 0

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a397445.main := by
  intro h0 h1 n
  constructor
  · intro hz
    have hn := Nat.mod_lt n (by norm_num : 0 < 4)
    have hn0 : n % 4 ≠ 0 := by intro h; exact h0 n h hz
    have hn1 : n % 4 ≠ 1 := by intro h; exact h1 n h hz
    omega
  · exact krawtchouk_zero_mod_four n

end OMA.R_oeis_a397445_R1
