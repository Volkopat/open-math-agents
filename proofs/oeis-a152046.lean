import OMAStatements.S_oeis_a152046
import Mathlib

namespace OMA.P152046

open OMA.S_oeis_a152046

/-- The primitive n-th root of unity exp(2 pi i / n). -/
noncomputable def z (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)

lemma z_prim (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (z n) n :=
  Complex.isPrimitiveRoot_exp n (by omega)

/-- 3 J(n) = 2^n - (-1)^n. -/
lemma jac3 : ∀ n : ℕ, (3 : ℂ) * (jacobsthal n : ℂ) = 2 ^ n - (-1) ^ n
  | 0 => by simp [jacobsthal]
  | 1 => by norm_num [jacobsthal]
  | (n + 2) => by
    have h1 := jac3 n
    have h2 := jac3 (n + 1)
    rw [jacobsthal]
    push_cast
    linear_combination h2 + 2 * h1

/-- prod_{k < n} (X - zeta^k) = X^n - 1. -/
lemma prod_X_sub (n : ℕ) (hn : 0 < n) {ζ : ℂ} (h : IsPrimitiveRoot ζ n) :
    ∏ k ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ k)) = Polynomial.X ^ n - 1 := by
  have hmonic : (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).Monic :=
    Polynomial.monic_X_pow_sub_C 1 (by omega)
  have hcard : (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).roots.card =
      (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    exact h.card_nthRoots_one
  have key := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  have hr : (Polynomial.X ^ n - Polynomial.C (1 : ℂ)).roots = Polynomial.nthRoots n (1 : ℂ) := rfl
  rw [hr, h.nthRoots_eq (one_pow n), Multiset.map_map] at key
  rw [Finset.prod_eq_multiset_prod, Finset.range_val]
  simpa [Function.comp_def] using key

/-- prod_{k < n} (2 + zeta^k) = 2^n - (-1)^n. -/
lemma prod_two_add (n : ℕ) (hn : 0 < n) {ζ : ℂ} (h : IsPrimitiveRoot ζ n) :
    ∏ k ∈ Finset.range n, (2 + ζ ^ k) = 2 ^ n - (-1) ^ n := by
  have e := congrArg (Polynomial.eval (-2 : ℂ)) (prod_X_sub n hn h)
  rw [Polynomial.eval_prod] at e
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_one] at e
  have h2 : ∏ k ∈ Finset.range n, (2 + ζ ^ k) = ∏ k ∈ Finset.range n, ((-1) * (-2 - ζ ^ k)) := by
    apply Finset.prod_congr rfl
    intro k _
    ring
  rw [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, e]
  have hsq : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have hneg : (-2 : ℂ) ^ n = (-1) ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [hneg]
  linear_combination (2 : ℂ) ^ n * hsq

lemma factor_aux (θ E E' : ℂ) (h1 : E = Complex.exp (2 * θ * Complex.I))
    (h2 : E' = Complex.exp (-(2 * θ) * Complex.I)) :
    1 + 8 * Complex.cos θ ^ 2 = (2 + E) * (2 + E') := by
  have h3 : Complex.exp (2 * θ * Complex.I) + Complex.exp (-(2 * θ) * Complex.I)
      = 2 * Complex.cos (2 * θ) := (Complex.two_cos _).symm
  have h4 : Complex.cos (2 * θ) = 2 * Complex.cos θ ^ 2 - 1 := Complex.cos_two_mul θ
  have h5 : Complex.exp (2 * θ * Complex.I) * Complex.exp (-(2 * θ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  subst h1 h2
  linear_combination (-2 : ℂ) * h3 - 4 * h4 - h5

/-- 1 + 8 cos(k pi / n)^2 = (2 + zeta^k) (2 + zeta^(n-k)). -/
lemma factor (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    (((1 + 8 * Real.cos ((k : ℝ) * Real.pi / (n : ℝ)) ^ 2 : ℝ)) : ℂ) =
      (2 + z n ^ k) * (2 + z n ^ (n - k)) := by
  have hprim := z_prim n hn
  have h1 : z n ^ k = Complex.exp (2 * ((k : ℂ) * (Real.pi : ℂ) / (n : ℂ)) * Complex.I) := by
    rw [z, ← Complex.exp_nat_mul]
    congr 1
    ring
  have h2 : z n ^ (n - k) =
      Complex.exp (-(2 * ((k : ℂ) * (Real.pi : ℂ) / (n : ℂ))) * Complex.I) := by
    have hmul : z n ^ (n - k) * z n ^ k = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hk, hprim.pow_eq_one]
    rw [eq_inv_of_mul_eq_one_left hmul, h1, ← Complex.exp_neg]
    congr 1
    ring
  have e : (((1 + 8 * Real.cos ((k : ℝ) * Real.pi / (n : ℝ)) ^ 2 : ℝ)) : ℂ)
      = 1 + 8 * Complex.cos ((k : ℂ) * (Real.pi : ℂ) / (n : ℂ)) ^ 2 := by
    push_cast
    ring
  rw [e]
  exact factor_aux _ _ _ h1 h2

lemma pair_odd (f : ℕ → ℂ) (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, f k) * (∏ k ∈ Finset.Icc 1 m, f (2 * m + 1 - k)) =
      ∏ k ∈ Finset.Ico 1 (2 * m + 1), f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_reflect f 1 (by omega),
    show 2 * m + 1 + 1 - (m + 1) = m + 1 by omega, show 2 * m + 1 + 1 - 1 = 2 * m + 1 by omega,
    Finset.prod_Ico_consecutive f (by omega) (by omega)]

lemma pair_even (f : ℕ → ℂ) (m : ℕ) :
    (∏ k ∈ Finset.Icc 1 m, f k) * (∏ k ∈ Finset.Icc 1 m, f (2 * m + 2 - k)) * f (m + 1) =
      ∏ k ∈ Finset.Ico 1 (2 * m + 2), f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_reflect f 1 (by omega),
    show 2 * m + 2 + 1 - (m + 1) = m + 2 by omega, show 2 * m + 2 + 1 - 1 = 2 * m + 2 by omega,
    ← Finset.prod_Ico_consecutive f (show 1 ≤ m + 1 by omega) (show m + 1 ≤ 2 * m + 2 by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show m + 1 < 2 * m + 2 by omega)]
  ring

theorem sol : type_of% @OMA.S_oeis_a152046.main := by
  intro n hn
  have hprim := z_prim n (by omega)
  apply Complex.ofReal_injective
  have hJ := jac3 n
  have hR := prod_two_add n (by omega) hprim
  rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega)] at hR
  have hP : ∏ k ∈ Finset.Ico 1 n, (2 + z n ^ k) = (jacobsthal n : ℂ) := by
    have h3 : (3 : ℂ) * ∏ k ∈ Finset.Ico 1 n, (2 + z n ^ k) = 3 * (jacobsthal n : ℂ) := by
      rw [hJ, ← hR]
      norm_num
    exact mul_left_cancel₀ (by norm_num) h3
  rw [Complex.ofReal_natCast, ← hP]
  unfold a
  rw [Complex.ofReal_prod]
  rw [Finset.prod_congr rfl (fun k hk => factor n k (by omega)
    (by rw [Finset.mem_Icc] at hk; omega))]
  rw [Finset.prod_mul_distrib]
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm : (2 * (m' + 1) - 1) / 2 = m' := by omega
    have hn2 : 2 * (m' + 1) = 2 * m' + 2 := by ring
    rw [hm, hn2]
    have hprim' := z_prim (2 * m' + 2) (by omega)
    have hmid : z (2 * m' + 2) ^ (m' + 1) = -1 := by
      have hsq : (z (2 * m' + 2) ^ (m' + 1)) ^ 2 = 1 := by
        rw [← pow_mul, show (m' + 1) * 2 = 2 * m' + 2 by ring, hprim'.pow_eq_one]
      have hne : z (2 * m' + 2) ^ (m' + 1) ≠ 1 :=
        hprim'.pow_ne_one_of_pos_of_lt (by omega) (by omega)
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact absurd h hne
      · exact h
    rw [← pair_even (fun k => 2 + z (2 * m' + 2) ^ k) m']
    simp only [hmid]
    norm_num
  · have hm : (2 * m + 1 - 1) / 2 = m := by omega
    rw [hm]
    exact pair_odd (fun k => 2 + z (2 * m + 1) ^ k) m

end OMA.P152046

theorem OMA.solution : type_of% @OMA.S_oeis_a152046.main := OMA.P152046.sol

