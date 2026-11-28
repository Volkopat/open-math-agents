import OMAStatements.S_oeis_a025184

/-!
# Proof of OEIS A025184 (Mathar's recurrence for A025177 diagonal)

We prove R. J. Mathar's conjectured 4th-order holonomic recurrence for `OMA.S_oeis_a025184.a`,
where `a n = T (2 * n) n` and `T` is the array A025177 with rows `[1]`, `[1, 0, 1]`, and
trinomial recursion `T (m + 2) k = T (m + 1) k + T (m + 1) (k - 1) + T (m + 1) (k - 2)`.

## Method
For `m ≥ 1`, `T m k` is the coefficient `[X^k]` of `Q^(m - 1) * (1 + X^2)` in `Polynomial ℤ`,
where `Q = 1 + X + X^2`. Thus for `n ≥ 1`, `a n = [X^n] (Q^(2n - 1) * (1 + X^2))`.
For any polynomial `G : Polynomial ℤ` and any `n : ℕ`, the operator `X * G' - n * G` has
coefficient `0` at `X^n`. Taking `G = R(n, X) * Q^(2n - 8)` for an explicit degree-16 integer
polynomial certificate `R(n, X)` (quadratic in `n`) yields an exact polynomial identity in
`Polynomial ℤ` whose `[X^n]` coefficient is Mathar's recurrence for all `n ≥ 5`. The single
boundary case `n = 4` (which uses `a 0 = 1`) is verified directly.
-/

namespace A025184Proof

open OMA.S_oeis_a025184 Polynomial

private noncomputable abbrev Q : Polynomial ℤ := 1 + X + X ^ 2

private lemma T_eq_coeff (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    T m k = (Q ^ (m - 1) * (1 + X ^ 2)).coeff k := by
  induction m, hm using Nat.le_induction generalizing k with
  | base =>
    simp only [Nat.sub_self, pow_zero, one_mul, coeff_add, coeff_one, coeff_X_pow]
    unfold T
    by_cases h0 : k = 0
    · subst h0; simp
    · by_cases h2 : k = 2
      · subst h2; simp
      · simp [h0, h2]
  | succ m hm ih =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hpow : Q ^ (m' + 1 + 1 - 1) * (1 + X ^ 2) =
        (Q ^ (m' + 1 - 1) * (1 + X ^ 2)) * (1 + X + X ^ 2) := by
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
    rw [hpow, mul_add, mul_add, mul_one, coeff_add, coeff_add]
    change T (m' + 1) k + (if 1 ≤ k then T (m' + 1) (k - 1) else 0) +
      (if 2 ≤ k then T (m' + 1) (k - 2) else 0) = _
    rw [ih k]
    congr 1
    · congr 1
      by_cases hk1 : 1 ≤ k
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [hk1, ↓reduceIte, Nat.add_sub_cancel, coeff_mul_X]
        exact ih j
      · have hk0 : k = 0 := by omega
        subst hk0
        simp
    · by_cases hk2 : 2 ≤ k
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
        simp only [hk2, ↓reduceIte, Nat.add_sub_cancel, coeff_mul_X_pow]
        exact ih j
      · simp only [↓reduceIte, coeff_mul_X_pow', hk2]

private lemma a_eq_coeff (n : ℕ) (hn : 1 ≤ n) :
    a n = (Q ^ (2 * n - 1) * (1 + X ^ 2)).coeff n := by
  unfold a
  exact T_eq_coeff (2 * n) (by omega) n

private lemma coeff_X_mul_derivative_sub (G : Polynomial ℤ) (n : ℕ) :
    (X * derivative G - C (n : ℤ) * G).coeff n = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_sub, mul_comm X, coeff_mul_X, coeff_derivative, coeff_C_mul]
    push_cast
    ring

private lemma derivative_Q : derivative Q = 1 + 2 * X := by
  unfold Q
  simp [derivative_add, derivative_pow]

private def P0 (n : ℤ) : ℤ := 33 * n * (3 * n - 1) * (3 * n - 2)
private def P1 (n : ℤ) : ℤ := 11 * (2047 * n ^ 3 - 10725 * n ^ 2 + 17192 * n - 8520)
private def P2 (n : ℤ) : ℤ := 9 * (-4397 * n ^ 3 - 10169 * n ^ 2 + 110500 * n - 145368)
private def P3 (n : ℤ) : ℤ := -54 * (2 * n - 5) * (5353 * n ^ 2 - 33313 * n + 53904)
private def P4 (n : ℤ) : ℤ := -115668 * (2 * n - 5) * (2 * n - 7) * (n - 4)

private noncomputable def R (n : ℤ) : Polynomial ℤ :=
  C (-66 + 297 * n - 297 * n ^ 2) +
  C (-94248 + 97834 * n - 25190 * n ^ 2) * X +
  C (-1265712 + 824969 * n - 132599 * n ^ 2) * X ^ 2 +
  C (-583000 + 237674 * n - 2767 * n ^ 2) * X ^ 3 +
  C (1256740 - 1215069 * n + 303013 * n ^ 2) * X ^ 4 +
  C (3819024 - 3160342 * n + 716329 * n ^ 2) * X ^ 5 +
  C (7752004 - 6020443 * n + 1273311 * n ^ 2) * X ^ 6 +
  C (7459184 - 6029988 * n + 1348263 * n ^ 2) * X ^ 7 +
  C (6566112 - 5424282 * n + 1236150 * n ^ 2) * X ^ 8 +
  C (3763464 - 3395250 * n + 845592 * n ^ 2) * X ^ 9 +
  C (1787928 - 1732486 * n + 464726 * n ^ 2) * X ^ 10 +
  C (648384 - 696542 * n + 208967 * n ^ 2) * X ^ 11 +
  C (185482 - 206492 * n + 69916 * n ^ 2) * X ^ 12 +
  C (33704 - 42504 * n + 18491 * n ^ 2) * X ^ 13 +
  C (792 - 3443 * n + 3443 * n ^ 2) * X ^ 14 +
  C (176 - 770 * n + 759 * n ^ 2) * X ^ 15 +
  C (22 - 99 * n + 99 * n ^ 2) * X ^ 16

private lemma poly_cert (n : ℤ) :
    X * Q * derivative (R n) + (C (2 * n - 8) * X * (1 + 2 * X) - C n * Q) * R n =
      C (P0 n) * (Q ^ 8 * (1 + X ^ 2)) +
      C (P1 n) * (X * (Q ^ 6 * (1 + X ^ 2))) +
      C (P2 n) * (X ^ 2 * (Q ^ 4 * (1 + X ^ 2))) +
      C (P3 n) * (X ^ 3 * (Q ^ 2 * (1 + X ^ 2))) +
      C (P4 n) * (X ^ 4 * (1 + X ^ 2)) := by
  unfold R Q P0 P1 P2 P3 P4
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
    zero_mul, zero_add, mul_one, Nat.cast_ofNat]
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one]
  ring

private lemma coeff_X_pow_mul (k n : ℕ) (hk : k ≤ n) (F : Polynomial ℤ) :
    (X ^ k * F).coeff n = F.coeff (n - k) := by
  rw [mul_comm, coeff_mul_X_pow']
  simp [hk]

private lemma recurrence_ge5 (n : ℕ) (hn : 5 ≤ n) :
    P0 n * a n + P1 n * a (n - 1) + P2 n * a (n - 2) + P3 n * a (n - 3) + P4 n * a (n - 4) = 0 := by
  let G : Polynomial ℤ := R n * Q ^ (2 * n - 8)
  have hG : X * derivative G - C (n : ℤ) * G =
      Q ^ (2 * n - 9) *
        (X * Q * derivative (R n) + (C (2 * (n : ℤ) - 8) * X * (1 + 2 * X) - C (n : ℤ) * Q) * R n) := by
    have hpow : Q ^ (2 * n - 8) = Q ^ (2 * n - 9) * Q := by
      rw [← pow_succ, show 2 * n - 9 + 1 = 2 * n - 8 by omega]
    have hcast : ((2 * n - 8 : ℕ) : ℤ) = 2 * (n : ℤ) - 8 := by omega
    have hder : derivative G =
        derivative (R n) * Q ^ (2 * n - 8) +
        R n * (C (2 * (n : ℤ) - 8) * Q ^ (2 * n - 9) * (1 + 2 * X)) := by
      simp only [G, derivative_mul, derivative_pow, derivative_Q,
        show 2 * n - 8 - 1 = 2 * n - 9 by omega, hcast]
    rw [hder]
    dsimp only [G]
    rw [hpow]
    ring
  rw [poly_cert (n : ℤ)] at hG
  have hzero : (X * derivative G - C (n : ℤ) * G).coeff n = 0 := coeff_X_mul_derivative_sub G n
  rw [hG] at hzero
  have hQ0 : Q ^ (2 * n - 9) * Q ^ 8 = Q ^ (2 * n - 1) := by
    rw [← pow_add, show 2 * n - 9 + 8 = 2 * n - 1 by omega]
  have hQ1 : Q ^ (2 * n - 9) * Q ^ 6 = Q ^ (2 * (n - 1) - 1) := by
    rw [← pow_add, show 2 * n - 9 + 6 = 2 * (n - 1) - 1 by omega]
  have hQ2 : Q ^ (2 * n - 9) * Q ^ 4 = Q ^ (2 * (n - 2) - 1) := by
    rw [← pow_add, show 2 * n - 9 + 4 = 2 * (n - 2) - 1 by omega]
  have hQ3 : Q ^ (2 * n - 9) * Q ^ 2 = Q ^ (2 * (n - 3) - 1) := by
    rw [← pow_add, show 2 * n - 9 + 2 = 2 * (n - 3) - 1 by omega]
  have hQ4 : Q ^ (2 * n - 9) = Q ^ (2 * (n - 4) - 1) := by
    congr 1; omega
  have hexpand :
      Q ^ (2 * n - 9) *
        (C (P0 n) * (Q ^ 8 * (1 + X ^ 2)) +
         C (P1 n) * (X * (Q ^ 6 * (1 + X ^ 2))) +
         C (P2 n) * (X ^ 2 * (Q ^ 4 * (1 + X ^ 2))) +
         C (P3 n) * (X ^ 3 * (Q ^ 2 * (1 + X ^ 2))) +
         C (P4 n) * (X ^ 4 * (1 + X ^ 2))) =
      C (P0 n) * (Q ^ (2 * n - 1) * (1 + X ^ 2)) +
      C (P1 n) * (X ^ 1 * (Q ^ (2 * (n - 1) - 1) * (1 + X ^ 2))) +
      C (P2 n) * (X ^ 2 * (Q ^ (2 * (n - 2) - 1) * (1 + X ^ 2))) +
      C (P3 n) * (X ^ 3 * (Q ^ (2 * (n - 3) - 1) * (1 + X ^ 2))) +
      C (P4 n) * (X ^ 4 * (Q ^ (2 * (n - 4) - 1) * (1 + X ^ 2))) := by
    rw [← hQ0, ← hQ1, ← hQ2, ← hQ3, ← hQ4]
    ring
  rw [hexpand] at hzero
  simp only [coeff_add, coeff_C_mul] at hzero
  rw [coeff_X_pow_mul 1 n (by omega), coeff_X_pow_mul 2 n (by omega),
      coeff_X_pow_mul 3 n (by omega), coeff_X_pow_mul 4 n (by omega)] at hzero
  rw [← a_eq_coeff n (by omega), ← a_eq_coeff (n - 1) (by omega),
      ← a_eq_coeff (n - 2) (by omega), ← a_eq_coeff (n - 3) (by omega),
      ← a_eq_coeff (n - 4) (by omega)] at hzero
  exact hzero

private lemma recurrence_4 :
    P0 4 * a 4 + P1 4 * a 3 + P2 4 * a 2 + P3 4 * a 1 + P4 4 * a 0 = 0 := by
  decide

theorem main_proof : ∀ n : ℕ, 4 ≤ n →
    33 * (n : ℤ) * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) - 2) * a n
      + 11 * (2047 * (n : ℤ) ^ 3 - 10725 * (n : ℤ) ^ 2 + 17192 * (n : ℤ) - 8520) * a (n - 1)
      + 9 * (-4397 * (n : ℤ) ^ 3 - 10169 * (n : ℤ) ^ 2 + 110500 * (n : ℤ) - 145368) * a (n - 2)
      - 54 * (2 * (n : ℤ) - 5) * (5353 * (n : ℤ) ^ 2 - 33313 * (n : ℤ) + 53904) * a (n - 3)
      - 115668 * (2 * (n : ℤ) - 5) * (2 * (n : ℤ) - 7) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  intro n hn
  have h : P0 n * a n + P1 n * a (n - 1) + P2 n * a (n - 2) + P3 n * a (n - 3) + P4 n * a (n - 4) = 0 := by
    by_cases h5 : 5 ≤ n
    · exact recurrence_ge5 n h5
    · have hn4 : n = 4 := by omega
      subst hn4
      exact recurrence_4
  unfold P0 P1 P2 P3 P4 at h
  linarith

end A025184Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a025184.main :=
  A025184Proof.main_proof
