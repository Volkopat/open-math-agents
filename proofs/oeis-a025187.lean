import OMAStatements.S_oeis_a025187

/-!
# Proof of OEIS A025187 (Mathar's recurrence for A025177 sub-diagonal)

We prove R. J. Mathar's conjectured 3rd-order holonomic recurrence for `OMA.S_oeis_a025187.a`,
where `a n = T (2 * n) (n - 1)` for `n ≥ 1` and `T` is the array A025177 with rows `[1]`,
`[1, 0, 1]`, and trinomial recursion `T (m + 2) k = T (m + 1) k + T (m + 1) (k - 1) + T (m + 1) (k - 2)`.

## Method
For `m ≥ 1`, `T m k` is `[X^k] (Q^(m - 1) * (1 + X^2))` in `Polynomial ℤ`, where `Q = 1 + X + X^2`.
Thus for `n ≥ 1`, `a n = [X^(n - 1)] (Q^(2n - 1) * (1 + X^2))`.
For any polynomial `G : Polynomial ℤ` and any `m : ℕ`, `(X * G' - C m * G).coeff m = 0`.
Multiplying Mathar's recurrence by `(n - 1) * (n - 2)` (nonzero for `n ≥ 4`) and setting
`G = R(n, X) * Q^(2n - 6)` for an explicit degree-12 integer polynomial certificate `R(n, X)`
yields an exact identity in `Polynomial ℤ` whose `[X^(n - 1)]` coefficient vanishes, proving
the recurrence for all `n ≥ 4`.
-/

namespace A025187Proof

open OMA.S_oeis_a025187 Polynomial

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
    a n = (Q ^ (2 * n - 1) * (1 + X ^ 2)).coeff (n - 1) := by
  unfold a
  exact T_eq_coeff (2 * n) (by omega) (n - 1)

private lemma coeff_X_mul_derivative_sub (G : Polynomial ℤ) (m : ℕ) :
    (X * derivative G - C (m : ℤ) * G).coeff m = 0 := by
  cases m with
  | zero => simp
  | succ m =>
    rw [coeff_sub, mul_comm X, coeff_mul_X, coeff_derivative, coeff_C_mul]
    push_cast
    ring

private lemma derivative_Q : derivative Q = 1 + 2 * X := by
  unfold Q
  simp [derivative_add, derivative_pow]

private def P0 (n : ℤ) : ℤ := 12 * n * (1573 * n - 2085) * (3 * n - 1) * (3 * n + 1)
private def P1 (n : ℤ) : ℤ :=
  259519 * n ^ 4 - 6550685 * n ^ 3 + 19840883 * n ^ 2 - 20466403 * n + 6720078
private def P2 (n : ℤ) : ℤ :=
  -54 * (2 * n - 3) * (63141 * n ^ 3 - 343882 * n ^ 2 + 645379 * n - 388606)
private def P3 (n : ℤ) : ℤ :=
  -324 * (n - 3) * (4693 * n - 5417) * (2 * n - 3) * (2 * n - 5)

private noncomputable def R (n : ℤ) : Polynomial ℤ :=
  C (50040 * n - 62772 * n ^ 2 - 431484 * n ^ 3 + 564948 * n ^ 4 - 169884 * n ^ 5) +
  C (6720078 - 26911261 * n + 39924510 * n ^ 2 - 28736416 * n ^ 3 + 10255188 * n ^ 4 - 1448707 * n ^ 5) * X +
  C (-15089136 + 36576370 * n - 34089645 * n ^ 2 + 14498437 * n ^ 3 - 2472891 * n ^ 4 + 85345 * n ^ 5) * X ^ 2 +
  C (-60000330 + 166265839 * n - 181404832 * n ^ 2 + 98092230 * n ^ 3 - 26830934 * n ^ 4 + 3091595 * n ^ 5) * X ^ 3 +
  C (-98126628 + 276034118 * n - 307884748 * n ^ 2 + 173933980 * n ^ 3 - 51467648 * n ^ 4 + 6577038 * n ^ 5) * X ^ 4 +
  C (-141659640 + 417047598 * n - 488286226 * n ^ 2 + 290151878 * n ^ 3 - 89825270 * n ^ 4 + 11785228 * n ^ 5) * X ^ 5 +
  C (-108633540 + 320549086 * n - 381366478 * n ^ 2 + 236284548 * n ^ 3 - 78570578 * n ^ 4 + 11245442 * n ^ 5) * X ^ 6 +
  C (-75422058 + 230580905 * n - 287291578 * n ^ 2 + 188249452 * n ^ 3 - 66216092 * n ^ 4 + 9902763 * n ^ 5) * X ^ 7 +
  C (-27714312 + 87421626 * n - 117825625 * n ^ 2 + 87666089 * n ^ 3 - 35621663 * n ^ 4 + 6024733 * n ^ 5) * X ^ 8 +
  C (-7070358 + 24375247 * n - 38452186 * n ^ 2 + 34235976 * n ^ 3 - 16067408 * n ^ 4 + 2978729 * n ^ 5) * X ^ 9 +
  C (-100080 + 1459944 * n - 6015112 * n ^ 2 + 8970872 * n ^ 3 - 5473352 * n ^ 4 + 1157728 * n ^ 5) * X ^ 10 +
  C (-16680 + 371204 * n - 1629976 * n ^ 2 + 2468416 * n ^ 3 - 1513856 * n ^ 4 + 320892 * n ^ 5) * X ^ 11 +
  C (50040 * n - 262932 * n ^ 2 + 420084 * n ^ 3 - 263820 * n ^ 4 + 56628 * n ^ 5) * X ^ 12

private lemma poly_cert (n : ℤ) :
    X * Q * derivative (R n) + (C (2 * n - 6) * X * (1 + 2 * X) - C (n - 1) * Q) * R n =
      C ((n - 1) * (n - 2)) *
        (C (P0 n) * (Q ^ 6 * (1 + X ^ 2)) +
         C (P1 n) * (X * (Q ^ 4 * (1 + X ^ 2))) +
         C (P2 n) * (X ^ 2 * (Q ^ 2 * (1 + X ^ 2))) +
         C (P3 n) * (X ^ 3 * (1 + X ^ 2))) := by
  unfold R Q P0 P1 P2 P3
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
    zero_mul, zero_add, mul_one, Nat.cast_ofNat]
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one]
  ring

private lemma coeff_X_pow_mul (k m : ℕ) (hk : k ≤ m) (F : Polynomial ℤ) :
    (X ^ k * F).coeff m = F.coeff (m - k) := by
  rw [mul_comm, coeff_mul_X_pow']
  simp [hk]

theorem main_proof : ∀ n : ℕ, 4 ≤ n →
    12 * (n : ℤ) * (1573 * (n : ℤ) - 2085) * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) + 1) * a n
      + (259519 * (n : ℤ) ^ 4 - 6550685 * (n : ℤ) ^ 3 + 19840883 * (n : ℤ) ^ 2 - 20466403 * (n : ℤ)
          + 6720078) * a (n - 1)
      - 54 * (2 * (n : ℤ) - 3) * (63141 * (n : ℤ) ^ 3 - 343882 * (n : ℤ) ^ 2 + 645379 * (n : ℤ) - 388606)
          * a (n - 2)
      - 324 * ((n : ℤ) - 3) * (4693 * (n : ℤ) - 5417) * (2 * (n : ℤ) - 3) * (2 * (n : ℤ) - 5) * a (n - 3)
      = 0 := by
  intro n hn
  let G : Polynomial ℤ := R n * Q ^ (2 * n - 6)
  have hG : X * derivative G - C ((n - 1 : ℕ) : ℤ) * G =
      Q ^ (2 * n - 7) *
        (X * Q * derivative (R n) +
          (C (2 * (n : ℤ) - 6) * X * (1 + 2 * X) - C ((n : ℤ) - 1) * Q) * R n) := by
    have hpow : Q ^ (2 * n - 6) = Q ^ (2 * n - 7) * Q := by
      rw [← pow_succ, show 2 * n - 7 + 1 = 2 * n - 6 by omega]
    have hcast1 : ((2 * n - 6 : ℕ) : ℤ) = 2 * (n : ℤ) - 6 := by omega
    have hcast2 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hder : derivative G =
        derivative (R n) * Q ^ (2 * n - 6) +
        R n * (C (2 * (n : ℤ) - 6) * Q ^ (2 * n - 7) * (1 + 2 * X)) := by
      simp only [G, derivative_mul, derivative_pow, derivative_Q,
        show 2 * n - 6 - 1 = 2 * n - 7 by omega, hcast1]
    rw [hder, hcast2]
    dsimp only [G]
    rw [hpow]
    ring
  rw [poly_cert (n : ℤ)] at hG
  have hzero : (X * derivative G - C ((n - 1 : ℕ) : ℤ) * G).coeff (n - 1) = 0 :=
    coeff_X_mul_derivative_sub G (n - 1)
  rw [hG] at hzero
  have hQ0 : Q ^ (2 * n - 7) * Q ^ 6 = Q ^ (2 * n - 1) := by
    rw [← pow_add, show 2 * n - 7 + 6 = 2 * n - 1 by omega]
  have hQ1 : Q ^ (2 * n - 7) * Q ^ 4 = Q ^ (2 * (n - 1) - 1) := by
    rw [← pow_add, show 2 * n - 7 + 4 = 2 * (n - 1) - 1 by omega]
  have hQ2 : Q ^ (2 * n - 7) * Q ^ 2 = Q ^ (2 * (n - 2) - 1) := by
    rw [← pow_add, show 2 * n - 7 + 2 = 2 * (n - 2) - 1 by omega]
  have hQ3 : Q ^ (2 * n - 7) = Q ^ (2 * (n - 3) - 1) := by
    congr 1; omega
  have hexpand :
      Q ^ (2 * n - 7) *
        (C (((n : ℤ) - 1) * ((n : ℤ) - 2)) *
          (C (P0 n) * (Q ^ 6 * (1 + X ^ 2)) +
           C (P1 n) * (X * (Q ^ 4 * (1 + X ^ 2))) +
           C (P2 n) * (X ^ 2 * (Q ^ 2 * (1 + X ^ 2))) +
           C (P3 n) * (X ^ 3 * (1 + X ^ 2)))) =
      C (((n : ℤ) - 1) * ((n : ℤ) - 2)) *
        (C (P0 n) * (Q ^ (2 * n - 1) * (1 + X ^ 2)) +
         C (P1 n) * (X ^ 1 * (Q ^ (2 * (n - 1) - 1) * (1 + X ^ 2))) +
         C (P2 n) * (X ^ 2 * (Q ^ (2 * (n - 2) - 1) * (1 + X ^ 2))) +
         C (P3 n) * (X ^ 3 * (Q ^ (2 * (n - 3) - 1) * (1 + X ^ 2)))) := by
    rw [← hQ0, ← hQ1, ← hQ2, ← hQ3]
    ring
  rw [hexpand] at hzero
  simp only [coeff_C_mul, coeff_add] at hzero
  rw [coeff_X_pow_mul 1 (n - 1) (by omega), coeff_X_pow_mul 2 (n - 1) (by omega),
      coeff_X_pow_mul 3 (n - 1) (by omega)] at hzero
  have hs1 : n - 1 - 1 = n - 1 - 1 := rfl
  have hs2 : n - 1 - 2 = n - 2 - 1 := by omega
  have hs3 : n - 1 - 3 = n - 3 - 1 := by omega
  rw [hs2, hs3, ← a_eq_coeff n (by omega), ← a_eq_coeff (n - 1) (by omega),
      ← a_eq_coeff (n - 2) (by omega), ← a_eq_coeff (n - 3) (by omega)] at hzero
  have hnz : (((n : ℤ) - 1) * ((n : ℤ) - 2)) ≠ 0 := by nlinarith
  have hrec : P0 n * a n + P1 n * a (n - 1) + P2 n * a (n - 2) + P3 n * a (n - 3) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hnz
  unfold P0 P1 P2 P3 at hrec
  linarith

end A025187Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a025187.main :=
  A025187Proof.main_proof
