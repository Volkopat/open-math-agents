import OMAStatements.S_oeis_a005908

/-!
# Proof of OEIS A005908

We prove that the sequence `a 0 = 0`, `a 1 = 1`, `a (n + 2) = ⌊φ * a (n + 1)⌋ + ⌊φ * a n⌋`
satisfies the five-term linear recurrence `a n = 2 * a (n - 1) + a (n - 2) - a (n - 4) - a (n - 5)`
for all `n > 4` and the corresponding rational generating function identity.

We introduce two integer linear-recurrence sequences `A` and `B`, establish
`A (n + 2) = B (n + 1) + B n` and `B (n + 3) = B (n + 2) + B (n + 1) + A (n + 2) + A (n + 1) - 1`,
deduce that `d n = φ * A n - B n - 1 / √5` satisfies `d (n + 3) = φ' * (d (n + 2) + d (n + 1))`,
and bound `|d n| < 1 / √5` using the quadratic Lyapunov function
`Q x y = x ^ 2 + (3 / 2) * y ^ 2 + x * y`.
-/

namespace OMA.Proof_oeis_a005908

open OMA.S_oeis_a005908 PowerSeries

private def A : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | n + 5 => 2 * A (n + 4) + A (n + 3) - A (n + 1) - A n

private def B : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 3
  | 4 => 6
  | n + 5 => 2 * B (n + 4) + B (n + 3) - B (n + 1) - B n

private lemma A_rec (n : ℕ) :
    A (n + 5) = 2 * A (n + 4) + A (n + 3) - A (n + 1) - A n := rfl

private lemma B_rec (n : ℕ) :
    B (n + 5) = 2 * B (n + 4) + B (n + 3) - B (n + 1) - B n := rfl

private lemma A_eq_B_add (n : ℕ) : A (n + 2) = B (n + 1) + B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 | 3 | 4 => rfl
    | k + 5 =>
      have h4 := ih (k + 4) (by omega)
      have h3 := ih (k + 3) (by omega)
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hA := A_rec (k + 2)
      have hB1 := B_rec (k + 1)
      have hB0 := B_rec k
      simp only [Nat.add_assoc] at h4 h3 h1 h0 hA hB1 hB0 ⊢
      linarith

private lemma B_rel (n : ℕ) :
    B (n + 3) = B (n + 2) + B (n + 1) + A (n + 2) + A (n + 1) - 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 | 3 | 4 => rfl
    | k + 5 =>
      have h4 := ih (k + 4) (by omega)
      have h3 := ih (k + 3) (by omega)
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hB3 := B_rec (k + 3)
      have hB2 := B_rec (k + 2)
      have hB1 := B_rec (k + 1)
      have hA2 := A_rec (k + 2)
      have hA1 := A_rec (k + 1)
      simp only [Nat.add_assoc] at h4 h3 h1 h0 hB3 hB2 hB1 hA2 hA1 ⊢
      linarith

private noncomputable def d (n : ℕ) : ℝ :=
  Real.goldenRatio * (A n : ℝ) - (B n : ℝ) - 1 / Real.sqrt 5

private lemma d_rec (n : ℕ) :
    d (n + 3) = Real.goldenConj * (d (n + 2) + d (n + 1)) := by
  have hA : (A (n + 3) : ℝ) = (B (n + 2) : ℝ) + (B (n + 1) : ℝ) := by
    exact_mod_cast A_eq_B_add (n + 1)
  have hB : (B (n + 3) : ℝ) =
      (B (n + 2) : ℝ) + (B (n + 1) : ℝ) + (A (n + 2) : ℝ) + (A (n + 1) : ℝ) - 1 := by
    exact_mod_cast B_rel n
  have hs5 : Real.sqrt 5 ≠ 0 := by positivity
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq3 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by rw [pow_succ, hsq]
  unfold d
  rw [hA, hB, Real.goldenRatio, Real.goldenConj]
  field_simp [hs5]
  ring_nf
  rw [hsq, hsq3]
  ring

private noncomputable def Q (x y : ℝ) : ℝ := x ^ 2 + 3 / 2 * y ^ 2 + x * y

private lemma sqrt5_bounds : (21 / 10 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

private lemma Q_step (x y : ℝ) : Q y (Real.goldenConj * (x + y)) ≤ Q x y := by
  have hc2 : Real.goldenConj ^ 2 = Real.goldenConj + 1 := Real.goldenConj_sq
  have ⟨hs1, hs2⟩ := sqrt5_bounds
  have hc_lt : Real.goldenConj < -1 / 2 := by rw [Real.goldenConj]; linarith
  have hc_gt : -1 < Real.goldenConj := by rw [Real.goldenConj]; linarith
  have hid : Q x y - Q y (Real.goldenConj * (x + y)) =
      (1 / 2 + Real.goldenConj / 2) * x ^ 2 +
      (-Real.goldenConj / 2) * y ^ 2 +
      (-1 - 2 * Real.goldenConj) * (x + y) ^ 2 := by
    unfold Q
    rw [mul_pow, hc2]
    ring
  have h1 : 0 ≤ (1 / 2 + Real.goldenConj / 2) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg x)
  have h2 : 0 ≤ (-Real.goldenConj / 2) * y ^ 2 := mul_nonneg (by linarith) (sq_nonneg y)
  have h3 : 0 ≤ (-1 - 2 * Real.goldenConj) * (x + y) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg (x + y))
  linarith

private lemma Q_d_le (n : ℕ) : Q (d (n + 1)) (d (n + 2)) ≤ Q (d 1) (d 2) := by
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
    rw [show k + 1 + 2 = k + 3 from rfl, d_rec k, add_comm (d (k + 2)) (d (k + 1))]
    exact (Q_step (d (k + 1)) (d (k + 2))).trans ih

private lemma floor_A (n : ℕ) : ⌊Real.goldenRatio * (A n : ℝ)⌋ = B n := by
  cases n with
  | zero => simp [A, B]
  | succ k =>
    have ⟨hs1, hs2⟩ := sqrt5_bounds
    have hs_pos : (0 : ℝ) < Real.sqrt 5 := by linarith
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hd1 : d 1 = (3 - Real.sqrt 5) / (2 * Real.sqrt 5) := by
      unfold d
      simp only [A, B, Int.cast_one, mul_one, Real.goldenRatio]
      field_simp [hs_pos.ne']
      ring_nf
      rw [hsq]
      ring
    have hd2 : d 2 = d 1 := by simp [d, A, B]
    have hQ1 : Q (d 1) (d 2) = 7 / 2 * d 1 ^ 2 := by rw [hd2]; unfold Q; ring
    have hQ_lb : 5 / 6 * d (k + 1) ^ 2 ≤ Q (d (k + 1)) (d (k + 2)) := by
      unfold Q
      nlinarith [sq_nonneg (d (k + 1) + 3 * d (k + 2))]
    have hQ_ub : Q (d (k + 1)) (d (k + 2)) ≤ 7 / 2 * d 1 ^ 2 := by
      rw [← hQ1]; exact Q_d_le k
    have hd1_sq : d 1 ^ 2 = (3 - Real.sqrt 5) ^ 2 / 20 := by
      rw [hd1, div_pow, mul_pow, hsq]; ring
    have hd_sq_lt : d (k + 1) ^ 2 < (1 / Real.sqrt 5) ^ 2 := by
      have h1 : (1 / Real.sqrt 5) ^ 2 = 1 / 5 := by rw [div_pow, one_pow, hsq]
      rw [h1]
      have h3s : (3 - Real.sqrt 5) ^ 2 < (9 / 10 : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hinv_pos : (0 : ℝ) < 1 / Real.sqrt 5 := by positivity
    have hd_bounds : -(1 / Real.sqrt 5) < d (k + 1) ∧ d (k + 1) < 1 / Real.sqrt 5 := by
      constructor <;> nlinarith
    rw [Int.floor_eq_iff]
    have hdiff : Real.goldenRatio * (A (k + 1) : ℝ) - (B (k + 1) : ℝ) =
        d (k + 1) + 1 / Real.sqrt 5 := by unfold d; ring
    have h2inv : 1 / Real.sqrt 5 + 1 / Real.sqrt 5 < 1 := by
      rw [← add_div, div_lt_one hs_pos]; linarith
    constructor <;> linarith

private lemma a_eq_A (n : ℕ) : a n = A n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      rw [a, ih (k + 1) (by omega), ih k (by omega), floor_A (k + 1), floor_A k, A_eq_B_add k]

private lemma a_rec (n : ℕ) (hn : 4 < n) :
    a n = 2 * a (n - 1) + a (n - 2) - a (n - 4) - a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [a_eq_A, Nat.add_sub_cancel]
  have h1 : k + 5 - 1 = k + 4 := by omega
  have h2 : k + 5 - 2 = k + 3 := by omega
  have h4 : k + 5 - 4 = k + 1 := by omega
  rw [h1, h2, h4, A_rec]

private lemma a_gf :
    (X ^ 5 + X ^ 4 - X ^ 2 - 2 * X + 1) * PowerSeries.mk a =
      (X * (-X ^ 3 - X ^ 2 - X + 1) : PowerSeries ℤ) := by
  have hlhs : (X ^ 5 + X ^ 4 - X ^ 2 - 2 * X + 1) * PowerSeries.mk a =
      X ^ 5 * PowerSeries.mk a + X ^ 4 * PowerSeries.mk a - X ^ 2 * PowerSeries.mk a -
      X ^ 1 * PowerSeries.mk a - X ^ 1 * PowerSeries.mk a + PowerSeries.mk a := by ring
  have hrhs : (X * (-X ^ 3 - X ^ 2 - X + 1) : PowerSeries ℤ) =
      -(X ^ 4) - X ^ 3 - X ^ 2 + X := by ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_X_pow_mul', coeff_X_pow, coeff_X, coeff_mk, a_eq_A]
  match n with
  | 0 | 1 | 2 | 3 | 4 => decide
  | k + 5 =>
    have hrec := A_rec k
    simp only [show ¬(k + 5 = 4) by omega, show ¬(k + 5 = 3) by omega,
      show ¬(k + 5 = 2) by omega, show ¬(k + 5 = 1) by omega,
      show 5 ≤ k + 5 by omega, show 4 ≤ k + 5 by omega, show 2 ≤ k + 5 by omega,
      show 1 ≤ k + 5 by omega, ite_true, ite_false]
    have h1 : k + 5 - 5 = k := by omega
    have h2 : k + 5 - 4 = k + 1 := by omega
    have h3 : k + 5 - 2 = k + 3 := by omega
    have h4 : k + 5 - 1 = k + 4 := by omega
    rw [h1, h2, h3, h4]
    linarith

end OMA.Proof_oeis_a005908

open OMA.Proof_oeis_a005908 in
theorem OMA.solution : type_of% @OMA.S_oeis_a005908.main :=
  ⟨a_rec, a_gf⟩
