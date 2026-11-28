import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R1
import Mathlib

-- Reduction ErdosMoser.erdos_moser_conjecture.R1.H2.R1.H1.R1 of step ErdosMoser.erdos_moser_conjecture.R1.H2.R1.H1
-- Credit: @rickmanelius

/-!
# Erdős-Moser, case `m ≡ 7 (mod 9)`: split by the size of `m / k`

The step: no solution of `S_k(m) = m ^ k` (`S_k(m) = 1 ^ k + ... + (m - 1) ^ k`) with `k` even,
`k + 2 ≤ m ≤ 2 k + 1`, `m ≡ 7 (mod 9)`, and the congruence and squarefreeness conditions of the
parent reduction.

Proved below, with no hypothesis (`powerSum_lt`): the lower range `m ≤ 1.44 k`. Reading the sum
backwards, `S_k(m) / m ^ k = ∑_{j = 1}^{m - 1} (1 - j / m) ^ k ≤ ∑_j q ^ j` with `q = e^(-k / m)`,
since `1 - x ≤ e^(-x)`. For `25 m ≤ 36 k` we have `k / m ≥ 25 / 36 > log 2`, so `q < 1 / 2` and the
geometric sum is below `1`: `S_k(m) < m ^ k`. (This is the classical bound `m > k / log 2`.)

What is left, by the size of `m`:
* `H1`: the window `1.44 k < m < 3 (k + 1) / 2`, the open core;
* `H2`: `3 (k + 1) / 2 ≤ m ≤ 2 k + 1`, where Krzysztofek (1966) shows that `S_k(m) > m ^ k`
  (a known range, by sharper estimates of the sum).
-/

namespace OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R1_H1_R1

open Finset

/-- The window `1.44 k < m < 3 (k + 1) / 2`. -/
def H1 : Prop := ∀ k m : ℕ, Even k → 2 ≤ k → 4 ≤ m → k + 2 ≤ m → m ≤ 2 * k + 1 →
  m % 8 = 3 → m % 9 = 7 →
  Squarefree (m - 1) → Squarefree ((m + 1) / 4) → Squarefree (2 * m - 1) →
  Squarefree (2 * m + 1) →
  (∀ p : ℕ, p.Prime → p ∣ m - 1 → (p - 1) ∣ k ∧ p ∣ (m - 1) / p + 1) →
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m + 1 → (p - 1) ∣ k ∧ p ∣ (m + 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m - 1 → (p - 1) ∣ k ∧ p ∣ (2 * m - 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m + 1 → (p - 1) ∣ k ∧ p ∣ (2 * m + 1) / p + 4) →
  (∀ p : ℕ, p.Prime → p ∣ m → ¬ (p - 1) ∣ k) →
  36 * k < 25 * m → 2 * m < 3 * (k + 1) →
  ErdosMoser.powerSum k m ≠ m ^ k

/-- The range `3 (k + 1) / 2 ≤ m` (Krzysztofek's bound). -/
def H2 : Prop := ∀ k m : ℕ, Even k → 2 ≤ k → 4 ≤ m → k + 2 ≤ m → m ≤ 2 * k + 1 →
  m % 8 = 3 → m % 9 = 7 →
  Squarefree (m - 1) → Squarefree ((m + 1) / 4) → Squarefree (2 * m - 1) →
  Squarefree (2 * m + 1) →
  (∀ p : ℕ, p.Prime → p ∣ m - 1 → (p - 1) ∣ k ∧ p ∣ (m - 1) / p + 1) →
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m + 1 → (p - 1) ∣ k ∧ p ∣ (m + 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m - 1 → (p - 1) ∣ k ∧ p ∣ (2 * m - 1) / p + 2) →
  (∀ p : ℕ, p.Prime → p ∣ 2 * m + 1 → (p - 1) ∣ k ∧ p ∣ (2 * m + 1) / p + 4) →
  (∀ p : ℕ, p.Prime → p ∣ m → ¬ (p - 1) ∣ k) →
  3 * (k + 1) ≤ 2 * m →
  ErdosMoser.powerSum k m ≠ m ^ k

/-- `1 - x ≤ e^(-x)`, raised to the power `k`, for `0 ≤ 1 - x`. -/
theorem pow_le_exp {x : ℝ} (hx : x ≤ 1) (k : ℕ) : (1 - x) ^ k ≤ Real.exp (-(k * x)) := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h0 : 0 ≤ 1 - x := by linarith
  calc (1 - x) ^ k ≤ Real.exp (-x) ^ k := pow_le_pow_left₀ h0 h1 k
    _ = Real.exp (-(k * x)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- The terms of the reflected power sum against a geometric sequence. -/
theorem term_le (k m i : ℕ) (hi : i < m) :
    ((m - 1 - i : ℕ) : ℝ) ^ k ≤ (m : ℝ) ^ k * Real.exp (-(k : ℝ) / m) ^ (i + 1) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hcast : ((m - 1 - i : ℕ) : ℝ) = m * (1 - ((i : ℝ) + 1) / m) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    field_simp
    push_cast
    ring
  have hx : ((i : ℝ) + 1) / m ≤ 1 := by
    rw [div_le_one hm]
    exact_mod_cast (show i + 1 ≤ m by omega)
  rw [hcast, mul_pow]
  have hpow := pow_le_exp hx k
  have he : Real.exp (-(k * (((i : ℝ) + 1) / m))) = Real.exp (-(k : ℝ) / m) ^ (i + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [he] at hpow
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A geometric sum. -/
theorem half_sum (m : ℕ) : ∑ i ∈ range m, ((1 : ℝ) / 2) ^ (i + 1) = 1 - (1 / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    ring

/-- Below `m = 1.44 k` the power sum is too small: `S_k(m) < m ^ k`, since
`S_k(m) / m ^ k = ∑ (1 - j / m) ^ k ≤ ∑ e^(-j k / m)` and `e^(-k / m) < 1/2`. -/
theorem powerSum_lt (k m : ℕ) (hm : 1 ≤ m) (h : 25 * m ≤ 36 * k) :
    ErdosMoser.powerSum k m < m ^ k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  -- the geometric ratio is at most one half
  have hq : Real.exp (-(k : ℝ) / m) ≤ 1 / 2 := by
    have hlog : Real.log 2 < (k : ℝ) / m := by
      have h1 : (25 : ℝ) / 36 ≤ (k : ℝ) / m := by
        rw [div_le_div_iff₀ (by norm_num) hmR]
        exact_mod_cast (by omega : 25 * m ≤ k * 36)
      have h2 := Real.log_two_lt_d9
      linarith
    have : Real.exp (-(k : ℝ) / m) ≤ Real.exp (-Real.log 2) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      linarith
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at this
    linarith
  have hq0 : 0 ≤ Real.exp (-(k : ℝ) / m) := (Real.exp_pos _).le
  have hk : k ≠ 0 := by omega
  -- the power sum over `range m`, read backwards
  have hN : ErdosMoser.powerSum k m = ∑ i ∈ range m, i ^ k := by
    unfold ErdosMoser.powerSum
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m)]
    simp [zero_pow hk]
  have hS : (ErdosMoser.powerSum k m : ℝ) = ∑ i ∈ range m, ((m - 1 - i : ℕ) : ℝ) ^ k := by
    rw [hN]
    push_cast
    exact (Finset.sum_range_reflect (fun i : ℕ => ((i : ℕ) : ℝ) ^ k) m).symm
  have hbound : ∑ i ∈ range m, ((m - 1 - i : ℕ) : ℝ) ^ k ≤
      ∑ i ∈ range m, (m : ℝ) ^ k * ((1 : ℝ) / 2) ^ (i + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    calc ((m - 1 - i : ℕ) : ℝ) ^ k ≤ (m : ℝ) ^ k * Real.exp (-(k : ℝ) / m) ^ (i + 1) :=
          term_le k m i (Finset.mem_range.mp hi)
      _ ≤ (m : ℝ) ^ k * ((1 : ℝ) / 2) ^ (i + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ hq0 hq _
  have hgeo : ∑ i ∈ range m, (m : ℝ) ^ k * ((1 : ℝ) / 2) ^ (i + 1) < (m : ℝ) ^ k := by
    rw [← Finset.mul_sum, half_sum]
    have h1 : (0 : ℝ) < (1 / 2) ^ m := by positivity
    have h2 : (0 : ℝ) < (m : ℝ) ^ k := by positivity
    nlinarith
  have hR : (ErdosMoser.powerSum k m : ℝ) < (m : ℝ) ^ k := by
    rw [hS]
    linarith
  exact_mod_cast hR

theorem main : H1 → H2 → OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R1.H1 := by
  intro h1 h2
  unfold OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R1.H1
  intro k m he hk2 hm4 hkm hku h83 r9 s1 s2 s3 s4 q1 q2 q3 q4 q5
  by_cases hlow : 25 * m ≤ 36 * k
  · exact (powerSum_lt k m (by omega) hlow).ne
  · by_cases hhigh : 3 * (k + 1) ≤ 2 * m
    · exact h2 k m he hk2 hm4 hkm hku h83 r9 s1 s2 s3 s4 q1 q2 q3 q4 q5 hhigh
    · exact h1 k m he hk2 hm4 hkm hku h83 r9 s1 s2 s3 s4 q1 q2 q3 q4 q5 (by omega) (by omega)

end OMA.R_ErdosMoser_erdos_moser_conjecture_R1_H2_R1_H1_R1
