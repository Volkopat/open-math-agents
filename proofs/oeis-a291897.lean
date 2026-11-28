import OMAStatements.S_oeis_a291897
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Positivity

/-! The arithmetic used in the centered expansion of the Euler polynomial. -/

namespace A291897Proof

/-- The coefficient of `X` in the centered expansion is a multiple of `m`.
    All higher powers of `X` give multiples of `m²` when evaluated at `m`. -/
theorem square_dvd_centered_sum (e : ℕ → ℤ) (m : ℕ) (hzero : e m = 0) :
    (m : ℤ) ^ 2 ∣ ∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℤ) * e (m - j) * (m : ℤ) ^ j := by
  apply Finset.dvd_sum
  intro j _
  cases j with
  | zero => simp [hzero]
  | succ j =>
    cases j with
    | zero =>
      refine ⟨e (m - 1), ?_⟩
      change (m.choose 1 : ℤ) * e (m - 1) * (m : ℤ) ^ 1 = _
      simp only [Nat.choose_one_right, pow_one]
      ring
    | succ k =>
      refine ⟨(m.choose (k + 2) : ℤ) * e (m - (k + 2)) * (m : ℤ)^k, ?_⟩
      simp only [pow_succ]
      ring

/-- Reduction of a fraction with power-of-two denominator preserves
    divisibility of its numerator by the square of an odd integer. -/
theorem square_dvd_reduced_num (m a : ℤ) (hodd : Odd m) (k : ℕ)
    (ha : m ^ 2 ∣ a) : m ^ 2 ∣ (Rat.divInt a (2 ^ k)).num := by
  let q := Rat.divInt a (2 ^ k)
  have hden : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have htwo : (2 : ℤ) ^ k ≠ 0 := by positivity
  have hcross : q.num * (2 : ℤ) ^ k = a * (q.den : ℤ) :=
    (Rat.divInt_eq_divInt_iff hden htwo).mp (Rat.num_divInt_den q)
  have hbase : IsCoprime m 2 := by
    obtain ⟨t, ht⟩ := hodd
    exact ⟨1, -t, by omega⟩
  have hc : IsCoprime (m ^ 2) ((2 : ℤ) ^ k) := hbase.pow
  apply hc.dvd_of_dvd_mul_right
  change m ^ 2 ∣ q.num * (2 : ℤ) ^ k
  rw [hcross]
  exact dvd_mul_of_dvd_left ha _

end A291897Proof

open OMA.S_oeis_a291897

theorem OMA.solution : type_of% @OMA.S_oeis_a291897.main := by
  intro n hn
  let m := 2 * n - 1
  have hm : (m : ℤ) = 2 * (n : ℤ) - 1 := by dsimp [m]; omega
  have hodd : Odd (m : ℤ) := ⟨(n : ℤ) - 1, by omega⟩
  have hp : m % 2 = 1 := by dsimp [m]; omega
  have hzero : secant m = 0 := by rw [secant, if_pos hp]
  change (2 * (n : ℤ) - 1) ^ 2 ∣
    (Rat.divInt (centeredEuler m (2 * (n : ℤ) - 1)) (2 ^ m)).num
  rw [← hm]
  exact A291897Proof.square_dvd_reduced_num (m : ℤ) _ hodd m
    (A291897Proof.square_dvd_centered_sum secant m hzero)
