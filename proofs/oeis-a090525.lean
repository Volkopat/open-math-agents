import OMAStatements.S_oeis_a090525
import Mathlib

open OMA.S_oeis_a090525

private theorem quotientTwo (N : ℕ) (hN : 4 ≤ N) : N / (N / 2) = 2 := by
  have positive : 0 < N / 2 := by omega
  have lower : 2 ≤ N / (N/2) :=
    (Nat.le_div_iff_mul_le positive).mpr (by omega)
  have upper : N / (N/2) < 3 :=
    (Nat.div_lt_iff_lt_mul positive).mpr (by omega)
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a090525.main := by
  intro n hn hz
  have minimum : 4 ≤ n^n := calc
    4 = 2 * 2 := by decide
    _ ≤ n * n := Nat.mul_le_mul hn hn
    _ = n^2 := (pow_two _).symm
    _ ≤ n^n := Nat.pow_le_pow_right (by omega) hn
  have nonempty : {k : ℕ | (n^n / k).Prime}.Nonempty := by
    refine ⟨n^n/2, ?_⟩
    change (n^n / (n^n/2)).Prime
    rw [quotientTwo _ minimum]
    exact Nat.prime_two
  have atMinimum : (n^n / a n).Prime :=
    Nat.sInf_mem nonempty
  exact Nat.not_prime_zero (by simpa only [hz, Nat.div_zero] using atMinimum)