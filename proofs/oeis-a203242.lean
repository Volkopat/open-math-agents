import OMAStatements.S_oeis_a203242
import Mathlib.Tactic

namespace A203242

open OMA.S_oeis_a203242 PowerSeries

private theorem sums_closed (n : ℕ) :
    sums n = (2 ^ (n + 1) - (n : ℚ) - 2,
      (4 ^ (n + 1) + 2) / 3 - (2 * (n : ℚ) + 2) * 2 ^ n +
      ((n : ℚ)^2 + 3 * (n : ℚ)) / 2) := by
  induction n with
  | zero => norm_num [sums]
  | succ n ih =>
    rw [sums, ih]
    simp only [Nat.cast_succ, pow_succ]
    have h4 : (4 : ℚ) ^ n = ((2 : ℚ) ^ n) ^ 2 := by
      rw [pow_two, ← mul_pow]
      norm_num
    rw [h4]
    apply Prod.ext <;> dsimp <;> ring

private theorem a_closed (n : ℕ) :
    a n = (4 ^ (n + 1) + 2) / 3 - (2 * (n : ℚ) + 2) * 2 ^ n +
      ((n : ℚ)^2 + 3 * (n : ℚ)) / 2 := congrArg Prod.snd (sums_closed n)

private theorem recurrence (n : ℕ) :
    (-103 * ((n : ℚ) + 4) + 258) * a (n+4) +
    (881 * ((n : ℚ) + 4) - 2116) * a (n+3) +
    6 * (-427 * ((n : ℚ) + 4) + 960) * a (n+2) +
    4 * (766 * ((n : ℚ) + 4) - 1545) * a (n+1) +
    16 * (-80 * ((n : ℚ) + 4) + 121) * a n = 0 := by
  norm_num [a_closed, pow_add, Nat.cast_add]
  ring

private theorem constant_recurrence (n : ℕ) :
    a (n+6) - 11 * a (n+5) + 47 * a (n+4) - 101 * a (n+3) +
      116 * a (n+2) - 68 * a (n+1) + 16 * a n = 0 := by
  norm_num [a_closed, pow_add, Nat.cast_add]
  ring

private theorem generating_function :
    (1 - X : ℚ⟦X⟧) ^ 3 * (1 - C 2 * X) ^ 2 * (1 - C 4 * X) * mk a =
      C 3 * X ^ 2 - C 2 * X ^ 3 - C 4 * X ^ 4 := by
  have hden : (1 - X : ℚ⟦X⟧) ^ 3 * (1 - C 2 * X) ^ 2 * (1 - C 4 * X) =
      1 - C 11 * X ^ 1 + C 47 * X ^ 2 - C 101 * X ^ 3 +
        C 116 * X ^ 4 - C 68 * X ^ 5 + C 16 * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [hden]
  ext n
  simp only [add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, coeff_mk,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]
  by_cases hn : n < 6
  · interval_cases n <;> norm_num [a_closed]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 6 := ⟨n - 6, by omega⟩
    simp
    linear_combination constant_recurrence k

theorem result : type_of% @OMA.S_oeis_a203242.main := by
  refine ⟨?_, generating_function⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k+4-1 = k+3 by omega, show k+4-2 = k+2 by omega,
    show k+4-3 = k+1 by omega, show k+4-4 = k by omega]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using recurrence k

end A203242

theorem OMA.solution : type_of% @OMA.S_oeis_a203242.main := A203242.result
