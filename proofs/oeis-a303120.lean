import OMAStatements.S_oeis_a303120
import Mathlib

/-!
# A303120: Barker's closed form and recurrence

Σ_{i=1..m} i(N − i) = N·m(m+1)/2 − m(m+1)(2m+1)/6 (induction on m). With N = n² and m = floor(n²/2)
(= 2t² for n = 2t, 2t² + 2t for n = 2t + 1) this is Barker's closed form, in which (−1)^n enters only
through the parity. The order-12 recurrence then holds because its characteristic polynomial
(1 − x)^7 (1 + x)^5 annihilates polynomials of degree ≤ 6 and (−1)^n times polynomials of degree ≤ 4;
it is checked symbolically from the closed form.
-/

namespace A303120Proof

theorem partialSum (N m : ℕ) (hm : m ≤ N) :
    ((∑ i ∈ Finset.Icc 1 m, i * (N - i) : ℕ) : ℚ) =
      (N : ℚ) * m * (m + 1) / 2 - (m : ℚ) * (m + 1) * (2 * m + 1) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega), Nat.cast_mul,
      Nat.cast_sub hm]
    push_cast
    ring

theorem closed (n : ℕ) :
    (OMA.S_oeis_a303120.a n : ℚ) =
      (n : ℚ) ^ 2 * (-4 + 3 * (1 + (-1) ^ n) * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 4) / 48 := by
  unfold OMA.S_oeis_a303120.a
  rw [partialSum _ _ (Nat.div_le_self _ _)]
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [show (t + t) ^ 2 / 2 = 2 * t ^ 2 by
      rw [show (t + t) ^ 2 = 2 * (2 * t ^ 2) by ring]; omega]
    rw [show (-1 : ℚ) ^ (t + t) = 1 by rw [← two_mul, pow_mul]; norm_num]
    push_cast
    ring
  · rw [show (2 * t + 1) ^ 2 / 2 = 2 * t ^ 2 + 2 * t by
      rw [show (2 * t + 1) ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 by ring]; omega]
    rw [show (-1 : ℚ) ^ (2 * t + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    push_cast
    ring

end A303120Proof

open OMA.S_oeis_a303120 in
theorem OMA.solution : type_of% @OMA.S_oeis_a303120.main := by
  refine ⟨fun n _ => A303120Proof.closed n, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
  have key : ((a (m + 13) : ℤ) : ℚ) =
      ((2 * a (m + 12) + 4 * a (m + 11) -
        10 * a (m + 10) - 5 * a (m + 9) +
        20 * a (m + 8) - 20 * a (m + 6) +
        5 * a (m + 5) + 10 * a (m + 4) -
        4 * a (m + 3) - 2 * a (m + 2) +
        a (m + 1) : ℤ) : ℚ) := by
    push_cast
    simp only [A303120Proof.closed]
    push_cast
    simp only [pow_add, pow_one]
    ring
  have key' := Int.cast_injective (α := ℚ) key
  rw [show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega,
    show m + 13 - 3 = m + 10 by omega, show m + 13 - 4 = m + 9 by omega,
    show m + 13 - 5 = m + 8 by omega, show m + 13 - 7 = m + 6 by omega,
    show m + 13 - 8 = m + 5 by omega, show m + 13 - 9 = m + 4 by omega,
    show m + 13 - 10 = m + 3 by omega, show m + 13 - 11 = m + 2 by omega,
    show m + 13 - 12 = m + 1 by omega]
  exact key'
