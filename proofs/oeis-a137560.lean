import OMAStatements.S_oeis_a137560

/-!
The coefficient of degree `k ≥ 1` has already stabilized after `k` iterates.
The proof uses the Catalan convolution, as suggested by the coefficient
stabilization recorded in https://oeis.org/A137560.
-/

namespace OMA.A137560Proof

open Polynomial Finset
open OMA.S_oeis_a137560

private theorem constant_zero (n : ℕ) : (P n).coeff 0 = 0 := by
  induction n with
  | zero => simp [P]
  | succ n ih => simp [P, pow_two, ih]

private theorem linear_coeff (n : ℕ) : (P (n + 1)).coeff 1 = 1 := by
  rw [P, coeff_add, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp [constant_zero]

private theorem higher_coeff (n d : ℕ) :
    (P (n + 1)).coeff (d + 2) =
      ∑ p ∈ antidiagonal d, (P n).coeff (p.1 + 1) * (P n).coeff (p.2 + 1) := by
  rw [P, coeff_add, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_succ']
  simp [constant_zero, coeff_X]

private theorem coeff_catalan (k : ℕ) :
    ∀ n : ℕ, k + 1 ≤ n → (P n).coeff (k + 1) = (catalan k : ℤ) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n hn
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    cases k with
    | zero => simpa only [catalan_zero, Nat.cast_one] using linear_coeff n
    | succ d =>
      rw [higher_coeff, catalan_succ', Nat.cast_sum]
      apply sum_congr rfl
      intro p hp
      have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      rw [ih p.1 (by omega) n (by omega), ih p.2 (by omega) n (by omega), Nat.cast_mul]

end OMA.A137560Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a137560.main := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨j + 1, fun n hn => ?_⟩
  simpa only [Nat.add_sub_cancel] using OMA.A137560Proof.coeff_catalan j n hn
