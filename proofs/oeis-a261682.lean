import OMAStatements.S_oeis_a261682
import Mathlib

/-!
# A261682: Mathar's recurrence

With c(k) = binomial(2k, k): a(2k) = 4^k + c(k)(2k+1)/(k+1) − 1 (using
binomial(2k+1, k) = c(k)(2k+1)/(k+1)) and a(2k+1) = 2^(2k+1) + (3/2)c(k+1) − 1. Splitting by
the parity of n and using (j+1)c(j+1) = 2(2j+1)c(j), every term of the recurrence becomes a
rational function of k times c(k), plus multiples of 4^k and constants, and the identity is
checked by clearing denominators.
-/

namespace A261682Proof

/-- The central binomial coefficient as a rational number. -/
noncomputable def c (j : ℕ) : ℚ := ((2 * j).choose j : ℚ)

theorem c_succ (j : ℕ) : c (j + 1) = 2 * (2 * j + 1) / (j + 1) * c j := by
  have h := Nat.succ_mul_centralBinom_succ j
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  unfold c
  have h' : ((j : ℚ) + 1) * ((2 * (j + 1)).choose (j + 1) : ℚ) =
      2 * (2 * j + 1) * ((2 * j).choose j : ℚ) := by
    exact_mod_cast h
  field_simp
  linear_combination h'

theorem odd_choose (k : ℕ) : ((2 * k + 1).choose k : ℚ) = c k * (2 * k + 1) / (k + 1) := by
  have h := Nat.add_one_mul_choose_eq (2 * k) k
  rw [Nat.choose_symm_half] at h
  have h' : ((2 * k : ℕ) + 1 : ℚ) * ((2 * k).choose k : ℚ) = ((2 * k + 1).choose k : ℚ) * (k + 1) := by
    exact_mod_cast h
  unfold c
  push_cast at h'
  field_simp
  linear_combination -h'

theorem a_even (k : ℕ) : OMA.S_oeis_a261682.a (2 * k) = 2 ^ (2 * k) + c k * (2 * k + 1) / (k + 1) - 1 := by
  unfold OMA.S_oeis_a261682.a
  rw [show 2 * k % 2 = 0 by omega, show (2 * k + 0) / 2 = k by omega, odd_choose]
  push_cast
  ring

theorem a_odd (k : ℕ) : OMA.S_oeis_a261682.a (2 * k + 1) = 2 ^ (2 * k + 1) + 3 / 2 * c (k + 1) - 1 := by
  unfold OMA.S_oeis_a261682.a
  rw [show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
    show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
  unfold c
  push_cast
  ring

end A261682Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a261682.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    subst hj
    rw [show k + 2 + (k + 2) = 2 * (k + 2) by ring,
      show 2 * (k + 2) - 1 = 2 * (k + 1) + 1 by omega, show 2 * (k + 2) - 2 = 2 * (k + 1) by omega,
      show 2 * (k + 2) - 3 = 2 * k + 1 by omega, show 2 * (k + 2) - 4 = 2 * k by omega,
      A261682Proof.a_even, A261682Proof.a_odd, A261682Proof.a_even, A261682Proof.a_odd,
      A261682Proof.a_even, A261682Proof.c_succ (k + 1), A261682Proof.c_succ k]
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    subst hj
    rw [show 2 * (k + 2) + 1 - 1 = 2 * (k + 2) by omega,
      show 2 * (k + 2) + 1 - 2 = 2 * (k + 1) + 1 by omega, show 2 * (k + 2) + 1 - 3 = 2 * (k + 1) by omega,
      show 2 * (k + 2) + 1 - 4 = 2 * k + 1 by omega,
      A261682Proof.a_odd, A261682Proof.a_even, A261682Proof.a_odd, A261682Proof.a_even,
      A261682Proof.a_odd, A261682Proof.c_succ (k + 2), A261682Proof.c_succ (k + 1), A261682Proof.c_succ k]
    push_cast
    field_simp
    ring
