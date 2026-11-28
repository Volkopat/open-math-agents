import OMAStatements.S_oeis_a296161

-- Original Lean proof: @ivillar.
-- Barker's recurrence equates consecutive second differences with step 4.

namespace A296161Proof

open OMA.S_oeis_a296161

private theorem sumK (n m : ℕ) (hm : m ≤ n) :
    ((∑ i ∈ Finset.Icc 1 m, (n - i) * (i % 2) : ℕ) : ℤ) =
      (((m + 1) / 2 : ℕ) : ℤ) * n - (((m + 1) / 2 : ℕ) : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega), Nat.cast_mul,
      Nat.cast_sub (show m + 1 ≤ n by omega)]
    rcases Nat.mod_two_eq_zero_or_one (m + 1) with h | h
    · simp [h, show (m + 1 + 1) / 2 = (m + 1) / 2 by omega]
    · have e : ((m + 1 : ℕ) : ℤ) = 2 * (((m + 1) / 2 : ℕ) : ℤ) + 1 := by
        exact_mod_cast (show m + 1 = 2 * ((m + 1) / 2) + 1 by omega)
      rw [h, show (m + 1 + 1) / 2 = (m + 1) / 2 + 1 by omega]
      push_cast at e ⊢
      linear_combination -e

private def k (n : ℕ) : ℕ := (n / 2 + 1) / 2

private theorem closed (n : ℕ) : (a n : ℤ) = k n * (n : ℤ) - (k n : ℤ) ^ 2 :=
  sumK n (n / 2) (Nat.div_le_self n 2)

theorem secondDiff (m : ℕ) : (a (m + 8) : ℤ) - 2 * a (m + 4) + a m = 6 := by
  have shift (d : ℕ) : k (m + 4 * d) = k m + d := by
    unfold k
    omega
  simp only [closed, show k (m + 8) = k m + 2 from shift 2,
    show k (m + 4) = k m + 1 from shift 1]
  push_cast
  ring

end A296161Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a296161.main := by
  intro n hn
  have h₀ := A296161Proof.secondDiff (n - 8)
  have h₁ := A296161Proof.secondDiff (n - 9)
  rw [show n - 8 + 8 = n by omega, show n - 8 + 4 = n - 4 by omega] at h₀
  rw [show n - 9 + 8 = n - 1 by omega, show n - 9 + 4 = n - 5 by omega] at h₁
  linear_combination h₀ - h₁
