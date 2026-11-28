import OMAStatements.S_oeis_a083451
import Mathlib

/-!
# A083451: n concatenated n times exceeds n^n

With L the number of decimal digits of n, appending a copy of n gives R(k+1) = n + 10^L·R(k), so
R(k+1) ≥ n·(10^L)^k. Since n < 10^L, n^n = n·n^(n−1) < n·(10^L)^(n−1) ≤ R(n) for n > 1 (the digit
count argument in the entry).
-/

namespace PA083451

theorem rep_succ (n k : ℕ) :
    Nat.ofDigits 10 (List.flatten (List.replicate (k + 1) (Nat.digits 10 n))) =
      n + 10 ^ (Nat.digits 10 n).length *
        Nat.ofDigits 10 (List.flatten (List.replicate k (Nat.digits 10 n))) := by
  rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, Nat.ofDigits_digits]

theorem rep_ge (n k : ℕ) :
    n * (10 ^ (Nat.digits 10 n).length) ^ k ≤
      Nat.ofDigits 10 (List.flatten (List.replicate (k + 1) (Nat.digits 10 n))) := by
  induction k with
  | zero => rw [rep_succ]; simp
  | succ k ih =>
    rw [rep_succ, pow_succ]
    calc n * ((10 ^ (Nat.digits 10 n).length) ^ k * 10 ^ (Nat.digits 10 n).length)
        = 10 ^ (Nat.digits 10 n).length * (n * (10 ^ (Nat.digits 10 n).length) ^ k) := by ring
      _ ≤ 10 ^ (Nat.digits 10 n).length *
          Nat.ofDigits 10 (List.flatten (List.replicate (k + 1) (Nat.digits 10 n))) :=
        Nat.mul_le_mul_left _ ih
      _ ≤ _ := Nat.le_add_left _ _

end PA083451

theorem OMA.solution : type_of% @OMA.S_oeis_a083451.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : k ≠ 0 := by omega
  have hlt : k + 1 < 10 ^ (Nat.digits 10 (k + 1)).length := Nat.lt_base_pow_length_digits (by norm_num)
  have h1 : (k + 1) ^ k < (10 ^ (Nat.digits 10 (k + 1)).length) ^ k := Nat.pow_lt_pow_left hlt hk
  have h2 := PA083451.rep_ge (k + 1) k
  have h3 : (k + 1) ^ (k + 1) < OMA.S_oeis_a083451.concatRep (k + 1) := by
    unfold OMA.S_oeis_a083451.concatRep
    calc (k + 1) ^ (k + 1) = (k + 1) * (k + 1) ^ k := by ring
      _ < (k + 1) * (10 ^ (Nat.digits 10 (k + 1)).length) ^ k :=
        Nat.mul_lt_mul_of_pos_left h1 (by omega)
      _ ≤ _ := h2
  have h4 : ((k + 1 : ℕ) : ℤ) ^ (k + 1) < (OMA.S_oeis_a083451.concatRep (k + 1) : ℤ) := by
    exact_mod_cast h3
  linarith
