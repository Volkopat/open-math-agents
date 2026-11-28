import OMAStatements.S_mse_1595838
import Mathlib

namespace OMA.R_mse_1595838_R1

def H1 : Prop := ∀ n m : ℕ, 8 < n → n < m → n ∣ m →
    (Nat.fib n).totient ≠ (Nat.fib m).totient

def H2 : Prop := ∀ n m : ℕ, 8 < n → n < m → ¬ n ∣ m →
    (Nat.fib n).totient ≠ (Nat.fib m).totient

theorem main : H1 → H2 → type_of% @OMA.S_mse_1595838.main := by
  intro h1 h2 n m hn hm hne
  have aux (a b : ℕ) (ha : 8 < a) (hab : a < b) :
      (Nat.fib a).totient ≠ (Nat.fib b).totient := by
    by_cases h : a ∣ b
    · exact h1 a b ha hab h
    · exact h2 a b ha hab h
  rcases lt_or_gt_of_ne hne with h | h
  · exact aux n m hn h
  · exact (aux m n hm h).symm

end OMA.R_mse_1595838_R1
