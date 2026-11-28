import Mathlib

/-!
# Proper factorizations whose factors' squares sum to their product

The four conjectures are due to Charles R. Hohn. A proper factorization here
has at least two factors, all greater than one. A squareful number is divisible
by the square of every prime that divides it.

Source: https://oeis.org/A380902.
-/
namespace OMA.S_oeis_a380902

def represents (f : List ℕ) (n : ℕ) : Prop :=
  2 ≤ f.length ∧ (∀ a ∈ f, 2 ≤ a) ∧ f.prod = n ∧ (f.map (·^2)).sum = n

def terms : Set ℕ := {n | ∃ f, represents f n}

def squareful (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

theorem main : terms.Infinite ∧
    (∀ n ∈ terms, ¬Squarefree n) ∧
    (∀ n ∈ terms, squareful n → n=16 ∨ n=27) ∧
    (∀ n f, represents f n → (∀ p ∈ f, Nat.Prime p) → n=16 ∨ n=27) := by
  sorry

end OMA.S_oeis_a380902
