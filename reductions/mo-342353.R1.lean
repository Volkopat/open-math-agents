import OMAStatements.S_mo_342353
import Mathlib

namespace OMA.R_mo_342353_R1

def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ((Nat.choose (n - 1) ((n - 1) / 2) : ℤ) ≡ (-1) ^ ((n - 1) / 2) * 4 ^ (n - 1) [ZMOD (n : ℤ) ^ 3]) → ∀ p : ℕ, p.Prime → p ∣ n → ∀ i : ℕ,
      ((n-1)/2) / p^i % p ≤ (n-1) / p^i % p

def H2 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → (∀ p : ℕ, p.Prime → p ∣ n → ∀ i : ℕ,
      ((n-1)/2) / p^i % p ≤ (n-1) / p^i % p) → ((Nat.choose (n - 1) ((n - 1) / 2) : ℤ) ≡ (-1) ^ ((n - 1) / 2) * 4 ^ (n - 1) [ZMOD (n : ℤ) ^ 3]) → n.Prime

theorem main : H1 → H2 → type_of% @OMA.S_mo_342353.main := by
  intro digits rest n hn ho h
  exact rest n hn ho (digits n hn ho h) h

end OMA.R_mo_342353_R1
