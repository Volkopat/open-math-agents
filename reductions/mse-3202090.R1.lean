import OMAStatements.S_mse_3202090
import Mathlib

/- Both base primes occur to valuation one in the common value.
Lifting the exponent at the multiplicative order gives two Fermat
quotient obstructions and excludes either prime from the other
exponent minus one. H2 retains uniqueness under these restrictions. -/
namespace OMA.R_mse_3202090_R1

def H1 : Prop :=
  ∀ p q n m : ℕ, p.Prime → q.Prime → Odd p → Odd q → q < p → 1 < n → 1 < m →
    p ^ n - p = q ^ m - q →
    (¬ p ^ 2 ∣ q ^ (p - 1) - 1) ∧ (¬ q ^ 2 ∣ p ^ (q - 1) - 1) ∧
    (¬ p ∣ m - 1) ∧ (¬ q ∣ n - 1)

def H2 : Prop :=
  ∀ p q n m : ℕ, p.Prime → q.Prime → Odd p → Odd q → q < p → 1 < n → 1 < m →
    (¬ p ^ 2 ∣ q ^ (p - 1) - 1) → (¬ q ^ 2 ∣ p ^ (q - 1) - 1) →
    (¬ p ∣ m - 1) → (¬ q ∣ n - 1) →
    p ^ n - p = q ^ m - q → p = 13 ∧ n = 3 ∧ q = 3 ∧ m = 7

theorem main : H1 → H2 → type_of% @OMA.S_mse_3202090.main := by
  intro obstructions residual p q n m hp hq op oq lt hn hm eqn
  obtain ⟨fermatP, fermatQ, expP, expQ⟩ :=
    obstructions p q n m hp hq op oq lt hn hm eqn
  exact residual p q n m hp hq op oq lt hn hm fermatP fermatQ expP expQ eqn

end OMA.R_mse_3202090_R1
