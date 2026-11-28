import Mathlib

/-!
# Periods of the binary sequences in OEIS A353890

Samuel Harkness, OEIS A353890 (2022), https://oeis.org/A353890.
Jacobsthal numbers follow OEIS A001045, https://oeis.org/A001045.
Formalization by @saientropy.
-/

namespace OMA.S_oeis_a353890

/-- The term is one when the first and second differences of the powers are coprime. -/
def binaryTerm (n m : ℕ) : ℕ :=
  let x : ℤ := m
  let first := (x + 1) ^ n - x ^ n
  let second := (x + 2) ^ n - 2 * (x + 1) ^ n + x ^ n
  if Int.gcd first second = 1 then 1 else 0

/-- The sequence begins at index one. -/
def IsPositivePeriod (n t : ℕ) : Prop :=
  0 < t ∧ ∀ m : ℕ, 0 < m → binaryTerm n (m + t) = binaryTerm n m

/-- Consecutive Jacobsthal numbers, starting with the pair (0, 1). -/
def jacobsthalPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let prev := jacobsthalPair n
    (prev.2, prev.2 + 2 * prev.1)

def jacobsthal (n : ℕ) : ℕ := (jacobsthalPair n).1

/-- Index 2 is the first exponent in A353890. -/
def IsProperExponentDivisor (d n : ℕ) : Prop := 2 ≤ d ∧ d < n ∧ d ∣ n

/-- Harkness conjectured that each sequence has a least positive period and gave two
formulas for its greatest prime factor at prime exponents at least five. For a composite
exponent, the prime factors of every indexed proper divisor's period are inherited.
Every remaining prime factor has the form `n * k + 1`. Prime exponents have no such
proper divisors. -/
theorem main :
    ∃ a : ℕ → ℕ,
      (∀ n : ℕ, 2 ≤ n → IsLeast {t : ℕ | IsPositivePeriod n t} (a n)) ∧
      (∀ n : ℕ, n.Prime → 5 ≤ n →
        IsGreatest ((a n).primeFactors : Set ℕ) (Nat.totient (2 ^ n + 1) / 2 + 1) ∧
          Nat.totient (2 ^ n + 1) / 2 + 1 = jacobsthal n) ∧
      (∀ n : ℕ, 2 ≤ n →
        (∀ p ∈ (a n).primeFactors,
          (∃ k : ℕ, p = n * k + 1) ∨
            ∃ d : ℕ, IsProperExponentDivisor d n ∧ p ∈ (a d).primeFactors) ∧
        ∀ d : ℕ, IsProperExponentDivisor d n → (a d).primeFactors ⊆ (a n).primeFactors) := by
  sorry

end OMA.S_oeis_a353890
