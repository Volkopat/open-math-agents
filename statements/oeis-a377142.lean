import Mathlib

/-!
# A377142: Numbers m such that phi(2*m-1)/2 = phi(2*m) - 1, where phi = A000010.

Source: https://oeis.org/A377142
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A377142 (Juri-Stepan Gerasimov, Oct 19 2024):
Conjecture 1: each term has the form p^(q-1), where p, q both some primes. Conjecture 2: sequence
is infinite.

Conventions:
* The sequence has offset 1 (data 2, 4, 5, 16, 64, 4096, 65536, 262144, ...).
* phi is the Euler totient function `Nat.totient`.
* The defining equation phi(2*m-1)/2 = phi(2*m) - 1 is an equation between rational numbers; it is
  written without division or subtraction as phi(2*m-1) + 2 = 2*phi(2*m) (helper `T`, for positive
  m; the natural subtraction 2*m - 1 is then exact).
* Both conjectures of the entry are formalized, as a conjunction; `infinite` is `Set.Infinite` of
  the set of all terms.
-/

namespace OMA.S_oeis_a377142

/-- m is a term of A377142: m > 0 and phi(2m-1)/2 = phi(2m) - 1. -/
def T (m : ℕ) : Prop := 0 < m ∧ Nat.totient (2 * m - 1) + 2 = 2 * Nat.totient (2 * m)

/-- The conjectures recorded in A377142. -/
theorem main : (∀ m : ℕ, T m → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p ^ (q - 1)) ∧
    Set.Infinite {m : ℕ | T m} := by
  sorry

end OMA.S_oeis_a377142
