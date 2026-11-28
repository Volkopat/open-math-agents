import Mathlib

/-!
# OEIS A122045: the odd composites m with m dividing the Euler number E(m-1)

Source: https://oeis.org/A122045 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry: Euler (or secant) numbers E(n), with e.g.f. sech(x). Comment (Thomas Ordowski,
Feb 06 2020): Odd primes p such that p | E(p-1) are primes p == 1 (mod 4), A002144. Conjecture:
odd composites m such that m | E(m-1) are Carmichael numbers m such that p == 1 (mod 4) for every
prime p|m, A265237.

Formalization notes:
* E is defined by the recurrence in the entry's formula section: E(0) = 1 and, for n ≥ 1,
  E(n) = -Sum_{k=1..floor(n/2)} C(n, 2k) E(n-2k). This is the e.g.f. identity cosh(x) sech(x) = 1
  read coefficient by coefficient, so E(n) are the Euler numbers (1, 0, -1, 0, 5, 0, -61, ...).
* IsCarmichael m is the definition of A002997: m > 1 is composite and a ^ (m - 1) ≡ 1 (mod m)
  for every a coprime to m. InA265237 m adds that every prime factor of m is ≡ 1 (mod 4), as
  the comment describes A265237.
* Both sentences are read as characterizations (if and only if), the first for odd primes p and
  the second for odd composites m; main is their conjunction.
-/

namespace OMA.S_oeis_a122045

/-- Euler (secant) numbers (A122045), by the recurrence in the entry: `E 0 = 1` and, for `n ≥ 1`,
`E n = -∑_{k=1}^{⌊n/2⌋} C(n, 2k) E (n - 2k)`. -/
def E : ℕ → ℤ
  | 0 => 1
  | n + 1 => -∑ k : Fin ((n + 1) / 2), ((n + 1).choose (2 * (k + 1)) : ℤ) * E (n + 1 - 2 * (k + 1))

/-- Carmichael numbers (A002997): composite `m > 1` with `a ^ (m - 1) ≡ 1 (mod m)` for every `a`
coprime to `m`. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ a : ℕ, Nat.Coprime a m → a ^ (m - 1) % m = 1

/-- A265237: Carmichael numbers all of whose prime factors are `≡ 1 (mod 4)`. -/
def InA265237 (m : ℕ) : Prop := IsCarmichael m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p % 4 = 1

/-- The comment's two sentences: an odd prime `p` divides `E(p-1)` exactly when `p ≡ 1 (mod 4)`,
and an odd composite `m` divides `E(m-1)` exactly when `m` is in A265237. -/
theorem main :
    (∀ p : ℕ, p.Prime → p ≠ 2 → ((p : ℤ) ∣ E (p - 1) ↔ p % 4 = 1)) ∧
      (∀ m : ℕ, Odd m → 1 < m → ¬ m.Prime → ((m : ℤ) ∣ E (m - 1) ↔ InA265237 m)) := by
  sorry

end OMA.S_oeis_a122045
