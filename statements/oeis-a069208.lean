import Mathlib

/-!
# A069208: sums of a multiplicative sequence over the powerful divisors

Source: https://oeis.org/A069208 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry: a(n) = Sum_{ d divides n } phi(n)/phi(d). Comment (Werner Schulte, Jan 23 2025):
Conjecture: Let (f(n)), n > 0, be a multiplicative sequence. Then holds:
  (1) p(f; n) = Sum_{d powerful number (A001694) dividing n} f(d) is multiplicative;
  (2) p(f; n) equals inverse Moebius transform of A112526(n) * f(n).

Formalization notes.
* A multiplicative sequence is a function `f` on the positive integers with f(1) = 1 and
  f(m n) = f(m) f(n) for coprime m, n. OEIS sequences have integer terms, so `f : ℕ → ℤ`; the
  value `f 0` is not used.
* A powerful number (A001694) is a positive integer d such that p^2 divides d for every prime p
  that divides d; 1 is powerful. The condition is written with `Nat.primeFactors`, the set of the
  primes that divide d.
* `chi` is A112526, the characteristic function of the powerful numbers.
* The inverse Moebius transform of a sequence b is n ↦ Sum_{d | n} b(d).
* `main` states both parts, for every multiplicative `f`.
-/

namespace OMA.S_oeis_a069208

/-- A112526: 1 if d is a powerful number, else 0. -/
def chi (d : ℕ) : ℤ := if ∀ p ∈ d.primeFactors, p ^ 2 ∣ d then 1 else 0

/-- p(f; n): the sum of f(d) over the powerful numbers d that divide n. -/
def P (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter (fun d => ∀ p ∈ d.primeFactors, p ^ 2 ∣ d), f d

/-- Schulte's conjecture: p(f; ·) is multiplicative, and it is the inverse Moebius transform of
A112526 * f. -/
theorem main : ∀ f : ℕ → ℤ, f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    (P f 1 = 1 ∧
      ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → P f (m * n) = P f m * P f n) ∧
    ∀ n : ℕ, 0 < n → P f n = ∑ d ∈ n.divisors, chi d * f d := by
  sorry

end OMA.S_oeis_a069208
