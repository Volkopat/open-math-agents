import Mathlib

/-!
# OEIS A391216: for p prime, a(p) = A098026(p)

Source: https://oeis.org/A391216 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Juri-Stepan Gerasimov, Jan 03 2026), offset 0: a(n) is the least k for which
omega(k)*omega(k + 1) = n where omega = A001221. The formula section states: Conjecture: For p
prime, a(p) = A098026(p). (Vaclav Kotesovec, Jan 03 2026.) A098026 (Lekraj Beedassy, Sep 10 2004),
offset 1: Smallest prime p such that p+1 is the product of exactly n distinct prime numbers.

Formalization notes:
* omega(n) = A001221(n) is the number of distinct primes dividing n (`n.primeFactors.card`).
* a(n) is the least k >= 1 with omega(k) * omega(k + 1) = n; k = 0 is excluded, as the data
  a(0) = 1 show (omega(0) * omega(1) = 0).
* A098026(n) is the least prime p such that p + 1 is the product of exactly n distinct primes,
  that is, p + 1 is squarefree with n prime factors.
* `main` states the conjecture as worded: a(p) = A098026(p) for every prime p.
-/

namespace OMA.S_oeis_a391216

/-- omega(n) = A001221(n): the number of distinct primes dividing n. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- A391216(n): the least k >= 1 with omega(k) * omega(k + 1) = n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | 1 ≤ k ∧ omega k * omega (k + 1) = n}

/-- A098026(n): the smallest prime p such that p + 1 is the product of exactly n distinct primes. -/
noncomputable def b (n : ℕ) : ℕ := sInf {p | p.Prime ∧ Squarefree (p + 1) ∧ omega (p + 1) = n}

/-- Kotesovec's conjecture: for every prime p, a(p) = A098026(p). -/
theorem main : ∀ p : ℕ, p.Prime → a p = b p := by
  sorry

end OMA.S_oeis_a391216
