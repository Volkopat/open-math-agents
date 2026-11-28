import Mathlib

/-!
# OEIS A364470: a(n+4) = 4 a(n) for n >= 7

Source: https://oeis.org/A364470 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Israel, Jul 25 2023), offset 1: a(n) is the least k > a(n-1) such that
Omega(k * (a(n-1)+k)) = n, where Omega = A001222; a(1) = 1. Data: 1, 2, 7, 11, 13, 19, 32, 56, 80,
120, 128, 224, ... Formula: Conjecture: a(n+4) = 4*a(n) for n >= 7.

Formalization notes:
* Omega(n) = A001222(n) is the number of prime factors of n counted with multiplicity, the
  length of `Nat.primeFactorsList n`.
* `a 1 = 1` and, for n >= 2, `a n` is the infimum of the k > a(n-1) with
  Omega(k (a(n-1) + k)) = n, which is the least such k (the proof file shows the set is
  nonempty at every n). `a 0 = 0` is a placeholder outside the entry's range and is not used.
* `main` is the conjecture: a(n+4) = 4 a(n) for every n >= 7.
* Controls proved in the proof file: a(1..11) = 1, 2, 7, 11, 13, 19, 32, 56, 80, 120, 128.
-/

namespace OMA.S_oeis_a364470

/-- Omega(n) = A001222(n), the number of prime factors of n counted with multiplicity. -/
def Omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- A364470: a(1) = 1, and for n >= 2, a(n) is the least k > a(n-1) with
Omega(k (a(n-1) + k)) = n (a(0) = 0 is a placeholder outside the entry's range). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => sInf {k | a (n + 1) < k ∧ Omega (k * (a (n + 1) + k)) = n + 2}

/-- Israel's conjecture: a(n+4) = 4 a(n) for n >= 7. -/
theorem main : ∀ n : ℕ, 7 ≤ n → a (n + 4) = 4 * a n := by
  sorry

end OMA.S_oeis_a364470
