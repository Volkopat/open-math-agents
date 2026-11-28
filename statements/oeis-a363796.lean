import Mathlib

/-!
# OEIS A363796: a(n) = -1 only when n = (q^2-1)/2 + k(q^2-q) for an odd prime q

Source: https://oeis.org/A363796 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Israel, Jun 22 2023), offset 1: a(n) is the least prime p such that p^n + 2*n is
prime, or -1 if there is no such p. Comment: If n = (q^2-1)/2 + k*(q^2-q) for some odd prime q and
integer k, then the only possible p is q, as otherwise q | p^n + 2*n. Conjecture: these are the only
cases where a(n) = -1.

Formalization notes:
* a n is an integer: the least prime p with p ^ n + 2 * n prime (Nat.find), or -1 when no prime
  p has that property; the existence test is classical.
* IsForm n says n = (q^2 - 1)/2 + k * (q^2 - q) for a prime q ≠ 2 and an integer k, computed in
  ℤ; the division is exact because q is odd.
* main says: for every n ≥ 1 (the offset), a n = -1 implies IsForm n. Reading the cases as the n of
  that form for which q^n + 2n is also composite gives a stronger conjecture, which main implies.
* Controls proved in the proof file: a 1 = 3 and a 12 = -1 (the form with q = 5, k = 0).
-/

namespace OMA.S_oeis_a363796

/-- a(n): the least prime `p` with `p ^ n + 2 * n` prime, or `-1` if there is none. -/
noncomputable def a (n : ℕ) : ℤ :=
  @dite ℤ (∃ p : ℕ, p.Prime ∧ (p ^ n + 2 * n).Prime) (Classical.propDecidable _)
    (fun h => (Nat.find h : ℤ)) (fun _ => -1)

/-- Israel's form: `n = (q^2 - 1)/2 + k * (q^2 - q)` for an odd prime `q` and an integer `k`. -/
def IsForm (n : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ k : ℤ, (n : ℤ) = ((q : ℤ) ^ 2 - 1) / 2 + k * ((q : ℤ) ^ 2 - q)

/-- Israel's conjecture: the n of that form are the only cases where a(n) = -1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = -1 → IsForm n := by
  sorry

end OMA.S_oeis_a363796
