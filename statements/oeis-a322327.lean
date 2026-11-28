import Mathlib

/-!
# A322327: the sequences A005361(n) * k^omega(n) are multiplicative

Source: https://oeis.org/A322327 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Werner Schulte, Dec 03 2018), offset 1: a(n) = A005361(n) * A034444(n).
Comment: Conjecture: Let k be some fixed integer and a_k(n) = A005361(n) * k^A001221(n) for
n > 0 with 0^0 = 1. Then a_k(n) is multiplicative with a_k(p^e) = k*e for prime p and e > 0.

Formalization notes.
* A005361(n) is the product of the exponents in the prime factorization of n:
  the product of `n.factorization p` over the primes p that divide n (`n.primeFactors`).
* A001221(n) = omega(n) is the number of distinct primes that divide n,
  `ArithmeticFunction.cardDistinctFactors` in Mathlib.
* In Lean `k ^ 0 = 1` for every k, also for k = 0, as the entry requires.
* Multiplicative means a_k(1) = 1 and a_k(m n) = a_k(m) a_k(n) for coprime positive m, n.
-/

namespace OMA.S_oeis_a322327

/-- a_k(n) = A005361(n) * k^omega(n). -/
def a (k : ℤ) (n : ℕ) : ℤ :=
  (∏ p ∈ n.primeFactors, (n.factorization p : ℤ)) * k ^ (ArithmeticFunction.cardDistinctFactors n)

/-- Schulte's conjecture: a_k is multiplicative with a_k(p^e) = k*e for prime p and e > 0. -/
theorem main : ∀ k : ℤ,
    a k 1 = 1 ∧
    (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → a k (m * n) = a k m * a k n) ∧
    ∀ p e : ℕ, p.Prime → 0 < e → a k (p ^ e) = k * e := by
  sorry

end OMA.S_oeis_a322327
