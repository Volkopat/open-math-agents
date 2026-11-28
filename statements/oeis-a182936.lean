import Mathlib

/-!
# A182936: Greatest common divisor of the proper divisors of n, 0 if there are none.

Source: https://oeis.org/A182936 (conjecture of Vaclav Kotesovec, Jan 29 2025).
Credit: @esracummings31-blip

Here a proper divisor d of n is a divisor of n with 1 < d < n.

Conjecture: Sum_{k=1..n} a(k) = A072107(n) - A034387(n) - 1, where A072107(n) is the partial sum
of A014963 (A014963(k) = p if k is a power p^e, e >= 1, of a prime p, and 1 otherwise) and
A034387(n) is the sum of the primes <= n.
-/

namespace OMA.S_oeis_a182936

/-- A182936: the gcd of the divisors `d` of `n` with `1 < d < n` (the gcd of the empty set is `0`). -/
def a (n : ℕ) : ℕ := ((n.properDivisors).filter (fun d => 1 < d)).gcd id

/-- A014963: `p` if `k` is a power `p ^ e` (`e ≥ 1`) of a prime `p`, otherwise `1`. -/
def expMangoldt (k : ℕ) : ℕ := if IsPrimePow k then k.minFac else 1

theorem main : ∀ n, 1 ≤ n →
    ((∑ k ∈ Finset.Icc 1 n, a k : ℕ) : ℤ) =
      (∑ k ∈ Finset.Icc 1 n, expMangoldt k : ℕ) -
        (∑ p ∈ Finset.Icc 1 n with p.Prime, p : ℕ) - 1 := by
  sorry

end OMA.S_oeis_a182936
