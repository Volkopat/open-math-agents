import Mathlib

/-!
# A266587: smallest index of a Lucas number that is divisible by prime(n)

Source: https://oeis.org/A266587 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A266587 (Richard R. Forberg, Jan 01 2016), offset 1: smallest index of a Lucas number
(A000032) that is divisible by prime(n), if it exists, or 0 if it does not exist (for n > 1).
Data 0, 2, 0, 4, 5, 0, 0, 9, 12, 7, 15, 0, 10, 22, 8, 0, 29, 0, 34, 35, 0, 39, 42, 0, 0, 25, ...

Comments: Conjecture: Infinite Lucas subsequences divisible by the powers of odd primes, p(n),
for which a(n) > 0, are given by:
Lucas(a(n) + a(n)*(p(n)-1)*(Sum_{j=1..m-1} p(n)^(j-1)) + 2*i*a(n)*p(n)^(m-1)) is divisible by
p(n)^m, where p(n) > 2, i >= 0, m > 1.

Formalization notes.
* `lucas` is the sequence of Lucas numbers A000032: L(0) = 2, L(1) = 1, L(k+2) = L(k+1) + L(k).
* For an odd prime p, the entry point a = a(n) > 0 is the least index k with p | L(k)
  (`IsLeast`; the index 0 is not in the set, because L(0) = 2). The hypothesis says that the
  entry point exists and is equal to a.
* `main` is the conjecture: for each odd prime p with entry point a, each m > 1 and each i >= 0,
  p^m divides L(a + a (p - 1) Sum_{j=1..m-1} p^(j-1) + 2 i a p^(m-1)).
-/

namespace OMA.S_oeis_a266587

/-- The Lucas numbers A000032. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- If a is the Lucas entry point of the odd prime p, then p^m divides
L(a + a (p - 1) Sum_{j=1..m-1} p^(j-1) + 2 i a p^(m-1)) for m > 1 and i ≥ 0. -/
theorem main : ∀ p a : ℕ, p.Prime → 2 < p → IsLeast {k : ℕ | p ∣ lucas k} a →
    ∀ m i : ℕ, 1 < m →
      p ^ m ∣ lucas (a + a * (p - 1) * (∑ j ∈ Finset.Icc 1 (m - 1), p ^ (j - 1))
        + 2 * i * a * p ^ (m - 1)) := by
  sorry

end OMA.S_oeis_a266587
