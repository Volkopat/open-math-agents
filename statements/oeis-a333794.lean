import Mathlib

/-!
# OEIS A333794: a(n) = n + Max a(n - n/p) over the primes p dividing n

Source: https://oeis.org/A333794 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry (Antti Karttunen, 2020), offset 1: a(1) = 1, and for n > 1, a(n) = n + a(n - A052126(n)),
where A052126(n) is n divided by its greatest prime factor. The formula section states:
a(n) = n + Max a(n - n/p), for p prime and dividing n. [Conjectured, holds at least up to n=2^24].
The comment section says the same in words: conjecturally, a(n) is the largest path sum when
iterating from n to 1 with the nondeterministic map k -> k - k/p, p any prime factor of k.

Formalization notes:
* `a` is defined through `aux`, the entry's recursion with a fuel argument, so that it is a plain
  structural recursion. With fuel n the recursion from n always reaches 1, because each step maps
  k >= 2 to k - k/gpf(k), which lies between 1 and k - 1.
* The maximum over the primes dividing n is `Finset.sup` over `n.primeFactors`, which is nonempty
  for n >= 2.
* Controls: the definition gives 1, 3, 6, 7, 12, 13, 20, 15, 22, 25 for n = 1..10, as in the entry.
-/

namespace OMA.S_oeis_a333794

/-- The greatest prime factor of n (0 for n = 0 and n = 1). -/
def gpf (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n)).sup id

/-- The recursion of the entry, with fuel. -/
def aux : ℕ → ℕ → ℕ
  | 0, n => n
  | f + 1, n => if n ≤ 1 then n else n + aux f (n - n / gpf n)

/-- A333794(n). -/
def a (n : ℕ) : ℕ := aux n n

/-- The conjectured formula: for n > 1, a(n) = n + max over primes p dividing n of a(n - n/p). -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = n + n.primeFactors.sup (fun p => a (n - n / p)) := by
  sorry

end OMA.S_oeis_a333794
