import Mathlib

/-!
# A257743: steps of the map x -> (3*x+1)' from the odd part of n to 1 or a prime

Source: https://oeis.org/A257743
Credit: @avivorly

Definition (the entry, verbatim): Let n'= odd part of n. If n' is 1 or prime, then a(n)=1; otherwise a(n) is 1+ the
number of times the map x -> (3*x+1)' must be applied to n' in order to reach 1 or a prime.

Conjecture (Vladimir Shevelev, May 07 2015, in the entry, verbatim): Conjecture: for every N>0 there exists n=n(N)
such that a(n)>N.

Conventions:
- `oddPart n = n / 2 ^ (n.factorization 2)` is the odd part `n'` of `n` (and `oddPart 0 = 0`; the offset is 1, so
  only `n ≥ 1` occurs).
- `T x = oddPart (3 * x + 1)` is the map `x -> (3*x+1)'`.
- `a n = 1 + sInf {k | T^[k] (oddPart n) = 1 ∨ (T^[k] (oddPart n)).Prime}`. The value `k = 0` gives `a n = 1` when
  `n'` is 1 or prime, as in the definition; otherwise the least such `k` is the number of applications of `T`, as in
  the entry's PARI program (`a(n)` starts at 1 and adds 1 per application of `x -> 3*x+1` before the odd part is
  taken again). Examples from the entry: `a 9 = 2` (9 -> 7) and `a 33 = 3` (33 -> 25 -> 19).
- If the orbit of `n'` never reaches 1 or a prime, the set is empty, `sInf` of it is 0, and `a n = 1`. This only
  makes the conjecture harder to satisfy, so no case is assumed away.
- The conjecture is read with `N` a natural number and `n ≥ 1` (the offset of the entry).
-/

namespace OMA.S_oeis_a257743

/-- The odd part `n'` of `n`: `n` divided by the largest power of 2 dividing it. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ (n.factorization 2)

/-- The map `x -> (3*x+1)'`. -/
def T (x : ℕ) : ℕ := oddPart (3 * x + 1)

/-- `a n = 1 +` the least number of applications of `T` that takes `n'` to 1 or a prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  1 + sInf {k : ℕ | T^[k] (oddPart n) = 1 ∨ (T^[k] (oddPart n)).Prime}

theorem main : ∀ N : ℕ, 0 < N → ∃ n : ℕ, 1 ≤ n ∧ N < a n := by
  sorry

end OMA.S_oeis_a257743
