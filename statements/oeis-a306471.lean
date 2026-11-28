import Mathlib

/-!
# A306471: Number of ways to write n as C(2w+1,2) + C(x+2,3) + C(y+3,4) + C(z+4,5) with w,x,y,z nonnegative integers, where C(n,k) denotes the binomial coefficient n!/(k!*(n-k)!).

Source: https://oeis.org/A306471
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306471 (Zhi-Wei Sun, Feb 17 2019), Conjecture 1: a(n)
> 1 for all n > 0.

Conventions:
* The sequence has offset 0 (data 1, 3, 3, 2, 4, 6, 5, 4, 4, 5, 7, 8, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with n = C(2w+1,2) + C(x+2,3) + C(y+3,4) + C(z+4,5),
  exactly as in the OEIS name.
* C(n,k) is the binomial coefficient `Nat.choose n k`.
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a306471

/-- The condition in the name of A306471 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  Nat.choose (2 * w + 1) 2 + Nat.choose (x + 2) 3 + Nat.choose (y + 3) 4 + Nat.choose (z + 4) 5 = n

/-- A306471: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A306471. -/
theorem main : ∀ n : ℕ, 0 < n → 1 < a n := by
  sorry

end OMA.S_oeis_a306471
