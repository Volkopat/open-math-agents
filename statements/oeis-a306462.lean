import Mathlib

/-!
# A306462: Number of ways to write n as C(2w,2) + C(x+2,3) + C(y+3,4) + C(z+4,5), where C(n,k) denotes the binomial coefficient n!/(k!*(n-k)!), w is a positive integer and x,y,z are nonnegative integers.

Source: https://oeis.org/A306462
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306462 (Zhi-Wei Sun, Feb 17 2019): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 1, 4, 5, 14, 19.

Conventions:
* The sequence has offset 1 (data 1, 3, 3, 1, 1, 4, 7, 6, 2, 2, 6, 8, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with w > 0 and n = C(2w,2) + C(x+2,3) + C(y+3,4) +
  C(z+4,5), exactly as in the OEIS name.
* C(n,k) is the binomial coefficient `Nat.choose n k`.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a306462

/-- The condition in the name of A306462 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < w ∧
  Nat.choose (2 * w) 2 + Nat.choose (x + 2) 3 + Nat.choose (y + 3) 4 + Nat.choose (z + 4) 5 = n

/-- A306462: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A306462. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 4, 5, 14, 19} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a306462
