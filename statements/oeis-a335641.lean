import Mathlib

/-!
# A335641: Number of ordered ways to write 2n+1 as p + x*(9x+7) with p prime and x an integer.

Source: https://oeis.org/A335641
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A335641 (Zhi-Wei Sun, Oct 03 2020), Conjecture 1: a(n)
> 0 for all n > 0. Also, a(n) = 1 only for n = 1, 4, 5, 7, 8, 18, 24, 25, 42, 68, 70, 85, 117,
118, 196, 238, 287, 497, 628, 677, 732.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, ...). `a n` is the number of
  pairs (p, x) with p a prime, x an integer and 2n+1 = p + x*(9x+7), exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a335641

/-- The condition in the name of A335641 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) (x : ℤ) : Prop :=
  p.Prime ∧ (p : ℤ) + x * (9 * x + 7) = 2 * (n : ℤ) + 1

/-- A335641: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℤ | P n t.1 t.2}

/-- The conjecture recorded in A335641. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 4, 5, 7, 8, 18, 24, 25, 42, 68, 70, 85, 117, 118, 196, 238, 287, 497, 628, 677,
        732} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a335641
