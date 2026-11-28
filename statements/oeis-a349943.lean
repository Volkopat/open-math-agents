import Mathlib

/-!
# A349943: Number of ways to write n as a^4 + (b^4 + c^2 + d^2)/9, where a,b,c,d are nonnegative integers with c <= d.

Source: https://oeis.org/A349943
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A349943 (Zhi-Wei Sun, Dec 05 2021), Conjecture 1: a(n)
> 0 for all n >= 0, and a(n) = 1 only for n = 0, 16^k*m (k = 0,1,2,... and m = 7, 8, 31, 39, 47,
79, 519).

Conventions:
* The sequence has offset 0 (data 1, 3, 5, 4, 3, 4, 3, 1, 1, 6, 9, 6, ...). `a n` is the number of
  quadruples (a, b, c, d) of natural numbers with c <= d and n = a^4 + (b^4 + c^2 + d^2)/9,
  exactly as in the OEIS name.
* The quotient (b^4 + c^2 + d^2)/9 is required to be an integer: the divisibility by 9 is a
  separate conjunct, and the natural-number division is then exact.
* Only Conjecture 1 of the entry is formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a349943

/-- The condition in the name of A349943 on a tuple, for a given n. -/
def P (n : ℕ) (a b c d : ℕ) : Prop :=
  c ≤ d ∧ 9 ∣ b ^ 4 + c ^ 2 + d ^ 2 ∧ a ^ 4 + (b ^ 4 + c ^ 2 + d ^ 2) / 9 = n

/-- A349943: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A349943. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n = 0 ∨
      (∃ k m : ℕ, m ∈ ({7, 8, 31, 39, 47, 79, 519} : Finset ℕ) ∧ n = 16 ^ k * m)) := by
  sorry

end OMA.S_oeis_a349943
