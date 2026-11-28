import Mathlib

/-!
# A257474: Number of unordered ways to write n = a + b, where a and b are distinct elements of the set {floor(x/3): 3*x-1 and 3*x+1 are twin prime}, one of a and b is even, and one of a and b has the form p-1 or p-2 with p prime.

Source: https://oeis.org/A257474
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A257474 (Zhi-Wei Sun, Apr 25 2015): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 1, 2, 4, 39, 44, 65, 76, 82, 86, 108, 110, 123, 154, 175, 178, 196,
205, 221, 284, 308, 621, 735, 4655.

Conventions:
* The sequence has offset 1 (data 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, ...). `a n` is the number of
  pairs (u, v) with u < v, n = u + v, u and v elements of the set {floor(x/3): 3*x-1 and 3*x+1 are
  twin prime}, at least one of u and v even, and at least one of u and v of the form p-1 or p-2
  with p prime; the two summands of the OEIS name are called u and v here.
* `S u` says that u = floor(x/3) for some natural number x with 3*x - 1 and 3*x + 1 both prime (a
  twin prime pair); floor(x/3) is the natural-number division x / 3.
* Unordered ways with distinct summands are counted as pairs (u, v) with u < v.
* `one of a and b is even` and `one of a and b has the form p-1 or p-2` are read as `at least
  one`, which reproduces the OEIS data; `u has the form p-1 or p-2 with p prime` is `(u + 1).Prime
  ∨ (u + 2).Prime`.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a257474

/-- u is an element of the set {floor(x/3) : 3x-1 and 3x+1 are twin primes}. -/
def S (u : ℕ) : Prop := ∃ x : ℕ, x / 3 = u ∧ (3 * x - 1).Prime ∧ (3 * x + 1).Prime

/-- The condition in the name of A257474 on a tuple, for a given n. -/
def P (n : ℕ) (u v : ℕ) : Prop :=
  u < v ∧ u + v = n ∧ S u ∧ S v ∧ (Even u ∨ Even v) ∧
  ((u + 1).Prime ∨ (u + 2).Prime ∨ (v + 1).Prime ∨ (v + 2).Prime)

/-- A257474: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A257474. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 2, 4, 39, 44, 65, 76, 82, 86, 108, 110, 123, 154, 175, 178, 196, 205, 221, 284,
        308, 621, 735, 4655} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a257474
