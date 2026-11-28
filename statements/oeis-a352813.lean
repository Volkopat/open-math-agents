import Mathlib

/-!
# A352813: Minimum difference |product(A) - product(B)| where A and B are a partition of {1,2,3,...,2*n} and |A| = |B| = n.

Source: https://oeis.org/A352813
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A352813 (Peter J. Taylor, Apr 04 2022): a(n) =
A038667(2*n) for all n. It is verified for n<=70.

Conventions:
* The sequence has offset 0 (data 0, 1, 2, 6, 18, 30, 576, 840, 24480, 93696, 800640, 7983360,
  ...).
* `diff N S` is |product(A) - product(B)| for the partition of {1, ..., N} into A = S and B = the
  complement of S in `Finset.Icc 1 N` (an empty product is 1); it is computed in `ℤ` and returned
  as a natural number.
* a(n) is the minimum of diff(2n, S) over the subsets S of {1, ..., 2n} with exactly n elements,
  and A038667(N) (minimal value of |product(A) - product(B)| where A and B are a partition of {1,
  2, 3, ..., N}) is the minimum over all subsets; both minima are written as `sInf` of nonempty
  sets of natural numbers.
-/

namespace OMA.S_oeis_a352813

/-- |product(S) - product(complement of S in {1..N})|. -/
def diff (N : ℕ) (S : Finset ℕ) : ℕ :=
  Int.natAbs ((∏ x ∈ S, (x : ℤ)) - ∏ x ∈ Finset.Icc 1 N \ S, (x : ℤ))

/-- The conjecture recorded in A352813. -/
theorem main : ∀ n : ℕ,
    sInf {d : ℕ | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 (2 * n) ∧ S.card = n ∧ d = diff (2 * n) S} =
      sInf {d : ℕ | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 (2 * n) ∧ d = diff (2 * n) S} := by
  sorry

end OMA.S_oeis_a352813
