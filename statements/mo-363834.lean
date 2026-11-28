import Mathlib

/-!
# A conjecture on circular permutations of `n` elements in an abelian group of odd order

Source: https://mathoverflow.net/questions/363834 (Zhi-Wei Sun, CC BY-SA 4.0).

Conjecture (Sun, 2013). Let `G` be an additive abelian group of odd order and `A ⊆ G` with
`|A| = n > 2`. Then there is a circular permutation `(a_1, …, a_n)` of all the elements of `A` such
that the adjacent sums `a_1 + a_2, …, a_{n-1} + a_n, a_n + a_1` are pairwise distinct.
(Verified for `|G| < 30` by Yu-Xuan Ji.)

Formalization notes:
* `G` is a finite additive commutative group with `Odd (Fintype.card G)`, in `Type`.
* A circular permutation of `A` is a bijection `f : Fin |A| ≃ A`; the next element after position
  `i` is at `finRotate _ i` (`i + 1`, and the last position wraps to `0`), so the adjacent sums are
  `f i + f (finRotate _ i)` and "pairwise distinct" is injectivity of that map.
* Checked numerically: holds for all subsets of size `> 2` of `ℤ/3`, `ℤ/5`, `ℤ/7`, and of
  `ℤ/3 × ℤ/3` up to size `7`.
-/

namespace OMA.S_mo_363834

/-- In a finite abelian group of odd order, every subset `A` with `|A| > 2` has a circular
arrangement whose adjacent sums are pairwise distinct. -/
theorem main : ∀ (G : Type) [AddCommGroup G] [Fintype G], Odd (Fintype.card G) →
    ∀ A : Finset G, 2 < A.card →
      ∃ f : Fin A.card ≃ A, Function.Injective (fun i => (f i : G) + (f (finRotate _ i) : G)) := by
  sorry

end OMA.S_mo_363834
