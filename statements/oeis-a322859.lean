import Mathlib.Data.List.Permutation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Three conjectures on permutations with distinct differences

Source: M. Farrokhi D. G., OEIS A322859, https://oeis.org/A322859 (CC BY-SA 4.0).
Credit: @jatin6

Passing from 1-based to 0-based indices subtracts one from every label
`2*p(i)-i`, preserving distinctness. The ratio in the first conjecture is
positive and its being `n^(1+o(1))` means its logarithm divided by `log n`
tends to one. The last conjecture is about the displayed polynomial in its
given coefficient order.
-/

namespace OMA.S_oeis_a322859

def labels (p : List ℕ) : List ℤ :=
  p.zipIdx.map fun (v, i) => 2 * (v : ℤ) - (i : ℤ)

def a (n : ℕ) : ℕ :=
  ((List.range n).permutations'.filter fun p => (labels p).Nodup).length

noncomputable def sectionPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range n, Polynomial.C (a (i+1) : ℤ) * Polynomial.X ^ i

theorem main :
    (Filter.Tendsto (fun n : ℕ => Real.log ((n.factorial : ℝ) / a n) / Real.log n)
      Filter.atTop (nhds 1)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (n-2) * a (n-1) ≤ a n ∧ a n ≤ (n-1) * a (n-1)) ∧
    (∀ n : ℕ, 1 ≤ n → Irreducible (sectionPolynomial n)) := by
  sorry

end OMA.S_oeis_a322859
