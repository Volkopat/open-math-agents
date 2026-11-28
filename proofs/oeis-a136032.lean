import OMAStatements.S_oeis_a136032
import Mathlib

/-!
# A136032: for squarefree Mersenne composites, `Ω = ω`

The `n`-th Mersenne composite, as defined through `Nat.nth`, is either an actual Mersenne
composite or the default value `0` (if there are fewer than `n` of them).  A Mersenne composite
is squarefree by hypothesis, and a squarefree number has as many prime factors with multiplicity
as distinct prime factors; for `0` both counts are `0`.
-/

open OMA.S_oeis_a136032 in
theorem OMA.solution : type_of% @OMA.S_oeis_a136032.main := by
  intro hsq n _
  unfold a A135975
  have hcases : A065341 n = 0 ∨ IsMersenneComposite (A065341 n) := by
    unfold A065341
    by_cases hf : (Set.ofPred IsMersenneComposite).Finite
    · rcases lt_or_ge (n - 1) hf.toFinset.card with h | h
      · exact Or.inr (Nat.nth_mem_of_lt_card hf h)
      · exact Or.inl (Nat.nth_of_card_le hf h)
    · exact Or.inr (Nat.nth_mem_of_infinite hf (n - 1))
  rcases hcases with h0 | hm
  · rw [h0]
    simp
  · have hs := hsq _ hm
    exact ((ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hs.ne_zero).mpr
      hs).symm
