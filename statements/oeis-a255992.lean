import Mathlib

/-!
# A255992: Binary words with separated downsteps

Source: https://oeis.org/A255992

A downstep is the adjacent pair 10. The entry's T(n,k) counts words of
length n+k with at most one downstep in every k consecutive adjacent
pairs, for positive n and k. Equivalently for these lengths, consecutive
downsteps have starting indices at least k apart.

We count all lengths m with the index-spacing convention. To recognize
these words, scan from left to right and forbid a downstep while the
remaining cooldown is positive. A downstep sets the cooldown to k-1;
any other transition decreases it by one. The initial virtual bit 0
does not introduce a downstep.

The generating function below, with the denominator cleared, is
Theorem 45 of Sela Fried, https://arxiv.org/abs/2607.24832.
The double sum of Lemma 46 is stated with its outer index shifted
from r to s=r-1. It gives the closed form recorded in the entry.
-/

namespace OMA.S_oeis_a255992

open PowerSeries

/-- Scan the remaining binary word with the given previous bit and cooldown. -/
def scan (k : ℕ) (previous : Bool) (cooldown : ℕ) : List Bool → Bool
  | [] => true
  | bit :: rest =>
      if previous && !bit then
        (cooldown == 0) && scan k bit (k - 1) rest
      else
        scan k bit (cooldown - 1) rest

/-- Number of admissible words following the supplied state. -/
noncomputable def countFrom (k : ℕ) (previous : Bool) (cooldown m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m → Bool)).filter fun w =>
    scan k previous cooldown (List.ofFn w) = true).card

/-- The count of words from the initial state. -/
noncomputable def count (k m : ℕ) : ℕ :=
  countFrom k false 0 m

/-- Fried's generating function for the counts underlying the columns of A255992. -/
def GeneratingFunction : Prop := ∀ k : ℕ, 1 ≤ k →
    PowerSeries.mk (fun m => (count k m : ℤ)) *
        ((1 - X)^2 * (1 - 2*X + X^2 - ((k : ℤ) - 1) • (X^k) +
          ((k : ℤ) - 2) • (X^(k+1))) : PowerSeries ℤ) =
      1 - 2*X + 2*X^2 - ((k : ℤ) - 1) • (X^k) +
        ((k : ℤ) - 2) • (X^(k+1))

/-- The OEIS double-binomial coefficient formula for T(n,k), indexed by s=r-1. -/
def BinomialFormula : Prop := ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (count k (n+k) : ℤ) = (n : ℤ) + k + 1 +
      ∑ s ∈ Finset.range ((n+k-2)/k+1),
        ∑ j ∈ Finset.range (s+1),
          (-1 : ℤ)^j * (s.choose j : ℤ) * ((k : ℤ)-1)^(s-j) * ((k : ℤ)-2)^j *
            (((n+k-2-s*k + 2*s+3-j).choose (2*s+3) : ℕ) : ℤ)

theorem main : GeneratingFunction ∧ BinomialFormula := by
  sorry

end OMA.S_oeis_a255992
