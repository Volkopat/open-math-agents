import Mathlib

/-!
# The two central-array identities conjectured in OEIS A006134

Source: https://oeis.org/A006134 (Wiseman, April 20, 2023)
Array sources: https://oeis.org/A013580 and https://oeis.org/A231147
Credit: @Heart-galaxy

A006134 has offset 0 and is the partial sum of central binomial coefficients.
Both explicitly marked conjectures are retained below for every n>=0.

Coordinate conventions follow Wiseman's surrounding examples. P(m) is the
zero-based modified-Pascal row of A013580: start with1, apply the Pascal rule,
and add1 to the center when the new zero-based row index is even. The source
bivariate g.f. is1/((1-(1+Y)X)*(1-Y*X^2)); its coefficient row has expansion
Sum_{j<=m/2}Y^j(1+Y)^(m-2j), proved equal to P in the companion proof.
Wiseman's T(N,k) labels rows by the set size N and columns by integer median
k, so it is coefficient k-1 of P(N-1). The flat sequence's offset0 does not
replace these one-based row/column labels.

For A231147, the source substitutes X+1/X into p(N,z)=Sum_{j=0..N-1}z^j
and takes its numerator. R(N)=Sum_{j=0..N-1}X^(N-1-j)(1+X^2)^j clears the
powers of X; its constant coefficient is1 when N>=1, so no X factor cancels.
The full row has median labels1,3/2,...,N. An integer label k is therefore
coefficient2*(k-1), or ordinary column rank2*k-1, not rank k. This is the
coordinate convention of the conjectured T(2n+1,n+1).

The subset-counting interpretations of either array are not assumed.
Unmarked ancillary statements, including the source's shifted first-difference
line, are not additional targets and are not used. Prior literature resolution
and mathematical novelty of the two marked conjectures are not claimed.
-/

namespace OMA.S_oeis_a006134

open Polynomial

def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n+1), Nat.choose (2*k) k

/-- The zero-based polynomial rows of the modified Pascal triangle. -/
noncomputable def P : ℕ → Polynomial ℕ
  | 0 => 1
  | n+1 => (1+X)*P n + if (n+1)%2 = 0 then X^((n+1)/2) else 0

/-- Source A013580 in Wiseman's one-based row and integer-median coordinates. -/
noncomputable def T013580 (r c : ℕ) : ℕ := (P (r-1)).coeff (c-1)

/-- Numerator after clearing the powers of X in the source geometric polynomial. -/
noncomputable def R (r : ℕ) : Polynomial ℕ :=
  ∑ j ∈ Finset.range r, X^(r-1-j)*(1+X^2)^j

/-- Integer-median entries of A231147; half-step columns have adjacent polynomial degrees. -/
noncomputable def T231147 (r c : ℕ) : ℕ := (R r).coeff (2*(c-1))


theorem main :
    (∀ n : ℕ, a n = T013580 (2*n+1) (n+1)) ∧
    (∀ n : ℕ, a n = T231147 (2*n+1) (n+1)) := by
  sorry

end OMA.S_oeis_a006134
