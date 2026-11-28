import Mathlib

/-!
# A250162: 0..3 arrays whose adjacent differences have a zero signed sum

A250162(n) is the number of arrays `x 0, ..., x n` (length n+1) with entries in 0..3 for
which some choice of signs `ε i ∈ {+1, -1}` makes
`∑ i < n, ε i * (x (i + 1) - x i) = 0`. The signs are encoded by a Boolean `b i`
(`true` for +1, `false` for -1). A brute-force count of this reading gives
4, 20, 96, 436, 1880, 7836, 32032 for n = 1..7, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 12 2018):
  G.f.: 4*x*(1 - 3*x + 5*x^2) / ((1 - x)^2*(1 - 2*x)*(1 - 4*x)),
  a(n) = 2*(2 - 3*2^n + 4^n + 2*n).
The g.f. is stated after multiplying both sides by the denominator; the closed form is
stated for the terms of the sequence, n ≥ 1.

Source: https://oeis.org/A250162
Credit: @VashaTS
-/

namespace OMA.S_oeis_a250162

open PowerSeries

/-- The sign encoded by a Boolean: `true` is +1, `false` is -1. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Some arrangement of signs on the adjacent differences of `x` sums to zero. -/
def SignedSumZero {n : ℕ} (x : Fin (n + 1) → Fin 4) : Prop :=
  ∃ b : Fin n → Bool, ∑ i : Fin n, sign (b i) * (((x i.succ).val : ℤ) - (x i.castSucc).val) = 0

instance {n : ℕ} (x : Fin (n + 1) → Fin 4) : Decidable (SignedSumZero x) := by
  unfold SignedSumZero; infer_instance

/-- A250162(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 1) → Fin 4 => SignedSumZero x).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - 2 * X) * (1 - 4 * X)) =
      4 * X * (1 - 3 * X + 5 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 2 * (2 - 3 * 2 ^ n + 4 ^ n + 2 * n) := by
  sorry

end OMA.S_oeis_a250162
