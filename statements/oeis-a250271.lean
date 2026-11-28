import Mathlib

/-!
# A250271: 0..2 arrays whose squared adjacent differences have a zero signed sum

A250271(n) is the number of arrays `x 0, ..., x n` (length n+1) with entries in 0..2 for
which some choice of signs `ε i ∈ {+1, -1}` makes
`∑ i < n, ε i * (x (i + 1) - x i) ^ 2 = 0`. The signs are encoded by a Boolean `b i`
(`true` for +1, `false` for -1). A brute-force count of this reading gives
3, 11, 27, 79, 255, 843, 2763, 8903 for n = 1..8, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 12 2018):
  G.f.: x*(3 - 16*x + 21*x^2 + 24*x^3 - 60*x^4 + 24*x^5) / ((1 - x)^2*(1 - 2*x)^2*(1 - 3*x)),
  a(n) = 5*3^(n-1) - (2^n-2)*n for n > 1.
The g.f. is stated after multiplying both sides by the denominator.

Source: https://oeis.org/A250271
Credit: @VashaTS
-/

namespace OMA.S_oeis_a250271

open PowerSeries

/-- The sign encoded by a Boolean: `true` is +1, `false` is -1. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Some arrangement of signs on the squared adjacent differences of `x` sums to zero. -/
def SignedSumZero {n : ℕ} (x : Fin (n + 1) → Fin 3) : Prop :=
  ∃ b : Fin n → Bool,
    ∑ i : Fin n, sign (b i) * (((x i.succ).val : ℤ) - (x i.castSucc).val) ^ 2 = 0

instance {n : ℕ} (x : Fin (n + 1) → Fin 3) : Decidable (SignedSumZero x) := by
  unfold SignedSumZero; infer_instance

/-- A250271(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 1) → Fin 3 => SignedSumZero x).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) =
      X * (3 - 16 * X + 21 * X ^ 2 + 24 * X ^ 3 - 60 * X ^ 4 + 24 * X ^ 5) ∧
    ∀ n : ℕ, 1 < n → (a n : ℤ) = 5 * 3 ^ (n - 1) - (2 ^ n - 2) * n := by
  sorry

end OMA.S_oeis_a250271
