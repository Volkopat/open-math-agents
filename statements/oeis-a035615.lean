import Mathlib

/-!
# A035615: Number of winning length n strings with a 2-symbol alphabet in "same game"

Source: https://oeis.org/A035615
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Ralf Stephan, May 11 2004; established by Burns and Purcell):
G.f.: x * (2*x^6 - 6*x^5 + 8*x^4 + 2*x^3 - 6*x^2 + 2*x) /
      ((1 - x^2) * (1 - 2*x) * (1 - x - x^2)^2).

Conventions:
A string over a 2-symbol alphabet (List Bool) is winning in 1D "same game" if it can be reduced
to the empty list by repeatedly removing a contiguous block of at least 2 identical symbols.
We express the conjectured rational generating function as an identity in PowerSeries ℤ by
clearing the denominator.
-/

namespace OMA.S_oeis_a035615

open PowerSeries

/-- A binary string is winning in 1D SameGame if it reduces to [] by removing runs of length >= 2. -/
inductive Winning : List Bool → Prop
  | nil : Winning []
  | step (u v : List Bool) (b : Bool) (k : ℕ) (hk : 2 ≤ k) :
      Winning (u ++ v) → Winning (u ++ List.replicate k b ++ v)

/-- Number of winning length-n binary strings in 1D SameGame. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {w : Vector Bool n // Winning w.toList}

/-- Conjectured rational generating function for A035615, expressed with cleared denominator. -/
theorem main :
    ((1 - X ^ 2) * (1 - 2 * X) * (1 - X - X ^ 2) ^ 2 : PowerSeries ℤ) *
        PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      X * (2 * X ^ 6 - 6 * X ^ 5 + 8 * X ^ 4 + 2 * X ^ 3 - 6 * X ^ 2 + 2 * X) := by
  sorry

end OMA.S_oeis_a035615
