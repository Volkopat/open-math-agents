import FormalConjectures.OEIS.«228552»

/-!
Reduction OeisA228552.conjecture.R2 of Square root of the absolute value of the
determinant of the prime sum indicator matrix.

`OeisA228552.a n` is `sqrt (|det M n|)`, where `det M n = OeisA69191.a n`. The two stages
are independent:

* H1 is the transfer from the raw determinant to the square-root wrapper: if the determinant
  `OeisA69191.a n` is nonzero, then `|det M n| > 0`, hence its integer square root is positive.
* H2 is the open core at the determinant level: for every `n > 15`, the prime-sum indicator
  matrix `M n` has nonzero determinant.

The main proof only passes the H2 determinant nonvanishing witness to H1.
-/

namespace OMA.R_OeisA228552_conjecture_R2

/-- Transfer lemma: a nonzero determinant `OeisA69191.a n` gives `OeisA228552.a n > 0`. -/
def H1 : Prop :=
  ∀ (n : ℕ), OeisA69191.a n ≠ 0 → OeisA228552.a n > 0

/-- Open core: for every `n > 15`, the prime-sum indicator matrix `M n` has nonzero
determinant, i.e. `OeisA69191.a n ≠ 0`. -/
def H2 : Prop :=
  ∀ (n : ℕ), 15 < n → OeisA69191.a n ≠ 0

theorem main : H1 → H2 → type_of% @OeisA228552.conjecture := by
  intro h1 h2 n hn
  exact h1 n (h2 n hn)

end OMA.R_OeisA228552_conjecture_R2
