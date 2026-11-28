import Mathlib

/-!
# OEIS A046747: probability that a random 0-1 matrix is singular

Source: https://oeis.org/A046747
`a n` is the number of singular `n × n` `{0,1}`-matrices (over the reals). Conjecture: the
probability `a n / 2^(n²)` that a random such matrix is singular is asymptotic to
`binom(n+1, 2) (1/2)^(n-1)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a046747

open Filter Asymptotics

/-- Number of singular `n × n` matrices with entries in `{0, 1}`. -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter fun M : Matrix (Fin n) (Fin n) Bool =>
    (M.map fun b => if b then (1 : ℝ) else 0).det = 0).card

theorem main :
    (fun n : ℕ => (a n : ℝ) / 2 ^ (n ^ 2)) ~[atTop]
      fun n : ℕ => ((n + 1).choose 2 : ℝ) * (1 / 2) ^ (n - 1) := by
  sorry

end OMA.S_oeis_a046747
