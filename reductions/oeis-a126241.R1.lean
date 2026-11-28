import OMAStatements.S_oeis_a126241
import Mathlib

/-! Terras's inequality: after `d` steps of the Terras map with `u` odd steps among them,
`3^u * n ≤ 2^d * T^d(n)`, since `T^d(n) = (3^u n + c) / 2^d` with `c ≥ 0`. It gives the two
classical halves of the conjecture for every `n ≥ 2`: a dropping time `d` has coefficient
`3^u / 2^d < 1` (so the coefficient stopping time is at most the dropping time), and before a
coefficient stopping time `d` the orbit never goes below `n`. The open rest is the reverse
inequality in each direction: no earlier coefficient drop before the dropping time, and an
actual drop of the orbit at the coefficient stopping time. -/

namespace OMA.R_oeis_a126241_R1

open OMA.S_oeis_a126241

/-- The classical halves, from Terras's inequality `3^u n ≤ 2^d T^d(n)`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ d : ℕ,
    (IsDropTime n d → 3 ^ oddSteps n d < 2 ^ d) ∧
    (IsCoefTime n d → 1 ≤ d ∧ ∀ e, 1 ≤ e → e < d → n ≤ T^[e] n)

/-- The open rest of Terras's Conjecture 2.9. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ d : ℕ,
    (IsDropTime n d → ∀ e < d, 2 ^ e ≤ 3 ^ oddSteps n e) ∧
    (IsCoefTime n d → T^[d] n < n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a126241.main := by
  intro h1 h2 n hn d
  constructor
  · intro h
    exact ⟨(h1 n hn d).1 h, (h2 n hn d).1 h⟩
  · intro h
    obtain ⟨hd, he⟩ := (h1 n hn d).2 h
    exact ⟨hd, (h2 n hn d).2 h, he⟩

end OMA.R_oeis_a126241_R1
