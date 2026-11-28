import Mathlib

/-!
# Period doubling for the rotating XOR process (OEIS A337742)

A state retains both the previous and current words. Positions on a ring of
width n are elements of ZMod n. Each update rotates their bitwise XOR one
place. The initial current word has a single bit at zero.
Source: Artem Yashin, https://oeis.org/A337742, doubling conjecture.
-/

namespace OMA.S_oeis_a337742

abbrev State (ι : Type) := (ι → Bool) × (ι → Bool)

def step {ι : Type} [Sub ι] [One ι] (s : State ι) : State ι :=
  (s.2, fun i => s.1 (i-1) ^^ s.2 (i-1))

def seed (n : ℕ) : State (ZMod n) :=
  (fun _ => false, fun i => decide (i = 0))

noncomputable def period (n : ℕ) : ℕ := Function.minimalPeriod step (seed n)

theorem main : ∀ n : ℕ, 0 < n → 0 < period n ∧ period (2*n) = 2 * period n := by
  sorry

end OMA.S_oeis_a337742
