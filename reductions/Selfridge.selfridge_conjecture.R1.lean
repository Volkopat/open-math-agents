import FormalConjectures.Wikipedia.Selfridge

-- Reduction Selfridge.selfridge_conjecture.R1 of the PSW (Selfridge) conjecture
-- Credit: @marcusbuffett

/-!
# The PSW conjecture: a kernel-checked initial range, and the open rest

The conjecture says that an odd `p ≡ ±2 (mod 5)` with `2 ^ (p - 1) ≡ 1 (mod p)` and
`F_(p + 1) ≡ 0 (mod p)` is prime.

* `H1`: this holds for `p ≤ 10000`. Checked inside the Lean kernel: every candidate is prime,
  or fails the Fermat test, or fails the Fibonacci test.
* `H2`: it holds for every `p > 10000`. This is the open conjecture (no counterexample is known,
  and it has been checked numerically very far; the range here is only what is cheap in the
  kernel).
-/

namespace OMA.R_Selfridge_selfridge_conjecture_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ p : ℕ, p ≤ 10000 → Selfridge.IsSelfridge p → p.Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ p : ℕ, 10000 < p → Selfridge.IsSelfridge p → p.Prime

theorem main : H1 → H2 → type_of% @Selfridge.selfridge_conjecture := by
  intro h1 h2 p hp
  by_cases h : p ≤ 10000
  · exact h1 p h hp
  · exact h2 p (by omega) hp

end OMA.R_Selfridge_selfridge_conjecture_R1
