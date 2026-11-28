import Mathlib

/-!
# OEIS A025527: `n!/lcm(1, …, n)` at `n = p - 1`

Source: https://oeis.org/A025527
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = n!/lcm(1, 2, …, n)`. Conjecture (OEIS entry):
`a(A006093(n)) = φ(A000142(A006093(n))) / φ(A003418(A006093(n)))`, i.e. for `m = p - 1` with `p`
prime (A006093), `m!/lcm(1, …, m) = φ(m!)/φ(lcm(1, …, m))`.

Conventions:
* `lcm(1, …, m)` is `(Finset.Icc 1 m).lcm id`; the quotients are exact divisions in `ℕ`
  (`lcm(1, …, m) ∣ m!`, and `φ(d) ∣ φ(n)` when `d ∣ n`).
-/

namespace OMA.S_oeis_a025527

/-- `lcm(1, …, m)`. -/
def L (m : ℕ) : ℕ := (Finset.Icc 1 m).lcm id

/-- For every prime `p`, with `m = p - 1`: `m!/L(m) = φ(m!)/φ(L(m))`. -/
theorem main : ∀ p : ℕ, p.Prime →
    (p - 1).factorial / L (p - 1) = Nat.totient (p - 1).factorial / Nat.totient (L (p - 1)) := by
  sorry

end OMA.S_oeis_a025527
