import Mathlib

/-!
# A003171: Negated discriminants of imaginary quadratic orders with 1 class per genus

Source: https://oeis.org/A003171
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
`7392` is the largest negated discriminant `D > 0` (`D ≡ 0` or `3 (mod 4)`) of an order
in an imaginary quadratic field having 1 class per genus.

Conventions:
- By Gauss's genus theory, the form class group `Cl(-D)` of primitive positive definite
  binary quadratic forms `a*x^2 + b*x*y + c*y^2` of discriminant `b^2 - 4*a*c = -D`
  has 1 class per genus if and only if every class has order dividing `2`, which is
  equivalent to every reduced primitive positive definite form `(a, b, c)` of
  discriminant `-D` being ambiguous (`b = 0 ∨ b = a ∨ a = c`).
-/

namespace OMA.S_oeis_a003171

/-- Predicate asserting that `-D` is the discriminant of an imaginary quadratic order
with 1 class per genus (equivalently, every reduced primitive positive definite binary
quadratic form of discriminant `-D` is ambiguous). -/
def hasOneClassPerGenus (D : ℕ) : Prop :=
  0 < D ∧ (D % 4 = 0 ∨ D % 4 = 3) ∧
    ∀ a b c : ℤ,
      0 < a →
      b ^ 2 - 4 * a * c = -(D : ℤ) →
      Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs) = 1 →
      |b| ≤ a →
      a ≤ c →
      (|b| = a → 0 ≤ b) →
      (a = c → 0 ≤ b) →
      b = 0 ∨ b = a ∨ a = c

/-- Every negated discriminant `D > 0` of an imaginary quadratic order with 1 class per
genus satisfies `D ≤ 7392`. -/
theorem main :
    ∀ D : ℕ, hasOneClassPerGenus D → D ≤ 7392 := by
  sorry

end OMA.S_oeis_a003171
