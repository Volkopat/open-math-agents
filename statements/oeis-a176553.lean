import Mathlib

/-!
# A176553: Numbers m whose concatenation of divisors is noncomposite

Source: https://oeis.org/A176553

Conjecture (OEIS A176553):
Every positive integer `m` whose base-10 concatenation of positive divisors in
increasing order (OEIS A037278) is noncomposite (`1` or prime) is a Loeschian number
(OEIS A003136), i.e., of the form `x^2 + x * y + y^2` for some `x, y : ℕ`.

Conventions:
- Offset: `1`; first terms: `1, 3, 7, 9, 13, 21, 31, 37, 67, 73, 79, 97, 103, 109, ...`.
- For `m = 3`, the divisors are `1, 3`, whose concatenation is `13` (prime), and
  `3 = 1^2 + 1*1 + 1^2`.
- For `m = 9`, the divisors are `1, 3, 9`, whose concatenation is `139` (prime), and
  `9 = 3^2 + 3*0 + 0^2`.
-/

namespace OMA.S_oeis_a176553

/-- Base-10 concatenation of the positive divisors of `m` in increasing order
(OEIS A037278). -/
def divConcat (m : ℕ) : ℕ :=
  let divs := (List.range (m + 1)).filter (fun d => decide (1 ≤ d ∧ d ∣ m))
  let msbDigits := divs.flatMap (fun d => (Nat.digits 10 d).reverse)
  Nat.ofDigits 10 msbDigits.reverse

/-- Predicate stating that `m` is a Loeschian number `x^2 + x * y + y^2`
(OEIS A003136). -/
def IsLoeschian (m : ℕ) : Prop :=
  ∃ x y : ℕ, m = x ^ 2 + x * y + y ^ 2

/-- Conjecture: every term of A176553 is a Loeschian number. -/
theorem main :
    ∀ m : ℕ, 1 ≤ m → (divConcat m = 1 ∨ Nat.Prime (divConcat m)) → IsLoeschian m := by
  sorry

end OMA.S_oeis_a176553
