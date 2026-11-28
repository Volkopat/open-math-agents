import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a389475

/-- Coefficient sequence of the formal power series `A(x) = x + x^2 + 7 x^3 + ...`
satisfying `A(3*x^2) = 2*x^2 + A(x)^2 - 2*A(x)^3` (OEIS A389475). -/
def a389475 : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let lhs : ℚ := if (n + 3) % 2 = 0 then (3 : ℚ) ^ ((n + 3) / 2) * a389475 ((n + 3) / 2) else 0
    let s2 : ℚ := ∑ i ∈ (Finset.Icc 2 (n + 1)).attach,
      a389475 i.1 * a389475 (n + 3 - i.1)
    let s3 : ℚ := ∑ i ∈ (Finset.Icc 1 (n + 1)).attach,
      ∑ j ∈ (Finset.Icc 1 (n + 2 - i.1)).attach,
        a389475 i.1 * a389475 j.1 * a389475 (n + 3 - i.1 - j.1)
    (lhs - s2 + 2 * s3) / 2
termination_by n => n
decreasing_by
  · omega
  · have := (Finset.mem_Icc.mp i.2).2; omega
  · have := (Finset.mem_Icc.mp i.2).1; omega
  · have := (Finset.mem_Icc.mp i.2).2; omega
  · have hi := (Finset.mem_Icc.mp i.2).1
    have hj := (Finset.mem_Icc.mp j.2).2
    omega
  · have hi := (Finset.mem_Icc.mp i.2).1
    have hj := (Finset.mem_Icc.mp j.2).1
    omega

/-- Cauchy convolution of two sequences. -/
def conv (f g : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

/-- OEIS A389475 conjectures (4.a) and (4.b):
`A(x)` has integer coefficients satisfying `A(3*x^2) = 2*x^2 + A(x)^2 - 2*A(x)^3`,
`(4.a) A(x)^3 ≡ A(x^3) (mod 3)`, and
`(4.b) A(x)^2 ≡ x^2 + 2*A(x^3) (mod 3)`. -/
theorem main :
    (∀ m : ℕ,
      (if m % 2 = 0 then (3 : ℚ) ^ (m / 2) * a389475 (m / 2) else 0) =
        (if m = 2 then 2 else 0) + conv a389475 a389475 m - 2 * conv (conv a389475 a389475) a389475 m) ∧
    (∀ n : ℕ,
      (a389475 n).den = 1 ∧
      (conv (conv a389475 a389475) a389475 n).den = 1 ∧
      (conv a389475 a389475 n).den = 1 ∧
      (conv (conv a389475 a389475) a389475 n).num % 3 =
        (if 3 ∣ n then (a389475 (n / 3)).num else 0) % 3 ∧
      (conv a389475 a389475 n).num % 3 =
        ((if n = 2 then 1 else 0) + 2 * (if 3 ∣ n then (a389475 (n / 3)).num else 0)) % 3) := by
  sorry

end OMA.S_oeis_a389475
