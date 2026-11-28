import Mathlib.Data.Nat.Choose.Basic

/-!
# OEIS A389536
The ordinary generating function A begins with x and satisfies
x A(x) = A(x² + 2x³). Writing B = A/x and f = x²(1+2x) gives
B(x) = (1+2x) B(f(x)), and b(0) = 1. The contribution of b(k) to b(n)
is b(k) times the coefficient of x^(n-2k) in (1+2x)^(k+1).
The functions below construct the unique coefficients with these rules.

Source: Paul D. Hanna, OEIS A389536, https://oeis.org/A389536 .
-/
namespace OMA.S_oeis_a389536

/-- A single binomial-expansion contribution to the coefficient of x^n in B. -/
def term (b : Nat → Nat) (n k : Nat) : Nat :=
  b k * Nat.choose (k+1) (n-2*k) * 2^(n-2*k)

/-- Coefficients of B = A/x, starting at index zero. -/
def b : Nat → Nat
  | 0 => 1
  | n+1 => ((List.range ((n+1)/2+1)).map
      (term (fun k => if _h : k < n+1 then b k else 0) (n+1))).sum
termination_by n => n
decreasing_by omega

/-- OEIS A389536, whose first published index is one and whose a(1) is one. -/
def a : Nat → Nat
  | 0 => 0
  | n+1 => b n

/-- For n > 1, a(n) has residue two modulo four exactly at powers of two plus
one, and residue zero at every other index. -/
theorem main : ∀ n : Nat, 1 < n →
    ((∃ k : Nat, n = 2^k + 1) ∧ a n % 4 = 2) ∨
    ((¬∃ k : Nat, n = 2^k + 1) ∧ a n % 4 = 0) := by
  sorry

end OMA.S_oeis_a389536
