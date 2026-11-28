import Mathlib

/-!
# The modulus of the complex Fibonacci function

Wolfdieter Lang's 2012 conjecture identifies the integer part of the modulus
at `(1+i)(n+2)` with Fibonacci(n+2) minus the parity of n. The exponential
form below uses the real logarithm of the positive golden ratio.

Source: https://oeis.org/A052952 (OEIS Foundation, CC BY-SA 4.0)
Credit: @connoranderson
-/

namespace OMA.S_oeis_a052952

noncomputable def complexFib (z : ℂ) : ℂ :=
  (Complex.exp ((Real.log Real.goldenRatio : ℂ)*z) -
    Complex.exp (Complex.I*Real.pi*z) *
      Complex.exp (-(Real.log Real.goldenRatio : ℂ)*z)) / (2*(Real.goldenRatio : ℂ)-1)

theorem main : ∀ n : ℕ,
    ⌊‖complexFib ((1+Complex.I)*(n+2))‖⌋ =
      ((n+2).fib : ℤ) - (n%2 : ℕ) := by
  sorry

end OMA.S_oeis_a052952
