import OMAStatements.S_mse_5153990
import Mathlib

/-!
# Reduction of MSE 5153990 (Mohanty–Mohanty Conjecture 4): Fibonacci Pythagorean numbers

Classical slice, not progress on the conjecture. The area of a right triangle with integer sides
is a multiple of `6` (in a Pythagorean triple one leg is divisible by `3`, and the product of
the legs by `4`). Since `gcd(F_n, F_m) = F_(gcd(n, m))`, `2 ∣ F_n` forces `3 ∣ n` and `3 ∣ F_n`
forces `4 ∣ n`. So a Fibonacci Pythagorean number `F_n` has `12 ∣ n`: this is `H1`.

`H2` is the open core: no `F_(12k)` is the area of an integer right triangle.
-/

namespace OMA.R_mse_5153990_R1

def H1 : Prop := ∀ n : ℕ, OMA.S_mse_5153990.IsPythagorean (Nat.fib n) → 12 ∣ n

def H2 : Prop := ∀ n : ℕ, 12 ∣ n → ¬ OMA.S_mse_5153990.IsPythagorean (Nat.fib n)

theorem main : H1 → H2 → type_of% @OMA.S_mse_5153990.main :=
  fun h1 h2 n hn => h2 n (h1 n hn) hn

end OMA.R_mse_5153990_R1
