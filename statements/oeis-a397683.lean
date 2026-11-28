import Mathlib

/-!
# A397683: units x, x + 1 modulo m with equal multiplicative orders

Source: https://oeis.org/A397683

A397683 is a(n) = f(2n - 1), where f(1) = 1 and otherwise f(m) is the number of x with
1 <= x < m such that gcd(x, m) = gcd(x + 1, m) = 1 and ord_m(x) = ord_m(x + 1).
Its comments state the conjecture: for odd m, f(m) = 0 iff m is a power of 3 or a power of 7.

Conventions:
* ord_m(x) is the multiplicative order of x modulo m: `orderOf (x : ZMod m)`. Both x and x + 1
  are units modulo m here, so these orders are the usual (positive) multiplicative orders.
* f(1) = 1, so 1 = 3^0 does not count as a power of 3: the powers of 3 and 7 are `3 ^ k`, `7 ^ k`
  with `k ≥ 1` (the only zeros of f are at m ≥ 2).
-/

namespace OMA.S_oeis_a397683

/-- `f` of A397683. -/
noncomputable def f (m : ℕ) : ℕ :=
  if m = 1 then 1 else
    ((Finset.Ico 1 m).filter (fun x => Nat.Coprime x m ∧ Nat.Coprime (x + 1) m ∧
      orderOf (x : ZMod m) = orderOf ((x + 1 : ℕ) : ZMod m))).card

/-- For odd `m`, `f m = 0` iff `m` is a power of 3 or a power of 7 (with exponent at least 1). -/
theorem main : ∀ m : ℕ, Odd m → (f m = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ (m = 3 ^ k ∨ m = 7 ^ k)) := by
  sorry

end OMA.S_oeis_a397683
