import Mathlib

/-!
# A124758: Product of the parts of the compositions in standard order.

Source: https://oeis.org/A124758
Credit: @avivorly

A124758 (offset 0): `a(k)` is the product of the parts of the `k`-th composition in standard order
(row `k` of A066099): 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 4, 2, 3, 2, 2, 1, 5, ...
As the entry says, the `k`-th composition in standard order is obtained by taking the set of positions
of 1's in the reversed binary expansion of `k`, prepending 0, taking first differences, and reversing
again; e.g. composition number 11 is (2, 1, 1), so `a(11) = 2`, and `a(146) = 18` from (3, 3, 2).

Conjectures (Mikhail Kurkov, Jul 11 2021):
- `a(2n+1) = a(n)` for `n >= 0`;
- `a(2n) = (1 + 1/A001511(n))*a(n) = 2*a(n) + a(n - 2^f(n)) - a(2n - 2^f(n))` for `n > 0` with
  `a(0) = 1`, where `f(n) = A007814(n)`;
- from the first formula for `a(2n)`: `a(4n+2) = 2*a(n)`, `a(4n) = 2*a(2n) - a(n)`;
- `Sum_{k=0..2^n - 1} a(k) = A001519(n+1)` for `n >= 0`;
- `a((4^n - 1)/3) = A011782(n)` for `n >= 0`;
- `a(2^m*(2^n - 1)) = m + 1` for `n > 0`, `m >= 0`.

All of them are stated, as a conjunction.

Conventions:
- Positions in the reversed binary expansion (`Nat.digits 2`, least significant digit first) are
  counted from 1; `a(0) = 1` is the empty product.
- `A007814(n) = padicValNat 2 n` (the 2-adic valuation) and `A001511(n) = padicValNat 2 (2n)`, the
  2-adic valuation of `2n` (the ruler function, `= A007814(n) + 1`); for `n > 0` the subtractions
  `n - 2^f(n)` and `2n - 2^f(n)` are exact.
- The identities with subtractions are stated in `ℤ`, and the one with `1/A001511(n)` in `ℚ`.
- The pair `a(4n+2) = 2a(n)`, `a(4n) = 2a(2n) - a(n)` is stated for every `n ≥ 0` (no range is given;
  at `n = 0` both read `2 = 2`, `1 = 1`).
- A001519: `b(0) = b(1) = 1`, `b(n) = 3 b(n-1) - b(n-2)`; A011782: 1, then `2^(n-1)` for `n ≥ 1`.
-/

namespace OMA.S_oeis_a124758

/-- The positions (counted from 1) of the 1's in the reversed binary expansion of `k`. -/
def onePos (k : ℕ) : List ℕ :=
  ((List.range (Nat.digits 2 k).length).filter (fun i => (Nat.digits 2 k).getD i 0 = 1)).map (· + 1)

/-- The `k`-th composition in standard order (row `k` of A066099): prepend 0 to `onePos k`, take first
differences, reverse. -/
def comp (k : ℕ) : List ℕ :=
  (List.zipWith (fun x y => y - x) (0 :: onePos k) (onePos k)).reverse

/-- A124758: the product of the parts of the `k`-th composition in standard order. -/
def a (k : ℕ) : ℕ := (comp k).prod

/-- A001519: `b 0 = b 1 = 1`, `b (n + 2) = 3 * b (n + 1) - b n`. -/
def A001519 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 3 * A001519 (n + 1) - A001519 n

/-- A011782: 1, 1, 2, 4, 8, ... -/
def A011782 (n : ℕ) : ℕ := if n = 0 then 1 else 2 ^ (n - 1)

theorem main :
    (∀ n : ℕ, a (2 * n + 1) = a n) ∧
    (∀ n : ℕ, 0 < n →
      (a (2 * n) : ℚ) = (1 + 1 / (padicValNat 2 (2 * n) : ℚ)) * a n ∧
      (a (2 * n) : ℤ) = 2 * a n + a (n - 2 ^ padicValNat 2 n) - a (2 * n - 2 ^ padicValNat 2 n)) ∧
    (∀ n : ℕ, a (4 * n + 2) = 2 * a n ∧ (a (4 * n) : ℤ) = 2 * a (2 * n) - a n) ∧
    (∀ n : ℕ, ((∑ k ∈ Finset.range (2 ^ n), a k : ℕ) : ℤ) = A001519 (n + 1)) ∧
    (∀ n : ℕ, a ((4 ^ n - 1) / 3) = A011782 n) ∧
    (∀ n m : ℕ, 0 < n → a (2 ^ m * (2 ^ n - 1)) = m + 1) := by
  sorry

end OMA.S_oeis_a124758
