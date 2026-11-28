import Mathlib

/-!
# A317850: the 10-adic integer x with x^7 + 1 = y and y^7 + 1 = x

Source: https://oeis.org/A317850
Credit: @avivorly

A317850 (offset 0) lists the decimal digits, least significant first, of the 10-adic integer
`x = ...603097394847873` satisfying `x^7 + 1 = y` and `y^7 + 1 = x` (the companion `y = ...480203107738498` is
A317864); for example `603097394847873^7 + 1 == 480203107738498 (mod 10^15)` and
`480203107738498^7 + 1 == 603097394847873 (mod 10^15)`.

Conjecture (Patrick A. Thomas, in the entry): There exists a pair of 10-adic integers satisfying `x^n + 1 = y` and
`y^n + 1 = x` iff `n == 3, 7, or 15 (mod 20)`.

Conventions:
- A 10-adic integer is an element of the inverse limit of the rings `ZMod (10 ^ k)`, given as a family
  `x : (k : ℕ) → ZMod (10 ^ k)` that is compatible (`IsTenAdic x`): reducing `x (k + 1)` modulo `10 ^ k` gives `x k`.
  The ring operations of the 10-adic integers are componentwise, so `x ^ n + 1 = y` holds iff `x k ^ n + 1 = y k`
  for every `k`, and likewise for `y ^ n + 1 = x`.
- The exponent `n` ranges over the positive integers (`1 ≤ n`): at `n = 0` the equations read `2 = y` and `2 = x`,
  a trivial solution, and the entry is about positive exponents.
- A pair is not required to have `x ≠ y`: for `n ≥ 1` every solution has `y ≡ x + 1 (mod 2)` (as `z ^ n ≡ z (mod 2)`),
  so `x ≠ y` holds automatically, and reading a pair as two distinct 10-adic integers gives the same statement.
- `n == 3, 7, or 15 (mod 20)` is read as `n % 20 = 3 ∨ n % 20 = 7 ∨ n % 20 = 15`.
-/

namespace OMA.S_oeis_a317850

/-- `x` is a 10-adic integer: a family of residues `x k` modulo `10 ^ k` that is compatible, i.e. `x (k + 1)`
reduces to `x k` modulo `10 ^ k` for every `k`. -/
def IsTenAdic (x : (k : ℕ) → ZMod (10 ^ k)) : Prop :=
  ∀ k : ℕ, ZMod.castHom (pow_dvd_pow 10 (Nat.le_succ k)) (ZMod (10 ^ k)) (x (k + 1)) = x k

/-- Thomas's conjecture in A317850: for `n ≥ 1`, there is a pair of 10-adic integers `x, y` with `x ^ n + 1 = y` and
`y ^ n + 1 = x` iff `n ≡ 3, 7` or `15 (mod 20)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((∃ x y : (k : ℕ) → ZMod (10 ^ k), IsTenAdic x ∧ IsTenAdic y ∧
          ∀ k : ℕ, x k ^ n + 1 = y k ∧ y k ^ n + 1 = x k) ↔
        (n % 20 = 3 ∨ n % 20 = 7 ∨ n % 20 = 15)) := by
  sorry

end OMA.S_oeis_a317850
