import Mathlib

/-!
# A006165: a(1) = a(2) = 1; thereafter a(2n+1) = a(n+1) + a(n), a(2n) = 2a(n).

Source: https://oeis.org/A006165 (OEIS Foundation, CC BY-SA 4.0)
Credit: @Pampasgras

Conjectures of Peter Bala (Jul 31 2022), from the formula section of the entry. Write
`a^(k)` for the `k`-th iterate of `a` (`a^(1) = a`, `a^(k)(n) = a^(k-1)(a(n))`), which is
`a^[k]` in Lean. For `n ≥ 2`:

* (i) `a(n) + a(n - a(n - a(n - a(n - a(n))))) = n`;
* (ii) `a(n - a(n - a(n - a(n)))) = a(n - a(n - a(n - a(n - a(n - a(n))))))`;
* (iii) `a^(2)(n) = a(n - a(n - a(n - a(n))))`;
* (iv) `n - a(n) = a(n - a^(2)(n))`;
* (v) `a(n - a(n)) = a^(2)(n - a^(2)(n - a^(2)(n - a^(2)(n))))`;
* (vi) for `k ≥ 2`, `a^(k)(n - a^(k)(n)) = a^(k)(n - a^(k)(n - a^(k)(n - a^(k)(n))))`;
* (vii) for `k ≥ 1`, the sequence `b(n) = n - a^(k)(n)`, `n ≥ 1`, has first differences
  either `0` or `1`; its repeated values are of the form `(2^k - 1) * 2^m`; and the number
  of times they occur is `2, 3, 5, 9, 17, 35, ...`, independent of `k`, conjecturally
  A000051 (`2^m + 1`).

Formalization notes.
* `a 0` is not part of the sequence (offset 1); it is set to `0` and the statement only
  evaluates `a` at the positions the source uses. Since `a(m) ≤ m` for `m ≥ 1`, every
  subtraction in the source is a genuine natural-number subtraction.
* (iii) writes `a^2(n)`; the surrounding text and the data show it means the iterate
  `a^(2)(n) = a(a(n))` (for example at `n = 5` both sides equal `2`, while `a(5)^2 = 9`).
* A value of `b` is repeated when it is taken at two different indices `n ≥ 1`.
* The last claim is read, as its reference to A000051 says, as: the value `(2^k - 1) * 2^m`
  is taken by `b` exactly `2^m + 1` times. The listed term `35` disagrees with A000051,
  whose sixth term is `33`; direct computation (`k ≤ 4`, `m ≤ 7`) gives `33`, so `35` is
  read as a typo for `33` and the A000051 formula is stated.
-/

namespace OMA.S_oeis_a006165

/-- A006165, with offset 1: `a(1) = a(2) = 1`, `a(2n+1) = a(n+1) + a(n)` for `n ≥ 1`,
`a(2n) = 2 a(n)` for `n ≥ 2`. The value at `0` is unused. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 =>
    if (n + 3) % 2 = 0 then 2 * a ((n + 3) / 2)
    else a ((n + 3) / 2 + 1) + a ((n + 3) / 2)

/-- Bala's conjectures (i)-(vii) for A006165. -/
theorem main :
    (∀ n ≥ 2, a n + a (n - a (n - a (n - a (n - a n)))) = n) ∧
    (∀ n ≥ 2, a (n - a (n - a (n - a n))) = a (n - a (n - a (n - a (n - a (n - a n)))))) ∧
    (∀ n ≥ 2, a^[2] n = a (n - a (n - a (n - a n)))) ∧
    (∀ n ≥ 2, n - a n = a (n - a^[2] n)) ∧
    (∀ n ≥ 2, a (n - a n) = a^[2] (n - a^[2] (n - a^[2] (n - a^[2] n)))) ∧
    (∀ k ≥ 2, ∀ n ≥ 2,
      a^[k] (n - a^[k] n) = a^[k] (n - a^[k] (n - a^[k] (n - a^[k] n)))) ∧
    (∀ k ≥ 1,
      (∀ n ≥ 1, (n + 1) - a^[k] (n + 1) = n - a^[k] n ∨
        (n + 1) - a^[k] (n + 1) = n - a^[k] n + 1) ∧
      (∀ n₁ n₂ : ℕ, 1 ≤ n₁ → 1 ≤ n₂ → n₁ ≠ n₂ → n₁ - a^[k] n₁ = n₂ - a^[k] n₂ →
        ∃ m : ℕ, n₁ - a^[k] n₁ = (2 ^ k - 1) * 2 ^ m) ∧
      (∀ m : ℕ, {n : ℕ | 1 ≤ n ∧ n - a^[k] n = (2 ^ k - 1) * 2 ^ m}.ncard = 2 ^ m + 1)) := by
  sorry

end OMA.S_oeis_a006165
