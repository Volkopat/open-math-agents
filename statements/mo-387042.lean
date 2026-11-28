import Mathlib

/-!
# The solutions of `x^y y^z = z^x` with `x ≠ z`

Source: https://mathoverflow.net/questions/387042
Credit: @koolkao

Question (Zhi-Wei Sun, MathOverflow 387042, 2021; CC BY-SA 4.0). Consider the equation
`x^y y^z = z^x` with `x, y, z ∈ {2, 3, …}`. Conjecture 1 of the source: the only solutions with
`x ≠ z` are `(x, y, z) = (8, 2, 2), (9, 3, 3), (4, 2, 8), (16, 4, 32), (128, 64, 32),
(512, 256, 32), (686, 392, 98)`.

`main` states Conjecture 1. A disproof is a solution with `x ≠ z` outside this list.

Translation choices:
* `x, y, z` are natural numbers with `2 ≤ x, y, z`, and the equation is in `ℕ`;
* the list of solutions is a `Finset (ℕ × ℕ × ℕ)`;
* only Conjecture 1 is stated; Conjecture 2 of the source (on `w^x + x^y + y^z = z^w`) is not.
-/

namespace OMA.S_mo_387042

/-- Every solution of `x^y y^z = z^x` in integers `≥ 2` with `x ≠ z` is one of the seven listed
triples. -/
theorem main :
    ∀ x y z : ℕ, 2 ≤ x → 2 ≤ y → 2 ≤ z → x ^ y * y ^ z = z ^ x → x ≠ z →
      (x, y, z) ∈ ({(8, 2, 2), (9, 3, 3), (4, 2, 8), (16, 4, 32), (128, 64, 32), (512, 256, 32),
        (686, 392, 98)} : Finset (ℕ × ℕ × ℕ)) := by
  sorry

end OMA.S_mo_387042
