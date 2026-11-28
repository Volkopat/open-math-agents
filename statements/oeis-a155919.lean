import Mathlib

/-!
# A155919: number of squared hypotenuses mod n in three dimensions

Source: https://oeis.org/A155919 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A155919 (Steven Finch, Jan 30 2009), offset 1: number of squared hypotenuses mod n in
three dimensions. Number of images of the map (x,y,z) -> x^2+y^2+z^2 in Z_n. Data
1, 2, 3, 4, 5, 6, 7, 7, 9, 10, 11, 12, 13, 14, 15, 14, 17, 18, 19, 20, 21, 22, 23, 21, 25, 26, ...
Entry A171231, offset 0: a(n) = (10*2^n + 3 - (-1)^n)/6. Data 2, 4, 7, 14, 27, 54, 107, 214, ...

Formula section, from Andrew Howroyd, Nov 17 2025:
Conjecture: a(2^k) = A171231(k-1) for k > 0; a(p^k) = p^k for odd prime p.

Formalization notes.
* `a n` is the number of elements of the image of the map (x, y, z) -> x^2 + y^2 + z^2 on
  (Z/nZ)^3 (`Set.ncard` of `Set.range`).
* The first part is a(2^k) = A171231(k-1) for k > 0, written without division as
  6 * a(2^k) = 10 * 2^(k-1) + 3 - (-1)^(k-1) in the integers.
* The second part is a(p^k) = p^k for each odd prime p and each k > 0.
-/

namespace OMA.S_oeis_a155919

/-- A155919(n): the number of values of x^2 + y^2 + z^2 in Z/nZ. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard (Set.range fun v : ZMod n × ZMod n × ZMod n => v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

/-- a(2^k) = A171231(k-1) for k > 0, and a(p^k) = p^k for an odd prime p. -/
theorem main :
    (∀ k : ℕ, 0 < k → 6 * (a (2 ^ k) : ℤ) = 10 * 2 ^ (k - 1) + 3 - (-1) ^ (k - 1)) ∧
    (∀ p k : ℕ, p.Prime → p ≠ 2 → 0 < k → a (p ^ k) = p ^ k) := by
  sorry

end OMA.S_oeis_a155919
