import Mathlib

/-!
# A270096: the smallest m with 2^m == 2^n (mod n) is at most n/3

Source: https://oeis.org/A270096 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A270096, offset 1: Smallest m such that 2^m == 2^n (mod n). Data
0, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4, 1, 6, 1, 4, 3, 2, 1, 4, 5, 2, 9, 4, 1, 2, 1, 5, 3, 2, ...

Comments, from Robert Israel, Mar 11 2016:
Conjecture: a(n) <= n/3 for all n > 8.

Formalization notes.
* The exponent m is a nonnegative integer (a(1) = 0 in the data), so `a n` is the infimum in ℕ
  of the set of the m with 2^m ≡ 2^n (mod n) (`Nat.ModEq`). The set contains n, so it is not
  empty and the infimum is its least element.
* The bound a(n) <= n/3 is stated without division as 3 * a(n) <= n. The bound is sharp:
  a(18) = 6 and a(27) = 9.
-/

namespace OMA.S_oeis_a270096

/-- A270096(n): the smallest m ≥ 0 such that 2^m ≡ 2^n (mod n). -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 2 ^ m ≡ 2 ^ n [MOD n]}

/-- Israel's conjecture: a(n) ≤ n/3 for all n > 8. -/
theorem main : ∀ n : ℕ, 8 < n → 3 * a n ≤ n := by
  sorry

end OMA.S_oeis_a270096
