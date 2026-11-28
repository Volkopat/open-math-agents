import Mathlib

/-!
# A214972: a(n) = a(floor(2*(n-1)/3)) + 1, where a(0) = 0.

Source: https://oeis.org/A214972
Credit: @esracummings31-blip

Conjecture (OEIS A214972): a(n) = a(n-1) + 1 if n is in A152009, and a(n) = a(n-1) otherwise
(for n >= 1).

A152009 is the (L)-sieve transform of A016777 = {1, 4, 7, 10, ..., 3n-2, ...}: start with the
natural numbers N = 1, 2, 3, ...; remove the first term s(1), then from the resulting sequence
delete all terms whose index is a term of A016777, obtaining N'; remove the first term s(2) of N',
delete from the resulting sequence all terms whose index is a term of A016777, and so on.
A152009(n) = s(n).

Conventions. A sequence is a function ℕ → ℕ with index 0 holding the first term (so the
1-based index of position j is j+1). After the first term is removed, the terms that survive the
deletion are those at 1-based indices not in A016777; the i-th survivor (0-based) sits at the
0-based position `Nat.nth kept i` of the shortened sequence.
-/

namespace OMA.S_oeis_a214972

/-- A214972. Here n+1 is the argument, so floor(2*((n+1)-1)/3) = 2*n/3. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => a (2 * n / 3) + 1
decreasing_by omega

/-- A016777: 3n - 2 (n >= 1). -/
def A016777 (n : ℕ) : ℕ := 3 * n - 2

/-- Position j (0-based, so 1-based index j+1) survives the deletion step. -/
def kept (j : ℕ) : Prop := ¬ ∃ m, 1 ≤ m ∧ j + 1 = A016777 m

/-- The sequence after k stages of the sieve (`stage 0` is N = 1, 2, 3, ...). -/
noncomputable def stage : ℕ → ℕ → ℕ
  | 0, i => i + 1
  | k + 1, i => stage k (Nat.nth kept i + 1)

/-- A152009(n) = s(n), the first term of the sequence after n-1 stages (n >= 1). -/
noncomputable def A152009 (n : ℕ) : ℕ := stage (n - 1) 0

theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∃ m, 1 ≤ m ∧ A152009 m = n) → a n = a (n - 1) + 1) ∧
    ((¬ ∃ m, 1 ≤ m ∧ A152009 m = n) → a n = a (n - 1)) := by
  sorry

end OMA.S_oeis_a214972
