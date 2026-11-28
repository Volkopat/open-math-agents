import Mathlib

/-!
# A304523: Number of ordered ways to write n as the sum of a Lucas number (A000032) and a positive odd squarefree number.

Source: https://oeis.org/A304523
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A304523 (Zhi-Wei Sun, May 13 2018): a(n) > 0 for all n
> 1, and a(n) = 1 only for n = 2, 3, 11, 13, 27, 29, 67, 139, 193, 247, 851.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, ...). `a n` is the number of
  pairs (l, s) of natural numbers with l a Lucas number, s a positive odd squarefree number and n
  = l + s, exactly as in the OEIS name.
* Lucas numbers (A000032) are L(0) = 2, L(1) = 1, L(k+2) = L(k) + L(k+1); the helper `luc` below
  is this sequence. The ways are counted by the value l of the Lucas number (the values L(k) are
  pairwise distinct).
* The positivity part is stated for n > 1 and the only-if part for every n >= 1 (the offset).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a304523

/-- The Lucas numbers A000032: L(0) = 2, L(1) = 1, L(k+2) = L(k) + L(k+1). -/
def luc : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (k + 2) => luc k + luc (k + 1)

/-- The condition in the name of A304523 on a tuple, for a given n. -/
def P (n : ℕ) (l s : ℕ) : Prop :=
  (∃ k : ℕ, l = luc k) ∧ 0 < s ∧ Odd s ∧ Squarefree s ∧ l + s = n

/-- A304523: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A304523. -/
theorem main : ∀ n : ℕ, 0 < n → ((1 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({2, 3, 11, 13, 27, 29, 67, 139, 193, 247, 851} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a304523
