import OMAStatements.S_oeis_a008544
import Mathlib

/-!
# A008544: Mathar's recurrence for the triple factorials

From the product, a(n) = (3n − 1)·a(n−1) and a(n−2) = (3n − 7)·a(n−3), so the four-term expression
splits into two vanishing pairs (Bill McEachen's argument in the entry). The proof peels the last
factors off the products and compares.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a008544.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  unfold OMA.S_oeis_a008544.a
  rw [Finset.prod_range_succ, Finset.prod_range_succ (n := m + 1), Finset.prod_range_succ (n := m)]
  push_cast
  ring
