import OMAStatements.S_oeis_a054118
import Mathlib

/-!
Write r(h) for the sum of row h. Inside the triangle T(n+2, k+2) = T(n+1, k+1) + r(n+1)
(induction on k from the defining rule). Summing this over row n+2 gives r(n+2) = (n+3) r(n+1),
and on the subdiagonal it gives a(n) = a(n-1) + r(n-1). With r(n-1) = n r(n-2) this is
a(n) = (n+1) a(n-1) - n a(n-2).
-/

namespace R054118
open OMA.S_oeis_a054118

/-- The sum of row `h`. -/
def r (h : ℕ) : ℕ := ∑ j ∈ Finset.range (h + 1), T h j

theorem T0 (n : ℕ) : T n 0 = 1 := by
  cases n <;> rw [T]

theorem T1 (n : ℕ) : T (n + 1) 1 = r n := by
  rw [T, r]

theorem Tss (n k : ℕ) : T (n + 1) (k + 2) = T (n + 1) (k + 1) + r (n - (k + 1)) := by
  rw [T, show n + 1 - (k + 2) = n - (k + 1) by omega, r]

theorem Q (n k : ℕ) (hk : k ≤ n) : T (n + 2) (k + 2) = T (n + 1) (k + 1) + r (n + 1) := by
  induction k with
  | zero =>
    show T (n + 1 + 1) (0 + 2) = T (n + 1) (0 + 1) + r (n + 1)
    rw [Tss (n + 1) 0, show n + 1 - (0 + 1) = n by omega, T1 (n + 1), T1 n]
    ring
  | succ k ih =>
    show T (n + 1 + 1) (k + 1 + 2) = T (n + 1) (k + 2) + r (n + 1)
    rw [Tss (n + 1) (k + 1), show n + 1 - (k + 1 + 1) = n - (k + 1) by omega,
      show T (n + 1 + 1) (k + 1 + 1) = T (n + 1) (k + 1) + r (n + 1) from ih (by omega),
      Tss n k]
    ring

theorem rrec (m : ℕ) : r (m + 2) = (m + 3) * r (m + 1) := by
  have h1 : r (m + 2) = ∑ i ∈ Finset.range (m + 1), T (m + 2) (i + 1 + 1) +
      T (m + 2) (0 + 1) + T (m + 2) 0 := by
    rw [r, Finset.sum_range_succ', Finset.sum_range_succ']
  have h2 : r (m + 1) = ∑ i ∈ Finset.range (m + 1), T (m + 1) (i + 1) + T (m + 1) 0 := by
    rw [r, Finset.sum_range_succ']
  have h3 : ∑ i ∈ Finset.range (m + 1), T (m + 2) (i + 1 + 1) =
      ∑ i ∈ Finset.range (m + 1), (T (m + 1) (i + 1) + r (m + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < m + 1 := Finset.mem_range.mp hi
    exact Q m i (by omega)
  have h4 : T (m + 2) (0 + 1) = r (m + 1) := T1 (m + 1)
  rw [h1, h3, h4, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, T0, h2,
    T0]
  push_cast
  ring

theorem solve : ∀ n : ℕ, 6 ≤ n →
    (a n : ℤ) = ((n : ℤ) + 1) * a (n - 1) - (n : ℤ) * a (n - 2) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega]
  have e6 : a (m + 6) = a (m + 5) + r (m + 5) := by
    show T (m + 6) (m + 6 - 3) = T (m + 5) (m + 5 - 3) + r (m + 5)
    rw [show m + 6 - 3 = m + 1 + 2 by omega, show m + 5 - 3 = m + 1 + 1 by omega]
    exact Q (m + 4) (m + 1) (by omega)
  have e5 : a (m + 5) = a (m + 4) + r (m + 4) := by
    show T (m + 5) (m + 5 - 3) = T (m + 4) (m + 4 - 3) + r (m + 4)
    rw [show m + 5 - 3 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
    exact Q (m + 3) m (by omega)
  have hr : r (m + 5) = (m + 6) * r (m + 4) := rrec (m + 3)
  rw [e6, e5, hr]
  push_cast
  ring

end R054118

theorem OMA.solution : type_of% @OMA.S_oeis_a054118.main := R054118.solve
