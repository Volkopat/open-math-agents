import Mathlib

/-!
# OEIS A073503

Source: https://oeis.org/A073503
Credit: @laurilehtinen

OEIS Foundation, CC BY-SA 4.0. Benoit Cloitre posed the conjectures.
Charles R Greathouse IV recorded their refutation in 2012. The statement
below retains the original strict bound and the disjunction as written.
-/

namespace OMA.S_oeis_a073503

/-- Count the residue classes modulo m whose k-th power is one. -/
def rootCount (m k : ℕ) : ℕ :=
  Nat.count (fun x => x^k % m = 1 % m) m

/-- The positive moduli defining A073503. -/
abbrev qualifies (m : ℕ) : Prop :=
  0 < m ∧ rootCount m 4 = 2 * rootCount m 2

/-- OEIS starts at index one. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth qualifies (n-1)

theorem main :
    Set.Infinite {n : ℕ | 0 < n ∧ (2*n > a n ∨ 2*n < a n)} ∧
    (∀ n : ℕ, 45 < n → |(a n : ℝ) - 2*(n : ℝ)| < Real.sqrt n) := by
  sorry

end OMA.S_oeis_a073503

