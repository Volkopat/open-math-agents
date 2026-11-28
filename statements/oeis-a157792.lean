import Mathlib

/-!
# Visibility from one edge of a square lattice (OEIS A157792)

The square has coordinates 0 through n-1. The observers lie on its bottom
edge. A point sees itself, and distinct lattice points see one another when
their coordinate differences are relatively prime. The empty square has count
zero, used as the constant coefficient of the generating series.
-/

namespace OMA.S_oeis_a157792

abbrev Visible (s x h : ℤ) : Prop := (s = x ∧ h = 0) ∨ Int.gcd (s-x) h = 1

abbrev Covers (n : ℕ) (s : Finset ℤ) : Prop :=
  ∀ x h : Fin n, ∃ p ∈ s, Visible p x.val h.val

def edge (n : ℕ) : Finset ℤ := (Finset.range n).image Nat.cast

def sizes (n : ℕ) : Finset ℕ :=
  insert (n+1) ((((edge n).powerset.filter (Covers n)).image Finset.card))

def a (n : ℕ) : ℕ :=
  (sizes n).min' ⟨n+1, Finset.mem_insert_self ..⟩

def numerator : ℕ → ℤ
  | 1 | 3 | 5 | 7 | 12 => 1
  | 4 | 6 | 8 | 10 => -1
  | _ => 0

theorem main :
    (∀ n ≥ 9, a n = n / 3 + 1) ∧
    (∀ n ≥ 13, (a n : ℤ) = a (n-1) + a (n-3) - a (n-4)) ∧
    ((PowerSeries.X^4 - PowerSeries.X^3 - PowerSeries.X + 1) *
      PowerSeries.mk (fun n => (a n : ℤ)) = PowerSeries.mk numerator) := by
  sorry

end OMA.S_oeis_a157792
