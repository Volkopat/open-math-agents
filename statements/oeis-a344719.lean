import Mathlib

/-!
# Minimum paintings with exactly two painted neighbors

Source: https://oeis.org/A344719.
The neighbors of a cell are its orthogonal neighbors within the square.
Each unpainted cell must have exactly two painted neighbors. In the stripe
conjecture the phase can depend on the row, as in the author's program.
The generating function has constant coefficient zero, corresponding to
the empty square.
-/

namespace OMA.S_oeis_a344719

abbrev Cell (n : ℕ) := Fin n × Fin n

def adjacent {n : ℕ} (u v : Cell n) : Bool :=
  decide (
    (u.1 = v.1 ∧ ((u.2.val+1 = v.2.val) ∨ (v.2.val+1 = u.2.val))) ∨
    (u.2 = v.2 ∧ ((u.1.val+1 = v.1.val) ∨ (v.1.val+1 = u.1.val))))

def Fair {n : ℕ} (painted : Finset (Cell n)) : Prop :=
  ∀ v : Cell n, v ∉ painted → (painted.filter (fun u => adjacent u v)).card = 2

def Striped {n : ℕ} (painted : Finset (Cell n)) : Prop :=
  ∀ r : Fin n, 2 ≤ r.val → r.val+2 < n → ∃ s : Fin 3,
    ∀ c : Fin n, 2 ≤ c.val → c.val+2 < n → ((r,c) ∈ painted ↔ c.val % 3 = s.val)

noncomputable def a (n : ℕ) : ℕ :=
  sInf { k | ∃ painted : Finset (Cell n), Fair painted ∧ k = painted.card }

open PowerSeries in
theorem main :
    (∀ n : ℕ, 6 ≤ n → ∃ painted : Finset (Cell n),
      Fair painted ∧ Striped painted ∧ painted.card = a n) ∧
    (∀ n : ℕ, 7 ≤ n → a n = ((n+2)^2+2)/3-6) ∧
    (((1 - X)^3 * (1 + X + X^2) : PowerSeries ℤ) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
        X * (1 + 2*X^2 - X^3 + X^5 - 2*X^6 + 3*X^7 - 3*X^8 + 2*X^9 - X^10)) := by
  sorry

end OMA.S_oeis_a344719
