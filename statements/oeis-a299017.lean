import Mathlib

/-!
# Triangular numbers among the maximum grid-diagonal packings

OEIS A299017 is the increasing intersection of A264041 with the triangular
numbers. A264041 uses an n by n grid of unit cells. The two diagonals of a
single cell cross, and diagonals in different cells can intersect only at a
common endpoint. The offset of A299017 is one. A zero constant coefficient
extends its generating function to a series indexed by all natural numbers.

Sources: https://oeis.org/A299017 and https://oeis.org/A264041
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a299017

abbrev Diagonal (n : ℕ) := Fin n × Fin n × Bool

def endpoints {n : ℕ} (d : Diagonal n) : Finset (ℕ × ℕ) :=
  let i := d.1.val
  let j := d.2.1.val
  if d.2.2 then {(i, j), (i + 1, j + 1)}
  else {(i, j + 1), (i + 1, j)}

def packing {n : ℕ} (s : Finset (Diagonal n)) : Prop :=
  ∀ d ∈ s, ∀ e ∈ s, d ≠ e →
    (d.1, d.2.1) ≠ (e.1, e.2.1) ∧ Disjoint (endpoints d) (endpoints e)

noncomputable def maxDiagonals (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Diagonal n)).powerset.filter packing).sup Finset.card

def commonValues : Set ℕ :=
  {v | (∃ n : ℕ, 0 < n ∧ maxDiagonals n = v) ∧
       (∃ k : ℕ, k * (k + 1) / 2 = v)}

open PowerSeries in
theorem main :
    ∃ a : ℕ → ℕ, a 0 = 0 ∧ StrictMono a ∧ a '' Set.Ioi 0 = commonValues ∧
      (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X)^3 =
        X * (1 + 6 * X^4 - 3 * X^5)) ∧
      (∀ n : ℕ, 3 < n → (a n : ℤ) = 6 - 7 * (n : ℤ) + 2 * (n : ℤ)^2) ∧
      (∀ n : ℕ, 3 < n → (a n : ℤ) =
        3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a299017
