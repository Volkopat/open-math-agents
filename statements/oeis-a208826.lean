import Mathlib

/-!
# A208826: 5-bead necklaces labeled -n..n allowing reversal, with sum zero

Number of 5-bead necklaces labeled with numbers -n..n allowing reversal, with sum zero.
Data (offset 1): 7, 45, 155, 415, 905, 1755, 3085, 5077, 7891, 11761, ...

Conjectures from Colin Barker, Jul 06 2018:
G.f.: x*(7 + 24*x + 27*x^2 + 30*x^3 + 5*x^4 - 2*x^5 + x^6) / ((1 - x)^5*(1 + x)^2).
a(n) = (23*n^4 + 46*n^3 + 58*n^2 + 44*n + 24) / 24 for n even.
a(n) = (23*n^4 + 46*n^3 + 58*n^2 + 26*n + 15) / 24 for n odd.

Conventions: the beads sit at the positions ZMod 5 and a labeling is a function f from
ZMod 5 to the integers with every label in -n..n and the labels summing to zero. Two labelings
are the same necklace when one is obtained from the other by a rotation or a reflection, that is
f i = g (s + i) for all i or f i = g (s - i) for all i, for some s; these ten maps form the
dihedral group of order 10, so the relation is already an equivalence and a n counts its classes.
The g.f. starts at x^1 (offset 1), so its coefficient at x^0 is 0. Every conjecture is stated
for n at least 1.
-/

namespace OMA.S_oeis_a208826

/-- Labelings of the five positions by -n..n with sum zero. -/
def Lab (n : ℕ) : Type := {f : ZMod 5 → ℤ // (∀ i, |f i| ≤ n) ∧ ∑ i, f i = 0}

/-- Same necklace: related by a rotation or a reflection. -/
def Same (n : ℕ) (f g : Lab n) : Prop :=
  ∃ s : ZMod 5, (∀ i, f.1 i = g.1 (s + i)) ∨ (∀ i, f.1 i = g.1 (s - i))

noncomputable def a (n : ℕ) : ℕ := Nat.card (Quot (Same n))

open PowerSeries in
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((1 - X) ^ 5 * (1 + X) ^ 2 : ℚ⟦X⟧) =
        X * (7 + 24 * X + 27 * X ^ 2 + 30 * X ^ 3 + 5 * X ^ 4 - 2 * X ^ 5 + X ^ 6) ∧
      (∀ n : ℕ, 1 ≤ n → Even n →
        (a n : ℚ) = (23 * n ^ 4 + 46 * n ^ 3 + 58 * n ^ 2 + 44 * n + 24) / 24) ∧
      (∀ n : ℕ, 1 ≤ n → Odd n →
        (a n : ℚ) = (23 * n ^ 4 + 46 * n ^ 3 + 58 * n ^ 2 + 26 * n + 15) / 24) := by
  sorry

end OMA.S_oeis_a208826
