import Mathlib

/-!
# Unlabelled rank-three lattices with five coatoms

In a bounded graded lattice of rank three, the only ranks between bottom and
top are the atoms and the coatoms. Incidence determines their order. Every
row and every column is nonempty. Two different rows have at most one common
column, since otherwise their join would not exist. Conversely this condition
also gives each pair of coatoms at most one common atom, so all meets and joins
exist. Independently permuting the two ranks is precisely lattice isomorphism.

Barker gives a rational ordinary generating function and a homogeneous
recurrence for n > 15. The series starts at x (offset one). The coefficient
equation below multiplies the series by the stated denominator
(1-x)^5 (1+x)^2 (1+x^2) (1+x+x^2) (1+x+x^2+x^3+x^4).

Source: https://oeis.org/A322600
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a322600

abbrev Incidence (n : ℕ) := Fin n → Fin 5 → Bool

def latticeIncidence {n : ℕ} (m : Incidence n) : Prop :=
  (∀ i, ∃ j, m i j = true) ∧ (∀ j, ∃ i, m i j = true) ∧
  ∀ i k, i ≠ k → ∀ c d,
    m i c = true → m k c = true → m i d = true → m k d = true → c = d

def isomorphic {n : ℕ} (m v : Incidence n) : Prop :=
  ∃ rows : Equiv.Perm (Fin n), ∃ cols : Equiv.Perm (Fin 5),
    ∀ i j, v (rows i) (cols j) = m i j

noncomputable def orbit {n : ℕ} (m : Incidence n) : Finset (Incidence n) := by
  classical
  exact Finset.univ.filter (isomorphic m)

noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact Int.ofNat ((Finset.univ.filter (@latticeIncidence n)).image orbit).card

noncomputable def lag (n d : ℕ) : ℤ := if d < n then a (n - d) else 0

/-- Coefficient of the denominator times the series at exponent n. -/
noncomputable def productCoeff (n : ℕ) : ℤ :=
  lag n 0 - lag n 1 - lag n 2 + lag n 5 + lag n 6 + lag n 7 -
    lag n 8 - lag n 9 - lag n 10 + lag n 13 + lag n 14 - lag n 15

def numerator (n : ℕ) : ℤ :=
  ([0, 1, 4, 14, 43, 102, 184, 282, 368, 411, 400, 333, 237, 142, 70, 26, 7, 1] :
    List ℤ).getD n 0

theorem main :
    (∀ n : ℕ, productCoeff n = numerator n) ∧
    (∀ n : ℕ, 15 < n → a n = a (n-1) + a (n-2) - a (n-5) - a (n-6) - a (n-7) +
      a (n-8) + a (n-9) + a (n-10) - a (n-13) - a (n-14) + a (n-15)) := by
  sorry

end OMA.S_oeis_a322600
