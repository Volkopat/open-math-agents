import Mathlib

/-!
# OEIS A183898: nondecreasing arrangements of four residues

Source: https://oeis.org/A183898

A term counts nondecreasing words of length n+3 over the residues 0 through 3 for which
each entry is the sum modulo four of entries in three distinct other positions. The sequence
starts at n=1. The theorem states the empirical cubic, multiplied through by six, and
Colin Barker's generating-function and recurrence conjectures.
-/

namespace OMA.S_oeis_a183898

def Valid {N : ℕ} (w : Fin N → Fin 4) : Prop :=
  ∀ i : Fin N, ∃ t : Finset (Fin N), t.card = 3 ∧ i ∉ t ∧
    (∑ j ∈ t, (w j).val) % 4 = (w i).val

instance (N : ℕ) : DecidablePred (@Valid N) := fun w => by
  unfold Valid
  infer_instance

instance (N : ℕ) : DecidablePred (fun w : Fin N → Fin 4 => Monotone w) := fun w => by
  unfold Monotone
  infer_instance

def sortedWords (N : ℕ) : Finset (Fin N → Fin 4) := Finset.univ.filter Monotone

def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else ((sortedWords (n + 3)).filter Valid).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 ≤ n → 6 * a n = (n : ℤ)^3 + 15*(n : ℤ)^2 + 50*(n : ℤ) - 84) ∧
    (PowerSeries.mk a * (1 - X)^4 = X*(5 - 6*X + 12*X^2 - 18*X^3 + 8*X^4)) ∧
    (∀ n : ℕ, 5 < n → a n = 4*a (n-1) - 6*a (n-2) + 4*a (n-3) - a (n-4)) := by
  sorry

end OMA.S_oeis_a183898
