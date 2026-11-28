import OMAStatements.S_oeis_a102341
import Mathlib

/-!
# A102341: close-to-equilateral Heronian triangles — the finiteness statement is false

The triangles `(b + 1, b + 1, b + 2)` have `16 · Area² = (3b + 4) · b · (b + 2)²`, so they are
Heronian with area `(b + 2) w` as soon as `16 w² = (3b + 4) b`.  This Pell-type equation has
the solution `(b, w) = (4, 2)` (the triangle `5, 5, 6` of area `12`) and is preserved by

  `(b, w) ↦ (7b + 16w + 4, 3b + 7w + 2)`,

which strictly increases `b`.  So there are infinitely many such triangles
(`5,5,6`, `65,65,66`, `901,901,902`, …), contradicting finiteness.
-/

namespace OMA.S_oeis_a102341

/-- The Pell-type orbit `(b, w)` starting at `(4, 2)`. -/
def orbit : ℕ → ℕ × ℕ
  | 0 => (4, 2)
  | n + 1 => (7 * (orbit n).1 + 16 * (orbit n).2 + 4, 3 * (orbit n).1 + 7 * (orbit n).2 + 2)

/-- The invariant `16 w² = (3b + 4) b` along the orbit. -/
lemma orbit_inv (n : ℕ) : 16 * (orbit n).2 ^ 2 = (3 * (orbit n).1 + 4) * (orbit n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [orbit]
    nlinarith [ih]

/-- Both coordinates stay positive. -/
lemma orbit_pos (n : ℕ) : 0 < (orbit n).1 ∧ 0 < (orbit n).2 := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih => simp only [orbit]; omega

/-- The first coordinate is strictly increasing. -/
lemma orbit_strictMono : StrictMono fun n => (orbit n).1 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  simp only [orbit]
  omega

/-- Every point of the orbit gives a close-to-equilateral Heronian triangle. -/
lemma orbit_mem (n : ℕ) :
    IsCloseToEquilateralHeronian ((orbit n).1 + 1, (orbit n).1 + 1, (orbit n).1 + 2) := by
  obtain ⟨hb, hw⟩ := orbit_pos n
  have hinv := orbit_inv n
  generalize (orbit n).1 = b at *
  generalize (orbit n).2 = w at *
  refine ⟨by omega, le_rfl, by omega, rfl, (b + 2) * w, Nat.mul_pos (by omega) hw, ?_⟩
  have e1 : b + 1 + (b + 1) + (b + 2) = 3 * b + 4 := by ring
  have e2 : b + 1 + (b + 1) - (b + 2) = b := by omega
  have e3 : b + 1 + (b + 2) - (b + 1) = b + 2 := by omega
  rw [e1, e2, e3]
  calc 16 * ((b + 2) * w) ^ 2 = (b + 2) ^ 2 * (16 * w ^ 2) := by ring
    _ = (b + 2) ^ 2 * ((3 * b + 4) * b) := by rw [hinv]
    _ = (3 * b + 4) * b * (b + 2) * (b + 2) := by ring

end OMA.S_oeis_a102341

open OMA.S_oeis_a102341 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a102341.main) := by
  intro hfin
  have hinj : Function.Injective
      fun n : ℕ => ((orbit n).1 + 1, (orbit n).1 + 1, (orbit n).1 + 2) := by
    intro m n h
    have h1 : (orbit m).1 + 1 = (orbit n).1 + 1 := congrArg Prod.fst h
    exact orbit_strictMono.injective (Nat.succ_injective h1)
  exact Set.infinite_of_injective_forall_mem hinj orbit_mem hfin
