import OMAStatements.S_oeis_a033487

-- Credit: @TienDat8605
-- Felsner, Antipodal pairs and crossing numbers of complete graphs, Sections 3 and 5.
-- Balko, Proof of the Harary–Hill conjecture: an exposition, Corollary 7 (arXiv:2610.34444v2).

namespace OMA.R_oeis_a033487_R1

open OMA.S_oeis_a033487

/-- The odd-order Harary–Hill lower bound for admissible drawings of complete graphs. -/
def H1 : Prop :=
  ∀ s : ℕ, 2 ≤ s →
    let V := Fin (2 * s + 1)
    let E := {e : V × V // e.1 < e.2}
    ∀ (pos : V → Plane) (arc : (e : E) → Path (pos e.1.1) (pos e.1.2)),
      let interior := fun e : E => arc e '' Set.Ioo (0 : unitInterval) 1
      let crossings : Set Plane := {p | ∃ e f : E, e ≠ f ∧ p ∈ interior e ∧ p ∈ interior f}
      Function.Injective pos →
      (∀ e, Function.Injective (arc e)) →
      (∀ e, ∀ p ∈ interior e, ∀ v, p ≠ pos v) →
      crossings.Finite →
      (∀ e f : E, e ≠ f → ∀ p ∈ interior e ∩ interior f,
        crossesAt (interior e) (interior f) p) →
      (∀ e f g : E, e ≠ f → f ≠ g → e ≠ g →
        interior e ∩ interior f ∩ interior g = ∅) →
      (s.choose 2) ^ 2 ≤ crossings.ncard

/-- Remove one vertex and splice its incident arcs in pairs to replace the missing
matching edges. A disk around that vertex costs at most one crossing per pair of chords. -/
def H2 : Prop :=
  ∀ n : ℕ, ∀ D : Drawing (n + 3), Admissible D →
    let V := Fin (2 * (n + 2) + 1)
    let E := {e : V × V // e.1 < e.2}
    ∃ (pos : V → Plane) (arc : (e : E) → Path (pos e.1.1) (pos e.1.2)),
      let interior := fun e : E => arc e '' Set.Ioo (0 : unitInterval) 1
      let crossings : Set Plane := {p | ∃ e f : E, e ≠ f ∧ p ∈ interior e ∧ p ∈ interior f}
      Function.Injective pos ∧
      (∀ e, Function.Injective (arc e)) ∧
      (∀ e, ∀ p ∈ interior e, ∀ v, p ≠ pos v) ∧
      crossings.Finite ∧
      (∀ e f : E, e ≠ f → ∀ p ∈ interior e ∩ interior f,
        crossesAt (interior e) (interior f) p) ∧
      (∀ e f g : E, e ≠ f → f ≠ g → e ≠ g →
        interior e ∩ interior f ∩ interior g = ∅) ∧
      crossings.ncard ≤ (crossingPoints D).ncard + (n + 2).choose 2

/-- In a generic antipodal spherical drawing, each crossing is indexed by four
parts, one of their three pairings into great circles, and one of two antipodes. -/
def H3 : Prop :=
  ∀ n : ℕ, ∃ D : Drawing (n + 3), Admissible D ∧
    ∃ label : crossingPoints D → ((Finset.univ : Finset (Fin (n + 3))).powersetCard 4) × Fin 6,
      Function.Injective label

lemma crossing_formula (n : ℕ) :
    (n + 2).choose 2 ^ 2 = (n + 2).choose 2 + n * (n + 1) * (n + 2) * (n + 3) / 4 := by
  have h : (n + 2).choose 2 * 2 = (n + 2) * (n + 1) := by
    simpa [Nat.descFactorial, Nat.factorial, Nat.mul_comm, show n + 2 - 1 = n + 1 by omega] using
      (Nat.descFactorial_eq_factorial_mul_choose (n + 2) 2).symm
  have hs : 4 * ((n + 2).choose 2 ^ 2) =
      4 * (n + 2).choose 2 + n * (n + 1) * (n + 2) * (n + 3) := by
    calc
      4 * ((n + 2).choose 2 ^ 2) = ((n + 2).choose 2 * 2) ^ 2 := by ring
      _ = 2 * ((n + 2).choose 2 * 2) + n * (n + 1) * (n + 2) * (n + 3) := by
        rw [h]
        ring
      _ = _ := by ring
  omega

lemma six_mul_choose_four (n : ℕ) :
    6 * (n + 3).choose 4 = n * (n + 1) * (n + 2) * (n + 3) / 4 := by
  have h : (n + 3).choose 4 * 24 = (n + 3) * (n + 2) * (n + 1) * n := by
    simpa [Nat.descFactorial, Nat.factorial, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega] using
      (Nat.descFactorial_eq_factorial_mul_choose (n + 3) 4).symm
  rw [show n * (n + 1) * (n + 2) * (n + 3) = (n + 3).choose 4 * 24 by rw [h]; ring]
  omega

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a033487.main := by
  intro hill splice upper n
  have lower (D : Drawing (n + 3)) (hD : Admissible D) :
      n * (n + 1) * (n + 2) * (n + 3) / 4 ≤ (crossingPoints D).ncard := by
    obtain ⟨pos, arc, hpos, harc, hav, hfin, hproper, htriple, hbound⟩ := splice n D hD
    have hh := hill (n + 2) (by omega) pos arc hpos harc hav hfin hproper htriple
    rw [crossing_formula] at hh
    omega
  obtain ⟨D, hD, label, hlabel⟩ := upper n
  have hu : (crossingPoints D).ncard ≤ 6 * (n + 3).choose 4 := by
    have h := Nat.card_le_card_of_injective label hlabel
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := _ × _)] at h
    simpa [Fintype.card_prod, Finset.card_powersetCard, Nat.mul_comm] using h
  rw [six_mul_choose_four] at hu
  exact ⟨⟨D, hD, le_antisymm hu (lower D hD)⟩, by
    rintro _ ⟨D', hD', rfl⟩
    exact lower D' hD'⟩

end OMA.R_oeis_a033487_R1
