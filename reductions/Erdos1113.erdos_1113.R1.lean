import FormalConjectures.ErdosProblems.«1113»

/-! A reduction to the explicit Filaseta-Finch-Kozek fourth-power candidate
and its exceptional exponent class. Credit: @LDJAI. -/
namespace OMA.R_Erdos1113_erdos_1113_R1

/-- The known fourth-power example of Filaseta, Finch and Kozek. -/
def H1 : Prop := Nat.IsSierpinskiNumber (44745755 ^ 4)

/-- Escape every bounded prime pool within the algebraically factored class. -/
def H2 : Prop := ∀ B : ℕ, ∃ u : ℕ, ∀ p : ℕ, p.Prime → p ≤ B →
  ¬ p ∣ 44745755 ^ 4 * 2 ^ (4*u+2) + 1

theorem main : H1 → H2 → type_of% @Erdos1113.erdos_1113 := by
  intro hs escape
  refine ⟨44745755^4, hs, ?_⟩
  rintro ⟨P,hprime,hcover⟩
  obtain ⟨u,hu⟩ := escape (P.sup id)
  obtain ⟨p,hp,hd⟩ := hcover (4*u+2)
  exact hu p (hprime p hp) (Finset.le_sup (f := id) hp) hd

end OMA.R_Erdos1113_erdos_1113_R1
