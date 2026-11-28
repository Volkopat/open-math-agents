import OMAStatements.S_oeis_a273309

/-!
The recurrence in OEIS A273309 is conjectured for n > 3. At n = 5 its
right-hand side is 116. The proposed closed form gives 112 at this index,
so the conjunction in the statement is false.
-/

open OMA.S_oeis_a273309

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a273309.main) := by
  intro h
  have h₁ : a 1 = 4 := by decide
  have h₂ : a 2 = 17 := by
    simpa using h.2.1 2 (by decide) (by decide)
  have h₄ : a 4 = 73 := by
    simpa using h.2.1 4 (by decide) (by decide)
  have h₅ : a 5 = 112 := by
    simpa using h.2.2.1 5 (by decide) (by decide)
  have hrec := h.2.2.2.1 5 (by decide)
  norm_num [h₁, h₂, h₄, h₅] at hrec
