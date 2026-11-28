import OMAStatements.S_oeis_a272766

namespace OMA.S_oeis_a272766


theorem primorial_eleven : primorial 11 = 2310 := by
  decide

theorem witness : (2 * 2310) ^ 2 - 1 ∣ (2 ^ 37) ^ (2 * 2310) - 1 := by
  decide +kernel

theorem not_term_2310 : ¬ IsTerm 2310 := by
  intro h
  exact h.2.2 37 (by norm_num) (by norm_num) witness

/-- The conjecture as stated, with the trivial primorial 1 excluded. -/
theorem conjecture_false :
    ¬ (∀ n : ℕ, 1 < primorial n → IsTerm (primorial n)) := by
  intro h
  have := h 11 (by rw [primorial_eleven]; norm_num)
  rw [primorial_eleven] at this
  exact not_term_2310 this

theorem disproof : ¬ (∀ n : ℕ, 1 < primorial n → IsTerm (primorial n)) := conjecture_false

end OMA.S_oeis_a272766

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a272766.main) :=
  OMA.S_oeis_a272766.disproof
