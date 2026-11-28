import OMAStatements.S_oeis_a110735

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a110735.main) := by
  intro h
  obtain ⟨g, hl, hb, _, hd⟩ := h 101 (by decide)
  have digits : Nat.digits 10 101 = [1, 0, 1] := by decide
  rw [digits] at hl hd
  rcases g with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, g⟩⟩⟩⟩⟩ <;> simp at hl
  have ha := hb a (by simp)
  have hh := hb b (by simp)
  have hc := hb c (by simp)
  have he := hb d (by simp)
  simp [OMA.S_oeis_a110735.insertDigits, Nat.ofDigits] at hd
  obtain ⟨x, hx⟩ := hd
  by_cases hq : x ≤ 990 + b + 99 * c + 9901 * d <;> omega
