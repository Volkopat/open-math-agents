import FormalConjectures.ErdosProblems.«477»

/-! If `a ∈ A`, the representation of `a - 4` is `c + m ^ 2` with `c ∈ A`. Then `a - c = m ^ 2 + 4`
is a difference of two squares, so some integer has two representations. -/

theorem OMA.solution : type_of% @Erdos477.erdos_477.variants.S_sq := by
  intro A
  by_contra! h
  have key (x y k l : ℤ) (hx : x ∈ A) (hy : y ∈ A) (e : x + k ^ 2 = y + l ^ 2) : x = y :=
    congrArg Prod.fst ((h (x + k ^ 2)).unique (y₁ := (x, k ^ 2)) (y₂ := (y, l ^ 2))
      ⟨⟨hx, k, by simp⟩, rfl⟩ ⟨⟨hy, l, by simp⟩, e⟩)
  obtain ⟨⟨a, _⟩, ⟨⟨ha, -⟩, -⟩, -⟩ := h 0
  obtain ⟨⟨c, _⟩, ⟨⟨hc, m, rfl⟩, hm⟩, -⟩ := h (a - 4)
  simp at hm
  obtain ⟨t, rfl | rfl⟩ := m.even_or_odd'
  · nlinarith [key c a (t ^ 2 + 2) (t ^ 2) hc ha (by linear_combination -hm)]
  · nlinarith [key c a (2 * t ^ 2 + 2 * t + 3) (2 * t ^ 2 + 2 * t + 2) hc ha
      (by linear_combination -hm)]
