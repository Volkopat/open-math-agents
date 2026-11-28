import OMAStatements.S_arxiv_2205_09212

-- First disproof: @justusklocke-cloud. Both inputs in column 5 must be positive,
-- so they cannot add to 1, although 5 + 5 is congruent to 1 modulo 9.
open OMA.S_arxiv_2205_09212 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2205_09212.main) := by
  intro h
  have h5 : label 5 := by unfold label; decide
  have h1 : label 1 := by unfold label; decide
  obtain ⟨x, y, hx, hy, hxy⟩ := h .add 5 5 1 1 h5 h5 h1
    (by show (5 + 5 : ℤ) ≡ 1 [ZMOD 9]; decide)
    ⟨1, 1, 2, by decide, by decide, by decide, rfl⟩ ⟨rfl, Int.ModEq.refl _⟩
  have px := Int.sign_eq_one_iff_pos.mp (show x.sign = 1 from hx.1)
  have py := Int.sign_eq_one_iff_pos.mp (show y.sign = 1 from hy.1)
  change x + y = 1 at hxy
  omega
