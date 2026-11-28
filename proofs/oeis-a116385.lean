import OMAStatements.S_oeis_a116385
import Mathlib

namespace OMA.S_oeis_a116385

lemma cq (N k d : ℕ) (h : N = k + d) :
    (N.choose k : ℚ) = (N.factorial : ℚ) / ((k.factorial : ℚ) * (d.factorial : ℚ)) := by
  subst h
  rw [Nat.cast_add_choose]

lemma av (j : ℕ) : a (2 * j + 4) = ((2 * j + 4).choose (j + 1) : ℤ) + ((2 * j + 4).choose j : ℤ) := by
  have h1 : besselCoeff 2 (2 * j + 4) = ((2 * j + 4).choose (j + 1) : ℤ) := by
    unfold besselCoeff
    rw [if_pos ⟨by omega, by omega⟩]
    congr 2; omega
  have h2 : besselCoeff 3 (2 * j + 4) = 0 := by
    unfold besselCoeff
    rw [if_neg (by omega)]
  have h3 : besselCoeff 4 (2 * j + 4) = ((2 * j + 4).choose j : ℤ) := by
    unfold besselCoeff
    rw [if_pos ⟨by omega, by omega⟩]
    congr 2; omega
  unfold a; rw [h1, h2, h3]; ring

lemma ao (j : ℕ) : a (2 * j + 3) = 2 * ((2 * j + 3).choose j : ℤ) := by
  have h1 : besselCoeff 2 (2 * j + 3) = 0 := by
    unfold besselCoeff
    rw [if_neg (by omega)]
  have h2 : besselCoeff 3 (2 * j + 3) = ((2 * j + 3).choose j : ℤ) := by
    unfold besselCoeff
    rw [if_pos ⟨by omega, by omega⟩]
    congr 2; omega
  have h3 : besselCoeff 4 (2 * j + 3) = 0 := by
    unfold besselCoeff
    rw [if_neg (by omega)]
  unfold a; rw [h1, h2, h3]; ring

set_option maxRecDepth 100000 in
lemma gen_ev (j : ℕ) :
    ((2 * j + 8 : ℕ) + 4 : ℚ) * (a (2 * j + 8) : ℚ) - 2 * a (2 * j + 7) + (-7 * ((2 * j + 8 : ℕ) : ℚ) - 8) * a (2 * j + 6)
      + 6 * a (2 * j + 5) + 12 * (((2 * j + 8 : ℕ) : ℚ) - 2) * a (2 * j + 4) = 0 := by
  have e8 := av (j + 2)
  have e7 := ao (j + 2)
  have e6 := av (j + 1)
  have e5 := ao (j + 1)
  have e4 := av j
  rw [show 2 * (j + 2) + 4 = 2 * j + 8 by ring, show j + 2 + 1 = j + 3 by ring] at e8
  rw [show 2 * (j + 2) + 3 = 2 * j + 7 by ring] at e7
  rw [show 2 * (j + 1) + 4 = 2 * j + 6 by ring] at e6
  rw [show 2 * (j + 1) + 3 = 2 * j + 5 by ring] at e5
  have e8' : (a (2 * j + 8) : ℚ) = ((2 * j + 8).choose (j + 3) : ℚ) + ((2 * j + 8).choose (j + 2) : ℚ) := by
    rw [e8]; push_cast; ring
  have e7' : (a (2 * j + 7) : ℚ) = 2 * ((2 * j + 7).choose (j + 2) : ℚ) := by
    rw [e7]; push_cast; ring
  have e6' : (a (2 * j + 6) : ℚ) = ((2 * j + 6).choose (j + 2) : ℚ) + ((2 * j + 6).choose (j + 1) : ℚ) := by
    rw [e6]; push_cast; ring
  have e5' : (a (2 * j + 5) : ℚ) = 2 * ((2 * j + 5).choose (j + 1) : ℚ) := by
    rw [e5]; push_cast; ring
  have e4' : (a (2 * j + 4) : ℚ) = ((2 * j + 4).choose (j + 1) : ℚ) + ((2 * j + 4).choose j : ℚ) := by
    rw [e4]; push_cast; ring
  rw [e8', e7', e6', e5', e4']
  rw [cq (2*j+8) (j+3) (j+5) (by ring), cq (2*j+8) (j+2) (j+6) (by ring), cq (2*j+7) (j+2) (j+5) (by ring),
    cq (2*j+6) (j+2) (j+4) (by ring), cq (2*j+6) (j+1) (j+5) (by ring), cq (2*j+5) (j+1) (j+4) (by ring),
    cq (2*j+4) (j+1) (j+3) (by ring), cq (2*j+4) j (j+4) (by ring)]
  simp only [Nat.factorial_succ]
  have hu : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
  have hv : (j.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

set_option maxRecDepth 100000 in
lemma gen_od (j : ℕ) :
    ((2 * j + 7 : ℕ) + 4 : ℚ) * (a (2 * j + 7) : ℚ) - 2 * a (2 * j + 6) + (-7 * ((2 * j + 7 : ℕ) : ℚ) - 8) * a (2 * j + 5)
      + 6 * a (2 * j + 4) + 12 * (((2 * j + 7 : ℕ) : ℚ) - 2) * a (2 * j + 3) = 0 := by
  have e7 := ao (j + 2)
  have e6 := av (j + 1)
  have e5 := ao (j + 1)
  have e4 := av j
  have e3 := ao j
  rw [show 2 * (j + 2) + 3 = 2 * j + 7 by ring] at e7
  rw [show 2 * (j + 1) + 4 = 2 * j + 6 by ring] at e6
  rw [show 2 * (j + 1) + 3 = 2 * j + 5 by ring] at e5
  have e7' : (a (2 * j + 7) : ℚ) = 2 * ((2 * j + 7).choose (j + 2) : ℚ) := by
    rw [e7]; push_cast; ring
  have e6' : (a (2 * j + 6) : ℚ) = ((2 * j + 6).choose (j + 2) : ℚ) + ((2 * j + 6).choose (j + 1) : ℚ) := by
    rw [e6]; push_cast; ring
  have e5' : (a (2 * j + 5) : ℚ) = 2 * ((2 * j + 5).choose (j + 1) : ℚ) := by
    rw [e5]; push_cast; ring
  have e4' : (a (2 * j + 4) : ℚ) = ((2 * j + 4).choose (j + 1) : ℚ) + ((2 * j + 4).choose j : ℚ) := by
    rw [e4]; push_cast; ring
  have e3' : (a (2 * j + 3) : ℚ) = 2 * ((2 * j + 3).choose j : ℚ) := by
    rw [e3]; push_cast; ring
  rw [e7', e6', e5', e4', e3']
  rw [cq (2*j+7) (j+2) (j+5) (by ring), cq (2*j+6) (j+2) (j+4) (by ring), cq (2*j+6) (j+1) (j+5) (by ring),
    cq (2*j+5) (j+1) (j+4) (by ring), cq (2*j+4) (j+1) (j+3) (by ring), cq (2*j+4) j (j+4) (by ring),
    cq (2*j+3) j (j+3) (by ring)]
  simp only [Nat.factorial_succ]
  have hu : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
  have hv : (j.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end OMA.S_oeis_a116385

theorem OMA.solution : type_of% @OMA.S_oeis_a116385.main := by
  intro n hn
  have hq : ∀ j : ℕ, ∀ m : ℕ, m = 2 * j + 8 ∨ m = 2 * j + 7 → True := fun _ _ _ => trivial
  rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
  · rcases (by obtain ⟨j, hj⟩ : ∃ j, q = j + 4 ∨ q = 2 ∨ q = 3 := ⟨q - 4, by omega⟩; rcases hj with hj | hj | hj; exacts [Or.inr (Or.inr ⟨j, hj⟩), Or.inl hj, Or.inr (Or.inl hj)] : q = 2 ∨ q = 3 ∨ ∃ j, q = j + 4) with rfl | rfl | ⟨j, rfl⟩
    · decide
    · decide
    · have := OMA.S_oeis_a116385.gen_ev j
      have h : 2 * (j + 4) = 2 * j + 8 := by ring
      rw [h]
      simp only [show 2 * j + 8 - 1 = 2 * j + 7 by omega, show 2 * j + 8 - 2 = 2 * j + 6 by omega,
        show 2 * j + 8 - 3 = 2 * j + 5 by omega, show 2 * j + 8 - 4 = 2 * j + 4 by omega]
      exact_mod_cast this
  · rcases (by obtain ⟨j, hj⟩ : ∃ j, q = j + 3 ∨ q = 2 := ⟨q - 3, by omega⟩; rcases hj with hj | hj; exacts [Or.inr ⟨j, hj⟩, Or.inl hj] : q = 2 ∨ ∃ j, q = j + 3) with rfl | ⟨j, rfl⟩
    · decide
    · have := OMA.S_oeis_a116385.gen_od j
      have h : 2 * (j + 3) + 1 = 2 * j + 7 := by ring
      rw [h]
      simp only [show 2 * j + 7 - 1 = 2 * j + 6 by omega, show 2 * j + 7 - 2 = 2 * j + 5 by omega,
        show 2 * j + 7 - 3 = 2 * j + 4 by omega, show 2 * j + 7 - 4 = 2 * j + 3 by omega]
      exact_mod_cast this
