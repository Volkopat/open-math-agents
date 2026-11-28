import OMAStatements.S_oeis_a218263
import Mathlib

open OMA.S_oeis_a218263

namespace P218263

lemma bev (t : ℕ) : ((2 * t + 3 : ℕ) : ℚ) * ((2 * t + 2).choose (t + 1) : ℚ) =
    2 * ((2 * t + 1).choose t : ℚ) + 4 * ((2 * t : ℕ) + 1 : ℚ) * ((2 * t).choose t : ℚ) := by
  have h1 := Nat.add_one_mul_choose_eq (2 * t) t
  have h2 := Nat.add_one_mul_choose_eq (2 * t + 1) t
  have hs : (2 * t + 1).choose (t + 1) = (2 * t + 1).choose t := by
    rw [Nat.choose_symm_of_eq_add]; omega
  rw [hs] at h1
  have q1 : ((2 * t + 1 : ℕ) : ℚ) * ((2 * t).choose t : ℚ) = ((2 * t + 1).choose t : ℚ) * ((t : ℚ) + 1) := by
    exact_mod_cast h1
  have q2 : ((2 * t + 1 + 1 : ℕ) : ℚ) * ((2 * t + 1).choose t : ℚ) = ((2 * t + 1 + 1).choose (t + 1) : ℚ) * ((t : ℚ) + 1) := by
    exact_mod_cast h2
  have ht : (t : ℚ) + 1 ≠ 0 := by positivity
  have hz : ((2 * t + 2).choose (t + 1) : ℚ) = 2 * ((2 * t + 1).choose t : ℚ) := by
    apply mul_right_cancel₀ ht
    rw [show 2 * t + 2 = 2 * t + 1 + 1 by omega, ← q2]; push_cast; ring
  push_cast at q1 ⊢
  linear_combination (2 * (t : ℚ) + 3) * hz - 4 * q1

lemma bod (t : ℕ) : ((2 * t + 1 + 3 : ℕ) : ℚ) * ((2 * t + 3).choose (t + 1) : ℚ) =
    2 * ((2 * t + 2).choose (t + 1) : ℚ) + 4 * ((2 * t + 1 : ℕ) + 1 : ℚ) * ((2 * t + 1).choose t : ℚ) := by
  have h1 := Nat.add_one_mul_choose_eq (2 * t + 1) t
  have h2 := Nat.add_one_mul_choose_eq (2 * t + 2) (t + 1)
  have hs : (2 * t + 3).choose (t + 2) = (2 * t + 3).choose (t + 1) := by
    rw [Nat.choose_symm_of_eq_add]; omega
  have q1 : ((2 * t + 1 + 1 : ℕ) : ℚ) * ((2 * t + 1).choose t : ℚ) = ((2 * t + 1 + 1).choose (t + 1) : ℚ) * ((t : ℚ) + 1) := by
    exact_mod_cast h1
  have q2 : ((2 * t + 2 + 1 : ℕ) : ℚ) * ((2 * t + 2).choose (t + 1) : ℚ) = ((2 * t + 2 + 1).choose (t + 1 + 1) : ℚ) * ((t : ℚ) + 1 + 1) := by
    exact_mod_cast h2
  rw [show 2 * t + 2 + 1 = 2 * t + 3 by omega, show t + 1 + 1 = t + 2 by omega, hs] at q2
  have ht : (t : ℚ) + 1 ≠ 0 := by positivity
  have hy : ((2 * t + 2).choose (t + 1) : ℚ) = 2 * ((2 * t + 1).choose t : ℚ) := by
    apply mul_right_cancel₀ ht
    rw [show 2 * t + 2 = 2 * t + 1 + 1 by omega, ← q1]; push_cast; ring
  push_cast at q2 ⊢
  linear_combination -2 * q2 + 4 * ((t : ℚ) + 1) * hy

lemma brec (k x1 x2 : ℕ) (h1 : x1 = k + 1) (h2 : x2 = k + 2) :
    ((k : ℚ) + 3) * (x2.choose (x2 / 2) : ℚ) =
      2 * (x1.choose (x1 / 2) : ℚ) + 4 * ((k : ℚ) + 1) * (k.choose (k / 2) : ℚ) := by
  subst h1 h2
  rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
  · have e1 : (2 * t + 2) / 2 = t + 1 := by omega
    have e2 : (2 * t + 1) / 2 = t := by omega
    have e3 : (2 * t) / 2 = t := by omega
    rw [e1, e2, e3]
    have := bev t
    push_cast at this ⊢
    linear_combination this
  · have e1 : (2 * t + 1 + 2) / 2 = t + 1 := by omega
    have e2 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    have e3 : (2 * t + 1) / 2 = t := by omega
    rw [e1, e2, e3, show 2 * t + 1 + 2 = 2 * t + 3 by omega, show 2 * t + 1 + 1 = 2 * t + 2 by omega]
    have := bod t
    push_cast at this ⊢
    linear_combination this

end P218263

theorem OMA.solution : type_of% @OMA.S_oeis_a218263.main := by
  intro I _ _ hI a ha n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have i0 := hI (m + 2) (by omega)
  have i1 := hI (m + 3) (by omega)
  have i2 := hI (m + 4) (by omega)
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at i0
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega] at i1
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega] at i2
  have b0 := P218263.brec m (m + 1) (m + 2) rfl rfl
  have b1 := P218263.brec (m + 1) (m + 2) (m + 3) rfl rfl
  have b2 := P218263.brec (m + 2) (m + 3) (m + 4) rfl rfl
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  rw [ha (m + 4), ha (m + 3), ha (m + 2), ha (m + 1), ha m]
  push_cast at i0 i1 i2 b0 b1 b2 ⊢
  linear_combination ((24 : ℚ) - 4 * m - 16 * m ^ 2 - 4 * m ^ 3) * i0 + ((30 : ℚ) + 4 * m - 2 * m ^ 2) * i1 +
    ((-10 : ℚ) - 7 * m + 4 * m ^ 2 + m ^ 3) * i2 - ((6 : ℚ) - m - 4 * m ^ 2 - m ^ 3) * b0 -
    ((9 : ℚ) - m ^ 2) * b1 - ((-2 : ℚ) - m + m ^ 2) * b2
