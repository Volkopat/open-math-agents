import OMAStatements.S_oeis_a262768
import Mathlib

namespace A262768

lemma cc (k : ℕ) : ((k : ℤ) + 1) * (((2 * (k + 1)).choose (k + 1) : ℕ) : ℤ) =
    2 * (2 * (k : ℤ) + 1) * (((2 * k).choose k : ℕ) : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  simp only [Nat.centralBinom] at h
  exact_mod_cast h

lemma down (k : ℕ) : ((k : ℤ) + 1) * (((2 * k).choose (k + 1) : ℕ) : ℤ) =
    (k : ℤ) * (((2 * k).choose k : ℕ) : ℤ) := by
  have h := Nat.choose_succ_right_eq (2 * k) k
  rw [show 2 * k - k = k by omega] at h
  have hz : (((2 * k).choose (k + 1) : ℕ) : ℤ) * ((k : ℤ) + 1) =
      (((2 * k).choose k : ℕ) : ℤ) * (k : ℤ) := by exact_mod_cast h
  linear_combination hz

lemma up2 (k : ℕ) : ((k : ℤ) + 2) * (((2 * k + 2).choose k : ℕ) : ℤ) =
    2 * (2 * (k : ℤ) + 1) * (((2 * k).choose k : ℕ) : ℤ) := by
  have h1 := Nat.choose_mul_succ_eq (2 * k) k
  have h2 := Nat.choose_mul_succ_eq (2 * k + 1) k
  rw [show 2 * k + 1 - k = k + 1 by omega] at h1
  rw [show 2 * k + 1 + 1 - k = k + 2 by omega] at h2
  have h1z : (((2 * k).choose k : ℕ) : ℤ) * (2 * (k : ℤ) + 1) =
      (((2 * k + 1).choose k : ℕ) : ℤ) * ((k : ℤ) + 1) := by exact_mod_cast h1
  have h2z : (((2 * k + 1).choose k : ℕ) : ℤ) * (2 * (k : ℤ) + 1 + 1) =
      (((2 * k + 2).choose k : ℕ) : ℤ) * ((k : ℤ) + 2) := by exact_mod_cast h2
  have key : ((k : ℤ) + 1) * (((k : ℤ) + 2) * (((2 * k + 2).choose k : ℕ) : ℤ) -
      2 * (2 * (k : ℤ) + 1) * (((2 * k).choose k : ℕ) : ℤ)) = 0 := by
    linear_combination (-(k : ℤ) - 1) * h2z - (2 * (k : ℤ) + 2) * h1z
  have hne : ((k : ℤ) + 1) ≠ 0 := by positivity
  have h := (mul_eq_zero.mp key).resolve_left hne
  linarith

lemma closedA (j : ℕ) : 2 * ((j : ℤ) + 3) * (2 * (j : ℤ) + 1) * OMA.S_oeis_a262768.a (j + 1) =
    (9 * (j : ℤ) + 7) * (j : ℤ) * (((2 * (j + 1)).choose (j + 1) : ℕ) : ℤ) := by
  unfold OMA.S_oeis_a262768.a
  rw [show 2 * (j + 1) - 2 = 2 * j by omega]
  have eP := up2 (j + 1)
  have eQ := down j
  have eC := cc j
  obtain ⟨P, hP⟩ : ∃ P : ℤ, P = (((2 * (j + 1) + 2).choose (j + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (((2 * j).choose (j + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℤ, c' = (((2 * (j + 1)).choose (j + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = (((2 * j).choose j : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hP, ← hc'] at eP
  rw [← hQ, ← hc] at eQ
  rw [← hc', ← hc] at eC
  rw [← hP, ← hQ, ← hc']
  push_cast at eP
  have key : ((j : ℤ) + 1) * (2 * ((j : ℤ) + 3) * (2 * (j : ℤ) + 1) * (P - 2 * c' + Q) -
      (9 * (j : ℤ) + 7) * (j : ℤ) * c') = 0 := by
    linear_combination (2 * (2 * (j : ℤ) + 1) * ((j : ℤ) + 1)) * eP
      + (2 * ((j : ℤ) + 3) * (2 * (j : ℤ) + 1)) * eQ - (((j : ℤ) + 3) * (j : ℤ)) * eC
  have hne : ((j : ℤ) + 1) ≠ 0 := by positivity
  have h := (mul_eq_zero.mp key).resolve_left hne
  linarith

end A262768

theorem OMA.solution : type_of% @OMA.S_oeis_a262768.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
  have e2 := A262768.closedA (m + 2)
  have e1 := A262768.closedA (m + 1)
  have e0 := A262768.closedA m
  have ez := A262768.cc (m + 2)
  have ey := A262768.cc (m + 1)
  rw [show m + 2 + 1 = m + 3 by ring] at e2 ez
  rw [show m + 1 + 1 = m + 2 by ring] at e1 ey
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (((2 * (m + 3)).choose (m + 3) : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = (((2 * (m + 2)).choose (m + 2) : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = (((2 * (m + 1)).choose (m + 1) : ℕ) : ℤ) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℤ, A2 = OMA.S_oeis_a262768.a (m + 3) := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1 : ℤ, A1 = OMA.S_oeis_a262768.a (m + 2) := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℤ, A0 = OMA.S_oeis_a262768.a (m + 1) := ⟨_, rfl⟩
  rw [← hz, ← hA2] at e2
  rw [← hy, ← hA1] at e1
  rw [← hx, ← hA0] at e0
  rw [← hz, ← hy] at ez
  rw [← hy, ← hx] at ey
  rw [← hA2, ← hA1, ← hA0]
  push_cast at e2 e1 e0 ez ey ⊢
  have key : ((2 * (m : ℤ) + 5) * ((m : ℤ) + 3) * 2 * (2 * (m : ℤ) + 3)) *
      (-2 * ((m : ℤ) + 3 + 2) * (49 * ((m : ℤ) + 3) - 95) * A2
        + 325 * ((m : ℤ) + 3 - 1) * ((m : ℤ) + 3 + 1) * A1
        + 2 * (67 * ((m : ℤ) + 3) - 38) * (2 * ((m : ℤ) + 3) - 5) * A0) = 0 := by
    linear_combination
      (-(49 * (m : ℤ) + 52) * ((m : ℤ) + 3) * 2 * (2 * (m : ℤ) + 3)) * e2
      - ((49 * (m : ℤ) + 52) * 2 * (2 * (m : ℤ) + 3) * (9 * (m : ℤ) + 25) * ((m : ℤ) + 2)) * ez
      + (325 * ((m : ℤ) + 2) * (2 * (m : ℤ) + 5) * ((m : ℤ) + 3)) * e1
      + (2 * (67 * (m : ℤ) + 163) * (2 * (m : ℤ) + 5) * (2 * (m : ℤ) + 3)) * e0
      + ((2 * (m : ℤ) + 5) * (-4 * (49 * (m : ℤ) + 52) * (9 * (m : ℤ) + 25) * (2 * (m : ℤ) + 3)
          + 325 * ((m : ℤ) + 3) * (9 * (m : ℤ) + 16) * ((m : ℤ) + 1))) * ey
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have p1 : (0 : ℤ) < 2 * (m : ℤ) + 5 := by omega
  have p2 : (0 : ℤ) < (m : ℤ) + 3 := by omega
  have p3 : (0 : ℤ) < 2 * (m : ℤ) + 3 := by omega
  have hne : ((2 * (m : ℤ) + 5) * ((m : ℤ) + 3) * 2 * (2 * (m : ℤ) + 3)) ≠ 0 :=
    (mul_pos (mul_pos (mul_pos p1 p2) (by norm_num)) p3).ne'
  exact (mul_eq_zero.mp key).resolve_left hne
