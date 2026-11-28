import OMAStatements.S_oeis_a003108
import Mathlib

/-!
Credit: @ivillar
Disproof: the conjectured g.f. 1/((1 - z)(1 - z^8)) only counts partitions into the parts 1
and 8, so it fails first at n = 27, where the cube 27 itself becomes available. If
(1 - z - z^8 + z^9) A = 1, the coefficients of z^0, ..., z^27 force a(27) = 4 (they give
a(n) = 1 for n < 8 and a(n) = a(n - 8) + 1 for n >= 8). But 27 has at least five partitions
into cubes: 27, 8+8+8+1+1+1, 8+8+1*11, 8+1*19 and 1*27.
-/

namespace OMAA003108Helpers
open OMA.S_oeis_a003108 PowerSeries

theorem key (n : ℕ) :
    coeff n (((1 : PowerSeries ℤ) - X - X ^ 8 + X ^ 9) * mk (fun n => (a003108 n : ℤ))) =
      (a003108 n : ℤ) - (if 1 ≤ n then (a003108 (n - 1) : ℤ) else 0)
        - (if 8 ≤ n then (a003108 (n - 8) : ℤ) else 0)
        + (if 9 ≤ n then (a003108 (n - 9) : ℤ) else 0) := by
  rw [show ((1 : PowerSeries ℤ) - X - X ^ 8 + X ^ 9) * mk (fun n => (a003108 n : ℤ)) =
      mk (fun n => (a003108 n : ℤ)) - X ^ 1 * mk (fun n => (a003108 n : ℤ))
        - X ^ 8 * mk (fun n => (a003108 n : ℤ)) + X ^ 9 * mk (fun n => (a003108 n : ℤ)) by ring]
  simp only [map_add, map_sub, coeff_X_pow_mul', coeff_mk]

def q1 : Nat.Partition 27 := ⟨{27}, by decide, by decide⟩
def q2 : Nat.Partition 27 := ⟨Multiset.replicate 27 1, by decide, by decide⟩
def q3 : Nat.Partition 27 := ⟨Multiset.replicate 19 1 + {8}, by decide, by decide⟩
def q4 : Nat.Partition 27 :=
  ⟨Multiset.replicate 11 1 + Multiset.replicate 2 8, by decide, by decide⟩
def q5 : Nat.Partition 27 :=
  ⟨Multiset.replicate 3 1 + Multiset.replicate 3 8, by decide, by decide⟩

theorem hcube (x : ℕ) (hx : x = 1 ∨ x = 8 ∨ x = 27) : ∃ k : ℕ, 1 ≤ k ∧ x = k ^ 3 := by
  rcases hx with rfl | rfl | rfl
  · exact ⟨1, le_rfl, rfl⟩
  · exact ⟨2, by norm_num, rfl⟩
  · exact ⟨3, by norm_num, rfl⟩

theorem lower : 5 ≤ a003108 27 := by
  classical
  have hS : ({q1, q2, q3, q4, q5} : Finset (Nat.Partition 27)).card = 5 := by decide
  rw [← hS]
  unfold a003108
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  intro x hx
  apply hcube
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [q1, q2, q3, q4, q5] at hx <;> omega

end OMAA003108Helpers

open OMAA003108Helpers OMA.S_oeis_a003108 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a003108.main) := by
  intro h
  have E : ∀ n : ℕ, (a003108 n : ℤ)
      - (if 1 ≤ n then (a003108 (n - 1) : ℤ) else 0)
      - (if 8 ≤ n then (a003108 (n - 8) : ℤ) else 0)
      + (if 9 ≤ n then (a003108 (n - 9) : ℤ) else 0)
      = if n = 0 then 1 else 0 := by
    intro n
    rw [← key, h, coeff_one]
  have e0 : (a003108 0 : ℤ) - 0 - 0
      + 0 = 1 := by
    have h' := E 0
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)] at h'
    exact h'
  have e1 : (a003108 1 : ℤ) - (a003108 0 : ℤ) - 0
      + 0 = 0 := by
    have h' := E 1
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e2 : (a003108 2 : ℤ) - (a003108 1 : ℤ) - 0
      + 0 = 0 := by
    have h' := E 2
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e3 : (a003108 3 : ℤ) - (a003108 2 : ℤ) - 0
      + 0 = 0 := by
    have h' := E 3
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e4 : (a003108 4 : ℤ) - (a003108 3 : ℤ) - 0
      + 0 = 0 := by
    have h' := E 4
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e5 : (a003108 5 : ℤ) - (a003108 4 : ℤ) - 0
      + 0 = 0 := by
    have h' := E 5
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e6 : (a003108 6 : ℤ) - (a003108 5 : ℤ) - 0
      + 0 = 0 := by
    have h' := E 6
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e7 : (a003108 7 : ℤ) - (a003108 6 : ℤ) - 0
      + 0 = 0 := by
    have h' := E 7
    rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e8 : (a003108 8 : ℤ) - (a003108 7 : ℤ) - (a003108 0 : ℤ)
      + 0 = 0 := by
    have h' := E 8
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)] at h'
    exact h'
  have e9 : (a003108 9 : ℤ) - (a003108 8 : ℤ) - (a003108 1 : ℤ)
      + (a003108 0 : ℤ) = 0 := by
    have h' := E 9
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e10 : (a003108 10 : ℤ) - (a003108 9 : ℤ) - (a003108 2 : ℤ)
      + (a003108 1 : ℤ) = 0 := by
    have h' := E 10
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e11 : (a003108 11 : ℤ) - (a003108 10 : ℤ) - (a003108 3 : ℤ)
      + (a003108 2 : ℤ) = 0 := by
    have h' := E 11
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e12 : (a003108 12 : ℤ) - (a003108 11 : ℤ) - (a003108 4 : ℤ)
      + (a003108 3 : ℤ) = 0 := by
    have h' := E 12
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e13 : (a003108 13 : ℤ) - (a003108 12 : ℤ) - (a003108 5 : ℤ)
      + (a003108 4 : ℤ) = 0 := by
    have h' := E 13
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e14 : (a003108 14 : ℤ) - (a003108 13 : ℤ) - (a003108 6 : ℤ)
      + (a003108 5 : ℤ) = 0 := by
    have h' := E 14
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e15 : (a003108 15 : ℤ) - (a003108 14 : ℤ) - (a003108 7 : ℤ)
      + (a003108 6 : ℤ) = 0 := by
    have h' := E 15
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e16 : (a003108 16 : ℤ) - (a003108 15 : ℤ) - (a003108 8 : ℤ)
      + (a003108 7 : ℤ) = 0 := by
    have h' := E 16
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e17 : (a003108 17 : ℤ) - (a003108 16 : ℤ) - (a003108 9 : ℤ)
      + (a003108 8 : ℤ) = 0 := by
    have h' := E 17
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e18 : (a003108 18 : ℤ) - (a003108 17 : ℤ) - (a003108 10 : ℤ)
      + (a003108 9 : ℤ) = 0 := by
    have h' := E 18
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e19 : (a003108 19 : ℤ) - (a003108 18 : ℤ) - (a003108 11 : ℤ)
      + (a003108 10 : ℤ) = 0 := by
    have h' := E 19
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e20 : (a003108 20 : ℤ) - (a003108 19 : ℤ) - (a003108 12 : ℤ)
      + (a003108 11 : ℤ) = 0 := by
    have h' := E 20
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e21 : (a003108 21 : ℤ) - (a003108 20 : ℤ) - (a003108 13 : ℤ)
      + (a003108 12 : ℤ) = 0 := by
    have h' := E 21
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e22 : (a003108 22 : ℤ) - (a003108 21 : ℤ) - (a003108 14 : ℤ)
      + (a003108 13 : ℤ) = 0 := by
    have h' := E 22
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e23 : (a003108 23 : ℤ) - (a003108 22 : ℤ) - (a003108 15 : ℤ)
      + (a003108 14 : ℤ) = 0 := by
    have h' := E 23
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e24 : (a003108 24 : ℤ) - (a003108 23 : ℤ) - (a003108 16 : ℤ)
      + (a003108 15 : ℤ) = 0 := by
    have h' := E 24
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e25 : (a003108 25 : ℤ) - (a003108 24 : ℤ) - (a003108 17 : ℤ)
      + (a003108 16 : ℤ) = 0 := by
    have h' := E 25
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e26 : (a003108 26 : ℤ) - (a003108 25 : ℤ) - (a003108 18 : ℤ)
      + (a003108 17 : ℤ) = 0 := by
    have h' := E 26
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have e27 : (a003108 27 : ℤ) - (a003108 26 : ℤ) - (a003108 19 : ℤ)
      + (a003108 18 : ℤ) = 0 := by
    have h' := E 27
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega)] at h'
    exact h'
  have hl : (5 : ℤ) ≤ (a003108 27 : ℤ) := by exact_mod_cast lower
  linarith
