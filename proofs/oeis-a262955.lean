import OMAStatements.S_oeis_a262955
import Mathlib

/-!
# A disproof of Sun's conjecture on OEIS A262955

Like the accepted disproof for the template entry A262999, we exhibit an n outside the printed
list with a(n) = 1. Here n = 4000: the only pair is (6, 20), with
4000 = 6^4 + 20*21/2 + 2*p_5(29) and p_5(29) = 1247. The OEIS b-file of A262955 also lists
a(4000) = 1. Bounds x < 8, y < 89 and index k < 53 reduce the claim to a finite kernel check.
-/

open OMA.S_oeis_a262955

namespace A262955Disproof

lemma pent_bound {z k : ℕ} (hz : z ≤ 4000) (hk : z = k * (3 * k - 1) / 2) : k < 53 := by
  by_contra h
  push Not at h
  have h1 : 53 * 158 ≤ k * (3 * k - 1) := Nat.mul_le_mul h (by omega)
  omega

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
lemma check : ∀ x : ℕ, x < 8 → ∀ y : ℕ, y < 89 → ∀ k : ℕ, k < 53 →
    (0 < y ∧ x ^ 4 + y * (y + 1) / 2 ≤ 4000 ∧
      (4000 - x ^ 4 - y * (y + 1) / 2 = k * (3 * k - 1) / 2 ∨
        4000 - x ^ 4 - y * (y + 1) / 2 = 2 * (k * (3 * k - 1) / 2))) → x = 6 ∧ y = 20 := by
  decide +kernel

lemma reps4000 : reps 4000 = {(6, 20)} := by
  ext ⟨x, y⟩
  simp only [reps, IsPentagonal, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hy, hle, hp⟩
    have hx : x < 8 := by
      by_contra h
      push Not at h
      have : 8 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left h 4
      omega
    have hy' : y < 89 := by
      by_contra h
      push Not at h
      have : 89 * 90 ≤ y * (y + 1) := Nat.mul_le_mul h (by omega)
      omega
    rcases hp with ⟨k, hk⟩ | ⟨w, ⟨k, hk⟩, hw⟩
    · exact check x hx y hy' k (pent_bound (by omega) hk) ⟨hy, hle, Or.inl hk⟩
    · subst hk
      exact check x hx y hy' k (pent_bound (z := k * (3 * k - 1) / 2) (by omega) rfl)
        ⟨hy, hle, Or.inr hw⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨by norm_num, by norm_num, Or.inr ⟨1247, ⟨29, by norm_num⟩, by norm_num⟩⟩

lemma a_eq_one : a 4000 = 1 := by
  rw [a, reps4000, Set.ncard_singleton]

end A262955Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a262955.main) := by
  intro h
  have h2 := h.2 4000 A262955Disproof.a_eq_one
  simp at h2
