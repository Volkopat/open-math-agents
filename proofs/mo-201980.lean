import OMAStatements.S_mo_201980
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_201980.main) := by
  rintro ⟨k, hk, n, hn, x, y, z, hx, hy, hz, h⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have : k ≤ 8 := by simp at hk; omega
  obtain ⟨m, hm, a, b, c⟩ : ∃ m ∈ [x, y, z], x ≤ m ∧ y ≤ m ∧ z ≤ m :=
    ⟨max x (max y z), by simp; omega, by omega, by omega, by omega⟩
  have : m * m ^ d * (m * m * m) ≤ 8 * (m * m * m) := by
    calc _ = m ^ (4 + d) := by ring
      _ ≤ x ^ (4 + d) + y ^ (4 + d) + z ^ (4 + d) := by simp at hm; rcases hm with rfl | rfl | rfl <;> omega
      _ ≤ 8 * m * m * m := by rw [h]; gcongr
      _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right this (by have := hx.trans_le a; positivity)
  have := Nat.one_le_pow d m (by omega)
  rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | h2
  · obtain ⟨rfl, rfl, rfl⟩ : x = 1 ∧ y = 1 ∧ z = 1 := by omega
    simp at h hk; omega
  have := Nat.pow_le_pow_left h2 d
  have := d.lt_two_pow_self
  exact (by decide +kernel : ∀ d ∈ Finset.range 4, ∀ x ∈ Finset.range 9, ∀ y ∈ Finset.range 9, ∀ z ∈ Finset.range 9, ∀ k ∈ ({4, 7, 8} : Finset ℕ), 0 < x → x ^ (4 + d) + y ^ (4 + d) + z ^ (4 + d) ≠ k * x * y * z) d (by simp; nlinarith) x (by simp; nlinarith) y (by simp; nlinarith) z (by simp; nlinarith) k hk hx h
