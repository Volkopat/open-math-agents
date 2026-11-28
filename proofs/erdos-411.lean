import OMAStatements.S_erdos_411
import Mathlib

namespace TotientDoubling

open OMA.S_erdos_411 Filter

private theorem from_three (l : ℕ) : g (2 ^ (l + 3) * 3) = 2 ^ (l + 5) := by
  have hc : Nat.Coprime (2 ^ (l + 3)) 3 := (show Nat.Coprime 2 3 by decide).pow_left _
  rw [g, Nat.totient_mul hc, Nat.totient_prime_pow Nat.prime_two (by omega),
    show Nat.totient 3 = 2 by decide, show l + 3 - 1 = l + 2 by omega]
  norm_num [pow_add]
  ring

private theorem from_power (l : ℕ) : g (2 ^ (l + 5)) = 2 ^ (l + 1 + 3) * 3 := by
  rw [g, Nat.totient_prime_pow Nat.prime_two (by omega), show l + 5 - 1 = l + 4 by omega]
  norm_num [pow_add]
  ring

private theorem orbit (k : ℕ) :
    (∃ l : ℕ, g^[k] 24 = 2 ^ (l + 3) * 3) ∨ (∃ l : ℕ, g^[k] 24 = 2 ^ (l + 5)) := by
  induction k with
  | zero => exact Or.inl ⟨0, by decide⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with ⟨l, h⟩ | ⟨l, h⟩
    · exact Or.inr ⟨l, h ▸ from_three l⟩
    · exact Or.inl ⟨l + 1, h ▸ from_power l⟩

private theorem doubles (k : ℕ) : g (g (g^[k] 24)) = 2 * g^[k] 24 := by
  rcases orbit k with ⟨l, h⟩ | ⟨l, h⟩
  · rw [h, from_three, from_power]
    simp only [pow_add]
    norm_num
    ring
  · rw [h, from_power, from_three (l + 1)]
    simp only [pow_add]
    norm_num
    ring

theorem eventual_double : ∀ᶠ k in atTop, g^[k + 2] 18 = 2 * g^[k] 18 := by
  refine eventually_atTop.mpr ⟨1, fun k hk => ?_⟩
  have h18 : g 18 = 24 := by decide
  have h : g^[k] 18 = g^[k - 1] 24 := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, Function.iterate_succ_apply, h18]
  rw [Nat.add_comm k 2, Function.iterate_add_apply, h]
  exact doubles (k - 1)

end TotientDoubling

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_411.main) := by
  intro h
  obtain ⟨_, l, p, hl, hp, he⟩ := (h 18 2 (by decide) (by decide)).1 TotientDoubling.eventual_double
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  have hp₀ : 0 < p := by omega
  have he₁ : 2 ^ l ≤ 18 := by
    calc
      2 ^ l ≤ 2 ^ l * p := Nat.le_mul_of_pos_right _ hp₀
      _ = 18 := he.symm
  have hle : l ≤ 4 := by
    by_contra hgt
    have hpw := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ l by omega)
    norm_num at hpw
    omega
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> interval_cases l <;> norm_num at he