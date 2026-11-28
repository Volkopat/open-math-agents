import OMAStatements.S_mo_113959
import Mathlib

/-! An even orbit starts with an explicitly computable run. Writing n−2 = 2^k u
with u odd, the first odd term is 2 + 3^k u. Only odd composite starts remain. -/
namespace OMA.R_mo_113959_R1

open OMA.S_mo_113959

def H1 : Prop := ∀ n : ℕ, 2 < n → ∃ k u : ℕ, Odd u ∧ n = 2 + 2^k*u ∧
  (∀ j ≤ k, f^[j] n = 2 + 2^(k-j)*3^j*u) ∧
  (∀ j < k, Even (f^[j] n)) ∧ Odd (f^[k] n)

def H2 : Prop := ∀ n : ℕ, 2 < n → Odd n → ¬ n.Prime → ∃ k : ℕ, (f^[k] n).Prime

theorem main : H1 → H2 → type_of% @OMA.S_mo_113959.main := by
  intro orbit oddCase n hn
  rcases eq_or_lt_of_le hn with rfl | h
  · exact ⟨0, Nat.prime_two⟩
  obtain ⟨k, u, hu, _, terms, _, ho⟩ := orbit n h
  by_cases hp : (f^[k] n).Prime
  · exact ⟨k, hp⟩
  have hu' : u ≠ 0 := fun hz => by simp [hz] at hu
  have hpos : 0 < 3^k*u := Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero hu')
  have hlarge : 2 < f^[k] n := by simpa [terms k le_rfl] using hpos
  obtain ⟨l, hl⟩ := oddCase _ hlarge ho hp
  exact ⟨l+k, by rwa [Function.iterate_add_apply]⟩

end OMA.R_mo_113959_R1
