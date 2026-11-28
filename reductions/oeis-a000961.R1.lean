import OMAStatements.S_oeis_a000961
import Mathlib

/-! Evaluate the Euler power sum locally at each full prime-power factor.
The remaining problem concerns only the totients of the complementary
factors and no longer involves power sums. -/
namespace OMA.R_oeis_a000961_R1
open OMA.S_oeis_a000961

def H1 : Prop := ∀ (p e t : ℕ), p.Prime → 0 < t → p.Coprime t →
    let m := p ^ (e + 1) * t
    ((∑ k ∈ Finset.range m, k ^ m.totient) ≡ m.totient [MOD p ^ (e + 1)]) ↔
      t ≡ t.totient [MOD p]

def H2 : Prop := ∀ m : ℕ, 0 < m →
    (∀ p e t : ℕ, p.Prime → p.Coprime t → m = p ^ (e + 1) * t →
      t ≡ t.totient [MOD p]) → InA000961 m

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000961.main := by
  intro localSum classify m hm
  constructor
  · rintro (rfl | h)
    · simp
    obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp h
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    simpa only [mul_one, Nat.ModEq] using
      (localSum p i 1 hp (by decide) (by simp)).mpr (by simp [Nat.ModEq])
  · intro h
    apply classify m hm
    intro p e t hp hc hprod
    subst m
    have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    apply (localSum p e t hp ht hc).mp
    exact Nat.ModEq.of_dvd (dvd_mul_right _ _) h

end OMA.R_oeis_a000961_R1
