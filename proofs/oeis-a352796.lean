import OMAStatements.S_oeis_a352796
import Mathlib.Tactic

open OMA.S_oeis_a352796 Finset

namespace Bipronics

private lemma sum_iff {m s : ℕ} (hm : 0 < m) :
    s ∈ sums m ↔ ∃ a b : ℕ, a*b = m ∧ a+b = s := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := mem_image.mp h
    exact ⟨a, m/a, Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1, rfl⟩
  · rintro ⟨a, b, rfl, rfl⟩
    have ha : 0 < a := by by_contra! h; simp [show a = 0 by omega] at hm
    exact mem_image.mpr ⟨a, Nat.mem_divisors.mpr ⟨dvd_mul_right a b, hm.ne'⟩,
      by rw [Nat.mul_div_cancel_left _ ha]⟩

private lemma lower (a b c d : ℤ) (hab : a ≤ b) (hc : 0 < c)
    (hp : a*b = c*d) (hs : a+b = c+d+1) : a ≤ c := by
  by_contra! h
  have e : (a-c)*(b-c)+c = 0 := by linear_combination hp - c*hs
  nlinarith only [e, hc, mul_nonneg (by omega : 0 ≤ a-c) (by omega : 0 ≤ b-c)]

private lemma sorted {a b c d : ℕ} (hm : 0 < a*b) (hab : a ≤ b)
    (hp : a*b = c*d) (hs : a+b = c+d+1) : bipronic (a*b) := by
  have le_small (u v : ℕ) (hprod : a*b = u*v) (hsum : a+b = u+v+1) : a ≤ u := by
    have hu : 0 < u := by
      have positive : 0 < u*v := hprod ▸ hm
      by_contra! h
      rw [show u = 0 by omega, Nat.zero_mul] at positive
      exact Nat.lt_irrefl 0 positive
    exact_mod_cast lower a b u v (by exact_mod_cast hab) (by exact_mod_cast hu)
      (by exact_mod_cast hprod) (by exact_mod_cast hsum)
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le (le_small c d hp hs)
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le
    (le_small d (a+x) (by simpa [Nat.mul_comm] using hp) (by omega))
  have hb : b = a+x+y+1 := by omega
  have ha : a = x*y := by rw [hb] at hp; nlinarith
  refine ⟨x, y, ?_⟩
  rw [hb, ha]
  ring

private lemma equivalent {m : ℕ} (hm : 0 < m) : adjacent m ↔ bipronic m := by
  constructor
  · rintro ⟨s,h₁,h₂⟩
    obtain ⟨a,b,hab,hab'⟩ := (sum_iff hm).1 h₂
    obtain ⟨c,d,hcd,hcd'⟩ := (sum_iff hm).1 h₁
    rcases le_total a b with h | h
    · rw [← hab]
      exact sorted (by omega) h (hab.trans hcd.symm) (by omega)
    · have hba : b*a = m := by simpa [Nat.mul_comm] using hab
      rw [← hba]
      exact sorted (by omega) h (hba.trans hcd.symm) (by omega)
  · rintro ⟨x,y,rfl⟩
    refine ⟨x*(y+1)+(x+1)*y, (sum_iff hm).2 ?_, (sum_iff hm).2 ?_⟩
    · exact ⟨x*(y+1), (x+1)*y, by ring, rfl⟩
    · exact ⟨x*y, (x+1)*(y+1), by ring, by ring⟩

end Bipronics

theorem OMA.solution : type_of% @OMA.S_oeis_a352796.main := by
  intro m
  by_cases hz : m = 0
  · subst m
    have h : bipronic 0 := ⟨0,0,rfl⟩
    simp [h]
  · have hm := Nat.pos_of_ne_zero hz
    simp [hm, Bipronics.equivalent hm]
