import OMAStatements.S_oeis_a263450
import Mathlib

-- Credit: @AkiRA-COM-FP

namespace OMA.A263450Aux

theorem zero_mem_digits (p : ℕ) (h1 : p % 100 = 1) (h2 : 100 < p) : 0 ∈ Nat.digits 10 p := by
  rw [Nat.digits_def' (by norm_num) (by omega), Nat.digits_def' (by norm_num) (by omega),
    show p / 10 % 10 = 0 by omega]
  simp

theorem a_eq_one (p : ℕ) (hp : p.Prime) (h1 : p % 100 = 1) (h2 : 100 < p) :
    OMA.S_oeis_a263450.a (Nat.count Nat.Prime p + 1) = 1 := by
  unfold OMA.S_oeis_a263450.a
  rw [show Nat.count Nat.Prime p + 1 - 1 = Nat.count Nat.Prime p by omega, Nat.nth_count hp]
  have hw : 1 ∈ {k : ℕ | 0 < k ∧ 0 ∈ Nat.digits 10 (p ^ k)} :=
    ⟨by decide, by simpa using zero_mem_digits p h1 h2⟩
  exact le_antisymm (Nat.sInf_le hw) (le_csInf ⟨1, hw⟩ (fun _ hk => hk.1))

end OMA.A263450Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a263450.main := by
  have hP : Set.Infinite {p : ℕ | p.Prime ∧ p % 100 = 1 ∧ 100 < p} := by
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨p, hpN, hp, hmod⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := 100) (a := 1) isUnit_one (N + 100)
    refine ⟨p, ⟨hp, ?_, by omega⟩, by omega⟩
    simpa using (ZMod.natCast_eq_natCast_iff' p 1 100).mp (by simpa using hmod)
  have hI : Set.Infinite ((fun p => Nat.count Nat.Prime p + 1) ''
      {p : ℕ | p.Prime ∧ p % 100 = 1 ∧ 100 < p}) := by
    apply hP.image
    intro x hx y hy hxy
    exact Nat.count_injective hx.1 hy.1 (by simpa using hxy)
  apply hI.mono
  rintro n ⟨p, ⟨hp, h1, h2⟩, rfl⟩
  exact ⟨Nat.le_add_left 1 _, OMA.A263450Aux.a_eq_one p hp h1 h2⟩
