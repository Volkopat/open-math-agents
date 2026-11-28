import OMAReductions.R_oeis_a284760_R1_H3_R1_H3_R1

namespace OMA.A284760

open Finset

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
/-- An even exponent with (p mid r+3) has the form (p(2k+1)-3). -/
private theorem checkCandidates :
    ∀ p : Fin 59, p.val.Prime → 5 ≤ p.val → ∀ k : Fin 29,
      let r := p.val * (2 * k.val + 1) - 3
      r < p.val * (p.val - 1) →
      (∑ i ∈ Ico 1 p.val, i ^ r) % p.val ^ 2 = 0 →
      p.val = 37 ∧ r % 36 = 32 := by
  decide +kernel

end OMA.A284760

theorem OMA.solution : OMA.R_oeis_a284760_R1_H3_R1_H3_R1.H1 := by
  intro p hp prime large r hr even congr divides
  have pBound : p < 59 := Finset.mem_range.mp hp
  have rBound : r < p * (p - 1) := Finset.mem_range.mp hr
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero congr
  have qBound : q < p := by
    by_contra! h
    have hmul := Nat.mul_le_mul_left p h
    rw [← hq] at hmul
    rw [Nat.mul_sub_left_distrib, Nat.mul_one] at rBound
    omega
  have qOdd : q % 2 = 1 := by
    by_contra h
    have hqEven : q % 2 = 0 := by omega
    have hmul := Nat.mul_mod p q 2
    rw [← hq, hqEven, Nat.mul_zero] at hmul
    omega
  have hindex : q / 2 < 29 := by omega
  have hexp : p * (2 * (q / 2) + 1) - 3 = r := by
    rw [show 2 * (q / 2) + 1 = q by omega, ← hq]
    omega
  have hcheck := OMA.A284760.checkCandidates ⟨p, pBound⟩ prime large ⟨q / 2, hindex⟩
  dsimp only at hcheck
  rw [hexp] at hcheck
  exact hcheck rBound (Nat.dvd_iff_mod_eq_zero.mp divides)
