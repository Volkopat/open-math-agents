import OMAReductions.R_oeis_a001013_R1
import Mathlib

/-! Step oeis-a001013.R1.H1. If `k ≥ 3` is a product of factorials `∏ jᵢ!`, then each
`jᵢ! ≤ k < k!`, so `jᵢ < k`, and `k! = (k-1)! · ∏ jᵢ!` is a product of smaller factorials. If
`k!` is a product of `j!` with `j < k`, then `k` is not prime: a prime `k` would divide some
`j!` with `j < k`. -/

namespace OMA.A001013H1

open OMA.S_oeis_a001013

theorem main (k : ℕ) (hk : 3 ≤ k) :
    (IsJordanPolya k → FactorialOfSmaller k) ∧ (FactorialOfSmaller k → ¬ k.Prime) := by
  constructor
  · rintro ⟨s, hs, hprod⟩
    refine ⟨(k - 1) ::ₘ s, ?_, ?_⟩
    · intro j hj
      rw [Multiset.mem_cons] at hj
      rcases hj with rfl | hj
      · omega
      · refine ⟨hs j hj, ?_⟩
        have hdvd : j.factorial ∣ k := by
          rw [← hprod]
          exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hj)
        have hle : j.factorial ≤ k := Nat.le_of_dvd (by omega) hdvd
        by_contra hjk
        push Not at hjk
        have : k.factorial ≤ j.factorial := Nat.factorial_le hjk
        have : k < k.factorial := Nat.lt_factorial_self hk
        omega
    · rw [Multiset.map_cons, Multiset.prod_cons, hprod]
      have : k = (k - 1) + 1 := by omega
      conv_rhs => rw [this, Nat.factorial_succ]
      rw [← this]; ring
  · rintro ⟨s, hs, hprod⟩ hp
    have hdvd : k ∣ (s.map Nat.factorial).prod := by
      rw [hprod]; exact Nat.dvd_factorial (by omega) le_rfl
    obtain ⟨j, hj, hkx⟩ := hp.prime.exists_mem_multiset_map_dvd hdvd
    have := (Nat.Prime.dvd_factorial hp).1 hkx
    have := (hs j hj).2
    omega

end OMA.A001013H1

theorem OMA.solution : OMA.R_oeis_a001013_R1.H1 :=
  fun k hk => OMA.A001013H1.main k hk
