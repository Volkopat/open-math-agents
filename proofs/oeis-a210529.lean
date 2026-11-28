import OMAStatements.S_oeis_a210529
import Mathlib

open OMA.S_oeis_a210529

-- Take a larger prime congruent to p modulo (p-1)!. This gives the stronger
-- unsquared congruence simultaneously for every prime less than p.
theorem OMA.solution : type_of% @OMA.S_oeis_a210529.main := by
  classical
  intro n _
  let p := primeAt n
  have hp : p.Prime := Nat.prime_nth_prime _
  have hpos := hp.pos
  have hc : p.Coprime (p-1).factorial := hp.coprime_iff_not_dvd.mpr fun h => by
    have := hp.dvd_factorial.mp h
    omega
  obtain ⟨q, hq, hprime, he⟩ := Nat.forall_exists_prime_gt_and_modEq p
    (Nat.factorial_ne_zero _) hc
  have ex : ∃ k, k ∈ Candidates p := by
    refine ⟨q, Or.inr hprime, hq.ne', fun r hr hrp => ?_⟩
    have hsmall : r < p := lt_of_le_of_lt (Nat.le_self_pow (by decide) _) hrp
    exact (he.of_dvd (Nat.dvd_factorial hr.pos (by omega))).pow 2
  exact ⟨Nat.find ex, Nat.find_spec ex, fun _ hm => Nat.find_min' ex hm⟩
