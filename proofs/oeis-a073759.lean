import OMAStatements.S_oeis_a073759
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a073759.main := by
  intro n hn
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  set p := n.minFac with hpdef
  have hpn : p ∣ n := Nat.minFac_dvd n
  have := Nat.minFac_le (show 0 < n by omega)
  have : (n - p) % 2 = 0 := by
    rcases hp.eq_two_or_odd with h | h
    · have := (Nat.minFac_eq_two_iff n).1 h; omega
    · have : ¬ 2 ∣ n := fun h2 => by have := (Nat.minFac_eq_two_iff n).2 h2; omega
      omega
  rw [OMA.S_oeis_a073759.halfGap, ← hpdef, show 2 * ((n - p) / 2) = n - p by omega,
    OMA.S_oeis_a073759.a]
  refine le_antisymm (Finset.sup_le fun m hm => ?_) ?_
  · simp only [Finset.mem_filter, Finset.mem_Ico] at hm
    obtain ⟨q, hq, hqm, hqn⟩ := Nat.Prime.not_coprime_iff_dvd.1 hm.2.2
    have := Nat.minFac_le_of_dvd hq.two_le hqn
    have := Nat.le_of_dvd (by omega) (Nat.dvd_sub hqn hqm)
    simp only [id]; omega
  by_cases h : n.Prime
  · simp [p, h.minFac_eq]
  have : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) h
  have := hp.two_le
  have : 2 * p ≤ n := by nlinarith
  refine Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, by omega⟩, fun hd => ?_, fun hc => ?_⟩)
  · have := Nat.le_of_dvd (by omega) (show n - p ∣ p by simpa [Nat.sub_sub_self (by omega : p ≤ n)] using Nat.dvd_sub hd (dvd_refl (n - p)))
    have : n = 2 * p := by omega
    nlinarith
  · have := Nat.dvd_gcd (Nat.dvd_sub hpn (dvd_refl p)) hpn
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
