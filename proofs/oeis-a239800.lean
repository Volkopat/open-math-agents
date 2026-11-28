import OMAStatements.S_oeis_a239800
import Mathlib

namespace OMA.A239800Proof

/-- With `m` divisible by every prime `r ≤ K - 1` (for example `m = (K - 1)!`), the number `2*K*m + 1` is coprime to
`2*K` times the product of all `2*m*k + 1` for `k < K`: a common prime `r` of `2*K*m + 1` and `2*m*k + 1` (with
`k ≥ 1`) divides `K*(2*m*k + 1) - k*(2*K*m + 1) = K - k`, so `r ≤ K - 1`, so `r ∣ m`, so `r ∣ 1`. -/
lemma coprime_core (K m : ℕ) (hm : ∀ r : ℕ, r.Prime → r ≤ K - 1 → r ∣ m) :
    Nat.Coprime (2 * K * m + 1) (2 * K * ∏ k ∈ Finset.range K, (2 * m * k + 1)) := by
  apply Nat.coprime_of_dvd
  intro r hr hra hrM
  rcases (Nat.Prime.dvd_mul hr).mp hrM with h2K | hL
  · have h1 : r ∣ 2 * K * m := Dvd.dvd.mul_right h2K m
    exact hr.not_dvd_one ((Nat.dvd_add_right h1).mp hra)
  · obtain ⟨k, hk, hrk⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hL
    rw [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with h0 | hkpos
    · subst h0
      exact hr.not_dvd_one (by simpa using hrk)
    · have h1 : r ∣ K * (2 * m * k + 1) := Dvd.dvd.mul_left hrk K
      have h2 : r ∣ k * (2 * K * m + 1) := Dvd.dvd.mul_left hra k
      have e1 : K * (2 * m * k + 1) = 2 * m * k * K + K := by ring
      have e2 : k * (2 * K * m + 1) = 2 * m * k * K + k := by ring
      have e3 : K * (2 * m * k + 1) = k * (2 * K * m + 1) + (K - k) := by
        rw [e1, e2]
        omega
      rw [e3] at h1
      have h3 : r ∣ K - k := (Nat.dvd_add_right h2).mp h1
      have h4 : r ≤ K - k := Nat.le_of_dvd (by omega) h3
      have h5 : r ∣ m := hm r hr (by omega)
      have h6 : r ∣ 2 * m * k := Dvd.dvd.mul_right (Dvd.dvd.mul_left h5 2) k
      exact hr.not_dvd_one ((Nat.dvd_add_right h6).mp hrk)

/-- For every `K ≥ 1` there is `n ≥ 1` with `2*n*K + 1` prime and `2*n*k + 1` not prime for `1 ≤ k < K`.
Take `m = (K - 1)!`, `L` the product of `2*m*k + 1` over `k < K`, and a prime `p ≡ 2*K*m + 1 (mod 2*K*L)` with
`p > 2*K*m + 1` (Dirichlet); write `p = 2*K*m + 1 + 2*K*L*t` with `t ≥ 1` and put `n = m + L*t`. Then
`2*n*K + 1 = p`, and for `1 ≤ k < K` the factor `2*m*k + 1` of `L` is a proper divisor `> 1` of `2*n*k + 1`. -/
lemma exists_n (K : ℕ) (hK : 1 ≤ K) :
    ∃ n : ℕ, 1 ≤ n ∧ (2 * n * K + 1).Prime ∧ ∀ k : ℕ, 1 ≤ k → k < K → ¬ (2 * n * k + 1).Prime := by
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = Nat.factorial (K - 1) := ⟨_, rfl⟩
  have hm_pos : 0 < m := by
    rw [hm_def]
    exact Nat.factorial_pos _
  have hm : ∀ r : ℕ, r.Prime → r ≤ K - 1 → r ∣ m := by
    intro r hr hle
    rw [hm_def]
    exact Nat.dvd_factorial hr.pos hle
  obtain ⟨L, hL_def⟩ : ∃ L : ℕ, L = ∏ k ∈ Finset.range K, (2 * m * k + 1) := ⟨_, rfl⟩
  have hL_pos : 0 < L := by
    rw [hL_def]
    exact Finset.prod_pos (fun i _ => by positivity)
  have hcop : Nat.Coprime (2 * K * m + 1) (2 * K * L) := by
    rw [hL_def]
    exact coprime_core K m hm
  have hM : 2 * K * L ≠ 0 := (Nat.mul_pos (Nat.mul_pos two_pos (by omega)) hL_pos).ne'
  obtain ⟨p, hpa, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (2 * K * m + 1) hM hcop
  have hdvd : 2 * K * L ∣ p - (2 * K * m + 1) := (Nat.modEq_iff_dvd' hpa.le).mp hmod.symm
  obtain ⟨t, ht⟩ := hdvd
  have ht_pos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      omega
    · exact h
  have hp_eq : p = 2 * K * m + 1 + 2 * K * L * t := by omega
  refine ⟨m + L * t, by omega, ?_, ?_⟩
  · have e : 2 * (m + L * t) * K + 1 = p := by
      rw [hp_eq]
      ring
    rw [e]
    exact hp
  · intro k hk1 hkK hpr
    have hdL : 2 * m * k + 1 ∣ L := by
      rw [hL_def]
      exact Finset.dvd_prod_of_mem (fun i => 2 * m * i + 1) (Finset.mem_range.mpr hkK)
    have e : 2 * (m + L * t) * k + 1 = (2 * m * k + 1) + L * (2 * k * t) := by ring
    have hd : 2 * m * k + 1 ∣ 2 * (m + L * t) * k + 1 := by
      rw [e]
      exact dvd_add dvd_rfl (Dvd.dvd.mul_right hdL _)
    have hk0 : 0 < k := by omega
    have hpos1 : 0 < 2 * m * k := Nat.mul_pos (Nat.mul_pos two_pos hm_pos) hk0
    have hpos2 : 0 < L * (2 * k * t) := Nat.mul_pos hL_pos (Nat.mul_pos (Nat.mul_pos two_pos hk0) ht_pos)
    rcases hpr.eq_one_or_self_of_dvd _ hd with h | h
    · omega
    · omega

end OMA.A239800Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a239800.main := by
  intro K hK
  obtain ⟨n, hn, hp, hnp⟩ := OMA.A239800Proof.exists_n K hK
  refine ⟨n, hn, ?_⟩
  show sInf {k : ℕ | 1 ≤ k ∧ (2 * n * k + 1).Prime} = K
  apply le_antisymm
  · exact Nat.sInf_le ⟨hK, hp⟩
  · refine le_csInf ⟨K, hK, hp⟩ ?_
    rintro k ⟨hk1, hkp⟩
    by_contra hlt
    exact hnp k hk1 (not_le.mp hlt) hkp
