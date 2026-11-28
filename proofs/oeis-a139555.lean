import OMAStatements.S_oeis_a139555
import Mathlib

namespace PrimePowerCount

open Finset Nat

private theorem primorial_step {p : ℕ} (hp : p.Prime) :
    primorial p = primorial (p - 1) * p := by
  have hp₂ := hp.two_le
  have h : p - 1 + 1 = p := by omega
  simp only [primorial, h, range_add_one, filter_insert, if_pos hp,
    mem_filter, mem_range, lt_irrefl, false_and, not_false_eq_true, prod_insert]
  exact Nat.mul_comm _ _

private theorem primorial_lower (m : ℕ) (hm : 13 ≤ m) :
    m ^ 3 < primorial (m - 1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hs : m < 26
    · interval_cases m <;> decide
    obtain ⟨p, hp, hp₁, hp₂⟩ :=
      Nat.exists_prime_lt_and_le_two_mul ((m - 1) / 2) (by omega)
    have hpm : p < m := by omega
    have hp13 : 13 ≤ p := by omega
    have hmp : m ≤ 2 * p := by omega
    calc
      m ^ 3 ≤ (2 * p) ^ 3 := Nat.pow_le_pow_left hmp _
      _ = 8 * p ^ 3 := by ring
      _ < p * primorial (p - 1) :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega))
          (Nat.mul_lt_mul_of_pos_left (ih p hpm hp13) hp.pos)
      _ = primorial p := by rw [primorial_step hp, Nat.mul_comm]
      _ ≤ primorial (m - 1) := primorial_mono (by omega)

private theorem missing_primes (n : ℕ) (hn : 60 < n) :
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q < r ∧ Coprime q n ∧ Coprime r n ∧ q * r ≤ n := by
  have hex (a : ℕ) : ∃ p, a < p ∧ p.Prime ∧ ¬ p ∣ n := by
    obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (max a n + 1)
    exact ⟨p, by omega, hp, fun h => (by omega : ¬ p ≤ n)
      (Nat.le_of_dvd (by omega) h)⟩
  have hfirst : ∃ p, p.Prime ∧ ¬ p ∣ n := by
    obtain ⟨p, _, hp, hnp⟩ := hex 0
    exact ⟨p, hp, hnp⟩
  let q := Nat.find hfirst
  have hq : q.Prime ∧ ¬ q ∣ n := Nat.find_spec hfirst
  let r := Nat.find (hex q)
  have hr : q < r ∧ r.Prime ∧ ¬ r ∣ n := Nat.find_spec (hex q)
  have hdiv (p : ℕ) (hp : p.Prime) (hpr : p < r) (hpq : p ≠ q) : p ∣ n := by
    by_contra h
    have hle : q ≤ p := Nat.find_min' hfirst ⟨hp, h⟩
    have : r ≤ p := Nat.find_min' (hex q) ⟨by omega, hp, h⟩
    omega
  refine ⟨q, r, hq.1, hr.2.1, hr.1, hq.1.coprime_iff_not_dvd.mpr hq.2,
    hr.2.1.coprime_iff_not_dvd.mpr hr.2.2, ?_⟩
  by_cases hlarge : 13 ≤ r
  · let s := (range r).filter Nat.Prime
    have hqs : q ∈ s := mem_filter.mpr ⟨mem_range.mpr hr.1, hq.1⟩
    have hd : (∏ p ∈ s.erase q, p) ∣ n := by
      refine prod_primes_dvd n (fun p hp => (mem_filter.mp (mem_erase.mp hp).2).2.prime) ?_
      intro p hp
      obtain ⟨hpq, hp⟩ := mem_erase.mp hp
      exact hdiv p (mem_filter.mp hp).2 (mem_range.mp (mem_filter.mp hp).1) hpq
    have heq : primorial (r - 1) = q * ∏ p ∈ s.erase q, p := by
      have he := mul_prod_erase s (fun p : ℕ => p) hqs
      rw [he]
      simp [s, primorial, show r - 1 + 1 = r by omega]
    have hbound : primorial (r - 1) ≤ q * n := by
      rw [heq]
      exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (by omega) hd)
    have hcube := primorial_lower r hlarge
    have hqr : q * (q * r) ≤ r ^ 3 := by
      calc
        q * (q * r) ≤ r * (r * r) := Nat.mul_le_mul (by omega)
          (Nat.mul_le_mul_right r (by omega))
        _ = r ^ 3 := by ring
    exact le_of_lt (Nat.lt_of_mul_lt_mul_left
      (lt_of_le_of_lt hqr (lt_of_lt_of_le hcube hbound)))
  · have hrsmall : r ≤ 7 ∨ r = 11 := by
      have hpr := hr.2.1
      interval_cases r <;> norm_num at *
    rcases hrsmall with hsmall | hr11
    · exact (Nat.mul_le_mul (by omega : q ≤ 7) hsmall).trans (by omega)
    · have hqsmall : q ≤ 5 ∨ q = 7 := by
        have hpr := hq.1
        have hqr := hr.1
        have hq10 : q ≤ 10 := by omega
        interval_cases q <;> norm_num at *
      rcases hqsmall with hsmall | hq7
      · exact (Nat.mul_le_mul hsmall (by omega : r ≤ 11)).trans (by omega)
      · have h2 : 2 ∣ n := hdiv 2 (by decide) (by omega) (by omega)
        have h3 : 3 ∣ n := hdiv 3 (by decide) (by omega) (by omega)
        have h5 : 5 ∣ n := hdiv 5 (by decide) (by omega) (by omega)
        have h6 : 6 ∣ n := (show Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3
        have h30 : 30 ∣ n := (show Coprime 6 5 by decide).mul_dvd_of_dvd_of_dvd h6 h5
        obtain ⟨k, hk⟩ := h30
        rw [hq7, hr11]
        omega

private theorem not_prime_power {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hne : q ≠ r) :
    ¬ IsPrimePow (q * r) := by
  intro h
  obtain ⟨p, k, hp, _, heq⟩ := (isPrimePow_nat_iff _).mp h
  have h₁ : q = p := Nat.prime_eq_prime_of_dvd_pow hq hp
    (heq ▸ dvd_mul_right q r)
  have h₂ : r = p := Nat.prime_eq_prime_of_dvd_pow hr hp
    (heq ▸ dvd_mul_left r q)
  exact hne (h₁.trans h₂.symm)

end PrimePowerCount

theorem OMA.solution : type_of% @OMA.S_oeis_a139555.main := by
  intro n hn
  obtain ⟨q, r, hq, hr, hqr, hqn, hrn, hbound⟩ := PrimePowerCount.missing_primes n hn
  have cop : Nat.Coprime (q * r) n := hqn.mul_left hrn
  have hlt {k : ℕ} (hk : k ≤ n) (hc : Nat.Coprime k n) : k < n := by
    refine lt_of_le_of_ne hk ?_
    intro heq
    rw [heq] at hc
    have : n = 1 := by simpa [Nat.Coprime] using hc
    omega
  rw [Nat.totient_eq_card_coprime, ← Set.ncard_coe_finset]
  unfold OMA.S_oeis_a139555.a
  refine Set.ncard_lt_ncard ?_ (Finset.finite_toSet _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rintro k ⟨_, hk, hc, _⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt hk hc), hc.symm⟩
  · intro heq
    have hmem : q * r ∈ (Finset.range n).filter (fun k => n.Coprime k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt hbound cop), cop.symm⟩
    have hm := Set.ext_iff.mp heq (q * r) |>.mpr hmem
    rcases hm.2.2.2 with h | h
    · have hp := Nat.mul_le_mul hq.two_le hr.two_le
      omega
    · exact PrimePowerCount.not_prime_power hq hr (ne_of_lt hqr) h