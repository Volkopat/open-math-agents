import OMAStatements.S_oeis_a258899
import Mathlib

/-!
# Proof of OEIS A258899 Conjecture

For any `n >= 2 * k + 4` and any proper divisor `m ∣ n` (`1 < m < n`):
Writing `d = n / m`, we have `2 <= m` and `2 <= d`, hence `m + d <= 2 + n / 2` and
`n - m - d >= k`. Since `n! / (m! * d!) = (n - m - d)! * C(n, m) * C(n - m, d)` is divisible by
`(n - m - d)!`, which is divisible by `k!`, hence by `k`, EVERY proper divisor term vanishes mod `k`!

Thus for all `n >= 2 * k + 4`, `a(n) ≡ 2 + 2^n [MOD k]` (coming solely from `m = 1` and `m = n`).
By Euler's theorem, `2^(n + phi(k)) ≡ 2^n [MOD k]` for all `n >= k`, whence
`a(n + phi(k)) ≡ a(n) [MOD k]` for all `n >= 2 * k + 4`.
-/

namespace OeisA258899Proof

open Finset

private lemma mul_fact_dvd_fact_of_add_le {n m d : ℕ} (h : m + d ≤ n) :
    m.factorial * d.factorial * (n - m - d).factorial ∣ n.factorial := by
  have h1 : m.factorial * (n - m).factorial ∣ n.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show m ≤ n by omega)
    exact ⟨Nat.choose n m, by linarith⟩
  have h2 : d.factorial * (n - m - d).factorial ∣ (n - m).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show d ≤ n - m by omega)
    exact ⟨Nat.choose (n - m) d, by linarith⟩
  rcases h1 with ⟨c1, hc1⟩
  rcases h2 with ⟨c2, hc2⟩
  refine ⟨c1 * c2, ?_⟩
  calc n.factorial = m.factorial * (n - m).factorial * c1 := hc1
    _ = m.factorial * (d.factorial * (n - m - d).factorial * c2) * c1 := by rw [hc2]
    _ = m.factorial * d.factorial * (n - m - d).factorial * (c1 * c2) := by ring

private lemma dvd_fact_div_of_proper_div {n m k : ℕ} (hk : 1 ≤ k) (hn : 2 * k + 4 ≤ n)
    (hmdvd : m ∣ n) (hm1 : 1 < m) (hmn : m < n) :
    k ∣ n.factorial / (m.factorial * (n / m).factorial) := by
  set d := n / m
  have hmd : m * d = n := Nat.mul_div_cancel' hmdvd
  have hd2 : 2 ≤ d := by
    cases hd : d with
    | zero => rw [hd, mul_zero] at hmd; omega
    | succ d' =>
      cases d' with
      | zero => simp [hd] at hmd; omega
      | succ d'' => omega
  have hsum : m + d + k ≤ n := by
    have hmul : (m - 2) * (d - 2) ≥ 0 := Nat.zero_le _
    -- 2 * (m + d) <= m * d + 4 = n + 4
    have h2 : 2 * (m + d) ≤ m * d + 4 := by
      have : (m - 2) * (d - 2) + 2 * (m + d) = m * d + 4 := by
        zify [show 2 ≤ m by omega, show 2 ≤ d by omega]
        ring
      omega
    rw [hmd] at h2
    omega
  have hdiv := mul_fact_dvd_fact_of_add_le (n := n) (m := m) (d := d) (by omega)
  rcases hdiv with ⟨c, hc⟩
  have hpos : 0 < m.factorial * d.factorial := Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos d)
  have hquot : n.factorial / (m.factorial * d.factorial) = (n - m - d).factorial * c := by
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hpos]
  rw [hquot]
  exact dvd_mul_of_dvd_left (Nat.dvd_factorial hk (by omega)) c

private lemma a_modEq_two_add_pow {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k + 4 ≤ n) :
    OMA.S_oeis_a258899.a n ≡ 2 + 2 ^ n [MOD k] := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨n', rfl⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  unfold OMA.S_oeis_a258899.a
  push_cast
  have h1mem : 1 ∈ (n' + 1).divisors := Nat.one_mem_divisors.mpr (by omega)
  have hnmem : n' + 1 ∈ (n' + 1).divisors := Nat.mem_divisors.mpr ⟨dvd_refl _, by omega⟩
  have hne : (1 : ℕ) ≠ n' + 1 := by omega
  have hsub : ({1, n' + 1} : Finset ℕ) ⊆ (n' + 1).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1mem
    · exact hnmem
  have hsplit : (n' + 1).divisors = {1, n' + 1} ∪ ((n' + 1).divisors \ {1, n' + 1}) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases h : x ∈ ({1, n' + 1} : Finset ℕ)
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | ⟨h, _⟩)
      · exact hsub h
      · exact h
  rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
  have htail : ∑ m ∈ (n' + 1).divisors \ {1, n' + 1},
      ((2 : ZMod k) ^ m * (((n' + 1).factorial / (m.factorial * ((n' + 1) / m).factorial) : ℕ) : ZMod k)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_sdiff, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    rcases hm with ⟨⟨hmdvd, _⟩, hm1, hmn⟩
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd (by omega)
    have hmle : m ≤ n' + 1 := Nat.le_of_dvd (by omega) hmdvd
    have hdvd := dvd_fact_div_of_proper_div hk hn hmdvd (by omega) (by omega)
    have h0 : (((n' + 1).factorial / (m.factorial * ((n' + 1) / m).factorial) : ℕ) : ZMod k) = 0 :=
      (ZMod.natCast_eq_zero_iff _ k).mpr hdvd
    rw [h0, mul_zero]
  rw [htail, add_zero, Finset.sum_pair hne]
  have hq1 : (n' + 1).factorial / ((1 : ℕ).factorial * ((n' + 1) / 1).factorial) = 1 := by
    simp [Nat.div_self (Nat.factorial_pos (n' + 1))]
  have hqn : (n' + 1).factorial / ((n' + 1).factorial * ((n' + 1) / (n' + 1)).factorial) = 1 := by
    simp [Nat.div_self (Nat.succ_pos n'), Nat.div_self (Nat.factorial_pos (n' + 1))]
  rw [hq1, hqn]
  simp

private lemma pow_add_totient_modEq (r : ℕ) :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → r ^ (n + Nat.totient k) ≡ r ^ n [MOD k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk n hn
    by_cases hk1 : k = 1
    · subst hk1; exact Nat.modEq_one
    · set p := k.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      set e := k.factorization p
      have he_pos : 1 ≤ e :=
        (Nat.Prime.dvd_iff_one_le_factorization hp (by omega)).mp (Nat.minFac_dvd k)
      set q := p ^ e
      have hq_dvd : q ∣ k := Nat.ordProj_dvd k p
      set m := k / q
      have hqm : q * m = k := Nat.mul_div_cancel' hq_dvd
      have hcop : Nat.Coprime q m := by
        have hpm : ¬ p ∣ m := by
          intro hpm
          have hpow1 : p ^ (e + 1) ∣ k := by
            rcases hpm with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            calc k = p ^ e * m := hqm.symm
              _ = p ^ e * (p * t) := by rw [ht]
              _ = p ^ (e + 1) * t := by rw [pow_succ]; ring
          have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp hpow1
          omega
        exact (hp.coprime_iff_not_dvd.mpr hpm).pow_left e
      have hm_pos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, mul_zero] at hqm; omega
        · exact hpos
      have hm_lt : m < k := by
        have hq_gt1 : 1 < q := one_lt_pow₀ hp.one_lt (by omega)
        nlinarith
      suffices h : r ^ (n + Nat.totient k) ≡ r ^ n [MOD q * m] by rwa [hqm] at h
      rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      constructor
      · by_cases hpr : p ∣ r
        · have he_le : e ≤ n := by
            have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
            have h2 : q ≤ k := Nat.le_of_dvd (by omega) hq_dvd
            omega
          have hd1 : q ∣ r ^ n := by
            rcases hpr with ⟨t, rfl⟩
            rw [mul_pow]
            exact dvd_mul_of_dvd_left (pow_dvd_pow p he_le) _
          have hd2 : q ∣ r ^ (n + Nat.totient k) :=
            dvd_trans hd1 (pow_dvd_pow r (Nat.le_add_right n _))
          rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd hd1, Nat.mod_eq_zero_of_dvd hd2]
        · have hcop_rq : Nat.Coprime r q := (hp.coprime_iff_not_dvd.mpr hpr).symm.pow_right e
          have heuler : r ^ Nat.totient q ≡ 1 [MOD q] := Nat.ModEq.pow_totient hcop_rq
          have htdvd : Nat.totient q ∣ Nat.totient k := Nat.totient_dvd_of_dvd hq_dvd
          rcases htdvd with ⟨t, ht⟩
          have hphi : r ^ Nat.totient k ≡ 1 [MOD q] := by
            rw [ht, pow_mul]
            simpa using heuler.pow t
          rw [pow_add]
          simpa using (Nat.ModEq.refl (r ^ n)).mul hphi
      · have hm_dvd : m ∣ k := ⟨q, by linarith⟩
        have htdvd : Nat.totient m ∣ Nat.totient k := Nat.totient_dvd_of_dvd hm_dvd
        rcases htdvd with ⟨t, ht⟩
        rw [ht]
        have hiter : ∀ s : ℕ, r ^ (n + Nat.totient m * s) ≡ r ^ n [MOD m] := by
          intro s
          induction s with
          | zero => simp [Nat.ModEq]
          | succ s ihs =>
            have hstep : r ^ (n + Nat.totient m * s + Nat.totient m) ≡
                r ^ (n + Nat.totient m * s) [MOD m] :=
              ih m hm_lt hm_pos (n + Nat.totient m * s) (by omega)
            rw [show n + Nat.totient m * (s + 1) = n + Nat.totient m * s + Nat.totient m by ring]
            exact hstep.trans ihs
        exact hiter t

end OeisA258899Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a258899.main := by
  intro k hk
  refine ⟨2 * k + 4, fun n hn => ?_⟩
  have h1 := OeisA258899Proof.a_modEq_two_add_pow hk (show 2 * k + 4 ≤ n + Nat.totient k by omega)
  have h2 := OeisA258899Proof.a_modEq_two_add_pow hk hn
  have hpow := OeisA258899Proof.pow_add_totient_modEq 2 k hk n (by omega)
  exact h1.trans (((Nat.ModEq.refl 2).add hpow).trans h2.symm)
