import OMAStatements.S_oeis_a120114
import Mathlib

-- Problem: OEIS A120114, a(n) = lcm(1, ..., 2n+4) / lcm(1, ..., 2n+2). Conjectures of Rotondo:
-- if a(n) is even and not 2 then a(n)/2 is a Mersenne prime; if a(n) is 1 or 2 then 2n+3 is an
-- odd number that is not a prime power, and 2n+3 divides lcm(1, 3, ..., 2n+1).
-- Statement: statements/oeis-a120114.lean (declaration OMA.S_oeis_a120114.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let L(m) = lcm(1, ..., m), and let E(m) = p if m is a power p^k (k >= 1) of a prime p,
-- and E(m) = 1 otherwise. Then L(m+1) = L(m) E(m+1): a prime power p^k that divides L(m) is at
-- most m, so if m+1 = p^(j+1) then L(m) = p^j c with p not a divisor of c; if m+1 is not a prime
-- power then m+1 = u v with u, v coprime and at most m, so m+1 divides L(m). Thus
-- a(n) = E(2n+3) E(2n+4), and E(2n+3) is odd. If a(n) is even then 2n+4 = 2^k and
-- a(n) = 2 E(2^k - 1). If a(n) is not 2 then 2^k - 1 = q^j for a prime q, and a(n)/2 = q.
-- The exponent j is odd because q^j = 3 (mod 4), so q + 1 divides q^j + 1 = 2^k, and q + 1 is a
-- power of 2. If a(n) is 1 or 2 then no odd prime divides a(n), so 2n+3 is not a prime power;
-- then 2n+3 = u v with u, v coprime, odd and less than 2n+3, and u, v divide lcm(1, 3, ..., 2n+1).

namespace OMA.A120114

open OMA.S_oeis_a120114

noncomputable def E (n : ℕ) : ℕ :=
  open Classical in if IsPrimePow n then n.minFac else 1

lemma E_pow (p s : ℕ) (hp : p.Prime) (hs : s ≠ 0) : E (p ^ s) = p := by
  unfold E
  rw [if_pos ((Nat.prime_iff.mp hp).isPrimePow.pow hs), Nat.pow_minFac hs, hp.minFac_eq]

lemma E_not (m : ℕ) (h : ¬ IsPrimePow m) : E m = 1 := by
  unfold E
  rw [if_neg h]

lemma L_pos (m : ℕ) : 0 < L m := by
  unfold L
  apply Nat.pos_of_ne_zero
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  simp at h

lemma dvd_L (m x : ℕ) (h1 : 1 ≤ x) (h2 : x ≤ m) : x ∣ L m :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨h1, h2⟩)

lemma L_succ (m : ℕ) : L (m + 1) = Nat.lcm (m + 1) (L m) := by
  unfold L
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert]
  rfl

/-- A number greater than 1 that is not a prime power is a product of two coprime factors
greater than 1. -/
lemma split (x : ℕ) (hx : 1 < x) (h : ¬ IsPrimePow x) :
    ∃ u v, x = u * v ∧ Nat.Coprime u v ∧ 1 < u ∧ 1 < v := by
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
  obtain ⟨e, r, hr, hxe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : x ≠ 0) p hp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    apply hr
    rw [hxe, pow_zero, one_mul] at hpx
    exact hpx
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hxe
    omega
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply h
    rw [hxe, mul_one]
    exact (Nat.prime_iff.mp hp).isPrimePow.pow he
  refine ⟨p ^ e, r, hxe, Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hr),
    Nat.one_lt_pow he hp.one_lt, by omega⟩

lemma pow_dvd_L (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) (m : ℕ) (h : p ^ k ∣ L m) : p ^ k ≤ m := by
  induction m with
  | zero =>
    have h1 : L 0 = 1 := by simp [L]
    rw [h1, Nat.dvd_one] at h
    have := Nat.one_lt_pow hk hp.one_lt
    omega
  | succ m ih =>
    rw [L_succ] at h
    have hne : Nat.lcm (m + 1) (L m) ≠ 0 := Nat.lcm_ne_zero (by omega) (L_pos m).ne'
    rw [hp.pow_dvd_iff_le_factorization hne, Nat.factorization_lcm (by omega) (L_pos m).ne'] at h
    rcases le_sup_iff.mp h with h1 | h1
    · exact Nat.le_of_dvd (by omega) ((hp.pow_dvd_iff_le_factorization (by omega)).2 h1)
    · have := ih ((hp.pow_dvd_iff_le_factorization (L_pos m).ne').2 h1)
      omega

lemma L_step (m : ℕ) : L (m + 1) = L m * E (m + 1) := by
  rw [L_succ]
  by_cases h : IsPrimePow (m + 1)
  · obtain ⟨p, k, hp, hk, hpk⟩ := h
    have hp' := hp.nat_prime
    rw [← hpk, E_pow p k hp' hk.ne']
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hle : p ^ j ≤ m := by
      have : p ^ j < p ^ (j + 1) := Nat.pow_lt_pow_right hp'.one_lt (by omega)
      omega
    obtain ⟨c, hc⟩ := dvd_L m (p ^ j) (Nat.pow_pos hp'.pos) hle
    have hpc : ¬ p ∣ c := by
      rintro ⟨d, rfl⟩
      have : p ^ (j + 1) ∣ L m := ⟨d, by rw [hc]; ring⟩
      have := pow_dvd_L p (j + 1) hp' (by omega) m this
      omega
    have hcop : Nat.Coprime p c := (Nat.Prime.coprime_iff_not_dvd hp').2 hpc
    rw [hc, pow_succ, Nat.lcm_mul_left, hcop.lcm_eq_mul]
    ring
  · rw [E_not _ h, mul_one]
    apply Nat.lcm_eq_right
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · obtain ⟨u, v, huv, hcop, hu, hv⟩ := split (m + 1) (by omega) h
      rw [huv]
      have hu' : u ≤ m := by nlinarith
      have hv' : v ≤ m := by nlinarith
      exact hcop.mul_dvd_of_dvd_of_dvd (dvd_L m u (by omega) hu') (dvd_L m v (by omega) hv')

lemma a_eq (n : ℕ) : a n = E (2 * n + 3) * E (2 * n + 4) := by
  unfold a
  rw [show 2 * n + 4 = (2 * n + 2 + 1) + 1 from rfl, L_step, L_step, mul_assoc,
    Nat.mul_div_cancel_left _ (L_pos _)]

lemma E_dvd_self (m : ℕ) : E m ∣ m := by
  unfold E
  split_ifs
  · exact Nat.minFac_dvd m
  · exact one_dvd m

lemma E_odd (n : ℕ) : Odd (E (2 * n + 3)) := by
  have h : Odd (2 * n + 3) := ⟨n + 1, by ring⟩
  exact Odd.of_dvd_nat h (E_dvd_self _)

/-- If `2 ^ k - 1` with `k ≥ 2` is a power of the prime `q`, then `q + 1` is a power of 2. -/
lemma mersenne (q j k : ℕ) (hk : 2 ≤ k) (h : q ^ j + 1 = 2 ^ k) :
    ∃ i, q + 1 = 2 ^ i := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 2 := ⟨k - 2, by omega⟩
  have h4 : 2 ^ (t + 2) = 4 * 2 ^ t := by ring
  rcases Nat.even_or_odd j with ⟨s, rfl⟩ | hj
  · exfalso
    have hsq : q ^ (s + s) = (q ^ s) * (q ^ s) := by ring
    have hm : (q ^ s) * (q ^ s) % 4 = 0 ∨ (q ^ s) * (q ^ s) % 4 = 1 := by
      have := Nat.mod_lt (q ^ s) (by norm_num : 0 < 4)
      rw [Nat.mul_mod]
      interval_cases (q ^ s % 4) <;> simp
    omega
  · have hd : q + 1 ∣ q ^ j + 1 ^ j := Odd.nat_add_dvd_pow_add_pow q 1 hj
    rw [one_pow, h] at hd
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact ⟨i, hi⟩

theorem part1 (n : ℕ) (he : Even (a n)) (h2 : a n ≠ 2) :
    (a n / 2).Prime ∧ ∃ k : ℕ, a n / 2 = 2 ^ k - 1 := by
  rw [a_eq] at he h2 ⊢
  have ho := E_odd n
  have he4 : Even (E (2 * n + 4)) := by
    rcases Nat.even_mul.mp he with h | h
    · exact absurd h (Nat.not_even_iff_odd.mpr ho)
    · exact h
  have hpp : IsPrimePow (2 * n + 4) := by
    by_contra hc
    rw [E_not _ hc] at he4
    exact absurd he4 (by decide)
  obtain ⟨p, k, hp, hk, hpk⟩ := hpp
  have hp' := hp.nat_prime
  have hE4 : E (2 * n + 4) = p := by rw [← hpk, E_pow p k hp' hk.ne']
  rw [hE4] at he4 h2 ⊢
  have hp2 : p = 2 := (Nat.Prime.even_iff hp').mp he4
  subst hp2
  rw [Nat.mul_div_cancel _ (by norm_num)]
  have hpp3 : IsPrimePow (2 * n + 3) := by
    by_contra hc
    rw [E_not _ hc] at h2
    exact h2 rfl
  obtain ⟨q, j, hq, hj, hqj⟩ := hpp3
  have hq' := hq.nat_prime
  rw [← hqj, E_pow q j hq' hj.ne']
  refine ⟨hq', ?_⟩
  have hk2 : 2 ≤ k := by
    by_contra hc
    have : k = 1 := by omega
    subst this
    omega
  obtain ⟨i, hi⟩ := mersenne q j k hk2 (by omega)
  exact ⟨i, by omega⟩

theorem part2 (n : ℕ) (h : a n = 1 ∨ a n = 2) :
    (Odd (2 * n + 3) ∧ ¬ (2 * n + 3).Prime ∧ ¬ IsPrimePow (2 * n + 3)) ∧
      (2 * (n + 1) + 1) ∣ oddLcm (n + 1) := by
  have hodd : Odd (2 * n + 3) := ⟨n + 1, by ring⟩
  have hnp : ¬ IsPrimePow (2 * n + 3) := by
    rintro ⟨q, j, hq, hj, hqj⟩
    have hq' := hq.nat_prime
    have hE : E (2 * n + 3) = q := by rw [← hqj, E_pow q j hq' hj.ne']
    have ho := E_odd n
    rw [hE] at ho
    have hq3 : 3 ≤ q := by
      have := hq'.two_le
      rcases ho with ⟨c, hc⟩
      omega
    have hd : q ∣ a n := by
      rw [a_eq, hE]
      exact dvd_mul_right _ _
    rcases h with h | h <;> rw [h] at hd <;> have := Nat.le_of_dvd (by norm_num) hd <;> omega
  refine ⟨⟨hodd, fun hpr => hnp (Nat.prime_iff.mp hpr).isPrimePow, hnp⟩, ?_⟩
  obtain ⟨u, v, huv, hcop, hu, hv⟩ := split (2 * n + 3) (by omega) hnp
  rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring, huv]
  have key : ∀ w, w ∣ 2 * n + 3 → w < 2 * n + 3 → w ∣ oddLcm (n + 1) := by
    intro w hw hlt
    have hwo : Odd w := Odd.of_dvd_nat hodd hw
    obtain ⟨c, hc⟩ := hwo
    have hmem : c ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have := Finset.dvd_lcm (f := fun i => 2 * i + 1) hmem
    rw [hc]
    exact this
  exact hcop.mul_dvd_of_dvd_of_dvd (key u ⟨v, huv⟩ (by nlinarith)) (key v ⟨u, by rw [huv, mul_comm]⟩ (by nlinarith))

end OMA.A120114

theorem OMA.solution : type_of% @OMA.S_oeis_a120114.main :=
  fun n => ⟨fun he h2 => OMA.A120114.part1 n he h2, OMA.A120114.part2 n⟩
