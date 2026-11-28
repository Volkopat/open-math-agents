import OMAStatements.S_oeis_a328202
import Mathlib

-- Problem: OEIS A328202, the gcd a(n) of the binomial coefficients C(n, k), 2 <= k <= n - 2.
-- Maiga's conjecture: a(n) = A014963(n) * A014963(n - 1). Israel's conjecture: a(n) > n only
-- when n is a Fermat prime or n - 1 is a Mersenne prime.
-- Statement: statements/oeis-a328202.lean (declaration OMA.S_oeis_a328202.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let E = A014963. E(n) divides C(n, k) for 0 < k < n (a prime p divides C(p^s, k)),
-- and E(n - 1) divides C(n, k) = C(n - 1, k - 1) + C(n - 1, k) for 2 <= k <= n - 2. The two
-- factors are coprime, so E(n) E(n - 1) divides a(n). For the other direction let p be a prime
-- and p^s the largest power of p that is at most n. By Kummer's theorem the exponent of p in
-- C(n, k) is at most the number of i with 1 <= i <= s and p^i not a divisor of k. If n is not
-- p^s or p^s + 1 then k = p^s gives the exponent 0 (k = 2 if s = 0). If n is p^s or p^s + 1
-- then k = p^(s - 1) gives an exponent of at most 1 (k = 2 if s = 1), and p divides
-- E(n) E(n - 1). So a(n) divides E(n) E(n - 1).
-- For the second part, E(n) E(n - 1) > n needs n = p^s and n - 1 = q^t. If s, t >= 2 then
-- (p q)^2 <= n (n - 1) < n^2. If s = 1 then n is an odd prime, q = 2, and n = 2^t + 1 is prime,
-- so t is a power of 2. If t = 1 then n - 1 is an odd prime and n is a power of 2.

namespace OMA.A328202

open OMA.S_oeis_a328202 Finset

lemma E_pos (m : ℕ) : 0 < E m := by
  unfold E
  split_ifs
  · exact Nat.minFac_pos m
  · exact Nat.one_pos

lemma E_dvd_self (m : ℕ) : E m ∣ m := by
  unfold E
  split_ifs
  · exact Nat.minFac_dvd m
  · exact one_dvd m

lemma E_le (m : ℕ) (hm : 0 < m) : E m ≤ m := Nat.le_of_dvd hm (E_dvd_self m)

lemma E_pow (p s : ℕ) (hp : p.Prime) (hs : s ≠ 0) : E (p ^ s) = p := by
  unfold E
  rw [if_pos ((Nat.prime_iff.mp hp).isPrimePow.pow hs), Nat.pow_minFac hs, hp.minFac_eq]

lemma E_prime (p : ℕ) (hp : p.Prime) : E p = p := by
  simpa using E_pow p 1 hp one_ne_zero

lemma E_not (m : ℕ) (h : ¬ IsPrimePow m) : E m = 1 := by
  unfold E
  rw [if_neg h]

lemma E_dvd_choose (m k : ℕ) (hk0 : k ≠ 0) (hkm : k < m) : E m ∣ m.choose k := by
  by_cases h : IsPrimePow m
  · obtain ⟨p, s, hp, hs, rfl⟩ := h
    rw [E_pow p s hp.nat_prime hs.ne']
    exact hp.nat_prime.dvd_choose_pow hk0 hkm.ne
  · rw [E_not m h]
    exact one_dvd _

/-- Kummer's theorem: a carry at the digit `i` needs `p ^ i ≤ n` and `¬ p ^ i ∣ k`. -/
lemma fact_le (p n k : ℕ) (hp : p.Prime) (hkn : k ≤ n) :
    (n.choose k).factorization p
      ≤ ((Ico 1 (Nat.log p n + 1)).filter (fun i => ¬ p ^ i ∣ k)).card := by
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, fun hd => ?_⟩
  have h0 : k % p ^ i = 0 := Nat.mod_eq_zero_of_dvd hd
  have hlt : (n - k) % p ^ i < p ^ i := Nat.mod_lt _ (pow_pos hp.pos i)
  have h2 := hi.2
  rw [h0, zero_add] at h2
  exact absurd h2 (not_le.mpr hlt)

lemma fact_zero (p n k : ℕ) (hp : p.Prime) (hkn : k ≤ n)
    (h : ∀ i, 1 ≤ i → i ≤ Nat.log p n → p ^ i ∣ k) : (n.choose k).factorization p = 0 := by
  have h1 := fact_le p n k hp hkn
  have he : (Ico 1 (Nat.log p n + 1)).filter (fun i => ¬ p ^ i ∣ k) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact not_not.mpr (h i hi.1 (by omega))
  rw [he, Finset.card_empty] at h1
  omega

lemma fact_le_one (p n k a : ℕ) (hp : p.Prime) (hkn : k ≤ n)
    (h : ∀ i, 1 ≤ i → i ≤ Nat.log p n → i ≠ a → p ^ i ∣ k) :
    (n.choose k).factorization p ≤ 1 := by
  refine le_trans (fact_le p n k hp hkn) ?_
  have hs : (Ico 1 (Nat.log p n + 1)).filter (fun i => ¬ p ^ i ∣ k) ⊆ {a} := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Ico] at hi
    rw [Finset.mem_singleton]
    by_contra hne
    exact hi.2 (h i hi.1.1 (by omega) hne)
  exact le_trans (Finset.card_le_card hs) (by simp)

lemma exists_k (n p : ℕ) (hn : 4 ≤ n) (hp : p.Prime) :
    ∃ k, 2 ≤ k ∧ k ≤ n - 2 ∧
      (n.choose k).factorization p ≤ (E n * E (n - 1)).factorization p := by
  have hp2 := hp.two_le
  have hlow : p ^ Nat.log p n ≤ n := Nat.pow_log_le_self p (by omega)
  have hhigh : n < p ^ (Nat.log p n + 1) := Nat.lt_pow_succ_log_self hp.one_lt n
  obtain ⟨s, hs⟩ : ∃ s, Nat.log p n = s := ⟨_, rfl⟩
  rw [hs] at hlow hhigh
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · refine ⟨2, le_rfl, by omega, ?_⟩
    rw [fact_zero p n 2 hp (by omega) (fun i h1 h2 => by omega)]
    exact Nat.zero_le _
  · by_cases hc : n = p ^ s ∨ n = p ^ s + 1
    · have hge : 1 ≤ (E n * E (n - 1)).factorization p := by
        apply hp.factorization_pos_of_dvd (Nat.mul_ne_zero (E_pos _).ne' (E_pos _).ne')
        rcases hc with h | h
        · have hE : E n = p := by rw [h, E_pow p s hp (by omega)]
          exact Dvd.dvd.mul_right (dvd_of_eq hE.symm) _
        · have hE : E (n - 1) = p := by rw [h, Nat.add_sub_cancel, E_pow p s hp (by omega)]
          exact Dvd.dvd.mul_left (dvd_of_eq hE.symm) _
      rcases Nat.lt_or_ge s 2 with h1 | h2
      · exact ⟨2, le_rfl, by omega, le_trans (fact_le_one p n 2 1 hp (by omega)
          (fun i h1 h2 h3 => by omega)) hge⟩
      · have hk2 : 2 ≤ p ^ (s - 1) := le_trans hp2 (Nat.le_self_pow (by omega) p)
        have hmul : p ^ (s - 1) * p = p ^ s := by
          rw [← pow_succ]
          congr 1
          omega
        have hkn : p ^ (s - 1) + 2 ≤ n := by nlinarith
        exact ⟨p ^ (s - 1), hk2, by omega, le_trans (fact_le_one p n _ s hp (by omega)
          (fun i h1 h2 h3 => pow_dvd_pow p (by omega))) hge⟩
    · push Not at hc
      have hk2 : 2 ≤ p ^ s := le_trans hp2 (Nat.le_self_pow (by omega) p)
      refine ⟨p ^ s, hk2, by omega, ?_⟩
      rw [fact_zero p n _ hp hlow (fun i h1 h2 => pow_dvd_pow p (by omega))]
      exact Nat.zero_le _

theorem part1 (n : ℕ) (hn : 4 ≤ n) : a n = E n * E (n - 1) := by
  have hne : E n * E (n - 1) ≠ 0 := Nat.mul_ne_zero (E_pos _).ne' (E_pos _).ne'
  have h2mem : 2 ∈ Finset.Icc 2 (n - 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have ha : a n = (Finset.Icc 2 (n - 2)).gcd (fun k => n.choose k) := rfl
  have hg : a n ≠ 0 := by
    intro h
    rw [ha] at h
    have := (Finset.gcd_eq_zero_iff.mp h) 2 h2mem
    exact (Nat.choose_pos (by omega : 2 ≤ n)).ne' this
  apply Nat.dvd_antisymm
  · rw [← Nat.factorization_prime_le_iff_dvd hg hne]
    intro p hp
    obtain ⟨k, hk2, hkn, hle⟩ := exists_k n p hn hp
    have hd : a n ∣ n.choose k := by
      rw [ha]
      exact Finset.gcd_dvd (Finset.mem_Icc.mpr ⟨hk2, hkn⟩)
    exact le_trans
      ((Nat.factorization_le_iff_dvd hg (Nat.choose_pos (by omega)).ne').mpr hd p) hle
  · rw [ha]
    apply Finset.dvd_gcd
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hcop : Nat.Coprime (E n) (E (n - 1)) := by
      have h1 : Nat.Coprime n (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp
      exact Nat.Coprime.coprime_dvd_left (E_dvd_self n)
        (Nat.Coprime.coprime_dvd_right (E_dvd_self _) h1)
    apply hcop.mul_dvd_of_dvd_of_dvd
    · exact E_dvd_choose n k (by omega) (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.choose_succ_succ]
      exact dvd_add (E_dvd_choose m j (by omega) (by omega))
        (E_dvd_choose m (j + 1) (by omega) (by omega))

theorem part2 (n : ℕ) (hn : 4 ≤ n) :
    n < E n * E (n - 1) ↔
      (n.Prime ∧ ∃ k : ℕ, n = 2 ^ 2 ^ k + 1) ∨ ((n - 1).Prime ∧ ∃ k : ℕ, n = 2 ^ k) := by
  constructor
  · intro h
    by_cases h1 : IsPrimePow n
    swap
    · rw [E_not n h1, one_mul] at h
      have := E_le (n - 1) (by omega)
      omega
    by_cases h2 : IsPrimePow (n - 1)
    swap
    · rw [E_not _ h2, mul_one] at h
      have := E_le n (by omega)
      omega
    obtain ⟨p, s, hp, hs, hps⟩ := h1
    obtain ⟨q, t, hq, ht, hqt⟩ := h2
    have hp' := hp.nat_prime
    have hq' := hq.nat_prime
    have hEn : E n = p := by rw [← hps, E_pow p s hp' hs.ne']
    have hEm : E (n - 1) = q := by rw [← hqt, E_pow q t hq' ht.ne']
    rw [hEn, hEm] at h
    by_cases hs1 : s = 1
    · left
      rw [hs1, pow_one] at hps
      have hnp : n.Prime := hps ▸ hp'
      have hodd : n % 2 = 1 := by
        rcases hnp.eq_two_or_odd with h | h <;> omega
      have h2q : 2 ∣ q ^ t := by
        rw [hqt]
        omega
      have hq2 : q = 2 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq').mp (Nat.prime_two.dvd_of_dvd_pow h2q)).symm
      have hn2 : n = 2 ^ t + 1 := by
        rw [← hq2, hqt]
        omega
      have hP : (2 ^ t + 1).Prime := by
        rw [← hn2]
        exact hnp
      obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) ht.ne' hP
      exact ⟨hnp, m, by rw [hn2, hm]⟩
    · by_cases ht1 : t = 1
      · right
        rw [ht1, pow_one] at hqt
        have hqp : (n - 1).Prime := hqt ▸ hq'
        have hodd : (n - 1) % 2 = 1 := by
          rcases hqp.eq_two_or_odd with h | h <;> omega
        have h2p : 2 ∣ p ^ s := by
          rw [hps]
          omega
        have hp2 : p = 2 :=
          ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp
            (Nat.prime_two.dvd_of_dvd_pow h2p)).symm
        exact ⟨hqp, s, by rw [← hp2, hps]⟩
      · exfalso
        have hs2 : 2 ≤ s := by omega
        have ht2 : 2 ≤ t := by omega
        have h1 : p ^ 2 ≤ n := hps ▸ Nat.pow_le_pow_right hp'.pos hs2
        have h2 : q ^ 2 ≤ n - 1 := hqt ▸ Nat.pow_le_pow_right hq'.pos ht2
        have h3 : p ^ 2 * q ^ 2 ≤ n * (n - 1) := Nat.mul_le_mul h1 h2
        have h4 : n * n < p * q * (p * q) := Nat.mul_lt_mul'' h h
        have h5 : p * q * (p * q) = p ^ 2 * q ^ 2 := by ring
        have h6 : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
        linarith
  · rintro (⟨hnp, k, hk⟩ | ⟨hqp, k, hk⟩)
    · have h1 : E n = n := E_prime n hnp
      have h2 : E (n - 1) = 2 := by
        have h3 : n - 1 = 2 ^ 2 ^ k := by omega
        rw [h3, E_pow 2 _ Nat.prime_two (pow_ne_zero _ two_ne_zero)]
      rw [h1, h2]
      omega
    · have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
        omega
      have h1 : E n = 2 := by rw [hk, E_pow 2 k Nat.prime_two hk0]
      have h2 : E (n - 1) = n - 1 := E_prime _ hqp
      rw [h1, h2]
      omega

theorem result (n : ℕ) (hn : 4 ≤ n) :
    a n = E n * E (n - 1) ∧
    (n < a n ↔ (n.Prime ∧ ∃ k : ℕ, n = 2 ^ 2 ^ k + 1) ∨ ((n - 1).Prime ∧ ∃ k : ℕ, n = 2 ^ k)) :=
  ⟨part1 n hn, by rw [part1 n hn]; exact part2 n hn⟩

end OMA.A328202

theorem OMA.solution : type_of% @OMA.S_oeis_a328202.main :=
  fun n hn => OMA.A328202.result n hn
