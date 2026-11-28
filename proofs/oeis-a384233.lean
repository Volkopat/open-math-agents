import OMAStatements.S_oeis_a384233
import Mathlib

-- Proof: the largest odd noncomposite divisor d of m is the 2nd divisor iff d is the least
-- prime factor of m; then m is odd and every prime factor of m is odd, at most d and at least
-- the least prime factor d, so m is a power p^j (j >= 1) of the odd prime p = d. Conversely
-- such an m has largest odd noncomposite divisor p and the only smaller divisor is 1. So the
-- numbers with the property for k = 2 are exactly the powers of odd primes other than 1, and
-- since 1 is the least power of an odd prime, the (n-1)-th of the former is the n-th of the
-- latter (compared through Nat.count).

namespace OMA.P_a384233
open OMA.S_oeis_a384233

lemma char (m : ℕ) : hasProperty 2 m ↔ IsOddPrimePower m ∧ m ≠ 1 := by
  constructor
  · rintro ⟨hm, d, ⟨hdm, hdodd, hdnc, hmax⟩, hcard⟩
    have hm0 : m ≠ 0 := hm.ne'
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hdm
    have hd1 : d ≠ 1 := by
      rintro rfl
      have : m.divisors.filter (· < 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx
        have := Nat.pos_of_mem_divisors hx
        omega
      rw [this, Finset.card_empty] at hcard
      omega
    have hdp : d.Prime := hdnc.resolve_left hd1
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hd1 (Nat.dvd_one.1 hdvd)
    have hq : m.minFac.Prime := Nat.minFac_prime hm1
    have hqd : m.minFac ≤ d := Nat.minFac_le_of_dvd hdp.two_le hdvd
    have hqeq : m.minFac = d := by
      by_contra hne
      have hlt : m.minFac < d := lt_of_le_of_ne hqd hne
      have hsub : ({1, m.minFac} : Finset ℕ) ⊆ m.divisors.filter (· < d) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_filter]
        rcases hx with rfl | rfl
        · exact ⟨Nat.one_mem_divisors.2 hm0, hdp.one_lt⟩
        · exact ⟨Nat.mem_divisors.2 ⟨Nat.minFac_dvd m, hm0⟩, hlt⟩
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_pair (Ne.symm hq.one_lt.ne')] at h2
      omega
    have hodd : ¬ 2 ∣ m := by
      intro h2
      have := Nat.minFac_le_of_dvd le_rfl h2
      have := hq.two_le
      have hd2 : d = 2 := by omega
      rw [hd2] at hdodd
      exact absurd hdodd (by decide)
    have huniq : ∀ {r : ℕ}, r.Prime → r ∣ m → r = d := by
      intro r hr hrm
      have hr2 : r ≠ 2 := by
        rintro rfl
        exact hodd hrm
      have h1 : r ≤ d := hmax r (Nat.mem_divisors.2 ⟨hrm, hm0⟩) (hr.odd_of_ne_two hr2) (Or.inr hr)
      have h2 : m.minFac ≤ r := Nat.minFac_le_of_dvd hr.two_le hrm
      omega
    exact ⟨⟨d, _, hdp, hdodd, Nat.eq_prime_pow_of_unique_prime_dvd hm0 huniq⟩,
      hm1⟩
  · rintro ⟨⟨p, j, hp, hpo, rfl⟩, h1⟩
    have hj : j ≠ 0 := by
      rintro rfl
      exact h1 (pow_zero p)
    have hpj : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
    refine ⟨Nat.pos_of_ne_zero hpj, p,
      ⟨Nat.mem_divisors.2 ⟨dvd_pow_self p hj, hpj⟩, hpo, Or.inr hp, ?_⟩, ?_⟩
    · intro e he _ hnc
      rcases hnc with rfl | hep
      · exact hp.one_lt.le
      · exact Nat.le_of_dvd hp.pos (hep.dvd_of_dvd_pow (Nat.dvd_of_mem_divisors he))
    · have : (p ^ j).divisors.filter (· < p) = {1} := by
        ext e
        rw [Finset.mem_filter, Finset.mem_singleton, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdv, _⟩, hlt⟩
          obtain ⟨i, _, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdv
          rcases Nat.eq_zero_or_pos i with rfl | hi
          · rfl
          · exact absurd hlt (not_lt.2 (by
              calc p = p ^ 1 := (pow_one p).symm
                _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi))
        · rintro rfl
          exact ⟨⟨one_dvd _, hpj⟩, hp.one_lt⟩
      rw [this, Finset.card_singleton]

lemma one_mem : IsOddPrimePower 1 := ⟨3, 0, Nat.prime_three, by decide, rfl⟩

lemma infinite : {m | hasProperty 2 m}.Infinite := by
  have hinj : Function.Injective (fun i : ℕ => 3 ^ (i + 1)) := by
    intro a b h
    have := Nat.pow_right_injective (le_refl 2) (show 2 ^ (a+1) = 2 ^ (b+1) from by
      have h' : 3 ^ (a+1) = 3 ^ (b+1) := h
      have := Nat.pow_right_injective (show 2 ≤ 3 by norm_num) h'
      rw [this])
    omega
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro i
  show hasProperty 2 (3 ^ (i+1))
  rw [char]
  exact ⟨⟨3, i+1, Nat.prime_three, by decide, rfl⟩,
    (Nat.one_lt_pow (Nat.succ_ne_zero i) (by norm_num)).ne'⟩

open Classical in
lemma count_eq (x : ℕ) (hx : 1 < x) :
    Nat.count IsOddPrimePower x = Nat.count (hasProperty 2) x + 1 := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  have : (Finset.range x).filter IsOddPrimePower =
      insert 1 ((Finset.range x).filter (hasProperty 2)) := by
    ext e
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, char]
    by_cases he : e = 1
    · subst he
      simp only [true_or, iff_true]
      exact ⟨hx, one_mem⟩
    · simp only [he, false_or, ne_eq, not_false_eq_true, and_true]
  rw [this, Finset.card_insert_of_notMem]
  rw [Finset.mem_filter, char]
  simp

end OMA.P_a384233

open Classical in
theorem OMA.solution : type_of% @OMA.S_oeis_a384233.main := by
  intro n hn
  unfold OMA.S_oeis_a384233.T OMA.S_oeis_a384233.A061345
  have hinf := OMA.P_a384233.infinite
  have hx := Nat.nth_mem_of_infinite hinf (n-1)
  have hcx := Nat.count_nth_of_infinite hinf (n-1)
  have hQ := (OMA.P_a384233.char _).1 hx
  have hc := OMA.P_a384233.count_eq _ (lt_of_le_of_ne hx.1 (Ne.symm hQ.2))
  rw [hcx, show n - 1 + 1 = n by omega] at hc
  have := Nat.nth_count hQ.1
  rw [hc] at this
  exact this.symm
