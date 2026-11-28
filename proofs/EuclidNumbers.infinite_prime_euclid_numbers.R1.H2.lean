import OMAReductions.R_EuclidNumbers_infinite_prime_euclid_numbers_R1
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
A Euclid number is never a proper power (Ligh and Neal, 1974). Reduce to a prime exponent q.
If q exceeds the largest prime used, size bounds give a contradiction. Otherwise q divides the
primorial exactly once, but Fermat forces q squared to divide b ^ q - 1.
-/

theorem OMA.solution : OMA.R_EuclidNumbers_infinite_prime_euclid_numbers_R1.H2 := by
  intro n a k hk he
  unfold EuclidNumbers.Euclid at he
  set P := ∏ i ∈ Finset.range n, i.nth Nat.Prime with hP
  have hq : k.minFac.Prime := Nat.minFac_prime (by omega)
  set q := k.minFac with hqdef
  set b := a ^ (k / q) with hbdef
  have hb : 1 + P = b ^ q := by
    rw [he, hbdef, ← pow_mul, Nat.div_mul_cancel (Nat.minFac_dvd k)]
  clear_value P q b
  have hq2 : 2 ≤ q := hq.two_le
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hP
    subst hP
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · interval_cases b
      · rw [zero_pow (by omega)] at hb; omega
      · rw [one_pow] at hb; omega
    · have : 2 ^ q ≤ b ^ q := Nat.pow_le_pow_left hb2 q
      have : 2 ^ 2 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq2
      omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hlist : ∀ r, r.Prime → r ≤ Nat.nth Nat.Prime m →
      Nat.count Nat.Prime r < m + 1 ∧ Nat.nth Nat.Prime (Nat.count Nat.Prime r) = r := by
    intro r hr hle
    have h1 := Nat.nth_count hr
    refine ⟨?_, h1⟩
    have : Nat.count Nat.Prime r ≤ m := by
      rw [← hmono.le_iff_le, h1]; exact hle
    omega
  have hdvdP : ∀ j, j < m + 1 → Nat.nth Nat.Prime j ∣ P := by
    intro j hj
    rw [hP]; exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)
  have hPpos : 0 < P := by
    rw [hP]; exact Finset.prod_pos (fun i _ => (Nat.prime_nth_prime i).pos)
  have hb2 : 2 ≤ b := by
    by_contra h
    push Not at h
    have : b ^ q ≤ 1 := by
      interval_cases b
      · rw [zero_pow (by omega)]; omega
      · rw [one_pow]
    omega
  have hrb : Nat.nth Nat.Prime m < b := by
    have hr := Nat.minFac_prime (show b ≠ 1 by omega)
    have hrdvd : b.minFac ∣ P + 1 := by
      rw [add_comm, hb]; exact dvd_pow (Nat.minFac_dvd b) (by omega)
    by_contra h
    push Not at h
    have hle : b.minFac ≤ Nat.nth Nat.Prime m := le_trans (Nat.minFac_le (by omega)) h
    obtain ⟨hc, he'⟩ := hlist _ hr hle
    have hd := hdvdP _ hc
    rw [he'] at hd
    have h1 : b.minFac ∣ 1 := (Nat.dvd_add_right hd).mp hrdvd
    exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
  have hPle : P ≤ (Nat.nth Nat.Prime m) ^ (m + 1) := by
    have := Finset.prod_le_pow_card (Finset.range (m + 1)) (fun i => Nat.nth Nat.Prime i)
      (Nat.nth Nat.Prime m) (fun i hi => hmono.monotone (by simp at hi; omega))
    rw [Finset.card_range] at this
    rw [hP]; exact this
  rcases Nat.lt_or_ge (Nat.nth Nat.Prime m) q with hqbig | hqsmall
  · exfalso
    have hm2 := Nat.add_two_le_nth_prime m
    have h1 : (Nat.nth Nat.Prime m) ^ (m + 1) < b ^ (m + 1) := Nat.pow_lt_pow_left hrb (by omega)
    have h2 : b ^ (m + 2) ≤ b ^ q := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : b ^ (m + 2) = b * b ^ (m + 1) := by ring
    have h4 : 2 * b ^ (m + 1) ≤ b * b ^ (m + 1) := Nat.mul_le_mul_right _ hb2
    have h5 : 0 < b ^ (m + 1) := by positivity
    linarith
  · obtain ⟨hj, hjq⟩ := hlist q hq hqsmall
    set j := Nat.count Nat.Prime q with hjdef
    clear_value j
    have hqP : q ∣ P := hjq ▸ hdvdP j hj
    have hnsq : ¬ q ^ 2 ∣ P := by
      intro hsq
      have hjmem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr hj
      have hsplit : Nat.nth Nat.Prime j *
          ∏ i ∈ (Finset.range (m + 1)).erase j, Nat.nth Nat.Prime i = P := by
        rw [hP]; exact Finset.mul_prod_erase _ (fun i => Nat.nth Nat.Prime i) hjmem
      rw [hjq] at hsplit
      rw [← hsplit, pow_two] at hsq
      have hd : q ∣ ∏ i ∈ (Finset.range (m + 1)).erase j, Nat.nth Nat.Prime i :=
        Nat.dvd_of_mul_dvd_mul_left hq.pos hsq
      obtain ⟨i, hi, hqi⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hd
      have hqi' : q = Nat.nth Nat.Prime i :=
        (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_nth_prime i)).mp hqi
      have hij : i = j := hmono.injective (by rw [← hqi', hjq])
      exact (Finset.mem_erase.mp hi).1 hij
    have := Fact.mk hq
    have hPz : (P : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff P q).mpr hqP
    have hbz : (b : ZMod q) = 1 := by
      have h1 : ((1 + P : ℕ) : ZMod q) = ((b ^ q : ℕ) : ZMod q) := by rw [hb]
      push_cast at h1
      rw [hPz, add_zero, ZMod.pow_card] at h1
      exact h1.symm
    have hfac : ((P : ℕ) : ℤ) = (∑ i ∈ Finset.range q, (b : ℤ) ^ i) * ((b : ℤ) - 1) := by
      rw [geom_sum_mul]
      have h1 : ((1 + P : ℕ) : ℤ) = ((b ^ q : ℕ) : ℤ) := by rw [hb]
      push_cast at h1
      linarith
    have hd1 : (q : ℤ) ∣ (b : ℤ) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hbz, sub_self]
    have hd2 : (q : ℤ) ∣ ∑ i ∈ Finset.range q, (b : ℤ) ^ i := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hbz]
      simp
    apply hnsq
    have h2 : ((q ^ 2 : ℕ) : ℤ) ∣ ((P : ℕ) : ℤ) := by
      rw [hfac]; push_cast; rw [pow_two]; exact mul_dvd_mul hd2 hd1
    exact Int.natCast_dvd_natCast.mp h2
