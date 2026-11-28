import OMAStatements.S_oeis_a233579

namespace OMA.S_oeis_a233579

open Finset

/-- The von Staudt-Clausen primes of B_2k: primes p < 2k + 2 with p - 1 | 2k. -/
def Qs (k : ℕ) : Finset ℕ := (range (2 * k + 2)).filter fun p => p.Prime ∧ (p - 1) ∣ 2 * k

lemma prime_of_mem {k p : ℕ} (h : p ∈ Qs k) : p.Prime := (mem_filter.mp h).2.1

lemma mem_Qs_of {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hd : (p - 1) ∣ 2 * k) : p ∈ Qs k := by
  refine mem_filter.mpr ⟨mem_range.mpr ?_, hp, hd⟩
  have := Nat.le_of_dvd (by omega) hd
  omega

/-- The product of the von Staudt-Clausen primes. -/
def Dk (k : ℕ) : ℕ := ∏ p ∈ Qs k, p

/-- D / q, as the product of the other primes. -/
def cof (k q : ℕ) : ℕ := ∏ p ∈ (Qs k).erase q, p

lemma mul_cof {k q : ℕ} (hq : q ∈ Qs k) : q * cof k q = Dk k :=
  Finset.mul_prod_erase (Qs k) (fun p => p) hq

lemma Dk_pos (k : ℕ) : 0 < Dk k := Finset.prod_pos (fun p hp => (prime_of_mem hp).pos)

lemma vsc (k : ℕ) : ∃ I : ℤ, (I : ℚ) = bernoulli (2 * k) + ∑ p ∈ Qs k, (1 : ℚ) / p :=
  Bernoulli.vonStaudt_clausen k

/-- The numerator candidate D*I - sum_q D/q. -/
def M (k : ℕ) (I : ℤ) : ℤ := (Dk k : ℤ) * I - ∑ q ∈ Qs k, (cof k q : ℤ)

lemma B_eq (k : ℕ) (I : ℤ) (hI : (I : ℚ) = bernoulli (2 * k) + ∑ p ∈ Qs k, (1 : ℚ) / p) :
    bernoulli (2 * k) = ((M k I : ℤ) : ℚ) / ((Dk k : ℤ) : ℚ) := by
  have hD : (Dk k : ℚ) ≠ 0 := by exact_mod_cast (Dk_pos k).ne'
  have hcast : ∀ q ∈ Qs k, ((cof k q : ℤ) : ℚ) = (Dk k : ℚ) * ((1 : ℚ) / q) := by
    intro q hq
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (prime_of_mem hq).ne_zero
    rw [Int.cast_natCast, ← mul_cof hq, Nat.cast_mul]
    field_simp
  have hsum : ((∑ q ∈ Qs k, (cof k q : ℤ) : ℤ) : ℚ) = (Dk k : ℚ) * ∑ q ∈ Qs k, (1 : ℚ) / q := by
    rw [Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hcast
  rw [Int.cast_natCast, eq_div_iff hD, M, Int.cast_sub, hsum, Int.cast_mul, Int.cast_natCast, hI]
  ring

lemma dvd_M_add_cof {k q : ℕ} (I : ℤ) (hq : q ∈ Qs k) : (q : ℤ) ∣ M k I + cof k q := by
  have h1 : (q : ℤ) ∣ (Dk k : ℤ) * I :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr ⟨cof k q, (mul_cof hq).symm⟩) I
  have h2 : (q : ℤ) ∣ ∑ q' ∈ (Qs k).erase q, (cof k q' : ℤ) := by
    apply Finset.dvd_sum
    intro q' hq'
    have hne : q' ≠ q := (mem_erase.mp hq').1
    have hmem : q ∈ (Qs k).erase q' := mem_erase.mpr ⟨Ne.symm hne, hq⟩
    exact Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem (fun p => p) hmem)
  have e : M k I + cof k q = (Dk k : ℤ) * I - ∑ q' ∈ (Qs k).erase q, (cof k q' : ℤ) := by
    rw [M, ← Finset.add_sum_erase (Qs k) _ hq]
    ring
  rw [e]
  exact dvd_sub h1 h2

lemma not_dvd_cof {k q : ℕ} (hq : q ∈ Qs k) : ¬ q ∣ cof k q := by
  intro h
  have hp := prime_of_mem hq
  obtain ⟨p, hp', hdvd⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp h
  have hne : p ≠ q := (mem_erase.mp hp').1
  have hpp : p.Prime := prime_of_mem (mem_erase.mp hp').2
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hpp).mp hdvd).symm

lemma not_dvd_M {k q : ℕ} (I : ℤ) (hq : q ∈ Qs k) : ¬ (q : ℤ) ∣ M k I := by
  intro h
  have h2 : (q : ℤ) ∣ (cof k q : ℤ) := (dvd_add_right h).mp (dvd_M_add_cof I hq)
  exact not_dvd_cof hq (Int.natCast_dvd_natCast.mp h2)

lemma coprime_M (k : ℕ) (I : ℤ) : Nat.Coprime (M k I).natAbs (Dk k) := by
  apply Nat.Coprime.prod_right
  intro q hq
  apply Nat.coprime_comm.mp
  apply (Nat.Prime.coprime_iff_not_dvd (prime_of_mem hq)).mpr
  intro h
  exact not_dvd_M I hq (Int.natCast_dvd.mpr h)

lemma num_eq (k : ℕ) (I : ℤ) (hI : (I : ℚ) = bernoulli (2 * k) + ∑ p ∈ Qs k, (1 : ℚ) / p) :
    (bernoulli (2 * k)).num = M k I := by
  rw [B_eq k I hI]
  exact Rat.num_div_eq_of_coprime (by exact_mod_cast Dk_pos k) (by simpa using coprime_M k I)

lemma den_eq (k : ℕ) (I : ℤ) (hI : (I : ℚ) = bernoulli (2 * k) + ∑ p ∈ Qs k, (1 : ℚ) / p) :
    (bernoulli (2 * k)).den = Dk k := by
  have h := Rat.den_div_eq_of_coprime (a := M k I) (b := (Dk k : ℤ))
    (by exact_mod_cast Dk_pos k) (by simpa using coprime_M k I)
  rw [B_eq k I hI]
  exact_mod_cast h

/-! ### The primes 2, 3 and 5 -/

lemma two_mem {k : ℕ} (hk : 1 ≤ k) : 2 ∈ Qs k :=
  mem_Qs_of hk Nat.prime_two (by norm_num)

lemma three_mem {k : ℕ} (hk : 1 ≤ k) : 3 ∈ Qs k :=
  mem_Qs_of hk Nat.prime_three (by norm_num)

lemma five_mem_iff {k : ℕ} (hk : 1 ≤ k) : 5 ∈ Qs k ↔ 2 ∣ k := by
  constructor
  · intro h
    have hd := (mem_filter.mp h).2.2
    norm_num at hd
    omega
  · intro h
    apply mem_Qs_of hk (by norm_num)
    norm_num
    omega

/-- E = D / 6, the product of the von Staudt-Clausen primes other than 2 and 3. -/
def E (k : ℕ) : ℕ := ∏ p ∈ ((Qs k).erase 2).erase 3, p

lemma cof_two {k : ℕ} (hk : 1 ≤ k) : cof k 2 = 3 * E k := by
  have h3 : 3 ∈ (Qs k).erase 2 := mem_erase.mpr ⟨by norm_num, three_mem hk⟩
  rw [cof, ← Finset.mul_prod_erase ((Qs k).erase 2) (fun p => p) h3]
  rfl

lemma cof_three {k : ℕ} (hk : 1 ≤ k) : cof k 3 = 2 * E k := by
  have h2 : 2 ∈ (Qs k).erase 3 := mem_erase.mpr ⟨by norm_num, two_mem hk⟩
  rw [cof, ← Finset.mul_prod_erase ((Qs k).erase 3) (fun p => p) h2, Finset.erase_right_comm]
  rfl

lemma Dk_eq {k : ℕ} (hk : 1 ≤ k) : Dk k = 6 * E k := by
  rw [← mul_cof (two_mem hk), cof_two hk]
  ring

lemma prime_dvd_E {k r : ℕ} (hr : r.Prime) (h : r ∣ E k) : r ∈ ((Qs k).erase 2).erase 3 := by
  obtain ⟨p, hp', hdvd⟩ := (Prime.dvd_finset_prod_iff hr.prime _).mp h
  have hpQ : p ∈ Qs k := (mem_erase.mp (mem_erase.mp hp').2).2
  have := (Nat.prime_dvd_prime_iff_eq hr (prime_of_mem hpQ)).mp hdvd
  rw [this]
  exact hp'

lemma E_odd (k : ℕ) : ¬ 2 ∣ E k := by
  intro h
  have := prime_dvd_E Nat.prime_two h
  simp at this

lemma E_not_three (k : ℕ) : ¬ 3 ∣ E k := by
  intro h
  have := prime_dvd_E Nat.prime_three h
  simp at this

lemma five_dvd_E_iff {k : ℕ} (hk : 1 ≤ k) : 5 ∣ E k ↔ 2 ∣ k := by
  rw [← five_mem_iff hk]
  constructor
  · intro h
    exact (mem_erase.mp (mem_erase.mp (prime_dvd_E (by norm_num) h)).2).2
  · intro h
    exact Finset.dvd_prod_of_mem (fun p => p)
      (mem_erase.mpr ⟨by norm_num, mem_erase.mpr ⟨by norm_num, h⟩⟩)

/-! ### The sign of B_2k -/

lemma bern_sign (k : ℕ) (hk : k ≠ 0) : 0 < (-1 : ℚ) ^ (k + 1) * bernoulli (2 * k) := by
  have h := hasSum_zeta_nat hk
  have hpos := h.summable.tsum_pos (fun n => by positivity) 1 (by norm_num)
  rw [h.tsum_eq] at hpos
  have hc : 0 < (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    positivity
  have e : (-1 : ℝ) ^ (k + 1) * 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) *
      ((bernoulli (2 * k) : ℚ) : ℝ) / ((2 * k).factorial : ℝ) =
      ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ)) *
        ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
    ring
  rw [e] at hpos
  have h' : 0 < (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ) :=
    (pos_iff_pos_of_mul_pos hpos).mpr hc
  exact_mod_cast h'

/-! ### The theorem -/

/-- The residue statement on integers, by cases on the sign. -/
lemma arith (m : ℤ) (e : ℕ) (h2 : (2 : ℤ) ∣ m + 3 * e) (h3 : (3 : ℤ) ∣ m + 2 * e)
    (he2 : ¬ 2 ∣ e) (he3 : ¬ 3 ∣ e) (s : Prop)
    (hpos : ¬ s → 0 < m ∧ ¬ 5 ∣ e) (hneg : s → m < 0 ∧ 5 ∣ e) :
    m.natAbs % 6 = 5 ↔ e % 30 = 11 ∨ e % 30 = 17 ∨ e % 30 = 23 ∨ e % 30 = 25 ∨ e % 30 = 29 := by
  by_cases hs : s
  · obtain ⟨hm, h5⟩ := hneg hs
    have ht : (m.natAbs : ℤ) = -m := Int.ofNat_natAbs_of_nonpos hm.le
    generalize m.natAbs = t at ht ⊢
    constructor <;> intro h <;> omega
  · obtain ⟨hm, h5⟩ := hpos hs
    have ht : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm.le
    generalize m.natAbs = t at ht ⊢
    constructor <;> intro h <;> omega

/-- The conjecture of the entry, for every n. -/
theorem conjecture (n : ℕ) :
    (bernoulli n).num.natAbs % 6 = 5 ↔
      (bernoulli n).den / 6 % 30 ∈ ({11, 17, 23, 25, 29} : Finset ℕ) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with h0 | hk1
    · subst h0
      have : n = 0 := by omega
      subst this
      simp [bernoulli_zero]
    · have hn : n = 2 * k := by omega
      subst hn
      obtain ⟨I, hI⟩ := vsc k
      rw [num_eq k I hI, den_eq k I hI, Dk_eq hk1, Nat.mul_div_cancel_left _ (by norm_num)]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have h2 := dvd_M_add_cof I (two_mem hk1)
      have h3 := dvd_M_add_cof I (three_mem hk1)
      rw [cof_two hk1] at h2
      rw [cof_three hk1] at h3
      push_cast at h2 h3
      have hsign := bern_sign k (by omega)
      apply arith (M k I) (E k) h2 h3 (E_odd k) (E_not_three k) (2 ∣ k)
      · intro hk2
        refine ⟨?_, fun h5 => hk2 ((five_dvd_E_iff hk1).mp h5)⟩
        have hodd : Odd k := Nat.odd_iff.mpr (by omega)
        have : (-1 : ℚ) ^ (k + 1) = 1 := (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hodd)).neg_one_pow
        rw [this, one_mul] at hsign
        rw [← num_eq k I hI]
        exact Rat.num_pos.mpr hsign
      · intro hk2
        refine ⟨?_, (five_dvd_E_iff hk1).mpr hk2⟩
        have heven : Even k := (even_iff_two_dvd).mpr hk2
        have : (-1 : ℚ) ^ (k + 1) = -1 := (Even.add_one heven).neg_one_pow
        rw [this] at hsign
        rw [← num_eq k I hI]
        have hB : bernoulli (2 * k) < 0 := by linarith
        exact lt_of_not_ge (fun h => absurd (Rat.num_nonneg.mp h) (not_le.mpr hB))
  · rcases (show n = 1 ∨ 1 < n by obtain ⟨j, hj⟩ := hodd; omega) with h1 | hlt
    · subst h1
      rw [bernoulli_one]
      have hnum : ((-1 : ℚ) / 2).num = -1 := by
        have := Rat.num_div_eq_of_coprime (a := -1) (b := 2) (by norm_num) (by norm_num)
        exact_mod_cast this
      have hden : ((-1 : ℚ) / 2).den = 2 := by
        have := Rat.den_div_eq_of_coprime (a := -1) (b := 2) (by norm_num) (by norm_num)
        exact_mod_cast this
      rw [hnum, hden]
      decide
    · rw [bernoulli_eq_zero_of_odd hodd hlt]
      decide

/-- The entry's second claim, "the union of A233578 and A233579 is all even numbers >= 2"
(A233578: denominator/6 congruent to 1, 5, 7, 13 or 19 modulo 30): for every k >= 1 the
denominator of B_2k divided by 6 lies in one of the ten classes. -/
theorem union_claim (k : ℕ) (hk : 1 ≤ k) :
    (bernoulli (2 * k)).den / 6 % 30 ∈ ({1, 5, 7, 13, 19, 11, 17, 23, 25, 29} : Finset ℕ) := by
  obtain ⟨I, hI⟩ := vsc k
  rw [den_eq k I hI, Dk_eq hk, Nat.mul_div_cancel_left _ (by norm_num)]
  have h2 := E_odd k
  have h3 := E_not_three k
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

end OMA.S_oeis_a233579

theorem OMA.solution : type_of% @OMA.S_oeis_a233579.main :=
  fun n => (OMA.S_oeis_a233579.conjecture n).symm
