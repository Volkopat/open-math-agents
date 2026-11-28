import OMAStatements.S_oeis_a233578

namespace OMA.S_oeis_a233578

open Finset


/-- The primes of the von Staudt-Clausen sum for B_{2k}. -/
def S (k : ℕ) : Finset ℕ := (range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)

def D (k : ℕ) : ℕ := ∏ p ∈ S k, p

def T (k : ℕ) : ℕ := ∑ q ∈ S k, ∏ r ∈ (S k).erase q, r

theorem mem_S {k p : ℕ} : p ∈ S k ↔ p < 2 * k + 2 ∧ p.Prime ∧ (p - 1) ∣ 2 * k := by
  simp [S]

theorem prime_of_mem {k p : ℕ} (h : p ∈ S k) : p.Prime := (mem_S.mp h).2.1

theorem D_pos (k : ℕ) : 0 < D k :=
  Finset.prod_pos (fun p hp => (prime_of_mem hp).pos)

theorem vsc (k : ℕ) : ∃ I : ℤ, bernoulli (2 * k) = I - ∑ p ∈ S k, (1 : ℚ) / p := by
  obtain ⟨I, hI⟩ := Bernoulli.vonStaudt_clausen k
  exact ⟨I, by rw [hI]; simp [S]⟩

theorem prod_erase_eq {s : Finset ℕ} {a : ℕ} (h : a ∈ s) :
    ∏ x ∈ s, x = a * ∏ x ∈ s.erase a, x :=
  (Finset.mul_prod_erase s (fun x => x) h).symm

theorem sum_inv (k : ℕ) : ∑ p ∈ S k, (1 : ℚ) / p = (T k : ℚ) / D k := by
  rw [T, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (prime_of_mem hp).ne_zero
  have hne : ∏ r ∈ (S k).erase p, (r : ℚ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r hr => by
      exact_mod_cast (prime_of_mem (Finset.mem_of_mem_erase hr)).ne_zero)
  have e : (D k : ℚ) = p * ∏ r ∈ (S k).erase p, (r : ℚ) := by
    rw [D, prod_erase_eq hp]
    push_cast
    rfl
  rw [Nat.cast_prod, e, eq_div_iff (mul_ne_zero hp0 hne), one_div, ← mul_assoc,
    inv_mul_cancel₀ hp0, one_mul]

theorem not_dvd_erase {k p : ℕ} (hp : p ∈ S k) : ¬ p ∣ ∏ r ∈ (S k).erase p, r := by
  intro h
  obtain ⟨r, hr, hpr⟩ := ((prime_of_mem hp).prime.dvd_finset_prod_iff _).mp h
  have hr' := Finset.mem_of_mem_erase hr
  have hne := Finset.ne_of_mem_erase hr
  exact hne ((Nat.prime_dvd_prime_iff_eq (prime_of_mem hp) (prime_of_mem hr')).mp hpr).symm

theorem T_mod {k p : ℕ} (hp : p ∈ S k) : p ∣ T k - ∏ r ∈ (S k).erase p, r ∧
    ∏ r ∈ (S k).erase p, r ≤ T k := by
  rw [T, ← Finset.add_sum_erase (S k) _ hp]
  refine ⟨?_, Nat.le_add_right _ _⟩
  rw [Nat.add_sub_cancel_left]
  apply Finset.dvd_sum
  intro q hq
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_erase.mpr ⟨fun h => Finset.ne_of_mem_erase hq h.symm, hp⟩

theorem not_dvd_N {k : ℕ} (I : ℤ) {p : ℕ} (hp : p ∈ S k) : ¬ (p : ℤ) ∣ I * D k - T k := by
  intro h
  have hD : (p : ℤ) ∣ I * D k := by
    apply Dvd.dvd.mul_left
    exact_mod_cast Finset.dvd_prod_of_mem _ hp
  have hT : (p : ℤ) ∣ (T k : ℤ) := by
    have := dvd_sub hD h
    simpa using this
  have hT' : p ∣ T k := by exact_mod_cast hT
  obtain ⟨h1, h2⟩ := T_mod hp
  have : p ∣ ∏ r ∈ (S k).erase p, r := by
    have := Nat.dvd_sub hT' h1
    rwa [Nat.sub_sub_self h2] at this
  exact not_dvd_erase hp this

theorem coprime_N (k : ℕ) (I : ℤ) : Nat.Coprime (I * D k - T k).natAbs (D k) := by
  rw [D]
  apply Nat.Coprime.prod_right
  intro p hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (prime_of_mem hp)]
  intro h
  exact not_dvd_N I hp (Int.ofNat_dvd_left.mpr h)

theorem num_den (k : ℕ) : ∃ I : ℤ, (bernoulli (2 * k)).num = I * D k - T k ∧
    (bernoulli (2 * k)).den = D k := by
  obtain ⟨I, hI⟩ := vsc k
  have hD : (0 : ℤ) < (D k : ℤ) := by exact_mod_cast D_pos k
  have hB : bernoulli (2 * k) = ((I * D k - T k : ℤ) : ℚ) / ((D k : ℤ) : ℚ) := by
    rw [hI, sum_inv]
    have : (D k : ℚ) ≠ 0 := by exact_mod_cast (D_pos k).ne'
    push_cast
    field_simp
  have hc : Nat.Coprime (I * D k - T k).natAbs (D k : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    exact coprime_N k I
  refine ⟨I, ?_, ?_⟩
  · rw [hB]
    exact Rat.num_div_eq_of_coprime hD hc
  · rw [hB]
    exact_mod_cast Rat.den_div_eq_of_coprime hD hc

/-- E = D / 6, the product of the primes >= 5 of S. -/
def E (k : ℕ) : ℕ := ∏ r ∈ ((S k).erase 2).erase 3, r

theorem two_mem {k : ℕ} (hk : 1 ≤ k) : 2 ∈ S k := mem_S.mpr ⟨by omega, Nat.prime_two, by simp⟩

theorem three_mem {k : ℕ} (hk : 1 ≤ k) : 3 ∈ S k :=
  mem_S.mpr ⟨by omega, Nat.prime_three, ⟨k, by omega⟩⟩

theorem D_eq {k : ℕ} (hk : 1 ≤ k) : D k = 6 * E k := by
  have h3 : 3 ∈ (S k).erase 2 := Finset.mem_erase.mpr ⟨by norm_num, three_mem hk⟩
  rw [D, prod_erase_eq (two_mem hk), prod_erase_eq h3, E]
  ring

theorem E_not_dvd {k q : ℕ} (hq : q.Prime) (hq2 : q = 2 ∨ q = 3) : ¬ q ∣ E k := by
  intro h
  obtain ⟨r, hr, hqr⟩ := (hq.prime.dvd_finset_prod_iff _).mp h
  have hr1 := Finset.ne_of_mem_erase hr
  have hr2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
  have hrS := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
  have := (Nat.prime_dvd_prime_iff_eq hq (prime_of_mem hrS)).mp hqr
  rcases hq2 with rfl | rfl <;> omega

theorem five_dvd_E {k : ℕ} (hk : 1 ≤ k) : 5 ∣ E k ↔ k % 2 = 0 := by
  constructor
  · intro h
    obtain ⟨r, hr, h5r⟩ := (Nat.prime_five.prime.dvd_finset_prod_iff _).mp h
    have hrS := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
    have hr5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five (prime_of_mem hrS)).mp h5r
    subst hr5
    obtain ⟨-, -, h4⟩ := mem_S.mp hrS
    omega
  · intro h
    apply Finset.dvd_prod_of_mem
    refine Finset.mem_erase.mpr ⟨by norm_num, Finset.mem_erase.mpr ⟨by norm_num, ?_⟩⟩
    exact mem_S.mpr ⟨by omega, Nat.prime_five, ⟨k / 2, by omega⟩⟩

/-- T is E mod 3 times 2 and 3E mod 2, through the terms D/3 = 2E and D/2 = 3E. -/
theorem T_mod3 {k : ℕ} (hk : 1 ≤ k) : 3 ∣ T k - 2 * E k ∧ 2 * E k ≤ T k := by
  have h := T_mod (three_mem hk)
  have h2 : 2 ∈ (S k).erase 3 := Finset.mem_erase.mpr ⟨by norm_num, two_mem hk⟩
  have e : ∏ r ∈ (S k).erase 3, r = 2 * E k := by
    rw [prod_erase_eq h2, E, Finset.erase_right_comm]
  rwa [e] at h

theorem T_mod2 {k : ℕ} (hk : 1 ≤ k) : 2 ∣ T k - 3 * E k ∧ 3 * E k ≤ T k := by
  have h := T_mod (two_mem hk)
  have h3 : 3 ∈ (S k).erase 2 := Finset.mem_erase.mpr ⟨by norm_num, three_mem hk⟩
  have e : ∏ r ∈ (S k).erase 2, r = 3 * E k := by
    rw [prod_erase_eq h3, E]
  rwa [e] at h

/-- The sign of B_{2k}: (-1)^(k+1) B_{2k} > 0, from Mathlib's value of zeta(2k). -/
theorem sign (k : ℕ) (hk : 1 ≤ k) : 0 < (-1 : ℚ) ^ (k + 1) * bernoulli (2 * k) := by
  have h := hasSum_zeta_nat (k := k) (by omega)
  have hle := le_hasSum h 1 (fun j _ => by positivity)
  simp only [Nat.cast_one, one_pow, div_one] at hle
  have hc : (0 : ℝ) < (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((2 * k).factorial : ℝ) := by
    positivity
  have e : (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) *
      ((bernoulli (2 * k) : ℚ) : ℝ) / ((2 * k).factorial : ℝ) =
      ((-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ)) *
        ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((2 * k).factorial : ℝ)) := by ring
  rw [e] at hle
  have key : (0 : ℝ) < (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ) :=
    pos_of_mul_pos_left (by linarith) hc.le
  have key' : (0 : ℝ) < (((-1 : ℚ) ^ (k + 1) * bernoulli (2 * k) : ℚ) : ℝ) := by
    push_cast
    exact key
  exact_mod_cast key'

/-- Control: the entry's example, the denominator of Bernoulli(100) is 33330. -/
theorem control_den100 : (bernoulli 100).den = 33330 := by
  obtain ⟨I, -, h⟩ := num_den 50
  rw [show (100 : ℕ) = 2 * 50 by norm_num, h]
  decide +kernel

/-- The conjecture of the entry. -/
theorem conjecture (n : ℕ) (hn : 2 ≤ n) :
    InSeq n ↔ (bernoulli n).num.natAbs % 6 = 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · have hk1 : 1 ≤ k := by omega
    rw [show n = 2 * k by omega]
    obtain ⟨I, hnum, hden⟩ := num_den k
    have hD := D_eq hk1
    unfold InSeq
    rw [hden, hD, hnum]
    have hdiv : 6 * E k / 6 = E k := by omega
    rw [hdiv]
    have hE2 := E_not_dvd (k := k) Nat.prime_two (Or.inl rfl)
    have hE3 := E_not_dvd (k := k) Nat.prime_three (Or.inr rfl)
    have hE5 := five_dvd_E hk1
    obtain ⟨t3, ht3⟩ := T_mod3 hk1
    obtain ⟨t2, ht2⟩ := T_mod2 hk1
    have hs := sign k hk1
    obtain ⟨I', hnum'⟩ := (⟨I, hnum⟩ : ∃ I, (bernoulli (2 * k)).num = I * D k - T k)
    -- the sign of the numerator
    have hsg : (k % 2 = 1 → 0 < I * D k - T k) ∧ (k % 2 = 0 → I * D k - T k < 0) := by
      have hnumpos : ∀ q : ℚ, 0 < q ↔ 0 < q.num := fun q => Rat.num_pos.symm
      constructor
      · intro hodd'
        have : (-1 : ℚ) ^ (k + 1) = 1 := by
          rw [show k + 1 = 2 * (k / 2 + 1) by omega, pow_mul]; norm_num
        rw [this, one_mul] at hs
        rw [← hnum]
        exact Rat.num_pos.mpr hs
      · intro heven
        have : (-1 : ℚ) ^ (k + 1) = -1 := by
          rw [show k + 1 = 2 * (k / 2) + 1 by omega, pow_succ, pow_mul]; norm_num
        rw [this, neg_one_mul, neg_pos] at hs
        rw [← hnum]
        exact Rat.num_neg.mpr hs
    have hDk : (D k : ℤ) = 6 * E k := by exact_mod_cast hD
    rw [hDk]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have h3' : (3 : ℤ) ∣ (T k : ℤ) - 2 * E k := by
      have := Int.natCast_dvd_natCast.mpr t3
      push_cast [ht3] at this
      exact this
    have h2' : (2 : ℤ) ∣ (T k : ℤ) - 3 * E k := by
      have := Int.natCast_dvd_natCast.mpr t2
      push_cast [ht2] at this
      exact this
    rw [hDk] at hsg
    have hE2' : E k % 2 = 1 := by omega
    have hE3' : E k % 3 ≠ 0 := by omega
    have hA : (k % 2 = 1 → (((I * (6 * (E k : ℤ)) - (T k : ℤ)).natAbs : ℕ) : ℤ) =
        I * (6 * (E k : ℤ)) - (T k : ℤ)) ∧
        (k % 2 = 0 → (((I * (6 * (E k : ℤ)) - (T k : ℤ)).natAbs : ℕ) : ℤ) =
        -(I * (6 * (E k : ℤ)) - (T k : ℤ))) :=
      ⟨fun h => Int.natAbs_of_nonneg (hsg.1 h).le, fun h => Int.ofNat_natAbs_of_nonpos (hsg.2 h).le⟩
    have h6 : (6 : ℤ) ∣ I * (6 * (E k : ℤ)) := ⟨I * E k, by ring⟩
    generalize (I * (6 * (E k : ℤ)) - (T k : ℤ)).natAbs = A at hA ⊢
    generalize I * (6 * (E k : ℤ)) = X at hA h6
    omega
  · have hB : bernoulli n = 0 := bernoulli_eq_zero_of_odd hodd (by omega)
    unfold InSeq
    rw [hB]
    simp

/-- Membership in the companion A233579: "Numbers n such that the denominator/6 of Bernoulli(n)
is congruent to {11, 17, 23, 25 or 29} modulo 30." -/
def InSeq' (n : ℕ) : Prop :=
  6 ∣ (bernoulli n).den ∧ (bernoulli n).den / 6 % 30 ∈ ({11, 17, 23, 25, 29} : Finset ℕ)

end OMA.S_oeis_a233578

theorem OMA.solution : type_of% @OMA.S_oeis_a233578.main :=
  fun n hn => OMA.S_oeis_a233578.conjecture n hn
