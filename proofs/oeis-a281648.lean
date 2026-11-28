import OMAStatements.S_oeis_a281648

namespace OMA.S_oeis_a281648

open Finset


/-- The conjecture as stated (a(n) is already reduced mod n). -/
def Conjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → (a n = (n : ℤ) - 1 ↔ (n = 6 ∨ n = 10 ∨ ∃ k : ℕ, n = 2 ^ k))

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-! ### The 3-adic size of Bernoulli numbers -/

lemma pn_one_div_prime {q : ℕ} (hq : q.Prime) : padicNorm 3 (1 / (q : ℚ)) ≤ 3 := by
  rw [padicNorm.div, padicNorm.one]
  by_cases h : q = 3
  · subst h
    rw [padicNorm.padicNorm_p_of_prime]
    norm_num
  · haveI := Fact.mk hq
    rw [padicNorm.padicNorm_of_prime_of_ne (Ne.symm h)]
    norm_num

/-- |B_i|_3 <= 3 for every i, from von Staudt-Clausen. -/
lemma pn_bernoulli (i : ℕ) : padicNorm 3 (bernoulli i) ≤ 3 := by
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | hodd
  · have hk2 : i = 2 * k := by omega
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    have hB : bernoulli i = (z : ℚ) - ∑ p ∈ range (2 * k + 2) with p.Prime ∧ (p - 1) ∣ 2 * k,
        (1 : ℚ) / p := by
      rw [hk2, hz]; ring
    rw [hB]
    refine le_trans padicNorm.sub (max_le ?_ ?_)
    · exact le_trans (padicNorm.of_int z) (by norm_num)
    · exact padicNorm.sum_le' (fun p hp => pn_one_div_prime (mem_filter.mp hp).2.1) (by norm_num)
  · rcases (show i = 1 ∨ 1 < i by obtain ⟨j, hj⟩ := hodd; omega) with h1 | hlt
    · subst h1
      rw [bernoulli_one, padicNorm.div, padicNorm.neg, padicNorm.one]
      have h2 : padicNorm 3 (2 : ℚ) = 1 := by
        have := (padicNorm.nat_eq_one_iff (p := 3) 2).mpr (by norm_num)
        exact_mod_cast this
      rw [h2]; norm_num
    · rw [bernoulli_eq_zero_of_odd hodd hlt, padicNorm.zero]; norm_num

/-! ### Faulhaber with nine terms -/

/-- The Faulhaber summand for the power sum of k^6660 over k < 9. -/
noncomputable def f (i : ℕ) : ℚ :=
  bernoulli i * ((6660 + 1).choose i) * ((9 : ℕ) : ℚ) ^ (6660 + 1 - i) / (6660 + 1)

/-- The error term E: the Faulhaber summands with i < 6659. -/
noncomputable def E : ℚ := ∑ i ∈ range 6659, f i

lemma pn_pow (x : ℚ) (n : ℕ) : padicNorm 3 (x ^ n) = padicNorm 3 x ^ n := by
  induction n with
  | zero => simp [padicNorm.one]
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma pn_nine : padicNorm 3 ((9 : ℕ) : ℚ) = (1 / 9 : ℚ) := by
  have : ((9 : ℕ) : ℚ) = (3 : ℚ) ^ 2 := by norm_num
  rw [this, pn_pow]
  have h3 : padicNorm 3 (3 : ℚ) = 1 / 3 := by
    have := padicNorm.padicNorm_p_of_prime (p := 3)
    norm_num at this ⊢; exact this
  rw [h3]; norm_num

/-- The bound for a general exponent N with 3 not dividing N + 1, so that no numeral is
evaluated. -/
lemma pn_term (N i : ℕ) (hN : ¬ 3 ∣ N + 1) (hi : i + 3 ≤ N + 1) :
    padicNorm 3 (bernoulli i * ((N + 1).choose i) * ((9 : ℕ) : ℚ) ^ (N + 1 - i) / (N + 1))
      ≤ 1 / 243 := by
  have hN1 : padicNorm 3 ((N : ℚ) + 1) = 1 := by
    have := (padicNorm.nat_eq_one_iff (p := 3) (N + 1)).mpr hN
    exact_mod_cast this
  have hC : padicNorm 3 (((N + 1).choose i : ℕ) : ℚ) ≤ 1 := padicNorm.of_nat _
  rw [padicNorm.div, padicNorm.mul, padicNorm.mul, pn_pow, pn_nine, hN1, div_one]
  have hB := pn_bernoulli i
  have hpow : (1 / 9 : ℚ) ^ (N + 1 - i) ≤ (1 / 9 : ℚ) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h0 : 0 ≤ padicNorm 3 (bernoulli i) := padicNorm.nonneg _
  have h0' : 0 ≤ padicNorm 3 (((N + 1).choose i : ℕ) : ℚ) := padicNorm.nonneg _
  calc padicNorm 3 (bernoulli i) * padicNorm 3 (((N + 1).choose i : ℕ) : ℚ) *
        (1 / 9 : ℚ) ^ (N + 1 - i)
      ≤ 3 * 1 * (1 / 9 : ℚ) ^ 3 := by gcongr
    _ = 1 / 243 := by norm_num

lemma pn_f {i : ℕ} (hi : i < 6659) : padicNorm 3 (f i) ≤ 1 / 243 := by
  have h := pn_term 6660 i (by decide) (by omega)
  simpa [f] using h

lemma pn_E : padicNorm 3 E ≤ 1 / 243 :=
  padicNorm.sum_le' (fun i hi => pn_f (mem_range.mp hi)) (by norm_num)

/-- Faulhaber: 9 * B_6660 = sum_{k < 9} k^6660 - E. -/
lemma faulhaber : 9 * bernoulli 6660 = (∑ k ∈ range 9, ((k : ℕ) : ℚ) ^ 6660) - E := by
  have h := sum_range_pow 9 6660
  rw [h, sum_range_succ, sum_range_succ]
  have h59 : bernoulli 6659 = 0 := bernoulli_eq_zero_of_odd ⟨3329, by norm_num⟩ (by norm_num)
  have hch : ((6660 + 1).choose 6660 : ℚ) = 6661 := by
    rw [Nat.choose_succ_self_right]; norm_num
  rw [E]
  simp only [f, h59, zero_mul, zero_div, add_zero]
  rw [hch]
  norm_num
  ring

/-! ### The denominator primes of B_6660 -/

/-- The primes q with q - 1 | 6660. -/
def Q : Finset ℕ := {2, 3, 5, 7, 11, 13, 19, 31, 37, 61, 149, 181, 223, 2221, 3331, 6661}

lemma hQ : ((range (2 * 3330 + 2)).filter fun p => p.Prime ∧ (p - 1) ∣ 2 * 3330) = Q := by
  have h1 : ((range (2 * 3330 + 2)).filter fun p => p.Prime ∧ (p - 1) ∣ 2 * 3330) =
      ((range 6662).filter fun p => (p - 1) ∣ 6660).filter Nat.Prime := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p _
    exact and_comm
  have h2 : ((range 6662).filter fun p => (p - 1) ∣ 6660) =
      {2, 3, 4, 5, 6, 7, 10, 11, 13, 16, 19, 21, 31, 37, 38, 46, 61, 75, 91, 112, 149, 181, 186,
        223, 334, 371, 445, 556, 667, 741, 1111, 1333, 1666, 2221, 3331, 6661} := by
    decide +kernel
  rw [h1, h2]
  simp only [Finset.filter_insert, Finset.filter_singleton]
  norm_num
  decide

lemma mem_Q_prime {q : ℕ} (hq : q ∈ Q) : q.Prime := by
  simp only [Q, mem_insert, mem_singleton] at hq
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := hq <;> norm_num

/-- von Staudt-Clausen for B_6660 with the explicit prime set. -/
lemma vsc : ∃ I : ℤ, (I : ℚ) = bernoulli 6660 + ∑ q ∈ Q, (1 : ℚ) / q := by
  obtain ⟨I, hI⟩ := Bernoulli.vonStaudt_clausen 3330
  refine ⟨I, ?_⟩
  rw [hI, hQ]

/-! ### Numerator and denominator of B_6660 -/

/-- D, the product of the primes in Q. -/
def D : ℕ := ∏ q ∈ Q, q

lemma D_val : D = 11831355864185132466564202830 := by decide +kernel

lemma q_dvd_D {q : ℕ} (hq : q ∈ Q) : q ∣ D := Finset.dvd_prod_of_mem _ hq

/-- The candidate numerator D * I - sum_{q in Q} D/q. -/
def M (I : ℤ) : ℤ := (D : ℤ) * I - ∑ q ∈ Q, ((D / q : ℕ) : ℤ)

lemma B_eq (I : ℤ) (hI : (I : ℚ) = bernoulli 6660 + ∑ q ∈ Q, (1 : ℚ) / q) :
    bernoulli 6660 = ((M I : ℤ) : ℚ) / ((D : ℤ) : ℚ) := by
  have hD : (D : ℚ) ≠ 0 := by rw [D_val]; norm_num
  have hcast : ∀ q ∈ Q, (((D / q : ℕ) : ℤ) : ℚ) = (D : ℚ) * ((1 : ℚ) / q) := by
    intro q hq
    have hp := mem_Q_prime hq
    have : ((D / q : ℕ) : ℚ) = (D : ℚ) / q :=
      Nat.cast_div (q_dvd_D hq) (by exact_mod_cast hp.ne_zero)
    rw [Int.cast_natCast, this]; ring
  have hsum : ((∑ q ∈ Q, ((D / q : ℕ) : ℤ) : ℤ) : ℚ) = (D : ℚ) * ∑ q ∈ Q, (1 : ℚ) / q := by
    rw [Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hcast
  rw [eq_div_iff (by exact_mod_cast hD), M, Int.cast_sub, hsum, Int.cast_mul, Int.cast_natCast,
    hI]
  ring

lemma M_add_dvd (I : ℤ) {q : ℕ} (hq : q ∈ Q) : (q : ℤ) ∣ M I + ((D / q : ℕ) : ℤ) := by
  have key : ∀ q ∈ Q, (∑ q' ∈ Q.erase q, D / q') % q = 0 := by decide +kernel
  have h1 : (q : ℤ) ∣ (D : ℤ) * I := Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (q_dvd_D hq)) I
  have h2 : (q : ℤ) ∣ ∑ q' ∈ Q.erase q, ((D / q' : ℕ) : ℤ) := by
    have := Nat.dvd_of_mod_eq_zero (key q hq)
    have h' : (q : ℤ) ∣ ((∑ q' ∈ Q.erase q, D / q' : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr this
    push_cast at h'
    exact h'
  have e : M I + ((D / q : ℕ) : ℤ) = (D : ℤ) * I - ∑ q' ∈ Q.erase q, ((D / q' : ℕ) : ℤ) := by
    rw [M, ← Finset.add_sum_erase Q _ hq]
    ring
  rw [e]
  exact dvd_sub h1 h2

lemma not_dvd_M (I : ℤ) {q : ℕ} (hq : q ∈ Q) : ¬ (q : ℤ) ∣ M I := by
  intro h
  have key : ∀ q ∈ Q, (D / q) % q ≠ 0 := by decide +kernel
  have h2 : (q : ℤ) ∣ ((D / q : ℕ) : ℤ) := (dvd_add_right h).mp (M_add_dvd I hq)
  exact key q hq (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp h2))

lemma coprime_M (I : ℤ) : Nat.Coprime (M I).natAbs D := by
  rw [D]
  apply Nat.Coprime.prod_right
  intro q hq
  have hp := mem_Q_prime hq
  apply Nat.coprime_comm.mp
  apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
  intro h
  exact not_dvd_M I hq (Int.natCast_dvd.mpr h)

lemma num_eq (I : ℤ) (hI : (I : ℚ) = bernoulli 6660 + ∑ q ∈ Q, (1 : ℚ) / q) :
    (bernoulli 6660).num = M I := by
  rw [B_eq I hI]
  have hD0 : (0 : ℤ) < (D : ℤ) := by rw [D_val]; norm_num
  exact Rat.num_div_eq_of_coprime hD0 (by simpa using coprime_M I)

/-! ### Residues of the numerator -/

lemma dvd_M_add_one (I : ℤ) {q : ℕ} (hq : q ∈ Q) (h1 : (D / q) % q = 1) :
    (q : ℤ) ∣ M I + 1 := by
  have h := M_add_dvd I hq
  have hd : (q : ℤ) ∣ ((D / q : ℕ) : ℤ) - 1 := by
    have e := Nat.div_add_mod (D / q) q
    rw [h1] at e
    refine ⟨((D / q / q : ℕ) : ℤ), ?_⟩
    have e' : ((D / q : ℕ) : ℤ) = (q : ℤ) * ((D / q / q : ℕ) : ℤ) + 1 := by exact_mod_cast e.symm
    rw [e']; ring
  have e : M I + 1 = (M I + ((D / q : ℕ) : ℤ)) - (((D / q : ℕ) : ℤ) - 1) := by ring
  rw [e]
  exact dvd_sub h hd

/-- S = sum_{k < 9} k^6660. -/
def S : ℕ := ∑ k ∈ range 9, k ^ 6660

lemma S_cast : ((S : ℕ) : ℚ) = ∑ k ∈ range 9, ((k : ℕ) : ℚ) ^ 6660 := by
  rw [S, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun k _ => Nat.cast_pow k 6660)

lemma S_mod3 : S % 3 = 0 := by decide +kernel

lemma D_mod3 : D % 3 = 0 := by decide +kernel

lemma AT_mod9 : (D / 3 * (S / 3)) % 9 = 8 := by decide +kernel

lemma nine_dvd (I : ℤ) (hI : (I : ℚ) = bernoulli 6660 + ∑ q ∈ Q, (1 : ℚ) / q) :
    (9 : ℤ) ∣ M I + 1 := by
  have hB := B_eq I hI
  have hF := faulhaber
  have hS := S_cast
  have hnum := AT_mod9
  have hS3 := S_mod3
  have hD3 := D_mod3
  have hD0 : (D : ℚ) ≠ 0 := by rw [D_val]; norm_num
  generalize hA : D / 3 = A at hnum
  generalize hT : S / 3 = T at hnum
  have hDA : D = 3 * A := by omega
  have hST : S = 3 * T := by omega
  -- M = D * B and 9 B = S - E, so M - A T = -A E / 3
  have hM : ((M I : ℤ) : ℚ) = (D : ℚ) * bernoulli 6660 := by
    rw [hB, Int.cast_natCast]; field_simp
  have h9 : bernoulli 6660 = ((S : ℚ) - E) / 9 := by rw [hS]; linarith
  have hDq : (D : ℚ) = 3 * (A : ℚ) := by exact_mod_cast hDA
  have hSq : (S : ℚ) = 3 * (T : ℚ) := by exact_mod_cast hST
  have hx : ((M I - ((A * T : ℕ) : ℤ) : ℤ) : ℚ) = -((A : ℚ) * E) / 3 := by
    rw [Int.cast_sub, hM, Int.cast_natCast, Nat.cast_mul, h9, hDq, hSq]
    ring
  have h3 : padicNorm 3 (3 : ℚ) = 1 / 3 := by
    have := padicNorm.padicNorm_p_of_prime (p := 3)
    norm_num at this ⊢; exact this
  have hpn : padicNorm 3 (((M I - ((A * T : ℕ) : ℤ) : ℤ) : ℚ)) ≤ (3 : ℚ) ^ (-(4 : ℤ)) := by
    rw [hx, padicNorm.div, padicNorm.neg, padicNorm.mul, h3]
    have hAn : padicNorm 3 (A : ℚ) ≤ 1 := padicNorm.of_nat _
    have hE := pn_E
    have h0 : 0 ≤ padicNorm 3 (A : ℚ) := padicNorm.nonneg _
    have h0' : 0 ≤ padicNorm 3 E := padicNorm.nonneg _
    generalize padicNorm 3 E = e at hE h0' ⊢
    generalize padicNorm 3 (A : ℚ) = u at hAn h0 ⊢
    calc u * e / (1 / 3) ≤ 1 * (1 / 243) / (1 / 3) := by gcongr
      _ = (3 : ℚ) ^ (-(4 : ℤ)) := by norm_num
  have h81 : ((3 ^ 4 : ℕ) : ℤ) ∣ M I - ((A * T : ℕ) : ℤ) :=
    (padicNorm.dvd_iff_norm_le (p := 3)).mpr (by exact_mod_cast hpn)
  generalize A * T = X at hnum h81
  push_cast at h81
  omega

/-! ### The value a(3330) and the disproof -/

lemma res2 : (D / 2) % 2 = 1 := by rw [D_val]

lemma res5 : (D / 5) % 5 = 1 := by rw [D_val]

lemma res37 : (D / 37) % 37 = 1 := by rw [D_val]

lemma mem2 : 2 ∈ Q := by simp [Q]

lemma mem5 : 5 ∈ Q := by simp [Q]

lemma mem37 : 37 ∈ Q := by simp [Q]

lemma M_mod (I : ℤ) (hI : (I : ℚ) = bernoulli 6660 + ∑ q ∈ Q, (1 : ℚ) / q) :
    M I % 3330 = 3329 := by
  have h2 := dvd_M_add_one I mem2 res2
  have h5 := dvd_M_add_one I mem5 res5
  have h37 := dvd_M_add_one I mem37 res37
  have h9 := nine_dvd I hI
  push_cast at h2 h5 h37
  generalize M I = m at h2 h5 h37 h9 ⊢
  omega

lemma num_mod : (bernoulli 6660).num % 3330 = 3329 := by
  obtain ⟨I, hI⟩ := vsc
  rw [num_eq I hI]
  exact M_mod I hI

theorem a_3330 : a 3330 = 3329 := by
  have e : a 3330 = (bernoulli 6660).num % 3330 := rfl
  rw [e]
  exact num_mod

/-- The conjecture of the entry is false: a(3330) = 3329 = 3330 - 1, but 3330 is not 6, 10 or a
power of 2. -/
theorem disproof : ¬ Conjecture := by
  intro h
  have hk := (h 3330 (by norm_num)).mp (by rw [a_3330]; norm_num)
  rcases hk with h6 | h10 | ⟨k, hk⟩
  · norm_num at h6
  · norm_num at h10
  · have h5 : (5 : ℕ) ∣ 2 ^ k := hk ▸ (by norm_num)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
    norm_num at this

end OMA.S_oeis_a281648

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a281648.main) :=
  OMA.S_oeis_a281648.disproof
