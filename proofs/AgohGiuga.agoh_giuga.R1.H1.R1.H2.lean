import OMAReductions.R_AgohGiuga_agoh_giuga_R1_H1_R1
import Mathlib

namespace AGH2

/-- Sum of `l`-th powers of the nonzero residues mod a prime `p`. -/
lemma units_sum (p : ℕ) [Fact p.Prime] (l : ℕ) :
    (∑ v ∈ Finset.Ioo 0 p, (v : ZMod p) ^ l) = if (p - 1) ∣ l then -1 else 0 := by
  have hbij : (∑ v ∈ Finset.Ioo 0 p, (v : ZMod p) ^ l) = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ l :=
    Finset.sum_bij'
      (fun v hv => Units.mk0 (v : ZMod p) (mt (ZMod.natCast_eq_zero_iff v p).mp
        (Nat.not_dvd_of_pos_of_lt (Finset.mem_Ioo.mp hv).1 (Finset.mem_Ioo.mp hv).2)))
      (fun u _ => (u : ZMod p).val)
      (fun _ _ => Finset.mem_univ _)
      (fun u _ => Finset.mem_Ioo.mpr
        ⟨Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero), ZMod.val_lt _⟩)
      (fun v hv => by simp [ZMod.val_cast_of_lt (Finset.mem_Ioo.mp hv).2])
      (fun u _ => Units.ext (ZMod.natCast_zmod_val _))
      (fun _ _ => rfl)
  rw [hbij, FiniteField.sum_pow_units, ZMod.card]

lemma ioo_eq_range (p n m : ℕ) (hm : m ≠ 0) :
    (∑ i ∈ Finset.Ioo 0 n, (i : ZMod p) ^ m) = ∑ i ∈ Finset.range n, (i : ZMod p) ^ m := by
  apply Finset.sum_subset
  · intro x hx
    exact Finset.mem_range.mpr (Finset.mem_Ioo.mp hx).2
  · intro x hx hx'
    have hx0 : x = 0 := by
      by_contra h0
      exact hx' (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero h0, Finset.mem_range.mp hx⟩)
    rw [hx0, Nat.cast_zero, zero_pow hm]

lemma range_mul_sum (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m ≠ 0) (t : ℕ) :
    (∑ i ∈ Finset.range (p * t), (i : ZMod p) ^ m) =
      (t : ZMod p) * (if (p - 1) ∣ m then -1 else 0) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h : ∀ x ∈ Finset.range p, ((p * t + x : ℕ) : ZMod p) ^ m = (x : ZMod p) ^ m := by
      intro x _
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
    rw [Finset.sum_congr rfl h, ← ioo_eq_range p p m hm, units_sum p m]
    push_cast
    ring

/-- Lemma G: the power sum `∑_{0<i<n} i^m` modulo a prime `p ∣ n`. -/
lemma lemmaG (p : ℕ) [Fact p.Prime] (n m : ℕ) (hm : m ≠ 0) (hpn : p ∣ n) :
    ((∑ i ∈ Finset.Ioo 0 n, i ^ m : ℕ) : ZMod p) =
      ((n / p : ℕ) : ZMod p) * (if (p - 1) ∣ m then -1 else 0) := by
  obtain ⟨t, rfl⟩ := hpn
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [Nat.mul_div_cancel_left t hp, Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [ioo_eq_range p (p * t) m hm]
  exact range_mul_sum p m hm t

/-- Giuga's congruence forces, for each prime `p ∣ n`: `(p-1) ∣ (n-1)` and `n/p ≡ 1 (mod p)`. -/
lemma giuga_prime (n : ℕ) (hn : 2 ≤ n) (h : n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1))
    (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) :
    (p - 1) ∣ (n - 1) ∧ ((n / p : ℕ) : ZMod p) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (hpn.trans h)
  rw [Nat.cast_add, Nat.cast_one, lemmaG p n (n - 1) (by omega) hpn] at h0
  by_cases hd : (p - 1) ∣ (n - 1)
  · rw [if_pos hd] at h0
    refine ⟨hd, ?_⟩
    linear_combination -h0
  · rw [if_neg hd, mul_zero, add_zero] at h0
    exact absurd h0 one_ne_zero

lemma giuga_squarefree (n : ℕ) (hn : 2 ≤ n) (h : n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1)) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (dvd_mul_right p p).trans hpp
  have h1 := (giuga_prime n hn h p hp hpn).2
  have h2 : ((n / p : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    obtain ⟨c, rfl⟩ := hpp
    rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right p c
  rw [h2] at h1
  exact zero_ne_one h1

lemma giuga_even (n : ℕ) (hn : 2 ≤ n) (h : n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1))
    (h2 : 2 ∣ n) : n = 2 := by
  by_contra hne
  have h1 := (giuga_prime n hn h 2 Nat.prime_two h2).2
  have hge : n / 2 ≠ 1 := by omega
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hge
  have hqn : q ∣ n := hqd.trans (Nat.div_dvd_of_dvd h2)
  have hq1 := (giuga_prime n hn h q hq hqn).1
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h0 : ((n / 2 : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqd
    rw [h0] at h1
    exact zero_ne_one h1
  have hqodd : 2 ∣ q - 1 := by
    rcases hq.eq_two_or_odd with h' | h'
    · exact absurd h' hq2
    · have := hq.two_le
      omega
  have h3 : 2 ∣ n - 1 := hqodd.trans hq1
  omega

lemma erase_prod_not_dvd (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (q : ℕ) (hq : q ∈ P) :
    ¬ q ∣ ∏ r ∈ P.erase q, r := by
  intro hd
  obtain ⟨r, hr, hqr⟩ := ((hP q hq).prime.dvd_finsetProd_iff (fun r => r)).mp hd
  rw [Finset.mem_erase] at hr
  exact hr.1 (((Nat.prime_dvd_prime_iff_eq (hP q hq) (hP r hr.2)).mp hqr).symm)

lemma sum_c_mod (P : Finset ℕ) (q : ℕ) (hq : q ∈ P) :
    (q : ℤ) ∣ (∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) - ((∏ s ∈ P.erase q, s : ℕ) : ℤ) := by
  have h2 : (q : ℤ) ∣ ∑ r ∈ P.erase q, ((∏ s ∈ P.erase r, s : ℕ) : ℤ) := by
    apply Finset.dvd_sum
    intro r hr
    rw [Finset.mem_erase] at hr
    exact Int.natCast_dvd_natCast.mpr
      (Finset.dvd_prod_of_mem (fun s => s) (Finset.mem_erase.mpr ⟨hr.1.symm, hq⟩))
  have h3 : ((∏ s ∈ P.erase q, s : ℕ) : ℤ) + ∑ r ∈ P.erase q, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)
      = ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ) :=
    Finset.add_sum_erase P (fun r => ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) hq
  have h4 : (∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) - ((∏ s ∈ P.erase q, s : ℕ) : ℤ)
      = ∑ r ∈ P.erase q, ((∏ s ∈ P.erase r, s : ℕ) : ℤ) := by
    linarith
  rw [h4]
  exact h2

lemma key_not_dvd (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (I : ℤ) (q : ℕ) (hq : q ∈ P) :
    ¬ (q : ℤ) ∣ ((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ) := by
  intro hd
  have h1 : (q : ℤ) ∣ ((∏ r ∈ P, r : ℕ) : ℤ) * I :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem (fun r => r) hq)) I
  have h2 := sum_c_mod P q hq
  have h4 : (q : ℤ) ∣ ((∏ s ∈ P.erase q, s : ℕ) : ℤ) := by
    have e : ((∏ s ∈ P.erase q, s : ℕ) : ℤ) =
        ((∏ r ∈ P, r : ℕ) : ℤ) * I
          - (((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ))
          - ((∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) - ((∏ s ∈ P.erase q, s : ℕ) : ℤ)) := by
      ring
    rw [e]
    exact dvd_sub (dvd_sub h1 hd) h2
  exact erase_prod_not_dvd P hP q hq (Int.natCast_dvd_natCast.mp h4)

lemma rat_eq (P : Finset ℕ) (I : ℤ) (B : ℚ) (hB : B + ∑ q ∈ P, (1 : ℚ) / q = I)
    (hP : ∀ q ∈ P, q.Prime) :
    B = ((((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ) : ℤ) : ℚ)
      / (((∏ r ∈ P, r : ℕ) : ℤ) : ℚ) := by
  have hM : ((∏ r ∈ P, r : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun r hr => (hP r hr).ne_zero))
  have hterm : ∀ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℚ)
      = ((∏ r ∈ P, r : ℕ) : ℚ) * ((1 : ℚ) / r) := by
    intro r hr
    have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hP r hr).ne_zero
    have h1 : ((∏ r ∈ P, r : ℕ) : ℚ) = (r : ℚ) * ((∏ s ∈ P.erase r, s : ℕ) : ℚ) := by
      exact_mod_cast (Finset.mul_prod_erase P (fun s => s) hr).symm
    rw [h1, mul_one_div, mul_div_cancel_left₀ _ hr0]
  have hsum : ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℚ)
      = ((∏ r ∈ P, r : ℕ) : ℚ) * ∑ r ∈ P, (1 : ℚ) / r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hA : ((((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ) : ℤ) : ℚ)
      = ((∏ r ∈ P, r : ℕ) : ℚ) * B := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
    rw [hsum]
    linear_combination (-((∏ r ∈ P, r : ℕ) : ℚ)) * hB
  rw [Int.cast_natCast, eq_div_iff hM, hA]
  ring

lemma num_den (P : Finset ℕ) (I : ℤ) (B : ℚ) (hB : B + ∑ q ∈ P, (1 : ℚ) / q = I)
    (hP : ∀ q ∈ P, q.Prime) :
    B.num = ((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ) ∧
    (B.den : ℤ) = ((∏ r ∈ P, r : ℕ) : ℤ) := by
  have hpos : (0 : ℤ) < ((∏ r ∈ P, r : ℕ) : ℤ) :=
    Int.natCast_pos.mpr (Finset.prod_pos (fun r hr => (hP r hr).pos))
  have hcop : Nat.Coprime
      (((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)).natAbs
      (((∏ r ∈ P, r : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast, Nat.coprime_prod_right_iff]
    intro q hq
    rw [Nat.coprime_comm, (hP q hq).coprime_iff_not_dvd, ← Int.natCast_dvd]
    exact key_not_dvd P hP I q hq
  rw [rat_eq P I B hB hP]
  exact ⟨Rat.num_div_eq_of_coprime hpos hcop, Rat.den_div_eq_of_coprime hpos hcop⟩

lemma sqfree_dvd_int (n : ℕ) (hsq : Squarefree n) (X : ℤ)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℤ) ∣ X) : (n : ℤ) ∣ X := by
  have h1 : ∏ p ∈ n.primeFactors, p ∣ X.natAbs :=
    Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => Int.natCast_dvd.mp
        (h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)))
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h1
  exact Int.natCast_dvd.mpr h1

lemma prime_dvd_final (n : ℕ) (P : Finset ℕ) (I : ℤ) (M' : ℕ) (hM' : ∏ r ∈ P, r = n * M')
    (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hpP : p ∈ P) (ht : ((n / p : ℕ) : ZMod p) = 1) :
    (p : ℤ) ∣ (((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ))
      + (M' : ℤ) := by
  obtain ⟨t, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left t hp.pos] at ht
  have h1 : (p : ℤ) ∣ ((∏ r ∈ P, r : ℕ) : ℤ) * I :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem (fun r => r) hpP)) I
  have h2 := sum_c_mod P p hpP
  have h3 : (p : ℤ) ∣ (t : ℤ) - 1 := by
    have h0 : (((t : ℤ) - 1 : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_one, ht, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  have hpc : p * ∏ s ∈ P.erase p, s = ∏ s ∈ P, s := Finset.mul_prod_erase P (fun s => s) hpP
  have h4 : ∏ s ∈ P.erase p, s = t * M' := by
    have h5 : p * ∏ s ∈ P.erase p, s = p * (t * M') := by
      rw [hpc, hM', mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left hp.pos h5
  have h4' : ((∏ s ∈ P.erase p, s : ℕ) : ℤ) = (t : ℤ) * (M' : ℤ) := by
    exact_mod_cast h4
  have e : (((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + (M' : ℤ)
      = ((∏ r ∈ P, r : ℕ) : ℤ) * I
        - ((∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) - ((∏ s ∈ P.erase p, s : ℕ) : ℤ))
        - (M' : ℤ) * ((t : ℤ) - 1) := by
    rw [h4']
    ring
  rw [e]
  exact dvd_sub (dvd_sub h1 h2) (Dvd.dvd.mul_left h3 _)

lemma final_arith (n : ℕ) (P : Finset ℕ) (I : ℤ) (hsq : Squarefree n)
    (hsub : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P ∧ ((n / p : ℕ) : ZMod p) = 1) :
    ∃ z : ℤ, (n : ℤ) * (((∏ r ∈ P, r : ℕ) : ℤ) * I
        - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + ((∏ r ∈ P, r : ℕ) : ℤ)
      = z * (n : ℤ) ^ 2 := by
  have hsubset : n.primeFactors ⊆ P := fun p hp =>
    (hsub p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)).1
  have hnM : n ∣ ∏ r ∈ P, r := by
    have h : ∏ p ∈ n.primeFactors, p ∣ ∏ r ∈ P, r :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsubset
    rwa [Nat.prod_primeFactors_of_squarefree hsq] at h
  obtain ⟨M', hM'⟩ := hnM
  obtain ⟨z, hz⟩ := sqfree_dvd_int n hsq
    ((((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + (M' : ℤ))
    (fun p hp hpn => prime_dvd_final n P I M' hM' p hp hpn (hsub p hp hpn).1 (hsub p hp hpn).2)
  have hMz : ((∏ r ∈ P, r : ℕ) : ℤ) = (n : ℤ) * (M' : ℤ) := by
    exact_mod_cast hM'
  exact ⟨z, by linear_combination (n : ℤ) * hz + hMz⟩

lemma odd_case (n k : ℕ) (hnk : n = 2 * k + 1) (hk : 1 ≤ k) (hsq : Squarefree n)
    (hpr : ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ 2 * k ∧ ((n / p : ℕ) : ZMod p) = 1) :
    ∃ z : ℤ, (n : ℤ) * (bernoulli' (2 * k)).num + ((bernoulli' (2 * k)).den : ℤ)
      = z * (n : ℤ) ^ 2 := by
  obtain ⟨I, hI⟩ := Bernoulli.vonStaudt_clausen k
  have hBB : bernoulli (2 * k) = bernoulli' (2 * k) :=
    bernoulli_eq_bernoulli'_of_ne_one (by omega)
  rw [hBB] at hI
  obtain ⟨hnum, hden⟩ := num_den _ I _ hI.symm (fun q hq => (Finset.mem_filter.mp hq).2.1)
  rw [hnum, hden]
  apply final_arith n _ I hsq
  intro p hp hpn
  obtain ⟨h1, h2⟩ := hpr p hp hpn
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp, h1⟩, h2⟩
  have := Nat.le_of_dvd (by omega) hpn
  omega

lemma case_two : ∃ z : ℤ, ((2 : ℕ) : ℤ) * (bernoulli' (2 - 1)).num
    + ((bernoulli' (2 - 1)).den : ℤ) = z * ((2 : ℕ) : ℤ) ^ 2 := by
  have h12 : bernoulli' (2 - 1) = ((1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
    have h : bernoulli' (2 - 1) = 1 / 2 := bernoulli'_one
    rw [h]
    norm_num
  have hc : Nat.Coprime (1 : ℤ).natAbs (2 : ℤ).natAbs := by
    decide
  have hnum := Rat.num_div_eq_of_coprime (a := 1) (b := 2) (by norm_num) hc
  have hden := Rat.den_div_eq_of_coprime (a := 1) (b := 2) (by norm_num) hc
  rw [h12, hnum, hden]
  exact ⟨1, by norm_num⟩

end AGH2

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_R1_H1_R1.H2 := by
  intro n hn h
  show ∃ k : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + ((bernoulli' (n - 1)).den : ℤ)
    = k * (n : ℤ) ^ 2
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h2 : n = 2 := AGH2.giuga_even n hn h ⟨r, by omega⟩
    subst h2
    exact AGH2.case_two
  · have hr1 : 1 ≤ r := by omega
    have hn1 : n - 1 = 2 * r := by omega
    rw [hn1]
    exact AGH2.odd_case n r hr hr1 (AGH2.giuga_squarefree n hn h) (fun p hp hpn => by
      have h3 := AGH2.giuga_prime n hn h p hp hpn
      rwa [hn1] at h3)
