import OMAReductions.R_AgohGiuga_agoh_giuga_R1_H1_R1
import Mathlib

namespace AGH1

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

lemma erase_prod_not_dvd (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (q : ℕ) (hq : q ∈ P) :
    ¬ q ∣ ∏ r ∈ P.erase q, r := by
  intro hd
  obtain ⟨r, hr, hqr⟩ := ((hP q hq).prime.dvd_finsetProd_iff (fun r => r)).mp hd
  rw [Finset.mem_erase] at hr
  exact hr.1 (((Nat.prime_dvd_prime_iff_eq (hP q hq) (hP r hr.2)).mp hqr).symm)

lemma mem_of_prime_dvd_prod (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : p.Prime)
    (h : p ∣ ∏ r ∈ P, r) : p ∈ P := by
  obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff (fun r => r)).mp h
  have hpr' : p = r := (Nat.prime_dvd_prime_iff_eq hp (hP r hr)).mp hpr
  rw [hpr']
  exact hr

lemma prod_not_sq_dvd (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : p.Prime) :
    ¬ p * p ∣ ∏ r ∈ P, r := by
  intro h
  have hpP : p ∈ P := mem_of_prime_dvd_prod P hP p hp ((dvd_mul_right p p).trans h)
  have hpc : p * ∏ s ∈ P.erase p, s = ∏ s ∈ P, s := Finset.mul_prod_erase P (fun s => s) hpP
  rw [← hpc] at h
  exact erase_prod_not_dvd P hP p hpP ((Nat.mul_dvd_mul_iff_left hp.pos).mp h)

lemma sqfree_of_dvd_prod (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (n : ℕ)
    (h : n ∣ ∏ r ∈ P, r) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  exact prod_not_sq_dvd P hP p hp (hpp.trans h)

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

/-- von Staudt-Clausen consequence: numerator and denominator of `B`. -/
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

lemma final_decomp (P : Finset ℕ) (I : ℤ) (M' p t : ℕ) (hp : p.Prime) (hpP : p ∈ P)
    (hM' : ∏ r ∈ P, r = p * t * M') :
    (((∏ r ∈ P, r : ℕ) : ℤ) * I - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + (M' : ℤ)
      = ((∏ r ∈ P, r : ℕ) : ℤ) * I
        - ((∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) - ((∏ s ∈ P.erase p, s : ℕ) : ℤ))
        - (M' : ℤ) * ((t : ℤ) - 1) := by
  have hpc : p * ∏ s ∈ P.erase p, s = ∏ s ∈ P, s := Finset.mul_prod_erase P (fun s => s) hpP
  have h4 : ∏ s ∈ P.erase p, s = t * M' := by
    have h5 : p * ∏ s ∈ P.erase p, s = p * (t * M') := by
      rw [hpc, hM', mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left hp.pos h5
  have h4' : ((∏ s ∈ P.erase p, s : ℕ) : ℤ) = (t : ℤ) * (M' : ℤ) := by
    exact_mod_cast h4
  rw [h4']
  ring

/-- If `p` divides `A + M'` (with `∏ P = p * t * M'`) then `p ∈ P` and `t ≡ 1 (mod p)`. -/
lemma prime_conv (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (I : ℤ) (M' p t : ℕ) (hp : p.Prime)
    (hM' : ∏ r ∈ P, r = p * t * M')
    (hd : (p : ℤ) ∣ (((∏ r ∈ P, r : ℕ) : ℤ) * I
      - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + (M' : ℤ)) :
    p ∈ P ∧ (t : ZMod p) = 1 := by
  have hpM : p ∣ ∏ r ∈ P, r := by
    rw [hM', mul_assoc]
    exact dvd_mul_right p _
  have hpP : p ∈ P := mem_of_prime_dvd_prod P hP p hp hpM
  refine ⟨hpP, ?_⟩
  have h1 : (p : ℤ) ∣ ((∏ r ∈ P, r : ℕ) : ℤ) * I :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpM) I
  have h2 := sum_c_mod P p hpP
  rw [final_decomp P I M' p t hp hpP hM'] at hd
  have h3 : (p : ℤ) ∣ (M' : ℤ) * ((t : ℤ) - 1) := (dvd_sub_right (dvd_sub h1 h2)).mp hd
  have hnM' : ¬ (p : ℤ) ∣ (M' : ℤ) := by
    intro h
    obtain ⟨w, hw⟩ := Int.natCast_dvd_natCast.mp h
    apply prod_not_sq_dvd P hP p hp
    rw [hM', hw]
    exact ⟨t * w, by ring⟩
  have h4 : (p : ℤ) ∣ (t : ℤ) - 1 :=
    ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h3).resolve_left hnM'
  have h0 : (((t : ℤ) - 1 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h4
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_one] at h0
  exact sub_eq_zero.mp h0

lemma odd_core (n m : ℕ) (hn0 : n ≠ 0) (hm : m ≠ 0) (P : Finset ℕ) (I z : ℤ)
    (hz : (n : ℤ) * (((∏ r ∈ P, r : ℕ) : ℤ) * I
        - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + ((∏ r ∈ P, r : ℕ) : ℤ)
      = z * (n : ℤ) ^ 2)
    (hP : ∀ q ∈ P, q.Prime) (hPm : ∀ q ∈ P, (q - 1) ∣ m) :
    n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ m := by
  have hnz : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnM : n ∣ ∏ r ∈ P, r := by
    apply Int.natCast_dvd_natCast.mp
    exact ⟨z * n - (((∏ r ∈ P, r : ℕ) : ℤ) * I
      - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)), by linear_combination hz⟩
  have hsq : Squarefree n := sqfree_of_dvd_prod P hP n hnM
  obtain ⟨M', hM'⟩ := hnM
  have hMz : ((∏ r ∈ P, r : ℕ) : ℤ) = (n : ℤ) * (M' : ℤ) := by
    exact_mod_cast hM'
  have hAM : (((∏ r ∈ P, r : ℕ) : ℤ) * I
      - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + (M' : ℤ) = z * (n : ℤ) := by
    have hh : (n : ℤ) * ((((∏ r ∈ P, r : ℕ) : ℤ) * I
        - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + (M' : ℤ)) = (n : ℤ) * (z * (n : ℤ)) := by
      linear_combination hz - hMz
    exact Int.eq_of_mul_eq_mul_left hnz hh
  have hprime : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ m := by
    intro p hp hpn
    have : Fact p.Prime := ⟨hp⟩
    have hM'' : ∏ r ∈ P, r = p * (n / p) * M' := by
      rw [Nat.mul_div_cancel' hpn]
      exact hM'
    have hd : (p : ℤ) ∣ (((∏ r ∈ P, r : ℕ) : ℤ) * I
        - ∑ r ∈ P, ((∏ s ∈ P.erase r, s : ℕ) : ℤ)) + (M' : ℤ) := by
      rw [hAM]
      exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hpn) z
    obtain ⟨hpP, ht⟩ := prime_conv P hP I M' p (n / p) hp hM'' hd
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, lemmaG p n m hm hpn,
      if_pos (hPm p hpP), ht]
    ring
  have h1 : ∏ p ∈ n.primeFactors, p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ m :=
    Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => hprime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  rwa [Nat.prod_primeFactors_of_squarefree hsq] at h1

lemma odd_case (n k : ℕ) (hnk : n = 2 * k + 1) (hk : 1 ≤ k)
    (h : ∃ z : ℤ, (n : ℤ) * (bernoulli' (2 * k)).num + ((bernoulli' (2 * k)).den : ℤ)
      = z * (n : ℤ) ^ 2) :
    n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (2 * k) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨I, hI⟩ := Bernoulli.vonStaudt_clausen k
  have hBB : bernoulli (2 * k) = bernoulli' (2 * k) :=
    bernoulli_eq_bernoulli'_of_ne_one (by omega)
  rw [hBB] at hI
  obtain ⟨hnum, hden⟩ := num_den _ I _ hI.symm (fun q hq => (Finset.mem_filter.mp hq).2.1)
  rw [hnum, hden] at hz
  exact odd_core n (2 * k) (by omega) (by omega) _ I z hz
    (fun q hq => (Finset.mem_filter.mp hq).2.1) (fun q hq => (Finset.mem_filter.mp hq).2.2)

lemma even_case (n : ℕ) (hn : 2 ≤ n) (h2 : 2 ∣ n)
    (h : ∃ z : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + ((bernoulli' (n - 1)).den : ℤ)
      = z * (n : ℤ) ^ 2) :
    n = 2 := by
  by_contra hne
  obtain ⟨z, hz⟩ := h
  have hodd : Odd (n - 1) := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c - 1, by omega⟩
  have hB0 : bernoulli' (n - 1) = 0 := bernoulli'_eq_zero_of_odd hodd (by omega)
  have h0n : (0 : ℚ).num = 0 := rfl
  have h0d : (0 : ℚ).den = 1 := rfl
  rw [hB0, h0n, h0d, Nat.cast_one] at hz
  have hdvd : (n : ℤ) ∣ 1 := ⟨z * n, by linear_combination hz⟩
  have hle : (n : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  omega

lemma two_case : (2 : ℕ) ∣ 1 + ∑ i ∈ Finset.Ioo (0 : ℕ) 2, i ^ (2 - 1) := by
  have hI : Finset.Ioo (0 : ℕ) 2 = {1} := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_singleton]
    constructor <;> intro hx <;> omega
  rw [hI, Finset.sum_singleton]
  decide

end AGH1

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_R1_H1_R1.H1 := by
  intro n hn h
  have h' : ∃ k : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + ((bernoulli' (n - 1)).den : ℤ)
      = k * (n : ℤ) ^ 2 := h
  rcases Nat.even_or_odd n with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h2 : n = 2 := AGH1.even_case n hn ⟨r, by omega⟩ h'
    subst h2
    exact AGH1.two_case
  · have hr1 : 1 ≤ r := by omega
    have hn1 : n - 1 = 2 * r := by omega
    rw [hn1] at h' ⊢
    exact AGH1.odd_case n r hr hr1 h'
