import FormalConjectures.Wikipedia.AgohGiuga

-- Problem: Agoh-Giuga conjecture — equivalence
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/AgohGiuga.lean:75 (declaration AgohGiuga.agoh_giuga.variants.equivalence)
-- Credit: @ZenimXD (the owner of the agent is credited as the solver)
-- Reference: Bernd C. Kellner, The Equivalence of Giuga’s and Agoh’s Conjectures (2004).

/-!
# Equivalence of Agoh's and Giuga's conjectures

We compare the two congruences for each natural number at least two.
-/

open Finset

namespace AgohGiuga

-- Von Staudt–Clausen bounds the reduced denominator by a product of distinct primes.
private lemma squarefree_bernoulli_den (j : ℕ) : Squarefree (bernoulli j).den := by
  rcases eq_or_ne j 1 with rfl | hj
  · norm_num [bernoulli_one]
    exact Nat.squarefree_two
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | hk
  · rw [show j = 2 * k by omega]
    let s := (range (2 * k + 2)).filter fun p => p.Prime ∧ (p - 1) ∣ 2 * k
    have hp (p) (h : p ∈ s) : p.Prime := (mem_filter.mp h).2.1
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
    change (z : ℚ) = bernoulli (2 * k) + ∑ p ∈ s, (1 : ℚ) / p at hz
    have hd := Rat.sub_den_dvd (z : ℚ) (∑ p ∈ s, (1 : ℚ) / p)
    rw [show (z : ℚ) - (∑ p ∈ s, (1 : ℚ) / p) = bernoulli (2 * k) by
      rw [hz, add_sub_cancel_right]] at hd
    simp only [Rat.den_intCast, one_mul] at hd
    have hprod := Rat.den_sum_dvd_prod_den s (fun p => (1 : ℚ) / p)
    have he : (∏ p ∈ s, ((1 : ℚ) / p).den) = ∏ p ∈ s, p := by
      exact prod_congr rfl fun p h => by simp [(hp p h).ne_zero]
    rw [he] at hprod
    have hsf : Squarefree (∏ p ∈ s, p) :=
      Finset.squarefree_prod_of_pairwise_isCoprime
        (fun p hp' q hq' hne =>
          Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hp') (hp q hq')).mpr hne))
        (fun p h => (hp p h).squarefree)
    exact hsf.squarefree_of_dvd (hd.trans hprod)
  · simp [bernoulli_eq_zero_of_odd hk (by have := hk.pos; omega)]

private lemma den_intCast_div_natCast_dvd (a : ℤ) (d : ℕ) :
    ((a : ℚ) / d).den ∣ d := by
  exact Int.natCast_dvd_natCast.mp (by
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd a (d : ℤ))

private lemma coprime_den_natCast_mul {n : ℕ} (hn : n ≠ 0) (q : ℚ) (hq : Squarefree q.den) :
    n.Coprime ((n : ℚ) * q).den := by
  simpa [Rat.mul_den, Int.natAbs_mul, q.reduced.gcd_mul_right_cancel, Nat.gcd_comm n q.den] using
    (Nat.coprime_div_gcd_of_squarefree (n := n) hq hn).symm

private lemma dvd_of_coprime_fraction_den {a : ℤ} {n d : ℕ} (hd : d ≠ 0)
    (hnd : n ∣ d) (hc : n.Coprime ((a : ℚ) / d).den) : (n : ℤ) ∣ a := by
  let q : ℚ := (a : ℚ) / d
  obtain ⟨c, ha, hden⟩ := Rat.num_den_mk (q := q) (n := a) (d := (d : ℤ))
    (by exact_mod_cast hd) (Rat.intCast_div_eq_divInt _ _)
  have he := congrArg Int.natAbs hden
  simp only [Int.natAbs_natCast, Int.natAbs_mul] at he
  rw [he] at hnd
  have hc' : n.Coprime q.den := hc
  exact ha ▸ dvd_mul_of_dvd_left (Int.natCast_dvd.mpr (hc'.dvd_mul_right.mp hnd)) q.num

private lemma giuga_fraction_iff {n a : ℕ} (hn : n ≠ 0) :
    n ∣ a ↔ n.Coprime ((a : ℚ) / n).den := by
  constructor
  · rintro ⟨k, rfl⟩
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    simp [Nat.cast_mul, hn']
  · intro hc
    have hd := dvd_of_coprime_fraction_den (a := (a : ℤ)) hn (dvd_refl n) (by simpa using hc)
    exact Int.natCast_dvd_natCast.mp hd

-- The reduced denominator is squarefree, so if it contains n, its quotient by n is coprime to n.
private lemma agoh_fraction_iff {n : ℕ} (hn : n ≠ 0) (q : ℚ) (hq : Squarefree q.den) :
    ((n : ℤ) ^ 2 ∣ (n : ℤ) * q.num + q.den) ↔ n.Coprime (q + 1 / (n : ℚ)).den := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hq' : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  constructor
  · rintro ⟨k, hk⟩
    have hnd : (n : ℤ) ∣ (q.den : ℤ) := by
      have h : (n : ℤ) ∣ (n : ℤ) * q.num + q.den := by
        rw [hk, pow_two, mul_assoc]
        exact dvd_mul_right _ _
      exact (dvd_add_right (dvd_mul_right (n : ℤ) q.num)).mp h
    obtain ⟨d, hd⟩ := Int.natCast_dvd_natCast.mp hnd
    have hc : n.Coprime d := Nat.coprime_of_squarefree_mul (hd ▸ hq)
    have hdq : (q.den : ℚ) = (n : ℚ) * d := by exact_mod_cast hd
    have hd' : (d : ℚ) ≠ 0 := fun e => hq' (by simp [hdq, e])
    have hkq := congrArg (fun z : ℤ => (z : ℚ)) hk
    push_cast at hkq
    have he : q + 1 / (n : ℚ) = (k : ℚ) / d := by
      conv_lhs => rw [← Rat.num_div_den q, hdq]
      field_simp [hn', hd']
      apply mul_left_cancel₀ hn'
      rw [hdq] at hkq
      linear_combination hkq
    rw [he]
    exact hc.of_dvd_right (den_intCast_div_natCast_dvd _ _)
  · intro hc
    let a : ℤ := (n : ℤ) * q.num + q.den
    have he : q + 1 / (n : ℚ) = (a : ℚ) / ((n * q.den : ℕ) : ℚ) := by
      conv_lhs => rw [← Rat.num_div_den q]
      push_cast [a]
      field_simp [hn', hq']
    have hnd : n ∣ q.den := by
      have h := Rat.sub_den_dvd (q + 1 / (n : ℚ)) q
      rw [add_sub_cancel_left] at h
      have hnDen : ((1 : ℚ) / n).den = n := by simp [hn]
      rw [hnDen] at h
      exact hc.dvd_mul_left.mp h
    have hd : n ^ 2 ∣ n * q.den := by
      simpa only [pow_two] using mul_dvd_mul (dvd_refl n) hnd
    exact_mod_cast dvd_of_coprime_fraction_den (a := a) (mul_ne_zero hn q.den_nz) hd
      (by rw [← he]; exact hc.pow_left 2)

private abbrev powerSum (n : ℕ) : ℕ :=
  ∑ j ∈ Ioo 0 n, j ^ (n - 1)

-- At the exponent k and length k + 1, the Faulhaber denominator is the length itself.
private lemma power_sum_div_sub_bernoulli {k : ℕ} (hk : 0 < k) :
    (powerSum (k + 1) : ℚ) / (k + 1) - bernoulli k =
      ∑ i ∈ range k, bernoulli i * ((k + 1).choose i : ℚ) * (k + 1 : ℚ) ^ (k - 1 - i) := by
  have hcast : (powerSum (k + 1) : ℚ) = ∑ j ∈ range (k + 1), (j : ℚ) ^ k := by
    have hs : Ioo 0 (k + 1) = Ico 1 (k + 1) := by
      ext j
      simp only [mem_Ioo, mem_Ico]
      omega
    simp [powerSum, hs, Finset.sum_range_eq_add_Ico, hk.ne']
  have hkq : (k + 1 : ℚ) ≠ 0 := by positivity
  have hlead : bernoulli k * ((k + 1).choose k : ℚ) * (k + 1 : ℚ) ^ (k + 1 - k) /
      (k + 1) / (k + 1) = bernoulli k := by
    rw [Nat.choose_succ_self_right, show k + 1 - k = 1 by omega, pow_one, Nat.cast_add,
      Nat.cast_one]
    field_simp
  rw [hcast, sum_range_pow, sum_range_succ]
  push_cast
  rw [add_div, hlead, add_sub_cancel_right, sum_div]
  refine sum_congr rfl fun i hi => ?_
  have hil := mem_range.mp hi
  rw [show k + 1 - i = (k - 1 - i) + 1 + 1 by omega, pow_succ, pow_succ]
  field_simp [hkq]

private lemma even_power_sum_exclusion {n : ℕ} (hn : 2 < n) (hk : Odd (n - 1)) :
    ¬ n ∣ 1 + powerSum n := by
  let s : ZMod n := ∑ j ∈ Ioo 0 n, (j : ZMod n) ^ (n - 1)
  have hmem (j) (hj : j ∈ Ioo 0 n) : n - j ∈ Ioo 0 n := by
    rw [mem_Ioo] at hj ⊢
    omega
  have hperm : s = ∑ j ∈ Ioo 0 n, ((n - j : ℕ) : ZMod n) ^ (n - 1) := by
    change (∑ j ∈ Ioo 0 n, (j : ZMod n) ^ (n - 1)) = _
    refine sum_bij' (fun j _ => n - j) (fun j _ => n - j) hmem hmem ?_ ?_ ?_
    · intro j hj
      have := (mem_Ioo.mp hj).2
      omega
    · intro j hj
      have := (mem_Ioo.mp hj).2
      omega
    · intro j hj
      have he : n - (n - j) = j := by have := (mem_Ioo.mp hj).2; omega
      rw [he]
  have hs : s = -s := by
    calc
      s = ∑ j ∈ Ioo 0 n, ((n - j : ℕ) : ZMod n) ^ (n - 1) := hperm
      _ = ∑ j ∈ Ioo 0 n, -((j : ZMod n) ^ (n - 1)) := by
        refine sum_congr rfl fun j hj => ?_
        rw [Nat.cast_sub (mem_Ioo.mp hj).2.le, ZMod.natCast_self, zero_sub, hk.neg_pow]
      _ = -s := Finset.sum_neg_distrib _
  intro hd
  have hz : (1 : ZMod n) + s = 0 := by
    change (1 : ZMod n) + ∑ j ∈ Ioo 0 n, (j : ZMod n) ^ (n - 1) = 0
    exact_mod_cast (ZMod.natCast_eq_zero_iff (1 + powerSum n) n).mpr hd
  have ht : (2 : ZMod n) = 0 := by linear_combination 2 * hz - hs
  have hn2 : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa using ht)
  exact (Nat.not_dvd_of_pos_of_lt (by decide : 0 < (2 : ℕ)) hn) hn2

-- In odd length, the lower-degree terms have a denominator coprime to the length.
private lemma odd_power_sum_difference {k : ℕ} (hk : 0 < k) (he : Even k) :
    (k + 1).Coprime (((powerSum (k + 1) : ℚ) / (k + 1) - bernoulli k).den) := by
  rw [power_sum_div_sub_bernoulli hk]
  apply Nat.Coprime.of_dvd_right (Rat.den_sum_dvd_prod_den _ _)
  refine Nat.Coprime.prod_right fun i hi => ?_
  have hki := mem_range.mp hi
  have hmul (q : ℚ) (a : ℕ) (hq : (k + 1).Coprime q.den) :
      (k + 1).Coprime (q * (a : ℚ)).den :=
    hq.of_dvd_right (by simpa using Rat.mul_den_dvd q (a : ℚ))
  by_cases hi' : i < k - 1
  · rw [show k - 1 - i = (k - 2 - i) + 1 by omega, pow_succ]
    have h :
        bernoulli i * ((k + 1).choose i : ℚ) * ((k + 1 : ℚ) ^ (k - 2 - i) * (k + 1)) =
          ((↑(k + 1 : ℕ) : ℚ) * bernoulli i) *
          ↑((k + 1).choose i * (k + 1) ^ (k - 2 - i)) := by push_cast; ring
    rw [h]
    exact hmul _ _ (coprime_den_natCast_mul (by omega) _ (squarefree_bernoulli_den i))
  · rw [show k - 1 - i = 0 by omega, pow_zero, mul_one]
    apply hmul
    by_cases hi1 : i = 1
    · have hk2 : k = 2 := by omega
      subst i
      subst k
      norm_num [bernoulli_one, one_div, Rat.inv_ofNat_den, Nat.coprime_iff_gcd_eq_one]
    · have hodd : Odd i := by
        obtain ⟨m, hm⟩ := he
        exact ⟨m - 1, by omega⟩
      simp [bernoulli_eq_zero_of_odd hodd (by have := hodd.pos; omega)]

private lemma coprime_add_den_iff {n : ℕ} {a b : ℚ} (hb : n.Coprime b.den) :
    n.Coprime (a + b).den ↔ n.Coprime a.den := by
  constructor
  · intro h
    have hd := Rat.sub_den_dvd (a + b) b
    rw [add_sub_cancel_right] at hd
    exact (h.mul_right hb).of_dvd_right hd
  · intro h
    exact (h.mul_right hb).of_dvd_right (Rat.add_den_dvd a b)

private lemma pointwise_equivalence (n : ℕ) (hn : 2 ≤ n) :
    (∃ k : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + (bernoulli' (n - 1)).den =
      k * (n : ℤ) ^ 2) ↔ n ∣ 1 + powerSum n := by
  rcases eq_or_ne n 2 with rfl | hn2
  · refine iff_of_true ⟨1, ?_⟩ ?_
    · rw [show (2 : ℕ) - 1 = 1 by decide, bernoulli'_one]
      norm_num [one_div, Rat.inv_ofNat_den, Rat.inv_ofNat_num]
    · have hs : Ioo (0 : ℕ) 2 = {1} := by decide
      simp [powerSum, hs]
  have hn0 : n ≠ 0 := by omega
  have hAgoh :
      (∃ k : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + (bernoulli' (n - 1)).den =
        k * (n : ℤ) ^ 2) ↔ ((n : ℤ) ^ 2 ∣
          (n : ℤ) * (bernoulli' (n - 1)).num + (bernoulli' (n - 1)).den) := by
    constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, hk.trans (mul_comm _ _)⟩
  rw [hAgoh, ← bernoulli_eq_bernoulli'_of_ne_one (by omega),
    agoh_fraction_iff hn0 _ (squarefree_bernoulli_den _)]
  rcases Nat.even_or_odd (n - 1) with he | ho
  · rw [giuga_fraction_iff hn0]
    have hR : n.Coprime (((powerSum n : ℚ) / n - bernoulli (n - 1)).den) := by
      have hs : n - 1 + 1 = n := by omega
      simpa only [← Nat.cast_add_one, hs] using
        (odd_power_sum_difference (by omega : 0 < n - 1) he)
    have hEq : ((1 + powerSum n : ℕ) : ℚ) / n =
        (bernoulli (n - 1) + 1 / (n : ℚ)) + ((powerSum n : ℚ) / n - bernoulli (n - 1)) := by
      push_cast
      ring
    rw [hEq, coprime_add_den_iff hR]
  · rw [bernoulli_eq_zero_of_odd ho (by omega), zero_add]
    have he : ((1 : ℚ) / n).den = n := by simp [hn0]
    rw [he]
    exact iff_of_false (by simp; omega) (even_power_sum_exclusion (by omega) ho)

end AgohGiuga

theorem OMA.solution : type_of% @AgohGiuga.agoh_giuga.variants.equivalence := by
  change AgohGiuga.AgohGiugaCongr ↔ AgohGiuga.AgohGiugaSum
  constructor
  · intro h n hn
    exact (h n hn).trans (AgohGiuga.pointwise_equivalence n hn)
  · intro h n hn
    exact (h n hn).trans (AgohGiuga.pointwise_equivalence n hn).symm
