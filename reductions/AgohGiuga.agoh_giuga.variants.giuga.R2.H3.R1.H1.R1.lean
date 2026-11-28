import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H3_R1

/-! Reciprocal sum bounds and congruences for the mixed residue case. -/

open scoped BigOperators Nat

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H3_R1_H1_R1

open OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H3_R1

private theorem reciprocal_bound (s T : Finset ℕ) (B K t : ℕ)
    (hs : ∀ p ∈ s, 0 < p) (hsmall : ∀ p ∈ s, p < B → p ∈ T)
    (hlarge : K ≤ B * t) :
    (K : ℚ) * (∑ p ∈ s, 1 / (p : ℚ)) ≤
      (s.card : ℚ) * t + (↑(∑ p ∈ T, ((K + p - 1) / p - t)) : ℚ) := by
  let extra (p : ℕ) := (K + p - 1) / p - t
  let weight (p : ℕ) : ℚ := t + if p ∈ T then (extra p : ℚ) else 0
  have hweight (p : ℕ) (hp : p ∈ s) : (K : ℚ) * (1 / (p : ℚ)) ≤ weight p := by
    have hpQ : (0 : ℚ) < p := by exact_mod_cast hs p hp
    rw [mul_one_div]
    apply (div_le_iff₀ hpQ).2
    by_cases h : p < B
    · have hceil : K ≤ p * ((K + p - 1) / p) := by
        have hm := Nat.mod_lt (K + p - 1) (hs p hp)
        have hd := Nat.div_add_mod (K + p - 1) p
        omega
      have hstep : K ≤ (t + extra p) * p := by
        rw [mul_comm (t + extra p) p]
        exact hceil.trans (Nat.mul_le_mul_left _ (by dsimp [extra]; omega))
      simp only [weight, if_pos (hsmall p hp h)]
      exact_mod_cast hstep
    · have hstep : K ≤ t * p := by
        rw [mul_comm t p]
        exact hlarge.trans (Nat.mul_le_mul_right t (by omega))
      have hbase : (K : ℚ) ≤ (t : ℚ) * p := by exact_mod_cast hstep
      apply hbase.trans
      apply mul_le_mul_of_nonneg_right _ hpQ.le
      dsimp [weight]
      split_ifs
      · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
      · simp
  calc
    _ = ∑ p ∈ s, (K : ℚ) * (1 / (p : ℚ)) := Finset.mul_sum ..
    _ ≤ ∑ p ∈ s, weight p := Finset.sum_le_sum hweight
    _ = (s.card : ℚ) * t + (↑(∑ p ∈ s.filter (· ∈ T), extra p) : ℚ) := by
      simp only [weight, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_filter, Nat.cast_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> simp
    _ ≤ _ := by
      apply add_le_add_right
      change (↑(∑ p ∈ s.filter (· ∈ T), extra p) : ℚ) ≤ ↑(∑ p ∈ T, extra p)
      exact_mod_cast (Finset.sum_le_sum_of_subset (f := extra) (s := s.filter (· ∈ T))
        (t := T) (fun _ hp => (Finset.mem_filter.mp hp).2))

private theorem prime_in_wheel (w : List ℕ) (hw : ∀ d ∈ w, Nat.Prime d)
    {p : ℕ} (hp : p.Prime) : p ∈ w ∨ p.Coprime w.prod := by
  induction w with
  | nil => simp
  | cons d w ih =>
    by_cases h : p = d
    · exact Or.inl (by simp [h])
    · rcases ih (fun q hq => hw q (List.mem_cons.mpr (Or.inr hq))) with hm | hc
      · exact Or.inl (List.mem_cons.mpr (Or.inr hm))
      · have hd : d.Prime := hw d List.mem_cons_self
        have hcop : p.Coprime d := hp.coprime_iff_not_dvd.mpr
          (fun hdvd => h ((Nat.prime_dvd_prime_iff_eq hp hd).mp hdvd))
        exact Or.inr (hcop.mul_right hc)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 20000000 in
/-- Integer upper bounds on the contributions above the uniform tail weight. -/
private theorem small_prime_weights (containsFive : Bool) :
    let wheelPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    (∑ p ∈ (Finset.Ico 5 20000).filter (fun p =>
        (p ∈ wheelPrimes ∨ p.Coprime wheelPrimes.prod) ∧
          (if containsFive then p % 5 ≠ 1 else p ≠ 5)), ((100000000 + p - 1) / p - 5000))
      ≤ if containsFive then 127300000 else 141005000 := by
  intro wheelPrimes
  rw [Finset.sum_filter]
  let weight (p : ℕ) : ℕ :=
    if (p ∈ wheelPrimes ∨ p.Coprime wheelPrimes.prod) ∧
        (if containsFive then p % 5 ≠ 1 else p ≠ 5)
    then (100000000 + p - 1) / p - 5000
    else 0
  change (∑ p ∈ Finset.Ico 5 20000, weight p) ≤
    if containsFive then 127300000 else 141005000
  cases containsFive
  case false =>
    have h1000 : (∑ p ∈ Finset.Ico 5 1000, weight p) = 115649757 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h2000 : (∑ p ∈ Finset.Ico 1000 2000, weight p) = 8761909 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h3000 : (∑ p ∈ Finset.Ico 2000 3000, weight p) = 4525156 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h4000 : (∑ p ∈ Finset.Ico 3000 4000, weight p) = 2853423 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h5000 : (∑ p ∈ Finset.Ico 4000 5000, weight p) = 2065620 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h6000 : (∑ p ∈ Finset.Ico 5000 6000, weight p) = 1509593 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h7000 : (∑ p ∈ Finset.Ico 6000 7000, weight p) = 1218229 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h8000 : (∑ p ∈ Finset.Ico 7000 8000, weight p) = 892650 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h9000 : (∑ p ∈ Finset.Ico 8000 9000, weight p) = 745322 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h10000 : (∑ p ∈ Finset.Ico 9000 10000, weight p) = 621605 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h11000 : (∑ p ∈ Finset.Ico 10000 11000, weight p) = 499175 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h12000 : (∑ p ∈ Finset.Ico 11000 12000, weight p) = 410416 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h13000 : (∑ p ∈ Finset.Ico 12000 13000, weight p) = 339358 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h14000 : (∑ p ∈ Finset.Ico 13000 14000, weight p) = 267683 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h15000 : (∑ p ∈ Finset.Ico 14000 15000, weight p) = 211932 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h16000 : (∑ p ∈ Finset.Ico 15000 16000, weight p) = 170404 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h17000 : (∑ p ∈ Finset.Ico 16000 17000, weight p) = 115819 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h18000 : (∑ p ∈ Finset.Ico 17000 18000, weight p) = 83526 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h19000 : (∑ p ∈ Finset.Ico 18000 19000, weight p) = 44238 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h20000 : (∑ p ∈ Finset.Ico 19000 20000, weight p) = 15295 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    rw [
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 19000) (k := 20000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 18000) (k := 19000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 17000) (k := 18000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 16000) (k := 17000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 15000) (k := 16000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 14000) (k := 15000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 13000) (k := 14000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 12000) (k := 13000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 11000) (k := 12000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 10000) (k := 11000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 9000) (k := 10000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 8000) (k := 9000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 7000) (k := 8000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 6000) (k := 7000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 5000) (k := 6000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 4000) (k := 5000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 3000) (k := 4000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 2000) (k := 3000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 1000) (k := 2000) (by decide) (by decide)]
    rw [h1000, h2000, h3000, h4000, h5000, h6000, h7000, h8000, h9000, h10000, h11000, h12000, h13000, h14000, h15000, h16000, h17000, h18000, h19000, h20000]
    decide
  case true =>
    have h1000 : (∑ p ∈ Finset.Ico 5 1000, weight p) = 108259571 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h2000 : (∑ p ∈ Finset.Ico 1000 2000, weight p) = 6586086 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h3000 : (∑ p ∈ Finset.Ico 2000 3000, weight p) = 3443880 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h4000 : (∑ p ∈ Finset.Ico 3000 4000, weight p) = 2105320 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h5000 : (∑ p ∈ Finset.Ico 4000 5000, weight p) = 1559446 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h6000 : (∑ p ∈ Finset.Ico 5000 6000, weight p) = 1099253 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h7000 : (∑ p ∈ Finset.Ico 6000 7000, weight p) = 885580 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h8000 : (∑ p ∈ Finset.Ico 7000 8000, weight p) = 725567 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h9000 : (∑ p ∈ Finset.Ico 8000 9000, weight p) = 561990 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h10000 : (∑ p ∈ Finset.Ico 9000 10000, weight p) = 437991 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h11000 : (∑ p ∈ Finset.Ico 10000 11000, weight p) = 384739 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h12000 : (∑ p ∈ Finset.Ico 11000 12000, weight p) = 318196 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h13000 : (∑ p ∈ Finset.Ico 12000 13000, weight p) = 251459 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h14000 : (∑ p ∈ Finset.Ico 13000 14000, weight p) = 205032 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h15000 : (∑ p ∈ Finset.Ico 14000 15000, weight p) = 160263 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h16000 : (∑ p ∈ Finset.Ico 15000 16000, weight p) = 121905 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h17000 : (∑ p ∈ Finset.Ico 16000 17000, weight p) = 86067 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h18000 : (∑ p ∈ Finset.Ico 17000 18000, weight p) = 62882 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h19000 : (∑ p ∈ Finset.Ico 18000 19000, weight p) = 32636 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    have h20000 : (∑ p ∈ Finset.Ico 19000 20000, weight p) = 10861 := by
      dsimp only [weight, wheelPrimes]
      decide +kernel
    rw [
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 19000) (k := 20000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 18000) (k := 19000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 17000) (k := 18000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 16000) (k := 17000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 15000) (k := 16000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 14000) (k := 15000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 13000) (k := 14000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 12000) (k := 13000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 11000) (k := 12000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 10000) (k := 11000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 9000) (k := 10000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 8000) (k := 9000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 7000) (k := 8000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 6000) (k := 7000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 5000) (k := 6000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 4000) (k := 5000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 3000) (k := 4000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 2000) (k := 3000) (by decide) (by decide),
      ← Finset.sum_Ico_consecutive weight (m := 5) (n := 1000) (k := 2000) (by decide) (by decide)]
    rw [h1000, h2000, h3000, h4000, h5000, h6000, h7000, h8000, h9000, h10000, h11000, h12000, h13000, h14000, h15000, h16000, h17000, h18000, h19000, h20000]
    decide

private theorem square_cast_mod_twentyfour {p : ℕ} (hp : p.Prime) (hge : 5 ≤ p) :
    (p : ZMod 24) * (p : ZMod 24) = 1 := by
  have hc2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hc3 : p.Coprime 3 := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hc : p.Coprime 24 := hc2.mul_right (hc2.mul_right (hc2.mul_right hc3))
  have hmod : (p % 24).Coprime 24 := by
    unfold Nat.Coprime at hc ⊢
    rwa [← Nat.gcd_rec 24 p, Nat.gcd_comm 24 p]
  have hfinite (a : Fin 24) : a.val.Coprime 24 → (a.val : ZMod 24) * (a.val : ZMod 24) = 1 := by
    revert a
    decide
  have hv := hfinite ⟨p % 24, Nat.mod_lt _ (by decide)⟩ hmod
  change ((p % 24 : ℕ) : ZMod 24) * ((p % 24 : ℕ) : ZMod 24) = 1 at hv
  simpa only [ZMod.natCast_mod] using hv

private theorem reciprocal_sum_mod_twentyfour {n k : ℕ} (hn : n ≠ 0) (hsqf : Squarefree n)
    (hge : ∀ p ∈ n.primeFactors, 5 ≤ p)
    (hs : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    ∑ p ∈ n.primeFactors, p ≡ k + n [MOD 24] := by
  have hp (p : ℕ) (hm : p ∈ n.primeFactors) : (p : ZMod 24) * (p : ZMod 24) = 1 :=
    square_cast_mod_twentyfour (Nat.prime_of_mem_primeFactors hm) (hge p hm)
  have hn_sq : (n : ZMod 24) * (n : ZMod 24) = 1 := by
    calc
      _ = (∏ p ∈ n.primeFactors, (p : ZMod 24)) * (∏ p ∈ n.primeFactors, (p : ZMod 24)) := by
        rw [← Nat.cast_prod, prod_primeFactors_of_sqf hsqf hn]
      _ = ∏ p ∈ n.primeFactors, (p : ZMod 24) * (p : ZMod 24) := Finset.prod_mul_distrib.symm
      _ = 1 := Finset.prod_eq_one hp
  have hprod (p : ℕ) (hm : p ∈ n.primeFactors) :
      (n : ZMod 24) * ((n / p : ℕ) : ZMod 24) = (p : ZMod 24) := by
    have hfactor : ((n / p : ℕ) : ZMod 24) * (p : ZMod 24) = (n : ZMod 24) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hm)]
    calc
      _ = (n : ZMod 24) * (((n / p : ℕ) : ZMod 24) * ((p : ZMod 24) * (p : ZMod 24))) := by
        rw [hp p hm, mul_one]
      _ = (p : ZMod 24) := by
        rw [← mul_assoc ((n / p : ℕ) : ZMod 24) (p : ZMod 24) (p : ZMod 24), hfactor,
          ← mul_assoc, hn_sq, one_mul]
  have hexact := congrArg (fun a : ℕ => (a : ZMod 24)) (sum_div_eq_mul_add_one hn hs)
  push_cast at hexact
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  calc
    _ = (n : ZMod 24) * (∑ p ∈ n.primeFactors, ((n / p : ℕ) : ZMod 24)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p hm => (hprod p hm).symm
    _ = (k : ZMod 24) + (n : ZMod 24) := by
      rw [hexact, mul_add, mul_one, mul_left_comm, hn_sq, mul_one]

private theorem mod_twentyfive_of_five {n : ℕ} (hn : 0 < n) (hfive : 5 ∈ n.primeFactors)
    (hstrong : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) : n % 25 = 5 := by
  have hdiv : 5 ∣ n := Nat.dvd_of_mem_primeFactors hfive
  have hco : 5 ∣ n / 5 - 1 := (show 5 ∣ 5 * (5 - 1) by decide).trans (hstrong 5 hfive)
  obtain ⟨j, hj⟩ := hco
  have hp := Nat.div_mul_cancel hdiv
  omega

private theorem card_from_reciprocal_sum {n k : ℕ} (hn : n ≠ 0) (containsFive : Bool)
    (hge : ∀ p ∈ n.primeFactors, 5 ≤ p)
    (hfilter : ∀ p ∈ n.primeFactors, if containsFive then p % 5 ≠ 1 else p ≠ 5)
    (hs : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    100000000 * k < 5000 * n.primeFactors.card + (if containsFive then 127300000 else 141005000) := by
  let wheelPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
    47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
  let T := (Finset.Ico 5 20000).filter (fun p =>
    (p ∈ wheelPrimes ∨ p.Coprime wheelPrimes.prod) ∧ (if containsFive then p % 5 ≠ 1 else p ≠ 5))
  have hw : ∀ d ∈ wheelPrimes, Nat.Prime d := by dsimp [wheelPrimes]; decide
  have hsmall (p : ℕ) (hp : p ∈ n.primeFactors) (hb : p < 20000) : p ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hge p hp, hb⟩,
      prime_in_wheel wheelPrimes hw (Nat.prime_of_mem_primeFactors hp), hfilter p hp⟩
  have hbound := reciprocal_bound n.primeFactors T 20000 100000000 5000
    (fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos) hsmall (by decide)
  have hT : (∑ p ∈ T, ((100000000 + p - 1) / p - 5000)) ≤
      if containsFive then 127300000 else 141005000 := small_prime_weights containsFive
  have hnQ : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpos : 0 < 1 / (n : ℚ) := one_div_pos.mpr hnQ
  have hk : (k : ℚ) < ∑ p ∈ n.primeFactors, 1 / (p : ℚ) := by linarith
  have hQ := mul_lt_mul_of_pos_left hk (show (0 : ℚ) < 100000000 by norm_num)
  have hUpper : (100000000 : ℚ) * k < (n.primeFactors.card : ℚ) * 5000 +
      (↑(if containsFive then 127300000 else 141005000 : ℕ) : ℚ) := by
    refine hQ.trans_le (hbound.trans ?_)
    apply add_le_add_right
    exact_mod_cast hT
  rw [mul_comm (n.primeFactors.card : ℚ)] at hUpper
  exact_mod_cast hUpper

/-- The case with prime divisor 5, with its supporting congruence and stronger count bound. -/
def H1 : Prop :=
  ∀ n k : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) →
    n % 4 = 1 → 5 ∈ n.primeFactors → n % 25 = 5 →
    100000000 * k < 5000 * n.primeFactors.card + 127300000 →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, 5 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    2 ≤ k → n.primeFactors.card % 4 = (k + 1) % 4 →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 →
    (∑ p ∈ n.primeFactors, p ≡ k + n [MOD 24]) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) → False

/-- The case without prime divisor 5, with its stronger count bound. -/
def H2 : Prop :=
  ∀ n k : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) →
    n % 4 = 1 → 5 ∉ n.primeFactors →
    100000000 * k < 5000 * n.primeFactors.card + 141005000 →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, 5 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    2 ≤ k → n.primeFactors.card % 4 = (k + 1) % 4 →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 →
    (∑ p ∈ n.primeFactors, p ≡ k + n [MOD 24]) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) → False

/-- Both branches together cover the mixed mod-four step. -/
theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H3_R1.H1 := by
  intro hyes hno n hcomp hsqf hodd hnot3 hn4 _ hmixed hcard3 hge hstrong hnormal hex
  obtain ⟨k, hk, hkcard, hkcard1, hsum⟩ := hex
  have hn : n ≠ 0 := by
    intro h
    subst n
    simp at hn4
  have hmod := reciprocal_sum_mod_twentyfour hn hsqf hge hsum
  by_cases hfive : 5 ∈ n.primeFactors
  · have hfilter (p : ℕ) (hp : p ∈ n.primeFactors) : p % 5 ≠ 1 := by
      intro hp1
      apply hnormal 5 hfive p hp
      have h := Nat.div_add_mod p 5
      refine ⟨p / 5, ?_⟩
      omega
    have hbound := card_from_reciprocal_sum hn true hge hfilter hsum
    have h25 := mod_twentyfive_of_five (Nat.pos_of_ne_zero hn) hfive hstrong
    exact hyes n k hcomp hsqf hodd hnot3 hn4 hfive h25 hbound hmixed hcard3 hge hstrong hnormal
      hk hkcard hkcard1 hmod hsum
  · have hfilter (p : ℕ) (hp : p ∈ n.primeFactors) : p ≠ 5 := by
      rintro rfl
      exact hfive hp
    have hbound := card_from_reciprocal_sum hn false hge hfilter hsum
    exact hno n k hcomp hsqf hodd hnot3 hn4 hfive hbound hmixed hcard3 hge hstrong hnormal
      hk hkcard hkcard1 hmod hsum

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H3_R1_H1_R1
