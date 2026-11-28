import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1

/-! In the primary Giuga branch with five dividing the candidate, split on seven.
The reciprocal identity bounds the number of distinct prime factors in each
case, and the cofactor identity fixes its residue modulo sixteen in terms of
two residue-class counts. The two remaining nonexistence statements are open. -/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R2

private theorem cofactor_cube : ∀ x y : ZMod 16, (x * y).val % 4 = 1 →
    (x * y) ^ 3 * y = x ^ 3 := by decide

private theorem sum_weights (weight : ZMod 16 → ZMod 16)
    (hunit : weight 1 = 0)
    (weight_mul : ∀ x y : ZMod 16, x.val % 2 = 1 → y.val % 2 = 1 →
      weight (x * y) = weight x + weight y) (s : Finset ℕ) (ho : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, weight (p : ZMod 16)) = weight ((∏ p ∈ s, p : ℕ) : ZMod 16) := by
  induction s using Finset.cons_induction with
  | empty => simp [hunit]
  | cons a s ha ih =>
    have hs : ∀ p ∈ s, Odd p := fun p hp => ho p (Finset.mem_cons_of_mem hp)
    have hprod : Odd (∏ p ∈ s, p) := s.prod_induction id Odd (fun _ _ hx hy => hx.mul hy) (by decide) hs
    rw [Finset.sum_cons, Finset.prod_cons, Nat.cast_mul, ih hs, weight_mul]
    · simp only [ZMod.val_natCast]
      have := Nat.odd_iff.mp (ho a (Finset.mem_cons_self a s))
      omega
    · simp only [ZMod.val_natCast]
      have := Nat.odd_iff.mp hprod
      omega

/-- A necessary condition on the number of factors in the 1 modulo 4 branch
of the primary Giuga identity. The hypothesis on the cofactor sum is the
integer form of the reciprocal identity in the project reduction. -/
theorem factor_count_mod_sixteen {n : ℕ} (hsq : Squarefree n) (hn : n % 4 = 1)
    (hsum : ∑ p ∈ n.primeFactors, n / p = n + 1) :
    (n.primeFactors.card : ZMod 16) = 2 +
      2 * ((n.primeFactors.filter (fun p => p % 4 = 3)).card : ZMod 16) +
      8 * ((n.primeFactors.filter (fun p => p % 8 = 3)).card : ZMod 16) := by
  let weight (x : ZMod 16) : ZMod 16 :=
    x ^ 3 - 1 + (if x.val % 4 = 3 then 2 else 0) +
      (if x.val % 8 = 3 then 8 else 0)
  have weight_mul : ∀ x y : ZMod 16, x.val % 2 = 1 → y.val % 2 = 1 →
      weight (x * y) = weight x + weight y := by
    simp only [weight]
    decide
  have total_cube : ∀ x : ZMod 16, x.val % 4 = 1 →
      x ^ 3 * (x + 1) = weight x + 2 := by
    simp only [weight]
    decide
  have hn' : (n : ZMod 16).val % 4 = 1 := by rw [ZMod.val_natCast]; omega
  have hterm (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n : ZMod 16) ^ 3 * ((n / p : ℕ) : ZMod 16) = (p : ZMod 16) ^ 3 := by
    have h : (p : ZMod 16) * ((n / p : ℕ) : ZMod 16) = (n : ZMod 16) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)]
    have hmod : ((p : ZMod 16) * ((n / p : ℕ) : ZMod 16)).val % 4 = 1 := by rwa [h]
    simpa only [h] using cofactor_cube (p : ZMod 16) ((n / p : ℕ) : ZMod 16) hmod
  have hsum' : (∑ p ∈ n.primeFactors, (p : ZMod 16) ^ 3) = weight n + 2 := by
    calc
      _ = ∑ p ∈ n.primeFactors, (n : ZMod 16) ^ 3 * ((n / p : ℕ) : ZMod 16) :=
        Finset.sum_congr rfl fun p hp => (hterm p hp).symm
      _ = (n : ZMod 16) ^ 3 * (n + 1) := by
        rw [← Finset.mul_sum, ← Nat.cast_sum, hsum, Nat.cast_add, Nat.cast_one]
      _ = _ := total_cube _ hn'
  have ho : Odd n := Nat.odd_iff.mpr (by omega)
  have hw := sum_weights weight (by dsimp only [weight]; decide) weight_mul n.primeFactors fun p hp =>
    ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  rw [Nat.prod_primeFactors_of_squarefree hsq] at hw
  simp only [weight, ZMod.val_natCast] at hw
  simp only [show ∀ p : ℕ, p % 16 % 4 = p % 4 from fun p => by omega,
    show ∀ p : ℕ, p % 16 % 8 = p % 8 from fun p => by omega,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite, mul_one] at hw
  unfold weight at hsum'
  simp only [ZMod.val_natCast, show ∀ p : ℕ, p % 16 % 4 = p % 4 from fun p => by omega,
    show ∀ p : ℕ, p % 16 % 8 = p % 8 from fun p => by omega] at hsum'
  linear_combination hsum' - hw

/-- For each prime below the cutoff, budget its excess over the uniform
contribution. All factors at or above the cutoff cost at most the uniform rate. -/
theorem card_bound (s : Finset ℕ) (T K : ℕ) (ht : 0 < T)
    (a : ℕ → Prop) [DecidablePred a] (ha : ∀ p ∈ s, a p)
    (hs : 1 < ∑ p ∈ s, (1 / (p : ℚ)))
    (hc : (K : ℚ) * (1 / (T : ℚ)) +
      ∑ p ∈ (Finset.range T).filter a, (1 / (p : ℚ) - 1 / (T : ℚ)) ≤ 1)
    (hpos : ∀ p, a p → 0 < p) : K < s.card := by
  by_contra! hk
  have hT : (0 : ℚ) < T := by exact_mod_cast ht
  have hsmall := Finset.sum_le_sum_of_subset_of_nonneg
    (s := s.filter (· < T)) (t := (Finset.range T).filter a)
    (f := fun p : ℕ => 1 / (p : ℚ) - 1 / (T : ℚ))
    (by
      intro p hp
      obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ha p hp⟩)
    (by
      intro p hp _
      obtain ⟨hm, hap⟩ := Finset.mem_filter.mp hp
      exact sub_nonneg.mpr (one_div_le_one_div_of_le (by exact_mod_cast hpos p hap)
        (by exact_mod_cast (Finset.mem_range.mp hm).le)))
  have htotal : (∑ p ∈ s, (1 / (p : ℚ))) ≤ ∑ p ∈ s, (1 / (T : ℚ) +
      if p < T then 1 / (p : ℚ) - 1 / (T : ℚ) else 0) := by
    apply Finset.sum_le_sum
    intro p _
    by_cases h : p < T
    · simp [h]
    · simpa [h] using one_div_le_one_div_of_le hT (by exact_mod_cast Nat.le_of_not_gt h : (T : ℚ) ≤ p)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at htotal
  have hcard := mul_le_mul_of_nonneg_right (show (s.card : ℚ) ≤ K by exact_mod_cast hk)
    (show 0 ≤ 1 / (T : ℚ) by positivity)
  linarith

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1500000 in
theorem seven_certificate : (80 : ℚ) * (1 / 300) +
    ∑ p ∈ (Finset.range 300).filter (fun p => Nat.Prime p ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p % 7 ≠ 1),
      (1 / (p : ℚ) - 1 / 300) ≤ 1 := by
  let ps : List ℕ := [5, 7, 13, 17, 19, 23, 37, 47, 53, 59, 67, 73, 79, 83, 89, 97, 103, 107, 109, 137, 139, 149, 157, 163, 167, 173, 179, 193, 199, 223, 227, 229, 233, 257, 263, 269, 277, 283, 293]
  have listed : (List.range 300).filter (fun p => decide (Nat.Prime p ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p % 7 ≠ 1)) = ps := by
    dsimp only [ps]
    decide
  have hset : (Finset.range 300).filter (fun p => Nat.Prime p ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p % 7 ≠ 1) = ps.toFinset := by
    rw [← listed]
    ext p
    simp
  rw [hset, List.sum_toFinset _ (show ps.Nodup by dsimp only [ps]; decide)]
  norm_num [ps, List.map, List.sum_cons]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1500000 in
theorem no_seven_certificate : (102 : ℚ) * (1 / 300) +
    ∑ p ∈ (Finset.range 300).filter (fun p => Nat.Prime p ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p ≠ 7),
      (1 / (p : ℚ) - 1 / 300) ≤ 1 := by
  let ps : List ℕ := [5, 13, 17, 19, 23, 29, 37, 43, 47, 53, 59, 67, 73, 79, 83, 89, 97, 103, 107, 109, 113, 127, 137, 139, 149, 157, 163, 167, 173, 179, 193, 197, 199, 223, 227, 229, 233, 239, 257, 263, 269, 277, 283, 293]
  have listed : (List.range 300).filter (fun p => decide (Nat.Prime p ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p ≠ 7)) = ps := by
    dsimp only [ps]
    decide
  have hset : (Finset.range 300).filter (fun p => Nat.Prime p ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p ≠ 7) = ps.toFinset := by
    rw [← listed]
    ext p
    simp
  rw [hset, List.sum_toFinset _ (show ps.Nodup by dsimp only [ps]; decide)]
  norm_num [ps, List.map, List.sum_cons]

def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → 5 ∣ n → 7 ∣ n →
    n % 4 = 1 →
    n.primeFactors.card % 4 = 2 → 82 ≤ n.primeFactors.card →
    (n.primeFactors.card : ZMod 16) = 2 +
      2 * ((n.primeFactors.filter (fun p => p % 4 = 3)).card : ZMod 16) +
      8 * ((n.primeFactors.filter (fun p => p % 8 = 3)).card : ZMod 16) →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    False

def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → 5 ∣ n → ¬ 7 ∣ n →
    n % 4 = 1 →
    n.primeFactors.card % 4 = 2 → 106 ≤ n.primeFactors.card →
    (n.primeFactors.card : ZMod 16) = 2 +
      2 * ((n.primeFactors.filter (fun p => p % 4 = 3)).card : ZMod 16) +
      8 * ((n.primeFactors.filter (fun p => p % 8 = 3)).card : ZMod 16) →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    False

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.H1 := by
  intro left right n hc hsq ho h3 h5 hn hk _ hex hr hones hprime hdiv hnormal hsum
  have hsum' : 1 < ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) := by
    have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
    have hpos : (0 : ℚ) < 1 / n := by positivity
    linarith
  have h16 := factor_count_mod_sixteen hsq hn
    (OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.sum_div_eq_add_one (by omega) hsum)
  have hres : n.primeFactors.card % 16 =
      (2 + 2 * (n.primeFactors.filter (fun p => p % 4 = 3)).card +
        8 * (n.primeFactors.filter (fun p => p % 8 = 3)).card) % 16 := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ 16).mp
    push_cast
    exact h16
  have h8 : n.primeFactors.card % 8 = 2 := by
    obtain ⟨v, hv⟩ := hr
    omega
  by_cases h7 : 7 ∣ n
  · have hmem : 7 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h7, by omega⟩
    have hbound := card_bound n.primeFactors 300 80 (by decide)
      (fun p => p.Prime ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p % 7 ≠ 1)
      (by
        intro p hp
        refine ⟨Nat.prime_of_mem_primeFactors hp, (hprime p hp).1, (hprime p hp).2, ?_⟩
        intro hg
        exact hnormal 7 hmem p hp (by omega))
      hsum' seven_certificate (fun _ h => by have := h.2.1; omega)
    exact left n hc hsq ho h3 h5 h7 hn hk (by omega) h16 hex hr hones hprime hdiv hnormal hsum
  · have hbound := card_bound n.primeFactors 300 102 (by decide)
      (fun p => p.Prime ∧ 5 ≤ p ∧ p % 5 ≠ 1 ∧ p ≠ 7)
      (by
        intro p hp
        refine ⟨Nat.prime_of_mem_primeFactors hp, (hprime p hp).1, (hprime p hp).2, ?_⟩
        rintro rfl
        exact h7 (Nat.dvd_of_mem_primeFactors hp))
      hsum' no_seven_certificate (fun _ h => by have := h.2.1; omega)
    exact right n hc hsq ho h3 h5 h7 hn hk (by omega) h16 hex hr hones hprime hdiv hnormal hsum

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R2
