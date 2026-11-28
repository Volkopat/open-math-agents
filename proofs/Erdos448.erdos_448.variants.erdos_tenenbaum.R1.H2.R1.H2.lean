import OMAReductions.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1

/-! Proof of `Erdos448.erdos_448.variants.erdos_tenenbaum.R1.H2.R1.H2` with explicit
constant `K = 3072` via `d = a^2 * b^3`, `τ(d)^4 ≤ 512^4 * d`, and telescoping sums. -/

open Filter Finset Real
open scoped Topology

private def IsPow2 (d : ℕ) : Prop :=
  0 < d ∧ ∀ p : ℕ, p.Prime → p ∣ d → p ^ 2 ∣ d

private lemma pow2_sq_cube {d : ℕ} :
    IsPow2 d → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ d = a ^ 2 * b ^ 3 := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => rintro ⟨h, -⟩; omega
  | one => intro _; exact ⟨1, 1, one_pos, one_pos, rfl⟩
  | prime_pow p k hp hk =>
    rintro ⟨-, hpow⟩
    have hk2 : 2 ≤ k :=
      (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 (hpow p hp (dvd_pow_self p hk.ne'))
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨p ^ j, 1, pow_pos hp.pos j, one_pos, ?_⟩
      rw [← two_mul, pow_mul]; ring
    · refine ⟨p ^ (j - 1), p, pow_pos hp.pos _, hp.pos, ?_⟩
      rw [← pow_mul, ← pow_add]; congr 1; omega
  | coprime u v hu hv huv ihu ihv =>
    rintro ⟨-, hpow⟩
    have hu2 : IsPow2 u := ⟨zero_lt_one.trans hu, fun p hp hpu =>
      ((huv.coprime_dvd_left hpu).pow_left 2).dvd_of_dvd_mul_right
        (hpow p hp (dvd_mul_of_dvd_left hpu v))⟩
    have hv2 : IsPow2 v := ⟨zero_lt_one.trans hv, fun p hp hpv =>
      ((huv.symm.coprime_dvd_left hpv).pow_left 2).dvd_of_dvd_mul_left
        (hpow p hp (dvd_mul_of_dvd_right hpv u))⟩
    obtain ⟨a₁, b₁, ha₁, hb₁, rfl⟩ := ihu hu2
    obtain ⟨a₂, b₂, ha₂, hb₂, rfl⟩ := ihv hv2
    exact ⟨a₁ * a₂, b₁ * b₂, mul_pos ha₁ ha₂, mul_pos hb₁ hb₂, by ring⟩

private lemma pow4_le_64_two_pow (k : ℕ) : (k + 1) ^ 4 ≤ 64 * 2 ^ k := by
  by_cases hk : k < 6
  · interval_cases k <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    clear hk
    induction m with
    | zero => decide
    | succ m ih =>
      have hstep : (m + 1 + 6 + 1) ^ 4 +
          (m ^ 4 + 24 * m ^ 3 + 204 * m ^ 2 + 696 * m + 706) = 2 * (m + 6 + 1) ^ 4 := by ring
      have hpow : 64 * 2 ^ (m + 1 + 6) = 2 * (64 * 2 ^ (m + 6)) := by
        rw [show m + 1 + 6 = (m + 6) + 1 by omega, pow_succ]; ring
      omega

private def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

private def weight (d : ℕ) : ℕ :=
  ∏ _p ∈ smallPrimes.filter (· ∣ d), 64

private lemma divisors_pow4_le_weight {d : ℕ} :
    0 < d → d.divisors.card ^ 4 ≤ weight d * d := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one => intro _; decide
  | prime_pow p k hp hk =>
    intro _
    rw [Nat.divisors_prime_pow hp, card_map, card_range]
    by_cases hp16 : 16 ≤ p
    · have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      have h2 : (k + 1) ^ 4 ≤ 16 ^ k :=
        (Nat.pow_le_pow_left h1 4).trans_eq (by rw [← pow_mul, mul_comm, pow_mul]; norm_num)
      have h3 : 16 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp16 k
      have hw : 1 ≤ weight (p ^ k) := one_le_prod' fun _ _ => by decide
      exact (h2.trans h3).trans (Nat.le_mul_of_pos_left _ hw)
    · have hmem : p ∈ smallPrimes.filter (· ∣ p ^ k) := by
        refine mem_filter.2 ⟨?_, dvd_pow_self p hk.ne'⟩
        have := hp.two_le
        interval_cases p <;> first | decide | exact absurd hp (by decide)
      have hw : 64 ≤ weight (p ^ k) :=
        single_le_prod' (f := fun _ => 64) (fun _ _ => by decide) hmem
      calc (k + 1) ^ 4
          ≤ 64 * 2 ^ k := pow4_le_64_two_pow k
        _ ≤ 64 * p ^ k := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hp.two_le k)
        _ ≤ weight (p ^ k) * p ^ k := Nat.mul_le_mul_right _ hw
  | coprime u v hu hv huv ihu ihv =>
    intro _
    have hprime : ∀ p ∈ smallPrimes, p.Prime := by decide
    have hunion : smallPrimes.filter (· ∣ u * v) =
        smallPrimes.filter (· ∣ u) ∪ smallPrimes.filter (· ∣ v) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hd⟩
        rcases (hprime p hp).dvd_mul.1 hd with hdu | hdv
        · exact Or.inl ⟨hp, hdu⟩
        · exact Or.inr ⟨hp, hdv⟩
      · rintro (⟨hp, hdu⟩ | ⟨hp, hdv⟩)
        · exact ⟨hp, dvd_mul_of_dvd_left hdu v⟩
        · exact ⟨hp, dvd_mul_of_dvd_right hdv u⟩
    have hdisj : Disjoint (smallPrimes.filter (· ∣ u)) (smallPrimes.filter (· ∣ v)) := by
      rw [Finset.disjoint_left]
      intro p hpu hpv
      have hp1 : p ∣ 1 := huv ▸ Nat.dvd_gcd (mem_filter.1 hpu).2 (mem_filter.1 hpv).2
      exact (hprime p (mem_filter.1 hpu).1).not_dvd_one hp1
    have hw : weight (u * v) = weight u * weight v := by
      unfold weight; rw [hunion, prod_union hdisj]
    rw [huv.card_divisors_mul, mul_pow, hw]
    calc u.divisors.card ^ 4 * v.divisors.card ^ 4
        ≤ (weight u * u) * (weight v * v) :=
          Nat.mul_le_mul (ihu (zero_lt_one.trans hu)) (ihv (zero_lt_one.trans hv))
      _ = weight u * weight v * (u * v) := by ring

private lemma divisors_le_512_fourthRoot {d : ℕ} (hd : 0 < d) :
    (d.divisors.card : ℝ) ≤ 512 * √(√(d : ℝ)) := by
  have hcard : weight d ≤ 64 ^ smallPrimes.card := by
    unfold weight
    calc (∏ _ ∈ smallPrimes.filter (· ∣ d), 64)
        = 64 ^ (smallPrimes.filter (· ∣ d)).card := by simp
      _ ≤ 64 ^ smallPrimes.card :=
        Nat.pow_le_pow_right (by decide) (card_le_card (filter_subset _ _))
  have hw512 : weight d ≤ 512 ^ 4 := hcard.trans (by decide)
  have hnat : d.divisors.card ^ 4 ≤ 512 ^ 4 * d :=
    (divisors_pow4_le_weight hd).trans (Nat.mul_le_mul_right d hw512)
  have hreal : ((d.divisors.card : ℝ)) ^ 4 ≤ (512 * √(√(d : ℝ))) ^ 4 := by
    have hsq1 : √(√(d : ℝ)) ^ 2 = √(d : ℝ) := sq_sqrt (sqrt_nonneg _)
    have hsq2 : √(d : ℝ) ^ 2 = (d : ℝ) := sq_sqrt (Nat.cast_nonneg d)
    have hrhs : (512 * √(√(d : ℝ))) ^ 4 = (512 : ℝ) ^ 4 * d := by
      calc (512 * √(√(d : ℝ))) ^ 4
          = (512 : ℝ) ^ 4 * (√(√(d : ℝ)) ^ 2) ^ 2 := by ring
        _ = (512 : ℝ) ^ 4 * d := by rw [hsq1, hsq2]
    rw [hrhs]
    exact_mod_cast hnat
  exact le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (by positivity) hreal

private lemma fourthRoot_sq_cube_le {a b : ℕ} (hb : 0 < b) :
    √(√(((a ^ 2 * b ^ 3 : ℕ) : ℝ))) ≤ √(a : ℝ) * (b : ℝ) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : (((a ^ 2 * b ^ 3 : ℕ) : ℝ)) ≤ (√(a : ℝ) * b) ^ 4 := by
    have hsa : √(a : ℝ) ^ 2 = (a : ℝ) := sq_sqrt (Nat.cast_nonneg a)
    have hlhs : (√(a : ℝ) * b) ^ 4 = (a : ℝ) ^ 2 * (b : ℝ) ^ 4 := by
      calc (√(a : ℝ) * b) ^ 4 = (√(a : ℝ) ^ 2) ^ 2 * (b : ℝ) ^ 4 := by ring
        _ = (a : ℝ) ^ 2 * (b : ℝ) ^ 4 := by rw [hsa]
    rw [hlhs]; push_cast
    have hb34 : (b : ℝ) ^ 3 ≤ (b : ℝ) ^ 4 := by
      simpa [pow_succ] using mul_le_mul_of_nonneg_left hb1 (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ 3)
    exact mul_le_mul_of_nonneg_left hb34 (sq_nonneg _)
  have h2 := sqrt_le_sqrt h1
  rw [show (√(a : ℝ) * b) ^ 4 = ((√(a : ℝ) * b) ^ 2) ^ 2 by ring,
    sqrt_sq (by positivity : (0 : ℝ) ≤ (√(a : ℝ) * b) ^ 2)] at h2
  have h3 := sqrt_le_sqrt h2
  rwa [sqrt_sq (by positivity : (0 : ℝ) ≤ √(a : ℝ) * b)] at h3

private lemma sum_inv_sq_le_two (N : ℕ) :
    ∑ b ∈ Icc 1 N, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 := by
  suffices h : ∀ M : ℕ, 1 ≤ M →
      ∑ b ∈ Icc 1 M, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 - 1 / (M : ℝ) by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have := h N hN
      have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith
  intro M hM
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  clear hM
  induction k with
  | zero => simp; norm_num
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 2)]
    have hstep : (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2 ≤
        1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ) := by
      set x : ℝ := ((k + 1 : ℕ) : ℝ)
      have hx : 0 < x := by positivity
      have hy : ((k + 2 : ℕ) : ℝ) = x + 1 := by simp [x]; ring
      rw [hy, div_sub_div _ _ hx.ne' (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

private lemma sum_inv_mul_sqrt_le_three (N : ℕ) :
    ∑ a ∈ Icc 1 N, (1 : ℝ) / ((a : ℝ) * √(a : ℝ)) ≤ 3 := by
  suffices h : ∀ M : ℕ, 1 ≤ M →
      ∑ a ∈ Icc 1 M, (1 : ℝ) / ((a : ℝ) * √(a : ℝ)) ≤ 3 - 2 / √(M : ℝ) by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have := h N hN
      have hpos : (0 : ℝ) ≤ 2 / √(N : ℝ) := by positivity
      linarith
  intro M hM
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  clear hM
  induction k with
  | zero => simp; norm_num
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 2)]
    have hstep : (1 : ℝ) / (((k + 2 : ℕ) : ℝ) * √((k + 2 : ℕ) : ℝ)) ≤
        2 / √((k + 1 : ℕ) : ℝ) - 2 / √((k + 2 : ℕ) : ℝ) := by
      set x : ℝ := ((k + 1 : ℕ) : ℝ)
      set y : ℝ := ((k + 2 : ℕ) : ℝ)
      have hx : 0 < x := by positivity
      have hy : 0 < y := by positivity
      have hxy : y - x = 1 := by simp [x, y]; ring
      have hsq : (√y - √x) * (√y + √x) = 1 := by
        rw [mul_comm, ← sq_sub_sq, sq_sqrt hy.le, sq_sqrt hx.le, hxy]
      have hle : √x ≤ √y := sqrt_le_sqrt (by linarith)
      have hub : (√y + √x) * √x * √y ≤ 2 * y * √y := by
        have h1 : √y + √x ≤ 2 * √y := by linarith
        have h2 : (√y + √x) * √x ≤ (2 * √y) * √y :=
          mul_le_mul h1 hle (sqrt_nonneg _) (by positivity)
        have h3 : (2 * √y) * √y = 2 * y := by rw [mul_assoc, mul_self_sqrt hy.le]
        exact (mul_le_mul_of_nonneg_right h2 (sqrt_nonneg _)).trans_eq (by rw [h3])
      rw [div_sub_div _ _ (sqrt_pos.2 hx).ne' (sqrt_pos.2 hy).ne']
      have hnum : 2 * √y - √x * 2 = 2 * (√y - √x) := by ring
      rw [hnum, div_le_div_iff₀ (by positivity) (by positivity)]
      calc 1 * (√x * √y) = (√y - √x) * ((√y + √x) * √x * √y) := by
            linear_combination (√x * √y) * hsq.symm
        _ ≤ (√y - √x) * (2 * y * √y) :=
            mul_le_mul_of_nonneg_left hub (sub_nonneg.2 hle)
        _ = 2 * (√y - √x) * (y * √y) := by ring
    linarith

private lemma sum_pow2_fourthRoot_div_le (S : Finset ℕ) (hS : ∀ d ∈ S, IsPow2 d) :
    ∑ d ∈ S, √(√(d : ℝ)) / (d : ℝ) ≤ 6 := by
  classical
  let N := S.sup id
  have hex (d : ℕ) : d ∈ S → ∃ p : ℕ × ℕ, p ∈ Icc 1 N ×ˢ Icc 1 N ∧ d = p.1 ^ 2 * p.2 ^ 3 := by
    intro hd
    obtain ⟨a, b, ha, hb, hab⟩ := pow2_sq_cube (hS d hd)
    have hdN : d ≤ N := le_sup (f := id) hd
    have haN : a ≤ N := by
      have h1 : a ≤ a ^ 2 := Nat.le_self_pow (by decide) a
      have h2 : a ^ 2 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_right _ (pow_pos hb 3)
      omega
    have hbN : b ≤ N := by
      have h1 : b ≤ b ^ 3 := Nat.le_self_pow (by decide) b
      have h2 : b ^ 3 ≤ a ^ 2 * b ^ 3 := Nat.le_mul_of_pos_left _ (pow_pos ha 2)
      omega
    exact ⟨(a, b), mem_product.2 ⟨mem_Icc.2 ⟨ha, haN⟩, mem_Icc.2 ⟨hb, hbN⟩⟩, hab⟩
  let φ (d : ℕ) : ℕ × ℕ := if hd : d ∈ S then (hex d hd).choose else (0, 0)
  have hφ_mem {d : ℕ} (hd : d ∈ S) : φ d ∈ Icc 1 N ×ˢ Icc 1 N := by
    simp only [φ, dif_pos hd]; exact (hex d hd).choose_spec.1
  have hφ_eq {d : ℕ} (hd : d ∈ S) : d = (φ d).1 ^ 2 * (φ d).2 ^ 3 := by
    simp only [φ, dif_pos hd]; exact (hex d hd).choose_spec.2
  have hφ_inj : Set.InjOn φ S := fun d₁ hd₁ d₂ hd₂ heq => by
    rw [hφ_eq hd₁, hφ_eq hd₂, heq]
  have hterm {d : ℕ} (hd : d ∈ S) :
      √(√(d : ℝ)) / (d : ℝ) ≤
        ((1 : ℝ) / (((φ d).1 : ℝ) * √((φ d).1 : ℝ))) * (1 / ((φ d).2 : ℝ) ^ 2) := by
    set a := (φ d).1
    set b := (φ d).2
    have hmem := mem_product.1 (hφ_mem hd)
    have ha : 0 < a := (mem_Icc.1 hmem.1).1
    have hb : 0 < b := (mem_Icc.1 hmem.2).1
    have heqd : d = a ^ 2 * b ^ 3 := hφ_eq hd
    have hub := fourthRoot_sq_cube_le (a := a) hb
    rw [← heqd] at hub
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast (hS d hd).1
    refine (div_le_div_of_nonneg_right hub hd_pos.le).trans ?_
    rw [heqd]
    push_cast
    have hsa : √(a : ℝ) * √(a : ℝ) = (a : ℝ) := mul_self_sqrt (Nat.cast_nonneg a)
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have heq_alg : √(a : ℝ) * (b : ℝ) * ((a : ℝ) * √(a : ℝ) * (b : ℝ) ^ 2) =
        1 * ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) := by
      calc √(a : ℝ) * (b : ℝ) * ((a : ℝ) * √(a : ℝ) * (b : ℝ) ^ 2)
          = (√(a : ℝ) * √(a : ℝ)) * (a : ℝ) * (b : ℝ) ^ 3 := by ring
        _ = 1 * ((a : ℝ) ^ 2 * (b : ℝ) ^ 3) := by rw [hsa]; ring
    exact heq_alg.le
  let g (p : ℕ × ℕ) : ℝ := ((1 : ℝ) / ((p.1 : ℝ) * √(p.1 : ℝ))) * (1 / (p.2 : ℝ) ^ 2)
  calc ∑ d ∈ S, √(√(d : ℝ)) / (d : ℝ)
      ≤ ∑ d ∈ S, g (φ d) :=
        sum_le_sum fun d hd => hterm hd
    _ = ∑ p ∈ S.image φ, g p :=
        (sum_image (f := g) hφ_inj).symm
    _ ≤ ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, g p :=
        sum_le_sum_of_subset_of_nonneg (image_subset_iff.2 fun d hd => hφ_mem hd)
          fun _ _ _ => by dsimp [g]; positivity
    _ = (∑ a ∈ Icc 1 N, (1 : ℝ) / ((a : ℝ) * √(a : ℝ))) *
          (∑ b ∈ Icc 1 N, (1 : ℝ) / (b : ℝ) ^ 2) := by
        dsimp [g]
        rw [Finset.sum_product]
        dsimp only
        rw [← Finset.sum_mul_sum]
    _ ≤ 3 * 2 := mul_le_mul (sum_inv_mul_sqrt_le_three N) (sum_inv_sq_le_two N)
          (sum_nonneg fun _ _ => by positivity) (by norm_num)
    _ = 6 := by norm_num

private lemma ncard_biUnion_le_sum (I : Finset ℕ) (F : ℕ → Set ℕ) :
    (⋃ d ∈ I, F d).ncard ≤ ∑ d ∈ I, (F d).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem OMA.solution :
    OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1.H2 := by
  refine ⟨3072, by norm_num, fun c hc B hB => ?_⟩
  let S : Set ℕ := {n : ℕ | ∃ d m : ℕ, 0 < d ∧
    (∀ p : ℕ, p.Prime → p ∣ d → p ^ 2 ∣ d) ∧ n = d * m ∧ m ∈ B d}
  show S.upperDensity ≤ 3072 * c
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨M, hM_gt⟩ := exists_nat_gt ((18 / δ) ^ 4 + 1)
  have hM1 : 1 ≤ M := by
    have hnn : (0 : ℝ) ≤ (18 / δ) ^ 4 := by positivity
    have : (1 : ℝ) < M := by linarith
    exact_mod_cast this.le
  have hM_pos_real : (0 : ℝ) < M := by exact_mod_cast hM1
  have hM_root : 6 / √(√(M : ℝ)) < δ / 3 := by
    have h18 : 18 / δ < √(√(M : ℝ)) := by
      have h1 : (18 / δ) ^ 4 < (M : ℝ) := by linarith
      have h2 : (18 / δ) ^ 2 < √(M : ℝ) := by
        have hsq : ((18 / δ) ^ 2) ^ 2 = (18 / δ) ^ 4 := by ring
        rw [← hsq] at h1
        exact (lt_sqrt (by positivity)).2 h1
      exact (lt_sqrt (by positivity)).2 h2
    rw [div_lt_iff₀ (sqrt_pos.2 (sqrt_pos.2 hM_pos_real))]
    have heq6 : (δ / 3) * (18 / δ) = 6 := by field_simp [hδ.ne']; ring
    have hmul := mul_lt_mul_of_pos_left h18 (by positivity : (0 : ℝ) < δ / 3)
    linarith
  let P_M := (Icc 1 M).filter (fun d => 0 < d ∧ ∀ p ∈ Icc 2 d, p.Prime → p ∣ d → p ^ 2 ∣ d)
  have hPM_iff (d : ℕ) : d ∈ P_M ↔ d ≤ M ∧ IsPow2 d := by
    simp only [P_M, mem_filter, mem_Icc, IsPow2]
    refine ⟨fun ⟨⟨_, hdM⟩, hd0, hp⟩ => ⟨hdM, hd0, fun p hpr hpd =>
      hp p ⟨hpr.two_le, Nat.le_of_dvd hd0 hpd⟩ hpr hpd⟩,
      fun ⟨hdM, hd0, hp⟩ => ⟨⟨hd0, hdM⟩, hd0, fun p _ hpr hpd => hp p hpr hpd⟩⟩
  let ε : ℝ := δ / (3 * (M + 1))
  have hε : 0 < ε := by positivity
  have hev_d : ∀ d ∈ P_M, ∀ᶠ k : ℕ in atTop,
      (B d).partialDensity Set.univ k < c * d.divisors.card + ε := by
    intro d hd
    have hpow := ((hPM_iff d).1 hd).2
    have hlt : (B d).upperDensity < c * d.divisors.card + ε :=
      lt_of_le_of_lt (hB d hpow.1 hpow.2) (by linarith)
    exact eventually_lt_of_limsup_lt hlt
      (isBoundedUnder_of_eventually_le (a := (1 : ℝ))
        (Eventually.of_forall fun _ => Set.partialDensity_le_one _ _ _))
  have hev_b : ∀ d ∈ P_M, ∀ᶠ b : ℕ in atTop,
      (B d).partialDensity Set.univ (b / d + 1) < c * d.divisors.card + ε := by
    intro d hd
    have hd0 : 0 < d := ((hPM_iff d).1 hd).2.1
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (hev_d d hd)
    refine eventually_atTop.2 ⟨K₀ * d, fun b hb => hK₀ (b / d + 1) ?_⟩
    have : K₀ ≤ b / d := (Nat.le_div_iff_mul_le hd0).2 hb
    omega
  have hev_all : ∀ᶠ b : ℕ in atTop, ∀ d ∈ P_M,
      (B d).partialDensity Set.univ (b / d + 1) < c * d.divisors.card + ε :=
    (Finset.eventually_all (I := P_M)).2 hev_b
  have hev_big : ∀ᶠ b : ℕ in atTop,
      S.partialDensity Set.univ b ≤ 3072 * c + δ := by
    let C_err : ℝ := 1 + (M : ℝ) * (c * M + ε)
    filter_upwards [hev_all, eventually_ge_atTop (max (M + 1) (⌈3 * C_err / δ⌉₊ + 1))] with b hb_all hb_ge
    have hb_pos : 0 < b := lt_of_lt_of_le (Nat.succ_pos M) ((le_max_left _ _).trans hb_ge)
    have hb_real : (0 : ℝ) < b := by exact_mod_cast hb_pos
    let P_tail := (Ioc M b).filter (fun d => 0 < d ∧ ∀ p ∈ Icc 2 d, p.Prime → p ∣ d → p ^ 2 ∣ d)
    have hPtail_iff (d : ℕ) : d ∈ P_tail ↔ M < d ∧ d ≤ b ∧ IsPow2 d := by
      simp only [P_tail, mem_filter, mem_Ioc, mem_Icc, IsPow2]
      refine ⟨fun ⟨⟨hMd, hdb⟩, hd0, hp⟩ => ⟨hMd, hdb, hd0, fun p hpr hpd =>
        hp p ⟨hpr.two_le, Nat.le_of_dvd hd0 hpd⟩ hpr hpd⟩,
        fun ⟨hMd, hdb, hd0, hp⟩ => ⟨⟨hMd, hdb⟩, hd0, fun p _ hpr hpd => hp p hpr hpd⟩⟩
    let smallSet (d : ℕ) : Set ℕ := (fun m => d * m) '' (B d ∩ Set.Iio (b / d + 1))
    let tailSet (d : ℕ) : Set ℕ := (fun m => d * m) '' (Set.Icc 1 (b / d))
    have hsub : (S ∩ Set.univ) ∩ Set.Iio b ⊆
        ({0} : Set ℕ) ∪ (⋃ d ∈ P_M, smallSet d) ∪ (⋃ d ∈ P_tail, tailSet d) := by
      rintro n ⟨⟨⟨d, m, hd0, hdp, rfl, hmB⟩, -⟩, hnb⟩
      change d * m < b at hnb
      have hmd_le : m * d ≤ b := by rw [mul_comm]; exact hnb.le
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exact Or.inl (Or.inl (by simp))
      · by_cases hdM : d ≤ M
        · refine Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨d, (hPM_iff d).2 ⟨hdM, hd0, hdp⟩, m, ⟨hmB, ?_⟩, rfl⟩))
          change m < b / d + 1
          have : m ≤ b / d := (Nat.le_div_iff_mul_le hd0).2 hmd_le
          omega
        · have hdb : d ≤ b := (Nat.le_mul_of_pos_right d hm0).trans hnb.le
          refine Or.inr (Set.mem_iUnion₂.2 ⟨d, (hPtail_iff d).2 ⟨by omega, hdb, hd0, hdp⟩, m, ?_, rfl⟩)
          exact ⟨hm0, (Nat.le_div_iff_mul_le hd0).2 hmd_le⟩
    have hfin_small (d : ℕ) : (smallSet d).Finite :=
      ((Set.finite_Iio _).inter_of_right (B d)).image _
    have hfin_tail (d : ℕ) : (tailSet d).Finite :=
      (Set.finite_Icc _ _).image _
    have hfin_U1 : (⋃ d ∈ P_M, smallSet d).Finite :=
      P_M.finite_toSet.biUnion fun d _ => hfin_small d
    have hfin_U2 : (⋃ d ∈ P_tail, tailSet d).Finite :=
      P_tail.finite_toSet.biUnion fun d _ => hfin_tail d
    have hncard_tot : (((S ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) ≤
        1 + (∑ d ∈ P_M, ((smallSet d).ncard : ℝ)) + (∑ d ∈ P_tail, ((tailSet d).ncard : ℝ)) := by
      have h1 := Set.ncard_le_ncard hsub (((Set.finite_singleton 0).union hfin_U1).union hfin_U2)
      have h2 := Set.ncard_union_le ({0} ∪ ⋃ d ∈ P_M, smallSet d) (⋃ d ∈ P_tail, tailSet d)
      have h3 := Set.ncard_union_le ({0} : Set ℕ) (⋃ d ∈ P_M, smallSet d)
      have h4 := ncard_biUnion_le_sum P_M smallSet
      have h5 := ncard_biUnion_le_sum P_tail tailSet
      have h0 : ({0} : Set ℕ).ncard = 1 := Set.ncard_singleton 0
      have hnat : ((S ∩ Set.univ) ∩ Set.Iio b).ncard ≤
          1 + (∑ d ∈ P_M, (smallSet d).ncard) + (∑ d ∈ P_tail, (tailSet d).ncard) := by omega
      exact_mod_cast hnat
    have hsmall_each (d : ℕ) (hd : d ∈ P_M) :
        ((smallSet d).ncard : ℝ) ≤
          (c * ((d.divisors.card : ℝ) / d) + ε) * b + (c * M + ε) := by
      have hd0 : 0 < d := ((hPM_iff d).1 hd).2.1
      have hdM : d ≤ M := ((hPM_iff d).1 hd).1
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      have hnc : (smallSet d).ncard ≤ ((B d ∩ Set.univ) ∩ Set.Iio (b / d + 1)).ncard := by
        have heq : B d ∩ Set.Iio (b / d + 1) = (B d ∩ Set.univ) ∩ Set.Iio (b / d + 1) := by simp
        rw [← heq]
        exact Set.ncard_image_le ((Set.finite_Iio _).inter_of_right (B d))
      have hpd := hb_all d hd
      have hden_univ : ((Set.univ ∩ Set.Iio (b / d + 1) : Set ℕ).ncard : ℝ) = (b / d + 1 : ℕ) := by
        simp [Set.univ_inter]
      have hnum : (((B d ∩ Set.univ) ∩ Set.Iio (b / d + 1)).ncard : ℝ) ≤
          (c * d.divisors.card + ε) * ((b / d : ℕ) + 1 : ℝ) := by
        unfold Set.partialDensity at hpd
        rw [hden_univ, div_lt_iff₀ (by positivity)] at hpd
        exact_mod_cast hpd.le
      have hbd : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / d := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self b d
      have hd_div_le : (d.divisors.card : ℝ) ≤ M := by
        have hsub_div : d.divisors ⊆ Icc 1 d := fun x hx =>
          mem_Icc.2 ⟨Nat.pos_of_mem_divisors hx, Nat.le_of_dvd hd0 (Nat.dvd_of_mem_divisors hx)⟩
        have hc_div : d.divisors.card ≤ M := (card_le_card hsub_div).trans (by simp [hdM])
        exact_mod_cast hc_div
      have hε_div : ε / d ≤ ε := div_le_self hε.le hd1
      have hstep1 : (((smallSet d).ncard : ℝ)) ≤ (c * d.divisors.card + ε) * ((b : ℝ) / d + 1) :=
        (by exact_mod_cast hnc : ((smallSet d).ncard : ℝ) ≤ _).trans
          (hnum.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
      have hexp : (c * d.divisors.card + ε) * ((b : ℝ) / d + 1) =
          (c * ((d.divisors.card : ℝ) / d) + ε / d) * b + (c * d.divisors.card + ε) := by ring
      rw [hexp] at hstep1
      have hmul_b : (c * ((d.divisors.card : ℝ) / d) + ε / d) * b ≤
          (c * ((d.divisors.card : ℝ) / d) + ε) * b :=
        mul_le_mul_of_nonneg_right (by linarith) hb_real.le
      have hconst_d : c * (d.divisors.card : ℝ) ≤ c * M :=
        mul_le_mul_of_nonneg_left hd_div_le hc
      linarith
    have hPM_card : (P_M.card : ℝ) ≤ M := by
      have : P_M.card ≤ (Icc 1 M).card := card_le_card (filter_subset _ _)
      simp at this
      exact_mod_cast this
    have hPM_div_sum : ∑ d ∈ P_M, (d.divisors.card : ℝ) / d ≤ 3072 := by
      calc ∑ d ∈ P_M, (d.divisors.card : ℝ) / d
          ≤ ∑ d ∈ P_M, (512 * √(√(d : ℝ))) / d :=
            sum_le_sum fun d hd =>
              div_le_div_of_nonneg_right (divisors_le_512_fourthRoot ((hPM_iff d).1 hd).2.1)
                (Nat.cast_nonneg d)
        _ = 512 * ∑ d ∈ P_M, √(√(d : ℝ)) / d := by
            simp_rw [mul_div_assoc, ← mul_sum]
        _ ≤ 512 * 6 := mul_le_mul_of_nonneg_left
            (sum_pow2_fourthRoot_div_le P_M fun d hd => ((hPM_iff d).1 hd).2) (by norm_num)
        _ = 3072 := by norm_num
    have hPM_sum : ∑ d ∈ P_M, ((smallSet d).ncard : ℝ) ≤
        (3072 * c + δ / 3) * b + (M : ℝ) * (c * M + ε) := by
      have h1 : ∑ d ∈ P_M, ((smallSet d).ncard : ℝ) ≤
          ∑ d ∈ P_M, ((c * ((d.divisors.card : ℝ) / d) + ε) * b + (c * M + ε)) :=
        sum_le_sum hsmall_each
      rw [sum_add_distrib, ← sum_mul, sum_add_distrib, ← mul_sum, sum_const, sum_const,
        nsmul_eq_mul, nsmul_eq_mul] at h1
      have hε_sum : (P_M.card : ℝ) * ε ≤ δ / 3 := by
        have hfrac : (P_M.card : ℝ) / ((M : ℝ) + 1) ≤ 1 :=
          (div_le_one (by positivity)).2 (by linarith [hPM_card])
        dsimp [ε]
        calc (P_M.card : ℝ) * (δ / (3 * ((M : ℝ) + 1)))
            = ((P_M.card : ℝ) / ((M : ℝ) + 1)) * (δ / 3) := by field_simp
          _ ≤ 1 * (δ / 3) := mul_le_mul_of_nonneg_right hfrac (by positivity)
          _ = δ / 3 := one_mul _
      have hc_sum : c * (∑ d ∈ P_M, (d.divisors.card : ℝ) / d) ≤ 3072 * c := by
        have := mul_le_mul_of_nonneg_left hPM_div_sum hc
        linarith
      have hpart1 : (c * ∑ d ∈ P_M, (d.divisors.card : ℝ) / d + P_M.card * ε) * b ≤
          (3072 * c + δ / 3) * b :=
        mul_le_mul_of_nonneg_right (by linarith) hb_real.le
      have hpart2 : (P_M.card : ℝ) * (c * M + ε) ≤ (M : ℝ) * (c * M + ε) :=
        mul_le_mul_of_nonneg_right hPM_card (by positivity)
      linarith
    have htail_each (d : ℕ) (hd : d ∈ P_tail) :
        ((tailSet d).ncard : ℝ) ≤ ((1 / √(√(M : ℝ))) * (√(√(d : ℝ)) / d)) * b := by
      obtain ⟨hMd, _, hd0, _⟩ := (hPtail_iff d).1 hd
      have hnc : (tailSet d).ncard ≤ b / d := by
        calc (tailSet d).ncard ≤ (Set.Icc 1 (b / d)).ncard :=
              Set.ncard_image_le (Set.finite_Icc _ _)
          _ = b / d := by rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]; simp
      have hbd : ((tailSet d).ncard : ℝ) ≤ (b : ℝ) / d :=
        (by exact_mod_cast hnc : ((tailSet d).ncard : ℝ) ≤ (b / d : ℕ)).trans <| by
          rw [le_div_iff₀ (by positivity)]
          exact_mod_cast Nat.div_mul_le_self b d
      have hroot : √(√(M : ℝ)) ≤ √(√(d : ℝ)) :=
        sqrt_le_sqrt (sqrt_le_sqrt (by exact_mod_cast hMd.le))
      have hM_pos : 0 < √(√(M : ℝ)) := sqrt_pos.2 (sqrt_pos.2 hM_pos_real)
      have hinv : (1 : ℝ) / d ≤ (1 / √(√(M : ℝ))) * (√(√(d : ℝ)) / d) := by
        have h1 : 1 ≤ √(√(d : ℝ)) / √(√(M : ℝ)) := (one_le_div hM_pos).2 hroot
        calc (1 : ℝ) / d ≤ (√(√(d : ℝ)) / √(√(M : ℝ))) / d :=
              div_le_div_of_nonneg_right h1 (Nat.cast_nonneg d)
          _ = (1 / √(√(M : ℝ))) * (√(√(d : ℝ)) / d) := by ring
      calc ((tailSet d).ncard : ℝ) ≤ (1 / (d : ℝ)) * b := by simpa [one_div, div_eq_inv_mul] using hbd
        _ ≤ ((1 / √(√(M : ℝ))) * (√(√(d : ℝ)) / d)) * b :=
            mul_le_mul_of_nonneg_right hinv hb_real.le
    have htail_sum : ∑ d ∈ P_tail, ((tailSet d).ncard : ℝ) ≤ (δ / 3) * b := by
      calc ∑ d ∈ P_tail, ((tailSet d).ncard : ℝ)
          ≤ ∑ d ∈ P_tail, ((1 / √(√(M : ℝ))) * (√(√(d : ℝ)) / d)) * b :=
            sum_le_sum htail_each
        _ = ((1 / √(√(M : ℝ))) * ∑ d ∈ P_tail, √(√(d : ℝ)) / d) * b := by
            rw [← sum_mul, ← mul_sum]
        _ ≤ ((1 / √(√(M : ℝ))) * 6) * b :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (sum_pow2_fourthRoot_div_le P_tail fun d hd => ((hPtail_iff d).1 hd).2.2)
                (by positivity)) hb_real.le
        _ ≤ (δ / 3) * b := by
            have : (1 / √(√(M : ℝ))) * 6 = 6 / √(√(M : ℝ)) := by ring
            rw [this]
            exact mul_le_mul_of_nonneg_right hM_root.le hb_real.le
    have herr_b : C_err ≤ (δ / 3) * b := by
      have hb_ceil : ⌈3 * C_err / δ⌉₊ + 1 ≤ b := (le_max_right _ _).trans hb_ge
      have hceil : 3 * C_err / δ ≤ (b : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ_of_le (le_refl _) |>.trans hb_ceil))
      rw [div_le_iff₀ hδ] at hceil
      linarith
    unfold Set.partialDensity
    have hden_b : ((Set.univ ∩ Set.Iio b : Set ℕ).ncard : ℝ) = b := by simp [Set.univ_inter]
    rw [hden_b, div_le_iff₀ hb_real]
    dsimp [C_err] at herr_b
    linarith [hncard_tot, hPM_sum, htail_sum, herr_b]
  exact limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (x := (0 : ℝ)) fun _ => by unfold Set.partialDensity; positivity)
    hev_big
