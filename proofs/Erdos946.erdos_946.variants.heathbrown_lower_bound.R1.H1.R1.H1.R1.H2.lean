import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1
import Mathlib

/-! Counting divisibility by large prime squares in affine forms. -/

open scoped BigOperators
open Filter

namespace Erdos946SquareFactorCount

/-- Two hits of divisibility by the same coprime modulus differ by a multiple of it. -/
lemma modulus_dvd_sub {a b q m n : ℕ} (hc : a.Coprime q) (hmn : m ≤ n)
    (hm : q ∣ a * m + b) (hn : q ∣ a * n + b) : q ∣ n - m := by
  have heq : (a * m + b) + a * (n - m) = a * n + b := by
    rw [Nat.add_right_comm, ← Nat.mul_add, Nat.add_sub_of_le hmn]
  have hsum : q ∣ (a * m + b) + a * (n - m) := by rwa [heq]
  exact hc.symm.dvd_of_dvd_mul_left ((Nat.dvd_add_iff_right hm).mpr hsum)

/-- A fixed coprime modulus has at most `N / q + 1` hits in `[1, N]`. -/
theorem card_dvd_affine_le {a b q N : ℕ} (hq : 0 < q) (hc : a.Coprime q) :
    ((Finset.Icc 1 N).filter (fun n => q ∣ a * n + b)).card ≤ N / q + 1 := by
  let S := (Finset.Icc 1 N).filter (fun n => q ∣ a * n + b)
  change S.card ≤ N / q + 1
  rw [← Finset.card_range (N / q + 1)]
  have injective_on_hits (m n : ℕ) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≤ n)
      (he : m / q = n / q) : m = n := by
    have hd := modulus_dvd_sub hc hmn (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hn).2
    have hmdecomp := Nat.mod_add_div m q
    have hndecomp := Nat.mod_add_div n q
    rw [he] at hmdecomp
    have hmod := Nat.mod_lt n hq
    have hlt : n - m < q := by omega
    by_contra hne
    have hpos : 0 < n - m := by omega
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos hd)
  apply Finset.card_le_card_of_injOn (fun n => n / q)
  · intro n hn
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2)
  · intro m hm n hn he
    rcases le_total m n with hmn | hnm
    · exact injective_on_hits m n hm hn hmn he
    · exact (injective_on_hits n m hn hm hnm he.symm).symm

/-- For a prime greater than the positive slope, there are at most `N / p² + 1` hits. -/
theorem card_prime_square_dvd_affine_le {a b p N : ℕ} (ha : 0 < a) (hp : p.Prime) (hap : a < p) :
    ((Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b)).card ≤ N / p ^ 2 + 1 := by
  have hpa : ¬p ∣ a := fun h => hap.not_ge (Nat.le_of_dvd ha h)
  exact card_dvd_affine_le (pow_pos hp.pos _) (hp.coprime_pow_of_not_dvd hpa)

/-- Union bound for a finite set of forbidden prime squares. -/
theorem card_bad_for_primes_le {a b N : ℕ} (ha : 0 < a) {P : Finset ℕ}
    (hp : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, a < p) :
    ((Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ a * n + b)).card ≤
      ∑ p ∈ P, (N / p ^ 2 + 1) := by
  classical
  let S (p : ℕ) := (Finset.Icc 1 N).filter (fun n => p ^ 2 ∣ a * n + b)
  have heq : (Finset.Icc 1 N).filter (fun n => ∃ p ∈ P, p ^ 2 ∣ a * n + b) = P.biUnion S := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion, S]
    tauto
  rw [heq]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun p hpP => card_prime_square_dvd_affine_le ha (hp p hpP) (hap p hpP))

private lemma inverse_square_tail_le (B T : ℕ) (hB : 0 < B) :
    (∑ p ∈ Finset.Ioc B T, 1 / (p : ℝ) ^ 2) ≤ 1 / (B : ℝ) := by
  let shift : ℕ ↪ ℕ := ⟨fun k => B + k + 1, by
    intro x y h
    change B + x + 1 = B + y + 1 at h
    omega⟩
  have hIoc : (Finset.range (T - B)).map shift = Finset.Ioc B T := by
    ext p
    simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ioc]
    change (∃ k : ℕ, k < T - B ∧ B + k + 1 = p) ↔ B < p ∧ p ≤ T
    exact ⟨by rintro ⟨k, hk, rfl⟩; omega, fun hp => ⟨p - B - 1, by omega, by omega⟩⟩
  rw [← hIoc, Finset.sum_map]
  change (∑ k ∈ Finset.range (T - B), 1 / ((B + k + 1 : ℕ) : ℝ) ^ 2) ≤ _
  let f (k : ℕ) : ℝ := 1 / ((B + k : ℕ) : ℝ)
  calc
    _ ≤ ∑ k ∈ Finset.range (T - B), (f k - f (k + 1)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      let c : ℝ := ((B + k : ℕ) : ℝ)
      have hc : 0 < c := by dsimp [c]; exact_mod_cast (show 0 < B + k by omega)
      have hshift : ((B + k + 1 : ℕ) : ℝ) = c + 1 := by simp only [Nat.cast_add, Nat.cast_one, c]
      rw [hshift]
      have hf : f (k + 1) = 1 / (c + 1) := by dsimp [f]; rw [← Nat.add_assoc, hshift]
      rw [hf]
      change 1 / (c + 1) ^ 2 ≤ 1 / c - 1 / (c + 1)
      calc
        _ ≤ 1 / (c * (c + 1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        _ = _ := by
          field_simp
          ring
    _ = f 0 - f (T - B) := Finset.sum_range_sub' f _
    _ ≤ 1 / (B : ℝ) := by simpa [f] using sub_le_self (f 0) (show 0 ≤ f (T - B) by dsimp [f]; positivity)

/-- Indices with a prime square divisor of `a * n + b` whose prime exceeds `B`. -/
def largePrimeSquareRows (a b B N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n =>
    ∃ p ∈ (Finset.Ioc B (Nat.sqrt (a * N + b))).filter Nat.Prime, p ^ 2 ∣ a * n + b

theorem mem_largePrimeSquareRows {a b B N n : ℕ} (ha : 0 < a) :
    n ∈ largePrimeSquareRows a b B N ↔
      n ∈ Finset.Icc 1 N ∧ ∃ p, p.Prime ∧ B < p ∧ p ^ 2 ∣ a * n + b := by
  rw [largePrimeSquareRows, Finset.mem_filter]
  refine and_congr_right fun hn => ⟨?_, ?_⟩
  · rintro ⟨p, hp, hd⟩
    obtain ⟨hpi, hp⟩ := Finset.mem_filter.mp hp
    exact ⟨p, hp, (Finset.mem_Ioc.mp hpi).1, hd⟩
  · rintro ⟨p, hp, hBp, hd⟩
    have hpos : 0 < a * n + b := by
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      positivity
    have hupper : a * n + b ≤ a * N + b := by gcongr; exact (Finset.mem_Icc.mp hn).2
    have hcutoff : p ≤ Nat.sqrt (a * N + b) :=
      Nat.le_sqrt'.mpr ((Nat.le_of_dvd hpos hd).trans hupper)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hBp, hcutoff⟩, hp⟩, hd⟩

/-- The total large-prime square loss is bounded by `N / B + sqrt (a * N + b)`. -/
theorem card_largePrimeSquareRows_le {a b B N : ℕ} (ha : 0 < a) (haB : a ≤ B) :
    ((largePrimeSquareRows a b B N).card : ℝ) ≤ N / (B : ℝ) + Nat.sqrt (a * N + b) := by
  let T := Nat.sqrt (a * N + b)
  let P := (Finset.Ioc B T).filter Nat.Prime
  have hP : P ⊆ Finset.Ioc B T := Finset.filter_subset _ _
  have hcount : (largePrimeSquareRows a b B N).card ≤ ∑ p ∈ P, (N / p ^ 2 + 1) :=
    card_bad_for_primes_le ha (fun _ hp => (Finset.mem_filter.mp hp).2)
      (fun _ hp => haB.trans_lt (Finset.mem_Ioc.mp (hP hp)).1)
  have hsum : (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 / (B : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hP (by intros; positivity)).trans
      (inverse_square_tail_le B T (ha.trans_le haB))
  have hcard : P.card ≤ T := by
    calc
      _ ≤ (Finset.Ioc B T).card := Finset.card_le_card hP
      _ ≤ T := by simp
  change ((largePrimeSquareRows a b B N).card : ℝ) ≤ N / (B : ℝ) + T
  calc
    _ ≤ ((∑ p ∈ P, (N / p ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ p ∈ P, ((N : ℝ) * (1 / (p : ℝ) ^ 2) + 1) := by
      push_cast
      refine Finset.sum_le_sum fun p _ => ?_
      have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ 2)
      push_cast at h
      simpa only [mul_one_div] using add_le_add h (le_refl (1 : ℝ))
    _ = (N : ℝ) * (∑ p ∈ P, 1 / (p : ℝ) ^ 2) + P.card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
    _ ≤ (N : ℝ) * (1 / (B : ℝ)) + T :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) (by exact_mod_cast hcard)
    _ = _ := by rw [mul_one_div]

private lemma eventually_pow_log_le {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ (7 : ℕ) ≤ C * x ^ r := by
  have ho : (fun x : ℝ => Real.log x ^ (7 : ℕ)) =o[atTop] (fun x => x ^ r) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (↑(7 : ℕ)) hr
  filter_upwards [(Asymptotics.isLittleO_iff.mp ho) hC, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 ≤ x := zero_le_one.trans hx1.le
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.log_nonneg hx1.le) _),
    abs_of_nonneg (Real.rpow_nonneg hx0 _)] using hx

/-- For fixed coefficients, subsampling to exclude large square divisors loses
`o(x / (log x)^7)` values. -/
theorem square_loss (a b : ℕ) (ha : 0 < a) (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop,
      K * (((Finset.Icc 1 ⌊x⌋₊).filter fun n =>
        ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b).card : ℝ) ≤
      x / (Real.log x)^7 := by
  let A : ℝ := Real.sqrt ((a : ℝ) + b)
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hA : 0 < A := by dsimp [A]; positivity
  have hlarge := (tendsto_rpow_atTop hδ).eventually_ge_atTop (max 2 (a : ℝ))
  have hlogδ := eventually_pow_log_le hδ (show 0 < 1 / (4 * K) by positivity)
  have hloghalf := eventually_pow_log_le (show (0 : ℝ) < 1 / 2 by norm_num)
    (show 0 < 1 / (2 * K * A) by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlarge, hlogδ, hloghalf] with x hx1 hlarge hlogδ hloghalf
  let N := ⌊x⌋₊
  let B := ⌊x ^ δ⌋₊
  let V := (Finset.Icc 1 N).filter fun n =>
    ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b
  have hx : 0 < x := zero_lt_one.trans hx1
  have hxδ : 0 < x ^ δ := Real.rpow_pos_of_pos hx _
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have haB : a ≤ B := Nat.le_floor ((le_max_right _ _).trans hlarge)
  have hBhalf : x ^ δ / 2 ≤ (B : ℝ) := by
    have hxδ2 := (le_max_left (2 : ℝ) (a : ℝ)).trans hlarge
    have hceil : x ^ δ < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hB : 0 < (B : ℝ) := (div_pos hxδ (by norm_num)).trans_le hBhalf
  have hV : V ⊆ largePrimeSquareRows a b B N := by
    intro n hn
    obtain ⟨hn, p, hp, hpx, hd⟩ := Finset.mem_filter.mp hn
    have hBp : (B : ℝ) < p := (Nat.floor_le hxδ.le).trans_lt hpx
    exact (mem_largePrimeSquareRows ha).mpr
      ⟨hn, p, Nat.prime_of_mem_primeFactors hp, by exact_mod_cast hBp, hd⟩
  have hcard : (V.card : ℝ) ≤ N / (B : ℝ) + Nat.sqrt (a * N + b) :=
    (show (V.card : ℝ) ≤ (largePrimeSquareRows a b B N).card by
      exact_mod_cast Finset.card_le_card hV).trans (card_largePrimeSquareRows_le ha haB)
  have hquot : (N : ℝ) / (B : ℝ) ≤ 2 * x / (x ^ δ) := by
    calc
      _ ≤ x / (B : ℝ) := div_le_div_of_nonneg_right hN hB.le
      _ ≤ x / (x ^ δ / 2) := div_le_div_of_nonneg_left hx.le (by positivity) hBhalf
      _ = _ := by field_simp [hxδ.ne']
  have hsqrt : (Nat.sqrt (a * N + b) : ℝ) ≤ A * Real.sqrt x := by
    calc
      _ ≤ Real.sqrt ((a * N + b : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt (((a : ℝ) + b) * x) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith only [mul_le_mul_of_nonneg_left hN haR.le,
          mul_le_mul_of_nonneg_left hx1.le (Nat.cast_nonneg b)]
      _ = _ := Real.sqrt_mul (by positivity) x
  have hlogpos : 0 < Real.log x ^ (7 : ℕ) := pow_pos (Real.log_pos hx1) _
  have htermδ : K * (2 * x / x ^ δ) * Real.log x ^ (7 : ℕ) ≤ x / 2 := by
    calc
      _ ≤ (K * (2 * x / x ^ δ)) * (1 / (4 * K) * x ^ δ) :=
        mul_le_mul_of_nonneg_left hlogδ (by positivity)
      _ = _ := by
        field_simp [hK.ne', hxδ.ne']
        ring
  have htermsqrt : K * (A * Real.sqrt x) * Real.log x ^ (7 : ℕ) ≤ x / 2 := by
    rw [← Real.sqrt_eq_rpow] at hloghalf
    calc
      _ ≤ (K * (A * Real.sqrt x)) * (1 / (2 * K * A) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hloghalf (by positivity)
      _ = (K * A * (1 / (2 * K * A))) * (Real.sqrt x * Real.sqrt x) := by ring
      _ = _ := by
        rw [Real.mul_self_sqrt hx.le]
        field_simp [hK.ne', hA.ne']
  change K * (V.card : ℝ) ≤ x / Real.log x ^ (7 : ℕ)
  apply (le_div_iff₀ hlogpos).mpr
  calc
    _ ≤ K * (2 * x / (x ^ δ) + A * Real.sqrt x) * Real.log x ^ (7 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hcard.trans (add_le_add hquot hsqrt)) hK.le) hlogpos.le
    _ ≤ x := by
      rw [mul_add, add_mul]
      exact (add_le_add htermδ htermsqrt).trans_eq (by ring)

end Erdos946SquareFactorCount

theorem OMA.solution : OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1.H2 :=
  Erdos946SquareFactorCount.square_loss
