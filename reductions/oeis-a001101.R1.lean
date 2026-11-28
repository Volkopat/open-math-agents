import OMAStatements.S_oeis_a001101

/-!
# Counting Moran numbers in three digit-sum classes

Witno states the conjecture for the counting function. The three classes
below have different congruence restrictions on the prime quotient.
An elementary inversion transfers a positive counting-function limit
to the exact statement about the increasing enumeration.
-/

namespace OMA.R_oeis_a001101_R1

open Filter Topology OMA.S_oeis_a001101
open scoped BigOperators Classical

/-- Digit sums coprime to nine, with prime quotient congruent to one modulo nine. -/
def H1 : Prop :=
  let P (k : ℕ) :=
    let s := (Nat.digits 10 k).sum
    IsMoran k ∧ ¬3 ∣ s ∧ (k / s) % 9 = 1
  ∃ C : ℝ, Tendsto (fun x : ℕ => (Nat.count P x : ℝ) * Real.log x ^ 2 / x) atTop (𝓝 C)

/-- Digit sums divisible by three but not nine, with quotient one modulo three. -/
def H2 : Prop :=
  let P (k : ℕ) :=
    let s := (Nat.digits 10 k).sum
    IsMoran k ∧ 3 ∣ s ∧ ¬9 ∣ s ∧ (k / s) % 3 = 1
  ∃ C : ℝ, Tendsto (fun x : ℕ => (Nat.count P x : ℝ) * Real.log x ^ 2 / x) atTop (𝓝 C)

/-- Digit sums divisible by nine, with no additional congruence on the quotient. -/
def H3 : Prop :=
  let P (k : ℕ) := IsMoran k ∧ 9 ∣ (Nat.digits 10 k).sum
  ∃ C : ℝ, Tendsto (fun x : ℕ => (Nat.count P x : ℝ) * Real.log x ^ 2 / x) atTop (𝓝 C)

/-- A positive lower bound at the conjectured scale. -/
def H4 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℕ in atTop, c ≤ (Nat.count IsMoran x : ℝ) * Real.log x ^ 2 / x

section

private theorem count_to_nth {p : ℕ → Prop} [DecidablePred p] {C : ℝ} (hC : 0 < C)
    (hcount : Tendsto (fun x : ℕ => (Nat.count p x : ℝ) * Real.log x ^ 2 / x)
      atTop (𝓝 C)) :
    Tendsto (fun n : ℕ => (Nat.nth p (n - 1) : ℝ) / (n * Real.log n ^ 2))
      atTop (𝓝 C⁻¹) := by
  have vanishes : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have infinite : (Set.ofPred p).Infinite := by
    intro hf
    let K : ℝ := hf.toFinset.card
    have hK : Tendsto (fun x : ℕ => K * (Real.log x ^ 2 / x)) atTop (𝓝 0) := by
      simpa using (vanishes.comp hnat).const_mul K
    have hbig := hcount.eventually (lt_mem_nhds (show C / 2 < C by linarith))
    have hsmall := hK.eventually (gt_mem_nhds (show 0 < C / 2 by positivity))
    obtain ⟨x, hx, hy⟩ := (hbig.and hsmall).exists
    have hcard : (Nat.count p x : ℝ) ≤ K := by dsimp [K]; exact_mod_cast Nat.count_le_card hf x
    have hle := mul_le_mul_of_nonneg_right hcard
      (show 0 ≤ Real.log (x : ℝ) ^ 2 / x by positivity)
    rw [mul_div_assoc] at hx
    exact (not_lt_of_ge hle) (hy.trans hx)
  let A (n : ℕ) := Nat.nth p (n-1)
  have hA : Tendsto A atTop atTop :=
    (Nat.nth_strictMono infinite).tendsto_atTop.comp (tendsto_sub_atTop_nat 1)
  have hAr : Tendsto (fun n => (A n : ℝ)) atTop atTop := hnat.comp hA
  let L (n : ℕ) := Real.log (A n)
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hAr
  have hvan := vanishes.comp hAr
  let R (n : ℕ) : ℝ := (n : ℝ) * L n ^ 2 / A n
  have hR : Tendsto R atTop (𝓝 C) := by
    have h := (hcount.comp hA).add hvan
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hca : Nat.count p (A n) = n - 1 := Nat.count_nth_of_infinite infinite _
    dsimp [Function.comp_def, R, L]
    rw [hca, Nat.cast_sub hn]
    push_cast
    ring
  have hlogR : Tendsto (fun n => Real.log (R n)) atTop (𝓝 (Real.log C)) :=
    (Real.continuousAt_log hC.ne').tendsto.comp hR
  have hpart : Tendsto (fun n => Real.log (R n) / L n) atTop (𝓝 0) :=
    hlogR.div_atTop hL
  have hloglog : Tendsto (fun n => Real.log (L n) / L n) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp hL
  have hratio : Tendsto (fun n : ℕ => Real.log n / L n) atTop (𝓝 1) := by
    have h := (hpart.add_const (1 : ℝ)).sub (hloglog.const_mul 2)
    simp only [zero_add, mul_zero, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ), hAr.eventually_gt_atTop 1] with n hn hAn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hAn' : (0 : ℝ) < A n := zero_lt_one.trans hAn
    have hLpos : 0 < L n := Real.log_pos hAn
    have hlogD : Real.log (R n) = Real.log n + 2 * Real.log (L n) - L n := by
      unfold R
      rw [Real.log_div (mul_ne_zero hn'.ne' (pow_ne_zero _ hLpos.ne')) hAn'.ne',
        Real.log_mul hn'.ne' (pow_ne_zero _ hLpos.ne'), Real.log_pow]
      rfl
    rw [hlogD]
    field_simp [hLpos.ne']
    ring
  have hfinal := (hR.mul (hratio.pow 2)).inv₀ (by simpa using hC.ne' : C * 1 ^ 2 ≠ 0)
  simp only [one_pow, mul_one] at hfinal
  apply hfinal.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ), hAr.eventually_gt_atTop 1] with n hn hAn
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hL0 : L n ≠ 0 := (Real.log_pos hAn).ne'
  have hA0 : (A n : ℝ) ≠ 0 := (zero_lt_one.trans hAn).ne'
  have hn0 : (n : ℝ) ≠ 0 := (zero_lt_one.trans hnreal).ne'
  have hl0 : Real.log n ≠ 0 := (Real.log_pos hnreal).ne'
  unfold R
  field_simp [hL0, hA0, hn0, hl0]
  ring

private theorem quotient_mod {k : ℕ} (hk : IsMoran k) :
    let s := (Nat.digits 10 k).sum
    (¬3 ∣ s → (k / s) % 9 = 1) ∧
    (3 ∣ s → ¬9 ∣ s → (k / s) % 3 = 1) := by
  let s := (Nat.digits 10 k).sum
  let p := k / s
  have hprod : s * p = k := by
    simpa [s, p, mul_comm] using Nat.div_mul_cancel hk.2.1
  have hmod : s * p ≡ s * 1 [MOD 9] := by
    rw [hprod, mul_one]
    exact Nat.modEq_nine_digits_sum k
  constructor
  · intro hs
    have hcop : Nat.gcd 9 s = 1 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hs).pow_left 2
    have hp := hmod.cancel_left_of_coprime hcop
    exact hp
  · intro hs hs9
    obtain ⟨d, hd⟩ := hs
    have hd3 : ¬3 ∣ d := by
      rintro ⟨r, rfl⟩
      apply hs9
      exact ⟨r, by rw [hd]; ring⟩
    have hmod' : 3 * (d * p) ≡ 3 * (d * 1) [MOD 3 * 3] := by
      simpa only [← mul_assoc, ← hd] using hmod
    have hmod'' := hmod'.mul_left_cancel' (by decide : (3 : ℕ) ≠ 0)
    have hp := hmod''.cancel_left_of_coprime (Nat.prime_three.coprime_iff_not_dvd.mpr hd3)
    exact hp

/-- Count Moran numbers with a condition on the digit sum and prime quotient. -/
theorem count_by_prime_quotient (R : ℕ → ℕ → Prop) (x : ℕ) :
    Nat.count (fun k => let s := (Nat.digits 10 k).sum
      IsMoran k ∧ R s (k / s)) x =
    ∑ s ∈ Finset.Icc 1 (9 * (Nat.digits 10 x).length),
      Nat.count (fun p => p.Prime ∧ (Nat.digits 10 (s * p)).sum = s ∧ R s p)
        ((x - 1) / s + 1) := by
  let D (k : ℕ) := (Nat.digits 10 k).sum
  let A : Finset ℕ := (Finset.range x).filter (fun k => IsMoran k ∧ R (D k) (k / D k))
  have hD (k : ℕ) (hk : k ∈ A) : D k ∈ Finset.Icc 1 (9 * (Nat.digits 10 x).length) := by
    have hk' : k < x ∧ (IsMoran k ∧ R (D k) (k / D k)) := by simpa [A] using hk
    have hpos : 1 ≤ D k := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      have hprime := hk'.2.1.2.2
      change (k / D k).Prime at hprime
      exact Nat.not_prime_zero (by simpa [hz] using hprime)
    have hdigs : D k ≤ (Nat.digits 10 k).length * 9 := by
      apply List.sum_le_card_nsmul
      intro d hd
      exact Nat.le_of_lt_succ (Nat.digits_lt_base (by decide) hd)
    have hlen := Nat.le_length_digits_le 10 k x hk'.1.le
    exact Finset.mem_Icc.mpr ⟨hpos, by
      rw [mul_comm 9]
      exact hdigs.trans (Nat.mul_le_mul_right 9 hlen)⟩
  rw [Nat.count_eq_card_filter_range]
  change A.card = _
  rw [Finset.card_eq_sum_card_fiberwise hD]
  apply Finset.sum_congr rfl
  intro s hs
  have hsp : 0 < s := (Finset.mem_Icc.mp hs).1
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij' (fun k _ => k / s) (fun p _ => s * p)
  · intro k hk
    have hk' : (k < x ∧ IsMoran k ∧ R (D k) (k / D k)) ∧ D k = s := by
      simpa [A] using hk
    obtain ⟨⟨hkx, hm, hr⟩, hks⟩ := hk'
    change 1 ≤ k ∧ D k ∣ k ∧ (k / D k).Prime at hm
    rw [hks] at hm hr
    have heq : s * (k / s) = k := by rw [mul_comm, Nat.div_mul_cancel hm.2.1]
    have hcut : k / s ≤ (x - 1) / s := by
      apply (Nat.le_div_iff_mul_le hsp).mpr
      rw [mul_comm, heq]
      omega
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le hcut, hm.2.2, ?_, hr⟩
    rw [heq]
    exact hks
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hp, hds, hr⟩ := hp
    have hds' : D (s * p) = s := hds
    have hquot : s * p / s = p := Nat.mul_div_cancel_left _ hsp
    have hpos : 0 < s * p := Nat.mul_pos hsp hp.pos
    have hcut := (Nat.le_div_iff_mul_le hsp).mp (Nat.le_of_lt_succ hpx)
    have hcut' : s * p < x := by rw [mul_comm] at hcut; omega
    have hm : IsMoran (s * p) := by
      change 1 ≤ s * p ∧ D (s * p) ∣ s * p ∧ (s * p / D (s * p)).Prime
      rw [hds', hquot]
      exact ⟨hpos, dvd_mul_right _ _, hp⟩
    simpa [A, hcut', hm, hds', hquot] using hr
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hm := (Finset.mem_filter.mp hk'.1).2.1
    have hd : D k ∣ k := hm.2.1
    rw [hk'.2] at hd
    exact (mul_comm s _).trans (Nat.div_mul_cancel hd)
  · intro p _
    exact Nat.mul_div_cancel_left _ hsp


private theorem count_split (x : ℕ) :
    Nat.count IsMoran x =
      Nat.count (fun k => let s := (Nat.digits 10 k).sum
        IsMoran k ∧ ¬3 ∣ s ∧ (k / s) % 9 = 1) x +
      Nat.count (fun k => let s := (Nat.digits 10 k).sum
        IsMoran k ∧ 3 ∣ s ∧ ¬9 ∣ s ∧ (k / s) % 3 = 1) x +
      Nat.count (fun k => IsMoran k ∧ 9 ∣ (Nat.digits 10 k).sum) x := by
  induction x with
  | zero => simp
  | succ x ih =>
    simp only [Nat.count_succ]
    rw [ih]
    by_cases h : IsMoran x
    · have hq := quotient_mod h
      by_cases h3 : 3 ∣ (Nat.digits 10 x).sum
      · by_cases h9 : 9 ∣ (Nat.digits 10 x).sum
        · simp [h, h3, h9]
          omega
        · simp [h, h3, h9, hq.2 h3 h9]
          omega
      · have h9 : ¬9 ∣ (Nat.digits 10 x).sum :=
          fun hd => h3 ((by decide : 3 ∣ 9).trans hd)
        simp [h, h3, h9, hq.1 h3]
        omega
    · simp [h]

end

/-- Padding a prime of digit sum `10^k` with `k` zeros produces a Moran number. -/
theorem moran_of_power_digit_sum {k p : ℕ} (hp : p.Prime)
    (hs : (Nat.digits 10 p).sum = 10 ^ k) : IsMoran (10 ^ k * p) := by
  have hsum : (Nat.digits 10 (10 ^ k * p)).sum = 10 ^ k := by
    rw [Nat.digits_base_pow_mul (by decide) hp.pos, List.sum_append]
    simpa using hs
  have hpow : 0 < (10 : ℕ) ^ k := by positivity
  unfold IsMoran
  rw [hsum, Nat.mul_div_cancel_left _ hpow]
  exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hpow.ne' hp.ne_zero), dvd_mul_right _ _, hp⟩

/-- Theorem 1.1 of Drmota, Mauduit and Rivat, DOI 10.1112/S0010437X08003898,
supplies the premise by centering the digit sum at `10^k`. -/
theorem infinite_of_power_digit_primes
    (h : ∀ᶠ k : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).sum = 10 ^ k) :
    (Set.ofPred IsMoran).Infinite := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp h
  apply Set.infinite_of_forall_exists_gt
  intro M
  let k := max K (M + 1)
  obtain ⟨p, hp, hds⟩ := hK k (le_max_left _ _)
  refine ⟨10 ^ k * p, moran_of_power_digit_sum hp hds, ?_⟩
  calc
    M < k := (Nat.lt_succ_self _).trans_le (le_max_right _ _)
    _ < 2 ^ k := Nat.lt_two_pow_self
    _ ≤ 10 ^ k := Nat.pow_le_pow_left (by decide) _
    _ ≤ 10 ^ k * p := Nat.le_mul_of_pos_right _ hp.pos


theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a001101.main := by
  intro h1 h2 h3 h4
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₂, hC₂⟩ := h2
  obtain ⟨C₃, hC₃⟩ := h3
  obtain ⟨c, hc, hlow⟩ := h4
  have htotal : Tendsto (fun x : ℕ => (Nat.count IsMoran x : ℝ) * Real.log x ^ 2 / x)
      atTop (𝓝 (C₁ + C₂ + C₃)) := by
    apply ((hC₁.add hC₂).add hC₃).congr'
    apply Eventually.of_forall
    intro x
    dsimp only
    rw [count_split x, Nat.cast_add, Nat.cast_add]
    ring
  have hC : 0 < C₁ + C₂ + C₃ := hc.trans_le (ge_of_tendsto htotal hlow)
  exact ⟨(C₁ + C₂ + C₃)⁻¹, inv_pos.mpr hC, count_to_nth hC htotal⟩

end OMA.R_oeis_a001101_R1
