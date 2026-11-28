import OMAStatements.S_oeis_a392208
import Mathlib

namespace OMA.S_oeis_a392208

private def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)

private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * f j * g (n - j)

private def hdivpow (g : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, n + 1 =>
    ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * g (j + 1) * hdivpow g k (n - j)

private def hcomp (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), f k * hdivpow g k n

private lemma egf_injective {f g : ℕ → ℤ} (h : egf f = egf g) : f = g := by
  ext n
  have hn := congr_arg (PowerSeries.coeff n) h
  simp only [egf, PowerSeries.coeff_mk] at hn
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  have hq : (f n : ℚ) = (g n : ℚ) := (div_left_inj' hfac).mp hn
  exact_mod_cast hq

private lemma egf_deriv (f : ℕ → ℤ) :
    PowerSeries.derivative ℚ (egf f) = egf (fun n => f (n + 1)) := by
  ext n
  rw [PowerSeries.coeff_derivative, egf, PowerSeries.coeff_mk, egf, PowerSeries.coeff_mk]
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  field_simp

private lemma egf_mul (f g : ℕ → ℤ) : egf f * egf g = egf (hmul f g) := by
  ext n
  rw [PowerSeries.coeff_mul]
  change ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
    PowerSeries.coeff x.1 (egf f) * PowerSeries.coeff x.2 (egf g) = _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (egf f) * PowerSeries.coeff j (egf g)) n]
  simp only [egf, hmul, PowerSeries.coeff_mk, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hch := Nat.choose_mul_factorial_mul_factorial hjn
  have hchQ : (Nat.choose n j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (n - j) : ℚ) =
      (Nat.factorial n : ℚ) := by exact_mod_cast hch
  have hfj : (Nat.factorial j : ℚ) ≠ 0 := by positivity
  have hfnj : (Nat.factorial (n - j) : ℚ) ≠ 0 := by positivity
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination -(f j : ℚ) * (g (n - j) : ℚ) * hchQ

private lemma hdivpow_zero_of_lt (g : ℕ → ℤ) : ∀ k n, n < k → hdivpow g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ m =>
      simp only [hdivpow]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [ih (m - j) (by omega), mul_zero]

private lemma egf_hdivpow (g : ℕ → ℤ) (hg0 : g 0 = 0) :
    ∀ k : ℕ, egf (hdivpow g k) = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) * (egf g) ^ k := by
  intro k
  induction k with
  | zero =>
    ext n
    cases n <;> simp [egf, hdivpow, PowerSeries.coeff_one]
  | succ k ih =>
    have hderiv : PowerSeries.derivative ℚ (egf (hdivpow g (k + 1))) =
        PowerSeries.derivative ℚ (PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) * (egf g) ^ (k + 1)) := by
      rw [egf_deriv]
      have h1 : egf (fun n => hdivpow g (k + 1) (n + 1)) =
          egf (fun n => g (n + 1)) * egf (hdivpow g k) := by
        rw [egf_mul]
        rfl
      rw [h1, ih, ← egf_deriv]
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero,
        Derivation.leibniz_pow]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
      rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by ext m; simp]
      have hfac : PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) *
          PowerSeries.C ((k + 1 : ℕ) : ℚ) = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) := by
        rw [← map_mul]; congr 1
        rw [Nat.factorial_succ]; push_cast
        have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
        have h2 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
        field_simp
      calc PowerSeries.derivative ℚ (egf g) *
            (PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) * egf g ^ k)
          = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) *
              (egf g ^ k * PowerSeries.derivative ℚ (egf g)) := by ring
        _ = PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) *
              (PowerSeries.C ((k + 1 : ℕ) : ℚ) *
                (egf g ^ k * PowerSeries.derivative ℚ (egf g))) := by
            rw [← hfac]; ring
    ext n
    cases n with
    | zero =>
      simp [egf, hdivpow, hg0, zero_pow (Nat.succ_ne_zero k)]
    | succ m =>
      have h := congr_arg (PowerSeries.coeff m) hderiv
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
      have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hne h

private lemma egf_hasSubst (g : ℕ → ℤ) (hg0 : g 0 = 0) :
    PowerSeries.HasSubst (egf g) := by
  refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
  change PowerSeries.constantCoeff (egf g) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, egf, PowerSeries.coeff_mk, hg0]
  simp

private lemma subst_egf (f g : ℕ → ℤ) (hg0 : g 0 = 0) :
    PowerSeries.subst (egf g) (egf f) = egf (hcomp f g) := by
  have hs := egf_hasSubst g hg0
  ext n
  rw [PowerSeries.coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp only [egf, PowerSeries.coeff_mk, hcomp, Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := congr_arg (PowerSeries.coeff n) (egf_hdivpow g hg0 k)
    rw [PowerSeries.coeff_C_mul, egf, PowerSeries.coeff_mk] at hk
    rw [smul_eq_mul]
    calc (f k : ℚ) / (Nat.factorial k : ℚ) * PowerSeries.coeff n (egf g ^ k)
        = (f k : ℚ) * ((Nat.factorial k : ℚ)⁻¹ * PowerSeries.coeff n (egf g ^ k)) := by ring
      _ = (f k : ℚ) * ((hdivpow g k n : ℚ) / (Nat.factorial n : ℚ)) := by rw [← hk]
      _ = ((f k * hdivpow g k n : ℤ) : ℚ) / (Nat.factorial n : ℚ) := by push_cast; ring
  · intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    by_contra hnot
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hnot
    have hk0 := congr_arg (PowerSeries.coeff n) (egf_hdivpow g hg0 k)
    rw [PowerSeries.coeff_C_mul, egf, PowerSeries.coeff_mk,
      hdivpow_zero_of_lt g k n (by omega), Int.cast_zero, zero_div] at hk0
    have hfac : (Nat.factorial k : ℚ)⁻¹ ≠ 0 := by positivity
    have hpow0 : PowerSeries.coeff n (egf g ^ k) = 0 :=
      (mul_eq_zero.mp hk0.symm).resolve_left hfac
    exact hk (by rw [hpow0, smul_zero])

private lemma exp_eq_egf_one : PowerSeries.exp ℚ = egf (fun _ => 1) := by
  ext n
  rw [PowerSeries.coeff_exp, egf, PowerSeries.coeff_mk, Algebra.algebraMap_self,
    RingHom.id_apply, Int.cast_one]

-- Hurwitz exponential recurrence: E[n+1] = (b' *_H E)[n]
private lemma hexp_succ (b : ℕ → ℤ) (n : ℕ) :
    hcomp (fun _ => 1) b (n + 1) =
      hmul (fun k => b (k + 1)) (hcomp (fun _ => 1) b) n := by
  simp only [hcomp, one_mul, hmul]
  rw [Finset.sum_range_succ']
  simp only [hdivpow, Nat.succ_ne_zero, ↓reduceIte, add_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_subset (Finset.range_mono (show n - j + 1 ≤ n + 1 by omega))]
  intro k hk hnot
  simp only [Finset.mem_range] at hk hnot
  exact hdivpow_zero_of_lt b k (n - j) (by omega)

private lemma hmul_congr_mod2 {f1 f2 g1 g2 : ℕ → ℤ} {N : ℕ}
    (hf : ∀ m ≤ N, f1 m % 2 = f2 m % 2)
    (hg : ∀ m ≤ N, g1 m % 2 = g2 m % 2) :
    ∀ n ≤ N, hmul f1 g1 n % 2 = hmul f2 g2 n % 2 := by
  intro n hn
  simp only [hmul]
  conv_lhs => rw [Finset.sum_int_mod]
  conv_rhs => rw [Finset.sum_int_mod]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 := hf j (by omega)
  have h2 := hg (n - j) (by omega)
  calc ((Nat.choose n j : ℤ) * f1 j * g1 (n - j)) % 2
      = (((Nat.choose n j : ℤ) * f1 j) % 2 * (g1 (n - j) % 2)) % 2 := Int.mul_emod _ _ _
    _ = ((((Nat.choose n j : ℤ) % 2 * (f1 j % 2)) % 2) * (g1 (n - j) % 2)) % 2 := by
          rw [Int.mul_emod (Nat.choose n j : ℤ)]
    _ = ((((Nat.choose n j : ℤ) % 2 * (f2 j % 2)) % 2) * (g2 (n - j) % 2)) % 2 := by rw [h1, h2]
    _ = (((Nat.choose n j : ℤ) * f2 j) % 2 * (g2 (n - j) % 2)) % 2 := by
          rw [← Int.mul_emod (Nat.choose n j : ℤ)]
    _ = ((Nat.choose n j : ℤ) * f2 j * g2 (n - j)) % 2 := (Int.mul_emod _ _ _).symm

private lemma hdivpow_congr_mod2 {g1 g2 : ℕ → ℤ} {N : ℕ}
    (hg : ∀ m ≤ N, g1 m % 2 = g2 m % 2) :
    ∀ k n, n ≤ N → hdivpow g1 k n % 2 = hdivpow g2 k n % 2 := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ m =>
      simp only [hdivpow]
      conv_lhs => rw [Finset.sum_int_mod]
      conv_rhs => rw [Finset.sum_int_mod]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 := hg (j + 1) (by omega)
      have h2 := ih (m - j) (by omega)
      calc ((Nat.choose m j : ℤ) * g1 (j + 1) * hdivpow g1 k (m - j)) % 2
          = (((Nat.choose m j : ℤ) * g1 (j + 1)) % 2 * (hdivpow g1 k (m - j) % 2)) % 2 :=
              Int.mul_emod _ _ _
        _ = ((((Nat.choose m j : ℤ) % 2 * (g1 (j + 1) % 2)) % 2) *
              (hdivpow g1 k (m - j) % 2)) % 2 := by rw [Int.mul_emod (Nat.choose m j : ℤ)]
        _ = ((((Nat.choose m j : ℤ) % 2 * (g2 (j + 1) % 2)) % 2) *
              (hdivpow g2 k (m - j) % 2)) % 2 := by rw [h1, h2]
        _ = (((Nat.choose m j : ℤ) * g2 (j + 1)) % 2 * (hdivpow g2 k (m - j) % 2)) % 2 := by
              rw [← Int.mul_emod (Nat.choose m j : ℤ)]
        _ = ((Nat.choose m j : ℤ) * g2 (j + 1) * hdivpow g2 k (m - j)) % 2 :=
              (Int.mul_emod _ _ _).symm

private lemma hcomp_congr_mod2 {f1 f2 g1 g2 : ℕ → ℤ} {N : ℕ}
    (hf : ∀ m ≤ N, f1 m % 2 = f2 m % 2)
    (hg : ∀ m ≤ N, g1 m % 2 = g2 m % 2) :
    ∀ n ≤ N, hcomp f1 g1 n % 2 = hcomp f2 g2 n % 2 := by
  intro n hn
  simp only [hcomp]
  conv_lhs => rw [Finset.sum_int_mod]
  conv_rhs => rw [Finset.sum_int_mod]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc (f1 k * hdivpow g1 k n) % 2
      = (f1 k % 2 * (hdivpow g1 k n % 2)) % 2 := Int.mul_emod _ _ _
    _ = (f2 k % 2 * (hdivpow g2 k n % 2)) % 2 := by rw [hf k (by omega), hdivpow_congr_mod2 hg k n hn]
    _ = (f2 k * hdivpow g2 k n) % 2 := (Int.mul_emod _ _ _).symm

-- Universal Hurwitz squaring identity mod 2: (f *_H f)[n] ≡ (if n=0 then f(0)^2 else 0) (mod 2)
private lemma even_choose_two_mul (k : ℕ) (hk : 1 ≤ k) :
    2 ∣ Nat.choose (2 * k) k := by
  have h1 : 2 * k = (2 * k - 1) + 1 := by omega
  have h2 : k = (k - 1) + 1 := by omega
  have hsym : Nat.choose (2 * k - 1) k = Nat.choose (2 * k - 1) (k - 1) := by
    have := Nat.choose_symm (show k - 1 ≤ 2 * k - 1 by omega)
    simpa [show 2 * k - 1 - (k - 1) = k by omega] using this
  refine ⟨Nat.choose (2 * k - 1) (k - 1), ?_⟩
  conv_lhs => rw [h1, h2]
  rw [Nat.choose_succ_succ, Nat.succ_eq_add_one, ← h2, hsym]
  ring

private lemma hmul_self_mod2 (f : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    hmul f f n % 2 = 0 := by
  simp only [hmul]
  have hsym : ∀ j ∈ Finset.range (n + 1),
      (Nat.choose n (n - j) : ℤ) * f (n - j) * f (n - (n - j)) =
      (Nat.choose n j : ℤ) * f j * f (n - j) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.choose_symm hjn, Nat.sub_sub_self hjn]; ring
  have h2 : 2 ∣ ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * f j * f (n - j) := by
    set g : ℕ → ℤ := fun j => (Nat.choose n j : ℤ) * f j * f (n - j)
    have hlow_high :
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j < n - j), g j =
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => n - j < j), g j := by
      refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
      · intro j1 hj1 j2 hj2 heq
        simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2; omega
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        exact ⟨n - j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
      · intro j hj
        simp only [Finset.mem_filter] at hj
        exact (hsym j hj.1).symm
    have hsplit : ∑ j ∈ Finset.range (n + 1), g j =
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j < n - j), g j +
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => n - j < j), g j +
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j = n - j), g j := by
      have h1 : Finset.range (n + 1) =
          (Finset.range (n + 1)).filter (fun j => j < n - j) ∪
          (Finset.range (n + 1)).filter (fun j => n - j < j) ∪
          (Finset.range (n + 1)).filter (fun j => j = n - j) := by
        ext j; by_cases hj : j ∈ Finset.range (n + 1) <;> simp [hj]; omega
      conv_lhs => rw [h1]
      rw [Finset.sum_union, Finset.sum_union]
      · exact Finset.disjoint_filter.mpr fun j _ h1 h2 => by omega
      · rw [Finset.disjoint_union_left]
        exact ⟨Finset.disjoint_filter.mpr fun j _ h1 h2 => by omega,
          Finset.disjoint_filter.mpr fun j _ h1 h2 => by omega⟩
    rw [hsplit, ← hlow_high]
    have hmid : 2 ∣ ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j = n - j), g j := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hk1 : 1 ≤ k := by omega
        have hfilt : (Finset.range (n + 1)).filter (fun j => j = n - j) = {k} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
        rw [hfilt, Finset.sum_singleton]
        simp only [g]
        obtain ⟨c, hc⟩ := even_choose_two_mul k hk1
        have hnk : n = 2 * k := by omega
        rw [hnk]
        have hcZ : (Nat.choose (2 * k) k : ℤ) = 2 * (c : ℤ) := by exact_mod_cast hc
        rw [hcZ]
        exact ⟨(c : ℤ) * f k * f (2 * k - k), by ring⟩
      · have hfilt : (Finset.range (n + 1)).filter (fun j => j = n - j) = ∅ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          intro ⟨_, h⟩; omega
        rw [hfilt, Finset.sum_empty]
        exact dvd_zero 2
    obtain ⟨m, hm⟩ := hmid
    exact ⟨(∑ j ∈ (Finset.range (n + 1)).filter (fun j => j < n - j), g j) + m, by linarith⟩
  obtain ⟨q, hq⟩ := h2
  rw [hq]; omega

private lemma hmul_one_left (f : ℕ → ℤ) (n : ℕ) :
    hmul (fun k => if k = 0 then 1 else 0) f n = f n := by
  simp only [hmul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj0; simp [hj0]
  · intro h0; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) h0

-- Target mod-2 sequences: a0 = [0, 1, 1, 0, 1, 1, ...], u = [1, 1, 0, 1, 1, 0, ...]
private def a0 (n : ℕ) : ℤ := if n % 3 = 0 then 0 else 1
private def uSeq (n : ℕ) : ℤ := if n % 3 = 2 then 0 else 1
private def b0 (n : ℕ) : ℤ := if n = 0 then 0 else 1

-- Bell numbers mod 2: hmul (fun _ => 1) uSeq n % 2 = uSeq (n + 1) % 2
private lemma hmul_ones_uSeq_mod2 (n : ℕ) :
    hmul (fun _ => 1) uSeq n % 2 = uSeq (n + 1) % 2 ∧
    hmul (fun _ => 1) (fun k => uSeq (k + 1)) n % 2 = uSeq n % 2 := by
  induction n with
  | zero =>
    simp [hmul, uSeq]
  | succ m ih =>
    have hstep : ∀ g : ℕ → ℤ,
        hmul (fun _ => 1) g (m + 1) =
          hmul (fun _ => 1) g m + hmul (fun _ => 1) (fun k => g (k + 1)) m := by
      intro g
      simp only [hmul, mul_one]
      have h1 : ∑ j ∈ Finset.range (m + 1 + 1), (Nat.choose (m + 1) j : ℤ) * g (m + 1 - j) =
          ∑ j ∈ Finset.range (m + 1 + 1), (Nat.choose (m + 1) j : ℤ) * g j := by
        rw [← Finset.sum_range_reflect (fun j => (Nat.choose (m + 1) j : ℤ) * g j) (m + 1 + 1)]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjm : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [show m + 1 + 1 - 1 - j = m + 1 - j by omega, Nat.choose_symm hjm]
      have h2 : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℤ) * g (m - j) =
          ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℤ) * g j := by
        rw [← Finset.sum_range_reflect (fun j => (Nat.choose m j : ℤ) * g j) (m + 1)]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [show m + 1 - 1 - j = m - j by omega, Nat.choose_symm hjm]
      have h3 : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℤ) * g (m - j + 1) =
          ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℤ) * g (j + 1) := by
        rw [← Finset.sum_range_reflect (fun j => (Nat.choose m j : ℤ) * g (j + 1)) (m + 1)]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [show m + 1 - 1 - j = m - j by omega, Nat.choose_symm hjm]
      rw [h1, h2, h3]
      rw [Finset.sum_range_succ', Finset.sum_range_succ (fun j => (Nat.choose m j : ℤ) * g (j + 1)),
        Finset.sum_range_succ' (fun j => (Nat.choose m j : ℤ) * g j)]
      simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul]
      have hpasc : ∑ j ∈ Finset.range (m + 1), (Nat.choose (m + 1) (j + 1) : ℤ) * g (j + 1) =
          (∑ j ∈ Finset.range m, (Nat.choose (m + 1) (j + 1) : ℤ) * g (j + 1)) +
          g (m + 1) := by
        rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul]
      rw [hpasc]
      have hmid : ∑ j ∈ Finset.range m, (Nat.choose (m + 1) (j + 1) : ℤ) * g (j + 1) =
          (∑ j ∈ Finset.range m, (Nat.choose m j : ℤ) * g (j + 1)) +
          (∑ j ∈ Finset.range m, (Nat.choose m (j + 1) : ℤ) * g (j + 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.choose_succ_succ]; push_cast; ring
      rw [hmid]; ring
    have hu_rec : ∀ k, (uSeq (k + 2)) % 2 = (uSeq k + uSeq (k + 1)) % 2 := by
      intro k; simp only [uSeq]; omega
    constructor
    · rw [hstep uSeq, Int.add_emod, ih.1, ih.2, show m + 1 + 1 = m + 2 by omega]
      have := hu_rec m
      omega
    · rw [hstep (fun k => uSeq (k + 1)), Int.add_emod, ih.2]
      have hshift : hmul (fun _ => 1) (fun k => uSeq (k + 2)) m % 2 =
          (hmul (fun _ => 1) uSeq m + hmul (fun _ => 1) (fun k => uSeq (k + 1)) m) % 2 := by
        have hadd : hmul (fun _ => 1) (fun k => uSeq k + uSeq (k + 1)) m =
            hmul (fun _ => 1) uSeq m + hmul (fun _ => 1) (fun k => uSeq (k + 1)) m := by
          simp only [hmul, mul_one, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [← hadd]
        exact hmul_congr_mod2 (fun _ _ => rfl) (fun k _ => hu_rec k) m le_rfl
      rw [hshift, Int.add_emod (hmul (fun _ => 1) uSeq m), ih.1, ih.2]
      simp only [uSeq]; omega

private lemma hcomp_one_b0_mod2 (n : ℕ) :
    hcomp (fun _ => 1) b0 n % 2 = uSeq n % 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [hcomp, hdivpow, uSeq]
    | succ m =>
      rw [hexp_succ]
      have h1 : hmul (fun k => b0 (k + 1)) (hcomp (fun _ => 1) b0) m % 2 =
          hmul (fun _ => 1) uSeq m % 2 :=
        hmul_congr_mod2 (fun k _ => by simp [b0]) (fun k hk => ih k (by omega)) m le_rfl
      exact h1.trans (hmul_ones_uSeq_mod2 m).1

private theorem main_proved :
    ∀ (a : ℕ → ℤ) (A : PowerSeries ℚ),
      A = PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) →
      a 0 = 0 →
      PowerSeries.derivative ℚ A =
        PowerSeries.subst (A * (PowerSeries.derivative ℚ A) ^ 3) (PowerSeries.exp ℚ) →
      ∀ n : ℕ, 1 ≤ n → (Even (a n) ↔ 3 ∣ n) := by
  intro a A hA ha0 heq
  have hA_egf : A = egf a := hA
  set ap : ℕ → ℤ := fun n => a (n + 1)
  set ap2 : ℕ → ℤ := hmul ap ap
  set ap3 : ℕ → ℤ := hmul ap2 ap
  set b : ℕ → ℤ := hmul a ap3
  have hb0 : b 0 = 0 := by simp [b, hmul, ha0]
  have hrec : ∀ n : ℕ, a (n + 1) = hcomp (fun _ => 1) b n := by
    have hseq : egf ap = egf (hcomp (fun _ => 1) b) := by
      calc egf ap = PowerSeries.derivative ℚ A := by rw [hA_egf, egf_deriv]
        _ = PowerSeries.subst (A * (PowerSeries.derivative ℚ A) ^ 3) (PowerSeries.exp ℚ) := heq
        _ = PowerSeries.subst (egf b) (egf (fun _ => 1)) := by
              rw [hA_egf, egf_deriv, exp_eq_egf_one]
              have hpow3 : (egf ap) ^ 3 = egf ap3 := by
                rw [pow_succ, pow_two, egf_mul, egf_mul]
              rw [hpow3, egf_mul]
        _ = egf (hcomp (fun _ => 1) b) := subst_egf (fun _ => 1) b hb0
    intro n
    exact congr_fun (egf_injective hseq) n
  have ha1 : a 1 = 1 := by
    have := hrec 0
    simpa [hcomp, hdivpow] using this
  have hap2_mod2 : ∀ n, ap2 n % 2 = (if n = 0 then 1 else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ap2, hmul, ap, ha1]
    · simp only [show n ≠ 0 by omega, ↓reduceIte]
      exact hmul_self_mod2 ap n hn
  have hap3_mod2 : ∀ n, ap3 n % 2 = ap n % 2 := by
    intro n
    have h1 : hmul ap2 ap n % 2 = hmul (fun k => if k = 0 then 1 else 0) ap n % 2 :=
      hmul_congr_mod2 (fun k _ => by rw [hap2_mod2 k]; split_ifs <;> rfl) (fun _ _ => rfl) n le_rfl
    rwa [hmul_one_left] at h1
  -- Key identity: hmul a0 uSeq n % 2 = b0 n % 2
  have ha0_mul_u : ∀ n, hmul a0 uSeq n % 2 = b0 n % 2 := by
    intro n
    have ha0_eq : ∀ k, a0 k % 2 = (uSeq k + uSeq (k + 1)) % 2 := by
      intro k; simp only [a0, uSeq]; omega
    have h1 : hmul a0 uSeq n % 2 =
        (hmul uSeq uSeq n + hmul (fun k => uSeq (k + 1)) uSeq n) % 2 := by
      have hadd : hmul (fun k => uSeq k + uSeq (k + 1)) uSeq n =
          hmul uSeq uSeq n + hmul (fun k => uSeq (k + 1)) uSeq n := by
        simp only [hmul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [← hadd]
      exact hmul_congr_mod2 (fun k _ => ha0_eq k) (fun _ _ => rfl) n le_rfl
    have h2 : hmul (fun k => uSeq (k + 1)) uSeq n % 2 = 1 := by
      have h3 : hmul (fun k => uSeq (k + 1)) uSeq n % 2 =
          hmul (hmul (fun _ => 1) uSeq) uSeq n % 2 :=
        hmul_congr_mod2 (fun k _ => (hmul_ones_uSeq_mod2 k).1.symm) (fun _ _ => rfl) n le_rfl
      have hassoc : hmul (hmul (fun _ => 1) uSeq) uSeq n =
          hmul (fun _ => 1) (hmul uSeq uSeq) n := by
        have hmul_assoc : egf (hmul (hmul (fun _ => 1) uSeq) uSeq) =
            egf (hmul (fun _ => 1) (hmul uSeq uSeq)) := by
          rw [← egf_mul, ← egf_mul, ← egf_mul, ← egf_mul, mul_assoc]
        exact congr_fun (egf_injective hmul_assoc) n
      rw [h3, hassoc]
      have h4 : hmul (fun _ => 1) (hmul uSeq uSeq) n % 2 =
          hmul (fun _ => 1) (fun k => if k = 0 then 1 else 0) n % 2 :=
        hmul_congr_mod2 (fun _ _ => rfl) (fun k _ => by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp [hmul, uSeq]
          · simp only [show k ≠ 0 by omega, ↓reduceIte, Int.zero_emod]
            exact hmul_self_mod2 uSeq k hk) n le_rfl
      have hcomm : hmul (fun _ => 1) (fun k => if k = 0 then 1 else 0) n = 1 := by
        have : egf (hmul (fun _ => 1) (fun k => if k = 0 then 1 else 0)) =
            egf (hmul (fun k => if k = 0 then 1 else 0) (fun _ => 1)) := by
          rw [← egf_mul, ← egf_mul, mul_comm]
        rw [congr_fun (egf_injective this) n, hmul_one_left]
      rw [h4, hcomm]; rfl
    rw [h1, Int.add_emod, h2]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hmul, uSeq, b0]
    · rw [hmul_self_mod2 uSeq n hn]; simp [b0, show n ≠ 0 by omega]
  -- Strong induction: a n % 2 = a0 n % 2
  have hmod2 : ∀ n : ℕ, a n % 2 = a0 n % 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | m
      · simp [ha0, a0]
      · simp [ha1, a0]
      · -- n = m + 2: a(m+2) = hcomp 1 b (m+1), which depends on b(0..m+1)
        -- b(k) = hmul a ap3 k, where a(0) = 0 so only a(1..k) and ap3(0..k-1) matter!
        have hb_mod2 : ∀ k ≤ m + 1, b k % 2 = b0 k % 2 := by
          intro k hk
          rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · simp [hb0, b0]
          · have hstep1 : b k % 2 = hmul a ap k % 2 :=
              hmul_congr_mod2 (fun _ _ => rfl) (fun j _ => hap3_mod2 j) k le_rfl
            have hstep2 : hmul a ap k % 2 = hmul a0 uSeq k % 2 := by
              simp only [hmul]
              conv_lhs => rw [Finset.sum_int_mod]
              conv_rhs => rw [Finset.sum_int_mod]
              congr 1
              refine Finset.sum_congr rfl fun j hj => ?_
              have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              rcases Nat.eq_zero_or_pos j with rfl | hjpos
              · simp [ha0, a0]
              · have ha_j : a j % 2 = a0 j % 2 := ih j (by omega)
                have hap_kj : ap (k - j) % 2 = uSeq (k - j) % 2 := by
                  have := ih (k - j + 1) (by omega)
                  have ha0_u : a0 (k - j + 1) = uSeq (k - j) := by
                    simp only [a0, uSeq]; split_ifs <;> omega
                  simpa [ap, ha0_u] using this
                calc ((Nat.choose k j : ℤ) * a j * ap (k - j)) % 2
                    = (((Nat.choose k j : ℤ) * a j) % 2 * (ap (k - j) % 2)) % 2 :=
                        Int.mul_emod _ _ _
                  _ = ((((Nat.choose k j : ℤ) % 2 * (a j % 2)) % 2) * (ap (k - j) % 2)) % 2 := by
                        rw [Int.mul_emod (Nat.choose k j : ℤ)]
                  _ = ((((Nat.choose k j : ℤ) % 2 * (a0 j % 2)) % 2) * (uSeq (k - j) % 2)) % 2 := by
                        rw [ha_j, hap_kj]
                  _ = (((Nat.choose k j : ℤ) * a0 j) % 2 * (uSeq (k - j) % 2)) % 2 := by
                        rw [← Int.mul_emod (Nat.choose k j : ℤ)]
                  _ = ((Nat.choose k j : ℤ) * a0 j * uSeq (k - j)) % 2 :=
                        (Int.mul_emod _ _ _).symm
            exact hstep1.trans (hstep2.trans (ha0_mul_u k))
        rw [hrec (m + 1)]
        have hcomp_m := hcomp_congr_mod2 (f1 := fun _ => 1) (f2 := fun _ => 1)
          (fun _ _ => rfl) hb_mod2 (m + 1) le_rfl
        have htarget : uSeq (m + 1) = a0 (m + 2) := by
          simp only [uSeq, a0]; split_ifs <;> omega
        rw [hcomp_m, hcomp_one_b0_mod2 (m + 1), htarget]
  intro n _
  have hm := hmod2 n
  simp only [a0] at hm
  rw [Int.even_iff]
  split_ifs at hm with h3
  · constructor
    · intro _; exact Nat.dvd_of_mod_eq_zero h3
    · intro _; omega
  · constructor
    · intro hev; omega
    · intro hdvd; exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h3

end OMA.S_oeis_a392208

theorem OMA.solution : type_of% @OMA.S_oeis_a392208.main :=
  OMA.S_oeis_a392208.main_proved
