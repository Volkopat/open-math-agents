import OMAStatements.S_oeis_a205572
import Mathlib

namespace OMA.P_oeis_a205572

-- 1. Hurwitz product and shift/difference operators on ℕ → ℤ
private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f k * g (n - k)

private def D (f : ℕ → ℤ) (n : ℕ) : ℤ := f (n + 1)

private def Δ2 (f : ℕ → ℤ) (n : ℕ) : ℤ := f (n + 2) - f n

private lemma hmul_comm (f g : ℕ → ℤ) : hmul f g = hmul g f := by
  funext n
  simp only [hmul]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have h1 : n + 1 - 1 - k = n - k := by omega
  have h2 : n - (n - k) = k := Nat.sub_sub_self hkn
  rw [h1, h2, Nat.choose_symm hkn]; ring

private lemma hmul_assoc (f g h : ℕ → ℤ) : hmul (hmul f g) h = hmul f (hmul g h) := by
  -- Prove via PowerSeries ℚ egf!
  let egf : (ℕ → ℤ) → PowerSeries ℚ := fun u =>
    PowerSeries.mk fun n => (u n : ℚ) / (Nat.factorial n : ℚ)
  have hegf_mul : ∀ u v : ℕ → ℤ, egf u * egf v = egf (hmul u v) := by
    intro u v
    ext n
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (egf u) * PowerSeries.coeff j (egf v))]
    simp only [egf, PowerSeries.coeff_mk, hmul, Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hch : (Nat.choose n k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) =
        (Nat.factorial n : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hfnk : (Nat.factorial (n - k) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
    have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    push_cast
    field_simp [hfk, hfnk, hfn]
    linear_combination (u k : ℚ) * (v (n - k) : ℚ) * hch.symm
  have heq : egf (hmul (hmul f g) h) = egf (hmul f (hmul g h)) := by
    rw [← hegf_mul, ← hegf_mul, ← hegf_mul, ← hegf_mul, mul_assoc]
  funext n
  have hc := congr_arg (PowerSeries.coeff n) heq
  simp only [egf, PowerSeries.coeff_mk] at hc
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hq : (hmul (hmul f g) h n : ℚ) = (hmul f (hmul g h) n : ℚ) :=
    (div_left_inj' hfn).mp hc
  exact_mod_cast hq

private lemma hmul_add_left (f1 f2 g : ℕ → ℤ) :
    hmul (fun k => f1 k + f2 k) g = fun k => hmul f1 g k + hmul f2 g k := by
  funext n; simp only [hmul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma hmul_add_right (f g1 g2 : ℕ → ℤ) :
    hmul f (fun k => g1 k + g2 k) = fun k => hmul f g1 k + hmul f g2 k := by
  funext n; simp only [hmul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma hmul_smul_left (c : ℤ) (f g : ℕ → ℤ) :
    hmul (fun k => c * f k) g = fun k => c * hmul f g k := by
  funext n; simp only [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma hmul_smul_right (c : ℤ) (f g : ℕ → ℤ) :
    hmul f (fun k => c * g k) = fun k => c * hmul f g k := by
  funext n; simp only [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma D_hmul (f g : ℕ → ℤ) :
    D (hmul f g) = fun n => hmul (D f) g n + hmul f (D g) n := by
  funext n
  simp only [D, hmul]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
    Nat.sub_self]
  have hmid : ∑ k ∈ Finset.range n, (Nat.choose (n + 1) (k + 1) : ℤ) * f (k + 1) * g (n + 1 - (k + 1)) =
      (∑ k ∈ Finset.range n, (Nat.choose n k : ℤ) * f (k + 1) * g (n - k)) +
      (∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℤ) * f (k + 1) * g (n - k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ, Nat.succ_sub_succ_eq_sub]
    push_cast; ring
  rw [hmid]
  have h1 : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * g (n - k) =
      (∑ k ∈ Finset.range n, (Nat.choose n k : ℤ) * f (k + 1) * g (n - k)) + f (n + 1) * g 0 := by
    rw [Finset.sum_range_succ]; simp
  have h2 : ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f k * g (n - k + 1) =
      (∑ k ∈ Finset.range n, (Nat.choose n (k + 1) : ℤ) * f (k + 1) * g (n - k)) + f 0 * g (n + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k < n := Finset.mem_range.mp hk
    rw [show n - (k + 1) + 1 = n - k by omega]
  rw [h1, h2]; ring

private lemma D2_hmul (f g : ℕ → ℤ) :
    D (D (hmul f g)) = fun n =>
      hmul (Δ2 f) g n + hmul f (Δ2 g) n + 2 * hmul f g n + 2 * hmul (D f) (D g) n := by
  have h1 : D (D (hmul f g)) = fun n =>
      hmul (D (D f)) g n + 2 * hmul (D f) (D g) n + hmul f (D (D g)) n := by
    rw [D_hmul]
    funext n
    change (hmul (D f) g (n + 1) + hmul f (D g) (n + 1)) = _
    have ha := congr_fun (D_hmul (D f) g) n
    have hb := congr_fun (D_hmul f (D g)) n
    simp only [D] at ha hb
    rw [ha, hb]; ring
  rw [h1]
  funext n
  have hf : D (D f) = fun k => f k + Δ2 f k := by funext k; simp [D, Δ2]
  have hg : D (D g) = fun k => g k + Δ2 g k := by funext k; simp [D, Δ2]
  rw [hf, hg, hmul_add_left, hmul_add_right]
  ring

private lemma D_iter_add (m : ℕ) (f g : ℕ → ℤ) :
    D^[m] (fun k => f k + g k) = fun k => D^[m] f k + D^[m] g k := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih]; funext k; simp [D]

private lemma D_iter_smul (m : ℕ) (c : ℤ) (f : ℕ → ℤ) :
    D^[m] (fun k => c * f k) = fun k => c * D^[m] f k := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih]; funext k; simp [D]

private lemma D_iter_eq (m : ℕ) (f : ℕ → ℤ) (k : ℕ) : D^[m] f k = f (k + m) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', D, ih]; congr 1; omega

private lemma Δ2_comm_D (f : ℕ → ℤ) : Δ2 (D f) = D (Δ2 f) := by
  funext k; simp [D, Δ2]

private lemma Δ2_iter_comm_D (j : ℕ) (f : ℕ → ℤ) : Δ2^[j] (D f) = D (Δ2^[j] f) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Δ2_comm_D]

private lemma Δ2_iter_smul (j : ℕ) (c : ℤ) (f : ℕ → ℤ) :
    Δ2^[j] (fun k => c * f k) = fun k => c * Δ2^[j] f k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext k; simp [Δ2]; ring

-- 2. Main 2-adic divisibility induction on m:
-- If ∀ j s, 2^j ∣ Δ2^[j] (D^[s] Y) and ∀ j < m, 2^j ∣ Δ2^[j] X,
-- then 2^m ∣ (D^[2*m] (hmul X Y) - hmul (Δ2^[m] X) Y)!
private lemma main_2adic_ind :
    ∀ m : ℕ, ∀ X Y : ℕ → ℤ,
      (∀ j s k : ℕ, (2 : ℤ) ^ j ∣ Δ2^[j] (D^[s] Y) k) →
      (∀ j : ℕ, j < m → ∀ k : ℕ, (2 : ℤ) ^ j ∣ Δ2^[j] X k) →
      ∀ k : ℕ, (2 : ℤ) ^ m ∣ (D^[2 * m] (hmul X Y) k - hmul (Δ2^[m] X) Y k) := by
  intro m
  induction m with
  | zero =>
    intro X Y _ _ k
    simp
  | succ m ihm =>
    intro X Y hY hX k
    have hD2m : D^[2 * (m + 1)] (hmul X Y) =
        D^[2 * m] (D (D (hmul X Y))) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, Function.iterate_add_apply]
      rfl
    rw [hD2m, D2_hmul, D_iter_add, D_iter_add, D_iter_add, D_iter_smul, D_iter_smul]
    -- Four pieces:
    -- (1) D^[2*m] (hmul (Δ2 X) Y) - hmul (Δ2^[m+1] X) Y
    have hp1 : (2 : ℤ) ^ (m + 1) ∣ (D^[2 * m] (hmul (Δ2 X) Y) k - hmul (Δ2^[m + 1] X) Y k) := by
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have hX1 : ∀ r : ℕ, (2 : ℤ) ∣ Δ2 X r := by
          intro r
          have := hX 1 (by omega) r
          simpa using this
        choose X' hX' using hX1
        have hΔX_eq : Δ2 X = fun r => 2 * X' r := funext hX'
        have hX'_div : ∀ j : ℕ, j < m → ∀ r : ℕ, (2 : ℤ) ^ j ∣ Δ2^[j] X' r := by
          intro j hj r
          have h1 := hX (j + 1) (by omega) r
          rw [Function.iterate_succ_apply, hΔX_eq, Δ2_iter_smul] at h1
          rw [pow_succ'] at h1
          exact Int.dvd_of_mul_dvd_mul_left (by norm_num : (2 : ℤ) ≠ 0) h1
        rw [Function.iterate_succ_apply, hΔX_eq, Δ2_iter_smul, hmul_smul_left, hmul_smul_left,
          D_iter_smul, ← mul_sub, pow_succ']
        exact mul_dvd_mul_left 2 (ihm X' Y hY hX'_div k)
    -- (2) D^[2*m] (hmul X (Δ2 Y))
    have hY1 : ∀ r : ℕ, (2 : ℤ) ∣ Δ2 Y r := by
      intro r
      have := hY 1 0 r
      simpa using this
    choose Y' hY' using hY1
    have hΔY_eq : Δ2 Y = fun r => 2 * Y' r := funext hY'
    have hY'_div : ∀ j s r : ℕ, (2 : ℤ) ^ j ∣ Δ2^[j] (D^[s] Y') r := by
      intro j s r
      have h1 := hY (j + 1) s r
      have hcomm : Δ2^[j + 1] (D^[s] Y) = fun t => 2 * Δ2^[j] (D^[s] Y') t := by
        have hDs : ∀ t, D^[s] (Δ2 Y) t = 2 * D^[s] Y' t := by
          intro t; rw [hΔY_eq, D_iter_smul]
        have hDcomm : Δ2 (D^[s] Y) = D^[s] (Δ2 Y) := by
          funext t; simp [Δ2, D_iter_eq, add_right_comm]
        rw [Function.iterate_succ_apply, hDcomm, funext hDs, Δ2_iter_smul]
      rw [hcomm, pow_succ'] at h1
      exact Int.dvd_of_mul_dvd_mul_left (by norm_num : (2 : ℤ) ≠ 0) h1
    have hXm_Y' : (2 : ℤ) ^ m ∣ hmul (Δ2^[m] X) Y' k := by
      simp only [hmul]
      refine Finset.dvd_sum fun i _ => ?_
      have hd := hX m (by omega) i
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
    have hp2 : (2 : ℤ) ^ (m + 1) ∣ D^[2 * m] (hmul X (Δ2 Y)) k := by
      rw [hΔY_eq, hmul_smul_right, D_iter_smul, pow_succ']
      have hsub := ihm X Y' hY'_div (fun j hj => hX j (by omega)) k
      have hadd := dvd_add hsub hXm_Y'
      rw [sub_add_cancel] at hadd
      exact mul_dvd_mul_left 2 hadd
    -- (3) 2 * D^[2*m] (hmul X Y)
    have hXm_Y : (2 : ℤ) ^ m ∣ hmul (Δ2^[m] X) Y k := by
      simp only [hmul]
      refine Finset.dvd_sum fun i _ => ?_
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hX m (by omega) i) _) _
    have hp3 : (2 : ℤ) ^ (m + 1) ∣ 2 * D^[2 * m] (hmul X Y) k := by
      rw [pow_succ']
      have hsub := ihm X Y hY (fun j hj => hX j (by omega)) k
      have hadd := dvd_add hsub hXm_Y
      rw [sub_add_cancel] at hadd
      exact mul_dvd_mul_left 2 hadd
    -- (4) 2 * D^[2*m] (hmul (D X) (D Y))
    have hDY_div : ∀ j s r : ℕ, (2 : ℤ) ^ j ∣ Δ2^[j] (D^[s] (D Y)) r := by
      intro j s r
      have h1 := hY j (s + 1) r
      rwa [Function.iterate_succ_apply] at h1
    have hDX_div : ∀ j : ℕ, j ≤ m → ∀ r : ℕ, (2 : ℤ) ^ j ∣ Δ2^[j] (D X) r := by
      intro j hj r
      rw [Δ2_iter_comm_D]
      exact hX j (by omega) (r + 1)
    have hDXm_DY : (2 : ℤ) ^ m ∣ hmul (Δ2^[m] (D X)) (D Y) k := by
      simp only [hmul]
      refine Finset.dvd_sum fun i _ => ?_
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hDX_div m le_rfl i) _) _
    have hp4 : (2 : ℤ) ^ (m + 1) ∣ 2 * D^[2 * m] (hmul (D X) (D Y)) k := by
      rw [pow_succ']
      have hsub := ihm (D X) (D Y) hDY_div (fun j hj => hDX_div j (by omega)) k
      have hadd := dvd_add hsub hDXm_DY
      rw [sub_add_cancel] at hadd
      exact mul_dvd_mul_left 2 hadd
    have hrew : (D^[2 * m] (hmul (Δ2 X) Y) k + D^[2 * m] (hmul X (Δ2 Y)) k +
        2 * D^[2 * m] (hmul X Y) k + 2 * D^[2 * m] (hmul (D X) (D Y)) k) -
        hmul (Δ2^[m + 1] X) Y k =
        (D^[2 * m] (hmul (Δ2 X) Y) k - hmul (Δ2^[m + 1] X) Y k) +
        D^[2 * m] (hmul X (Δ2 Y)) k +
        2 * D^[2 * m] (hmul X Y) k +
        2 * D^[2 * m] (hmul (D X) (D Y)) k := by ring
    rw [hrew]
    exact dvd_add (dvd_add (dvd_add hp1 hp2) hp3) hp4

-- 3. Newton forward difference formula for step 2:
-- f (k + 2 * N) = ∑ r ∈ range (N + 1), C(N, r) * Δ2^[r] f k
private lemma shift2_eq_sum_Δ2 (N : ℕ) (f : ℕ → ℤ) (k : ℕ) :
    f (k + 2 * N) = ∑ r ∈ Finset.range (N + 1), (Nat.choose N r : ℤ) * Δ2^[r] f k := by
  induction N generalizing f k with
  | zero => simp
  | succ N ih =>
    have hstep : f (k + 2 * (N + 1)) = f (k + 2 * N) + Δ2 f (k + 2 * N) := by
      simp only [Δ2]; rw [show k + 2 * (N + 1) = k + 2 * N + 2 by omega]; ring
    rw [hstep, ih f k, ih (Δ2 f) k]
    have h1 : ∑ r ∈ Finset.range (N + 1), (Nat.choose N r : ℤ) * Δ2^[r] (Δ2 f) k =
        ∑ r ∈ Finset.range (N + 1), (Nat.choose N r : ℤ) * Δ2^[r + 1] f k := by
      refine Finset.sum_congr rfl fun r _ => by rw [Function.iterate_succ_apply]
    rw [h1]
    conv_rhs => rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, Function.iterate_zero_apply]
    rw [Finset.sum_range_succ' (fun r => (Nat.choose N r : ℤ) * Δ2^[r] f k),
      Finset.sum_range_succ (fun r => (Nat.choose N r : ℤ) * Δ2^[r + 1] f k)]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, Function.iterate_zero_apply]
    have hmid : (∑ r ∈ Finset.range N, (Nat.choose N (r + 1) : ℤ) * Δ2^[r + 1] f k) +
        (∑ r ∈ Finset.range N, (Nat.choose N r : ℤ) * Δ2^[r + 1] f k) =
        ∑ r ∈ Finset.range N, (Nat.choose (N + 1) (r + 1) : ℤ) * Δ2^[r + 1] f k := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Nat.choose_succ_succ]; push_cast; ring
    linarith

-- 4. Divisibility: for n ≥ 1 and 1 ≤ r ≤ 2^(n-1), 2^n ∣ C(2^(n-1), r) * 2^r!
private lemma two_pow_dvd_choose_mul_two_pow (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    2 ^ n ∣ Nat.choose (2 ^ (n - 1)) r * 2 ^ r := by
  -- Use r * C(2^(n-1), r) = 2^(n-1) * C(2^(n-1) - 1, r - 1) and v_2(r) < r!
  have hr0 : r ≠ 0 := by omega
  have hv : ∃ t u : ℕ, Odd u ∧ r = 2 ^ t * u := by
    refine ⟨r.factorization 2, r / 2 ^ (r.factorization 2), ?_, ?_⟩
    · rw [Nat.odd_iff]
      by_contra h
      have h2 : 2 ∣ r / 2 ^ (r.factorization 2) := Nat.dvd_of_mod_eq_zero (by omega)
      have hd : 2 ^ (r.factorization 2) ∣ r := Nat.ordProj_dvd r 2
      have hd' : 2 ^ (r.factorization 2 + 1) ∣ r := by
        obtain ⟨q, hq⟩ := h2
        refine ⟨q, ?_⟩
        rw [pow_succ, mul_assoc, ← hq, Nat.mul_div_cancel' hd]
      have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hr0).mp hd'
      omega
    · exact (Nat.mul_div_cancel' (Nat.ordProj_dvd r 2)).symm
  obtain ⟨t, u, hu_odd, hr_eq⟩ := hv
  have ht_lt : t < r := by
    have h1 : t < 2 ^ t := Nat.lt_two_pow_self
    have hu_pos : 1 ≤ u := by obtain ⟨m, hm⟩ := hu_odd; omega
    have h2 : 2 ^ t ≤ 2 ^ t * u := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hmul : r * Nat.choose (2 ^ (n - 1)) r =
      2 ^ (n - 1) * Nat.choose (2 ^ (n - 1) - 1) (r - 1) := by
    have h := Nat.add_one_mul_choose_eq (2 ^ (n - 1) - 1) (r - 1)
    have h1 : 2 ^ (n - 1) - 1 + 1 = 2 ^ (n - 1) := by
      have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
      omega
    have h2 : r - 1 + 1 = r := by omega
    rw [h1, h2] at h
    linarith
  have hdvd_mul : 2 ^ n * 2 ^ t ∣ u * (Nat.choose (2 ^ (n - 1)) r * 2 ^ r) * 2 ^ t := by
    have heq : u * (Nat.choose (2 ^ (n - 1)) r * 2 ^ r) * 2 ^ t =
        (r * Nat.choose (2 ^ (n - 1)) r) * 2 ^ r := by rw [hr_eq]; ring
    rw [heq, hmul]
    have hpow_le : n + t ≤ (n - 1) + r := by omega
    have hd1 : 2 ^ (n + t) ∣ 2 ^ ((n - 1) + r) := Nat.pow_dvd_pow 2 hpow_le
    rw [pow_add, pow_add] at hd1
    calc 2 ^ n * 2 ^ t ∣ 2 ^ (n - 1) * 2 ^ r := hd1
      _ ∣ (2 ^ (n - 1) * Nat.choose (2 ^ (n - 1) - 1) (r - 1)) * 2 ^ r := by
          refine ⟨Nat.choose (2 ^ (n - 1) - 1) (r - 1), by ring⟩
  have hdvd_u : 2 ^ n ∣ u * (Nat.choose (2 ^ (n - 1)) r * 2 ^ r) :=
    (Nat.mul_dvd_mul_iff_right (by positivity : 0 < 2 ^ t)).mp hdvd_mul
  have hcop : Nat.Coprime (2 ^ n) u :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by
      intro h; obtain ⟨m, hm⟩ := hu_odd; obtain ⟨q, hq⟩ := h; omega)).pow_left n
  exact hcop.dvd_of_dvd_mul_left hdvd_u

private theorem main_proved :
    ∀ a : ℕ → ℤ,
      (let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
       let C : PowerSeries ℚ :=
         PowerSeries.mk (fun n =>
           (if 4 ∣ n then (1 : ℚ) else -1) / (Nat.factorial n : ℚ))
       A * C = 1) →
      ∀ (k n : ℕ), 1 ≤ n →
        a (2 ^ n + k) ≡ a k [ZMOD (2 ^ n : ℤ)] := by
  intro a hAC
  let c : ℕ → ℤ := fun j => if 4 ∣ j then 1 else -1
  -- Extract hmul a c = delta_0
  have hac : ∀ m : ℕ, hmul a c m = if m = 0 then 1 else 0 := by
    intro m
    have hm := congr_arg (PowerSeries.coeff m) hAC
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j =>
          PowerSeries.coeff i (PowerSeries.mk fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) *
          PowerSeries.coeff j (PowerSeries.mk fun n => (if 4 ∣ n then (1 : ℚ) else -1) / (Nat.factorial n : ℚ))),
      PowerSeries.coeff_one] at hm
    have hL : (∑ i ∈ Finset.range (m + 1),
          ((a i : ℚ) / (Nat.factorial i : ℚ)) *
          ((if 4 ∣ m - i then (1 : ℚ) else -1) / (Nat.factorial (m - i) : ℚ))) =
        (hmul a c m : ℚ) / (Nat.factorial m : ℚ) := by
      simp only [hmul, Int.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hch : (Nat.choose m i : ℚ) * (Nat.factorial i : ℚ) * (Nat.factorial (m - i) : ℚ) =
          (Nat.factorial m : ℚ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial him
      have hfi : (Nat.factorial i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have hfmi : (Nat.factorial (m - i) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - i))
      have hfm : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      have hc_eq : (c (m - i) : ℚ) = if 4 ∣ m - i then (1 : ℚ) else -1 := by
        simp only [c]; split_ifs <;> norm_num
      rw [← hc_eq]
      push_cast
      field_simp [hfi, hfmi, hfm]
      linear_combination (a i : ℚ) * (c (m - i) : ℚ) * hch.symm
    simp only [PowerSeries.coeff_mk] at hm
    rw [hL] at hm
    have hfm : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hq : (hmul a c m : ℚ) = if m = 0 then 1 else 0 := by
      split_ifs at hm ⊢ with h
      · subst h; simpa using hm
      · exact (div_eq_zero_iff.mp hm).resolve_right hfm
    split_ifs at hq ⊢ <;> exact_mod_cast hq
  -- Verify ∀ j s k, 2^j ∣ Δ2^[j] (D^[s] c) k
  have hc_div : ∀ j s k : ℕ, (2 : ℤ) ^ j ∣ Δ2^[j] (D^[s] c) k := by
    intro j
    induction j with
    | zero => intro s k; simp
    | succ j ihj =>
      intro s k
      cases j with
      | zero =>
        simp only [Nat.zero_add, pow_one, Function.iterate_one, Δ2, D_iter_eq, c]
        split_ifs <;> norm_num
      | succ j =>
        have hstep : Δ2 (Δ2 (D^[s] c)) = fun r => (-2) * Δ2 (D^[s] c) r := by
          funext r
          simp only [Δ2, D_iter_eq, c]
          have h4 : 4 ∣ r + 2 + 2 + s ↔ 4 ∣ r + s := by
            rw [show r + 2 + 2 + s = (r + s) + 4 by omega]
            exact ⟨fun ⟨q, hq⟩ => ⟨q - 1, by omega⟩, fun ⟨q, hq⟩ => ⟨q + 1, by omega⟩⟩
          split_ifs <;> omega
        rw [show j + 1 + 1 = j + 2 by omega, Function.iterate_add_apply,
          show Δ2^[2] (D^[s] c) = Δ2 (Δ2 (D^[s] c)) from rfl, hstep, Δ2_iter_smul]
        dsimp only
        have hprev := ihj s k
        rw [Function.iterate_succ_apply] at hprev
        rw [pow_succ']
        have hneg : (-2 : ℤ) = 2 * (-1) := by norm_num
        rw [hneg, mul_assoc]
        exact mul_dvd_mul_left 2 (dvd_mul_of_dvd_right hprev (-1))
  -- Prove ∀ m k, 2^m ∣ Δ2^[m] a k by strong induction on m!
  have ha_div : ∀ m k : ℕ, (2 : ℤ) ^ m ∣ Δ2^[m] a k := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      cases m with
      | zero => intro k; simp
      | succ m =>
        have hD0 : ∀ k : ℕ, D^[2 * (m + 1)] (hmul a c) k = 0 := by
          intro k
          rw [D_iter_eq, hac]
          simp
        have hmul_div : ∀ k : ℕ, (2 : ℤ) ^ (m + 1) ∣ hmul (Δ2^[m + 1] a) c k := by
          intro k
          have h1 := main_2adic_ind (m + 1) a c hc_div (fun j hj => ih j hj) k
          rw [hD0 k, zero_sub, dvd_neg] at h1
          exact h1
        -- Multiply hmul (Δ2^[m+1] a) c by a on the right using hmul_assoc and hmul c a = delta_0!
        intro k
        have hca : hmul c a = fun r => if r = 0 then 1 else 0 := by
          rw [hmul_comm]; exact funext hac
        have heq : Δ2^[m + 1] a k = hmul (hmul (Δ2^[m + 1] a) c) a k := by
          rw [hmul_assoc, hca]
          simp only [hmul]
          rw [Finset.sum_eq_single k]
          · simp
          · intro j hj hjk
            have hjk' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            simp [show k - j ≠ 0 by omega]
          · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) h
        rw [heq]
        simp only [hmul]
        refine Finset.dvd_sum fun j _ => ?_
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hmul_div j) _) _
  -- Conclude: a (2^n + k) - a k = ∑_{r=1}^{2^(n-1)} C(2^(n-1), r) * Δ2^[r] a k ≡ 0 (mod 2^n)!
  intro k n hn
  rw [Int.modEq_iff_dvd, add_comm]
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
  rw [h2n, shift2_eq_sum_Δ2 (2 ^ (n - 1)) a k, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Function.iterate_zero_apply,
    sub_add_cancel_right, dvd_neg]
  refine Finset.dvd_sum fun r _ => ?_
  have hd1 : ((2 ^ n : ℕ) : ℤ) ∣ ((Nat.choose (2 ^ (n - 1)) (r + 1) * 2 ^ (r + 1) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (two_pow_dvd_choose_mul_two_pow n (r + 1) hn (Nat.succ_pos r))
  obtain ⟨q, hq⟩ := ha_div (r + 1) k
  rw [hq]
  have hrew : (Nat.choose (2 ^ (n - 1)) (r + 1) : ℤ) * ((2 : ℤ) ^ (r + 1) * q) =
      ((Nat.choose (2 ^ (n - 1)) (r + 1) * 2 ^ (r + 1) : ℕ) : ℤ) * q := by
    push_cast; ring
  rw [hrew]
  exact dvd_mul_of_dvd_left (by simpa using hd1) q

end OMA.P_oeis_a205572

theorem OMA.solution : type_of% @OMA.S_oeis_a205572.main :=
  OMA.P_oeis_a205572.main_proved
