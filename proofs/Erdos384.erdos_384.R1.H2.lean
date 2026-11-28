import OMAReductions.R_Erdos384_erdos_384_R1
import Mathlib


/-!
# Chebyshev 30m Central-Range Lemma for Erdős 384 (H2)

We prove that for `4 ≤ k`, `2 * k ≤ n`, `n ≤ 14 * k`, and `700000 ≤ n`, there is a prime
`p ∣ n.choose k` with `2 * p ≤ n`.

The proof is completely elementary, using Chebyshev's 1852 `30m` identity:
  `F(x) = T(x) - T(x/2) - T(x/3) - T(x/5) + T(x/30)`
which satisfies `ψ(x) - ψ(x/6) ≤ F(x) ≤ ψ(x)` for all `x : ℕ`, combined with elementary
Stirling bounds, Erdős's 1932 bound `ϑ(x) ≤ (2 log 2) x`, and the elementary max-term
binomial lower bound `log C(n, k) ≥ n H(k/n) - log(n + 1)`.
-/

open Nat Finset Real ArithmeticFunction

namespace OMA.Erdos384Cheb

/-! ## Definitions -/

noncomputable def theta (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, Real.log (p : ℝ)

noncomputable def psi (x : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, Λ m

noncomputable def T (x : ℕ) : ℝ :=
  Real.log (x ! : ℝ)

noncomputable def F (x : ℕ) : ℝ :=
  T x - T (x / 2) - T (x / 3) - T (x / 5) + T (x / 30)

noncomputable def A_const : ℝ :=
  (14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5) / 30

noncomputable def ent (α : ℝ) : ℝ :=
  -α * Real.log α - (1 - α) * Real.log (1 - α)

/-! ## Step 1: Prime product bound on `n.choose k` -/

lemma theta_sub_eq (a b : ℕ) (hab : a ≤ b) :
    theta b - theta a = ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log (p : ℝ) := by
  unfold theta
  have hunion : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Ioc a b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2
    omega
  rw [hunion, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hdisj)]
  ring

lemma log_choose_le_theta_sub (n k : ℕ) (h2k : 2 * k ≤ n)
    (hcon : ∀ p : ℕ, p.Prime → p ∣ n.choose k → n < 2 * p) :
    Real.log (n.choose k : ℝ) ≤ theta n - theta (n - k) := by
  have hC0 : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hpf : (n.choose k).primeFactors ⊆ (Finset.Ioc (n - k) n).filter Nat.Prime := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpd, -⟩ := hp
    have h2p := hcon p hpp hpd
    have hdesc : p ∣ ∏ i ∈ Finset.range k, (n - i) := by
      rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
      exact Dvd.dvd.mul_left hpd _
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdesc
    rw [Finset.mem_range] at hi
    obtain ⟨c, hc⟩ := hpi
    have hc1 : c = 1 := by
      rcases c with _ | _ | c
      · simp at hc; omega
      · rfl
      · have : n - i ≤ n := Nat.sub_le n i
        nlinarith
    subst hc1
    rw [mul_one] at hc
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hpp⟩
  have hsqf : Squarefree (n.choose k) := by
    rw [Nat.squarefree_iff_factorization_le_one hC0]
    intro p
    by_cases hp : p.Prime
    · by_cases hpd : p ∣ n.choose k
      · apply Nat.factorization_choose_le_one
        have h1 := hcon p hp hpd
        have h2 := hp.two_le
        rw [sq]; nlinarith
      · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hCdvd : n.choose k ∣ ∏ p ∈ (Finset.Ioc (n - k) n).filter Nat.Prime, p :=
    calc n.choose k = ∏ p ∈ (n.choose k).primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree hsqf).symm
      _ ∣ _ := Finset.prod_dvd_prod_of_subset _ _ _ hpf
  have hPpos : 0 < ∏ p ∈ (Finset.Ioc (n - k) n).filter Nat.Prime, p := by
    apply Finset.prod_pos
    intro p hp
    rw [Finset.mem_filter] at hp
    exact hp.2.pos
  have hCle : n.choose k ≤ ∏ p ∈ (Finset.Ioc (n - k) n).filter Nat.Prime, p :=
    Nat.le_of_dvd hPpos hCdvd
  rw [theta_sub_eq (n - k) n (Nat.sub_le n k)]
  have hCpos : (0 : ℝ) < (n.choose k : ℝ) := by positivity
  calc Real.log (n.choose k : ℝ)
      ≤ Real.log ((∏ p ∈ (Finset.Ioc (n - k) n).filter Nat.Prime, p : ℕ) : ℝ) :=
        Real.log_le_log hCpos (by exact_mod_cast hCle)
    _ = Real.log (∏ p ∈ (Finset.Ioc (n - k) n).filter Nat.Prime, (p : ℝ)) := by
        rw [Nat.cast_prod]
    _ = ∑ p ∈ (Finset.Ioc (n - k) n).filter Nat.Prime, Real.log (p : ℝ) := by
        rw [Real.log_prod]
        intro p hp
        rw [Finset.mem_filter] at hp
        exact Nat.cast_ne_zero.mpr hp.2.ne_zero

/-! ## Step 2: Chebyshev's identity `T(x) = ∑ Λ(m) * ⌊x/m⌋` -/

lemma T_eq_sum_log (x : ℕ) : T x = ∑ m ∈ Finset.Icc 1 x, Real.log (m : ℝ) := by
  induction x with
  | zero => simp [T]
  | succ x ih =>
    have hIcc : Finset.Icc 1 (x + 1) = insert (x + 1) (Finset.Icc 1 x) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : x + 1 ∉ Finset.Icc 1 x := by simp
    rw [hIcc, Finset.sum_insert hnotmem, ← ih, T, T, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]

lemma card_filter_dvd_Icc (x d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 x).filter (fun m => d ∣ m)).card = x / d := by
  have h : ((Finset.Icc 1 x).filter (fun m => d ∣ m)).card = (Finset.Icc 1 (x / d)).card := by
    apply Finset.card_nbij' (fun m => m / d) (fun j => d * j)
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      obtain ⟨⟨hm1, hmx⟩, k, rfl⟩ := hm
      have hk1 : 1 ≤ k := by nlinarith
      rw [Nat.mul_div_cancel_left k (by omega)]
      exact ⟨hk1, (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)⟩
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      refine ⟨⟨by nlinarith, ?_⟩, ⟨j, rfl⟩⟩
      have := (Nat.le_div_iff_mul_le (by omega)).mp hj.2
      nlinarith
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter] at hm
      exact Nat.mul_div_cancel' hm.2
    · intro j _
      exact Nat.mul_div_cancel_left j (by omega)
  rw [h]
  simp

lemma T_eq_sum_vonMangoldt (x : ℕ) :
    T x = ∑ d ∈ Finset.Icc 1 x, Λ d * ((x / d : ℕ) : ℝ) := by
  rw [T_eq_sum_log]
  have h1 : ∑ m ∈ Finset.Icc 1 x, Real.log (m : ℝ) =
      ∑ m ∈ Finset.Icc 1 x, ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ∣ m), Λ d := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [← ArithmeticFunction.vonMangoldt_sum]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdm, hm0⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdm (by omega)
      have hdx : d ≤ x := le_trans (Nat.le_of_dvd (by omega) hdm) hm.2
      exact ⟨⟨hd1, hdx⟩, hdm⟩
    · rintro ⟨⟨_, _⟩, hdm⟩
      exact ⟨hdm, by omega⟩
  rw [h1]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_Icc] at hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_dvd_Icc x d hd.1, mul_comm]

/-! ## Step 3: Chebyshev's `30m` identity `ψ(x) - ψ(x/6) ≤ F(x) ≤ ψ(x)` -/

lemma T_div_eq (x d : ℕ) (_hd : 1 ≤ d) :
    T (x / d) = ∑ m ∈ Finset.Icc 1 x, Λ m * (((x / m) / d : ℕ) : ℝ) := by
  rw [T_eq_sum_vonMangoldt]
  have hsub : Finset.Icc 1 (x / d) ⊆ Finset.Icc 1 x := by
    intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, le_trans hm.2 (Nat.div_le_self x d)⟩
  rw [Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro m _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d m]
  · intro m hm hnot
    rw [Finset.mem_Icc] at hm hnot
    have hgt : x / d < m := by omega
    have hzero : (x / d) / m = 0 := Nat.div_eq_of_lt hgt
    rw [hzero, Nat.cast_zero, mul_zero]

def g30 (u : ℕ) : ℤ :=
  (u : ℤ) - (u / 2 : ℕ) - (u / 3 : ℕ) - (u / 5 : ℕ) + (u / 30 : ℕ)

lemma g30_nonneg (u : ℕ) : 0 ≤ g30 u := by unfold g30; omega

lemma g30_le_one (u : ℕ) : g30 u ≤ 1 := by unfold g30; omega

lemma g30_eq_one (u : ℕ) (h1 : 1 ≤ u) (h5 : u ≤ 5) : g30 u = 1 := by unfold g30; omega

lemma F_eq_sum_g30 (x : ℕ) :
    F x = ∑ m ∈ Finset.Icc 1 x, Λ m * (g30 (x / m) : ℝ) := by
  unfold F
  rw [T_eq_sum_vonMangoldt x, T_div_eq x 2 (by omega), T_div_eq x 3 (by omega),
    T_div_eq x 5 (by omega), T_div_eq x 30 (by omega)]
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  unfold g30
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
  ring

lemma F_le_psi (x : ℕ) : F x ≤ psi x := by
  rw [F_eq_sum_g30, psi]
  apply Finset.sum_le_sum
  intro m _
  have hΛ : 0 ≤ Λ m := ArithmeticFunction.vonMangoldt_nonneg
  have hg : (g30 (x / m) : ℝ) ≤ 1 := by exact_mod_cast g30_le_one (x / m)
  nlinarith

lemma psi_sub_le_F (x : ℕ) : psi x - psi (x / 6) ≤ F x := by
  rw [F_eq_sum_g30]
  have hsub_eq : psi x - psi (x / 6) = ∑ m ∈ Finset.Ioc (x / 6) x, Λ m := by
    unfold psi
    have hunion : Finset.Icc 1 x = Finset.Icc 1 (x / 6) ∪ Finset.Ioc (x / 6) x := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have hdisj : Disjoint (Finset.Icc 1 (x / 6)) (Finset.Ioc (x / 6) x) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hm1 hm2; omega
    rw [hunion, Finset.sum_union hdisj]; ring
  rw [hsub_eq]
  have hsub : Finset.Ioc (x / 6) x ⊆ Finset.Icc 1 x := by
    intro m hm; rw [Finset.mem_Ioc] at hm; rw [Finset.mem_Icc]; omega
  calc ∑ m ∈ Finset.Ioc (x / 6) x, Λ m
      = ∑ m ∈ Finset.Ioc (x / 6) x, Λ m * (g30 (x / m) : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_Ioc] at hm
        have hmpos : 0 < m := by omega
        have h1 : 1 ≤ x / m := (Nat.le_div_iff_mul_le hmpos).mpr (by omega)
        have h5 : x / m ≤ 5 := by
          have : x < 6 * m := by
            by_contra h
            push Not at h
            have : m ≤ x / 6 := (Nat.le_div_iff_mul_le (by omega : 0 < 6)).mpr (by omega)
            omega
          exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hmpos).mpr (by omega))
        rw [g30_eq_one (x / m) h1 h5, Int.cast_one, mul_one]
    _ ≤ ∑ m ∈ Finset.Icc 1 x, Λ m * (g30 (x / m) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro m _ _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by exact_mod_cast g30_nonneg (x / m))

/-! ## Step 4: Elementary Stirling bounds and bounds on `F(x)` -/

noncomputable def stirlingF (t : ℝ) : ℝ := t * Real.log t - t

lemma stirling_lower (x : ℕ) (hx : 1 ≤ x) : stirlingF (x : ℝ) ≤ T x := by
  induction x with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp [stirlingF, T]
    · have hm : 1 ≤ m + 1 := by omega
      have hih := ih hm
      rw [T, Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      rw [← T]
      have hmpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have hstep : Real.log (((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
          ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at hstep
      have hmul := mul_le_mul_of_nonneg_left hstep hmpos.le
      have hsimp : ((m + 1 : ℕ) : ℝ) * (((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1) = 1 := by
        field_simp
        push_cast
        ring
      rw [hsimp] at hmul
      unfold stirlingF at hih ⊢
      push_cast at hih hmul ⊢
      rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
      linarith

lemma stirling_upper (x : ℕ) (hx : 1 ≤ x) :
    T x ≤ stirlingF (x : ℝ) + Real.log (x : ℝ) + 1 := by
  induction x with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp [stirlingF, T]
    · have hm : 1 ≤ m + 1 := by omega
      have hih := ih hm
      rw [T, Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
      rw [← T]
      have hm2pos : (0 : ℝ) < (m + 2 : ℕ) := by positivity
      have hstep : Real.log (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤
          ((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at hstep
      have hmul := mul_le_mul_of_nonneg_left hstep hm2pos.le
      have hsimp : ((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ) - 1) = -1 := by
        field_simp
        push_cast
        ring
      rw [hsimp] at hmul
      unfold stirlingF at hih ⊢
      push_cast at hih hmul ⊢
      rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
      linarith

lemma stirlingF_ge_neg_one {v : ℝ} (hv : 0 < v) : -1 ≤ stirlingF v := by
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hv)
  rw [Real.log_div one_ne_zero hv.ne', Real.log_one, zero_sub] at h
  have hmul := mul_le_mul_of_nonneg_left h hv.le
  have hsimp : v * (1 / v - 1) = 1 - v := by field_simp
  rw [hsimp] at hmul
  unfold stirlingF
  linarith

lemma stirlingF_div_lower (x d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) :
    stirlingF ((x : ℝ) / (d : ℝ)) - Real.log (x : ℝ) ≤ T (x / d) := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlogx : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1
  have hvpos : (0 : ℝ) < (x : ℝ) / (d : ℝ) := by positivity
  by_cases hu : x / d = 0
  · rw [hu, T, Nat.factorial_zero, Nat.cast_one, Real.log_one]
    have hvlt : (x : ℝ) / (d : ℝ) < 1 := by
      have : x < d := by
        by_contra h; push Not at h
        have : 1 ≤ x / d := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by omega : 1 * d ≤ x)
        omega
      rw [div_lt_one (by positivity)]
      exact_mod_cast this
    have hlogv : Real.log ((x : ℝ) / (d : ℝ)) ≤ 0 := Real.log_nonpos hvpos.le hvlt.le
    unfold stirlingF
    have : (x : ℝ) / (d : ℝ) * Real.log ((x : ℝ) / (d : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hvpos.le hlogv
    linarith
  · have hu1 : 1 ≤ x / d := Nat.pos_of_ne_zero hu
    have hT := stirling_lower (x / d) hu1
    set u : ℝ := ((x / d : ℕ) : ℝ)
    set v : ℝ := (x : ℝ) / (d : ℝ)
    have hupos : 0 < u := by positivity
    have huv : u ≤ v := by
      rw [le_div_iff₀ (by positivity)]
      simp only [u]
      exact_mod_cast Nat.div_mul_le_self x d
    have hvu1 : v - u ≤ 1 := by
      have hlt : x < (x / d + 1) * d := by
        have := Nat.lt_div_mul_add (a := x) (b := d) (by omega)
        linarith
      have hlt' : v < u + 1 := by
        rw [div_lt_iff₀ (by positivity)]
        simp only [u]
        exact_mod_cast hlt
      linarith
    have hv1 : 1 ≤ v := le_trans (by simp only [u]; exact_mod_cast hu1) huv
    have hvx : v ≤ (x : ℝ) := div_le_self (by positivity) (by exact_mod_cast hd)
    have hlog_vu : Real.log (v / u) ≤ v / u - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hvpos hupos)
    rw [Real.log_div hvpos.ne' hupos.ne'] at hlog_vu
    have hmul := mul_le_mul_of_nonneg_left hlog_vu hupos.le
    have hsimp : u * (v / u - 1) = v - u := by field_simp
    rw [hsimp] at hmul
    have hlogv_le : Real.log v ≤ Real.log (x : ℝ) := Real.log_le_log hvpos hvx
    have hlogv_nn : 0 ≤ Real.log v := Real.log_nonneg hv1
    have hdiff : stirlingF v - stirlingF u ≤ Real.log (x : ℝ) := by
      unfold stirlingF
      nlinarith
    linarith

lemma stirlingF_div_upper (x d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) :
    T (x / d) ≤ stirlingF ((x : ℝ) / (d : ℝ)) + Real.log (x : ℝ) + 1 := by
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlogx : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1
  have hvpos : (0 : ℝ) < (x : ℝ) / (d : ℝ) := by positivity
  by_cases hu : x / d = 0
  · rw [hu, T, Nat.factorial_zero, Nat.cast_one, Real.log_one]
    have hge := stirlingF_ge_neg_one hvpos
    linarith
  · have hu1 : 1 ≤ x / d := Nat.pos_of_ne_zero hu
    have hT := stirling_upper (x / d) hu1
    set u : ℝ := ((x / d : ℕ) : ℝ)
    set v : ℝ := (x : ℝ) / (d : ℝ)
    have hupos : 0 < u := by positivity
    have huv : u ≤ v := by
      rw [le_div_iff₀ (by positivity)]
      simp only [u]
      exact_mod_cast Nat.div_mul_le_self x d
    have hux : u ≤ (x : ℝ) := by simp only [u]; exact_mod_cast Nat.div_le_self x d
    have hlogu_nn : 0 ≤ Real.log u := Real.log_nonneg (by simp only [u]; exact_mod_cast hu1)
    have hlogu_le : Real.log u ≤ Real.log (x : ℝ) := Real.log_le_log hupos hux
    have hlog_uv : Real.log (u / v) ≤ u / v - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hupos hvpos)
    rw [Real.log_div hupos.ne' hvpos.ne'] at hlog_uv
    have hmul := mul_le_mul_of_nonneg_left hlog_uv hvpos.le
    have hsimp : v * (u / v - 1) = u - v := by field_simp
    rw [hsimp] at hmul
    have hmono : stirlingF u ≤ stirlingF v := by
      unfold stirlingF
      nlinarith
    linarith

lemma stirlingF_comb {x : ℝ} (hx : 0 < x) :
    stirlingF x - stirlingF (x / 2) - stirlingF (x / 3) - stirlingF (x / 5) + stirlingF (x / 30) =
      A_const * x := by
  unfold stirlingF A_const
  rw [Real.log_div hx.ne' (by norm_num), Real.log_div hx.ne' (by norm_num),
    Real.log_div hx.ne' (by norm_num), Real.log_div hx.ne' (by norm_num)]
  have h30 : Real.log (30 : ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [h30]
  ring

lemma F_lower (x : ℕ) (hx : 1 ≤ x) :
    A_const * (x : ℝ) - 4 * Real.log (x : ℝ) - 3 ≤ F x := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have h1 := stirling_lower x hx
  have h2 := stirlingF_div_upper x 2 hx (by omega)
  have h3 := stirlingF_div_upper x 3 hx (by omega)
  have h5 := stirlingF_div_upper x 5 hx (by omega)
  have h30 := stirlingF_div_lower x 30 hx (by omega)
  have hcomb := stirlingF_comb hxpos
  unfold F
  norm_num at h2 h3 h5 h30
  linarith

lemma F_upper (x : ℕ) (hx : 1 ≤ x) :
    F x ≤ A_const * (x : ℝ) + 5 * Real.log (x : ℝ) + 2 := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have h1 := stirling_upper x hx
  have h2 := stirlingF_div_lower x 2 hx (by omega)
  have h3 := stirlingF_div_lower x 3 hx (by omega)
  have h5 := stirlingF_div_lower x 5 hx (by omega)
  have h30 := stirlingF_div_upper x 30 hx (by omega)
  have hcomb := stirlingF_comb hxpos
  unfold F
  norm_num at h2 h3 h5 h30
  linarith

/-! ## Step 5: Bounds on `ψ(x)`, `ϑ(x)`, and `ψ(x) - ϑ(x)` -/

lemma A_const_pos : 0 < A_const := by
  unfold A_const
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  linarith

lemma psi_lower (x : ℕ) (hx : 1 ≤ x) :
    A_const * (x : ℝ) - 4 * Real.log (x : ℝ) - 3 ≤ psi x :=
  le_trans (F_lower x hx) (F_le_psi x)

lemma psi_upper : ∀ x : ℕ, 1 ≤ x →
    psi x ≤ (6 / 5) * A_const * (x : ℝ) +
      (5 * Real.log (x : ℝ) + 2) * (Real.log (x : ℝ) / Real.log 6 + 1) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    have hlog6 : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
    have hlogx : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx)
    have hA : 0 < A_const := A_const_pos
    by_cases h6 : x < 6
    · have hx6 : x / 6 = 0 := Nat.div_eq_of_lt h6
      have hpsi0 : psi 0 = 0 := by simp [psi]
      have h1 : psi x ≤ F x := by
        have := psi_sub_le_F x
        rw [hx6, hpsi0, sub_zero] at this
        exact this
      have h2 := F_upper x hx
      have h3 : 0 ≤ Real.log (x : ℝ) / Real.log 6 := div_nonneg hlogx hlog6.le
      nlinarith
    · push Not at h6
      have hx6_pos : 1 ≤ x / 6 := (Nat.le_div_iff_mul_le (by omega : 0 < 6)).mpr (by omega)
      have hx6_lt : x / 6 < x := Nat.div_lt_self (by omega) (by omega)
      have hih := ih (x / 6) hx6_lt hx6_pos
      have hF := F_upper x hx
      have hsub := psi_sub_le_F x
      have hx6_le : ((x / 6 : ℕ) : ℝ) ≤ (x : ℝ) / 6 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
        exact_mod_cast Nat.div_mul_le_self x 6
      have hlog_x6 : Real.log ((x / 6 : ℕ) : ℝ) ≤ Real.log (x : ℝ) - Real.log 6 := by
        calc Real.log ((x / 6 : ℕ) : ℝ)
            ≤ Real.log ((x : ℝ) / 6) := Real.log_le_log (by positivity) hx6_le
          _ = Real.log (x : ℝ) - Real.log 6 := Real.log_div (by positivity) (by norm_num)
      have hdiv_le : Real.log ((x / 6 : ℕ) : ℝ) / Real.log 6 + 1 ≤
          Real.log (x : ℝ) / Real.log 6 := by
        have : Real.log ((x / 6 : ℕ) : ℝ) / Real.log 6 ≤
            (Real.log (x : ℝ) - Real.log 6) / Real.log 6 :=
          div_le_div_of_nonneg_right hlog_x6 hlog6.le
        have hsub6 : (Real.log (x : ℝ) - Real.log 6) / Real.log 6 =
            Real.log (x : ℝ) / Real.log 6 - 1 := by
          rw [sub_div, div_self hlog6.ne']
        linarith
      have hdiv_nn : 0 ≤ Real.log ((x / 6 : ℕ) : ℝ) / Real.log 6 + 1 := by
        have : 0 ≤ Real.log ((x / 6 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hx6_pos)
        linarith [div_nonneg this hlog6.le]
      have h5_le : 5 * Real.log ((x / 6 : ℕ) : ℝ) + 2 ≤ 5 * Real.log (x : ℝ) + 2 := by linarith
      have hprod_le : (5 * Real.log ((x / 6 : ℕ) : ℝ) + 2) *
            (Real.log ((x / 6 : ℕ) : ℝ) / Real.log 6 + 1) ≤
          (5 * Real.log (x : ℝ) + 2) * (Real.log (x : ℝ) / Real.log 6) :=
        mul_le_mul h5_le hdiv_le hdiv_nn (by linarith)
      nlinarith

lemma theta_le_psi (x : ℕ) : theta x ≤ psi x := by
  unfold theta psi
  calc ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, Real.log (p : ℝ)
      = ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime, Λ p := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_filter] at hp
        exact (ArithmeticFunction.vonMangoldt_apply_prime hp.2).symm
    _ ≤ ∑ m ∈ Finset.Icc 1 x, Λ m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro m _ _
        exact ArithmeticFunction.vonMangoldt_nonneg

lemma theta_sub_odd_le (m : ℕ) (hm : 1 ≤ m) :
    theta (2 * m + 1) - theta (m + 1) ≤ 2 * (m : ℝ) * Real.log 2 := by
  rw [theta_sub_eq (m + 1) (2 * m + 1) (by omega)]
  have hdvd : ∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p ∣
      (2 * m + 1).choose m := by
    apply Finset.prod_primes_dvd
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact hp.2.prime
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
      have hmul := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m + 1 by omega)
      rw [show 2 * m + 1 - m = m + 1 by omega] at hmul
      have hpf : p ∣ (2 * m + 1)! := hpp.dvd_factorial.mpr hp2
      rw [← hmul] at hpf
      have hnot1 : ¬ p ∣ m ! := mt hpp.dvd_factorial.mp (by omega)
      have hnot2 : ¬ p ∣ (m + 1)! := mt hpp.dvd_factorial.mp (by omega)
      rcases hpp.dvd_mul.mp hpf with h1 | h2
      · rcases hpp.dvd_mul.mp h1 with h3 | h4
        · exact h3
        · exact absurd h4 hnot1
      · exact absurd h2 hnot2
  have hCpos : 0 < (2 * m + 1).choose m := Nat.choose_pos (by omega)
  have hCle : (2 * m + 1).choose m ≤ 2 ^ (2 * m) := by
    have hsum := Nat.sum_range_choose (2 * m + 1)
    have hsub : ({m, m + 1} : Finset ℕ) ⊆ Finset.range (2 * m + 1 + 1) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at hj ⊢
      omega
    have hle : ∑ j ∈ ({m, m + 1} : Finset ℕ), (2 * m + 1).choose j ≤ 2 ^ (2 * m + 1) := by
      rw [← hsum]
      exact Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair (by omega : m ≠ m + 1)] at hle
    have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
      rw [← Nat.choose_symm (show m ≤ 2 * m + 1 by omega)]
      congr 1; omega
    rw [hsymm, pow_succ] at hle
    omega
  have hPpos : 0 < ∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p := by
    apply Finset.prod_pos
    intro p hp; rw [Finset.mem_filter] at hp; exact hp.2.pos
  have hPle : ∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p ≤ 2 ^ (2 * m) :=
    le_trans (Nat.le_of_dvd hCpos hdvd) hCle
  calc ∑ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, Real.log (p : ℝ)
      = Real.log (∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp; rw [Finset.mem_filter] at hp; exact Nat.cast_ne_zero.mpr hp.2.ne_zero
    _ = Real.log ((∏ p ∈ (Finset.Ioc (m + 1) (2 * m + 1)).filter Nat.Prime, p : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
    _ ≤ Real.log ((2 ^ (2 * m) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hPpos) (by exact_mod_cast hPle)
    _ = 2 * (m : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]; push_cast; ring

lemma theta_le_two_log_two : ∀ x : ℕ, theta x ≤ 2 * Real.log 2 * (x : ℝ) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rcases (show x = 0 ∨ x = 1 ∨ x = 2 ∨ (3 ≤ x ∧ x % 2 = 1) ∨ (4 ≤ x ∧ x % 2 = 0) by omega) with
      rfl | rfl | rfl | ⟨hx3, hodd⟩ | ⟨hx4, heven⟩
    · simp [theta]
    · have h1 : (Finset.Icc 1 1).filter Nat.Prime = ∅ := by decide
      rw [theta, h1, Finset.sum_empty, Nat.cast_one, mul_one]; linarith
    · have : (Finset.Icc 1 2).filter Nat.Prime = {2} := by decide
      simp [theta, this]; linarith
    · obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m + 1 := ⟨x / 2, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hih := ih (m + 1) (by omega)
      have hsub := theta_sub_odd_le m hm1
      push_cast at hih ⊢
      linarith
    · have hnotp : ¬ x.Prime := by
        intro hp
        have := hp.eq_two_or_odd
        omega
      have heq : theta x = theta (x - 1) := by
        unfold theta
        congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hp1, hpx⟩, hpp⟩
          refine ⟨⟨hp1, ?_⟩, hpp⟩
          have hne : p ≠ x := fun h => hnotp (h ▸ hpp)
          omega
        · rintro ⟨⟨hp1, hpx⟩, hpp⟩
          exact ⟨⟨hp1, by omega⟩, hpp⟩
      rw [heq]
      have hih := ih (x - 1) (by omega)
      have hcast : ((x - 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast Nat.sub_le x 1
      nlinarith

lemma minFac_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) : (p ^ k).minFac = p := by
  have hne : p ^ k ≠ 1 := (one_lt_pow₀ hp.one_lt (by omega)).ne'
  have hmp : (p ^ k).minFac.Prime := Nat.minFac_prime hne
  exact (Nat.prime_dvd_prime_iff_eq hmp hp).mp (hmp.dvd_of_dvd_pow (Nat.minFac_dvd _))

lemma psi_sub_theta_le (m : ℕ) (hm : 1 ≤ m) :
    psi m - theta m ≤
      2 * Real.log 2 * Real.sqrt (m : ℝ) +
      2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 3) +
      2 * (m : ℝ) ^ ((1 : ℝ) / 4) * Real.log (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiff : psi m - theta m = ∑ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime), Λ d := by
    unfold psi theta
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 m) Nat.Prime (fun d => Λ d)
    have hpr : ∑ p ∈ (Finset.Icc 1 m).filter Nat.Prime, Λ p =
        ∑ p ∈ (Finset.Icc 1 m).filter Nat.Prime, Real.log (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp; rw [Finset.mem_filter] at hp
      exact ArithmeticFunction.vonMangoldt_apply_prime hp.2
    linarith
  rw [hdiff]
  -- Bound by summing over prime powers p^j with 2 ≤ j ≤ Nat.log 2 m
  set L := Nat.log 2 m
  set S_pairs := (Finset.Icc 2 L).biUnion (fun j =>
    ((Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m)).map
      ⟨fun p => (p, j), fun _ _ h => (Prod.mk.inj h).1⟩)
  have hsum_le : ∑ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime), Λ d ≤
      ∑ pj ∈ S_pairs, Real.log (pj.1 : ℝ) := by
    -- Map each non-prime prime-power d = p^j to (p, j) ∈ S_pairs
    have hzero : ∑ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime), Λ d =
        ∑ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime ∧ IsPrimePow d), Λ d := by
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 m).filter (fun d => ¬ d.Prime))
        IsPrimePow]
      have h0 : ∑ d ∈ ((Finset.Icc 1 m).filter (fun d => ¬ d.Prime)).filter (fun d => ¬ IsPrimePow d),
          Λ d = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        rw [Finset.mem_filter] at hd
        exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hd.2
      rw [h0, add_zero, Finset.filter_filter]
    rw [hzero]
    let f : ℕ → ℕ × ℕ := fun d => (d.minFac, d.factorization d.minFac)
    have hf_maps : ∀ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime ∧ IsPrimePow d),
        f d ∈ S_pairs := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdm⟩, hnotp, hpp⟩ := hd
      obtain ⟨p, k, hp_prime, hk_pos, rfl⟩ := hpp
      have hp : p.Prime := Nat.prime_iff.mpr hp_prime
      have hmin : (p ^ k).minFac = p := minFac_prime_pow hp hk_pos
      have hfac : (p ^ k).factorization p = k := by
        rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
      have hk2 : 2 ≤ k := by
        by_contra h
        have hk1 : k = 1 := by omega
        subst hk1; simp [hp] at hnotp
      have hkL : k ≤ L := by
        apply Nat.le_log_of_pow_le (by omega)
        calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
          _ ≤ m := hdm
      simp only [S_pairs, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_map, Finset.mem_filter,
        f, hmin, hfac]
      refine ⟨k, ⟨hk2, hkL⟩, p, ⟨⟨hp.one_le, le_trans (Nat.le_self_pow (by omega) p) hdm⟩,
        hp, hdm⟩, rfl⟩
    have hf_inj : Set.InjOn f ((Finset.Icc 1 m).filter (fun d => ¬ d.Prime ∧ IsPrimePow d)) := by
      intro d1 hd1 d2 hd2 hfeq
      simp only [Finset.mem_coe, Finset.mem_filter] at hd1 hd2
      obtain ⟨p1, k1, hp1, hk1, rfl⟩ := hd1.2.2
      obtain ⟨p2, k2, hp2, hk2, rfl⟩ := hd2.2.2
      have h1 : p1.Prime := Nat.prime_iff.mpr hp1
      have h2 : p2.Prime := Nat.prime_iff.mpr hp2
      simp only [f, minFac_prime_pow h1 hk1, minFac_prime_pow h2 hk2,
        Nat.Prime.factorization_pow h1, Nat.Prime.factorization_pow h2,
        Finsupp.single_eq_same, Prod.mk.injEq] at hfeq
      rw [hfeq.1, hfeq.2]
    have hf_val : ∀ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime ∧ IsPrimePow d),
        Λ d = Real.log ((f d).1 : ℝ) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨p, k, hp, hk, rfl⟩ := hd.2.2
      have h1 : p.Prime := Nat.prime_iff.mpr hp
      simp only [f, minFac_prime_pow h1 hk]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime h1]
    calc ∑ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime ∧ IsPrimePow d), Λ d
        = ∑ d ∈ (Finset.Icc 1 m).filter (fun d => ¬ d.Prime ∧ IsPrimePow d),
            Real.log ((f d).1 : ℝ) := Finset.sum_congr rfl hf_val
      _ = ∑ pj ∈ ((Finset.Icc 1 m).filter (fun d => ¬ d.Prime ∧ IsPrimePow d)).image f,
            Real.log (pj.1 : ℝ) :=
          (Finset.sum_image (f := fun pj : ℕ × ℕ => Real.log (pj.1 : ℝ)) hf_inj).symm
      _ ≤ ∑ pj ∈ S_pairs, Real.log (pj.1 : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro pj hpj
            rw [Finset.mem_image] at hpj
            obtain ⟨d, hd, rfl⟩ := hpj
            exact hf_maps d hd
          · intro pj hpj _
            simp only [S_pairs, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter] at hpj
            obtain ⟨_, _, p, hp, rfl⟩ := hpj
            exact Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)
  -- Expand S_pairs into a sum over j ∈ Icc 2 L
  have hS_eq : ∑ pj ∈ S_pairs, Real.log (pj.1 : ℝ) =
      ∑ j ∈ Finset.Icc 2 L,
        ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ) := by
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_map]
      rfl
    · intro j1 _ j2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map] at hx1 hx2
      obtain ⟨_, _, rfl⟩ := hx1
      obtain ⟨_, _, h⟩ := hx2
      exact hne (Prod.mk.inj h).2.symm
  -- Helper: inner sum for j is bounded by theta ⌊m^(1/j)⌋
  have hinner_le : ∀ j : ℕ, 1 ≤ j →
      ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ) ≤
        2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := by
    intro j hj
    set r : ℕ := Nat.floor ((m : ℝ) ^ ((1 : ℝ) / (j : ℝ)))
    have hsub : (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m) ⊆
        (Finset.Icc 1 r).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      refine ⟨⟨hp.1.1, ?_⟩, hp.2.1⟩
      apply Nat.le_floor
      have hpj : (p : ℝ) ^ j ≤ (m : ℝ) := by exact_mod_cast hp.2.2
      have hjpos : (0 : ℝ) < (j : ℝ) := by positivity
      calc (p : ℝ) = ((p : ℝ) ^ (j : ℝ)) ^ ((1 : ℝ) / (j : ℝ)) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg p), mul_one_div_cancel hjpos.ne', Real.rpow_one]
        _ ≤ (m : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := by
            apply Real.rpow_le_rpow (by positivity) _ (by positivity)
            rw [Real.rpow_natCast]
            exact hpj
    calc ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ)
        ≤ theta r := by
          unfold theta
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p hp _
          rw [Finset.mem_filter] at hp
          exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
      _ ≤ 2 * Real.log 2 * (r : ℝ) := theta_le_two_log_two r
      _ ≤ 2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  -- Split j ∈ Icc 2 L into j = 2, j = 3, and j ∈ Icc 4 L
  have hterm_nn : ∀ j : ℕ, 0 ≤
      ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ) := by
    intro j
    apply Finset.sum_nonneg
    intro p hp; rw [Finset.mem_filter] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.1.one_le)
  have h2_bound : ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ 2 ≤ m), Real.log (p : ℝ) ≤
      2 * Real.log 2 * Real.sqrt (m : ℝ) := by
    have := hinner_le 2 (by omega)
    rw [Nat.cast_ofNat, ← Real.sqrt_eq_rpow] at this
    exact this
  have h3_bound : ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ 3 ≤ m), Real.log (p : ℝ) ≤
      2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 3) := by
    simpa using hinner_le 3 (by omega)
  have h4_bound : ∑ j ∈ Finset.Icc 4 L,
      ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ) ≤
      2 * (m : ℝ) ^ ((1 : ℝ) / 4) * Real.log (m : ℝ) := by
    calc ∑ j ∈ Finset.Icc 4 L,
          ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ)
        ≤ ∑ _j ∈ Finset.Icc 4 L, (2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 4)) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_Icc] at hj
          calc ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ)
              ≤ 2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / (j : ℝ)) := hinner_le j (by omega)
            _ ≤ 2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
                exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hj.1)
      _ = ((Finset.Icc 4 L).card : ℝ) * (2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 4)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L : ℝ) * (2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 4)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : (Finset.Icc 4 L).card ≤ L := by simp
          exact_mod_cast hcard
      _ = 2 * (m : ℝ) ^ ((1 : ℝ) / 4) * ((L : ℝ) * Real.log 2) := by ring
      _ ≤ 2 * (m : ℝ) ^ ((1 : ℝ) / 4) * Real.log (m : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hpow : 2 ^ L ≤ m := Nat.pow_log_le_self 2 (by omega)
          have hpowR : (2 : ℝ) ^ L ≤ (m : ℝ) := by exact_mod_cast hpow
          have hlog := Real.log_le_log (by positivity) hpowR
          rwa [Real.log_pow] at hlog
  -- Combine cases for L
  have htotal : ∑ j ∈ Finset.Icc 2 L,
      ∑ p ∈ (Finset.Icc 1 m).filter (fun p => p.Prime ∧ p ^ j ≤ m), Real.log (p : ℝ) ≤
      2 * Real.log 2 * Real.sqrt (m : ℝ) +
      2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 3) +
      2 * (m : ℝ) ^ ((1 : ℝ) / 4) * Real.log (m : ℝ) := by
    have hnn1 : 0 ≤ 2 * Real.log 2 * Real.sqrt (m : ℝ) := by positivity
    have hnn2 : 0 ≤ 2 * Real.log 2 * (m : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have hnn3 : 0 ≤ 2 * (m : ℝ) ^ ((1 : ℝ) / 4) * Real.log (m : ℝ) :=
      mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hm))
    rcases (show L < 2 ∨ L = 2 ∨ L = 3 ∨ 4 ≤ L by omega) with hL | hL | hL | hL
    · have : Finset.Icc 2 L = ∅ := Finset.Icc_eq_empty (by omega)
      rw [this, Finset.sum_empty]; linarith
    · rw [hL, Finset.Icc_self, Finset.sum_singleton]; linarith
    · have : Finset.Icc 2 L = {2, 3} := by rw [hL]; decide
      rw [this, Finset.sum_pair (by omega)]; linarith
    · have hunion : Finset.Icc 2 L = insert 2 (insert 3 (Finset.Icc 4 L)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hunion, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      linarith
  linarith

/-! ## Step 6: Elementary binomial lower bound `log C(n, k) ≥ n H(k/n) - log(n + 1)` -/

lemma log_choose_ge_ent (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    (n : ℝ) * ent ((k : ℝ) / (n : ℝ)) - Real.log ((n + 1 : ℕ) : ℝ) ≤
      Real.log (n.choose k : ℝ) := by
  set α : ℝ := (k : ℝ) / (n : ℝ)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast hkn)
  have h1α : 0 < 1 - α := by linarith
  let f : ℕ → ℝ := fun j => (n.choose j : ℝ) * α ^ j * (1 - α) ^ (n - j)
  -- Show f is nondecreasing for j < k and nonincreasing for j ≥ k
  have hf_inc : ∀ j : ℕ, j < k → f j ≤ f (j + 1) := by
    intro j hj
    have hjn : j < n := lt_trans hj hkn
    have hchoose : ((j + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ) =
        ((n - j : ℕ) : ℝ) * (n.choose j : ℝ) := by
      exact_mod_cast (by linarith [Nat.choose_succ_right_eq n j] :
        (j + 1) * n.choose (j + 1) = (n - j) * n.choose j)
    have hpow : (1 - α) ^ (n - j) = (1 - α) * (1 - α) ^ (n - (j + 1)) := by
      rw [← _root_.pow_succ', show n - (j + 1) + 1 = n - j by omega]
    have hα_eq : α = (k : ℝ) / (n : ℝ) := rfl
    have h1α_eq : 1 - α = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
      rw [hα_eq, Nat.cast_sub (le_of_lt hkn)]
      field_simp
    have hdiff : ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) * (k : ℝ) := by
      have : (j + 1) * (n - k) ≤ (n - j) * k := by
        zify [show k ≤ n by omega, show j ≤ n by omega]
        nlinarith
      exact_mod_cast this
    have hratio : ((j + 1 : ℕ) : ℝ) * (1 - α) ≤ ((n - j : ℕ) : ℝ) * α := by
      rw [hα_eq, h1α_eq]
      have := div_le_div_of_nonneg_right hdiff hnpos.le
      linarith [mul_div_assoc ((j + 1 : ℕ) : ℝ) ((n - k : ℕ) : ℝ) (n : ℝ),
        mul_div_assoc ((n - j : ℕ) : ℝ) (k : ℝ) (n : ℝ)]
    have hfj1 : ((j + 1 : ℕ) : ℝ) * f (j + 1) =
        ((n - j : ℕ) : ℝ) * α * ((n.choose j : ℝ) * α ^ j * (1 - α) ^ (n - (j + 1))) := by
      simp only [f, pow_succ]
      calc ((j + 1 : ℕ) : ℝ) * ((n.choose (j + 1) : ℝ) * (α ^ j * α) * (1 - α) ^ (n - (j + 1)))
          = (((j + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ)) * (α ^ j * α * (1 - α) ^ (n - (j + 1))) := by ring
        _ = ((n - j : ℕ) : ℝ) * (n.choose j : ℝ) * (α ^ j * α * (1 - α) ^ (n - (j + 1))) := by rw [hchoose]
        _ = _ := by ring
    have hfj : ((j + 1 : ℕ) : ℝ) * f j =
        ((j + 1 : ℕ) : ℝ) * (1 - α) * ((n.choose j : ℝ) * α ^ j * (1 - α) ^ (n - (j + 1))) := by
      simp only [f, hpow]; ring
    have hmul : ((j + 1 : ℕ) : ℝ) * f j ≤ ((j + 1 : ℕ) : ℝ) * f (j + 1) := by
      rw [hfj, hfj1]
      apply mul_le_mul_of_nonneg_right hratio
      positivity
    exact le_of_mul_le_mul_left hmul (by positivity)
  have hf_dec : ∀ j : ℕ, k ≤ j → j < n → f (j + 1) ≤ f j := by
    intro j hjk hjn
    have hchoose : ((j + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ) =
        ((n - j : ℕ) : ℝ) * (n.choose j : ℝ) := by
      exact_mod_cast (by linarith [Nat.choose_succ_right_eq n j] :
        (j + 1) * n.choose (j + 1) = (n - j) * n.choose j)
    have hpow : (1 - α) ^ (n - j) = (1 - α) * (1 - α) ^ (n - (j + 1)) := by
      rw [← _root_.pow_succ', show n - (j + 1) + 1 = n - j by omega]
    have hα_eq : α = (k : ℝ) / (n : ℝ) := rfl
    have h1α_eq : 1 - α = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
      rw [hα_eq, Nat.cast_sub (le_of_lt hkn)]
      field_simp
    have hdiff : ((n - j : ℕ) : ℝ) * (k : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by
      have : (n - j) * k ≤ (j + 1) * (n - k) := by
        zify [show k ≤ n by omega, show j ≤ n by omega]
        nlinarith
      exact_mod_cast this
    have hratio : ((n - j : ℕ) : ℝ) * α ≤ ((j + 1 : ℕ) : ℝ) * (1 - α) := by
      rw [hα_eq, h1α_eq]
      have := div_le_div_of_nonneg_right hdiff hnpos.le
      linarith [mul_div_assoc ((j + 1 : ℕ) : ℝ) ((n - k : ℕ) : ℝ) (n : ℝ),
        mul_div_assoc ((n - j : ℕ) : ℝ) (k : ℝ) (n : ℝ)]
    have hfj1 : ((j + 1 : ℕ) : ℝ) * f (j + 1) =
        ((n - j : ℕ) : ℝ) * α * ((n.choose j : ℝ) * α ^ j * (1 - α) ^ (n - (j + 1))) := by
      simp only [f, pow_succ]
      calc ((j + 1 : ℕ) : ℝ) * ((n.choose (j + 1) : ℝ) * (α ^ j * α) * (1 - α) ^ (n - (j + 1)))
          = (((j + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ)) * (α ^ j * α * (1 - α) ^ (n - (j + 1))) := by ring
        _ = ((n - j : ℕ) : ℝ) * (n.choose j : ℝ) * (α ^ j * α * (1 - α) ^ (n - (j + 1))) := by rw [hchoose]
        _ = _ := by ring
    have hfj : ((j + 1 : ℕ) : ℝ) * f j =
        ((j + 1 : ℕ) : ℝ) * (1 - α) * ((n.choose j : ℝ) * α ^ j * (1 - α) ^ (n - (j + 1))) := by
      simp only [f, hpow]; ring
    have hmul : ((j + 1 : ℕ) : ℝ) * f (j + 1) ≤ ((j + 1 : ℕ) : ℝ) * f j := by
      rw [hfj, hfj1]
      apply mul_le_mul_of_nonneg_right hratio
      positivity
    exact le_of_mul_le_mul_left hmul (by positivity)
  have hf_inc_add : ∀ d j : ℕ, j + d ≤ k → f j ≤ f (j + d) := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hjd
      exact le_trans (ih j (by omega)) (hf_inc (j + d) (by omega))
  have hf_dec_add : ∀ d j : ℕ, k ≤ j → j + d ≤ n → f (j + d) ≤ f j := by
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ d ih =>
      intro j hkj hjd
      exact le_trans (hf_dec (j + d) (by omega) (by omega)) (ih j hkj (by omega))
  have hf_max : ∀ j ∈ Finset.range (n + 1), f j ≤ f k := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hjk : j ≤ k
    · simpa [Nat.add_sub_of_le hjk] using hf_inc_add (k - j) j (by omega)
    · simpa [Nat.add_sub_of_le (show k ≤ j by omega)] using
        hf_dec_add (j - k) k (le_refl k) (by omega)
  -- Binomial theorem: ∑ f j = 1
  have hbinom : ∑ j ∈ Finset.range (n + 1), f j = 1 := by
    have h := add_pow α (1 - α) n
    rw [add_sub_cancel, one_pow] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f]; ring
  have h1le : 1 ≤ ((n + 1 : ℕ) : ℝ) * f k := by
    calc (1 : ℝ) = ∑ j ∈ Finset.range (n + 1), f j := hbinom.symm
      _ ≤ ∑ _j ∈ Finset.range (n + 1), f k := Finset.sum_le_sum hf_max
      _ = ((n + 1 : ℕ) : ℝ) * f k := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfk_pos : 0 < f k := by
    simp only [f]
    have hCpos : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos (le_of_lt hkn)
    positivity
  have hlog := Real.log_le_log zero_lt_one h1le
  rw [Real.log_one, Real.log_mul (by positivity) hfk_pos.ne'] at hlog
  have hlog_fk : Real.log (f k) =
      Real.log (n.choose k : ℝ) + (k : ℝ) * Real.log α + ((n - k : ℕ) : ℝ) * Real.log (1 - α) := by
    simp only [f]
    have hCpos : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast Nat.choose_pos (le_of_lt hkn)
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul hCpos.ne' (by positivity),
      Real.log_pow, Real.log_pow]
  rw [hlog_fk] at hlog
  have hnk_eq : (n : ℝ) * ent α = -(k : ℝ) * Real.log α - ((n - k : ℕ) : ℝ) * Real.log (1 - α) := by
    unfold ent
    rw [Nat.cast_sub (le_of_lt hkn)]
    have h1 : (n : ℝ) * α = (k : ℝ) := mul_div_cancel₀ (k : ℝ) hnpos.ne'
    have h2 : (n : ℝ) * (1 - α) = (n : ℝ) - (k : ℝ) := by linarith
    calc (n : ℝ) * (-α * Real.log α - (1 - α) * Real.log (1 - α))
        = -((n : ℝ) * α) * Real.log α - ((n : ℝ) * (1 - α)) * Real.log (1 - α) := by ring
      _ = -(k : ℝ) * Real.log α - ((n : ℝ) - (k : ℝ)) * Real.log (1 - α) := by rw [h1, h2]
  linarith

/-! ## Step 7: Concavity of `ent`, numerical log bounds, and final contradiction -/

lemma x_mul_log_convex {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) * x + t * y) * Real.log ((1 - t) * x + t * y) ≤
      (1 - t) * (x * Real.log x) + t * (y * Real.log y) := by
  set z := (1 - t) * x + t * y
  have hz : 0 < z := by
    simp only [z]
    rcases eq_or_lt_of_le ht0 with rfl | ht
    · linarith
    · nlinarith
  have h1 : Real.log (z / x) ≤ z / x - 1 := Real.log_le_sub_one_of_pos (div_pos hz hx)
  rw [Real.log_div hz.ne' hx.ne'] at h1
  have h2 : Real.log (z / y) ≤ z / y - 1 := Real.log_le_sub_one_of_pos (div_pos hz hy)
  rw [Real.log_div hz.ne' hy.ne'] at h2
  have hm1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (1 - t) * x by nlinarith)
  have hm2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ t * y by nlinarith)
  have hs1 : (1 - t) * x * (z / x - 1) = (1 - t) * (z - x) := by field_simp
  have hs2 : t * y * (z / y - 1) = t * (z - y) := by field_simp
  rw [hs1] at hm1
  rw [hs2] at hm2
  have hsum : (1 - t) * (z - x) + t * (z - y) = 0 := by simp only [z]; ring
  have hadd : (1 - t) * x * (Real.log z - Real.log x) + t * y * (Real.log z - Real.log y) ≤ 0 := by
    linarith
  have hlin : z * Real.log z - (1 - t) * (x * Real.log x) - t * (y * Real.log y) =
      (1 - t) * x * (Real.log z - Real.log x) + t * y * (Real.log z - Real.log y) := by
    simp only [z]; ring
  linarith

lemma ent_concave {a b t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * ent a + t * ent b ≤ ent ((1 - t) * a + t * b) := by
  have h1 := x_mul_log_convex ha0 hb0 ht0 ht1
  have h2 := x_mul_log_convex (sub_pos.mpr ha1) (sub_pos.mpr hb1) ht0 ht1
  have hsub : (1 - t) * (1 - a) + t * (1 - b) = 1 - ((1 - t) * a + t * b) := by ring
  rw [hsub] at h2
  unfold ent
  linarith

-- Elementary Taylor bounds on `Real.exp` for `0 ≤ x ≤ 1/2` using `Real.exp_bound`
lemma log_lt_of_exp_gt {a r : ℝ} (ha : 0 < a) (h : a < Real.exp r) : Real.log a < r := by
  rwa [← Real.exp_lt_exp, Real.exp_log ha]

lemma lt_log_of_exp_lt {a r : ℝ} (ha : 0 < a) (h : Real.exp r < a) : r < Real.log a := by
  rwa [← Real.exp_lt_exp, Real.exp_log ha]

lemma exp_le_poly5 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 600 := by
  have h := Real.exp_bound (x := x) (n := 6) (by rw [abs_of_nonneg hx0]; linarith) (by norm_num)
  rw [abs_le] at h
  have hsum : ∑ m ∈ Finset.range 6, x ^ m / (m ! : ℝ) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum, abs_of_nonneg hx0] at h
  have hrem : x ^ 6 * ((6 + 1 : ℝ) / ((6 ! : ℕ) * 6)) ≤ x ^ 6 / 600 := by
    have hx6 : 0 ≤ x ^ 6 := by positivity
    norm_num [Nat.factorial]
    nlinarith
  linarith [h.2]

lemma poly5_le_exp {x : ℝ} (hx0 : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx0 6
  have hsum : ∑ m ∈ Finset.range 6, x ^ m / (m ! : ℝ) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  linarith

lemma log_two_bounds : (0.693147 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.693148 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

lemma log_three_lt : Real.log 3 < 1.0987 := by
  have h2 := log_two_bounds.2
  have h32 : Real.log (3 / 2 : ℝ) < 0.4055 := by
    apply log_lt_of_exp_gt (by norm_num)
    have := poly5_le_exp (x := 0.4055) (by norm_num)
    linarith [show (3 / 2 : ℝ) < 1 + 0.4055 + 0.4055 ^ 2 / 2 + 0.4055 ^ 3 / 6 +
      0.4055 ^ 4 / 24 + 0.4055 ^ 5 / 120 by norm_num]
  rw [Real.log_div (by norm_num) (by norm_num)] at h32
  linarith

lemma log_five_lt : Real.log 5 < 1.6095 := by
  have h2 := log_two_bounds.2
  have h54 : Real.log (5 / 4 : ℝ) < 0.2232 := by
    apply log_lt_of_exp_gt (by norm_num)
    have := poly5_le_exp (x := 0.2232) (by norm_num)
    linarith [show (5 / 4 : ℝ) < 1 + 0.2232 + 0.2232 ^ 2 / 2 + 0.2232 ^ 3 / 6 +
      0.2232 ^ 4 / 24 + 0.2232 ^ 5 / 120 by norm_num]
  rw [Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h54
  push_cast at h54
  linarith

lemma log_seven_gt : (1.9459 : ℝ) < Real.log 7 := by
  have h2 := log_two_bounds.1
  have h87 : Real.log (8 / 7 : ℝ) < 0.13354 := by
    apply log_lt_of_exp_gt (by norm_num)
    have := poly5_le_exp (x := 0.13354) (by norm_num)
    linarith [show (8 / 7 : ℝ) < 1 + 0.13354 + 0.13354 ^ 2 / 2 + 0.13354 ^ 3 / 6 +
      0.13354 ^ 4 / 24 + 0.13354 ^ 5 / 120 by norm_num]
  rw [Real.log_div (by norm_num) (by norm_num),
    show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h87
  push_cast at h87
  linarith

lemma log_fourteen_div_thirteen_gt : (0.0741 : ℝ) < Real.log (14 / 13 : ℝ) := by
  apply lt_log_of_exp_lt (by norm_num)
  have := exp_le_poly5 (x := 0.0741) (by norm_num) (by norm_num)
  linarith [show 1 + 0.0741 + 0.0741 ^ 2 / 2 + 0.0741 ^ 3 / 6 + 0.0741 ^ 4 / 24 +
    0.0741 ^ 5 / 120 + 0.0741 ^ 6 / 600 < (14 / 13 : ℝ) by norm_num]

lemma A_const_lt : A_const < 0.9214 := by
  unfold A_const
  linarith [log_two_bounds.2, log_three_lt, log_five_lt]

lemma gap_lower_bound {α : ℝ} (hlo : 1 / 14 ≤ α) (hhi : α ≤ 1 / 2) :
    (0.007 : ℝ) ≤ ent α - ((6 / 5) * A_const - A_const * (1 - α)) := by
  -- Express α as convex combination of 1/14 and 1/2
  set t := (α - 1 / 14) / (1 / 2 - 1 / 14)
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by norm_num)
  have ht1 : t ≤ 1 := (div_le_one (by norm_num)).mpr (by linarith)
  have hα : (1 - t) * (1 / 14 : ℝ) + t * (1 / 2 : ℝ) = α := by
    simp only [t]; field_simp; ring
  have hconc := ent_concave (a := 1 / 14) (b := 1 / 2) (t := t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht0 ht1
  rw [hα] at hconc
  -- Evaluate endpoints
  have hA := A_const_lt
  have h14 : (0.007 : ℝ) ≤ ent (1 / 14) - ((6 / 5) * A_const - A_const * (1 - 1 / 14)) := by
    unfold ent
    have hlog14 : Real.log (1 / 14 : ℝ) = -(Real.log 2 + Real.log 7) := by
      rw [Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub,
        show (14 : ℝ) = 2 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have hlog1314 : Real.log (1 - 1 / 14 : ℝ) = -Real.log (14 / 13 : ℝ) := by
      rw [show (1 - 1 / 14 : ℝ) = (14 / 13 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hlog14, hlog1314]
    linarith [log_two_bounds.1, log_seven_gt, log_fourteen_div_thirteen_gt]
  have h2 : (0.007 : ℝ) ≤ ent (1 / 2) - ((6 / 5) * A_const - A_const * (1 - 1 / 2)) := by
    unfold ent
    have hlog2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div one_ne_zero (by norm_num), Real.log_one, zero_sub]
    have h12 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [h12, hlog2]
    linarith [log_two_bounds.1]
  have hcomb : (1 - t) * (ent (1 / 14) - ((6 / 5) * A_const - A_const * (1 - 1 / 14))) +
      t * (ent (1 / 2) - ((6 / 5) * A_const - A_const * (1 - 1 / 2))) =
      ((1 - t) * ent (1 / 14) + t * ent (1 / 2)) - ((6 / 5) * A_const - A_const * (1 - α)) := by
    have : (1 - t) * (1 - 1 / 14 : ℝ) + t * (1 - 1 / 2 : ℝ) = 1 - α := by linarith
    nlinarith
  nlinarith

lemma log_six_gt : (1.7 : ℝ) < Real.log 6 := by
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h3 : (1.09 : ℝ) < Real.log 3 := by
    apply lt_log_of_exp_lt (by norm_num)
    have h32 : Real.exp (0.397 : ℝ) < 3 / 2 := by
      have := exp_le_poly5 (x := 0.397) (by norm_num) (by norm_num)
      linarith [show 1 + 0.397 + 0.397 ^ 2 / 2 + 0.397 ^ 3 / 6 + 0.397 ^ 4 / 24 +
        0.397 ^ 5 / 120 + 0.397 ^ 6 / 600 < (3 / 2 : ℝ) by norm_num]
    have h2 : Real.exp (0.693 : ℝ) < 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_lt_exp.mpr (by linarith [log_two_bounds.1])
    calc Real.exp (1.09 : ℝ) = Real.exp (0.693 + 0.397) := by norm_num
      _ = Real.exp 0.693 * Real.exp 0.397 := Real.exp_add _ _
      _ < 2 * (3 / 2) := mul_lt_mul'' h2 h32 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = 3 := by norm_num
  linarith [log_two_bounds.1]

lemma error_lt_margin {n : ℕ} (hn : 700000 ≤ n) :
    (5 * Real.log (n : ℝ) + 2) * (Real.log (n : ℝ) / Real.log 6 + 1) +
      (4 * Real.log (n : ℝ) + 3) +
      (2 * Real.log 2 * Real.sqrt (n : ℝ) +
       2 * Real.log 2 * (n : ℝ) ^ ((1 : ℝ) / 3) +
       2 * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log (n : ℝ)) +
      Real.log ((n + 1 : ℕ) : ℝ) <
      0.007 * (n : ℝ) := by
  have hnR : (700000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set u : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4)
  have hu4 : u ^ 4 = (n : ℝ) := by
    rw [show (u : ℝ) ^ 4 = ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) by norm_cast,
      ← Real.rpow_mul hnpos.le]
    norm_num
  have hu28 : (28 : ℝ) ≤ u := by
    have h28 : (28 : ℝ) ^ (4 : ℝ) ≤ (n : ℝ) := by norm_num; linarith
    calc (28 : ℝ) = ((28 : ℝ) ^ (4 : ℝ)) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ u := Real.rpow_le_rpow (by positivity) h28 (by norm_num)
  have hupos : 0 < u := by linarith
  -- Bound log n in terms of u
  have hlog28 : Real.log (28 : ℝ) < 3.41 := by
    have hlt : (28 : ℝ) < 2 * 3 * 5 := by norm_num
    have h := Real.log_lt_log (by norm_num) hlt
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)] at h
    linarith [log_two_bounds.2, log_three_lt, log_five_lt]
  have hlogu : Real.log u ≤ 2.41 + u / 28 := by
    have h1 : Real.log (u / 28) ≤ u / 28 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hupos.ne' (by norm_num)] at h1
    linarith
  have hlogn_eq : Real.log (n : ℝ) = 4 * Real.log u := by
    rw [← hu4, Real.log_pow]; push_cast; ring
  have hlogn_le : Real.log (n : ℝ) ≤ 9.64 + u / 7 := by linarith
  have hlogn_half : Real.log (n : ℝ) ≤ 0.5 * u := by linarith
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  -- Bound each piece
  -- Piece 1: (5 log n + 2) * (log n / log 6 + 1) ≤ 0.0013 * n
  have hlog6 : (1.7 : ℝ) < Real.log 6 := log_six_gt
  have hdiv6 : Real.log (n : ℝ) / Real.log 6 ≤ 0.3 * u := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith only [hlogn_half, hlog6, hupos]
  have hp1 : (5 * Real.log (n : ℝ) + 2) * (Real.log (n : ℝ) / Real.log 6 + 1) ≤ u ^ 2 := by
    have ha : 5 * Real.log (n : ℝ) + 2 ≤ 2.5 * u + 2 := by linarith
    have hb : Real.log (n : ℝ) / Real.log 6 + 1 ≤ 0.3 * u + 1 := by linarith
    have hprod := mul_le_mul ha hb (by positivity) (by positivity)
    nlinarith only [hprod, hu28]
  have hu2_le : u ^ 2 ≤ 0.0013 * (n : ℝ) := by
    have : (784 : ℝ) ≤ u ^ 2 := by nlinarith only [hu28]
    nlinarith only [hu4, this]
  -- Piece 2: 2 * log 2 * sqrt n ≤ 0.00181 * n
  have hsqrt : Real.sqrt (n : ℝ) = u ^ 2 := by
    rw [← hu4, show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlog2 := log_two_bounds.2
  have hlog2_pos : 0 < Real.log 2 := by linarith [log_two_bounds.1]
  have hp2 : 2 * Real.log 2 * Real.sqrt (n : ℝ) ≤ 0.00181 * (n : ℝ) := by
    rw [hsqrt]
    nlinarith only [hlog2, hlog2_pos, hu2_le, hnpos]
  -- Piece 3: 2 * log 2 * n^(1/3) ≤ 0.0002 * n
  have hcbrt : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (n : ℝ) / 7800 := by
    have h3 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (n : ℝ) := by
      rw [show ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast,
        ← Real.rpow_mul hnpos.le]
      norm_num
    have hle : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ≤ ((n : ℝ) / 7800) ^ 3 := by
      rw [h3]
      have h7800 : (7800 : ℝ) ^ 3 ≤ (n : ℝ) ^ 2 := by nlinarith only [hnR]
      have : (n : ℝ) * (7800 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by nlinarith only [h7800, hnpos]
      rw [div_pow]
      exact (le_div_iff₀ (by positivity)).mpr this
    have hnn2 : 0 ≤ (n : ℝ) / 7800 := by positivity
    by_contra hgt
    push Not at hgt
    have : ((n : ℝ) / 7800) ^ 3 < ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 :=
      pow_lt_pow_left₀ hgt hnn2 (by omega)
    linarith
  have hp3 : 2 * Real.log 2 * (n : ℝ) ^ ((1 : ℝ) / 3) ≤ 0.0002 * (n : ℝ) := by
    have hnn : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hnpos.le _
    nlinarith only [hlog2, hlog2_pos, hcbrt, hnn, hnpos]
  -- Piece 4: 2 * u * log n ≤ 0.0013 * n
  have hp4 : 2 * u * Real.log (n : ℝ) ≤ 0.0013 * (n : ℝ) := by
    have h1 : 2 * u * Real.log (n : ℝ) ≤ 2 * u * (9.64 + u / 7) := by
      nlinarith only [hlogn_le, hupos]
    have hu2 : (784 : ℝ) ≤ u ^ 2 := by nlinarith only [hu28]
    have h2 : 2 * (9.64 + u / 7) ≤ 0.0013 * u ^ 3 := by
      nlinarith only [hu28, hu2]
    have h3 : 2 * u * (9.64 + u / 7) ≤ 0.0013 * u ^ 4 := by
      nlinarith only [h2, hupos]
    linarith only [h1, h3, hu4]
  -- Piece 5: 4 log n + 3 + log(n + 1) ≤ 0.0002 * n
  have hlogn1 : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) + 1 := by
    have h : ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hnpos]; push_cast; linarith
    have h1 := Real.log_le_sub_one_of_pos (show 0 < ((n + 1 : ℕ) : ℝ) / (n : ℝ) by positivity)
    rw [Real.log_div (by positivity) hnpos.ne'] at h1
    linarith
  have hp5 : (4 * Real.log (n : ℝ) + 3) + Real.log ((n + 1 : ℕ) : ℝ) ≤ 0.0002 * (n : ℝ) := by
    have h1 : 5 * Real.log (n : ℝ) + 4 ≤ 2.5 * u + 4 := by linarith only [hlogn_half]
    have hu2 : (784 : ℝ) ≤ u ^ 2 := by nlinarith only [hu28]
    have hu3 : (21952 : ℝ) ≤ u ^ 3 := by nlinarith only [hu28, hu2]
    have h2 : 2.5 * u + 4 ≤ 0.0002 * u ^ 4 := by nlinarith only [hu28, hu3]
    linarith only [hlogn1, h1, h2, hu4]
  linarith only [hp1, hu2_le, hp2, hp3, hp4, hp5, hnpos]

/-! ## Main Theorem -/

theorem chebyshev_central_range (n k : ℕ) (h4 : 4 ≤ k) (h2k : 2 * k ≤ n) (h14k : n ≤ 14 * k)
    (hn : 700000 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_contra hcon
  push Not at hcon
  have hkn : k < n := by omega
  have hnk_pos : 1 ≤ n - k := by omega
  have hn_pos : 1 ≤ n := by omega
  -- Lower bound on log C(n, k)
  have hlo := log_choose_ge_ent n k (by omega) hkn
  -- Upper bound on log C(n, k)
  have hup := log_choose_le_theta_sub n k h2k hcon
  -- Bound theta n - theta (n - k) via psi
  have hth_n : theta n ≤ psi n := theta_le_psi n
  have hpsi_n := psi_upper n hn_pos
  have hpsi_nk := psi_lower (n - k) hnk_pos
  have hdiff_nk := psi_sub_theta_le (n - k) hnk_pos
  -- Monotonicity of error terms from n - k to n
  have hnk_le_n : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n k
  have hnk_posR : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk_pos
  have hlog_nk : Real.log ((n - k : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hnk_posR hnk_le_n
  have hsqrt_nk : Real.sqrt ((n - k : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt hnk_le_n
  have hcbrt_nk : ((n - k : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ (n : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hnk_posR.le hnk_le_n (by norm_num)
  have h4rt_nk : ((n - k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hnk_posR.le hnk_le_n (by norm_num)
  have h4log_nk : ((n - k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) * Real.log ((n - k : ℕ) : ℝ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log (n : ℝ) :=
    mul_le_mul h4rt_nk hlog_nk (Real.log_nonneg (by exact_mod_cast hnk_pos)) (by positivity)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Express (n - k : ℝ) = n * (1 - α)
  set α : ℝ := (k : ℝ) / (n : ℝ)
  have hnk_alpha : ((n - k : ℕ) : ℝ) = (n : ℝ) * (1 - α) := by
    rw [Nat.cast_sub (le_of_lt hkn)]
    simp only [α]
    have hnpos : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hα_lo : 1 / 14 ≤ α := by
    simp only [α]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    exact_mod_cast (by omega : 1 * n ≤ k * 14)
  have hα_hi : α ≤ 1 / 2 := by
    simp only [α]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    exact_mod_cast (by omega : k * 2 ≤ 1 * n)
  have hgap := gap_lower_bound hα_lo hα_hi
  have herr := error_lt_margin hn
  have hpsi_nk' : A_const * ((n : ℝ) * (1 - α)) - 4 * Real.log (n : ℝ) - 3 ≤ psi (n - k) := by
    rw [← hnk_alpha]
    linarith only [hpsi_nk, hlog_nk]
  have hdiff_nk' : psi (n - k) - theta (n - k) ≤
      2 * Real.log 2 * Real.sqrt (n : ℝ) +
      2 * Real.log 2 * (n : ℝ) ^ ((1 : ℝ) / 3) +
      2 * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log (n : ℝ) := by
    nlinarith only [hdiff_nk, hsqrt_nk, hcbrt_nk, h4log_nk, hlog2_pos]
  have hmain : (n : ℝ) * (ent α - ((6 / 5) * A_const - A_const * (1 - α))) ≤
      (5 * Real.log (n : ℝ) + 2) * (Real.log (n : ℝ) / Real.log 6 + 1) +
      (4 * Real.log (n : ℝ) + 3) +
      (2 * Real.log 2 * Real.sqrt (n : ℝ) +
       2 * Real.log 2 * (n : ℝ) ^ ((1 : ℝ) / 3) +
       2 * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log (n : ℝ)) +
      Real.log ((n + 1 : ℕ) : ℝ) := by
    linarith only [hlo, hup, hth_n, hpsi_n, hpsi_nk', hdiff_nk']
  have hmargin : 0.007 * (n : ℝ) ≤
      (n : ℝ) * (ent α - ((6 / 5) * A_const - A_const * (1 - α))) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    nlinarith only [hgap, hnpos]
  linarith only [hmain, hmargin, herr]

end OMA.Erdos384Cheb


/-!
# Erdos384.erdos_384.R1.H2: Selberg upper bound sieve, Sieve-30/210, Prime Chains, and Finite Range

This file proves all regimes of `Erdos384.erdos_384.R1.H2` except the central Chebyshev range
`2 * k ≤ n ≤ 14 * k` with `n ≥ 700000` (which is proved in `erdos384_chebyshev.lean`).
-/

namespace OMA.Erdos384Selberg

open Nat Finset Real

/-! ## Section 1: Exact Composite-Product Identity & Kummer Divisibility -/

/-- If `k / p^j + (n - k) / p^j < n / p^j` for some prime `p` and `j ≥ 1`, then `p ∣ n.choose k`. -/
lemma dvd_choose_of_carry {n k p j : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hj : 1 ≤ j)
    (hcarry : k / p ^ j + (n - k) / p ^ j < n / p ^ j) : p ∣ n.choose k := by
  have hC0 : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hfact := Nat.choose_mul_factorial_mul_factorial hkn
  have hfac_eq : (n.choose k).factorization p + (k !).factorization p + ((n - k) !).factorization p =
      (n !).factorization p := by
    have h1 : (n.choose k * k ! * (n - k) !).factorization p = (n !).factorization p := by
      rw [hfact]
    rw [Nat.factorization_mul (mul_ne_zero hC0 (Nat.factorial_ne_zero k))
          (Nat.factorial_ne_zero (n - k)),
        Nat.factorization_mul hC0 (Nat.factorial_ne_zero k)] at h1
    simpa [Finsupp.add_apply] using h1
  set b := max (Nat.log p n + 1) (j + 1)
  have hb_n : Nat.log p n < b := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hb_k : Nat.log p k < b := lt_of_le_of_lt (Nat.log_mono_right hkn) hb_n
  have hb_nk : Nat.log p (n - k) < b := lt_of_le_of_lt (Nat.log_mono_right (Nat.sub_le n k)) hb_n
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      Nat.factorization_def _ hp, Nat.factorization_def _ hp] at hfac_eq
  have : Fact p.Prime := ⟨hp⟩
  have hpn : padicValNat p (n !) = ∑ i ∈ Ico 1 b, n / p ^ i := padicValNat_factorial hb_n
  have hpk : padicValNat p (k !) = ∑ i ∈ Ico 1 b, k / p ^ i := padicValNat_factorial hb_k
  have hpnk : padicValNat p ((n - k) !) = ∑ i ∈ Ico 1 b, (n - k) / p ^ i := padicValNat_factorial hb_nk
  rw [hpn, hpk, hpnk] at hfac_eq
  have hlt : ∑ i ∈ Ico 1 b, (k / p ^ i + (n - k) / p ^ i) < ∑ i ∈ Ico 1 b, n / p ^ i := by
    apply Finset.sum_lt_sum
    · intro i _
      have hpos : 0 < p ^ i := pow_pos hp.pos i
      have h1 := Nat.div_add_mod k (p ^ i)
      have h2 := Nat.div_add_mod (n - k) (p ^ i)
      have h3 : p ^ i * (k / p ^ i + (n - k) / p ^ i) ≤ n := by
        calc p ^ i * (k / p ^ i + (n - k) / p ^ i)
            = p ^ i * (k / p ^ i) + p ^ i * ((n - k) / p ^ i) := by ring
          _ ≤ k + (n - k) := Nat.add_le_add (Nat.mul_div_le k (p ^ i)) (Nat.mul_div_le (n - k) (p ^ i))
          _ = n := by omega
      exact (Nat.le_div_iff_mul_le hpos).mpr (by linarith)
    · refine ⟨j, Finset.mem_Ico.mpr ⟨hj, lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)⟩,
        hcarry⟩
  rw [Finset.sum_add_distrib] at hlt
  have hpos_val : 0 < (n.choose k).factorization p := by
    rw [Nat.factorization_def _ hp]; omega
  exact (hp.dvd_iff_one_le_factorization hC0).mpr hpos_val

/-- Prime-in-interval lemma 1: if `k < p` and `n - k < 2 * p ≤ n`, then `p ∣ n.choose k`. -/
lemma dvd_choose_of_prime_half {n k p : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hkp : k < p) (h1 : n - k < 2 * p) (h2 : 2 * p ≤ n) :
    p ∣ n.choose k ∧ 2 * p ≤ n := by
  refine ⟨dvd_choose_of_carry hp hkn le_rfl ?_, h2⟩
  rw [pow_one]
  have hk0 : k / p = 0 := Nat.div_eq_of_lt hkp
  have hnk1 : (n - k) / p ≤ 1 := by
    have : (n - k) / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
    omega
  have hn2 : 2 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
  omega

/-- Prime-in-interval lemma 2: if `2 * k ≤ n` and `n - k < 2 * p` and `3 * p ≤ n`,
then `p ∣ n.choose k` and `2 * p ≤ n`. -/
lemma dvd_choose_of_prime_third {n k p : ℕ} (hp : p.Prime) (h2k : 2 * k ≤ n)
    (h1 : n - k < 2 * p) (h2 : 3 * p ≤ n) :
    p ∣ n.choose k ∧ 2 * p ≤ n := by
  refine ⟨dvd_choose_of_carry hp (by omega) le_rfl ?_, by omega⟩
  rw [pow_one]
  have hk1 : k / p ≤ 1 := by
    have : k / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
    omega
  have hnk1 : (n - k) / p ≤ 1 := by
    have : (n - k) / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
    omega
  have hn3 : 3 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
  omega

/-- Under the contradiction hypothesis `∀ p, p.Prime → p ∣ n.choose k → n < 2 * p`,
`n.choose k` equals the product of primes in `(n - k, n]`, and the product of non-primes
in `(n - k, n]` equals `k!`. -/
lemma prod_nonprimes_eq_factorial {n k : ℕ} (hk : 2 ≤ k) (h2k : 2 * k ≤ n)
    (hcon : ∀ p : ℕ, p.Prime → p ∣ n.choose k → n < 2 * p) :
    ∏ m ∈ (Ioc (n - k) n).filter (fun m => ¬ m.Prime), m = k ! := by
  have hkn : k ≤ n := by omega
  have hC0 : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hprod : ∏ m ∈ Ioc (n - k) n, m = k ! * n.choose k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    apply Finset.prod_nbij' (fun m => n - m) (fun i => n - i)
    · intro a ha; simp only [mem_Ioc] at ha; simp only [mem_range]; omega
    · intro a ha; simp only [mem_range] at ha; simp only [mem_Ioc]; omega
    · intro a ha; simp only [mem_Ioc] at ha; omega
    · intro a ha; simp only [mem_range] at ha; omega
    · intro a ha; simp only [mem_Ioc] at ha; omega
  have hpf_eq : (n.choose k).primeFactors = (Ioc (n - k) n).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primeFactors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hpp, hpd, -⟩
      have h2p := hcon p hpp hpd
      have hdesc : p ∣ ∏ m ∈ Ioc (n - k) n, m := by
        rw [hprod]; exact dvd_mul_of_dvd_right hpd _
      obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdesc
      rw [mem_Ioc] at hm
      obtain ⟨c, hc⟩ := hpm
      have hc1 : c = 1 := by
        rcases c with _ | _ | c
        · simp at hc; omega
        · rfl
        · nlinarith
      subst hc1; rw [mul_one] at hc
      exact ⟨⟨by omega, by omega⟩, hpp⟩
    · rintro ⟨⟨h1, h2⟩, hpp⟩
      refine ⟨hpp, ?_, hC0⟩
      have hdvd_prod : p ∣ k ! * n.choose k := by
        rw [← hprod]
        exact Finset.dvd_prod_of_mem _ (mem_Ioc.mpr ⟨h1, h2⟩)
      have hnotk : ¬ p ∣ k ! := by
        intro h
        have := (Nat.Prime.dvd_factorial hpp).mp h
        omega
      exact (hpp.dvd_mul.mp hdvd_prod).resolve_left hnotk
  have hsqf : Squarefree (n.choose k) := by
    rw [Nat.squarefree_iff_factorization_le_one hC0]
    intro p
    by_cases hp : p.Prime
    · by_cases hpd : p ∣ n.choose k
      · apply Nat.factorization_choose_le_one
        have h1 := hcon p hp hpd
        have h2 := hp.two_le
        rw [sq]; nlinarith
      · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hC_eq : n.choose k = ∏ p ∈ (Ioc (n - k) n).filter Nat.Prime, p := by
    rw [← hpf_eq]
    exact (Nat.prod_primeFactors_of_squarefree hsqf).symm
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Ioc (n - k) n) Nat.Prime (fun m => m)
  rw [← hC_eq, hprod] at hsplit
  exact Nat.eq_of_mul_eq_mul_left (Nat.choose_pos hkn) (by linarith)

/-- Corollary: `(n - k) ^ (k - P) ≤ k !` where `P` is the number of primes in `(n - k, n]`. -/
lemma pow_sub_prime_count_le_factorial {n k : ℕ} (hk : 2 ≤ k) (h2k : 2 * k ≤ n)
    (hcon : ∀ p : ℕ, p.Prime → p ∣ n.choose k → n < 2 * p) :
    (n - k) ^ (k - ((Ioc (n - k) n).filter Nat.Prime).card) ≤ k ! := by
  have hprod := prod_nonprimes_eq_factorial hk h2k hcon
  have hcard : ((Ioc (n - k) n).filter (fun m => ¬ m.Prime)).card =
      k - ((Ioc (n - k) n).filter Nat.Prime).card := by
    have hsum := Finset.card_filter_add_card_filter_not (s := Ioc (n - k) n)
      (p := Nat.Prime)
    have htot : (Ioc (n - k) n).card = k := by
      rw [Nat.card_Ioc]; omega
    omega
  rw [← hprod, ← hcard]
  calc (n - k) ^ ((Ioc (n - k) n).filter (fun m => ¬ m.Prime)).card
      = ∏ _m ∈ (Ioc (n - k) n).filter (fun m => ¬ m.Prime), (n - k) := by rw [Finset.prod_const]
    _ ≤ ∏ m ∈ (Ioc (n - k) n).filter (fun m => ¬ m.Prime), m := by
        apply Finset.prod_le_prod'
        intro m hm
        simp only [mem_filter, mem_Ioc] at hm
        omega

/-! ## Section 2: Elementary Logarithm & Factorial Bounds -/

/-- For `t ≥ 0`, `t - t^2 / 2 ≤ Real.log (1 + t)`. -/
lemma log_one_add_ge {t : ℝ} (ht : 0 ≤ t) : t - t ^ 2 / 2 ≤ Real.log (1 + t) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - (x - x ^ 2 / 2)
  have hf0 : f 0 = 0 := by simp [f]
  suffices hmono : MonotoneOn f (Set.Ici 0) by
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only [f, hf0] at this
    linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro x hx
    have h1 : 0 < 1 + x := by linarith [Set.mem_Ici.mp hx]
    exact ((continuousAt_const.add continuousAt_id).log h1.ne').sub
      (continuousAt_id.sub ((continuousAt_id.pow 2).div_const 2)) |>.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by rwa [interior_Ici] at hx
    have h1 : 0 < 1 + x := by linarith
    have hd1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add 1).log h1.ne'
    have hd2 : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x := by
      have h2 := (hasDerivAt_pow 2 x).div_const (2 : ℝ)
      have hsub := (hasDerivAt_id x).sub h2
      have hval : (1 : ℝ) - (2 : ℕ) * x ^ (2 - 1) / 2 = 1 - x := by norm_num
      exact hval ▸ hsub
    have hfd : HasDerivAt f (1 / (1 + x) - (1 - x)) x := hd1.sub hd2
    exact hfd.differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : 0 < x := by rwa [interior_Ici] at hx
    have h1 : 0 < 1 + x := by linarith
    have hd1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add 1).log h1.ne'
    have hd2 : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x := by
      have h2 := (hasDerivAt_pow 2 x).div_const (2 : ℝ)
      have hsub := (hasDerivAt_id x).sub h2
      have hval : (1 : ℝ) - (2 : ℕ) * x ^ (2 - 1) / 2 = 1 - x := by norm_num
      exact hval ▸ hsub
    have hfd : HasDerivAt f (1 / (1 + x) - (1 - x)) x := hd1.sub hd2
    rw [hfd.deriv]
    have : 1 / (1 + x) - (1 - x) = x ^ 2 / (1 + x) := by field_simp; ring
    rw [this]
    positivity

/-- For `t ≥ 0`, `Real.log (1 + t) ≤ t - t^2 / 2 + t^3 / 3`. -/
lemma log_one_add_le {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 := by
  let f : ℝ → ℝ := fun x => (x - x ^ 2 / 2 + x ^ 3 / 3) - Real.log (1 + x)
  have hf0 : f 0 = 0 := by simp [f]
  suffices hmono : MonotoneOn f (Set.Ici 0) by
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only [f, hf0] at this
    linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro x hx
    have h1 : 0 < 1 + x := by linarith [Set.mem_Ici.mp hx]
    exact ((continuousAt_id.sub ((continuousAt_id.pow 2).div_const 2)).add
      ((continuousAt_id.pow 3).div_const 3)).sub
      ((continuousAt_const.add continuousAt_id).log h1.ne') |>.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by rwa [interior_Ici] at hx
    have h1 : 0 < 1 + x := by linarith
    have hd1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add 1).log h1.ne'
    have hd2 : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3) (1 - x + x ^ 2) x := by
      have h2 := (hasDerivAt_pow 2 x).div_const (2 : ℝ)
      have h3 := (hasDerivAt_pow 3 x).div_const (3 : ℝ)
      have hadd := ((hasDerivAt_id x).sub h2).add h3
      have hval : (1 : ℝ) - (2 : ℕ) * x ^ (2 - 1) / 2 + (3 : ℕ) * x ^ (3 - 1) / 3 =
          1 - x + x ^ 2 := by norm_num
      exact hval ▸ hadd
    have hfd : HasDerivAt f ((1 - x + x ^ 2) - 1 / (1 + x)) x := hd2.sub hd1
    exact hfd.differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : 0 < x := by rwa [interior_Ici] at hx
    have h1 : 0 < 1 + x := by linarith
    have hd1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      simpa using ((hasDerivAt_id x).const_add 1).log h1.ne'
    have hd2 : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2 + y ^ 3 / 3) (1 - x + x ^ 2) x := by
      have h2 := (hasDerivAt_pow 2 x).div_const (2 : ℝ)
      have h3 := (hasDerivAt_pow 3 x).div_const (3 : ℝ)
      have hadd := ((hasDerivAt_id x).sub h2).add h3
      have hval : (1 : ℝ) - (2 : ℕ) * x ^ (2 - 1) / 2 + (3 : ℕ) * x ^ (3 - 1) / 3 =
          1 - x + x ^ 2 := by norm_num
      exact hval ▸ hadd
    have hfd : HasDerivAt f ((1 - x + x ^ 2) - 1 / (1 + x)) x := hd2.sub hd1
    rw [hfd.deriv]
    have : (1 - x + x ^ 2) - 1 / (1 + x) = x ^ 3 / (1 + x) := by field_simp; ring
    rw [this]
    positivity

lemma log_two_bounds : (0.693147 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 0.693148 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

lemma log_twelve_bounds : (2.4846 : ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ 2.485 := by
  have h2 := log_two_bounds
  have h98 : Real.log 12 = (7 / 2 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log (1 + 1 / 8) := by
    have h1 : (12 : ℝ) ^ 2 = (2 : ℝ) ^ 7 * (1 + 1 / 8) := by norm_num
    have h2' := congrArg Real.log h1
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2'
    push_cast at h2'
    linarith
  have hlo := log_one_add_ge (t := (1 / 8 : ℝ)) (by norm_num)
  have hhi := log_one_add_le (t := (1 / 8 : ℝ)) (by norm_num)
  constructor <;> linarith

lemma log_thirteen_bounds : (2.564 : ℝ) ≤ Real.log 13 ∧ Real.log 13 ≤ 2.5651 := by
  have h12 := log_twelve_bounds
  have h13 : Real.log 13 = Real.log 12 + Real.log (1 + 1 / 12) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hlo := log_one_add_ge (t := (1 / 12 : ℝ)) (by norm_num)
  have hhi := log_one_add_le (t := (1 / 12 : ℝ)) (by norm_num)
  constructor <;> linarith

lemma log_nineteen_ge : (2.942 : ℝ) ≤ Real.log 19 := by
  have h2 := log_two_bounds
  have h19 : Real.log 19 = 4 * Real.log 2 + Real.log (1 + 3 / 16) := by
    have h1 : (19 : ℝ) = (2 : ℝ) ^ 4 * (1 + 3 / 16) := by norm_num
    rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hlo := log_one_add_ge (t := (3 / 16 : ℝ)) (by norm_num)
  linarith

lemma log_200000_bounds : (12.2 : ℝ) ≤ Real.log 200000 ∧ Real.log 200000 ≤ 12.23 := by
  have h2 := log_two_bounds
  constructor
  · have h1 : (2 : ℝ) ^ 35 * (1 + 10 / 61) ≤ (200000 : ℝ) ^ 2 := by norm_num
    have h2' := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h2'
    push_cast at h2'
    have hlo := log_one_add_ge (t := (10 / 61 : ℝ)) (by norm_num)
    linarith
  · have h1 : (200000 : ℝ) * (1 + 3 / 10) ≤ (2 : ℝ) ^ 18 := by norm_num
    have h2' := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h2'
    push_cast at h2'
    have hlo := log_one_add_ge (t := (3 / 10 : ℝ)) (by norm_num)
    linarith

lemma log_10000_le : Real.log 10000 ≤ 9.25 := by
  have h2 := log_two_bounds
  have h1 : (10000 : ℝ) ^ 2 * (1 + 1 / 3) ≤ (2 : ℝ) ^ 27 := by norm_num
  have h2' := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h2'
  push_cast at h2'
  have hlo := log_one_add_ge (t := (1 / 3 : ℝ)) (by norm_num)
  linarith

lemma log_upper_of_mul_pow_two {a t b : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (m : ℕ)
    (h : a * (1 + t) ≤ (2 : ℝ) ^ m) (hb : (m : ℝ) * 0.693148 - (t - t ^ 2 / 2) ≤ b) :
    Real.log a ≤ b := by
  have h2 := log_two_bounds.2
  have h1 := Real.log_le_log (by positivity) h
  rw [Real.log_mul ha.ne' (by positivity), Real.log_pow] at h1
  have hlo := log_one_add_ge ht
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

lemma log_250_le : Real.log 250 ≤ 5.55 := by
  exact log_upper_of_mul_pow_two (by norm_num) (t := 0) (by norm_num) 8 (by norm_num) (by norm_num)

/-- Elementary upper bound on `log(k!)`: `Real.log (k ! : ℝ) ≤ (k + 1) * Real.log (k + 1) - k`. -/
lemma log_factorial_le (k : ℕ) :
    Real.log (k ! : ℝ) ≤ ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) - (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h3 : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    have hlog_step : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≥
        1 / ((k : ℝ) + 2) := by
      have h1 : Real.log (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤
          ((k : ℝ) + 1) / ((k : ℝ) + 2) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h1
      have h2 : ((k : ℝ) + 1) / ((k : ℝ) + 2) - 1 = -1 / ((k : ℝ) + 2) := by field_simp; ring
      have hneg : -1 / ((k : ℝ) + 2) = -(1 / ((k : ℝ) + 2)) := by ring
      linarith
    have hmul : ((k : ℝ) + 2) * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) ≥ 1 := by
      calc ((k : ℝ) + 2) * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))
          ≥ ((k : ℝ) + 2) * (1 / ((k : ℝ) + 2)) := by
            gcongr
        _ = 1 := by field_simp
    rw [h3]
    nlinarith

/-- Harmonic number lower bound: for `z ≥ 6`, `Real.log (z + 1) + 1 / 2 ≤ ∑ m ∈ Icc 1 z, 1 / m`. -/
lemma harmonic_ge_log_add_half (z : ℕ) (hz : 6 ≤ z) :
    Real.log ((z : ℝ) + 1) + 1 / 2 ≤ ∑ m ∈ Icc 1 z, (1 : ℝ) / (m : ℝ) := by
  induction z, hz using Nat.le_induction with
  | base =>
    have hsum : ∑ m ∈ (Icc 1 6 : Finset ℕ), (1 : ℝ) / (m : ℝ) = 49 / 20 := by
      norm_num [Finset.sum_Icc_succ_top]
    rw [hsum]
    have h7 : Real.log 7 ≤ 1.95 := by
      have h2 := log_two_bounds
      have h1 : (7 : ℝ) * (1 + 1 / 7) = (2 : ℝ) ^ 3 := by norm_num
      have h2' := congrArg Real.log h1
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at h2'
      push_cast at h2'
      have hlo := log_one_add_ge (t := (1 / 7 : ℝ)) (by norm_num)
      linarith
    norm_num at h7 ⊢
    linarith
  | succ z hz ih =>
    have hsplit : ∑ m ∈ Icc 1 (z + 1), (1 : ℝ) / (m : ℝ) =
        (∑ m ∈ Icc 1 z, (1 : ℝ) / (m : ℝ)) + 1 / ((z : ℝ) + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast; rfl
    rw [hsplit]
    have hstep : Real.log (((z : ℝ) + 1) + 1) - Real.log ((z : ℝ) + 1) ≤ 1 / ((z : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have h1 := Real.log_le_sub_one_of_pos (x := ((z : ℝ) + 1 + 1) / ((z : ℝ) + 1)) (by positivity)
      have h2 : ((z : ℝ) + 1 + 1) / ((z : ℝ) + 1) - 1 = 1 / ((z : ℝ) + 1) := by field_simp; ring
      linarith
    push_cast
    linarith

/-! ## Section 3: Selberg Upper Bound Sieve -/

/-- The Selberg denominator `G z = ∑_{1 ≤ d ≤ z, Squarefree d} 1 / φ(d)`. -/
noncomputable def selbergG (z : ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 z).filter Squarefree, (1 : ℝ) / (Nat.totient d : ℝ)

lemma selbergG_pos {z : ℕ} (hz : 1 ≤ z) : 0 < selbergG z := by
  unfold selbergG
  apply Finset.sum_pos'
  · intro d hd
    have h1 : 1 ≤ d := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hphi : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
    positivity
  · refine ⟨1, mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hz⟩, squarefree_one⟩, ?_⟩
    simp

/-- Squarefree radical of `m`: product of distinct prime factors of `m`. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

lemma rad_squarefree (m : ℕ) : Squarefree (rad m) := by
  unfold rad
  have hne : (∏ p ∈ m.primeFactors, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [Nat.squarefree_iff_factorization_le_one hne]
  intro q
  rw [Nat.factorization_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  simp only [Finsupp.finsetSum_apply]
  by_cases hq : q ∈ m.primeFactors
  · rw [Finset.sum_eq_single q]
    · rw [(Nat.prime_of_mem_primeFactors hq).factorization_self]
    · intro p hp hpq
      rw [(Nat.prime_of_mem_primeFactors hp).factorization]
      simp [hpq]
    · intro h; exact absurd hq h
  · rw [Finset.sum_eq_zero]
    · exact Nat.zero_le 1
    · intro p hp
      rw [(Nat.prime_of_mem_primeFactors hp).factorization]
      have hpq : p ≠ q := fun h => hq (h ▸ hp)
      simp [hpq]

lemma rad_dvd (m : ℕ) : rad m ∣ m :=
  Nat.prod_primeFactors_dvd m

lemma rad_le (m : ℕ) (hm : 0 < m) : rad m ≤ m :=
  Nat.le_of_dvd hm (rad_dvd m)

lemma rad_pos (m : ℕ) : 0 < rad m :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma rad_primeFactors (m : ℕ) : (rad m).primeFactors = m.primeFactors := by
  unfold rad
  ext q
  rw [Nat.mem_primeFactors]
  have hne : (∏ p ∈ m.primeFactors, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  constructor
  · rintro ⟨hq, hqdvd, -⟩
    obtain ⟨p, hpm, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqdvd
    have hpp := Nat.prime_of_mem_primeFactors hpm
    rwa [(Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp]
  · intro hqm
    exact ⟨Nat.prime_of_mem_primeFactors hqm, Finset.dvd_prod_of_mem _ hqm, hne⟩

/-- Helper: bound a sum over `s` by a sum over `t` via an injective map `F : s → t`. -/
private lemma sum_le_sum_of_inj {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} {f : α → ℝ} {g : β → ℝ} (F : α → β)
    (hmaps : ∀ a ∈ s, F a ∈ t) (hinj : Set.InjOn F s)
    (hnonneg : ∀ b ∈ t, 0 ≤ g b) (hle : ∀ a ∈ s, f a ≤ g (F a)) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  calc ∑ a ∈ s, f a ≤ ∑ a ∈ s, g (F a) := Finset.sum_le_sum hle
    _ = ∑ b ∈ s.image F, g b := (Finset.sum_image (fun _ hx _ hy h => hinj hx hy h)).symm
    _ ≤ ∑ b ∈ t, g b := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hmaps) (fun b hb _ => hnonneg b hb)

/-- Every `m ∈ Icc 1 z` contributes `1/m` to `1 / φ(rad m)`, hence `∑_{m=1}^z 1/m ≤ G z`. -/
lemma harmonic_le_selbergG (z : ℕ) :
    ∑ m ∈ Icc 1 z, (1 : ℝ) / (m : ℝ) ≤ selbergG z := by
  unfold selbergG
  have hpart : ∑ m ∈ Icc 1 z, (1 : ℝ) / (m : ℝ) =
      ∑ d ∈ (Icc 1 z).filter Squarefree,
        ∑ m ∈ (Icc 1 z).filter (fun m => rad m = d), (1 : ℝ) / (m : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := rad)]
    intro m hm
    rw [mem_Icc] at hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨rad_pos m, (rad_le m (by omega)).trans hm.2⟩,
      rad_squarefree m⟩
  rw [hpart]
  apply Finset.sum_le_sum
  intro d hd
  rw [mem_filter, mem_Icc] at hd
  obtain ⟨⟨hd1, hdz⟩, hdsqf⟩ := hd
  have hd0 : d ≠ 0 := by omega
  -- For each squarefree d, ∑_{m ≤ z, rad m = d} 1/m ≤ (1/d) * ∏_{p ∈ d.primeFactors} (p / (p - 1)) = 1 / φ(d)
  have hphi_eq : (1 : ℝ) / (Nat.totient d : ℝ) =
      (1 / (d : ℝ)) * ∏ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    have htot := Nat.totient_eq_mul_prod_factors d
    have hcast : (Nat.totient d : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have h1 := congrArg (Rat.cast (K := ℝ)) htot
      simpa [Rat.cast_prod] using h1
    rw [hcast, one_div, mul_inv, ← Finset.prod_inv_distrib, ← one_div]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hphi_eq]
  -- Bound each factor p / (p - 1) from below by ∑_{e=0}^z (1/p)^e
  have hgeom : ∏ p ∈ d.primeFactors, (∑ e ∈ range (z + 1), ((1 : ℝ) / (p : ℝ)) ^ e) ≤
      ∏ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    apply Finset.prod_le_prod
    · intro p _; positivity
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hlt : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      rw [geom_sum_eq hlt.ne]
      have hden : (1 : ℝ) / (p : ℝ) - 1 = -(((p : ℝ) - 1) / (p : ℝ)) := by field_simp; ring
      have hpos : (0 : ℝ) < ((p : ℝ) - 1) / (p : ℝ) := div_pos (by linarith) (by linarith)
      have hnum_eq : ((1 : ℝ) / (p : ℝ)) ^ (z + 1) - 1 = -(1 - ((1 : ℝ) / (p : ℝ)) ^ (z + 1)) := by ring
      rw [hden, hnum_eq, neg_div_neg_eq]
      calc (1 - ((1 : ℝ) / (p : ℝ)) ^ (z + 1)) / (((p : ℝ) - 1) / (p : ℝ))
          ≤ 1 / (((p : ℝ) - 1) / (p : ℝ)) := by
            gcongr; linarith [show (0 : ℝ) ≤ ((1 : ℝ) / (p : ℝ)) ^ (z + 1) by positivity]
        _ = (p : ℝ) / ((p : ℝ) - 1) := by field_simp
  calc ∑ m ∈ (Icc 1 z).filter (fun m => rad m = d), (1 : ℝ) / (m : ℝ)
      ≤ (1 / (d : ℝ)) * ∏ p ∈ d.primeFactors, (∑ e ∈ range (z + 1), ((1 : ℝ) / (p : ℝ)) ^ e) := by
        rw [Finset.prod_sum, Finset.mul_sum]
        -- Map each m with rad m = d to its exponent vector F(p) = m.factorization p - 1
        let F : ℕ → ∀ p ∈ d.primeFactors, ℕ := fun m p _ => m.factorization p - 1
        refine sum_le_sum_of_inj F ?_ ?_ ?_ ?_
        · intro m hm
          rw [mem_filter, mem_Icc] at hm
          rw [Finset.mem_pi]
          intro p hp
          rw [mem_range]
          have hle : m.factorization p ≤ m := by
            by_cases h0 : m.factorization p = 0
            · omega
            · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
              have hpow : p ^ m.factorization p ≤ m :=
                Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)
              have hlt : m.factorization p < 2 ^ m.factorization p := Nat.lt_two_pow_self
              have hpow2 : 2 ^ m.factorization p ≤ p ^ m.factorization p :=
                Nat.pow_le_pow_left hp2 _
              omega
          simp only [F]; omega
        · intro m₁ hm₁ m₂ hm₂ hfeq
          rw [Finset.mem_coe, mem_filter, mem_Icc] at hm₁ hm₂
          have hpf1 : m₁.primeFactors = d.primeFactors := by rw [← rad_primeFactors m₁, hm₁.2]
          have hpf2 : m₂.primeFactors = d.primeFactors := by rw [← rad_primeFactors m₂, hm₂.2]
          apply Nat.eq_of_factorization_eq (by omega) (by omega)
          intro p
          by_cases hp : p ∈ d.primeFactors
          · have h1 : 1 ≤ m₁.factorization p := by
              have : p ∈ m₁.primeFactors := hpf1 ▸ hp
              exact (Nat.Prime.dvd_iff_one_le_factorization
                (Nat.prime_of_mem_primeFactors this) (by omega)).mp
                (Nat.dvd_of_mem_primeFactors this)
            have h2 : 1 ≤ m₂.factorization p := by
              have : p ∈ m₂.primeFactors := hpf2 ▸ hp
              exact (Nat.Prime.dvd_iff_one_le_factorization
                (Nat.prime_of_mem_primeFactors this) (by omega)).mp
                (Nat.dvd_of_mem_primeFactors this)
            have he := congrFun (congrFun hfeq p) hp
            simp only [F] at he
            omega
          · have h1 : m₁.factorization p = 0 := by
              rw [← Finsupp.notMem_support_iff, Nat.support_factorization, hpf1]; exact hp
            have h2 : m₂.factorization p = 0 := by
              rw [← Finsupp.notMem_support_iff, Nat.support_factorization, hpf2]; exact hp
            omega
        · intro f _; positivity
        · intro m hm
          rw [mem_filter, mem_Icc] at hm
          have hm0 : m ≠ 0 := by omega
          have hpf : m.primeFactors = d.primeFactors := by rw [← rad_primeFactors m, hm.2]
          have hm_prod : (m : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (p : ℝ) ^ (m.factorization p - 1) := by
            have h1 : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p :=
              (Nat.prod_factorization_pow_eq_self hm0).symm
            have hd_prod : d = ∏ p ∈ d.primeFactors, p :=
              (Nat.prod_primeFactors_of_squarefree hdsqf).symm
            have h2 : m = d * ∏ p ∈ d.primeFactors, p ^ (m.factorization p - 1) := by
              calc m = ∏ p ∈ m.primeFactors, p ^ m.factorization p := h1
                _ = ∏ p ∈ d.primeFactors, p ^ m.factorization p := by rw [hpf]
                _ = ∏ p ∈ d.primeFactors, (p * p ^ (m.factorization p - 1)) := by
                      apply Finset.prod_congr rfl
                      intro p hp
                      have h1p : 1 ≤ m.factorization p := by
                        have : p ∈ m.primeFactors := hpf ▸ hp
                        exact (Nat.Prime.dvd_iff_one_le_factorization
                          (Nat.prime_of_mem_primeFactors this) hm0).mp
                          (Nat.dvd_of_mem_primeFactors this)
                      rw [← pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel h1p]
                _ = (∏ p ∈ d.primeFactors, p) * ∏ p ∈ d.primeFactors, p ^ (m.factorization p - 1) :=
                      Finset.prod_mul_distrib
                _ = d * ∏ p ∈ d.primeFactors, p ^ (m.factorization p - 1) := by rw [← hd_prod]
            exact_mod_cast h2
          apply le_of_eq
          rw [hm_prod, one_div, mul_inv, ← one_div, ← Finset.prod_inv_distrib]
          congr 1
          rw [← Finset.prod_attach (s := d.primeFactors)]
          apply Finset.prod_congr rfl
          intro p _
          simp [F, one_div, inv_pow]
    _ ≤ (1 / (d : ℝ)) * ∏ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
        gcongr

/-- Key Selberg identity: for squarefree `d`, `∑_{t ∣ d} 1 / φ(t) = d / φ(d)`. -/
lemma sum_inv_totient_divisors {d : ℕ} (hd : Squarefree d) :
    ∑ t ∈ d.divisors, (1 : ℝ) / (Nat.totient t : ℝ) = (d : ℝ) / (Nat.totient d : ℝ) := by
  have hd0 : d ≠ 0 := hd.ne_zero
  -- Induction on number of prime factors via Finset.prod_one_add
  have h1 : (d : ℝ) / (Nat.totient d : ℝ) = ∏ p ∈ d.primeFactors, (1 + (1 : ℝ) / (Nat.totient p : ℝ)) := by
    have htot := Nat.totient_eq_mul_prod_factors d
    have hcast : (Nat.totient d : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have h1 := congrArg (Rat.cast (K := ℝ)) htot
      simpa [Rat.cast_prod] using h1
    rw [hcast]
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    rw [div_mul_eq_div_div, div_self hd_pos.ne', one_div, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.totient_prime hpp]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
    field_simp; ring
  rw [h1, Finset.prod_one_add]
  -- Bijection between subsets of d.primeFactors and d.divisors (since d is squarefree)
  apply Finset.sum_nbij' (fun t => t.primeFactors) (fun s => ∏ p ∈ s, p)
  · intro t ht
    rw [Finset.mem_powerset]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors ht) hd0
  · intro s hs
    rw [Finset.mem_powerset] at hs
    rw [Nat.mem_divisors]
    refine ⟨?_, hd0⟩
    calc ∏ p ∈ s, p ∣ ∏ p ∈ d.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hs
      _ = d := Nat.prod_primeFactors_of_squarefree hd
  · intro t ht
    have htsqf : Squarefree t := hd.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht)
    exact Nat.prod_primeFactors_of_squarefree htsqf
  · intro s hs
    rw [Finset.mem_powerset] at hs
    ext q
    rw [Nat.mem_primeFactors]
    have hprod_ne : (∏ p ∈ s, p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primeFactors (hs hp)).ne_zero
    constructor
    · rintro ⟨hq, hqdvd, -⟩
      obtain ⟨p, hps, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqdvd
      have hpp := Nat.prime_of_mem_primeFactors (hs hps)
      have heq := (Nat.prime_dvd_prime_iff_eq hq hpp).mp hqp
      rwa [heq]
    · intro hqs
      exact ⟨Nat.prime_of_mem_primeFactors (hs hqs), Finset.dvd_prod_of_mem _ hqs, hprod_ne⟩
  · intro t ht
    have htsqf : Squarefree t := hd.squarefree_of_dvd (Nat.dvd_of_mem_divisors ht)
    have hprod_tot : Nat.totient t = ∏ p ∈ t.primeFactors, Nat.totient p := by
      have htot := Nat.totient_eq_mul_prod_factors t
      have ht_prod : t = ∏ p ∈ t.primeFactors, p := (Nat.prod_primeFactors_of_squarefree htsqf).symm
      have hq : (Nat.totient t : ℚ) = ∏ p ∈ t.primeFactors, (Nat.totient p : ℚ) := by
        rw [htot]
        nth_rw 1 [ht_prod]
        rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        rw [Nat.totient_prime hpp, Nat.cast_sub hpp.one_le, Nat.cast_one]
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
        field_simp
      exact_mod_cast hq
    rw [hprod_tot, Nat.cast_prod, one_div, ← Finset.prod_inv_distrib]
    simp [one_div]

/-- Count of multiples of `D` in `(n - k, n]` is at most `k / D + 1`, and equals `k / D + err` with `|err| ≤ 1`. -/
lemma card_multiples_Ioc (n k D : ℕ) (hD : 0 < D) (hkn : k ≤ n) :
    |((((Ioc (n - k) n).filter (fun m => D ∣ m)).card : ℝ) - (k : ℝ) / (D : ℝ))| ≤ 1 := by
  have hcard : ((Ioc (n - k) n).filter (fun m => D ∣ m)).card = n / D - (n - k) / D := by
    have h1 : ∀ a : ℕ, ((Icc 1 a).filter (fun m => D ∣ m)).card = a / D := by
      intro a
      have hIcc : (Icc 1 (a / D)).card = a / D := by simp [Nat.card_Icc]
      rw [← hIcc]
      apply Finset.card_bij (fun m _ => m / D)
      · intro m hm
        simp only [mem_filter, mem_Icc] at hm ⊢
        exact ⟨(Nat.le_div_iff_mul_le hD).mpr (by
          obtain ⟨c, rfl⟩ := hm.2
          rcases c with _ | c
          · simp at hm
          · nlinarith), Nat.div_le_div_right hm.1.2⟩
      · intro m₁ hm₁ m₂ hm₂ h
        simp only [mem_filter] at hm₁ hm₂
        obtain ⟨c₁, rfl⟩ := hm₁.2
        obtain ⟨c₂, rfl⟩ := hm₂.2
        rw [Nat.mul_div_cancel_left _ hD, Nat.mul_div_cancel_left _ hD] at h
        rw [h]
      · intro c hc
        simp only [mem_Icc] at hc
        refine ⟨D * c, mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,
          (Nat.le_div_iff_mul_le hD).mp hc.2 |> fun h => by linarith⟩, dvd_mul_right D c⟩,
          Nat.mul_div_cancel_left c hD⟩
    have hsdiff : (Ioc (n - k) n).filter (fun m => D ∣ m) =
        (Icc 1 n).filter (fun m => D ∣ m) \ (Icc 1 (n - k)).filter (fun m => D ∣ m) := by
      ext x; simp only [mem_filter, mem_Ioc, mem_sdiff, mem_Icc]; omega
    rw [hsdiff, Finset.card_sdiff_of_subset
      (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right (Nat.sub_le n k))), h1 n, h1 (n - k)]
  rw [hcard]
  have hsub : (n - k) / D ≤ n / D := Nat.div_le_div_right (Nat.sub_le n k)
  rw [Nat.cast_sub hsub]
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hdiv : ∀ a : ℕ, (a : ℝ) / (D : ℝ) - 1 < (a / D : ℕ) ∧ ((a / D : ℕ) : ℝ) ≤ (a : ℝ) / (D : ℝ) := by
    intro a
    have hq := Nat.div_add_mod a D
    have hmod : a % D < D := Nat.mod_lt a hD
    have hqR : (D : ℝ) * (a / D : ℕ) + (a % D : ℕ) = (a : ℝ) := by exact_mod_cast hq
    have hmodR : ((a % D : ℕ) : ℝ) < (D : ℝ) := by exact_mod_cast hmod
    have hmod0 : (0 : ℝ) ≤ (a % D : ℕ) := by positivity
    constructor
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hDpos]; nlinarith
    · rw [le_div_iff₀ hDpos]; nlinarith
  have hn := hdiv n
  have hnk := hdiv (n - k)
  have hknR : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hkn
  rw [hknR] at hnk
  rw [abs_le]
  constructor <;> linarith [show (n : ℝ) / D - ((n : ℝ) - k) / D = (k : ℝ) / D by ring]

/-- Selberg upper bound sieve on `(n - k, n]`:
for `1 ≤ z ≤ n - k`, `π(n) - π(n - k) ≤ k / G(z) + z^2`. -/
theorem selberg_upper_bound {n k z : ℕ} (hkn : k ≤ n) (hz1 : 1 ≤ z) (hznk : z ≤ n - k) :
    (((Ioc (n - k) n).filter Nat.Prime).card : ℝ) ≤ (k : ℝ) / selbergG z + (z : ℝ) ^ 2 := by
  set S := (Icc 1 z).filter Squarefree
  have hGpos : 0 < selbergG z := selbergG_pos hz1
  -- Define Selberg weights λ_d for d ∈ S
  let lam : ℕ → ℝ := fun d =>
    if d ∈ S then
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) / selbergG z *
        ∑ r ∈ S.filter (fun r => d * r ≤ z ∧ d.Coprime r),
          (1 : ℝ) / (Nat.totient (d * r) : ℝ)
    else 0
  have hlam1 : lam 1 = 1 := by
    have h1S : 1 ∈ S := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hz1⟩, squarefree_one⟩
    simp only [lam, h1S, ↓reduceIte, ArithmeticFunction.moebius_apply_one, Int.cast_one,
      Nat.cast_one, one_mul, one_div]
    have hfilt : S.filter (fun r => r ≤ z ∧ Nat.Coprime 1 r) = S := by
      ext r; simp only [mem_filter, S, mem_Icc, Nat.coprime_one_left_eq_true, and_true]
      tauto
    rw [hfilt]
    have hGeq : ∑ x ∈ S, (Nat.totient x : ℝ)⁻¹ = selbergG z := by
      unfold selbergG; simp only [one_div]; rfl
    rw [hGeq]
    exact inv_mul_cancel₀ hGpos.ne'
  -- Bound |lam d| ≤ 1 for all d ∈ S
  have hlam_abs : ∀ d ∈ S, |lam d| ≤ 1 := by
    intro d hd
    have hdsqf : Squarefree d := (mem_filter.mp hd).2
    have hd1 : 1 ≤ d := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hdphi_pos : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
    simp only [lam, hd, ↓reduceIte]
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [ArithmeticFunction.moebius_apply_of_squarefree hdsqf]
      simp [abs_pow]
    have hsum_nonneg : 0 ≤ ∑ r ∈ S.filter (fun r => d * r ≤ z ∧ d.Coprime r),
        (1 : ℝ) / (Nat.totient (d * r) : ℝ) := by
      apply Finset.sum_nonneg; intro r _; positivity
    rw [abs_mul, abs_div, abs_mul, hmu, one_mul, abs_of_nonneg (Nat.cast_nonneg d),
      abs_of_pos hGpos, abs_of_nonneg hsum_nonneg]
    rw [div_mul_eq_mul_div, div_le_one hGpos]
    -- Rewrite d * ∑_{r} 1/φ(d*r) = (d / φ(d)) * ∑_{r} 1/φ(r) = (∑_{t∣d} 1/φ(t)) * (∑_{r} 1/φ(r))
    have hmul_tot : ∀ r ∈ S.filter (fun r => d * r ≤ z ∧ d.Coprime r),
        (1 : ℝ) / (Nat.totient (d * r) : ℝ) =
        (1 / (Nat.totient d : ℝ)) * (1 / (Nat.totient r : ℝ)) := by
      intro r hr
      rw [Nat.totient_mul (mem_filter.mp hr).2.2, Nat.cast_mul]
      ring
    rw [Finset.sum_congr rfl hmul_tot, ← Finset.mul_sum, ← mul_assoc,
      mul_one_div, ← sum_inv_totient_divisors hdsqf, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    -- Every pair (t, r) with t ∣ d, r ∈ S, d*r ≤ z, coprime(d, r) maps injectively to t*r ∈ S
    rw [Finset.sum_comm]
    have hpair : ∑ r ∈ S.filter (fun r => d * r ≤ z ∧ d.Coprime r),
        ∑ t ∈ d.divisors, (1 : ℝ) / (Nat.totient t : ℝ) * ((1 : ℝ) / (Nat.totient r : ℝ)) =
        ∑ p ∈ (S.filter (fun r => d * r ≤ z ∧ d.Coprime r)) ×ˢ d.divisors,
          (1 : ℝ) / (Nat.totient (p.2 * p.1) : ℝ) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl; intro r hr
      apply Finset.sum_congr rfl; intro t ht
      have hcop : t.Coprime r := (mem_filter.mp hr).2.2.coprime_dvd_left (Nat.dvd_of_mem_divisors ht)
      rw [Nat.totient_mul hcop, Nat.cast_mul]; ring
    rw [hpair]
    unfold selbergG
    refine sum_le_sum_of_inj (fun p => p.2 * p.1) ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_product, mem_filter] at hp
      obtain ⟨⟨hrS, hdrz, hcop⟩, htdiv⟩ := hp
      have htd : p.2 ∣ d := Nat.dvd_of_mem_divisors htdiv
      have hr1 : 1 ≤ p.1 := (mem_Icc.mp (mem_filter.mp hrS).1).1
      have ht1 : 1 ≤ p.2 := Nat.pos_of_dvd_of_pos htd (by omega)
      have htd_le : p.2 ≤ d := Nat.le_of_dvd (by omega) htd
      have hcop_tr : p.2.Coprime p.1 := hcop.coprime_dvd_left htd
      have htsqf : Squarefree p.2 := hdsqf.squarefree_of_dvd htd
      have hrsqf : Squarefree p.1 := (mem_filter.mp hrS).2
      have hsqf : Squarefree (p.2 * p.1) := (Nat.squarefree_mul hcop_tr).mpr ⟨htsqf, hrsqf⟩
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩, hsqf⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      dsimp only at heq
      rw [Finset.mem_coe, mem_product, mem_filter] at hp₁ hp₂
      have ht1d : p₁.2 ∣ d := Nat.dvd_of_mem_divisors hp₁.2
      have ht2d : p₂.2 ∣ d := Nat.dvd_of_mem_divisors hp₂.2
      have hcop1 : d.Coprime p₁.1 := hp₁.1.2.2
      have hcop2 : d.Coprime p₂.1 := hp₂.1.2.2
      have h12 : p₁.2 ∣ p₂.2 := by
        have h : p₁.2 ∣ p₂.2 * p₂.1 := heq ▸ dvd_mul_right p₁.2 p₁.1
        exact (hcop2.coprime_dvd_left ht1d).dvd_of_dvd_mul_right h
      have h21 : p₂.2 ∣ p₁.2 := by
        have h : p₂.2 ∣ p₁.2 * p₁.1 := heq.symm ▸ dvd_mul_right p₂.2 p₂.1
        exact (hcop1.coprime_dvd_left ht2d).dvd_of_dvd_mul_right h
      have ht_eq : p₁.2 = p₂.2 := Nat.dvd_antisymm h12 h21
      have ht_pos : 0 < p₁.2 := Nat.pos_of_dvd_of_pos ht1d (by omega)
      have hr_eq : p₁.1 = p₂.1 := Nat.eq_of_mul_eq_mul_left ht_pos (by rw [← ht_eq] at heq; exact heq)
      exact Prod.ext hr_eq ht_eq
    · intro x _; positivity
    · intro _ _; exact le_rfl
  -- Step 1: Every prime p ∈ (n - k, n] has p > z, so its only divisor in S is 1, hence (∑_{d∣p, d∈S} λ_d)^2 = 1
  have hstep1 : (((Ioc (n - k) n).filter Nat.Prime).card : ℝ) ≤
      ∑ m ∈ Ioc (n - k) n, (∑ d ∈ S.filter (fun d => d ∣ m), lam d) ^ 2 := by
    calc (((Ioc (n - k) n).filter Nat.Prime).card : ℝ)
        = ∑ p ∈ (Ioc (n - k) n).filter Nat.Prime, (1 : ℝ) := by simp
      _ = ∑ p ∈ (Ioc (n - k) n).filter Nat.Prime,
            (∑ d ∈ S.filter (fun d => d ∣ p), lam d) ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [mem_filter, mem_Ioc] at hp
          have hfilt : S.filter (fun d => d ∣ p) = {1} := by
            ext d
            simp only [mem_filter, mem_singleton, S, mem_Icc]
            constructor
            · rintro ⟨⟨⟨hd1, hdz⟩, -⟩, hdp⟩
              rcases hp.2.eq_one_or_self_of_dvd d hdp with rfl | rfl
              · rfl
              · omega
            · rintro rfl
              exact ⟨⟨⟨le_rfl, hz1⟩, squarefree_one⟩, one_dvd p⟩
          rw [hfilt, Finset.sum_singleton, hlam1, one_pow]
      _ ≤ ∑ m ∈ Ioc (n - k) n, (∑ d ∈ S.filter (fun d => d ∣ m), lam d) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro _ _ _; positivity
  -- Step 2: Expand the square and swap sums
  have hexpand : ∑ m ∈ Ioc (n - k) n, (∑ d ∈ S.filter (fun d => d ∣ m), lam d) ^ 2 =
      ∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ *
        (((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) := by
    have hsq : ∀ m ∈ Ioc (n - k) n,
        (∑ d ∈ S.filter (fun d => d ∣ m), lam d) ^ 2 =
        ∑ d₁ ∈ S, ∑ d₂ ∈ S, if Nat.lcm d₁ d₂ ∣ m then lam d₁ * lam d₂ else 0 := by
      intro m _
      rw [sq, Finset.sum_mul_sum, Finset.sum_filter (s := S)]
      apply Finset.sum_congr rfl; intro d₁ _
      by_cases h1 : d₁ ∣ m
      · simp only [h1, ↓reduceIte, Finset.sum_filter (s := S)]
        apply Finset.sum_congr rfl; intro d₂ _
        by_cases h2 : d₂ ∣ m
        · have hlcm : Nat.lcm d₁ d₂ ∣ m := Nat.lcm_dvd h1 h2
          simp [h2, hlcm]
        · have hlcm : ¬ Nat.lcm d₁ d₂ ∣ m := fun h => h2 ((Nat.dvd_lcm_right d₁ d₂).trans h)
          simp [h2, hlcm]
      · simp only [h1, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero; intro d₂ _
        have hlcm : ¬ Nat.lcm d₁ d₂ ∣ m := fun h => h1 ((Nat.dvd_lcm_left d₁ d₂).trans h)
        simp [hlcm]
    rw [Finset.sum_congr rfl hsq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d₂ _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 3: Split card into k / lcm(d₁, d₂) + error
  have hmain_quad : ∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ / (Nat.lcm d₁ d₂ : ℝ) = 1 / selbergG z := by
    -- Use 1 / lcm(d₁, d₂) = gcd(d₁, d₂) / (d₁ * d₂) = (1 / (d₁ * d₂)) * ∑_{h ∣ d₁, h ∣ d₂} φ(h)
    have hlcm : ∀ d₁ ∈ S, ∀ d₂ ∈ S,
        (1 : ℝ) / (Nat.lcm d₁ d₂ : ℝ) =
        ∑ h ∈ S.filter (fun h => h ∣ d₁ ∧ h ∣ d₂),
          (Nat.totient h : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
      intro d₁ hd₁ d₂ hd₂
      have h1pos : 0 < d₁ := (mem_Icc.mp (mem_filter.mp hd₁).1).1
      have h2pos : 0 < d₂ := (mem_Icc.mp (mem_filter.mp hd₂).1).1
      have hg_pos : 0 < Nat.gcd d₁ d₂ := Nat.gcd_pos_of_pos_left d₂ h1pos
      have hlcm_eq : (Nat.gcd d₁ d₂ : ℝ) * (Nat.lcm d₁ d₂ : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
      have hsum_tot : ∑ h ∈ (Nat.gcd d₁ d₂).divisors, (Nat.totient h : ℝ) = (Nat.gcd d₁ d₂ : ℝ) := by
        exact_mod_cast Nat.sum_totient (Nat.gcd d₁ d₂)
      have hfilt_eq : S.filter (fun h => h ∣ d₁ ∧ h ∣ d₂) = (Nat.gcd d₁ d₂).divisors := by
        ext h
        simp only [mem_filter, S, mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨⟨h1, h2⟩, hg_pos.ne'⟩
        · rintro ⟨⟨h1, h2⟩, _⟩
          have h1le : h ≤ d₁ := Nat.le_of_dvd h1pos h1
          have h1z : d₁ ≤ z := (mem_Icc.mp (mem_filter.mp hd₁).1).2
          have hsqf : Squarefree h := (mem_filter.mp hd₁).2.squarefree_of_dvd h1
          exact ⟨⟨⟨Nat.pos_of_dvd_of_pos h1 h1pos, h1le.trans h1z⟩, hsqf⟩, h1, h2⟩
      rw [hfilt_eq]
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, hsum_tot, ← div_eq_mul_inv]
      have hlcm_pos : (0 : ℝ) < Nat.lcm d₁ d₂ := by
        exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero h1pos.ne' h2pos.ne')
      have hd12_pos : (0 : ℝ) < (d₁ : ℝ) * (d₂ : ℝ) := by positivity
      rw [← div_eq_mul_inv, div_eq_div_iff hlcm_pos.ne' hd12_pos.ne']
      linarith
    -- Substitute hlcm and swap the h-sum to the outside
    have hswap : ∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ / (Nat.lcm d₁ d₂ : ℝ) =
        ∑ h ∈ S, (Nat.totient h : ℝ) * (∑ d ∈ S.filter (fun d => h ∣ d), lam d / (d : ℝ)) ^ 2 := by
      have hstep : ∀ d₁ ∈ S, ∀ d₂ ∈ S,
          lam d₁ * lam d₂ / (Nat.lcm d₁ d₂ : ℝ) =
          ∑ h ∈ S, if h ∣ d₁ ∧ h ∣ d₂ then
            (Nat.totient h : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) else 0 := by
        intro d₁ hd₁ d₂ hd₂
        rw [div_eq_mul_one_div, hlcm d₁ hd₁ d₂ hd₂, Finset.mul_sum, ← Finset.sum_filter]
        apply Finset.sum_congr rfl; intro h _
        ring
      calc ∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ / (Nat.lcm d₁ d₂ : ℝ)
          = ∑ d₁ ∈ S, ∑ d₂ ∈ S, ∑ h ∈ S, if h ∣ d₁ ∧ h ∣ d₂ then
              (Nat.totient h : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) else 0 := by
            apply Finset.sum_congr rfl; intro d₁ hd₁
            apply Finset.sum_congr rfl; intro d₂ hd₂
            exact hstep d₁ hd₁ d₂ hd₂
        _ = ∑ d₁ ∈ S, ∑ h ∈ S, ∑ d₂ ∈ S, if h ∣ d₁ ∧ h ∣ d₂ then
              (Nat.totient h : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) else 0 := by
            apply Finset.sum_congr rfl; intro d₁ _
            exact Finset.sum_comm
        _ = ∑ h ∈ S, ∑ d₁ ∈ S, ∑ d₂ ∈ S, if h ∣ d₁ ∧ h ∣ d₂ then
              (Nat.totient h : ℝ) * (lam d₁ / (d₁ : ℝ)) * (lam d₂ / (d₂ : ℝ)) else 0 :=
            Finset.sum_comm
        _ = ∑ h ∈ S, (Nat.totient h : ℝ) * (∑ d ∈ S.filter (fun d => h ∣ d), lam d / (d : ℝ)) ^ 2 := by
            apply Finset.sum_congr rfl; intro h _
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_filter (s := S)]
            apply Finset.sum_congr rfl; intro d₁ _
            by_cases h1 : h ∣ d₁
            · simp only [h1, true_and, ↓reduceIte, Finset.mul_sum, Finset.sum_filter (s := S)]
              apply Finset.sum_congr rfl; intro d₂ _
              split_ifs <;> ring
            · simp [h1]
    -- Compute y(h) = ∑_{d ∈ S, h ∣ d} lam d / d = μ(h) / (φ(h) * G(z))
    have hy : ∀ h ∈ S,
        ∑ d ∈ S.filter (fun d => h ∣ d), lam d / (d : ℝ) =
        ((ArithmeticFunction.moebius h : ℤ) : ℝ) / ((Nat.totient h : ℝ) * selbergG z) := by
      intro h hh
      have hhsqf : Squarefree h := (mem_filter.mp hh).2
      have hh1 : 1 ≤ h := (mem_Icc.mp (mem_filter.mp hh).1).1
      have hhz : h ≤ z := (mem_Icc.mp (mem_filter.mp hh).1).2
      -- Substitute d = h * m with m ∈ S, h * m ≤ z, h.Coprime m
      have hreidx : ∑ d ∈ S.filter (fun d => h ∣ d), lam d / (d : ℝ) =
          ∑ m ∈ S.filter (fun m => h * m ≤ z ∧ h.Coprime m),
            ((ArithmeticFunction.moebius (h * m) : ℤ) : ℝ) / selbergG z *
              ∑ r ∈ S.filter (fun r => h * m * r ≤ z ∧ (h * m).Coprime r),
                (1 : ℝ) / (Nat.totient (h * m * r) : ℝ) := by
        apply Finset.sum_nbij' (fun d => d / h) (fun m => h * m)
        · intro d hd
          rw [mem_filter] at hd
          obtain ⟨hdS, ⟨m, rfl⟩⟩ := hd
          have hdsqf : Squarefree (h * m) := (mem_filter.mp hdS).2
          have hdz : h * m ≤ z := (mem_Icc.mp (mem_filter.mp hdS).1).2
          have hd1 : 1 ≤ h * m := (mem_Icc.mp (mem_filter.mp hdS).1).1
          have hm1 : 1 ≤ m := by rcases m with _ | m; simp at hd1; omega
          have hcop : h.Coprime m := Nat.coprime_of_squarefree_mul hdsqf
          have hmsqf : Squarefree m := hdsqf.squarefree_of_dvd (dvd_mul_left m h)
          rw [Nat.mul_div_cancel_left m (by omega)]
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1, by nlinarith⟩, hmsqf⟩, hdz, hcop⟩
        · intro m hm
          rw [mem_filter] at hm
          obtain ⟨hmS, hmz, hcop⟩ := hm
          have hm1 : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hmS).1).1
          have hmsqf : Squarefree m := (mem_filter.mp hmS).2
          have hsqf : Squarefree (h * m) := (Nat.squarefree_mul hcop).mpr ⟨hhsqf, hmsqf⟩
          exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, hmz⟩, hsqf⟩, dvd_mul_right h m⟩
        · intro d hd
          exact Nat.mul_div_cancel' (mem_filter.mp hd).2
        · intro m _
          exact Nat.mul_div_cancel_left m (by omega)
        · intro d hd
          rw [mem_filter] at hd
          obtain ⟨hdS, ⟨m, rfl⟩⟩ := hd
          have hd0 : ((h * m : ℕ) : ℝ) ≠ 0 := by
            have : 1 ≤ h * m := (mem_Icc.mp (mem_filter.mp hdS).1).1
            exact_mod_cast (by omega : h * m ≠ 0)
          rw [Nat.mul_div_cancel_left m (by omega)]
          simp only [lam, hdS, ↓reduceIte]
          field_simp
      rw [hreidx]
      -- Group by u = m * r ∈ S.filter (fun u => h * u ≤ z ∧ h.Coprime u)
      set U := S.filter (fun u => h * u ≤ z ∧ h.Coprime u)
      have hgroup : ∑ m ∈ U,
            ((ArithmeticFunction.moebius (h * m) : ℤ) : ℝ) / selbergG z *
              ∑ r ∈ S.filter (fun r => h * m * r ≤ z ∧ (h * m).Coprime r),
                (1 : ℝ) / (Nat.totient (h * m * r) : ℝ) =
          ((ArithmeticFunction.moebius h : ℤ) : ℝ) / selbergG z *
            ∑ u ∈ U, (1 : ℝ) / (Nat.totient (h * u) : ℝ) *
              ∑ m ∈ u.divisors, ((ArithmeticFunction.moebius m : ℤ) : ℝ) := by
        -- Expand both sides as sums over pairs (m, r) and (u, m) with u = m * r
        have hL : ∑ m ∈ U,
              ((ArithmeticFunction.moebius (h * m) : ℤ) : ℝ) / selbergG z *
                ∑ r ∈ S.filter (fun r => h * m * r ≤ z ∧ (h * m).Coprime r),
                  (1 : ℝ) / (Nat.totient (h * m * r) : ℝ) =
            ((ArithmeticFunction.moebius h : ℤ) : ℝ) / selbergG z *
              ∑ p ∈ U.sigma (fun m => S.filter (fun r => h * m * r ≤ z ∧ (h * m).Coprime r)),
                ((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) *
                  ((1 : ℝ) / (Nat.totient (h * (p.1 * p.2)) : ℝ)) := by
          rw [Finset.sum_sigma, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro m hm
          have hcop : h.Coprime m := (mem_filter.mp hm).2.2
          have hmu_mul : ArithmeticFunction.moebius (h * m) =
              ArithmeticFunction.moebius h * ArithmeticFunction.moebius m :=
            ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
          rw [hmu_mul, Int.cast_mul, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _
          rw [mul_assoc]; ring
        have hR : ∑ u ∈ U, (1 : ℝ) / (Nat.totient (h * u) : ℝ) *
              ∑ m ∈ u.divisors, ((ArithmeticFunction.moebius m : ℤ) : ℝ) =
            ∑ q ∈ U.sigma (fun u => u.divisors),
              ((ArithmeticFunction.moebius q.2 : ℤ) : ℝ) *
                ((1 : ℝ) / (Nat.totient (h * q.1) : ℝ)) := by
          rw [Finset.sum_sigma]
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro m _
          ring
        rw [hL, hR]
        congr 1
        apply Finset.sum_nbij' (fun p => ⟨p.1 * p.2, p.1⟩) (fun q => ⟨q.2, q.1 / q.2⟩)
        · intro p hp
          rw [mem_sigma] at hp
          obtain ⟨hmU, hrF⟩ := hp
          rw [mem_filter] at hmU hrF
          obtain ⟨hmS, hmz, hcop_hm⟩ := hmU
          obtain ⟨hrS, hhmrz, hcop_hmr⟩ := hrF
          have hm1 : 1 ≤ p.1 := (mem_Icc.mp (mem_filter.mp hmS).1).1
          have hr1 : 1 ≤ p.2 := (mem_Icc.mp (mem_filter.mp hrS).1).1
          have hmsqf : Squarefree p.1 := (mem_filter.mp hmS).2
          have hrsqf : Squarefree p.2 := (mem_filter.mp hrS).2
          have hcop_mr : p.1.Coprime p.2 := hcop_hmr.coprime_dvd_left (dvd_mul_left p.1 h)
          have hcop_hr : h.Coprime p.2 := hcop_hmr.coprime_dvd_left (dvd_mul_right h p.1)
          have hsqf_mr : Squarefree (p.1 * p.2) := (Nat.squarefree_mul hcop_mr).mpr ⟨hmsqf, hrsqf⟩
          have hmr_z : p.1 * p.2 ≤ z := by nlinarith
          have huU : p.1 * p.2 ∈ U :=
            mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith, hmr_z⟩, hsqf_mr⟩,
              by linarith [mul_assoc h p.1 p.2], hcop_hm.mul_right hcop_hr⟩
          exact mem_sigma.mpr ⟨huU, Nat.mem_divisors.mpr ⟨dvd_mul_right p.1 p.2, by positivity⟩⟩
        · intro q hq
          rw [mem_sigma] at hq
          obtain ⟨huU, hmdiv⟩ := hq
          rw [mem_filter] at huU
          obtain ⟨huS, huz, hcop_hu⟩ := huU
          have hu1 : 1 ≤ q.1 := (mem_Icc.mp (mem_filter.mp huS).1).1
          have husqf : Squarefree q.1 := (mem_filter.mp huS).2
          have hmu : q.2 ∣ q.1 := Nat.dvd_of_mem_divisors hmdiv
          have hm1 : 1 ≤ q.2 := Nat.pos_of_dvd_of_pos hmu (by omega)
          have hmq_eq : q.2 * (q.1 / q.2) = q.1 := Nat.mul_div_cancel' hmu
          have hmsqf : Squarefree q.2 := husqf.squarefree_of_dvd hmu
          have hrsqf : Squarefree (q.1 / q.2) := husqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hmu)
          have hcop_mr : q.2.Coprime (q.1 / q.2) :=
            Nat.coprime_of_squarefree_mul (hmq_eq.symm ▸ husqf)
          have hcop_hm : h.Coprime q.2 := hcop_hu.coprime_dvd_right hmu
          have hcop_hr : h.Coprime (q.1 / q.2) := hcop_hu.coprime_dvd_right (Nat.div_dvd_of_dvd hmu)
          have hr1 : 1 ≤ q.1 / q.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hmu) (by omega)
          have hmU : q.2 ∈ U :=
            mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1, (Nat.le_of_dvd (by omega) hmu).trans
              (mem_Icc.mp (mem_filter.mp huS).1).2⟩, hmsqf⟩,
              by nlinarith [Nat.le_of_dvd (by omega) hmu], hcop_hm⟩
          have hrS : q.1 / q.2 ∈ S :=
            mem_filter.mpr ⟨mem_Icc.mpr ⟨hr1, (Nat.div_le_self q.1 q.2).trans
              (mem_Icc.mp (mem_filter.mp huS).1).2⟩, hrsqf⟩
          have hrF : q.1 / q.2 ∈ S.filter (fun r => h * q.2 * r ≤ z ∧ (h * q.2).Coprime r) :=
            mem_filter.mpr ⟨hrS, by rw [mul_assoc, hmq_eq]; exact huz, hcop_hr.mul_left hcop_mr⟩
          exact mem_sigma.mpr ⟨hmU, hrF⟩
        · intro p hp
          rw [mem_sigma] at hp
          have hm1 : 1 ≤ p.1 := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp.1).1).1).1
          exact Sigma.ext rfl (heq_of_eq (Nat.mul_div_cancel_left p.2 (by omega)))
        · intro q hq
          rw [mem_sigma] at hq
          have hmu : q.2 ∣ q.1 := Nat.dvd_of_mem_divisors hq.2
          exact Sigma.ext (Nat.mul_div_cancel' hmu) (heq_of_eq rfl)
        · intro p _; rfl
      rw [hgroup]
      -- In ∑_{u ∈ U} (1/φ(h*u)) * ∑_{m ∣ u} μ(m), only u = 1 survives!
      have h1U : 1 ∈ U :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hz1⟩, squarefree_one⟩,
          by omega, Nat.coprime_one_right h⟩
      have hsum_u : ∑ u ∈ U, (1 : ℝ) / (Nat.totient (h * u) : ℝ) *
            ∑ m ∈ u.divisors, ((ArithmeticFunction.moebius m : ℤ) : ℝ) =
          (1 : ℝ) / (Nat.totient h : ℝ) := by
        rw [Finset.sum_eq_single 1]
        · simp
        · intro u _ hu1
          have hmu0 : ∑ m ∈ u.divisors, (ArithmeticFunction.moebius m : ℤ) = 0 := by
            have h1 := congrFun (congrArg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) u
            rw [ArithmeticFunction.coe_mul_zeta_apply] at h1
            simp [hu1] at h1
            exact h1
          have hmu0R : ∑ m ∈ u.divisors, ((ArithmeticFunction.moebius m : ℤ) : ℝ) = 0 := by
            exact_mod_cast hmu0
          rw [hmu0R, mul_zero]
        · intro hnot; exact absurd h1U hnot
      rw [hsum_u]
      ring
    rw [hswap]
    have hsum_h : ∑ h ∈ S, (Nat.totient h : ℝ) * (∑ d ∈ S.filter (fun d => h ∣ d), lam d / (d : ℝ)) ^ 2 =
        ∑ h ∈ S, (1 : ℝ) / (Nat.totient h : ℝ) / (selbergG z) ^ 2 := by
      apply Finset.sum_congr rfl; intro h hh
      rw [hy h hh]
      have hhsqf : Squarefree h := (mem_filter.mp hh).2
      have hmu_sq : (((ArithmeticFunction.moebius h : ℤ) : ℝ)) ^ 2 = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hhsqf]
        push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
      have hh1 : 1 ≤ h := (mem_Icc.mp (mem_filter.mp hh).1).1
      have hphi_pos : (0 : ℝ) < Nat.totient h := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      rw [div_pow, hmu_sq, mul_pow]
      field_simp
    rw [hsum_h]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have hGeq : ∑ x ∈ S, (Nat.totient x : ℝ)⁻¹ = selbergG z := by
      unfold selbergG; simp only [one_div]; rfl
    simp only [one_mul, hGeq]
    field_simp
  -- Step 4: Error term bounded by (∑_{d∈S} |lam d|)^2 ≤ z^2
  have herr : |∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ *
      ((((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) -
        (k : ℝ) / (Nat.lcm d₁ d₂ : ℝ))| ≤ (z : ℝ) ^ 2 := by
    calc |∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ *
            ((((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) -
              (k : ℝ) / (Nat.lcm d₁ d₂ : ℝ))|
        ≤ ∑ d₁ ∈ S, |∑ d₂ ∈ S, lam d₁ * lam d₂ *
            ((((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) -
              (k : ℝ) / (Nat.lcm d₁ d₂ : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d₁ ∈ S, ∑ d₂ ∈ S, |lam d₁ * lam d₂ *
            ((((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) -
              (k : ℝ) / (Nat.lcm d₁ d₂ : ℝ))| := by
            apply Finset.sum_le_sum; intro d₁ _; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d₁ ∈ S, ∑ d₂ ∈ S, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro d₁ hd₁
            apply Finset.sum_le_sum; intro d₂ hd₂
            rw [abs_mul, abs_mul]
            have h1 := hlam_abs d₁ hd₁
            have h2 := hlam_abs d₂ hd₂
            have hd1_pos : 0 < d₁ := (mem_Icc.mp (mem_filter.mp hd₁).1).1
            have hd2_pos : 0 < d₂ := (mem_Icc.mp (mem_filter.mp hd₂).1).1
            have h3 := card_multiples_Ioc n k (Nat.lcm d₁ d₂)
              (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd1_pos.ne' hd2_pos.ne')) hkn
            have ha1 : 0 ≤ |lam d₁| := abs_nonneg _
            have ha2 : 0 ≤ |lam d₂| := abs_nonneg _
            have ha3 : 0 ≤ |(((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) -
                (k : ℝ) / (Nat.lcm d₁ d₂ : ℝ)| := abs_nonneg _
            have h12 : |lam d₁| * |lam d₂| ≤ 1 := by nlinarith
            nlinarith
      _ = (S.card : ℝ) ^ 2 := by simp [sq]
      _ ≤ (z : ℝ) ^ 2 := by
            have hScard : S.card ≤ z := by
              calc S.card ≤ (Icc 1 z).card := Finset.card_filter_le _ _
                _ = z := by rw [Nat.card_Icc]; omega
            gcongr
  -- Combine Steps 1, 2, 3, 4
  have hdiff : ∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ *
      (((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) =
      (k : ℝ) * (∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ / (Nat.lcm d₁ d₂ : ℝ)) +
      ∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ *
        ((((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) -
          (k : ℝ) / (Nat.lcm d₁ d₂ : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d₁ _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d₂ _
    ring
  rw [hmain_quad, mul_one_div] at hdiff
  linarith [le_abs_self (∑ d₁ ∈ S, ∑ d₂ ∈ S, lam d₁ * lam d₂ *
    ((((Ioc (n - k) n).filter (fun m => Nat.lcm d₁ d₂ ∣ m)).card : ℝ) -
      (k : ℝ) / (Nat.lcm d₁ d₂ : ℝ)))]

/-! ## Section 4: Selberg Asymptotic (`14 * k ≤ n`, `200000 ≤ k`) -/

private lemma selberg_cubic_aux {L : ℝ} (hL : 12.2 ≤ L) :
    1 / ((5 / 12 : ℝ) * L - 0.292) + 4 / L ^ 2 < 3.563 / (L + 2.565) := by
  have hD1 : (0 : ℝ) < L + 2.565 := by linarith
  have hD2 : (0 : ℝ) < (5 / 12 : ℝ) * L - 0.292 := by linarith
  have hD3 : (0 : ℝ) < L ^ 2 := by positivity
  have hD : (0 : ℝ) < (L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) * L ^ 2 := by positivity
  suffices h : (L + 2.565) * L ^ 2 + 4 * (L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) <
      3.563 * ((5 / 12 : ℝ) * L - 0.292) * L ^ 2 by
    have h1 : (1 / ((5 / 12 : ℝ) * L - 0.292) + 4 / L ^ 2) *
        ((L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) * L ^ 2) =
        (L + 2.565) * L ^ 2 + 4 * (L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) := by
      rw [add_mul]
      have ha : 1 / ((5 / 12 : ℝ) * L - 0.292) * ((L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) * L ^ 2) =
          (L + 2.565) * L ^ 2 := by
        rw [div_mul_eq_mul_div, div_eq_iff hD2.ne']; ring
      have hb : 4 / L ^ 2 * ((L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) * L ^ 2) =
          4 * (L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) := by
        rw [div_mul_eq_mul_div, div_eq_iff hD3.ne']; ring
      linarith
    have h2 : 3.563 / (L + 2.565) * ((L + 2.565) * ((5 / 12 : ℝ) * L - 0.292) * L ^ 2) =
        3.563 * ((5 / 12 : ℝ) * L - 0.292) * L ^ 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff hD1.ne']; ring
    exact lt_of_mul_lt_mul_right (by linarith) hD.le
  have hsqL : 0 ≤ (L - 12.2) ^ 2 := sq_nonneg _
  have hcubL : 0 ≤ (L - 12.2) ^ 2 * (L - 12.2) := mul_nonneg hsqL (by linarith)
  nlinarith

set_option maxHeartbeats 400000 in
/-- Case 4: `14 * k ≤ n` and `200000 ≤ k` via Selberg upper bound sieve. -/
theorem selberg_large_k {n k : ℕ} (hk : 200000 ≤ k) (h14k : 14 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_contra hcon
  push Not at hcon
  have h2k : 2 * k ≤ n := by omega
  have hkn : k ≤ n := by omega
  set P := ((Ioc (n - k) n).filter Nat.Prime).card
  have hP_le : P ≤ k := by
    calc P ≤ (Ioc (n - k) n).card := Finset.card_filter_le _ _
      _ = k := by rw [Nat.card_Ioc]; omega
  -- Lower bound on P from (n - k)^(k - P) ≤ k!
  have hpow := pow_sub_prime_count_le_factorial (by omega) h2k hcon
  have hpowR : ((n - k : ℕ) : ℝ) ^ (k - P) ≤ (k ! : ℝ) := by exact_mod_cast hpow
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := by
    have : 0 < n - k := by omega
    exact_mod_cast this
  have hlog_pow : ((k - P : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) ≤ Real.log (k ! : ℝ) := by
    have h1 := Real.log_le_log (pow_pos hnk_pos _) hpowR
    rwa [Real.log_pow] at h1
  have hlog_k_ge : (12.2 : ℝ) ≤ Real.log (k : ℝ) := by
    calc (12.2 : ℝ) ≤ Real.log 200000 := log_200000_bounds.1
      _ ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  set L := Real.log (k : ℝ)
  have hL_pos : 0 < L := by linarith
  have h13 : (13 : ℝ) * (k : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
    have : 13 * k ≤ n - k := by omega
    exact_mod_cast this
  have hlog_nk : L + 2.564 ≤ Real.log ((n - k : ℕ) : ℝ) := by
    have h1 := Real.log_le_log (by positivity) h13
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    linarith [log_thirteen_bounds.1]
  have hlog_nk_pos : 0 < Real.log ((n - k : ℕ) : ℝ) := by linarith
  have hfact := log_factorial_le k
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlog_k1 : Real.log ((k : ℝ) + 1) ≤ L + 1 / (k : ℝ) := by
    have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hk_pos.ne'] at h1
    have h2 : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by field_simp; ring
    linarith
  have hfact_ub : Real.log (k ! : ℝ) ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := by
    have hinv : (1 : ℝ) / (k : ℝ) ≤ 1 := by rw [div_le_one hk_pos]; linarith [show (200000 : ℝ) ≤ k by exact_mod_cast hk]
    have hk1_mul : ((k : ℝ) + 1) * (1 / (k : ℝ)) = 1 + 1 / (k : ℝ) := by field_simp
    nlinarith
  -- Choose z = ⌊2 * √k / L⌋₊
  set z : ℕ := ⌊2 * Real.sqrt (k : ℝ) / L⌋₊
  have hsqrt_ge : (447 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    have h1 : (447 : ℝ) ^ 2 ≤ (k : ℝ) := by
      have : (200000 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    calc (447 : ℝ) = Real.sqrt ((447 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt h1
  -- Show 6 ≤ z
  have hz6 : 6 ≤ z := by
    apply Nat.le_floor
    have hL_le_sqrt : L ≤ Real.sqrt (k : ℝ) / 10 := by
      -- log k = 2 * log(√k) ≤ 2 * (√k / 20 + log 20 - 1)? Simpler: log(√k / 400) ≤ √k / 400 - 1
      have h1 : Real.log (Real.sqrt (k : ℝ) / 400) ≤ Real.sqrt (k : ℝ) / 400 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at h1
      have h400 : Real.log 400 ≤ 6.3 := by
        have h2 := log_two_bounds.2
        have hle : (400 : ℝ) ≤ (2 : ℝ) ^ 9 := by norm_num
        have := Real.log_le_log (by norm_num) hle
        rw [Real.log_pow] at this; push_cast at this; linarith
      have hsq : Real.log (Real.sqrt (k : ℝ)) = L / 2 := by
        rw [Real.log_sqrt hk_pos.le]
      nlinarith
    rw [le_div_iff₀ hL_pos]
    norm_num
    nlinarith
  have hz_le : (z : ℝ) ≤ 2 * Real.sqrt (k : ℝ) / L := Nat.floor_le (by positivity)
  have hz_lt : 2 * Real.sqrt (k : ℝ) / L < (z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hznk : z ≤ n - k := by
    have h1 : (z : ℝ) ≤ (k : ℝ) := by
      have hsq : Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
        have : (1 : ℝ) ≤ k := by linarith [show (200000 : ℝ) ≤ k by exact_mod_cast hk]
        nlinarith [Real.sq_sqrt hk_pos.le]
      have hdiv : 2 * Real.sqrt (k : ℝ) / L ≤ Real.sqrt (k : ℝ) := by
        rw [div_le_iff₀ hL_pos]; nlinarith
      linarith
    have hzk : z ≤ k := by exact_mod_cast h1
    omega
  -- Apply Selberg upper bound
  have hsel := selberg_upper_bound hkn (by omega : 1 ≤ z) hznk
  have hG_lb : Real.log ((z : ℝ) + 1) + 1 / 2 ≤ selbergG z :=
    (harmonic_ge_log_add_half z hz6).trans (harmonic_le_selbergG z)
  -- Lower bound log(z + 1) + 1/2 ≥ (5/12) * L - 0.292
  have hlog_z1 : (5 / 12 : ℝ) * L - 0.292 ≤ Real.log ((z : ℝ) + 1) + 1 / 2 := by
    have h1 : Real.log (2 * Real.sqrt (k : ℝ) / L) ≤ Real.log ((z : ℝ) + 1) :=
      Real.log_le_log (by positivity) hz_lt.le
    rw [Real.log_div (by positivity) hL_pos.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_sqrt hk_pos.le] at h1
    have hlogL : Real.log L ≤ Real.log 12 + (L - 12) / 12 := by
      have h2 := Real.log_le_sub_one_of_pos (x := L / 12) (by positivity)
      rw [Real.log_div hL_pos.ne' (by norm_num)] at h2
      linarith
    linarith [log_two_bounds.1, log_twelve_bounds.2]
  have hdenom_pos : (0 : ℝ) < (5 / 12 : ℝ) * L - 0.292 := by linarith
  have hP_ub : (P : ℝ) ≤ (k : ℝ) / ((5 / 12 : ℝ) * L - 0.292) + 4 * (k : ℝ) / L ^ 2 := by
    have hG_ge : (5 / 12 : ℝ) * L - 0.292 ≤ selbergG z := hlog_z1.trans hG_lb
    have h1 : (k : ℝ) / selbergG z ≤ (k : ℝ) / ((5 / 12 : ℝ) * L - 0.292) := by
      gcongr
    have h2 : (z : ℝ) ^ 2 ≤ 4 * (k : ℝ) / L ^ 2 := by
      calc (z : ℝ) ^ 2 ≤ (2 * Real.sqrt (k : ℝ) / L) ^ 2 := by gcongr
        _ = 4 * (Real.sqrt (k : ℝ)) ^ 2 / L ^ 2 := by ring
        _ = 4 * (k : ℝ) / L ^ 2 := by rw [Real.sq_sqrt hk_pos.le]
    linarith
  -- Lower bound P ≥ (3.563 / (L + 2.565)) * k
  have hP_lb : 3.563 * (k : ℝ) / (L + 2.565) ≤ (P : ℝ) := by
    have hsubR : ((k - P : ℕ) : ℝ) = (k : ℝ) - (P : ℝ) := Nat.cast_sub hP_le
    rw [hsubR] at hlog_pow
    -- ((k - P) : ℝ) * (L + 2.564) ≤ (k - P) * log(n - k) ≤ k * L - k + L + 2
    have hkp_nonneg : (0 : ℝ) ≤ (k : ℝ) - (P : ℝ) := by
      have : (P : ℝ) ≤ (k : ℝ) := by exact_mod_cast hP_le
      linarith
    have h1 : ((k : ℝ) - (P : ℝ)) * (L + 2.564) ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := by
      calc ((k : ℝ) - (P : ℝ)) * (L + 2.564)
          ≤ ((k : ℝ) - (P : ℝ)) * Real.log ((n - k : ℕ) : ℝ) := by gcongr
        _ ≤ Real.log (k ! : ℝ) := hlog_pow
        _ ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := hfact_ub
    -- Hence P * (L + 2.564) ≥ 3.564 * k - L - 2
    have h2 : 3.564 * (k : ℝ) - L - 2 ≤ (P : ℝ) * (L + 2.564) := by nlinarith
    -- Show L + 2 ≤ 0.001 * k (since k ≥ 200000 and L ≤ √k)
    have hL_small : L + 2 ≤ 0.001 * (k : ℝ) := by
      have hk200 : (200000 : ℝ) ≤ k := by exact_mod_cast hk
      have hlog_le : L ≤ (k : ℝ) / 10000 + 10 := by
        have h3 := Real.log_le_sub_one_of_pos (x := (k : ℝ) / 10000) (by positivity)
        rw [Real.log_div hk_pos.ne' (by norm_num)] at h3
        linarith [log_10000_le]
      linarith
    have h3 : 3.563 * (k : ℝ) ≤ (P : ℝ) * (L + 2.565) := by
      have hP_nonneg : (0 : ℝ) ≤ (P : ℝ) := by positivity
      nlinarith
    exact (div_le_iff₀ (by linarith)).mpr h3
  -- Combine hP_lb and hP_ub to get contradiction via selberg_cubic_aux!
  have hcomb : 3.563 * (k : ℝ) / (L + 2.565) ≤
      (k : ℝ) / ((5 / 12 : ℝ) * L - 0.292) + 4 * (k : ℝ) / L ^ 2 :=
    hP_lb.trans hP_ub
  have hdivk : 3.563 / (L + 2.565) ≤ 1 / ((5 / 12 : ℝ) * L - 0.292) + 4 / L ^ 2 := by
    have h1 : (k : ℝ) * (3.563 / (L + 2.565)) ≤
        (k : ℝ) * (1 / ((5 / 12 : ℝ) * L - 0.292) + 4 / L ^ 2) := by
      linarith [show (k : ℝ) * (3.563 / (L + 2.565)) = 3.563 * (k : ℝ) / (L + 2.565) by ring,
        show (k : ℝ) * (1 / ((5 / 12 : ℝ) * L - 0.292) + 4 / L ^ 2) =
          (k : ℝ) / ((5 / 12 : ℝ) * L - 0.292) + 4 * (k : ℝ) / L ^ 2 by ring]
    exact le_of_mul_le_mul_left h1 hk_pos
  linarith [selberg_cubic_aux hlog_k_ge]

/-! ## Section 5: Sieve-210 (`250 ≤ k < 200000`, `14 * k ≤ n`) & Sieve-30 (`25 ≤ k < 250`, `20 * k ≤ n`) -/

/-- General modular sieve bound: in `(a, a + k]`, the number of integers coprime to `M` is at most
`φ(M) * (k / M + 1)`. -/
lemma card_coprime_Ioc_le (a k M : ℕ) (hM : 0 < M) :
    ((Ioc a (a + k)).filter (fun m => m.Coprime M)).card ≤ Nat.totient M * (k / M + 1) := by
  -- Cover Ioc a (a + k) by (k / M + 1) blocks of length M: Ioc (a + j*M) (a + (j+1)*M)
  have hsub : (Ioc a (a + k)).filter (fun m => m.Coprime M) ⊆
      (range (k / M + 1)).biUnion (fun j => (Ioc (a + j * M) (a + (j + 1) * M)).filter (fun m => m.Coprime M)) := by
    intro m hm
    rw [mem_filter, mem_Ioc] at hm
    rw [mem_biUnion]
    refine ⟨(m - a - 1) / M, mem_range.mpr ?_, mem_filter.mpr ⟨mem_Ioc.mpr ?_, hm.2⟩⟩
    · have hlt : m - a - 1 < k := by omega
      have : (m - a - 1) / M ≤ k / M := Nat.div_le_div_right hlt.le
      omega
    · have h1 := Nat.div_mul_le_self (m - a - 1) M
      have h2 := Nat.lt_div_mul_add (a := m - a - 1) hM
      constructor
      · omega
      · have : ((m - a - 1) / M + 1) * M = (m - a - 1) / M * M + M := by ring
        omega
  calc ((Ioc a (a + k)).filter (fun m => m.Coprime M)).card
      ≤ ((range (k / M + 1)).biUnion (fun j =>
          (Ioc (a + j * M) (a + (j + 1) * M)).filter (fun m => m.Coprime M))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ range (k / M + 1),
          ((Ioc (a + j * M) (a + (j + 1) * M)).filter (fun m => m.Coprime M)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ range (k / M + 1), Nat.totient M := by
        apply Finset.sum_le_sum
        intro j _
        -- Map m ↦ m % M injectively into (range M).filter (fun r => r.Coprime M)
        rw [Nat.totient_eq_card_coprime]
        apply Finset.card_le_card_of_injOn (fun m => m % M)
        · intro m hm
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioc, Finset.mem_range] at hm ⊢
          refine ⟨Nat.mod_lt m hM, ?_⟩
          rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, ← Nat.gcd_rec]
          exact hm.2.symm.gcd_eq_one
        · intro m₁ hm₁ m₂ hm₂ hmod
          simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ioc] at hm₁ hm₂
          have h1 : m₁ % M = m₂ % M := hmod
          have hM1 : a + (j + 1) * M = a + j * M + M := by ring
          have hd1 := Nat.div_add_mod m₁ M
          have hd2 := Nat.div_add_mod m₂ M
          rcases lt_trichotomy (m₁ / M) (m₂ / M) with hlt | heq | hgt
          · have : m₁ + M ≤ m₂ := by nlinarith
            omega
          · rw [heq] at hd1; omega
          · have : m₂ + M ≤ m₁ := by nlinarith
            omega
    _ = Nat.totient M * (k / M + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

/-- Every prime in `(n - k, n]` is coprime to `M` if `M ≤ n - k`. -/
lemma card_primes_Ioc_le_coprime {n k M : ℕ} (hkn : k ≤ n) (hM : 0 < M) (hMnk : M ≤ n - k) :
    ((Ioc (n - k) n).filter Nat.Prime).card ≤ Nat.totient M * (k / M + 1) := by
  have hsub : (Ioc (n - k) n).filter Nat.Prime ⊆ (Ioc (n - k) n).filter (fun m => m.Coprime M) := by
    intro p hp
    rw [mem_filter, mem_Ioc] at hp ⊢
    refine ⟨hp.1, ?_⟩
    exact (hp.2.coprime_iff_not_dvd).mpr (fun hdvd => by
      have := Nat.le_of_dvd hM hdvd
      omega)
  calc ((Ioc (n - k) n).filter Nat.Prime).card
      ≤ ((Ioc (n - k) n).filter (fun m => m.Coprime M)).card := Finset.card_le_card hsub
    _ = ((Ioc (n - k) ((n - k) + k)).filter (fun m => m.Coprime M)).card := by
        rw [Nat.sub_add_cancel hkn]
    _ ≤ Nat.totient M * (k / M + 1) := card_coprime_Ioc_le (n - k) k M hM

/-- Case 5: `14 * k ≤ n` and `250 ≤ k ≤ 200000` via Sieve-210. -/
theorem sieve210_mid_k {n k : ℕ} (hk1 : 250 ≤ k) (hk2 : k ≤ 200000) (h14k : 14 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_contra hcon
  push Not at hcon
  have h2k : 2 * k ≤ n := by omega
  have hkn : k ≤ n := by omega
  set P := ((Ioc (n - k) n).filter Nat.Prime).card
  have hP_le : P ≤ 48 * (k / 210 + 1) := by
    have htot : Nat.totient 210 = 48 := by decide
    rw [← htot]
    exact card_primes_Ioc_le_coprime hkn (by norm_num) (by omega)
  have hpow := pow_sub_prime_count_le_factorial (by omega) h2k hcon
  have hpowR : ((n - k : ℕ) : ℝ) ^ (k - P) ≤ (k ! : ℝ) := by exact_mod_cast hpow
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast (by omega : 0 < n - k)
  have hlog_pow : ((k - P : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) ≤ Real.log (k ! : ℝ) := by
    have h1 := Real.log_le_log (pow_pos hnk_pos _) hpowR
    rwa [Real.log_pow] at h1
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set L := Real.log (k : ℝ)
  have hL_ge : (0 : ℝ) ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have h13 : (13 : ℝ) * (k : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
    have : 13 * k ≤ n - k := by omega
    exact_mod_cast this
  have hlog_nk : L + 2.564 ≤ Real.log ((n - k : ℕ) : ℝ) := by
    have h1 := Real.log_le_log (by positivity) h13
    rw [Real.log_mul (by norm_num) hk_pos.ne'] at h1
    linarith [log_thirteen_bounds.1]
  have hlog_k1 : Real.log ((k : ℝ) + 1) ≤ L + 1 / (k : ℝ) := by
    have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hk_pos.ne'] at h1
    have h2 : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by field_simp; ring
    linarith
  have hfact_ub : Real.log (k ! : ℝ) ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := by
    have hinv : (1 : ℝ) / (k : ℝ) ≤ 1 := by rw [div_le_one hk_pos]; exact_mod_cast (by omega : 1 ≤ k)
    have hk1_mul : ((k : ℝ) + 1) * (1 / (k : ℝ)) = 1 + 1 / (k : ℝ) := by field_simp
    nlinarith [log_factorial_le k]
  have hC_lb : (27 / 35 : ℝ) * (k : ℝ) - 48 ≤ ((k - P : ℕ) : ℝ) := by
    have hdiv : ((k / 210 : ℕ) : ℝ) ≤ (k : ℝ) / 210 := by
      have : 210 * (k / 210) ≤ k := Nat.mul_div_le k 210
      have : (210 : ℝ) * ((k / 210 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
      linarith
    have hPR : (P : ℝ) ≤ 48 * ((k : ℝ) / 210 + 1) := by
      have h1 : (P : ℝ) ≤ 48 * (((k / 210 : ℕ) : ℝ) + 1) := by exact_mod_cast hP_le
      linarith
    have hP_le_k : P ≤ k := by omega
    have hsubR : ((k - P : ℕ) : ℝ) = (k : ℝ) - (P : ℝ) := Nat.cast_sub hP_le_k
    linarith
  have hmain : ((27 / 35 : ℝ) * (k : ℝ) - 48) * (L + 2.564) ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := by
    have hC_pos : (0 : ℝ) ≤ (27 / 35 : ℝ) * (k : ℝ) - 48 := by
      have : (250 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    calc ((27 / 35 : ℝ) * (k : ℝ) - 48) * (L + 2.564)
        ≤ ((k - P : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) := by gcongr
      _ ≤ Real.log (k ! : ℝ) := hlog_pow
      _ ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := hfact_ub
  -- Split [250, 200000] into 6 subintervals
  by_cases h1 : k ≤ 320
  · have h320 : Real.log 320 ≤ 5.79 := by
      have h2 := log_two_bounds.2
      have hle : (320 : ℝ) ^ 2 * (1 + 1 / 4) ≤ (2 : ℝ) ^ 17 := by norm_num
      have hlg := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlg
      push_cast at hlg
      have hlo := log_one_add_ge (t := (1 / 4 : ℝ)) (by norm_num)
      linarith
    have hL_ub : L ≤ 5.79 := (Real.log_le_log hk_pos (by exact_mod_cast h1)).trans h320
    have hk_ge : (250 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  · by_cases h2 : k ≤ 500
    · have hL_ub : L ≤ 6.22 :=
        (Real.log_le_log hk_pos (by exact_mod_cast h2)).trans
          (log_upper_of_mul_pow_two (a := 500) (by norm_num) (t := 1 / 50) (by norm_num) 9 (by norm_num) (by norm_num))
      have hk_ge : (320 : ℝ) ≤ k := by exact_mod_cast (by omega : 320 ≤ k)
      nlinarith
    · by_cases h3 : k ≤ 1200
      · have hL_ub : L ≤ 7.18 :=
          (Real.log_le_log hk_pos (by exact_mod_cast h3)).trans
            (log_upper_of_mul_pow_two (a := 1200) (by norm_num) (t := 7 / 10) (by norm_num) 11 (by norm_num) (by norm_num))
        have hk_ge : (500 : ℝ) ≤ k := by exact_mod_cast (by omega : 500 ≤ k)
        nlinarith
      · by_cases h4 : k ≤ 4000
        · have hL_ub : L ≤ 8.30 :=
            (Real.log_le_log hk_pos (by exact_mod_cast h4)).trans
              (log_upper_of_mul_pow_two (a := 4000) (by norm_num) (t := 1 / 50) (by norm_num) 12 (by norm_num) (by norm_num))
          have hk_ge : (1200 : ℝ) ≤ k := by exact_mod_cast (by omega : 1200 ≤ k)
          nlinarith
        · by_cases h5 : k ≤ 20000
          · have hL_ub : L ≤ 9.98 :=
              (Real.log_le_log hk_pos (by exact_mod_cast h5)).trans
                (log_upper_of_mul_pow_two (a := 20000) (by norm_num) (t := 3 / 5) (by norm_num) 15 (by norm_num) (by norm_num))
            have hk_ge : (4000 : ℝ) ≤ k := by exact_mod_cast (by omega : 4000 ≤ k)
            nlinarith
          · have hL_ub : L ≤ 12.23 :=
              (Real.log_le_log hk_pos (by exact_mod_cast hk2)).trans log_200000_bounds.2
            have hk_ge : (20000 : ℝ) ≤ k := by exact_mod_cast (by omega : 20000 ≤ k)
            nlinarith

/-- Case 6a: `20 * k ≤ n` and `30 ≤ k ≤ 250` via Sieve-30. -/
theorem sieve30_small_k {n k : ℕ} (hk1 : 30 ≤ k) (hk2 : k ≤ 250) (h20k : 20 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_contra hcon
  push Not at hcon
  have h2k : 2 * k ≤ n := by omega
  have hkn : k ≤ n := by omega
  set P := ((Ioc (n - k) n).filter Nat.Prime).card
  have hP_le : P ≤ 8 * (k / 30 + 1) := by
    have htot : Nat.totient 30 = 8 := by decide
    rw [← htot]
    exact card_primes_Ioc_le_coprime hkn (by norm_num) (by omega)
  have hpow := pow_sub_prime_count_le_factorial (by omega) h2k hcon
  have hpowR : ((n - k : ℕ) : ℝ) ^ (k - P) ≤ (k ! : ℝ) := by exact_mod_cast hpow
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := by exact_mod_cast (by omega : 0 < n - k)
  have hlog_pow : ((k - P : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) ≤ Real.log (k ! : ℝ) := by
    have h1 := Real.log_le_log (pow_pos hnk_pos _) hpowR
    rwa [Real.log_pow] at h1
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set L := Real.log (k : ℝ)
  have hL_ge : (0 : ℝ) ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have h19 : (19 : ℝ) * (k : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
    have : 19 * k ≤ n - k := by omega
    exact_mod_cast this
  have hlog_nk : L + 2.942 ≤ Real.log ((n - k : ℕ) : ℝ) := by
    have h1 := Real.log_le_log (by positivity) h19
    rw [Real.log_mul (by norm_num) hk_pos.ne'] at h1
    linarith [log_nineteen_ge]
  have hlog_k1 : Real.log ((k : ℝ) + 1) ≤ L + 1 / (k : ℝ) := by
    have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) hk_pos.ne'] at h1
    have h2 : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / (k : ℝ) := by field_simp; ring
    linarith
  have hfact_ub : Real.log (k ! : ℝ) ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := by
    have hinv : (1 : ℝ) / (k : ℝ) ≤ 1 := by rw [div_le_one hk_pos]; exact_mod_cast (by omega : 1 ≤ k)
    have hk1_mul : ((k : ℝ) + 1) * (1 / (k : ℝ)) = 1 + 1 / (k : ℝ) := by field_simp
    nlinarith [log_factorial_le k]
  have hC_lb : (11 / 15 : ℝ) * (k : ℝ) - 8 ≤ ((k - P : ℕ) : ℝ) := by
    have hdiv : ((k / 30 : ℕ) : ℝ) ≤ (k : ℝ) / 30 := by
      have : 30 * (k / 30) ≤ k := Nat.mul_div_le k 30
      have : (30 : ℝ) * ((k / 30 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
      linarith
    have hPR : (P : ℝ) ≤ 8 * ((k : ℝ) / 30 + 1) := by
      have h1 : (P : ℝ) ≤ 8 * (((k / 30 : ℕ) : ℝ) + 1) := by exact_mod_cast hP_le
      linarith
    have hP_le_k : P ≤ k := by omega
    have hsubR : ((k - P : ℕ) : ℝ) = (k : ℝ) - (P : ℝ) := Nat.cast_sub hP_le_k
    linarith
  have hmain : ((11 / 15 : ℝ) * (k : ℝ) - 8) * (L + 2.942) ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := by
    have hC_pos : (0 : ℝ) ≤ (11 / 15 : ℝ) * (k : ℝ) - 8 := by
      have : (30 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    calc ((11 / 15 : ℝ) * (k : ℝ) - 8) * (L + 2.942)
        ≤ ((k - P : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) := by gcongr
      _ ≤ Real.log (k ! : ℝ) := hlog_pow
      _ ≤ (k : ℝ) * L - (k : ℝ) + L + 2 := hfact_ub
  by_cases h1 : k ≤ 45
  · have hL_ub : L ≤ 3.84 :=
      (Real.log_le_log hk_pos (by exact_mod_cast h1)).trans
        (log_upper_of_mul_pow_two (a := 45) (by norm_num) (t := 2 / 5) (by norm_num) 6 (by norm_num) (by norm_num))
    have hk_ge : (30 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  · by_cases h2 : k ≤ 120
    · have hL_ub : L ≤ 4.80 :=
        (Real.log_le_log hk_pos (by exact_mod_cast h2)).trans
          (log_upper_of_mul_pow_two (a := 120) (by norm_num) (t := 1 / 16) (by norm_num) 7 (by norm_num) (by norm_num))
      have hk_ge : (45 : ℝ) ≤ k := by exact_mod_cast (by omega : 45 ≤ k)
      nlinarith
    · have hL_ub : L ≤ 5.55 :=
        (Real.log_le_log hk_pos (by exact_mod_cast hk2)).trans log_250_le
      have hk_ge : (120 : ℝ) ≤ k := by exact_mod_cast (by omega : 120 ≤ k)
      nlinarith

/-! ## Section 6: Prime Chains & Tiny Bottom Check -/

/-- Purely structurally recursive binary-tree universal check over `[lo, lo + 2^d)`. -/
def allPow2 (f : ℕ → Bool) (lo : ℕ) : ℕ → Bool
  | 0 => f lo
  | d + 1 => allPow2 f lo d && allPow2 f (lo + 2 ^ d) d

lemma allPow2_sound (f : ℕ → Bool) :
    ∀ (d lo x : ℕ), allPow2 f lo d = true → lo ≤ x → x < lo + 2 ^ d → f x = true
  | 0, lo, x, h, h1, h2 => by
    simp only [allPow2, pow_zero] at h h2
    have : x = lo := by omega
    rwa [this]
  | d + 1, lo, x, h, h1, h2 => by
    simp only [allPow2, Bool.and_eq_true] at h
    rw [pow_succ] at h2
    by_cases hlt : x < lo + 2 ^ d
    · exact allPow2_sound f d lo x h.1 h1 hlt
    · exact allPow2_sound f d (lo + 2 ^ d) x h.2 (by omega) (by omega)

/-- Fast structurally recursive primality check for odd `p < 1025^2` using `allPow2` depth 9. -/
def isPrimeFast (p : ℕ) : Bool :=
  (3 ≤ p) && (p % 2 != 0) &&
    allPow2 (fun i =>
      let d := 2 * i + 3
      if d * d ≤ p then p % d != 0 else true) 0 9

lemma isPrimeFast_sound {p : ℕ} (hp_bound : p < 1025 * 1025) (h : isPrimeFast p = true) :
    p.Prime := by
  simp only [isPrimeFast, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h3, hodd⟩, hall⟩ := h
  rw [Nat.prime_def_lt']
  refine ⟨by omega, fun m hm2 hmlt hdvd => ?_⟩
  -- Since m ∣ p, let d = min m (p / m); then 2 ≤ d and d * d ≤ p and d ∣ p
  set d := min m (p / m)
  have hd_dvd : d ∣ p := by
    by_cases hle : m ≤ p / m
    · simp only [d, min_eq_left hle]; exact hdvd
    · simp only [d, min_eq_right (le_of_not_ge hle)]; exact Nat.div_dvd_of_dvd hdvd
  have hd2 : 2 ≤ d := by
    have hq : 2 ≤ p / m := by
      have : m * (p / m) = p := Nat.mul_div_cancel' hdvd
      rcases h : p / m with _ | _ | q
      · rw [h] at this; omega
      · rw [h] at this; omega
      · omega
    exact le_min hm2 hq
  have hd_sq : d * d ≤ p := by
    have hprod : m * (p / m) = p := Nat.mul_div_cancel' hdvd
    by_cases hle : m ≤ p / m
    · simp only [d, min_eq_left hle]
      calc m * m ≤ m * (p / m) := Nat.mul_le_mul_left m hle
        _ = p := hprod
    · simp only [d, min_eq_right (le_of_not_ge hle)]
      calc (p / m) * (p / m) ≤ (p / m) * m := Nat.mul_le_mul_left _ (le_of_not_ge hle)
        _ = p := by linarith
  have hd_odd : d % 2 ≠ 0 := by
    intro heven
    have h2d : 2 ∣ d := Nat.dvd_of_mod_eq_zero heven
    have h2p : 2 ∣ p := h2d.trans hd_dvd
    exact hodd (Nat.mod_eq_zero_of_dvd h2p)
  have hd3 : 3 ≤ d := by omega
  have hd_lt : d < 1025 := by nlinarith
  set i := (d - 3) / 2
  have hi_lt : i < 2 ^ 9 := by omega
  have hdi : 2 * i + 3 = d := by omega
  have hcheck := allPow2_sound _ 9 0 i hall (Nat.zero_le _) (by simpa using hi_lt)
  simp only [hdi, hd_sq, ↓reduceIte, bne_iff_ne, ne_eq] at hcheck
  exact hcheck (Nat.mod_eq_zero_of_dvd hd_dvd)

/-- Recursive check that a list is a valid prime chain with ratio `num / den` and all elements `< 1025^2`. -/
def isValidChain (num den : ℕ) : List ℕ → Bool
  | [] => true
  | [p] => (p < 1025 * 1025) && isPrimeFast p
  | p :: q :: rest =>
      (p < 1025 * 1025) && isPrimeFast p && (p < q) && (den * q ≤ num * p) && isValidChain num den (q :: rest)

/-- If `den < num`, `isValidChain num den L = true`, and `L.head ≤ x ≤ L.getLast`, then there exists
`p ∈ L` with `p.Prime`, `p ≤ x`, and `den * x < num * p`. -/
lemma exists_prime_in_chain (num den x : ℕ) (hnd : den < num) :
    ∀ L : List ℕ, isValidChain num den L = true →
      (hL : L ≠ []) → L.head hL ≤ x → x ≤ L.getLast hL →
      ∃ p ∈ L, p.Prime ∧ p ≤ x ∧ den * x < num * p
  | [], _, hne, _, _ => absurd rfl hne
  | [p], hval, _, hle, hge => by
    simp only [isValidChain, Bool.and_eq_true, decide_eq_true_eq] at hval
    have hp := isPrimeFast_sound hval.1 hval.2
    simp only [List.head_cons, List.getLast_singleton] at hle hge
    have hxp : x = p := by omega
    refine ⟨p, List.mem_cons_self, hp, hle, ?_⟩
    rw [hxp]
    exact Nat.mul_lt_mul_of_pos_right hnd hp.pos
  | p :: q :: rest, hval, _, hle, hge => by
    simp only [isValidChain, Bool.and_eq_true, decide_eq_true_eq] at hval
    obtain ⟨⟨⟨⟨hpb, hpfast⟩, hpq⟩, hrat⟩, hrest⟩ := hval
    have hp := isPrimeFast_sound hpb hpfast
    simp only [List.head_cons] at hle
    by_cases hxq : x < q
    · refine ⟨p, List.mem_cons_self, hp, hle, ?_⟩
      rcases Nat.eq_zero_or_pos den with rfl | hd
      · simp only [zero_mul]
        exact Nat.mul_pos (by omega) hp.pos
      · have h1 : den * x < den * q := Nat.mul_lt_mul_of_pos_left hxq hd
        omega
    · have hq_le : q ≤ x := by omega
      have hlast : (q :: rest).getLast (List.cons_ne_nil q rest) =
          (p :: q :: rest).getLast (List.cons_ne_nil p _) := rfl
      obtain ⟨r, hr, hrp, hrle, hrrat⟩ :=
        exists_prime_in_chain num den x hnd (q :: rest) hrest (List.cons_ne_nil q rest) hq_le (hlast ▸ hge)
      exact ⟨r, List.mem_cons_of_mem p hr, hrp, hrle, hrrat⟩

/-- Explicit prime chain of ratio `16 / 15` covering `[149, 580487]`. -/
def chain16 : List ℕ :=
  [149, 157, 167, 173, 181, 193, 199, 211, 223, 233, 241, 257, 271, 283, 293, 311,
   331, 353, 373, 397, 421, 449, 467, 491, 523, 557, 593, 631, 673, 709, 751, 797,
   839, 887, 941, 997, 1063, 1129, 1201, 1279, 1361, 1451, 1543, 1637, 1741, 1847,
   1951, 2081, 2213, 2357, 2503, 2663, 2837, 3023, 3221, 3433, 3659, 3889, 4139,
   4409, 4691, 5003, 5333, 5683, 6053, 6451, 6871, 7321, 7793, 8311, 8863, 9439,
   10067, 10733, 11447, 12203, 13009, 13873, 14797, 15773, 16823, 17939, 19121,
   20393, 21751, 23201, 24733, 26371, 28123, 29989, 31981, 34061, 36319, 38737,
   41299, 44041, 46957, 50087, 53419, 56963, 60757, 64793, 69109, 73709, 78607,
   83843, 89431, 95393, 101749, 108529, 115763, 123479, 131707, 140477, 149839,
   159811, 170447, 181789, 193891, 206813, 220589, 235289, 250969, 267679, 285521,
   304553, 324847, 346501, 369581, 394211, 420481, 448451, 478343, 510227, 544223,
   580487]

/-- Explicit prime chain of ratio `21 / 20` covering `[241, 2707]`. -/
def chain21 : List ℕ :=
  [241, 251, 263, 271, 283, 293, 307, 317, 331, 347, 359, 373, 389, 401, 421, 439,
   457, 479, 499, 523, 547, 571, 599, 619, 647, 677, 709, 743, 773, 811, 839, 877,
   919, 953, 997, 1039, 1087, 1129, 1181, 1237, 1297, 1361, 1429, 1499, 1571, 1637,
   1709, 1789, 1877, 1951, 2039, 2137, 2243, 2351, 2467, 2579, 2707]

set_option maxHeartbeats 1600000 in
lemma chain16_valid : isValidChain 16 15 chain16 = true := by decide

set_option maxHeartbeats 800000 in
lemma chain21_valid : isValidChain 21 20 chain21 = true := by decide

/-- Case 2: `500 ≤ n ≤ 1100000` and `2 * k ≤ n ≤ 14 * k` via `chain16`. -/
theorem chain16_central {n k : ℕ} (h2k : 2 * k ≤ n) (h14k : n ≤ 14 * k)
    (hn1 : 500 ≤ n) (hn2 : n ≤ 1100000) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_cases h38 : 8 * k < 3 * n + 10
  · -- Use p ∈ (max(k, (n-k)/2), n/2]
    have hx1 : 149 ≤ n / 2 := by omega
    have hx2 : n / 2 ≤ 580487 := by omega
    obtain ⟨p, -, hp, hple, hrat⟩ :=
      exists_prime_in_chain 16 15 (n / 2) (by norm_num) chain16 chain16_valid
        (by decide) hx1 hx2
    refine ⟨p, hp, ?_⟩
    exact dvd_choose_of_prime_half hp (by omega) (by omega) (by omega) (by omega)
  · -- 3 * n + 10 ≤ 8 * k: use p ∈ ((n - k) / 2, n / 3]
    have hx1 : 149 ≤ n / 3 := by omega
    have hx2 : n / 3 ≤ 580487 := by omega
    obtain ⟨p, -, hp, hple, hrat⟩ :=
      exists_prime_in_chain 16 15 (n / 3) (by norm_num) chain16 chain16_valid
        (by decide) hx1 hx2
    refine ⟨p, hp, ?_⟩
    exact dvd_choose_of_prime_third hp h2k (by omega) (by omega)

/-- Case 6b: `500 ≤ n ≤ 5000` and `14 * k ≤ n ≤ 20 * k` via `chain21`. -/
theorem chain21_range {n k : ℕ} (h14k : 14 * k ≤ n) (h20k : n ≤ 20 * k)
    (hn1 : 500 ≤ n) (hn2 : n ≤ 5000) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  have hx1 : 241 ≤ n / 2 := by omega
  have hx2 : n / 2 ≤ 2707 := by omega
  obtain ⟨p, -, hp, hple, hrat⟩ :=
    exists_prime_in_chain 21 20 (n / 2) (by norm_num) chain21 chain21_valid
      (by decide) hx1 hx2
  refine ⟨p, hp, ?_⟩
  exact dvd_choose_of_prime_half hp (by omega) (by omega) (by omega) (by omega)

/-- Fast computable Kummer carry check for small primes `p ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]`. -/
def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

def hasCarryPow (n k p : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 =>
    let pj := p ^ (j + 1)
    if k / pj + (n - k) / pj < n / pj then true else hasCarryPow n k p j

def hasSmallPrimeDiv (n k : ℕ) : Bool :=
  smallPrimes.any fun p => (2 * p ≤ n) && hasCarryPow n k p 10

lemma hasCarryPow_sound {n k p : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    ∀ m : ℕ, hasCarryPow n k p m = true → p ∣ n.choose k
  | 0, h => by simp [hasCarryPow] at h
  | j + 1, h => by
    simp only [hasCarryPow] at h
    split_ifs at h with hc
    · exact dvd_choose_of_carry hp hkn (by omega) hc
    · exact hasCarryPow_sound hp hkn j h

lemma smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by decide

lemma hasSmallPrimeDiv_sound {n k : ℕ} (hkn : k ≤ n) (h : hasSmallPrimeDiv n k = true) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  simp only [hasSmallPrimeDiv, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp_mem, h2p, hcarry⟩ := h
  have hp : p.Prime := smallPrimes_prime p hp_mem
  exact ⟨p, hp, hasCarryPow_sound hp hkn 10 hcarry, h2p⟩

/-- Check all `(n, k)` with `n < 512`, `4 ≤ k`, `2 * k ≤ n`, `n ≤ k * k`. -/
def checkSmallN : Bool :=
  allPow2 (fun n =>
    allPow2 (fun k =>
      if 4 ≤ k ∧ 2 * k ≤ n ∧ n ≤ k * k then hasSmallPrimeDiv n k else true) 0 8) 0 9

/-- Check the tiny corner `20 ≤ k < 30` and `20 * k ≤ n ≤ k * k` (`n ≤ 841`). -/
def checkTinyCorner : Bool :=
  allPow2 (fun k =>
    if 20 ≤ k ∧ k < 30 then
      allPow2 (fun n =>
        if 20 * k ≤ n ∧ n ≤ k * k then hasSmallPrimeDiv n k else true) (20 * k) 9
    else true) 20 4

set_option maxHeartbeats 1600000 in
lemma checkSmallN_true : checkSmallN = true := by decide

set_option maxHeartbeats 800000 in
lemma checkTinyCorner_true : checkTinyCorner = true := by decide

/-- Case 1: `n < 500`. -/
theorem small_n_case {n k : ℕ} (hk : 4 ≤ k) (hsq : n ≤ k * k) (h2k : 2 * k ≤ n) (hn : n < 500) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  have h1 := allPow2_sound _ 9 0 n checkSmallN_true (Nat.zero_le _) (by omega)
  have h2 := allPow2_sound _ 8 0 k h1 (Nat.zero_le _) (by omega)
  simp only [hk, h2k, hsq, and_self, ↓reduceIte] at h2
  exact hasSmallPrimeDiv_sound (by omega) h2

/-- Tiny corner: `20 ≤ k < 30` and `20 * k ≤ n ≤ k * k`. -/
theorem tiny_corner_case {n k : ℕ} (hk1 : 20 ≤ k) (hk2 : k < 30)
    (h20k : 20 * k ≤ n) (hsq : n ≤ k * k) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  have h1 := allPow2_sound _ 4 20 k checkTinyCorner_true hk1 (by omega)
  simp only [hk1, hk2, and_self, ↓reduceIte] at h1
  have hlt : n < 20 * k + 2 ^ 9 := by nlinarith
  have h2 := allPow2_sound _ 9 (20 * k) n h1 h20k hlt
  simp only [h20k, hsq, and_self, ↓reduceIte] at h2
  exact hasSmallPrimeDiv_sound (by omega) h2

/-- Master assembly of all non-Chebyshev cases: proves `Erdos384.erdos_384.R1.H2` given
the central Chebyshev range `2 * k ≤ n ≤ 14 * k` with `n ≥ 700000`. -/
theorem H2_of_chebyshev
    (hcheb : ∀ n k : ℕ, 4 ≤ k → 2 * k ≤ n → n ≤ 14 * k → 700000 ≤ n →
      ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n) :
    ∀ n k : ℕ, 4 ≤ k → n ≤ k * k → 2 * k ≤ n →
      ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  intro n k hk hsq h2k
  by_cases hn500 : n < 500
  · exact small_n_case hk hsq h2k hn500
  · by_cases h14 : n ≤ 14 * k
    · by_cases hn11 : n ≤ 1100000
      · exact chain16_central h2k h14 (by omega) hn11
      · exact hcheb n k hk h2k h14 (by omega)
    · -- 14 * k < n
      by_cases hk200k : 200000 ≤ k
      · exact selberg_large_k hk200k (by omega)
      · by_cases hk250 : 250 ≤ k
        · exact sieve210_mid_k hk250 (by omega) (by omega)
        · -- k < 250
          by_cases h20 : 20 * k ≤ n
          · have hk20 : 20 ≤ k := by nlinarith
            by_cases hk30 : 30 ≤ k
            · exact sieve30_small_k hk30 (by omega) h20
            · exact tiny_corner_case hk20 (by omega) h20 hsq
          · -- 14 * k < n < 20 * k and k < 250 => n < 5000
            exact chain21_range (by omega) (by omega) (by omega) (by omega)

end OMA.Erdos384Selberg



theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1.H2 :=
  OMA.Erdos384Selberg.H2_of_chebyshev OMA.Erdos384Cheb.chebyshev_central_range
