import OMAStatements.S_oeis_a096319

/-!
# Nonperiodicity of the last digit of prime sums

An eventual period would make the quadratic character modulo 5 periodic on the
ordered primes. Subtracting the period mean gives bounded partial sums and thus
a Mellin continuation beyond the line of absolute convergence. The zeta pole
first forces the mean to vanish. The quadratic term of the Euler product then
produces a pole at one half, contradicting analyticity of the Dirichlet L-function.

The prime-character obstruction follows the argument in
https://mathoverflow.net/questions/168378/the-prime-numbers-modulo-k-are-not-periodic.
-/

namespace PrimeDigitPeriod
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

open Filter Complex Set Topology
open scoped BigOperators

private noncomputable def base (p : Nat.Primes) (δ : ℝ) := (p : ℝ) ^ (-δ)
private lemma base_bounds (p : Nat.Primes) {δ : ℝ} (hδ : 0 < δ) :
    0 < base p δ ∧ base p δ ≤ (2 : ℝ) ^ (-δ) ∧ (2 : ℝ) ^ (-δ) < 1 := by
  exact ⟨Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _,
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le) (by linarith),
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩

private lemma majorant {m : ℕ} {δ : ℝ} (hd : 0 < δ) (hm : 1 < δ * m) :
    Summable fun t : Nat.Primes × ℕ => base t.1 δ ^ (t.2 + m) := by
  let q := (2 : ℝ) ^ (-δ)
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hp : ∀ p : Nat.Primes, Summable fun k : ℕ => base p δ ^ (k + m) := by
    intro p
    simp_rw [pow_add]
    have h := base_bounds p hd
    exact (summable_geometric_of_lt_one h.1.le (h.2.1.trans_lt hq)).mul_right _
  have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(δ * m))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).comp_injective Subtype.val_injective
  refine (summable_prod_of_nonneg fun t => pow_nonneg (base_bounds t.1 hd).1.le _).mpr ⟨hp, ?_⟩
  refine ((hs.mul_left ((1-q)⁻¹))).of_nonneg_of_le (fun p => tsum_nonneg fun k => pow_nonneg (base_bounds p hd).1.le _) ?_
  intro p
  have h := base_bounds p hd
  simp_rw [pow_add, tsum_mul_right, tsum_geometric_of_lt_one h.1.le (h.2.1.trans_lt hq)]
  have hb : base p δ ^ m = (p : ℝ) ^ (-(δ * m)) := by
    rw [base, ← Real.rpow_mul_natCast (Nat.cast_nonneg p.val)]
    congr 1
    ring
  rw [hb]
  gcongr
  exact h.2.1

private noncomputable def tailTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ℕ)
    (t : Nat.Primes × ℕ) (s : ℂ) : ℂ :=
  (χ t.1 * (t.1 : ℂ)^(-s)) ^ (t.2 + m) / ((t.2 + m : ℕ) : ℂ)

private lemma norm_term {N m : ℕ} (χ : DirichletCharacter ℂ N) (hm : 0 < m) (t : Nat.Primes × ℕ)
    {δ : ℝ} {s : ℂ} (hs : δ ≤ s.re) : ‖tailTerm χ m t s‖ ≤ base t.1 δ ^ (t.2 + m) := by
  have hp : 1 ≤ (t.1 : ℝ) := mod_cast t.1.prop.one_le
  have hc : ‖χ t.1 * (t.1 : ℂ)^(-s)‖ ≤ base t.1 δ := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (mod_cast t.1.prop.pos), neg_re]
    exact (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans
      (Real.rpow_le_rpow_of_exponent_le hp (neg_le_neg hs))
  rw [tailTerm, norm_div, norm_pow, Complex.norm_natCast]
  refine (div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ t.2 + m by omega))).trans ?_
  gcongr

private noncomputable def tailFn {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ℕ) (s : ℂ) : ℂ :=
  ∑' t : Nat.Primes × ℕ, tailTerm χ m t s

private lemma analytic_tail {N m : ℕ} (χ : DirichletCharacter ℂ N) (hm : 0 < m) :
    DifferentiableOn ℂ (tailFn χ m) {s : ℂ | 1 < s.re * m} := by
  intro s hs
  change 1 < s.re * m at hs
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  obtain ⟨δ,h1,h2⟩ := exists_between (show (1 : ℝ) / m < s.re from (div_lt_iff₀ hmr).mpr hs)
  have hd : 0 < δ := (div_pos zero_lt_one hmr).trans h1
  let U := {z : ℂ | δ < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const continuous_re
  have hD : DifferentiableOn ℂ (tailFn χ m) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm (majorant hd ((div_lt_iff₀ hmr).mp h1)) (hU := ho)
    · intro t z _
      unfold tailTerm
      have hne : (t.1 : ℂ) ≠ 0 := by exact_mod_cast t.1.prop.ne_zero
      fun_prop (disch := aesop)
    · intro t z hz
      exact norm_term χ hm t (le_of_lt hz)
  exact (hD.differentiableAt (ho.mem_nhds h2)).differentiableWithinAt

private lemma summable_terms {N m : ℕ} (χ : DirichletCharacter ℂ N) (hm : 0 < m)
    {s : ℂ} (hd : 0 < s.re) (hs : 1 < s.re * m) :
    Summable fun t : Nat.Primes × ℕ => tailTerm χ m t s :=
  (majorant hd hs).of_norm_bounded fun t => norm_term χ hm t le_rfl

private noncomputable def degreeSum {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ℕ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, tailTerm χ m (p,0) s

private lemma tail_step {N m : ℕ} (χ : DirichletCharacter ℂ N) (hm : 0 < m) {s : ℂ}
    (hd : 0 < s.re) (hs : 1 < s.re * m) :
    tailFn χ m s = degreeSum χ m s + tailFn χ (m+1) s := by
  have h := summable_terms χ hm hd hs
  have h' := summable_terms χ (Nat.succ_pos m) hd (show 1 < s.re * (m+1 : ℕ) by push_cast; nlinarith)
  have h0 : Summable fun p : Nat.Primes => tailTerm χ m (p,0) s :=
    h.comp_injective (i := fun p : Nat.Primes => (p,0)) (fun _ _ he => (Prod.mk.inj he).1)
  rw [tailFn, h.tsum_prod, tailFn, h'.tsum_prod, degreeSum, ← h0.tsum_add h'.prod]
  refine tsum_congr fun p => ?_
  have hp := (h.prod_factor p).sum_add_tsum_nat_add 1
  simpa [tailTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.symm

private lemma exp_tail_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (tailFn χ 1 s) = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← χ.LSeries_eulerProduct_exp_log hs,
    tailFn, (summable_terms χ (by decide : 0 < 1) (by linarith : 0 < s.re) (by simpa using hs)).tsum_prod]
  congr 1
  refine tsum_congr fun p => ?_
  have hn : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    grw [norm_mul, χ.norm_le_one, Complex.norm_natCast_cpow_of_pos (mod_cast p.prop.pos), neg_re, one_mul]
    exact Real.rpow_lt_one_of_one_lt_of_neg (mod_cast p.prop.one_lt) (by linarith)
  simpa [tailTerm] using (Complex.hasSum_taylorSeries_neg_log' hn).tsum_eq

private noncomputable def trivialChar : DirichletCharacter ℂ 1 := 1

private lemma exp_tail_zeta {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (tailFn trivialChar 1 s) = riemannZeta s := by
  rw [exp_tail_one _ hs, DirichletCharacter.LFunction_eq_LSeries _ hs, ← LSeries_one_eq_riemannZeta hs]
  congr 1
  funext n
  exact MulChar.one_apply (isUnit_of_subsingleton _)

private noncomputable def char5 : DirichletCharacter ℂ 5 :=
  (quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ)

private lemma char5_ne_one : char5 ≠ 1 := by
  intro h
  have hn : ¬ IsSquare (2 : ZMod 5) := by decide
  have hval := quadraticChar_neg_one_iff_not_isSquare.mpr hn
  have hu : IsUnit (2 : ZMod 5) := by decide
  have hc := congrArg (fun χ : DirichletCharacter ℂ 5 => χ 2) h
  change char5 (2 : ZMod 5) = (1 : DirichletCharacter ℂ 5) (2 : ZMod 5) at hc
  rw [char5, MulChar.ringHomComp_apply, hval, MulChar.one_apply hu] at hc
  norm_num at hc

private noncomputable def primeCoeff {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  if n.Prime then χ n else 0

private lemma prime_summable {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (primeCoeff χ) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by
    by_cases h : n.Prime <;> simp [primeCoeff,h,χ.norm_le_one]) hs

private lemma prime_series {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    degreeSum χ 1 s = LSeries (primeCoeff χ) s := by
  rw [LSeries_def₀ (by simp [primeCoeff, Nat.not_prime_zero]) s]
  let f (n : ℕ) := primeCoeff χ n / (n : ℂ) ^ s
  have hsup : Function.support f ⊆ {n | n.Prime} := by
    intro n hn
    by_contra hh
    exact hn (by simp [f, primeCoeff, show ¬n.Prime from hh])
  calc
    _ = ∑' n : {n : ℕ // n.Prime}, f n := by
      apply tsum_congr
      intro p
      simp [tailTerm, f, primeCoeff, p.prop, div_eq_mul_inv, Complex.cpow_neg]
    _ = _ := tsum_subtype_eq_of_support_subset hsup

private lemma trivial_value (n : ℕ) : trivialChar n = 1 := MulChar.one_apply (isUnit_of_subsingleton _)

private lemma char5_sq (p : Nat.Primes) (hp : (p : ℕ) ≠ 5) : char5 p ^ 2 = 1 := by
  have hz : (p : ZMod 5) ≠ 0 := by
    intro hz
    have hd : 5 ∣ p.val := (ZMod.natCast_eq_zero_iff p.val 5).mp hz
    exact hp ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) p.prop).mp hd).symm
  have hh := congrArg (Int.castRingHom ℂ) (quadraticChar_sq_one hz)
  simpa [char5, MulChar.ringHomComp_apply] using hh

private lemma square_sum (s : ℂ) (hs : 1 < s.re) :
    2 * degreeSum char5 2 s = degreeSum trivialChar 1 (2*s) - (5:ℂ)^(-(2*s)) := by
  let five : Nat.Primes := ⟨5, by decide⟩
  let f (p : Nat.Primes) := (p : ℂ)^(-(2*s))
  have hterm : ∀ p : Nat.Primes, 2 * tailTerm char5 2 (p,0) s = if p = five then 0 else f p := by
    intro p
    by_cases hp : p = five
    · subst p
      rw [if_pos rfl]
      have hzero : char5 (5 : ZMod 5) = 0 := by
        rw [show (5 : ZMod 5) = 0 by decide]
        exact MulChar.map_nonunit _ (by simp)
      change 2 * ((char5 (5 : ZMod 5) * (5 : ℂ)^(-s))^2 / 2) = 0
      rw [hzero]
      norm_num
    · have hne : (p:ℕ) ≠ 5 := fun he => hp (Subtype.ext he)
      have hpow : ((p:ℂ)^(-s))^2 = f p := by
        dsimp only [f]
        rw [← Complex.cpow_nat_mul]
        congr 1
        push_cast
        ring
      simp [tailTerm, hp, mul_pow, char5_sq p hne, hpow]
      ring
  have htwo : 1 < (2*s).re := by simp only [two_mul, Complex.add_re]; linarith
  have ht := summable_terms trivialChar (by decide : 0<1) (by linarith : 0 < (2*s).re) (by simpa using htwo)
  have hsum : Summable f := by
    have hh := ht.comp_injective (i := fun p : Nat.Primes => (p,0)) (fun _ _ he => (Prod.mk.inj he).1)
    simpa [Function.comp_def, f, tailTerm, trivial_value] using hh
  have htriv : degreeSum trivialChar 1 (2*s) = ∑' p, f p := by
    simp [degreeSum, tailTerm, trivial_value, f]
  rw [htriv, degreeSum, ← tsum_mul_left, tsum_congr hterm]
  have heq := hsum.tsum_eq_add_tsum_ite five
  dsimp only [f, five] at heq ⊢
  linear_combination -heq
open Finset
private noncomputable def primeAt (i : ℕ) := Nat.nth Nat.Prime i
private noncomputable def digit (n : ℕ) := (∑ i ∈ range n, primeAt i) % 10
private noncomputable def f5 (n : ℕ) : ℤ := quadraticChar (ZMod 5) (n : ZMod 5)

private lemma char_period {N T : ℕ} (h : ∀ n ≥ N, digit (n+T) = digit n) :
    ∀ n ≥ N, f5 (primeAt (n+T)) = f5 (primeAt n) := by
  intro n hn
  have congrSum (k : ℕ) (hk : N ≤ k) :
      (∑ i ∈ range (k+T), (primeAt i : ZMod 5)) = ∑ i ∈ range k, (primeAt i : ZMod 5) := by
    have he : (∑ i ∈ range (k+T), primeAt i) ≡ (∑ i ∈ range k, primeAt i) [MOD 10] := h k hk
    have he5 := he.of_dvd (by decide : 5 ∣ 10)
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr he5
  have h1 := congrSum n hn
  have h2 := congrSum (n+1) (by omega)
  rw [show n+1+T = (n+T)+1 by omega, sum_range_succ, sum_range_succ, h1] at h2
  exact congrArg (quadraticChar (ZMod 5)) (add_left_cancel h2)

private def initialSum (f : ℕ → ℤ) (n : ℕ) := ∑ i ∈ range n, f i

private lemma periodic_center {N T : ℕ} (hT : 0 < T) (f : ℕ → ℤ) (h : ∀ n ≥ N, f (n+T) = f n) :
    ∃ M K : ℤ, 0 ≤ K ∧ ∀ n, |(T:ℤ) * initialSum f n - (n:ℤ) * M| ≤ K := by
  let M := initialSum f (N+T) - initialSum f N
  have step (n : ℕ) (hn : N ≤ n) : initialSum f (n+T) - initialSum f n = M := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [show n+1+T = n+T+1 by omega]
      simp only [initialSum, sum_range_succ] at ih ⊢
      rw [h n hn]
      omega
  let g (n : ℕ) := (T:ℤ) * initialSum f n - (n:ℤ) * M
  have per (n : ℕ) (hn : N ≤ n) : g (n+T) = g n := by
    have he : initialSum f (n+T) = initialSum f n + M := by linarith [step n hn]
    dsimp [g]
    rw [he]
    ring
  let K := ∑ i ∈ range (N+T), |g i|
  refine ⟨M,K,sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  change ∀ n, |g n| ≤ K
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N+T
    · exact single_le_sum (fun i _ => abs_nonneg (g i)) (mem_range.mpr hn)
    · have hv : g n = g (n-T) := by
        simpa only [Nat.sub_add_cancel (show T ≤ n by omega)] using per (n-T) (by omega)
      rw [hv]
      exact ih _ (by omega)

private lemma primes_prefix_sum (g : ℕ → ℤ) (x : ℕ) :
    (∑ k ∈ range x, if k.Prime then g k else 0) =
      initialSum (fun i => g (primeAt i)) (Nat.count Nat.Prime x) := by
  induction x with
  | zero => simp [initialSum]
  | succ x ih =>
    rw [sum_range_succ, ih, Nat.count_succ]
    by_cases hx : x.Prime
    · simp [hx, initialSum, sum_range_succ, primeAt, Nat.nth_count hx]
    · simp [hx]

private lemma prime_discrepancy {N T : ℕ} (hT : 0 < T) (h : ∀ n ≥ N, digit (n+T) = digit n) :
    ∃ M K : ℤ, 0 ≤ K ∧ ∀ n, |∑ i ∈ Icc 1 n, (if i.Prime then (T:ℤ) * f5 i - M else 0)| ≤ K := by
  obtain ⟨M,K,hK,hb⟩ := periodic_center hT (fun i => f5 (primeAt i)) (char_period h)
  refine ⟨M,K,hK,fun n => ?_⟩
  have hset : Finset.Icc 1 n = (range (n+1)).erase 0 := by ext i; simp; omega
  have hzero : (if Nat.Prime 0 then (T:ℤ) * f5 0 - M else 0) = 0 := by simp [Nat.not_prime_zero]
  have herase := sum_erase_add (range (n+1)) (fun i : ℕ => if i.Prime then (T:ℤ)*f5 i-M else 0)
    (mem_range.mpr (by omega) : 0 ∈ range (n+1))
  rw [hzero, add_zero] at herase
  rw [hset, herase, primes_prefix_sum]
  simpa [initialSum, sum_sub_distrib, ← mul_sum] using hb (Nat.count Nat.Prime (n+1))
open Set Filter Complex Topology MeasureTheory Asymptotics
private noncomputable def cutoff (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  if 1 < x then ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k else 0
private noncomputable def continuation (f : ℕ → ℂ) (s : ℂ) : ℂ := s * mellin (cutoff f) (-s)

private lemma bounded_analytic (f : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ K) :
    DifferentiableOn ℂ (continuation f) {s : ℂ | 0 < s.re} := by
  have hnorm (x : ℝ) : ‖cutoff f x‖ ≤ K := by
    by_cases hx : 1 < x
    · simpa [cutoff,hx] using hb ⌊x⌋₊
    · simpa [cutoff,hx] using hK
  have hm : Measurable (cutoff f) := by
    exact Measurable.ite measurableSet_Ioi
      ((measurable_of_countable fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k).comp Nat.measurable_floor)
      measurable_const
  have hloc : LocallyIntegrableOn (cutoff f) (Ioi 0) := by
    exact (locallyIntegrableOn_const K).mono hm.aestronglyMeasurable (Eventually.of_forall fun x =>
      (hnorm x).trans (Real.le_norm_self K))
  intro s hs
  have htop : cutoff f =O[atTop] fun x : ℝ => x ^ (-(0:ℝ)) :=
    isBigO_of_le' atTop (c := K) fun x => by simpa using hnorm x
  have hsmall : cutoff f =ᶠ[𝓝[>] (0:ℝ)] (fun _ => 0) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with x hx
    simp [cutoff, not_lt.mpr hx.le]
  have hbnoise : cutoff f =O[𝓝[>] 0] fun x : ℝ => x ^ (-(-s.re-1)) :=
    hsmall.trans_isBigO (isBigO_zero _ _)
  have hd := mellin_differentiableAt_of_isBigO_rpow (s := -s) (b := -s.re-1) hloc htop (by simpa using hs) hbnoise (by simp)
  exact (differentiableAt_id.mul (hd.comp s differentiableAt_id.neg)).differentiableWithinAt

private lemma continuation_eq (f : ℕ → ℂ) (K : ℝ) (hb : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ K)
    {s : ℂ} (hs : 0 < s.re) (ha : LSeriesSummable f s) : continuation f s = LSeries f s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n:ℝ)^(0:ℝ) :=
    isBigO_of_le' atTop (c := K) fun n => by simpa using hb n
  rw [LSeries_eq_mul_integral f (le_refl 0) hs ha hO, continuation, mellin]
  congr 1
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioi (1:ℝ) ⊆ Ioi 0 from Ioi_subset_Ioi (by norm_num))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    change 1 < x at hx
    simp only [cutoff, if_pos hx, smul_eq_mul, show -s - 1 = -(s + 1) by ring, mul_comm]
  · intro x hx
    simp [cutoff, show ¬ 1 < x from hx.2]
open Filter Set Complex Topology

private lemma pole_forbids_power (A B : ℂ → ℂ) (ha : ContinuousAt A 1) (hb : ContinuousAt B 1)
    (hB : B 1 ≠ 0) (k : ℕ) (hk : 0 < k) (h : ∀ s : ℂ, 1 < s.re → A s = B s * riemannZeta s ^ k) : False := by
  let u : ℕ → ℂ := fun n => 1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have h0 : Tendsto (fun n : ℕ => ((1 / ((n:ℝ)+1) : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast (show Tendsto _ atTop _ from
      (Complex.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [u] using (tendsto_const_nhds (x := (1:ℂ))).add h0
  have hre (n : ℕ) : 1 < (u n).re := by
    simp only [u, add_re, one_re, ofReal_re, lt_add_iff_pos_right]
    positivity
  have hpun : Tendsto u atTop (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall fun n => ?_⟩
    change u n ≠ 1
    intro hh
    have hr := hre n
    rw [hh, one_re] at hr
    exact lt_irrefl _ hr
  have left := (ha.tendsto.comp hu).mul ((hu.sub (tendsto_const_nhds (x := (1:ℂ)))).pow k)
  have right := (hb.tendsto.comp hu).mul ((riemannZeta_residue_one.comp hpun).pow k)
  have eq := tendsto_nhds_unique (left.congr fun n => by
    change A (u n) * (u n - 1)^k = B (u n) * ((u n - 1) * riemannZeta (u n))^k
    rw [h _ (hre n), mul_pow]
    ring) right
  exact hB (by simpa [hk.ne'] using eq.symm)

private lemma mean_zero (A B : ℂ → ℂ) (ha : ContinuousAt A 1) (hb : ContinuousAt B 1)
    (ha0 : A 1 ≠ 0) (hb0 : B 1 ≠ 0) (M : ℤ)
    (h : ∀ s : ℂ, 1 < s.re → A s = B s * riemannZeta s ^ M) : M = 0 := by
  cases M with
  | ofNat k =>
    cases k with
    | zero => rfl
    | succ k =>
      exfalso
      apply pole_forbids_power A B ha hb hb0 (k+1) (by omega)
      intro s hs
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h s hs
  | negSucc k =>
    exfalso
    apply pole_forbids_power (fun s => (A s)⁻¹) (fun s => (B s)⁻¹) (ha.inv₀ ha0) (hb.inv₀ hb0)
      (inv_ne_zero hb0) (k+1) (by omega)
    intro s hs
    rw [h s hs, mul_inv_rev, zpow_negSucc, inv_inv, mul_comm]
open Filter Complex Set Topology

private theorem pole_obstruction (L F : ℂ → ℂ)
    (hL : Differentiable ℂ L) (hF : DifferentiableOn ℂ F {s | (1/3:ℝ) < s.re})
    (heq : ∀ s : ℂ, 2 < s.re → L (s/2)^2 = riemannZeta s * Complex.exp (F (s/2))) : False := by
  let U := {s : ℂ | 1 < s.re}
  have ho : IsOpen U := isOpen_lt continuous_const continuous_re
  have hc : Convex ℝ U := convex_halfSpace_re_gt _
  have hlu : AnalyticOnNhd ℂ (fun s : ℂ => L (s/2)^2) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    fun_prop
  have hru : AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta s * Complex.exp (F (s/2))) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro s hs
    have hs' : 1 < s.re := hs
    have hz : s ≠ 1 := by intro h; subst s; norm_num at hs'
    have hsi : (1/3:ℝ) < (s/2).re := by rw [Complex.div_ofNat_re]; linarith
    have hfo : DifferentiableAt ℂ F (s/2) := hF.differentiableAt (isOpen_lt continuous_const continuous_re |>.mem_nhds hsi)
    exact ((differentiableAt_riemannZeta hz).mul
      (Complex.differentiableAt_exp.comp s (hfo.comp s ((differentiableAt_id).div_const 2)))).differentiableWithinAt
  have h3 : (3:ℂ) ∈ U := by change 1 < (3:ℂ).re; norm_num
  have hw : (fun s : ℂ => L (s/2)^2) =ᶠ[𝓝 (3:ℂ)] (fun s => riemannZeta s * Complex.exp (F (s/2))) :=
    by
    refine Filter.eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num : (2:ℝ) < (3:ℂ).re)) ?_
    exact fun s hs => heq s hs
  have he := hlu.eqOn_of_preconnected_of_eventuallyEq hru hc.isPreconnected h3 hw
  let u : ℕ → ℂ := fun n => 1 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have h0 : Tendsto (fun n : ℕ => ((1 / ((n:ℝ)+1) : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast (show Tendsto _ atTop _ from
      (Complex.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [u] using (tendsto_const_nhds (x := (1:ℂ))).add h0
  have hre (n : ℕ) : 1 < (u n).re := by
    simp only [u, add_re, one_re, ofReal_re, lt_add_iff_pos_right]
    positivity
  have hpun : Tendsto u atTop (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall fun n => ?_⟩
    change u n ≠ 1
    intro h
    have hr := hre n
    rw [h, one_re] at hr
    exact lt_irrefl _ hr
  have hv : Tendsto (fun n => u n / 2) atTop (𝓝 (1/2:ℂ)) := hu.div_const _
  have hFhalf := hF.differentiableAt (isOpen_lt continuous_const continuous_re |>.mem_nhds (show (1/3:ℝ) < (1/2:ℂ).re by norm_num))
  have left := (hu.sub (tendsto_const_nhds (x:=(1:ℂ)))).mul (((hL _).continuousAt.tendsto.comp hv).pow 2)
  have right := (riemannZeta_residue_one.comp hpun).mul (Complex.continuous_exp.continuousAt.tendsto.comp (hFhalf.continuousAt.tendsto.comp hv))
  have eq := tendsto_nhds_unique (left.congr fun n => by
    change (u n - 1) * L (u n / 2) ^ 2 = ((u n - 1) * riemannZeta (u n)) * Complex.exp (F (u n / 2))
    have hn : L (u n / 2)^2 = riemannZeta (u n) * Complex.exp (F (u n / 2)) := he (hre n)
    rw [hn, mul_assoc]) right
  exact Complex.exp_ne_zero (F (1/2)) (by simpa only [sub_self, zero_mul, one_mul] using eq.symm)
private noncomputable def discrepancy (T : ℕ) (M : ℤ) : ℕ → ℂ :=
  (T:ℂ) • primeCoeff char5 - (M:ℂ) • primeCoeff trivialChar

private lemma discrepancy_value (T : ℕ) (M : ℤ) (i : ℕ) :
    discrepancy T M i = ((if i.Prime then (T:ℤ) * f5 i - M else 0 : ℤ) : ℂ) := by
  by_cases hi : i.Prime
  · simp [discrepancy,primeCoeff, hi, f5, char5, MulChar.ringHomComp_apply, trivial_value]
  · simp [discrepancy, primeCoeff, hi]

private lemma discrepancy_series {T : ℕ} {M K : ℤ}
    (hb : ∀ n, |∑ i ∈ Finset.Icc 1 n, (if i.Prime then (T:ℤ)*f5 i-M else 0)| ≤ K) :
    (DifferentiableOn ℂ (continuation (discrepancy T M)) {s : ℂ | 0 < s.re}) ∧
    ∀ s : ℂ, 1 < s.re → continuation (discrepancy T M) s =
      (T:ℂ)*degreeSum char5 1 s - (M:ℂ)*degreeSum trivialChar 1 s := by
  have hb' (n : ℕ) : ‖∑ i ∈ Finset.Icc 1 n, discrepancy T M i‖ ≤ (K:ℝ) := by
    simp_rw [discrepancy_value]
    rw [← Int.cast_sum, Complex.norm_intCast]
    exact_mod_cast hb n
  have hK : (0:ℝ) ≤ K := by simpa using hb' 0
  refine ⟨bounded_analytic _ _ hK hb', fun s hs => ?_⟩
  have hh := LSeriesSummable.smul (T:ℂ) (prime_summable char5 hs)
  have ht := LSeriesSummable.smul (M:ℂ) (prime_summable trivialChar hs)
  rw [continuation_eq _ _ hb' (by linarith) (LSeriesSummable.sub hh ht), discrepancy, LSeries_sub hh ht,
    LSeries_smul, LSeries_smul, prime_series, prime_series]

private lemma cancel_mean {T : ℕ} {M : ℤ} (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G {s : ℂ | 0 < s.re})
    (hd : ∀ s : ℂ, 1 < s.re → G s = (T:ℂ)*degreeSum char5 1 s - (M:ℂ)*degreeSum trivialChar 1 s) : M = 0 := by
  let F := fun s => G s + (T:ℂ)*tailFn char5 2 s - (M:ℂ)*tailFn trivialChar 2 s
  have hG1 : ContinuousAt G 1 := (hG.differentiableAt (isOpen_lt continuous_const continuous_re |>.mem_nhds (show (0:ℝ) < (1:ℂ).re by norm_num))).continuousAt
  have htail {q : ℕ} (χ : DirichletCharacter ℂ q) : ContinuousAt (tailFn χ 2) 1 := by
    have ho : IsOpen {s : ℂ | (1:ℝ) < s.re * (2:ℕ)} := isOpen_lt continuous_const (continuous_re.mul continuous_const)
    exact ((analytic_tail χ (by decide : 0 < 2)).differentiableAt (ho.mem_nhds (by norm_num))).continuousAt
  have hF : ContinuousAt F 1 := (hG1.add (continuousAt_const.mul (htail char5))).sub (continuousAt_const.mul (htail trivialChar))
  have hL := (DirichletCharacter.differentiable_LFunction char5_ne_one (1:ℂ)).continuousAt
  have hn : DirichletCharacter.LFunction char5 1 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re char5 (.inl char5_ne_one) (by simp)
  apply mean_zero (fun s => (DirichletCharacter.LFunction char5 s)^T) (fun s => Complex.exp (F s)) (hL.pow T) (Complex.continuous_exp.continuousAt.comp hF)
    (pow_ne_zero T hn) (Complex.exp_ne_zero _) M
  intro s hs
  have hst : 0 < s.re := by linarith
  have hs1 : 1 < s.re * (1:ℕ) := by simpa using hs
  rw [← exp_tail_one char5 hs, ← exp_tail_zeta hs, ← Complex.exp_nat_mul,
    ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  dsimp only [F]
  rw [tail_step char5 (by decide : 0<1) hst hs1, tail_step trivialChar (by decide : 0<1) hst hs1, hd s hs]
  norm_num
  ring

private lemma final_contradiction {T : ℕ} (hT : 0 < T) (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G {s : ℂ | 0 < s.re})
    (hd : ∀ s : ℂ, 1 < s.re → G s = (T:ℂ)*degreeSum char5 1 s) : False := by
  let F := fun s : ℂ => 2 * (G s / (T:ℂ)) + 2 * tailFn char5 3 s -
    tailFn trivialChar 2 (2*s) - (5:ℂ)^(-(2*s))
  have hF : DifferentiableOn ℂ F {s : ℂ | (1/3:ℝ) < s.re} := by
    intro s hs
    change (1/3:ℝ) < s.re at hs
    have hg := hG.differentiableAt (isOpen_lt continuous_const continuous_re |>.mem_nhds (show 0 < s.re by linarith))
    have ha {q m : ℕ} (χ : DirichletCharacter ℂ q) (hm : 0 < m) (z : ℂ) (hz : 1 < z.re * m) :
        DifferentiableAt ℂ (tailFn χ m) z := by
      have ho : IsOpen {w : ℂ | 1 < w.re * m} := isOpen_lt continuous_const (continuous_re.mul continuous_const)
      exact (analytic_tail χ hm).differentiableAt (ho.mem_nhds hz)
    have hc := ha char5 (by decide : 0 < 3) s (by norm_num; linarith)
    have ht := ha trivialChar (by decide : 0 < 2) (2*s) (by simp only [two_mul, Complex.add_re, Nat.cast_ofNat]; linarith)
    have hlin : DifferentiableAt ℂ (fun z : ℂ => 2*z) s := differentiableAt_id.const_mul 2
    have hp : DifferentiableAt ℂ (fun z : ℂ => (5:ℂ)^(-(2*z))) s :=
      hlin.neg.const_cpow (Or.inl (by norm_num))
    exact ((((hg.div_const (T:ℂ)).const_mul 2).add (hc.const_mul 2)).sub (ht.comp s hlin) |>.sub hp).differentiableWithinAt
  apply pole_obstruction (DirichletCharacter.LFunction char5) F (DirichletCharacter.differentiable_LFunction char5_ne_one) hF
  intro z hz
  let s := z/2
  have hz' : 2*s = z := by dsimp [s]; ring
  have hs : 1 < s.re := by dsimp only [s]; rw [Complex.div_ofNat_re]; linarith
  have hh : 0 < s.re := by linarith
  have hs1 : 1 < s.re * (1:ℕ) := by simpa using hs
  have hs2 : 1 < s.re * (2:ℕ) := by norm_num; linarith
  have hz1 : 1 < (2*s).re * (1:ℕ) := by simp only [hz', Nat.cast_one, mul_one]; linarith
  have hc := square_sum s hs
  have ht : G s / (T:ℂ) = degreeSum char5 1 s := by
    rw [hd s hs, mul_div_cancel_left₀ _ (by exact_mod_cast hT.ne' : (T:ℂ) ≠ 0)]
  change DirichletCharacter.LFunction char5 s ^ 2 = riemannZeta z * Complex.exp (F s)
  rw [← hz', ← exp_tail_one char5 hs, ← exp_tail_zeta (by rw [hz']; linarith),
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  dsimp only [F]
  rw [tail_step char5 (by decide : 0<1) hh hs1, tail_step char5 (by decide : 0<2) hh hs2,
    tail_step trivialChar (by decide : 0<1) (by rw [hz']; linarith) hz1, ht]
  norm_num at hc ⊢
  linear_combination hc

private lemma no_period {N T : ℕ} (hT : 0 < T) (h : ∀ n ≥ N, digit (n+T) = digit n) : False := by
  obtain ⟨M,K,_,hb⟩ := prime_discrepancy hT h
  obtain ⟨hg,hd⟩ := discrepancy_series hb
  have hm := cancel_mean _ hg hd
  subst M
  exact final_contradiction hT _ hg (by simpa using hd)

end PrimeDigitPeriod


theorem OMA.solution : type_of% @OMA.S_oeis_a096319.main := by
  rintro ⟨N, T, hT, h⟩
  exact PrimeDigitPeriod.no_period hT h
