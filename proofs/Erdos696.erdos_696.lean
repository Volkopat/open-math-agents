import FormalConjectures.ErdosProblems.«696»

/-!
Elementary, axiom-free proof of Erdos Problem 696 (`Erdos696.erdos_696`).

We show that it is not true that `H(n) / h(n) -> infty` on a set of asymptotic density 1,
by proving that at least 42 percent of integers up to arbitrarily large scales `N = S(L + 1)`
satisfy `H(n) <= 4 * h(n)`:
1. Effective Dirichlet L-series lower bounds via elementary Abel summation, the Euler product,
   and Dirichlet hyperbola splitting yield an explicit lower bound on the sum of `1 / p` over
   primes `p == 1 (mod q)` in bounded intervals.
2. Exact CRT residue counting along a tower `S(k)` produces a set of density at least 43/100
   with `h(n) >= L + 1`.
3. Elementary divisor-chain union bounds along a tower `T(k)` show that at least 99/100 of
   integers up to `T(m)` satisfy `H(n) <= T(0) + m`.
4. Comparing the towers (`S(k) <= T(3 * k)`) bounds the partial density of
   `{n | h(n) > 0 and H(n) / h(n) > 4}` by 58/100 infinitely often, contradicting density 1.
-/

-- Problem: Erdos Problem 696
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/696.lean:78 (declaration Erdos696.erdos_696)
-- Credit: @PrimordialAA (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos696Proof

open Erdos696 Filter Finset Complex

/- ### Part 1: Elementary Abel summation and Dirichlet L-series bounds -/

lemma sum_dirichlet_Ico_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (a : ℕ) : ∑ k ∈ Ico a (a + q), χ k = 0 := by
  have hbij : ∑ k ∈ Ico a (a + q), χ k = ∑ x : ZMod q, χ x := by
    refine Finset.sum_bij (fun k _ => (k : ZMod q)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro k₁ hk₁ k₂ hk₂ hEq
      rw [mem_Ico] at hk₁ hk₂
      have hsub : ((k₁ : ZMod q) - (k₂ : ZMod q)) = 0 := sub_eq_zero.mpr hEq
      have hdvd : (q : ℤ) ∣ (k₁ : ℤ) - (k₂ : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        exact hsub
      obtain ⟨c, hc⟩ := hdvd
      have h1 : - (q : ℤ) < (k₁ : ℤ) - (k₂ : ℤ) := by omega
      have h2 : (k₁ : ℤ) - (k₂ : ℤ) < (q : ℤ) := by omega
      have hc0 : c = 0 := by nlinarith
      rw [hc0, mul_zero] at hc
      omega
    · intro x _
      let r : ℕ := ((x - (a : ZMod q)).val)
      refine ⟨a + r, mem_Ico.mpr ⟨Nat.le_add_right _ _, by
        have hr : r < q := ZMod.val_lt _
        omega⟩, ?_⟩
      simp only [Nat.cast_add, r, ZMod.natCast_zmod_val, add_sub_cancel]
    · intro _ _; rfl
  rw [hbij]
  exact MulChar.sum_eq_zero_of_ne_one hχ

lemma norm_sum_dirichlet_Ico_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (a b : ℕ) : ‖∑ k ∈ Ico a b, χ k‖ ≤ (q : ℝ) := by
  by_cases hab : b ≤ a
  · rw [Ico_eq_empty_of_le hab, sum_empty, norm_zero]
    exact Nat.cast_nonneg q
  push Not at hab
  have hq : 0 < q := NeZero.pos q
  set m := b - a
  have hb : b = a + m := by omega
  rw [hb]
  suffices ∀ t r : ℕ, r < q → ‖∑ k ∈ Ico a (a + (q * t + r)), χ k‖ ≤ (q : ℝ) by
    have hdiv := Nat.div_add_mod m q
    simpa [hdiv] using this (m / q) (m % q) (Nat.mod_lt m hq)
  intro t
  induction t with
  | zero =>
    intro r hr
    simp only [mul_zero, zero_add]
    calc ‖∑ k ∈ Ico a (a + r), χ k‖
        ≤ ∑ k ∈ Ico a (a + r), ‖χ k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Ico a (a + r), (1 : ℝ) := sum_le_sum fun k _ => χ.norm_le_one k
      _ = (r : ℝ) := by simp
      _ ≤ (q : ℝ) := by exact_mod_cast hr.le
  | succ t ih =>
    intro r hr
    have hsplit : Ico a (a + (q * (t + 1) + r)) =
        Ico a (a + (q * t + r)) ∪ Ico (a + (q * t + r)) (a + (q * t + r) + q) := by
      ext k
      simp only [mem_Ico, mem_union]
      have hmul : q * (t + 1) = q * t + q := Nat.mul_succ q t
      omega
    have hdisj : Disjoint (Ico a (a + (q * t + r))) (Ico (a + (q * t + r)) (a + (q * t + r) + q)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      rw [mem_Ico] at hk1 hk2
      omega
    rw [hsplit, sum_union hdisj, sum_dirichlet_Ico_eq_zero hχ, add_zero]
    exact ih r hr

lemma sum_sub_succ_Ico (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ico a b, (g n - g (n + 1)) = g a - g b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

lemma abel_summation_Ico (f : ℕ → ℂ) (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Ico a b, f n * (g n : ℂ) =
      (∑ k ∈ Ico a b, f k) * (g b : ℂ) +
      ∑ n ∈ Ico a b, (∑ k ∈ Ico a (n + 1), f k) * ((g n - g (n + 1) : ℝ) : ℂ) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih, Finset.sum_Ico_succ_top hab,
        Finset.sum_Ico_succ_top hab, Finset.sum_Ico_succ_top hab]
    push_cast
    ring

lemma norm_sum_mul_le_of_antitone {f : ℕ → ℂ} {g : ℕ → ℝ} {a b : ℕ} {B : ℝ}
    (hab : a ≤ b) (_hB : 0 ≤ B)
    (hf : ∀ k ∈ Ico a (b + 1), ‖∑ j ∈ Ico a k, f j‖ ≤ B)
    (hg0 : 0 ≤ g b)
    (hanti : ∀ n ∈ Ico a b, g (n + 1) ≤ g n) :
    ‖∑ n ∈ Ico a b, f n * (g n : ℂ)‖ ≤ B * g a := by
  rw [abel_summation_Ico f g hab]
  have h1 : ‖(∑ k ∈ Ico a b, f k) * (g b : ℂ)‖ ≤ B * g b := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_right (hf b (mem_Ico.mpr ⟨hab, Nat.lt_succ_self b⟩)) hg0
  have h2 : ‖∑ n ∈ Ico a b, (∑ k ∈ Ico a (n + 1), f k) * ((g n - g (n + 1) : ℝ) : ℂ)‖ ≤
      B * (g a - g b) := by
    calc ‖∑ n ∈ Ico a b, (∑ k ∈ Ico a (n + 1), f k) * ((g n - g (n + 1) : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Ico a b, ‖(∑ k ∈ Ico a (n + 1), f k) * ((g n - g (n + 1) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Ico a b, B * (g n - g (n + 1)) := by
          refine sum_le_sum fun n hn => ?_
          have hd : 0 ≤ g n - g (n + 1) := sub_nonneg.mpr (hanti n hn)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd]
          have hn' : n + 1 ∈ Ico a (b + 1) := by
            rw [mem_Ico] at hn ⊢; omega
          exact mul_le_mul_of_nonneg_right (hf (n + 1) hn') hd
      _ = B * ∑ n ∈ Ico a b, (g n - g (n + 1)) := by rw [← mul_sum]
      _ = B * (g a - g b) := by rw [sum_sub_succ_Ico g hab]
  calc ‖(∑ k ∈ Ico a b, f k) * (g b : ℂ) +
        ∑ n ∈ Ico a b, (∑ k ∈ Ico a (n + 1), f k) * ((g n - g (n + 1) : ℝ) : ℂ)‖
      ≤ ‖(∑ k ∈ Ico a b, f k) * (g b : ℂ)‖ +
        ‖∑ n ∈ Ico a b, (∑ k ∈ Ico a (n + 1), f k) * ((g n - g (n + 1) : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ B * g b + B * (g a - g b) := add_le_add h1 h2
    _ = B * g a := by ring

lemma LSeries_eq_lim_Ico {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ico 1 N, χ n * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) atTop (nhds (LSeries (fun n : ℕ => χ n) σ)) := by
  have hsum : LSeriesSummable (fun n : ℕ => χ n) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ (by simpa using hσ)
  have hhas : HasSum (LSeries.term (fun n : ℕ => χ n) (σ : ℂ)) (LSeries (fun n : ℕ => χ n) σ) := hsum.LSeriesHasSum
  have htend := hhas.tendsto_sum_nat
  refine htend.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← Nat.Ico_zero_eq_range, ← Finset.sum_Ico_consecutive (f := LSeries.term (fun n : ℕ => χ n) (σ : ℂ))
    (by omega : 0 ≤ 1) hN]
  have h0 : ∑ x ∈ Ico 0 1, LSeries.term (fun n : ℕ => χ n) (σ : ℂ) x = 0 := by
    simp [LSeries.term]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by rw [mem_Ico] at hn; omega
  rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg,
    Complex.ofReal_cpow (Nat.cast_nonneg n)]

lemma norm_LSeries_nontriv_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {eps : ℝ} (heps : 0 < eps) : ‖LSeries (fun n : ℕ => χ n) ((1 + eps : ℝ) : ℂ)‖ ≤ (q : ℝ) := by
  have hσ : 1 < 1 + eps := by linarith
  have htend := (LSeries_eq_lim_Ico χ hσ).norm
  refine le_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound := norm_sum_mul_le_of_antitone (f := fun n => χ n)
    (g := fun n => (n : ℝ) ^ (-(1 + eps))) (a := 1) (b := N) (B := q)
    hN (Nat.cast_nonneg q)
    (fun k _ => norm_sum_dirichlet_Ico_le hχ 1 k)
    (by positivity)
    (fun n hn => by
      have hn1 : (0 : ℝ) < n := by rw [mem_Ico] at hn; exact_mod_cast (by omega : 0 < n)
      exact Real.rpow_le_rpow_of_nonpos hn1 (by exact_mod_cast Nat.le_succ n) (by linarith))
  simpa using hbound

lemma norm_LSeries_nontriv_tail_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {eps : ℝ} (heps : 0 < eps) (Y : ℕ) :
    ‖LSeries (fun n : ℕ => χ n) ((1 + eps : ℝ) : ℂ) - ∑ n ∈ Ico 1 (Y + 1), χ n * (((n : ℝ) ^ (-(1 + eps)) : ℝ) : ℂ)‖ ≤
      (q : ℝ) / (Y + 1 : ℝ) := by
  have hσ : 1 < 1 + eps := by linarith
  have htend := ((LSeries_eq_lim_Ico χ hσ).sub_const
    (∑ n ∈ Ico 1 (Y + 1), χ n * (((n : ℝ) ^ (-(1 + eps)) : ℝ) : ℂ))).norm
  refine le_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop (Y + 1)] with N hN
  have hsub : (∑ n ∈ Ico 1 N, χ n * (((n : ℝ) ^ (-(1 + eps)) : ℝ) : ℂ)) -
      (∑ n ∈ Ico 1 (Y + 1), χ n * (((n : ℝ) ^ (-(1 + eps)) : ℝ) : ℂ)) =
      ∑ n ∈ Ico (Y + 1) N, χ n * (((n : ℝ) ^ (-(1 + eps)) : ℝ) : ℂ) := by
    rw [sub_eq_iff_eq_add', Finset.sum_Ico_consecutive _ (by omega : 1 ≤ Y + 1) hN]
  rw [hsub]
  have hbound := norm_sum_mul_le_of_antitone (f := fun n => χ n)
    (g := fun n => (n : ℝ) ^ (-(1 + eps))) (a := Y + 1) (b := N) (B := q)
    hN (Nat.cast_nonneg q)
    (fun k _ => norm_sum_dirichlet_Ico_le hχ (Y + 1) k)
    (by positivity)
    (fun n hn => by
      have hn1 : (0 : ℝ) < n := by rw [mem_Ico] at hn; exact_mod_cast (by omega : 0 < n)
      exact Real.rpow_le_rpow_of_nonpos hn1 (by exact_mod_cast Nat.le_succ n) (by linarith))
  refine hbound.trans ?_
  rw [div_eq_mul_inv]
  gcongr
  have hY1 : (1 : ℝ) ≤ (Y + 1 : ℕ) := by exact_mod_cast Nat.succ_pos Y
  calc ((Y + 1 : ℕ) : ℝ) ^ (-(1 + eps))
      ≤ ((Y + 1 : ℕ) : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    _ = ((Y + 1 : ℝ))⁻¹ := by rw [Real.rpow_neg_one]; push_cast; rfl

/- Lipschitz bound on L(1+eps, chi) via elementary total variation of n^(-s1) - n^(-s2) -/

lemma rpow_sub_rpow_le_mul_log {a s₁ s₂ : ℝ} (ha : 1 ≤ a) (hs : s₁ ≤ s₂) (hs₁ : 0 ≤ s₁) :
    a ^ (-s₁) - a ^ (-s₂) ≤ Real.log a * (s₂ - s₁) := by
  have ha0 : 0 < a := by linarith
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha
  have h1 : a ^ (-s₁) - a ^ (-s₂) = a ^ (-s₁) * (1 - Real.exp (-(Real.log a * (s₂ - s₁)))) := by
    rw [Real.rpow_def_of_pos ha0, Real.rpow_def_of_pos ha0, mul_sub, mul_one, ← Real.exp_add]
    congr 2; ring
  rw [h1]
  have h2 : 1 - Real.exp (-(Real.log a * (s₂ - s₁))) ≤ Real.log a * (s₂ - s₁) := by
    have := Real.add_one_le_exp (-(Real.log a * (s₂ - s₁)))
    linarith
  have h3 : a ^ (-s₁) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
  have h4 : 0 ≤ 1 - Real.exp (-(Real.log a * (s₂ - s₁))) := by
    rw [sub_nonneg, Real.exp_le_one_iff]
    nlinarith
  nlinarith

lemma log_mul_rpow_antitone {σ : ℝ} (hσ : 1 ≤ σ) :
    AntitoneOn (fun x : ℝ => Real.log x * x ^ (-σ)) (Set.Ici (3 : ℝ)) := by
  have hderiv : ∀ x ∈ interior (Set.Ici (3 : ℝ)),
      HasDerivAt (fun t : ℝ => Real.log t * t ^ (-σ))
        ((1 - σ * Real.log x) * x ^ (-σ - 1)) x := by
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 : 0 < x := by linarith
    have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
    have h2 : HasDerivAt (fun t : ℝ => t ^ (-σ)) ((-σ) * x ^ (-σ - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
    have hmul : HasDerivAt (fun t : ℝ => Real.log t * t ^ (-σ))
        (x⁻¹ * x ^ (-σ) + Real.log x * (-σ * x ^ (-σ - 1))) x := h1.mul h2
    have hpow : x⁻¹ * x ^ (-σ) = x ^ (-σ - 1) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0]; congr 1; ring
    have heq : x⁻¹ * x ^ (-σ) + Real.log x * (-σ * x ^ (-σ - 1)) =
        (1 - σ * Real.log x) * x ^ (-σ - 1) := by rw [hpow]; ring
    rwa [heq] at hmul
  refine antitoneOn_of_deriv_nonpos (convex_Ici 3) ?_ ?_ ?_
  · intro x hx
    have hx0 : x ≠ 0 := by have : 3 ≤ x := hx; linarith
    exact ((Real.continuousAt_log hx0).mul (Real.continuousAt_rpow_const _ _ (Or.inl hx0))).continuousWithinAt
  · intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hderiv x hx).deriv]
    rw [interior_Ici, Set.mem_Ioi] at hx
    have hx0 : 0 < x := by linarith
    have hlog3 : 1 < Real.log 3 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      linarith [Real.exp_one_lt_d9]
    have hlogx : 1 < Real.log x := hlog3.trans (Real.log_lt_log (by norm_num) hx)
    have hneg : 1 - σ * Real.log x ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hneg (Real.rpow_nonneg hx0.le _)

lemma rpow_step_antitone {n : ℕ} (hn : 3 ≤ n) :
    AntitoneOn (fun σ : ℝ => (n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ)) (Set.Ici (1 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn10 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hderiv : ∀ σ ∈ interior (Set.Ici (1 : ℝ)),
      HasDerivAt (fun s : ℝ => (n : ℝ) ^ (-s) - ((n + 1 : ℕ) : ℝ) ^ (-s))
        (Real.log (n + 1 : ℕ) * ((n + 1 : ℕ) : ℝ) ^ (-σ) - Real.log n * (n : ℝ) ^ (-σ)) σ := by
    intro σ _
    have h1 : HasDerivAt (fun s : ℝ => (n : ℝ) ^ (-s))
        (Real.log n * (-1) * (n : ℝ) ^ (-σ)) σ :=
      (hasDerivAt_neg σ).const_rpow hn0
    have h2 : HasDerivAt (fun s : ℝ => ((n + 1 : ℕ) : ℝ) ^ (-s))
        (Real.log (n + 1 : ℕ) * (-1) * ((n + 1 : ℕ) : ℝ) ^ (-σ)) σ :=
      (hasDerivAt_neg σ).const_rpow hn10
    have hsub := h1.sub h2
    have heq : Real.log n * (-1) * (n : ℝ) ^ (-σ) -
        Real.log (n + 1 : ℕ) * (-1) * ((n + 1 : ℕ) : ℝ) ^ (-σ) =
        Real.log (n + 1 : ℕ) * ((n + 1 : ℕ) : ℝ) ^ (-σ) - Real.log n * (n : ℝ) ^ (-σ) := by ring
    rwa [heq] at hsub
  refine antitoneOn_of_deriv_nonpos (convex_Ici 1) ?_ ?_ ?_
  · intro σ _
    exact (((continuous_const.rpow continuous_neg (fun _ => Or.inl hn0.ne')).sub
      (continuous_const.rpow continuous_neg (fun _ => Or.inl hn10.ne'))).continuousAt).continuousWithinAt
  · intro σ hσ
    exact (hderiv σ hσ).differentiableAt.differentiableWithinAt
  · intro σ hσ
    rw [(hderiv σ hσ).deriv]
    rw [interior_Ici, Set.mem_Ioi] at hσ
    have hanti := log_mul_rpow_antitone hσ.le
    have hle := hanti (show (3 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn)
      (show (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast (by omega : 3 ≤ n + 1))
      (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n)
    linarith

lemma norm_sum_dirichlet_lipschitz {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {s₁ s₂ : ℝ} (hs₁ : 1 ≤ s₁) (hs : s₁ ≤ s₂) (N : ℕ) (hN : 3 ≤ N) :
    ‖∑ n ∈ Ico 1 N, χ n * ((((n : ℝ) ^ (-s₁) - (n : ℝ) ^ (-s₂)) : ℝ) : ℂ)‖ ≤
      8 * (q : ℝ) * (s₂ - s₁) := by
  let g : ℕ → ℝ := fun n => (n : ℝ) ^ (-s₁) - (n : ℝ) ^ (-s₂)
  rw [abel_summation_Ico (fun n => χ n) g (by omega : 1 ≤ N)]
  have hgN : 0 ≤ g N := by
    dsimp [g]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have htermN : ‖(∑ k ∈ Ico 1 N, χ k) * (g N : ℂ)‖ ≤ (q : ℝ) * g N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hgN]
    exact mul_le_mul_of_nonneg_right (norm_sum_dirichlet_Ico_le hχ 1 N) hgN
  have hsum_abs : ∑ n ∈ Ico 1 N, |g n - g (n + 1)| ≤ 6 * (s₂ - s₁) - g N := by
    have hsplit : Ico 1 N = Ico 1 3 ∪ Ico 3 N := by
      ext n; simp only [mem_Ico, mem_union]; omega
    have hdisj : Disjoint (Ico 1 3) (Ico 3 N) := by
      rw [Finset.disjoint_left]; intro n h1 h2; rw [mem_Ico] at h1 h2; omega
    rw [hsplit, sum_union hdisj]
    have htail : ∑ n ∈ Ico 3 N, |g n - g (n + 1)| = g 3 - g N := by
      have hnonneg : ∀ n ∈ Ico 3 N, 0 ≤ g n - g (n + 1) := by
        intro n hn
        rw [mem_Ico] at hn
        have hstep := rpow_step_antitone hn.1 hs₁ (hs₁.trans hs) hs
        dsimp [g]; push_cast at hstep ⊢; linarith
      rw [Finset.sum_congr rfl fun n hn => abs_of_nonneg (hnonneg n hn)]
      exact sum_sub_succ_Ico g hN
    rw [htail]
    have h12 : Ico 1 3 = {1, 2} := by decide
    rw [h12, sum_pair (by decide : (1 : ℕ) ≠ 2)]
    have hg1 : g 1 = 0 := by simp [g]
    have hg2_nonneg : 0 ≤ g 2 := by
      dsimp [g]; exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    have hg3_nonneg : 0 ≤ g 3 := by
      dsimp [g]; exact sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
    have hg2_le : g 2 ≤ Real.log 2 * (s₂ - s₁) :=
      rpow_sub_rpow_le_mul_log (by norm_num) hs (by linarith)
    have hg3_le : g 3 ≤ Real.log 3 * (s₂ - s₁) :=
      rpow_sub_rpow_le_mul_log (by norm_num) hs (by linarith)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have habs1 : |g 1 - g 2| = g 2 := by rw [hg1, zero_sub, abs_neg, abs_of_nonneg hg2_nonneg]
    have habs2 : |g 2 - g 3| ≤ g 2 + g 3 := by
      calc |g 2 - g 3| ≤ |g 2| + |g 3| := abs_sub _ _
        _ = g 2 + g 3 := by rw [abs_of_nonneg hg2_nonneg, abs_of_nonneg hg3_nonneg]
    rw [habs1]
    nlinarith
  have hsum_norm : ‖∑ n ∈ Ico 1 N, (∑ k ∈ Ico 1 (n + 1), χ k) * ((g n - g (n + 1) : ℝ) : ℂ)‖ ≤
      (q : ℝ) * (6 * (s₂ - s₁) - g N) := by
    calc ‖∑ n ∈ Ico 1 N, (∑ k ∈ Ico 1 (n + 1), χ k) * ((g n - g (n + 1) : ℝ) : ℂ)‖
        ≤ ∑ n ∈ Ico 1 N, ‖(∑ k ∈ Ico 1 (n + 1), χ k) * ((g n - g (n + 1) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Ico 1 N, (q : ℝ) * |g n - g (n + 1)| := by
          refine sum_le_sum fun n _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (norm_sum_dirichlet_Ico_le hχ 1 (n + 1)) (abs_nonneg _)
      _ = (q : ℝ) * ∑ n ∈ Ico 1 N, |g n - g (n + 1)| := by rw [← mul_sum]
      _ ≤ (q : ℝ) * (6 * (s₂ - s₁) - g N) := mul_le_mul_of_nonneg_left hsum_abs (Nat.cast_nonneg q)
  calc ‖(∑ k ∈ Ico 1 N, χ k) * (g N : ℂ) +
        ∑ n ∈ Ico 1 N, (∑ k ∈ Ico 1 (n + 1), χ k) * ((g n - g (n + 1) : ℝ) : ℂ)‖
      ≤ ‖(∑ k ∈ Ico 1 N, χ k) * (g N : ℂ)‖ +
        ‖∑ n ∈ Ico 1 N, (∑ k ∈ Ico 1 (n + 1), χ k) * ((g n - g (n + 1) : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ (q : ℝ) * g N + (q : ℝ) * (6 * (s₂ - s₁) - g N) := add_le_add htermN hsum_norm
    _ = 6 * (q : ℝ) * (s₂ - s₁) := by ring
    _ ≤ 8 * (q : ℝ) * (s₂ - s₁) := by
        have : 0 ≤ (q : ℝ) * (s₂ - s₁) := mul_nonneg (Nat.cast_nonneg q) (sub_nonneg.mpr hs)
        linarith

lemma norm_LSeries_nontriv_lipschitz {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) :
    ‖LSeries (fun n : ℕ => χ n) ((1 + d₁ : ℝ) : ℂ) - LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ ≤ 8 * (q : ℝ) * (d₂ - d₁) := by
  have htend := ((LSeries_eq_lim_Ico χ (by linarith : 1 < 1 + d₁)).sub
    (LSeries_eq_lim_Ico χ (by linarith : 1 < 1 + d₂))).norm
  refine le_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hsub : (∑ n ∈ Ico 1 N, χ n * (((n : ℝ) ^ (-(1 + d₁)) : ℝ) : ℂ)) -
      (∑ n ∈ Ico 1 N, χ n * (((n : ℝ) ^ (-(1 + d₂)) : ℝ) : ℂ)) =
      ∑ n ∈ Ico 1 N, χ n * ((((n : ℝ) ^ (-(1 + d₁)) - (n : ℝ) ^ (-(1 + d₂))) : ℝ) : ℂ) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n _ => ?_
    push_cast; ring
  rw [hsub]
  have h := norm_sum_dirichlet_lipschitz hχ (s₁ := 1 + d₁) (s₂ := 1 + d₂)
    (by linarith) (by linarith) N hN
  simpa [show (1 + d₂) - (1 + d₁) = d₂ - d₁ by ring] using h

/- Bounds on L(1+d, 1) and tail of ∑ n^(-(1+d)) -/

lemma rpow_step_lower {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd : 0 < d) :
    d * b ^ (-(1 + d)) * (b - a) ≤ a ^ (-d) - b ^ (-d) := by
  by_cases heq : a = b
  · subst heq; simp
  have hlt : a < b := lt_of_le_of_ne hab heq
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-d)) (Set.Icc a b) :=
    fun t ht => (Real.continuousAt_rpow_const t (-d) (Or.inl (by linarith [ht.1]))).continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun x : ℝ => x ^ (-d)) ((-d) * t ^ (-d - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-d))
    (fun t => (-d) * t ^ (-d - 1)) hlt hcont hderiv
  have hcb : c ≤ b := hc.2.le
  have hc0 : 0 < c := by linarith [hc.1]
  have hmon : b ^ (-(1 + d)) ≤ c ^ (-(1 + d)) :=
    Real.rpow_le_rpow_of_nonpos hc0 hcb (by linarith)
  have hpow : c ^ (-d - 1) = c ^ (-(1 + d)) := by congr 1; ring
  have hslope : (b ^ (-d) - a ^ (-d)) = ((-d) * c ^ (-(1 + d))) * (b - a) := by
    rw [← hpow, hmv, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
  have hba : 0 ≤ b - a := by linarith
  have hmul : d * b ^ (-(1 + d)) * (b - a) ≤ d * c ^ (-(1 + d)) * (b - a) := by
    gcongr
  linarith

lemma rpow_step_upper {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hd : 0 < d) :
    a ^ (-d) - b ^ (-d) ≤ d * a ^ (-(1 + d)) * (b - a) := by
  by_cases heq : a = b
  · subst heq; simp
  have hlt : a < b := lt_of_le_of_ne hab heq
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-d)) (Set.Icc a b) :=
    fun t ht => (Real.continuousAt_rpow_const t (-d) (Or.inl (by linarith [ht.1]))).continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun x : ℝ => x ^ (-d)) ((-d) * t ^ (-d - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  obtain ⟨c, hc, hmv⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-d))
    (fun t => (-d) * t ^ (-d - 1)) hlt hcont hderiv
  have hac : a ≤ c := hc.1.le
  have hmon : c ^ (-(1 + d)) ≤ a ^ (-(1 + d)) :=
    Real.rpow_le_rpow_of_nonpos ha hac (by linarith)
  have hpow : c ^ (-d - 1) = c ^ (-(1 + d)) := by congr 1; ring
  have hslope : (b ^ (-d) - a ^ (-d)) = ((-d) * c ^ (-(1 + d))) * (b - a) := by
    rw [← hpow, hmv, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
  have hba : 0 ≤ b - a := by linarith
  have hmul : d * c ^ (-(1 + d)) * (b - a) ≤ d * a ^ (-(1 + d)) * (b - a) := by
    gcongr
  linarith

lemma sum_rpow_Ico_le {M N : ℕ} (hM : 1 ≤ M) (hMN : M + 1 ≤ N) {d : ℝ} (hd : 0 < d) :
    ∑ n ∈ Ico (M + 1) N, (n : ℝ) ^ (-(1 + d)) ≤ (M : ℝ) ^ (-d) / d := by
  have hterm : ∀ n ∈ Ico (M + 1) N,
      (n : ℝ) ^ (-(1 + d)) ≤ (((n - 1 : ℕ) : ℝ) ^ (-d) - (n : ℝ) ^ (-d)) / d := by
    intro n hn
    rw [mem_Ico] at hn
    have ha : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
    have hdiff : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
      have : n = (n - 1) + 1 := by omega
      conv_lhs => rw [this]
      push_cast; ring
    have hlow := rpow_step_lower ha (show ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast (by omega : n - 1 ≤ n)) hd
    rw [hdiff, mul_one] at hlow
    exact (le_div_iff₀ hd).mpr (by linarith)
  calc ∑ n ∈ Ico (M + 1) N, (n : ℝ) ^ (-(1 + d))
      ≤ ∑ n ∈ Ico (M + 1) N, (((n - 1 : ℕ) : ℝ) ^ (-d) - (n : ℝ) ^ (-d)) / d :=
        sum_le_sum hterm
    _ = (∑ n ∈ Ico (M + 1) N, (((n - 1 : ℕ) : ℝ) ^ (-d) - (n : ℝ) ^ (-d))) / d := by
        rw [← sum_div]
    _ = ((M : ℝ) ^ (-d) - ((N - 1 : ℕ) : ℝ) ^ (-d)) / d := by
        congr 1
        have hshift : ∑ n ∈ Ico (M + 1) N, (((n - 1 : ℕ) : ℝ) ^ (-d) - (n : ℝ) ^ (-d)) =
            ∑ k ∈ Ico M (N - 1), ((k : ℝ) ^ (-d) - ((k + 1 : ℕ) : ℝ) ^ (-d)) := by
          refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
          · intro n hn; rw [mem_Ico] at hn ⊢; omega
          · intro n₁ hn₁ n₂ hn₂ h; rw [mem_Ico] at hn₁ hn₂; omega
          · intro k hk; rw [mem_Ico] at hk; exact ⟨k + 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro n hn
            rw [mem_Ico] at hn
            have hn1 : (n - 1) + 1 = n := by omega
            simp only [hn1]
        rw [hshift, sum_sub_succ_Ico (fun k => (k : ℝ) ^ (-d)) (by omega)]
    _ ≤ (M : ℝ) ^ (-d) / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        have : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) ^ (-d) := by positivity
        linarith

lemma sum_rpow_Ico_ge {N : ℕ} (hN : 1 ≤ N) {d : ℝ} (hd : 0 < d) :
    (1 - (N : ℝ) ^ (-d)) / d ≤ ∑ n ∈ Ico 1 N, (n : ℝ) ^ (-(1 + d)) := by
  have hterm : ∀ n ∈ Ico 1 N,
      ((n : ℝ) ^ (-d) - ((n + 1 : ℕ) : ℝ) ^ (-d)) / d ≤ (n : ℝ) ^ (-(1 + d)) := by
    intro n hn
    rw [mem_Ico] at hn
    have ha : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hdiff : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
    have hup := rpow_step_upper ha (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ n) hd
    rw [hdiff, mul_one] at hup
    exact (div_le_iff₀ hd).mpr (by linarith)
  calc (1 - (N : ℝ) ^ (-d)) / d
      = (∑ n ∈ Ico 1 N, ((n : ℝ) ^ (-d) - ((n + 1 : ℕ) : ℝ) ^ (-d))) / d := by
        rw [sum_sub_succ_Ico (fun k => (k : ℝ) ^ (-d)) hN]; simp
    _ = ∑ n ∈ Ico 1 N, ((n : ℝ) ^ (-d) - ((n + 1 : ℕ) : ℝ) ^ (-d)) / d := by rw [sum_div]
    _ ≤ ∑ n ∈ Ico 1 N, (n : ℝ) ^ (-(1 + d)) := sum_le_sum hterm

lemma norm_LSeries_one_le {q : ℕ} {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)‖ ≤ 2 / d := by
  have htend := (LSeries_eq_lim_Ico (1 : DirichletCharacter ℂ q) (by linarith : 1 < 1 + d)).norm
  refine le_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  calc ‖∑ n ∈ Ico 1 N, (1 : DirichletCharacter ℂ q) n * (((n : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)‖
      ≤ ∑ n ∈ Ico 1 N, ‖(1 : DirichletCharacter ℂ q) n * (((n : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Ico 1 N, (n : ℝ) ^ (-(1 + d)) := by
        refine sum_le_sum fun n _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left (by positivity) ((1 : DirichletCharacter ℂ q).norm_le_one n)
    _ = (1 : ℝ) ^ (-(1 + d)) + ∑ n ∈ Ico 2 N, (n : ℝ) ^ (-(1 + d)) := by
        rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ 2) hN]
        have : Ico 1 2 = {1} := by decide
        rw [this, sum_singleton]; norm_num
    _ ≤ 1 + (1 : ℝ) ^ (-d) / d := by
        simp only [Real.one_rpow, add_le_add_iff_left]
        simpa using sum_rpow_Ico_le (M := 1) (N := N) le_rfl hN hd
    _ ≤ 2 / d := by
        rw [Real.one_rpow]
        have : 1 ≤ 1 / d := (one_le_div hd).mpr hd1
        linarith [show 1 / d + 1 / d = 2 / d by ring]

lemma norm_LSeries_one_ge {q : ℕ} (hq : q.Prime) {d : ℝ} (hd : 0 < d) :
    1 / (2 * d) ≤ ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)‖ := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hre : 1 / (2 * d) ≤ (LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)).re := by
    have htend : Tendsto (fun N : ℕ =>
        (∑ n ∈ Ico 1 N, (1 : DirichletCharacter ℂ q) n * (((n : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)).re)
        atTop (nhds (LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp
        (LSeries_eq_lim_Ico (1 : DirichletCharacter ℂ q) (by linarith))
    have htend_rhs : Tendsto (fun N : ℕ => (1 - (1 : ℝ) / q) * ((1 - (N : ℝ) ^ (-d)) / d))
        atTop (nhds ((1 - (1 : ℝ) / q) * ((1 - 0) / d))) := by
      have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-d)) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
      exact ((tendsto_const_nhds.sub h0).div_const d).const_mul _
    have hle : (1 - (1 : ℝ) / q) * ((1 - 0) / d) ≤
        (LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)).re := by
      refine le_of_tendsto_of_tendsto htend_rhs htend ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hsum_re : (∑ n ∈ Ico 1 N, (1 : DirichletCharacter ℂ q) n *
          (((n : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)).re =
          ∑ n ∈ (Ico 1 N).filter (fun n => ¬ q ∣ n), (n : ℝ) ^ (-(1 + d)) := by
        rw [Complex.re_sum, Finset.sum_filter]
        refine sum_congr rfl fun n _ => ?_
        by_cases hdiv : q ∣ n
        · have hnu : ¬ IsUnit (n : ZMod q) := by
            rw [ZMod.isUnit_iff_coprime]
            intro hc
            have hdvd := Nat.dvd_gcd hdiv (dvd_refl q)
            rw [hc.gcd_eq_one] at hdvd
            exact hq.not_dvd_one hdvd
          simp [hdiv, MulChar.map_nonunit _ hnu]
        · have hu : IsUnit (n : ZMod q) := by
            rw [ZMod.isUnit_iff_coprime]
            exact (hq.coprime_iff_not_dvd.mpr hdiv).symm
          simp [hdiv, MulChar.one_apply hu]
      rw [hsum_re]
      have hpart' : ∑ n ∈ Ico 1 N, (n : ℝ) ^ (-(1 + d)) =
          ∑ n ∈ (Ico 1 N).filter (fun n => q ∣ n), (n : ℝ) ^ (-(1 + d)) +
          ∑ n ∈ (Ico 1 N).filter (fun n => ¬ q ∣ n), (n : ℝ) ^ (-(1 + d)) :=
        (Finset.sum_filter_add_sum_filter_not (Ico 1 N) (fun n => q ∣ n) _).symm
      have hmult : ∑ n ∈ (Ico 1 N).filter (fun n => q ∣ n), (n : ℝ) ^ (-(1 + d)) ≤
          ((1 : ℝ) / q) * ∑ n ∈ Ico 1 N, (n : ℝ) ^ (-(1 + d)) := by
        have hbij : ∑ n ∈ (Ico 1 N).filter (fun n => q ∣ n), (n : ℝ) ^ (-(1 + d)) =
            ∑ m ∈ Ico 1 ((N + q - 1) / q), ((q * m : ℕ) : ℝ) ^ (-(1 + d)) := by
          refine Finset.sum_bij (fun n _ => n / q) ?_ ?_ ?_ ?_
          · intro n hn
            rw [mem_filter, mem_Ico] at hn
            obtain ⟨k, rfl⟩ := hn.2
            have hq0 : 0 < q := hq.pos
            have hk0 : 1 ≤ k := by
              by_contra hk; push Not at hk
              have : k = 0 := by omega
              subst this; simp at hn
            rw [Nat.mul_div_cancel_left k hq0, mem_Ico]
            refine ⟨hk0, ?_⟩
            have h1 : (k + 1) * q ≤ N + q - 1 := by
              have : q * k < N := hn.1.2
              have : (k + 1) * q = q * k + q := by ring
              omega
            have h2 := Nat.div_le_div_right (c := q) h1
            rw [Nat.mul_div_cancel (k + 1) hq0] at h2
            omega
          · intro n₁ hn₁ n₂ hn₂ hEq
            rw [mem_filter] at hn₁ hn₂
            rw [← Nat.mul_div_cancel' hn₁.2, ← Nat.mul_div_cancel' hn₂.2, hEq]
          · intro m hm
            rw [mem_Ico] at hm
            have hq0 : 0 < q := hq.pos
            have hlt : q * m < N := by
              have h1 : m * q + q ≤ N + q - 1 := by
                have := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hm.2)
                have := Nat.div_mul_le_self (N + q - 1) q
                nlinarith
              have hcomm : m * q = q * m := mul_comm m q
              omega
            refine ⟨q * m, mem_filter.mpr ⟨mem_Ico.mpr ⟨by nlinarith [hq.two_le], hlt⟩, dvd_mul_right q m⟩,
              Nat.mul_div_cancel_left m hq0⟩
          · intro n hn
            rw [mem_filter] at hn
            rw [Nat.mul_div_cancel' hn.2]
        rw [hbij]
        have hsub : Ico 1 ((N + q - 1) / q) ⊆ Ico 1 N := by
          intro m hm; rw [mem_Ico] at hm ⊢
          refine ⟨hm.1, ?_⟩
          have hq2 : 2 ≤ q := hq.two_le
          have h1 : (N + q - 1) / q ≤ N := by
            rw [Nat.div_le_iff_le_mul_add_pred hq.pos]
            have : N ≤ q * N := Nat.le_mul_of_pos_left N hq.pos
            omega
          omega
        calc ∑ m ∈ Ico 1 ((N + q - 1) / q), ((q * m : ℕ) : ℝ) ^ (-(1 + d))
            = (q : ℝ) ^ (-(1 + d)) * ∑ m ∈ Ico 1 ((N + q - 1) / q), (m : ℝ) ^ (-(1 + d)) := by
              rw [mul_sum]
              refine sum_congr rfl fun m _ => ?_
              rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg m)]
          _ ≤ ((1 : ℝ) / q) * ∑ m ∈ Ico 1 N, (m : ℝ) ^ (-(1 + d)) := by
              have hqpow : (q : ℝ) ^ (-(1 + d)) ≤ (1 : ℝ) / q := by
                rw [one_div, ← Real.rpow_neg_one]
                exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq.one_lt.le) (by linarith)
              have hsum_le : ∑ m ∈ Ico 1 ((N + q - 1) / q), (m : ℝ) ^ (-(1 + d)) ≤
                  ∑ m ∈ Ico 1 N, (m : ℝ) ^ (-(1 + d)) :=
                sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
              exact mul_le_mul hqpow hsum_le (sum_nonneg fun _ _ => by positivity) (by positivity)
      have hge := sum_rpow_Ico_ge hN hd
      have h1q : 0 ≤ 1 - (1 : ℝ) / q := by
        have : (1 : ℝ) / q ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hq.one_lt.le) (by positivity)
        linarith
      nlinarith
    have h1q : (1 : ℝ) / 2 ≤ 1 - (1 : ℝ) / q := by
      have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
      have : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq2
      linarith
    calc 1 / (2 * d) = (1 / 2) * (1 / d) := by ring
      _ ≤ (1 - (1 : ℝ) / q) * ((1 - 0) / d) := by
          rw [sub_zero]; exact mul_le_mul_of_nonneg_right h1q (by positivity)
      _ ≤ (LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)).re := hle
  exact hre.trans (Complex.re_le_norm _)

/- Complex character lower bound via Mathlib's 3-4-1 inequality -/

lemma norm_LSeries_complex_ge {q : ℕ} (hq : q.Prime) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hsq : χ ^ 2 ≠ 1) {d : ℝ} (hd : 0 < d) (hd_le : d ≤ Real.exp (-100 * (q : ℝ))) :
    Real.exp (-25 * (q : ℝ)) ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  set u : ℝ := 1 / (32 * (q : ℝ) ^ 2)
  set d₂ : ℝ := u ^ 4
  have hu_pos : 0 < u := by positivity
  have hd₂_pos : 0 < d₂ := by positivity
  have hd₂_le1 : d₂ ≤ 1 := by
    have hu1 : u ≤ 1 := by
      dsimp [u]; rw [div_le_one (by positivity)]; nlinarith
    exact pow_le_one₀ hu_pos.le hu1
  have hd_le_d₂ : d ≤ d₂ := by
    refine hd_le.trans ?_
    have h32 : (32 * (q : ℝ) ^ 2) ^ 4 ≤ Real.exp (100 * (q : ℝ)) := by
      have hexp : (25 * (q : ℝ)) ^ 3 / 6 ≤ Real.exp (25 * (q : ℝ)) := by
        have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 25 * (q : ℝ)) 4
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
          pow_zero, Nat.factorial, Nat.cast_one, div_one, pow_one, Nat.cast_mul] at h
        have hpos1 : (0 : ℝ) ≤ 1 + 25 * (q : ℝ) + (25 * (q : ℝ)) ^ 2 / 2 := by positivity
        linarith
      have hpow : 32 * (q : ℝ) ^ 2 ≤ Real.exp (25 * (q : ℝ)) := by
        have : 32 * (q : ℝ) ^ 2 ≤ (25 * (q : ℝ)) ^ 3 / 6 := by nlinarith [sq_nonneg ((q : ℝ) - 2)]
        linarith
      calc (32 * (q : ℝ) ^ 2) ^ 4
          ≤ (Real.exp (25 * (q : ℝ))) ^ 4 := pow_le_pow_left₀ (by positivity) hpow 4
        _ = Real.exp (4 * (25 * (q : ℝ))) := by rw [← Real.exp_nat_mul]; norm_num
        _ = Real.exp (100 * (q : ℝ)) := by ring_nf
    rw [show (-100 * (q : ℝ)) = -(100 * (q : ℝ)) by ring, Real.exp_neg]
    dsimp [d₂, u]
    rw [one_div, inv_pow, inv_le_inv₀ (by positivity) (by positivity)]
    exact h32
  have h341 := DirichletCharacter.norm_LSeries_product_ge_one χ hd₂_pos 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at h341
  have hcast : (1 + (d₂ : ℂ)) = ((1 + d₂ : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast] at h341
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at h341
  have hL1 : ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d₂ : ℝ) : ℂ)‖ ≤ 2 / d₂ :=
    norm_LSeries_one_le hd₂_pos hd₂_le1
  have hL2 : ‖LSeries (fun n : ℕ => (χ ^ 2) n) ((1 + d₂ : ℝ) : ℂ)‖ ≤ q := norm_LSeries_nontriv_le hsq hd₂_pos
  have hLχ_pow : (u ^ 3 / (2 * (q : ℝ))) ^ 4 ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ ^ 4 := by
    have hprod_le : ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d₂ : ℝ) : ℂ)‖ ^ 3 *
        ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ ^ 4 * ‖LSeries (fun n : ℕ => (χ ^ 2) n) ((1 + d₂ : ℝ) : ℂ)‖ ≤
        (2 / d₂) ^ 3 * ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ ^ 4 * q := by
      gcongr
    have h1 : 1 ≤ (2 / d₂) ^ 3 * ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ ^ 4 * q := h341.le.trans hprod_le
    have hden : 0 < (2 / d₂) ^ 3 * q := by positivity
    have h2 : 1 / ((2 / d₂) ^ 3 * q) ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ ^ 4 := by
      rw [div_le_iff₀ hden]; linarith
    refine le_trans ?_ h2
    have hq_cube : 8 * (q : ℝ) ≤ 16 * (q : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    have hident : (u ^ 3 / (2 * (q : ℝ))) ^ 4 = d₂ ^ 3 / (16 * (q : ℝ) ^ 4) := by
      dsimp [d₂]; ring
    rw [hident, div_le_div_iff₀ (by positivity) hden]
    have hcancel : (2 / d₂) ^ 3 * q * d₂ ^ 3 = 8 * (q : ℝ) := by
      have h8 : (2 / d₂) ^ 3 * d₂ ^ 3 = 8 := by field_simp [hd₂_pos.ne']; norm_num
      rw [show (2 / d₂) ^ 3 * (q : ℝ) * d₂ ^ 3 = ((2 / d₂) ^ 3 * d₂ ^ 3) * (q : ℝ) by ring, h8]
    nlinarith
  have hLχ_d₂ : u ^ 3 / (2 * (q : ℝ)) ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ := by
    by_contra hlt; push Not at hlt
    have := pow_lt_pow_left₀ hlt (norm_nonneg _) (by decide : 4 ≠ 0)
    linarith
  have hlip := norm_LSeries_nontriv_lipschitz hχ hd hd_le_d₂
  have htri : ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ - ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ ≤ 8 * (q : ℝ) * (d₂ - d) := by
    calc ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ - ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖
        ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ) - LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := norm_sub_norm_le _ _
      _ = ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ) - LSeries (fun n : ℕ => χ n) ((1 + d₂ : ℝ) : ℂ)‖ := norm_sub_rev _ _
      _ ≤ 8 * (q : ℝ) * (d₂ - d) := hlip
  have hlower : u ^ 3 / (4 * (q : ℝ)) ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
    have h8 : 8 * (q : ℝ) * d₂ = u ^ 3 / (4 * (q : ℝ)) := by
      dsimp [d₂, u]; field_simp [hq.ne_zero]; ring
    have hpos : 0 ≤ 8 * (q : ℝ) * d := by positivity
    have hhalf : u ^ 3 / (2 * (q : ℝ)) - u ^ 3 / (4 * (q : ℝ)) = u ^ 3 / (4 * (q : ℝ)) := by ring
    linarith
  refine le_trans ?_ hlower
  have hbig : 4 * (32 * (q : ℝ) ^ 2) ^ 3 * (q : ℝ) ≤ Real.exp (25 * (q : ℝ)) := by
    have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 25 * (q : ℝ)) 8
    have hterm7 : (25 * (q : ℝ)) ^ 7 / (Nat.factorial 7 : ℝ) ≤
        ∑ i ∈ Finset.range 8, (25 * (q : ℝ)) ^ i / (Nat.factorial i : ℝ) :=
      Finset.single_le_sum (f := fun i : ℕ => (25 * (q : ℝ)) ^ i / (Nat.factorial i : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by decide))
    have h7 : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
    rw [h7] at hterm7
    have hq7 : 4 * (32 * (q : ℝ) ^ 2) ^ 3 * (q : ℝ) ≤ (25 * (q : ℝ)) ^ 7 / 5040 := by
      have heq1 : 4 * (32 * (q : ℝ) ^ 2) ^ 3 * (q : ℝ) = 131072 * (q : ℝ) ^ 7 := by ring
      have heq2 : (25 * (q : ℝ)) ^ 7 / 5040 = (25 ^ 7 / 5040 : ℝ) * (q : ℝ) ^ 7 := by ring
      have hcoef : (131072 : ℝ) ≤ 25 ^ 7 / 5040 := by norm_num
      rw [heq1, heq2]
      exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by linarith : (0 : ℝ) ≤ q) 7)
    linarith
  rw [show (-25 * (q : ℝ)) = -(25 * (q : ℝ)) by ring, Real.exp_neg]
  have hu3 : u ^ 3 / (4 * (q : ℝ)) = (4 * (32 * (q : ℝ) ^ 2) ^ 3 * (q : ℝ))⁻¹ := by
    dsimp [u]; field_simp [hq.ne_zero]
  rw [hu3]
  exact inv_anti₀ (by positivity) hbig

/- Quadratic character lower bound via elementary Dirichlet hyperbola method -/

lemma sum_sqrt_sub_pred (M : ℕ) :
    ∑ k ∈ Icc 1 M, (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) = Real.sqrt M := by
  induction M with
  | zero => simp
  | succ m ih =>
    have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert (by simp), ih]
    simp only [Nat.add_sub_cancel]; ring

lemma inv_sqrt_step_bounds {k : ℕ} (hk : 2 ≤ k) :
    0 ≤ 2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - 1 / Real.sqrt k ∧
    2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - 1 / Real.sqrt k ≤
      1 / Real.sqrt (k - 1 : ℕ) - 1 / Real.sqrt k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
  have hsk1 : 0 < Real.sqrt (k - 1 : ℕ) := Real.sqrt_pos.mpr hk1
  have hdiff_sq : (Real.sqrt k) ^ 2 - (Real.sqrt (k - 1 : ℕ)) ^ 2 = 1 := by
    rw [Real.sq_sqrt hk0.le, Real.sq_sqrt hk1.le]
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this]
    push_cast; ring
  have hle : Real.sqrt (k - 1 : ℕ) ≤ Real.sqrt k :=
    Real.sqrt_le_sqrt (by exact_mod_cast (by omega : k - 1 ≤ k))
  have hdiff_eq : Real.sqrt k - Real.sqrt (k - 1 : ℕ) =
      1 / (Real.sqrt k + Real.sqrt (k - 1 : ℕ)) := by
    rw [eq_div_iff (by positivity)]
    linarith [show (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) * (Real.sqrt k + Real.sqrt (k - 1 : ℕ)) =
      (Real.sqrt k) ^ 2 - (Real.sqrt (k - 1 : ℕ)) ^ 2 by ring]
  constructor
  · rw [hdiff_eq, sub_nonneg, mul_one_div, div_le_div_iff₀ hsk (by positivity)]
    nlinarith
  · rw [hdiff_eq]
    have h1 : 2 * (1 / (Real.sqrt k + Real.sqrt (k - 1 : ℕ))) ≤ 1 / Real.sqrt (k - 1 : ℕ) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hsk1]
      linarith
    linarith

lemma inv_sqrt_sum_le (M : ℕ) :
    ∑ e ∈ Icc 1 M, 1 / Real.sqrt e ≤ 2 * Real.sqrt M := by
  have hstep : ∀ e ∈ Icc 1 M, 1 / Real.sqrt e ≤ 2 * (Real.sqrt e - Real.sqrt (e - 1 : ℕ)) := by
    intro e he
    rw [mem_Icc] at he
    by_cases he1 : e = 1
    · subst he1; norm_num
    have := (inv_sqrt_step_bounds (by omega : 2 ≤ e)).1
    linarith
  calc ∑ e ∈ Icc 1 M, 1 / Real.sqrt e
      ≤ ∑ e ∈ Icc 1 M, 2 * (Real.sqrt e - Real.sqrt (e - 1 : ℕ)) := sum_le_sum hstep
    _ = 2 * ∑ e ∈ Icc 1 M, (Real.sqrt e - Real.sqrt (e - 1 : ℕ)) := by rw [← mul_sum]
    _ = 2 * Real.sqrt M := by rw [sum_sqrt_sub_pred]

lemma inv_sqrt_sum_asymp :
    ∃ c₀ : ℝ, |c₀| ≤ 2 ∧ ∀ M : ℕ, 1 ≤ M →
      0 ≤ (∑ e ∈ Icc 1 M, 1 / Real.sqrt e) - 2 * Real.sqrt M - c₀ ∧
      (∑ e ∈ Icc 1 M, 1 / Real.sqrt e) - 2 * Real.sqrt M - c₀ ≤ 1 / Real.sqrt M := by
  let v : ℕ → ℝ := fun k =>
    if k = 0 then 0 else 2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - 1 / Real.sqrt k
  have hv_nonneg : ∀ k, 0 ≤ v k := by
    intro k
    by_cases hk0 : k = 0
    · simp [v, hk0]
    by_cases hk1 : k = 1
    · subst hk1; norm_num [v]
    simpa [v, hk0] using (inv_sqrt_step_bounds (by omega : 2 ≤ k)).1
  have hv_le : ∀ k, 2 ≤ k → v k ≤ 1 / Real.sqrt (k - 1 : ℕ) - 1 / Real.sqrt k := by
    intro k hk2
    have hk0 : k ≠ 0 := by omega
    simpa [v, hk0] using (inv_sqrt_step_bounds hk2).2
  have hpart_le : ∀ N : ℕ, ∑ k ∈ Finset.range N, v k ≤ 2 := by
    intro N
    by_cases hN2 : N ≤ 2
    · interval_cases N
      · simp
      · simp [v]
      · simp [Finset.sum_range_succ, v]
    push Not at hN2
    rw [← Nat.Ico_zero_eq_range, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ 2) hN2.le]
    have h02 : ∑ k ∈ Ico 0 2, v k = 1 := by
      have : Ico 0 2 = {0, 1} := by decide
      rw [this, sum_pair (by decide : (0 : ℕ) ≠ 1)]
      simp only [v, ↓reduceIte, one_ne_zero, Nat.cast_one, Real.sqrt_one, Nat.sub_self,
        Nat.cast_zero, Real.sqrt_zero, sub_zero, mul_one, div_one, zero_add]
      norm_num
    rw [h02]
    have htail : ∑ k ∈ Ico 2 N, v k ≤ 1 := by
      calc ∑ k ∈ Ico 2 N, v k
          ≤ ∑ k ∈ Ico 2 N, (1 / Real.sqrt (k - 1 : ℕ) - 1 / Real.sqrt k) :=
            sum_le_sum fun k hk => hv_le k (mem_Ico.mp hk).1
        _ = ∑ j ∈ Ico 1 (N - 1), (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ)) := by
            refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
            · intro k hk; rw [mem_Ico] at hk ⊢; omega
            · intro k₁ hk₁ k₂ hk₂ h; rw [mem_Ico] at hk₁ hk₂; omega
            · intro j hj; rw [mem_Ico] at hj; exact ⟨j + 1, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro k hk
              rw [mem_Ico] at hk
              have hk' : (k - 1) + 1 = k := by omega
              rw [hk']
        _ = 1 / Real.sqrt (1 : ℕ) - 1 / Real.sqrt (N - 1 : ℕ) :=
            sum_sub_succ_Ico (fun j => 1 / Real.sqrt j) (by omega)
        _ ≤ 1 := by
            simp only [Nat.cast_one, Real.sqrt_one, div_one]
            have : 0 ≤ 1 / Real.sqrt (N - 1 : ℕ) := by positivity
            linarith
    linarith
  have hsum_v : Summable v := summable_of_sum_range_le hv_nonneg hpart_le
  refine ⟨-(∑' k, v k), ?_, ?_⟩
  · rw [abs_neg, abs_of_nonneg (tsum_nonneg hv_nonneg)]
    exact hsum_v.tsum_le_of_sum_range_le hpart_le
  · intro M hM
    have htel : ∑ k ∈ Finset.range (M + 1), v k = 2 * Real.sqrt M - ∑ e ∈ Icc 1 M, 1 / Real.sqrt e := by
      have hsplit : Finset.range (M + 1) = {0} ∪ Icc 1 M := by
        ext k; simp only [Finset.mem_range, mem_union, mem_singleton, mem_Icc]; omega
      rw [hsplit, sum_union (by simp), sum_singleton]
      simp only [v, ↓reduceIte, zero_add]
      have hcongr : ∑ k ∈ Icc 1 M, (if k = 0 then (0 : ℝ) else
          2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - 1 / Real.sqrt k) =
          ∑ k ∈ Icc 1 M, (2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - 1 / Real.sqrt k) :=
        sum_congr rfl fun k hk => by
          have hk0 : k ≠ 0 := by rw [mem_Icc] at hk; omega
          simp [hk0]
      rw [hcongr, sum_sub_distrib, ← mul_sum, sum_sqrt_sub_pred]
    have heq : (∑ e ∈ Icc 1 M, 1 / Real.sqrt e) - 2 * Real.sqrt M - -(∑' k, v k) =
        ∑' k, v (k + (M + 1)) := by
      have hsplit := hsum_v.sum_add_tsum_nat_add (M + 1)
      linarith
    rw [heq]
    constructor
    · exact tsum_nonneg fun k => hv_nonneg _
    · have hsum_shift : Summable (fun k => v (k + (M + 1))) :=
        (summable_nat_add_iff (M + 1)).mpr hsum_v
      refine hsum_shift.tsum_le_of_sum_range_le fun N => ?_
      calc ∑ k ∈ Finset.range N, v (k + (M + 1))
          ≤ ∑ k ∈ Finset.range N, (1 / Real.sqrt (k + M : ℕ) - 1 / Real.sqrt (k + M + 1 : ℕ)) := by
            refine sum_le_sum fun k _ => ?_
            have h := hv_le (k + (M + 1)) (by omega)
            have h1 : k + (M + 1) - 1 = k + M := by omega
            have h2 : k + (M + 1) = k + M + 1 := by omega
            simpa [h1, h2] using h
        _ = ∑ j ∈ Ico M (M + N), (1 / Real.sqrt j - 1 / Real.sqrt (j + 1 : ℕ)) := by
            refine Finset.sum_bij (fun k _ => k + M) ?_ ?_ ?_ ?_
            · intro k hk; rw [Finset.mem_range] at hk; rw [mem_Ico]; omega
            · intro k₁ _ k₂ _ h; omega
            · intro j hj; rw [mem_Ico] at hj; exact ⟨j - M, Finset.mem_range.mpr (by omega), by omega⟩
            · intro _ _; rfl
        _ = 1 / Real.sqrt M - 1 / Real.sqrt (M + N : ℕ) :=
            sum_sub_succ_Ico (fun j => 1 / Real.sqrt j) (Nat.le_add_right M N)
        _ ≤ 1 / Real.sqrt M := by
            have : 0 ≤ 1 / Real.sqrt (M + N : ℕ) := by positivity
            linarith

lemma quadratic_zetaMul_re_nonneg {q : ℕ} {χ : DirichletCharacter ℂ q} (hsq : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ (χ.zetaMul n).re := (DirichletCharacter.zetaMul_nonneg hsq n).1

lemma quadratic_zetaMul_prime_even_pow {q : ℕ} {χ : DirichletCharacter ℂ q} (hsq : χ ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    1 ≤ (χ.zetaMul (p ^ (2 * k))).re ∧ (χ.zetaMul (p ^ (2 * k))).im = 0 := by
  have heval : χ.zetaMul (p ^ (2 * k)) = ∑ i ∈ Finset.range (2 * k + 1), (χ p) ^ i := by
    simp only [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply,
      Nat.sum_divisors_prime_pow hp]
    refine sum_congr rfl fun i _ => ?_
    have hne : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
    rw [← DirichletCharacter.apply_eq_toArithmeticFunction_apply χ hne, Nat.cast_pow, map_pow]
  rw [heval]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsq p with h | h | h
  · rw [h]
    constructor
    · rw [Complex.re_sum]
      have h0 : (0 : ℕ) ∈ Finset.range (2 * k + 1) := Finset.mem_range.mpr (by omega)
      calc (1 : ℝ) = ((0 : ℂ) ^ 0).re := by simp
        _ ≤ ∑ i ∈ Finset.range (2 * k + 1), ((0 : ℂ) ^ i).re :=
          Finset.single_le_sum (f := fun i : ℕ => ((0 : ℂ) ^ i).re)
            (fun i _ => by rcases i with _ | i <;> simp) h0
    · rw [Complex.im_sum]
      exact Finset.sum_eq_zero fun i _ => by rcases i with _ | i <;> simp
  · rw [h]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      Complex.natCast_re, Complex.natCast_im]
    exact ⟨by exact_mod_cast (by omega : 1 ≤ 2 * k + 1), trivial⟩
  · rw [h, neg_one_geom_sum]
    have hodd : ¬ Even (2 * k + 1) := by intro ⟨r, hr⟩; omega
    simp [hodd]

lemma quadratic_zetaMul_sq_ge_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hsq : χ ^ 2 = 1)
    {m : ℕ} (hm : 1 ≤ m) : 1 ≤ (χ.zetaMul (m ^ 2)).re := by
  have hm2 : m ^ 2 ≠ 0 := by positivity
  have hfac := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (f := χ.zetaMul) χ.isMultiplicative_zetaMul (n := m ^ 2) hm2
  rw [hfac]
  have hprod_real : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      1 ≤ (∏ p ∈ s, χ.zetaMul (p ^ (m ^ 2).factorization p)).re ∧
      (∏ p ∈ s, χ.zetaMul (p ^ (m ^ 2).factorization p)).im = 0 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp]
      have hp' : p.Prime := hs p (mem_insert_self p s)
      have hih := ih (fun r hr => hs r (mem_insert_of_mem hr))
      have hpow_even : (m ^ 2).factorization p = 2 * m.factorization p := by
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      rw [hpow_even]
      have hpk := quadratic_zetaMul_prime_even_pow hsq hp' (m.factorization p)
      rw [Complex.mul_re, Complex.mul_im, hpk.2, hih.2]
      refine ⟨by nlinarith, by ring⟩
  exact (hprod_real (m ^ 2).primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)).1

lemma hyperbola_split_sum (f : ℕ → ℝ) (X Y : ℕ) :
    ∑ n ∈ Icc 1 X, (∑ d ∈ n.divisors, f d) / Real.sqrt n =
      ∑ d ∈ Icc 1 Y, (f d / Real.sqrt d) * (∑ e ∈ Icc 1 (X / d), 1 / Real.sqrt e) +
      ∑ e ∈ Icc 1 (X / (Y + 1)), (1 / Real.sqrt e) * (∑ d ∈ Icc (Y + 1) (X / e), f d / Real.sqrt d) := by
  let S := (Icc 1 X ×ˢ Icc 1 X).filter (fun p => p.1 * p.2 ≤ X)
  have hL : ∑ n ∈ Icc 1 X, (∑ d ∈ n.divisors, f d) / Real.sqrt n =
      ∑ p ∈ S, f p.1 / (Real.sqrt p.1 * Real.sqrt p.2) := by
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_div _ _ _]
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun x _ => (x.2, x.1 / x.2)) ?_ ?_ ?_ ?_
    · intro ⟨n, d⟩ hx
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨hn1, hnX⟩, hdvd, _⟩ := hx
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdX : d ≤ X := (Nat.le_of_dvd (by omega) hdvd).trans hnX
      have he1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd1
      have heX : n / d ≤ X := (Nat.div_le_self n d).trans hnX
      simp only [S, mem_filter, mem_product, mem_Icc]
      exact ⟨⟨⟨hd1, hdX⟩, ⟨he1, heX⟩⟩, by rw [Nat.mul_div_cancel' hdvd]; exact hnX⟩
    · intro ⟨n₁, d₁⟩ h₁ ⟨n₂, d₂⟩ h₂ hEq
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h₁ h₂
      simp only [Prod.mk.injEq] at hEq
      have hn : n₁ = n₂ := by
        have h1' := Nat.mul_div_cancel' h₁.2.1
        have h2' := Nat.mul_div_cancel' h₂.2.1
        rw [← h1', ← h2', hEq.2, hEq.1]
      exact Sigma.ext hn (heq_of_eq hEq.1)
    · intro ⟨d, e⟩ hp
      simp only [S, mem_filter, mem_product, mem_Icc] at hp
      obtain ⟨⟨⟨hd1, _⟩, ⟨he1, _⟩⟩, hmul⟩ := hp
      refine ⟨⟨d * e, d⟩, ?_, ?_⟩
      · simp only [mem_sigma, mem_Icc, Nat.mem_divisors]
        exact ⟨⟨by nlinarith, hmul⟩, dvd_mul_right d e, by positivity⟩
      · simp [Nat.mul_div_cancel_left e (by omega : 0 < d)]
    · intro ⟨n, d⟩ hx
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at hx
      have hmul : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' hx.2.1).symm
      rw [hmul, Real.sqrt_mul (Nat.cast_nonneg d)]
  rw [hL, ← Finset.sum_filter_add_sum_filter_not S (fun p => p.1 ≤ Y)]
  congr 1
  · have hR1 : ∑ d ∈ Icc 1 Y, (f d / Real.sqrt d) * (∑ e ∈ Icc 1 (X / d), 1 / Real.sqrt e) =
        ∑ x ∈ (Icc 1 Y).sigma (fun d => Icc 1 (X / d)), f x.1 / (Real.sqrt x.1 * Real.sqrt x.2) := by
      calc ∑ d ∈ Icc 1 Y, (f d / Real.sqrt d) * (∑ e ∈ Icc 1 (X / d), 1 / Real.sqrt e)
          = ∑ d ∈ Icc 1 Y, ∑ e ∈ Icc 1 (X / d), f d / (Real.sqrt d * Real.sqrt e) := by
            refine sum_congr rfl fun d _ => ?_
            rw [Finset.mul_sum]; refine sum_congr rfl fun e _ => by ring
        _ = ∑ x ∈ (Icc 1 Y).sigma (fun d => Icc 1 (X / d)), f x.1 / (Real.sqrt x.1 * Real.sqrt x.2) :=
            Finset.sum_sigma' _ _ _
    rw [hR1]
    refine Finset.sum_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_ ?_
    · intro ⟨d, e⟩ hp
      simp only [S, mem_filter, mem_product, mem_Icc] at hp
      simp only [mem_sigma, mem_Icc]
      exact ⟨⟨hp.1.1.1.1, hp.2⟩, ⟨hp.1.1.2.1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [hp.1.2])⟩⟩
    · intro ⟨d₁, e₁⟩ _ ⟨d₂, e₂⟩ _ h; cases h; rfl
    · intro ⟨d, e⟩ hx
      simp only [mem_sigma, mem_Icc] at hx
      have hmul : d * e ≤ X := by
        have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hx.2.2
        linarith
      refine ⟨(d, e), ?_, rfl⟩
      simp only [S, mem_filter, mem_product, mem_Icc]
      exact ⟨⟨⟨⟨hx.1.1, by nlinarith⟩, ⟨hx.2.1, by nlinarith⟩⟩, hmul⟩, hx.1.2⟩
    · intro _ _; rfl
  · have hR2 : ∑ e ∈ Icc 1 (X / (Y + 1)), (1 / Real.sqrt e) * (∑ d ∈ Icc (Y + 1) (X / e), f d / Real.sqrt d) =
        ∑ x ∈ (Icc 1 (X / (Y + 1))).sigma (fun e => Icc (Y + 1) (X / e)), f x.2 / (Real.sqrt x.2 * Real.sqrt x.1) := by
      calc ∑ e ∈ Icc 1 (X / (Y + 1)), (1 / Real.sqrt e) * (∑ d ∈ Icc (Y + 1) (X / e), f d / Real.sqrt d)
          = ∑ e ∈ Icc 1 (X / (Y + 1)), ∑ d ∈ Icc (Y + 1) (X / e), f d / (Real.sqrt d * Real.sqrt e) := by
            refine sum_congr rfl fun e _ => ?_
            rw [Finset.mul_sum]; refine sum_congr rfl fun d _ => by ring
        _ = ∑ x ∈ (Icc 1 (X / (Y + 1))).sigma (fun e => Icc (Y + 1) (X / e)), f x.2 / (Real.sqrt x.2 * Real.sqrt x.1) :=
            Finset.sum_sigma' _ _ _
    rw [hR2]
    refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
    · intro ⟨d, e⟩ hp
      simp only [S, mem_filter, mem_product, mem_Icc] at hp
      simp only [mem_sigma, mem_Icc]
      have hdY : Y + 1 ≤ d := by omega
      have he_le : e ≤ X / (Y + 1) := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < Y + 1)]
        have : e * (Y + 1) ≤ d * e := by nlinarith
        omega
      have hd_le : d ≤ X / e := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < e)]
        linarith [hp.1.2]
      exact ⟨⟨hp.1.1.2.1, he_le⟩, ⟨hdY, hd_le⟩⟩
    · intro ⟨d₁, e₁⟩ _ ⟨d₂, e₂⟩ _ h; cases h; rfl
    · intro ⟨e, d⟩ hx
      simp only [mem_sigma, mem_Icc] at hx
      have hmul : d * e ≤ X := by
        have := (Nat.le_div_iff_mul_le (by omega : 0 < e)).mp hx.2.2
        linarith
      refine ⟨(d, e), ?_, rfl⟩
      simp only [S, mem_filter, mem_product, mem_Icc]
      exact ⟨⟨⟨⟨by omega, by nlinarith⟩, ⟨hx.1.1, by nlinarith⟩⟩, hmul⟩, by omega⟩
    · intro _ _; rfl

lemma sum_inv_ge_log_succ (K : ℕ) : Real.log ((K + 1 : ℕ) : ℝ) ≤ ∑ m ∈ Icc 1 K, (1 : ℝ) / m := by
  induction K with
  | zero => simp
  | succ k ih =>
    have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
      ext m; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert (by simp)]
    have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hstep : Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div (by positivity) hk1.ne']
      have hle := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (k + 2 : ℕ)) hk1)
      have hdiv : ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = 1 / ((k + 1 : ℕ) : ℝ) := by
        field_simp [hk1.ne']; push_cast; ring
      linarith
    linarith

lemma quadratic_hyperbola_S2_le {q X Y : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hX_pos : 0 < X) (hsqrt_le_Y1 : Real.sqrt ((q : ℝ) * (X : ℝ)) ≤ ((Y + 1 : ℕ) : ℝ)) :
    ∑ e ∈ Icc 1 (X / (Y + 1)), (1 / Real.sqrt e) *
      (∑ d ∈ Icc (Y + 1) (X / e), (χ d).re / Real.sqrt d) ≤ 4 * Real.sqrt q := by
  have hinner : ∀ e ∈ Icc 1 (X / (Y + 1)),
      ∑ d ∈ Icc (Y + 1) (X / e), (χ d).re / Real.sqrt d ≤ (q : ℝ) / Real.sqrt (Y + 1 : ℕ) := by
    intro e he
    rw [mem_Icc] at he
    by_cases hle : X / e < Y + 1
    · rw [Icc_eq_empty_of_lt hle, sum_empty]; positivity
    push Not at hle
    have hIcc_eq : Icc (Y + 1) (X / e) = Ico (Y + 1) (X / e + 1) := rfl
    rw [hIcc_eq]
    have hre : ∑ d ∈ Ico (Y + 1) (X / e + 1), (χ d).re / Real.sqrt d =
        (∑ d ∈ Ico (Y + 1) (X / e + 1), χ d * (((1 / Real.sqrt d : ℝ) : ℂ))).re := by
      rw [Complex.re_sum]
      refine sum_congr rfl fun d _ => by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv, one_div]
    rw [hre]
    refine (Complex.re_le_norm _).trans ?_
    have hb := norm_sum_mul_le_of_antitone (f := fun n => χ n)
      (g := fun n => 1 / Real.sqrt n) (a := Y + 1) (b := X / e + 1) (B := q)
      (by omega) (Nat.cast_nonneg q)
      (fun k _ => norm_sum_dirichlet_Ico_le hχ (Y + 1) k)
      (by positivity)
      (fun n hn => by
        rw [mem_Ico] at hn
        exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n)))
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)))
    simpa [div_eq_mul_inv] using hb
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  calc ∑ e ∈ Icc 1 (X / (Y + 1)), (1 / Real.sqrt e) *
        (∑ d ∈ Icc (Y + 1) (X / e), (χ d).re / Real.sqrt d)
      ≤ ∑ e ∈ Icc 1 (X / (Y + 1)), (1 / Real.sqrt e) * ((q : ℝ) / Real.sqrt (Y + 1 : ℕ)) :=
        sum_le_sum fun e he => mul_le_mul_of_nonneg_left (hinner e he) (by positivity)
    _ = (∑ e ∈ Icc 1 (X / (Y + 1)), 1 / Real.sqrt e) * ((q : ℝ) / Real.sqrt (Y + 1 : ℕ)) := by
        rw [← sum_mul]
    _ ≤ (2 * Real.sqrt ((X / (Y + 1) : ℕ) : ℝ)) * ((q : ℝ) / Real.sqrt (Y + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_right (inv_sqrt_sum_le _) (by positivity)
    _ ≤ (2 * Real.sqrt ((X : ℝ) / (Y + 1 : ℕ))) * ((q : ℝ) / Real.sqrt (Y + 1 : ℕ)) := by
        gcongr
        exact Nat.cast_div_le
    _ = 2 * (q : ℝ) * Real.sqrt X / ((Y + 1 : ℕ) : ℝ) := by
        rw [Real.sqrt_div (Nat.cast_nonneg X)]
        have hpos : (0 : ℝ) < Real.sqrt ((Y + 1 : ℕ) : ℝ) := by positivity
        field_simp [hpos.ne']
        rw [Real.sq_sqrt (by positivity)]
    _ ≤ 2 * (q : ℝ) * Real.sqrt X / Real.sqrt ((q : ℝ) * (X : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by positivity)) hsqrt_le_Y1
    _ = 2 * Real.sqrt q := by
        rw [Real.sqrt_mul (Nat.cast_nonneg q)]
        have hsq : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hq0
        have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
        field_simp [hsq.ne', hsX.ne']
        rw [Real.sq_sqrt (Nat.cast_nonneg q)]
    _ ≤ 4 * Real.sqrt q := by linarith [Real.sqrt_nonneg q]

lemma quadratic_hyperbola_err_abs {X k : ℕ} {c₀ : ℝ}
    (hk1 : 1 ≤ k) (h2k : 2 * k ≤ X)
    (ha : 0 ≤ (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) - 2 * Real.sqrt ((X / k : ℕ) : ℝ) - c₀ ∧
          (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) - 2 * Real.sqrt ((X / k : ℕ) : ℝ) - c₀ ≤
            1 / Real.sqrt ((X / k : ℕ) : ℝ)) :
    |(∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) - 2 * Real.sqrt ((X : ℝ) / k) - c₀| ≤
      4 * Real.sqrt ((k : ℝ) / X) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXk_le : ((X / k : ℕ) : ℝ) ≤ (X : ℝ) / k := Nat.cast_div_le
  have hXk_ge : (X : ℝ) / k - 1 ≤ ((X / k : ℕ) : ℝ) := by
    have hdiv := Nat.div_add_mod X k
    have hmod : X % k < k := Nat.mod_lt X (by omega)
    have h1 : (X : ℝ) < ((X / k : ℕ) : ℝ) * k + k := by
      have : X < (X / k) * k + k := by nlinarith
      exact_mod_cast this
    have h2 : (X : ℝ) / k < ((X / k : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hk0]; linarith
    linarith
  have hXk_half : (X : ℝ) / (2 * k) ≤ ((X / k : ℕ) : ℝ) := by
    have h2k_r : (2 * k : ℝ) ≤ X := by exact_mod_cast h2k
    have : 1 ≤ (X : ℝ) / (2 * k) := (one_le_div (by positivity)).mpr h2k_r
    have : (X : ℝ) / k - (X : ℝ) / (2 * k) = (X : ℝ) / (2 * k) := by ring
    linarith
  have hsqrt_diff : 0 ≤ Real.sqrt ((X : ℝ) / k) - Real.sqrt ((X / k : ℕ) : ℝ) ∧
      Real.sqrt ((X : ℝ) / k) - Real.sqrt ((X / k : ℕ) : ℝ) ≤ Real.sqrt ((k : ℝ) / X) := by
    constructor
    · exact sub_nonneg.mpr (Real.sqrt_le_sqrt hXk_le)
    · have hs1 : 0 < Real.sqrt ((X : ℝ) / k) := Real.sqrt_pos.mpr (div_pos hX0 hk0)
      have hprod : (Real.sqrt ((X : ℝ) / k) - Real.sqrt ((X / k : ℕ) : ℝ)) *
          (Real.sqrt ((X : ℝ) / k) + Real.sqrt ((X / k : ℕ) : ℝ)) =
          (X : ℝ) / k - ((X / k : ℕ) : ℝ) := by
        rw [mul_comm, ← sq_sub_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg _)]
      have hsq_d : (Real.sqrt ((X : ℝ) / k) - Real.sqrt ((X / k : ℕ) : ℝ)) *
          (Real.sqrt ((X : ℝ) / k) + Real.sqrt ((X / k : ℕ) : ℝ)) ≤ 1 := by linarith
      have hsum_ge : Real.sqrt ((X : ℝ) / k) ≤
          Real.sqrt ((X : ℝ) / k) + Real.sqrt ((X / k : ℕ) : ℝ) := by
        linarith [Real.sqrt_nonneg ((X / k : ℕ) : ℝ)]
      have hinv : 1 / Real.sqrt ((X : ℝ) / k) = Real.sqrt ((k : ℝ) / X) := by
        rw [Real.sqrt_div (Nat.cast_nonneg X), Real.sqrt_div (Nat.cast_nonneg k), one_div_div]
      rw [← hinv, le_div_iff₀ hs1]
      nlinarith [sub_nonneg.mpr (Real.sqrt_le_sqrt hXk_le)]
  have hrem : 1 / Real.sqrt ((X / k : ℕ) : ℝ) ≤ 2 * Real.sqrt ((k : ℝ) / X) := by
    have hinv : 1 / Real.sqrt ((X : ℝ) / (2 * k)) = Real.sqrt 2 * Real.sqrt ((k : ℝ) / X) := by
      rw [Real.sqrt_div (Nat.cast_nonneg X), Real.sqrt_mul (by norm_num),
          Real.sqrt_div (Nat.cast_nonneg k)]
      have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
      have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk0
      field_simp [hsX.ne', hsk.ne']
    have hle1 : 1 / Real.sqrt ((X / k : ℕ) : ℝ) ≤ 1 / Real.sqrt ((X : ℝ) / (2 * k)) :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt hXk_half)
    have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg ((k : ℝ) / X)]
  have herr_eq : (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) - 2 * Real.sqrt ((X : ℝ) / k) - c₀ =
      ((∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) - 2 * Real.sqrt ((X / k : ℕ) : ℝ) - c₀) -
      2 * (Real.sqrt ((X : ℝ) / k) - Real.sqrt ((X / k : ℕ) : ℝ)) := by ring
  rw [herr_eq, abs_le]
  constructor <;> linarith

lemma quadratic_hyperbola_S1_le {q X Y : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {d : ℝ} (hd : 0 < d) (hd_le : d ≤ Real.exp (-100 * (q : ℝ)))
    (hY_ge3 : 3 ≤ Y) (h2Y_le_X : 2 * Y ≤ X)
    (hY_le_sqrt : (Y : ℝ) ≤ Real.sqrt ((q : ℝ) * (X : ℝ)))
    (hsqrt_le_Y1 : Real.sqrt ((q : ℝ) * (X : ℝ)) ≤ ((Y + 1 : ℕ) : ℝ))
    (hsqrtX_le : Real.sqrt X ≤ 2 * Real.exp (20 * (q : ℝ))) :
    ∑ k ∈ Icc 1 Y, ((χ k).re / Real.sqrt k) * (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) ≤
      2 * Real.sqrt X * (LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)).re + 2 * (q : ℝ) + 12 * Real.sqrt q + 1 := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  obtain ⟨c₀, hc0, hasymp⟩ := inv_sqrt_sum_asymp
  let err : ℕ → ℝ := fun k => (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) - 2 * Real.sqrt ((X : ℝ) / k) - c₀
  have hsplit1 : ∑ k ∈ Icc 1 Y, ((χ k).re / Real.sqrt k) * (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) =
      2 * Real.sqrt X * (∑ k ∈ Icc 1 Y, (χ k).re / k) +
      c₀ * (∑ k ∈ Icc 1 Y, (χ k).re / Real.sqrt k) +
      ∑ k ∈ Icc 1 Y, ((χ k).re / Real.sqrt k) * err k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
    have hsqk : Real.sqrt k * Real.sqrt k = (k : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg k)
    dsimp [err]
    rw [Real.sqrt_div (Nat.cast_nonneg X)]
    have hterm : ((χ k).re / Real.sqrt k) * (2 * (Real.sqrt X / Real.sqrt k)) =
        2 * Real.sqrt X * ((χ k).re / k) := by
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp [hsk.ne', hk0]
      rw [Real.sq_sqrt (Nat.cast_nonneg k)]
    linarith [show ((χ k).re / Real.sqrt k) * (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) =
      ((χ k).re / Real.sqrt k) * (2 * (Real.sqrt X / Real.sqrt k)) +
      c₀ * ((χ k).re / Real.sqrt k) +
      ((χ k).re / Real.sqrt k) * ((∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) -
        2 * (Real.sqrt X / Real.sqrt k) - c₀) by ring]
  rw [hsplit1]
  have hterm3 : ∑ k ∈ Icc 1 Y, ((χ k).re / Real.sqrt k) * err k ≤ 4 * Real.sqrt q := by
    calc ∑ k ∈ Icc 1 Y, ((χ k).re / Real.sqrt k) * err k
        ≤ ∑ k ∈ Icc 1 Y, |((χ k).re / Real.sqrt k) * err k| := sum_le_sum fun _ _ => le_abs_self _
      _ ≤ ∑ k ∈ Icc 1 Y, (1 / Real.sqrt k) * (4 * Real.sqrt ((k : ℝ) / X)) := by
          refine sum_le_sum fun k hk => ?_
          rw [mem_Icc] at hk
          rw [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hre1 : |(χ k).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (χ.norm_le_one k)
          have hdiv1 : |(χ k).re| / Real.sqrt k ≤ 1 / Real.sqrt k :=
            div_le_div_of_nonneg_right hre1 (Real.sqrt_nonneg _)
          have herr := quadratic_hyperbola_err_abs hk.1 (by omega)
            (hasymp (X / k) (Nat.div_pos (by omega) hk.1))
          exact mul_le_mul hdiv1 herr (abs_nonneg _) (by positivity)
      _ = ∑ _k ∈ Icc 1 Y, (4 / Real.sqrt X) := by
          refine sum_congr rfl fun k hk => ?_
          rw [mem_Icc] at hk
          have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
          rw [Real.sqrt_div (Nat.cast_nonneg k)]
          field_simp [hsk.ne']
      _ = (Y : ℝ) * (4 / Real.sqrt X) := by simp
      _ ≤ Real.sqrt ((q : ℝ) * (X : ℝ)) * (4 / Real.sqrt X) :=
          mul_le_mul_of_nonneg_right hY_le_sqrt (by positivity)
      _ = 4 * Real.sqrt q := by
          rw [Real.sqrt_mul (Nat.cast_nonneg q)]
          have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
          field_simp [hsX.ne']
  have hterm2 : c₀ * (∑ k ∈ Icc 1 Y, (χ k).re / Real.sqrt k) ≤ 2 * (q : ℝ) := by
    have habs_sum : |∑ k ∈ Icc 1 Y, (χ k).re / Real.sqrt k| ≤ q := by
      have hIcc_eq : Icc 1 Y = Ico 1 (Y + 1) := rfl
      rw [hIcc_eq]
      have hre : ∑ k ∈ Ico 1 (Y + 1), (χ k).re / Real.sqrt k =
          (∑ k ∈ Ico 1 (Y + 1), χ k * (((1 / Real.sqrt k : ℝ) : ℂ))).re := by
        rw [Complex.re_sum]
        refine sum_congr rfl fun k _ => by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv, one_div]
      rw [hre]
      refine (Complex.abs_re_le_norm _).trans ?_
      have hb := norm_sum_mul_le_of_antitone (f := fun n => χ n)
        (g := fun n => 1 / Real.sqrt n) (a := 1) (b := Y + 1) (B := q)
        (by omega) (Nat.cast_nonneg q)
        (fun k _ => norm_sum_dirichlet_Ico_le hχ 1 k)
        (by positivity)
        (fun n hn => by
          rw [mem_Ico] at hn
          exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n)))
            (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)))
      simpa using hb
    calc c₀ * (∑ k ∈ Icc 1 Y, (χ k).re / Real.sqrt k)
        ≤ |c₀ * (∑ k ∈ Icc 1 Y, (χ k).re / Real.sqrt k)| := le_abs_self _
      _ = |c₀| * |∑ k ∈ Icc 1 Y, (χ k).re / Real.sqrt k| := abs_mul _ _
      _ ≤ 2 * (q : ℝ) := mul_le_mul hc0 habs_sum (abs_nonneg _) (by norm_num)
  have hterm1 : 2 * Real.sqrt X * ((∑ k ∈ Icc 1 Y, (χ k).re / k) - (LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)).re) ≤
      8 * Real.sqrt q + 1 := by
    have hIcc_eq : Icc 1 Y = Ico 1 (Y + 1) := rfl
    have hdiff_split : (∑ k ∈ Icc 1 Y, (χ k).re / k) - (LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)).re =
        (∑ k ∈ Ico 1 (Y + 1), χ k * ((((k : ℝ) ^ (-1 : ℝ) - (k : ℝ) ^ (-(1 + d))) : ℝ) : ℂ)).re -
        (LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ) - ∑ k ∈ Ico 1 (Y + 1), χ k * (((k : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)).re := by
      rw [hIcc_eq, Complex.sub_re, Complex.re_sum, Complex.re_sum]
      have hcongr : ∑ k ∈ Ico 1 (Y + 1), (χ k * ((((k : ℝ) ^ (-1 : ℝ) - (k : ℝ) ^ (-(1 + d))) : ℝ) : ℂ)).re =
          (∑ k ∈ Ico 1 (Y + 1), (χ k).re / k) -
          (∑ k ∈ Ico 1 (Y + 1), (χ k * (((k : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)).re) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun k _ => by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
            Real.rpow_neg_one, div_eq_mul_inv]
          ring
      linarith
    rw [hdiff_split]
    have h1_lip : (∑ k ∈ Ico 1 (Y + 1), χ k * ((((k : ℝ) ^ (-1 : ℝ) - (k : ℝ) ^ (-(1 + d))) : ℝ) : ℂ)).re ≤
        8 * (q : ℝ) * d := by
      refine (Complex.re_le_norm _).trans ?_
      have h := norm_sum_dirichlet_lipschitz hχ (s₁ := 1) (s₂ := 1 + d) le_rfl (by linarith) (Y + 1) (by omega)
      simpa [show (1 + d) - 1 = d by ring] using h
    have h2_tail : -(LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ) -
        ∑ k ∈ Ico 1 (Y + 1), χ k * (((k : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)).re ≤
        (q : ℝ) / ((Y + 1 : ℕ) : ℝ) := by
      have hneg := Complex.re_le_norm (-(LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ) -
        ∑ k ∈ Ico 1 (Y + 1), χ k * (((k : ℝ) ^ (-(1 + d)) : ℝ) : ℂ)))
      rw [Complex.neg_re, norm_neg] at hneg
      have htail := norm_LSeries_nontriv_tail_le hχ hd Y
      rw [Nat.cast_add, Nat.cast_one]
      exact hneg.trans htail
    have h2_mul : 2 * Real.sqrt X * ((q : ℝ) / ((Y + 1 : ℕ) : ℝ)) ≤ 8 * Real.sqrt q := by
      calc 2 * Real.sqrt X * ((q : ℝ) / ((Y + 1 : ℕ) : ℝ))
          ≤ 2 * Real.sqrt X * ((q : ℝ) / Real.sqrt ((q : ℝ) * (X : ℝ))) := by
            gcongr
        _ = 2 * Real.sqrt q := by
            rw [Real.sqrt_mul (Nat.cast_nonneg q)]
            have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
            have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
            field_simp [hsq.ne', hsX.ne']
            rw [Real.sq_sqrt (Nat.cast_nonneg q)]
        _ ≤ 8 * Real.sqrt q := by linarith [Real.sqrt_nonneg q]
    have h1_mul : 2 * Real.sqrt X * (8 * (q : ℝ) * d) ≤ 1 := by
      have hq_exp : 32 * (q : ℝ) ≤ Real.exp (80 * (q : ℝ)) := by
        have := Real.add_one_le_exp (80 * (q : ℝ))
        linarith
      calc 2 * Real.sqrt X * (8 * (q : ℝ) * d)
          ≤ 2 * (2 * Real.exp (20 * (q : ℝ))) * (8 * (q : ℝ) * Real.exp (-100 * (q : ℝ))) := by
            gcongr
        _ = 32 * (q : ℝ) * Real.exp (-80 * (q : ℝ)) := by
            have hmul : Real.exp (20 * (q : ℝ)) * Real.exp (-100 * (q : ℝ)) = Real.exp (-80 * (q : ℝ)) := by
              rw [← Real.exp_add]; ring_nf
            rw [show 2 * (2 * Real.exp (20 * (q : ℝ))) * (8 * (q : ℝ) * Real.exp (-100 * (q : ℝ))) =
              32 * (q : ℝ) * (Real.exp (20 * (q : ℝ)) * Real.exp (-100 * (q : ℝ))) by ring, hmul]
        _ ≤ Real.exp (80 * (q : ℝ)) * Real.exp (-80 * (q : ℝ)) :=
            mul_le_mul_of_nonneg_right hq_exp (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.sqrt_nonneg X]
  linarith

lemma norm_LSeries_quadratic_ge {q : ℕ} (hq : q.Prime) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) {d : ℝ} (hd : 0 < d) (hd_le : d ≤ Real.exp (-100 * (q : ℝ))) :
    Real.exp (-25 * (q : ℝ)) ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  set X : ℕ := ⌈Real.exp (40 * (q : ℝ))⌉₊
  set Y : ℕ := Nat.sqrt (q * X)
  have hexp_ge : 16 * (q : ℝ) ^ 2 ≤ Real.exp (40 * (q : ℝ)) := by
    have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 40 * (q : ℝ)) 3
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      pow_zero, Nat.factorial, Nat.cast_one, div_one, pow_one, Nat.cast_mul] at h
    nlinarith
  have hX_real : Real.exp (40 * (q : ℝ)) ≤ (X : ℝ) := Nat.le_ceil _
  have hX_real_lt : (X : ℝ) ≤ Real.exp (40 * (q : ℝ)) + 1 := by
    have := Nat.ceil_lt_add_one (Real.exp_nonneg (40 * (q : ℝ)))
    linarith
  have hX_ge : 16 * q ^ 2 ≤ X := by exact_mod_cast (hexp_ge.trans hX_real)
  have hX_pos : 0 < X := by nlinarith [hq.two_le]
  have hY_sq_le : Y ^ 2 ≤ q * X := by simpa [sq] using Nat.sqrt_le (q * X)
  have hY_lt : q * X < (Y + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt (q * X)
  have hY_ge_q : 4 * q ≤ Y := by
    by_contra hlt; push Not at hlt
    have h1 : Y + 1 ≤ 4 * q := by omega
    have h2 : (Y + 1) ^ 2 ≤ 16 * q ^ 2 := by nlinarith
    have h3 : 16 * q ^ 3 ≤ q * X := by nlinarith
    nlinarith [hq.two_le]
  have hY_ge3 : 3 ≤ Y := by
    have := hq.two_le; omega
  have h2Y_le_X : 2 * Y ≤ X := by
    by_contra hlt; push Not at hlt
    have h1 : X ^ 2 < 4 * Y ^ 2 := by nlinarith
    have h2 : 4 * Y ^ 2 ≤ 4 * q * X := by nlinarith
    have h3 : 4 * q * X ≤ X ^ 2 := by nlinarith [hq.two_le]
    omega
  have hY_le_sqrt : (Y : ℝ) ≤ Real.sqrt ((q : ℝ) * (X : ℝ)) := by
    rw [Real.le_sqrt (Nat.cast_nonneg Y) (by positivity)]
    exact_mod_cast hY_sq_le
  have hsqrt_le_Y1 : Real.sqrt ((q : ℝ) * (X : ℝ)) ≤ ((Y + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by exact_mod_cast hY_lt.le⟩
  have hsqrtX_le : Real.sqrt X ≤ 2 * Real.exp (20 * (q : ℝ)) := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (Real.exp (20 * (q : ℝ))) ^ 2 = Real.exp (40 * (q : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h1 : (1 : ℝ) ≤ Real.exp (40 * (q : ℝ)) := Real.one_le_exp (by positivity)
    nlinarith
  let a : ℕ → ℝ := fun n => (χ.zetaMul n).re
  have ha_eq : ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ n.divisors, (χ k).re := by
    intro n _
    dsimp [a]
    simp only [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply, Complex.re_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
    rw [← DirichletCharacter.apply_eq_toArithmeticFunction_apply χ hk0]
  have hS_lower : 20 * (q : ℝ) ≤ ∑ n ∈ Icc 1 X, a n / Real.sqrt n := by
    set K := Nat.sqrt X
    have hK_sub : (Icc 1 K).image (fun m => m ^ 2) ⊆ Icc 1 X := by
      intro n hn
      rcases mem_image.mp hn with ⟨m, hm, rfl⟩
      rw [mem_Icc] at hm ⊢
      refine ⟨by nlinarith, ?_⟩
      have := Nat.sqrt_le X
      nlinarith
    have h1 : ∑ m ∈ Icc 1 K, (1 : ℝ) / m ≤ ∑ n ∈ Icc 1 X, a n / Real.sqrt n := by
      calc ∑ m ∈ Icc 1 K, (1 : ℝ) / m
          ≤ ∑ m ∈ Icc 1 K, a (m ^ 2) / Real.sqrt ((m ^ 2 : ℕ) : ℝ) := by
            refine sum_le_sum fun m hm => ?_
            rw [mem_Icc] at hm
            rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]
            exact div_le_div_of_nonneg_right (quadratic_zetaMul_sq_ge_one hsq hm.1) (Nat.cast_nonneg m)
        _ = ∑ n ∈ (Icc 1 K).image (fun m => m ^ 2), a n / Real.sqrt n := by
            rw [Finset.sum_image]
            intro m₁ _ m₂ _ hEq; exact Nat.pow_left_injective (by decide : 2 ≠ 0) hEq
        _ ≤ ∑ n ∈ Icc 1 X, a n / Real.sqrt n :=
            sum_le_sum_of_subset_of_nonneg hK_sub fun n _ _ =>
              div_nonneg (quadratic_zetaMul_re_nonneg hsq n) (Real.sqrt_nonneg _)
    have hlogX : 40 * (q : ℝ) ≤ Real.log (X : ℝ) := by
      rw [← Real.log_exp (40 * (q : ℝ))]
      exact Real.log_le_log (Real.exp_pos _) hX_real
    have hKlog : Real.log (X : ℝ) / 2 ≤ Real.log ((K + 1 : ℕ) : ℝ) := by
      have hX_lt : (X : ℝ) < ((K + 1 : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast (by simpa [sq] using Nat.lt_succ_sqrt X)
      have h1' := Real.log_le_log (by positivity : (0 : ℝ) < X) hX_lt.le
      rw [Real.log_pow] at h1'
      push_cast at h1' ⊢; linarith
    linarith [sum_inv_ge_log_succ K]
  have hS_eq : ∑ n ∈ Icc 1 X, a n / Real.sqrt n =
      ∑ k ∈ Icc 1 Y, ((χ k).re / Real.sqrt k) * (∑ e ∈ Icc 1 (X / k), 1 / Real.sqrt e) +
      ∑ e ∈ Icc 1 (X / (Y + 1)), (1 / Real.sqrt e) * (∑ k ∈ Icc (Y + 1) (X / e), (χ k).re / Real.sqrt k) := by
    rw [Finset.sum_congr rfl fun n hn => by rw [ha_eq n (mem_Icc.mp hn).1]]
    exact hyperbola_split_sum (fun k => (χ k).re) X Y
  have hS1 := quadratic_hyperbola_S1_le hχ hd hd_le hY_ge3 h2Y_le_X hY_le_sqrt hsqrt_le_Y1 hsqrtX_le
  have hS2 := quadratic_hyperbola_S2_le hχ hX_pos hsqrt_le_Y1
  have hcomb : 2 * (q : ℝ) ≤ 2 * Real.sqrt X * (LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)).re := by
    have h16 : 16 * Real.sqrt q ≤ 12 * (q : ℝ) := by
      have : Real.sqrt q ≤ (q : ℝ) * (3 / 4) := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith
      linarith
    linarith
  have hre_ge : (q : ℝ) / Real.sqrt X ≤ (LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)).re := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
    linarith
  have hexp_bound : Real.exp (-25 * (q : ℝ)) ≤ (q : ℝ) / Real.sqrt X := by
    calc Real.exp (-25 * (q : ℝ))
        ≤ Real.exp (-20 * (q : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / Real.exp (20 * (q : ℝ)) := by
          rw [show (-20 * (q : ℝ)) = -(20 * (q : ℝ)) by ring, Real.exp_neg, one_div]
      _ = 2 / (2 * Real.exp (20 * (q : ℝ))) := by ring
      _ ≤ (q : ℝ) / (2 * Real.exp (20 * (q : ℝ))) :=
          div_le_div_of_nonneg_right hq2 (by positivity)
      _ ≤ (q : ℝ) / Real.sqrt X :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrtX_le
  exact hexp_bound.trans (hre_ge.trans (Complex.re_le_norm _))

lemma norm_LSeries_nontriv_ge {q : ℕ} (hq : q.Prime) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {d : ℝ} (hd : 0 < d) (hd_le : d ≤ Real.exp (-100 * (q : ℝ))) :
    Real.exp (-25 * (q : ℝ)) ≤ ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
  by_cases hsq : χ ^ 2 = 1
  · exact norm_LSeries_quadratic_ge hq hχ hsq hd hd_le
  · exact norm_LSeries_complex_ge hq hχ hsq hd hd_le

/- Prime AP reciprocal sum lower bound via Euler product and character orthogonality -/

lemma card_dirichletCharacter (q : ℕ) [NeZero q] :
    Fintype.card (DirichletCharacter ℂ q) = q.totient := by
  have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_one : IsUnit (1 : ZMod q)) 1
  simp at horth
  exact Nat.cast_injective horth

lemma sum_inv_sq_primes_le : ∑' p : Nat.Primes, (1 : ℝ) / (p.1 : ℝ) ^ 2 ≤ 1 := by
  have hsum_nat : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsum_p : Summable (fun p : Nat.Primes => (1 : ℝ) / (p.1 : ℝ) ^ 2) :=
    hsum_nat.comp_injective Subtype.val_injective
  refine hsum_p.tsum_le_of_sum_le fun s => ?_
  let M : ℕ := (s.image Subtype.val).sup id
  have hsub : s.image Subtype.val ⊆ Icc 2 (max M 2) := by
    intro n hn
    rcases mem_image.mp hn with ⟨p, hp, rfl⟩
    rw [mem_Icc]
    exact ⟨p.prop.two_le, le_trans (Finset.le_sup (f := id) (mem_image_of_mem _ hp)) (le_max_left _ _)⟩
  calc ∑ p ∈ s, (1 : ℝ) / (p.1 : ℝ) ^ 2
      = ∑ n ∈ s.image Subtype.val, (1 : ℝ) / (n : ℝ) ^ 2 := by
        symm
        exact Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (fun _ _ _ _ h => Subtype.ext h)
    _ ≤ ∑ n ∈ Icc 2 (max M 2), (1 : ℝ) / (n : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ n ∈ Icc 2 (max M 2), (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := by
        refine sum_le_sum fun n hn => ?_
        rw [mem_Icc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
        have hdiff : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
          have : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (show n = (n - 1) + 1 by omega)
          linarith
        have hrhs : 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) = 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by
          rw [div_sub_div _ _ hn1.ne' hn0.ne', one_mul, mul_one, hdiff]
        rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ = ∑ k ∈ Ico 1 (max M 2), (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
        · intro n hn; rw [mem_Icc] at hn; rw [mem_Ico]; omega
        · intro n₁ hn₁ n₂ hn₂ h; rw [mem_Icc] at hn₁ hn₂; omega
        · intro k hk; rw [mem_Ico] at hk; exact ⟨k + 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro n hn; rw [mem_Icc] at hn; rw [Nat.sub_add_cancel (by omega)]
    _ = 1 / ((1 : ℕ) : ℝ) - 1 / ((max M 2 : ℕ) : ℝ) :=
        sum_sub_succ_Ico (fun k => 1 / (k : ℝ)) (show 1 ≤ max M 2 by omega)
    _ ≤ 1 := by
        simp only [Nat.cast_one, div_one]
        linarith [show (0 : ℝ) ≤ 1 / ((max M 2 : ℕ) : ℝ) by positivity]

lemma log_LSeries_le_prime_sum {q : ℕ} (χ : DirichletCharacter ℂ q) {d : ℝ} (hd : 0 < d) :
    Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ ≤
      (∑' p : Nat.Primes, (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d))) + 1 := by
  have hσ : 1 < (((1 + d : ℝ) : ℂ)).re := by simp [hd]
  have hlog_eq : Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ =
      ∑' p : Nat.Primes, (-Complex.log (1 - χ p.1 * (p.1 : ℂ) ^ (-((1 + d : ℝ) : ℂ)))).re := by
    have heul := DirichletCharacter.LSeries_eulerProduct_exp_log χ hσ
    rw [← heul, Complex.norm_exp, Real.log_exp]
    exact Complex.re_tsum (DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow χ hσ)
  have hterm_diff : ∀ p : Nat.Primes,
      (-Complex.log (1 - χ p.1 * (p.1 : ℂ) ^ (-((1 + d : ℝ) : ℂ)))).re ≤
        (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d)) + 1 / (p.1 : ℝ) ^ 2 := by
    intro p
    have hcpow_eq : (p.1 : ℂ) ^ (-((1 + d : ℝ) : ℂ)) = (((p.1 : ℝ) ^ (-(1 + d)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg,
          Complex.ofReal_cpow (Nat.cast_nonneg p.1)]
    set z : ℂ := -(χ p.1 * (((p.1 : ℝ) ^ (-(1 + d)) : ℝ) : ℂ))
    have hp2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.prop.two_le
    have hz_norm : ‖z‖ ≤ (p.1 : ℝ) ^ (-(1 + d)) := by
      dsimp [z]
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.1) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p.1) _) (χ.norm_le_one _)
    have hp_inv : (p.1 : ℝ) ^ (-(1 + d)) ≤ 1 / (p.1 : ℝ) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hz_half : ‖z‖ ≤ 1 / 2 := hz_norm.trans (hp_inv.trans (by
      rw [one_div_le_one_div (by positivity) (by norm_num)]; exact hp2))
    have hlog_b := Complex.norm_log_one_add_sub_self_le (z := z) (by linarith)
    have hre_z : (-z).re = (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d)) := by
      dsimp [z]
      rw [neg_neg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h1z : 1 + z = 1 - χ p.1 * (p.1 : ℂ) ^ (-((1 + d : ℝ) : ℂ)) := by
      dsimp [z]; rw [hcpow_eq]; ring
    have hdiff_le : ‖-Complex.log (1 + z) - (-z)‖ ≤ 1 / (p.1 : ℝ) ^ 2 := by
      rw [show -Complex.log (1 + z) - (-z) = -(Complex.log (1 + z) - z) by ring, norm_neg]
      refine hlog_b.trans ?_
      have hinv2 : (1 - ‖z‖)⁻¹ / 2 ≤ 1 := by
        have h1 : (1 : ℝ) / 2 ≤ 1 - ‖z‖ := by linarith
        have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        linarith
      have hsq : ‖z‖ ^ 2 ≤ 1 / (p.1 : ℝ) ^ 2 := by
        have hle : ‖z‖ ≤ 1 / (p.1 : ℝ) := hz_norm.trans hp_inv
        calc ‖z‖ ^ 2 ≤ (1 / (p.1 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
          _ = 1 / (p.1 : ℝ) ^ 2 := by ring
      calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2
          = ‖z‖ ^ 2 * ((1 - ‖z‖)⁻¹ / 2) := by ring
        _ ≤ ‖z‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hinv2 (sq_nonneg _)
        _ ≤ 1 / (p.1 : ℝ) ^ 2 := by linarith
    have hre_diff := (Complex.re_le_norm _).trans hdiff_le
    rw [Complex.sub_re, h1z, hre_z] at hre_diff
    linarith
  have hsum_prpow : Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-(1 + d))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hsum_chi_p : Summable (fun p : Nat.Primes => (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d))) := by
    refine Summable.of_norm_bounded hsum_prpow fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.1) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p.1) _)
      ((Complex.abs_re_le_norm _).trans (χ.norm_le_one _))
  have hsum_inv2 : Summable (fun p : Nat.Primes => (1 : ℝ) / (p.1 : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).comp_injective Subtype.val_injective
  rw [hlog_eq]
  have h1 := ((hasSum_re (DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow χ hσ).hasSum).summable).tsum_le_tsum
    hterm_diff (hsum_chi_p.add hsum_inv2)
  rw [hsum_chi_p.tsum_add hsum_inv2] at h1
  linarith [sum_inv_sq_primes_le]

lemma prime_ap_sum_ge {q M : ℕ} (hq : q.Prime) (hqM : q ≤ M) :
    2 * (M : ℝ) ≤
      ∑ p ∈ (Ioc M (2 ^ (2 ^ (400 * M ^ 2)))).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]),
        (1 : ℝ) / p := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hM2 : 2 ≤ M := hq.two_le.trans hqM
  have hM2r : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hqMr : (q : ℝ) ≤ M := by exact_mod_cast hqM
  set d : ℝ := Real.exp (-200 * (M : ℝ) ^ 2)
  have hd_pos : 0 < d := Real.exp_pos _
  have hd_le_q : d ≤ Real.exp (-100 * (q : ℝ)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have hsum_prpow : Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-(1 + d))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hsum_chi_p : ∀ χ : DirichletCharacter ℂ q,
      Summable (fun p : Nat.Primes => (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d))) := by
    intro χ
    refine Summable.of_norm_bounded hsum_prpow fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.1) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p.1) _)
      ((Complex.abs_re_le_norm _).trans (χ.norm_le_one _))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := card_dirichletCharacter q
  have hsum_chars : ∑ χ : DirichletCharacter ℂ q, Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ ≤
      (q.totient : ℝ) * (∑' p : Nat.Primes, if p.1 ≡ 1 [MOD q] then (p.1 : ℝ) ^ (-(1 + d)) else 0) +
      (q.totient : ℝ) := by
    calc ∑ χ : DirichletCharacter ℂ q, Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖
        ≤ ∑ χ : DirichletCharacter ℂ q, ((∑' p : Nat.Primes, (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d))) + 1) :=
          sum_le_sum fun χ _ => log_LSeries_le_prime_sum χ hd_pos
      _ = (∑ χ : DirichletCharacter ℂ q, ∑' p : Nat.Primes, (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d))) +
          (q.totient : ℝ) := by
          rw [sum_add_distrib, sum_const, card_univ, hcard, nsmul_eq_mul, mul_one]
      _ = (∑' p : Nat.Primes, ∑ χ : DirichletCharacter ℂ q, (χ p.1).re * (p.1 : ℝ) ^ (-(1 + d))) +
          (q.totient : ℝ) := by
          rw [(Summable.tsum_finsetSum fun χ _ => hsum_chi_p χ).symm]
      _ = (q.totient : ℝ) * (∑' p : Nat.Primes, if p.1 ≡ 1 [MOD q] then (p.1 : ℝ) ^ (-(1 + d)) else 0) +
          (q.totient : ℝ) := by
          congr 1
          rw [← tsum_mul_left]
          congr 1; ext p
          rw [← sum_mul, ← Complex.re_sum]
          have horth := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_one : IsUnit (1 : ZMod q)) (p.1 : ZMod q)
          have h1 : (∑ χ : DirichletCharacter ℂ q, χ (p.1 : ZMod q)) =
              if (1 : ZMod q) = (p.1 : ZMod q) then (q.totient : ℂ) else 0 := by
            simpa using horth
          rw [h1]
          by_cases hmod : p.1 ≡ 1 [MOD q]
          · have hzeq : (1 : ZMod q) = (p.1 : ZMod q) := by
              rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
              exact hmod.symm
            rw [if_pos hzeq, if_pos hmod, Complex.natCast_re]
          · have hzne : (1 : ZMod q) ≠ (p.1 : ZMod q) := by
              intro heq; apply hmod
              rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at heq
              exact heq.symm
            rw [if_neg hzne, if_neg hmod, Complex.zero_re, zero_mul, mul_zero]
  have hsum_lower : 170 * (M : ℝ) ^ 2 ≤ ∑ χ : DirichletCharacter ℂ q, Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
    have hsplit : ∑ χ : DirichletCharacter ℂ q, Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ =
        Real.log ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)‖ +
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
      rw [Finset.add_sum_erase univ (fun χ : DirichletCharacter ℂ q => Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖) (mem_univ 1)]
    rw [hsplit]
    have h1_ge : 200 * (M : ℝ) ^ 2 - 1 ≤ Real.log ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) ((1 + d : ℝ) : ℂ)‖ := by
      have hge := norm_LSeries_one_ge hq hd_pos
      have hlog := Real.log_le_log (by positivity) hge
      rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hd_pos.ne'] at hlog
      have hdlog : Real.log d = -200 * (M : ℝ) ^ 2 := Real.log_exp _
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      linarith
    have hrest_ge : -(25 * (M : ℝ) ^ 2) ≤
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
      have hcard_erase : (((univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) ≤ (q : ℝ) := by
        have h1 : ((univ : Finset (DirichletCharacter ℂ q)).erase 1).card ≤
            Fintype.card (DirichletCharacter ℂ q) := card_le_univ _
        have h3 : q.totient ≤ q := Nat.totient_le q
        exact_mod_cast (h1.trans (hcard.le.trans h3))
      calc -(25 * (M : ℝ) ^ 2)
          ≤ -(25 * (q : ℝ) * (q : ℝ)) := by nlinarith
        _ ≤ (((univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) * (-25 * (q : ℝ)) := by nlinarith
        _ = ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, (-25 * (q : ℝ)) := by simp
        _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, Real.log ‖LSeries (fun n : ℕ => χ n) ((1 + d : ℝ) : ℂ)‖ := by
            refine sum_le_sum fun χ hχ => ?_
            have hne : χ ≠ 1 := (mem_erase.mp hχ).1
            have hge := norm_LSeries_nontriv_ge hq hne hd_pos hd_le_q
            have hlog := Real.log_le_log (Real.exp_pos _) hge
            rwa [Real.log_exp] at hlog
    nlinarith
  have hphi_pos : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq.pos)
  have hphi_le : (q.totient : ℝ) ≤ M := by exact_mod_cast (Nat.totient_le q).trans hqM
  have htsum_ge : 160 * (M : ℝ) ≤
      ∑' p : Nat.Primes, if p.1 ≡ 1 [MOD q] then (p.1 : ℝ) ^ (-(1 + d)) else 0 := by
    have h1 : 160 * (M : ℝ) * (q.totient : ℝ) ≤
        (q.totient : ℝ) * (∑' p : Nat.Primes, if p.1 ≡ 1 [MOD q] then (p.1 : ℝ) ^ (-(1 + d)) else 0) := by
      nlinarith
    exact le_of_mul_le_mul_left (by linarith) hphi_pos
  set X_tail : ℕ := 2 ^ (2 ^ (400 * M ^ 2))
  have hX_tail_gt : M < X_tail := by
    have h1 : M < 2 ^ M := Nat.lt_two_pow_self
    have h2 : M ≤ 400 * M ^ 2 := by nlinarith
    have h3 : 2 ^ M ≤ 2 ^ (400 * M ^ 2) := Nat.pow_le_pow_right (by decide) h2
    have h4 : 2 ^ (400 * M ^ 2) < 2 ^ (2 ^ (400 * M ^ 2)) := Nat.lt_two_pow_self
    omega
  let f : Nat.Primes → ℝ := fun p => if p.1 ≡ 1 [MOD q] then (p.1 : ℝ) ^ (-(1 + d)) else 0
  have hf_nonneg : ∀ p, 0 ≤ f p := fun p => by dsimp [f]; split_ifs <;> positivity
  have hf_sum : Summable f :=
    hsum_prpow.of_nonneg_of_le hf_nonneg fun p => by
      dsimp [f]; split_ifs with h
      · exact le_rfl
      · positivity
  let S_le : Finset Nat.Primes :=
    ((Icc 1 X_tail).filter Nat.Prime).attach.map
      ⟨fun x => (⟨x.1, (mem_filter.mp x.2).2⟩ : Nat.Primes),
       fun a b h => Subtype.ext (by simpa using congrArg (fun z : Nat.Primes => (z : ℕ)) h)⟩
  have htsum_split : ∑' p : Nat.Primes, f p ≤ (∑ p ∈ S_le, f p) + 1 := by
    have htail_le : ∑' p : Nat.Primes, (if p ∈ S_le then 0 else f p) ≤ 1 := by
      have hsum_tail : Summable (fun p : Nat.Primes => if p ∈ S_le then 0 else f p) :=
        hf_sum.of_nonneg_of_le (fun p => by split_ifs; exact le_rfl; exact hf_nonneg p)
          (fun p => by split_ifs; exact hf_nonneg p; exact le_rfl)
      refine hsum_tail.tsum_le_of_sum_le fun s => ?_
      let K := max (X_tail + 1) ((s.image (fun p : Nat.Primes => (p : ℕ))).sup id + 1)
      have hsub : (s.filter (fun p => p ∉ S_le)).image (fun p : Nat.Primes => (p : ℕ)) ⊆ Ico (X_tail + 1) K := by
        intro n hn
        rcases mem_image.mp hn with ⟨p, hp, rfl⟩
        have hp' : p ∈ s ∧ p ∉ S_le := mem_filter.mp hp
        rw [mem_Ico]
        refine ⟨?_, ?_⟩
        · by_contra hle; push Not at hle
          apply hp'.2
          rw [Finset.mem_map]
          refine ⟨⟨(p : ℕ), mem_filter.mpr ⟨mem_Icc.mpr ⟨p.prop.pos, by omega⟩, p.prop⟩⟩, mem_attach _ _, ?_⟩
          exact Subtype.ext rfl
        · have hle : (p : ℕ) ≤ (s.image (fun p : Nat.Primes => (p : ℕ))).sup id :=
            Finset.le_sup (f := id) (mem_image_of_mem _ hp'.1)
          omega
      calc ∑ p ∈ s, (if p ∈ S_le then 0 else f p)
          = ∑ p ∈ s.filter (fun p => p ∉ S_le), f p := by
            rw [Finset.sum_filter]; refine sum_congr rfl fun p _ => by split_ifs <;> rfl
        _ ≤ ∑ p ∈ s.filter (fun p => p ∉ S_le), (p.1 : ℝ) ^ (-(1 + d)) :=
            sum_le_sum fun p _ => by dsimp [f]; split_ifs; exact le_rfl; positivity
        _ = ∑ n ∈ (s.filter (fun p => p ∉ S_le)).image (fun p : Nat.Primes => (p : ℕ)), (n : ℝ) ^ (-(1 + d)) := by
            symm
            exact Finset.sum_image (f := fun n : ℕ => (n : ℝ) ^ (-(1 + d)))
              (fun _ _ _ _ h => Subtype.ext h)
        _ ≤ ∑ n ∈ Ico (X_tail + 1) K, (n : ℝ) ^ (-(1 + d)) :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ (X_tail : ℝ) ^ (-d) / d := sum_rpow_Ico_le (by omega) (le_max_left _ _) hd_pos
        _ ≤ 1 := by
            rw [div_le_one hd_pos, Real.rpow_def_of_pos (by positivity)]
            have hlogX : (2 ^ (400 * M ^ 2) : ℝ) * (1 / 2) ≤ Real.log (X_tail : ℝ) := by
              have hcast : (X_tail : ℝ) = (2 : ℝ) ^ (2 ^ (400 * M ^ 2)) := by
                dsimp [X_tail]; push_cast; rfl
              rw [hcast, Real.log_pow]
              have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
              push_cast
              exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
            have hexp_le_pow : Real.exp (200 * (M : ℝ) ^ 2) * (400 * (M : ℝ) ^ 2) ≤
                (2 : ℝ) ^ (400 * M ^ 2) := by
              have h2pow : Real.exp (250 * (M : ℝ) ^ 2) ≤ (2 : ℝ) ^ (400 * M ^ 2) := by
                rw [← Real.rpow_natCast (2 : ℝ), Real.rpow_def_of_pos (by norm_num)]
                apply Real.exp_le_exp.mpr
                have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
                push_cast; nlinarith
              have h400 : 400 * (M : ℝ) ^ 2 ≤ Real.exp (50 * (M : ℝ) ^ 2) := by
                have h := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 50 * (M : ℝ) ^ 2) 3
                norm_num [Finset.sum_range_succ, Nat.factorial] at h
                have hM4 : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
                nlinarith
              calc Real.exp (200 * (M : ℝ) ^ 2) * (400 * (M : ℝ) ^ 2)
                  ≤ Real.exp (200 * (M : ℝ) ^ 2) * Real.exp (50 * (M : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_left h400 (Real.exp_nonneg _)
                _ = Real.exp (250 * (M : ℝ) ^ 2) := by rw [← Real.exp_add]; ring_nf
                _ ≤ (2 : ℝ) ^ (400 * M ^ 2) := h2pow
            have hd_log : 200 * (M : ℝ) ^ 2 ≤ d * Real.log (X_tail : ℝ) := by
              have h1 : d * ((2 ^ (400 * M ^ 2) : ℝ) * (1 / 2)) ≤ d * Real.log (X_tail : ℝ) :=
                mul_le_mul_of_nonneg_left hlogX hd_pos.le
              have h2 : 200 * (M : ℝ) ^ 2 ≤ d * ((2 ^ (400 * M ^ 2) : ℝ) * (1 / 2)) := by
                dsimp [d]
                rw [show (-200 * (M : ℝ) ^ 2) = -(200 * (M : ℝ) ^ 2) by ring, Real.exp_neg,
                    ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _)]
                linarith
              linarith
            exact Real.exp_le_exp.mpr (by linarith)
    have hdecomp : ∑' p : Nat.Primes, f p =
        (∑ p ∈ S_le, f p) + ∑' p : Nat.Primes, (if p ∈ S_le then 0 else f p) := by
      have h1 : ∀ p : Nat.Primes, f p =
          (if p ∈ S_le then f p else 0) + (if p ∈ S_le then 0 else f p) := by
        intro p; split_ifs <;> ring
      have hs1 : Summable (fun p : Nat.Primes => if p ∈ S_le then f p else 0) :=
        hf_sum.of_nonneg_of_le (fun p => by split_ifs; exact hf_nonneg p; exact le_rfl)
          (fun p => by split_ifs; exact le_rfl; exact hf_nonneg p)
      have hs2 : Summable (fun p : Nat.Primes => if p ∈ S_le then 0 else f p) :=
        hf_sum.of_nonneg_of_le (fun p => by split_ifs; exact le_rfl; exact hf_nonneg p)
          (fun p => by split_ifs; exact hf_nonneg p; exact le_rfl)
      rw [tsum_congr h1, hs1.tsum_add hs2]
      congr 1
      rw [tsum_eq_sum (s := S_le) (fun p hp => by simp [hp])]
      exact sum_congr rfl fun p hp => by simp [hp]
    linarith
  have hS_le_bound : ∑ p ∈ S_le, f p ≤
      (M : ℝ) + ∑ p ∈ (Ioc M X_tail).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]), (1 : ℝ) / p := by
    have hbij : ∑ p ∈ S_le, f p =
        ∑ p ∈ (Icc 1 X_tail).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]), (p : ℝ) ^ (-(1 + d)) := by
      dsimp [S_le]
      rw [Finset.sum_map]
      change ∑ x ∈ ((Icc 1 X_tail).filter Nat.Prime).attach,
          (if x.1 ≡ 1 [MOD q] then (x.1 : ℝ) ^ (-(1 + d)) else 0) = _
      rw [Finset.sum_attach ((Icc 1 X_tail).filter Nat.Prime)
          (fun p => if p ≡ 1 [MOD q] then (p : ℝ) ^ (-(1 + d)) else 0)]
      rw [← Finset.sum_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext p; simp only [mem_filter]; tauto
    rw [hbij]
    have hle_inv : ∑ p ∈ (Icc 1 X_tail).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]), (p : ℝ) ^ (-(1 + d)) ≤
        ∑ p ∈ (Icc 1 X_tail).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]), (1 : ℝ) / p := by
      refine sum_le_sum fun p hp => ?_
      rw [mem_filter] at hp
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.2.1.one_lt.le) (by linarith)
    refine hle_inv.trans ?_
    have hsplit_M : (Icc 1 X_tail).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]) =
        (Icc 1 M).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]) ∪
        (Ioc M X_tail).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]) := by
      ext p; simp only [mem_filter, mem_union, mem_Icc, mem_Ioc]
      by_cases hp : p.Prime ∧ p ≡ 1 [MOD q]
      · simp [hp]; omega
      · simp [hp]
    have hdisj_M : Disjoint ((Icc 1 M).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]))
        ((Ioc M X_tail).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q])) := by
      rw [Finset.disjoint_left]; intro p h1 h2; rw [mem_filter, mem_Icc] at h1; rw [mem_filter, mem_Ioc] at h2; omega
    rw [hsplit_M, sum_union hdisj_M]
    gcongr
    calc ∑ p ∈ (Icc 1 M).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]), (1 : ℝ) / p
        ≤ ∑ _p ∈ (Icc 1 M).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]), (1 : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_filter] at hp
          exact div_le_one_of_le₀ (by exact_mod_cast hp.2.1.one_lt.le) (by positivity)
      _ ≤ ∑ _p ∈ Icc 1 M, (1 : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => zero_le_one
      _ = (M : ℝ) := by simp
  linarith

/- ### Part 2: CRT prime-chain lower bound on h(n) -/

def S : ℕ → ℕ
  | 0 => 2
  | k + 1 => 2 ^ (2 ^ (400 * (S k) ^ 2))

lemma S_ge_two (k : ℕ) : 2 ≤ S k := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [S]
    have h1 : 1 ≤ 2 ^ (400 * S k ^ 2) := Nat.one_le_two_pow
    exact le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) h1)

lemma S_lt_succ (k : ℕ) : S k < S (k + 1) := by
  simp only [S]
  have h1 : S k < 2 ^ (S k) := Nat.lt_two_pow_self
  have h2 : S k ≤ 400 * (S k) ^ 2 := by nlinarith [S_ge_two k]
  have h3 : 2 ^ (S k) ≤ 2 ^ (400 * (S k) ^ 2) := Nat.pow_le_pow_right (by decide) h2
  have h4 : 2 ^ (400 * (S k) ^ 2) < 2 ^ (2 ^ (400 * (S k) ^ 2)) := Nat.lt_two_pow_self
  omega

lemma S_strictMono : StrictMono S := strictMono_nat_of_lt_succ S_lt_succ

lemma add_two_le_S (k : ℕ) : k + 2 ≤ S k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have := S_lt_succ k
    omega

def Pset (k : ℕ) : Finset ℕ := (Icc 1 (S k)).filter Nat.Prime

def Pprod (k : ℕ) : ℕ := ∏ p ∈ Pset k, p

def Qset (k : ℕ) : Finset ℕ := (Ioc (S k) (S (k + 1))).filter Nat.Prime

def Qprod (k : ℕ) : ℕ := ∏ p ∈ Qset k, p

lemma Pprod_pos (k : ℕ) : 0 < Pprod k :=
  Finset.prod_pos fun _p hp => (mem_filter.mp hp).2.pos

lemma Qprod_pos (k : ℕ) : 0 < Qprod k :=
  Finset.prod_pos fun _p hp => (mem_filter.mp hp).2.pos

lemma Pprod_succ (k : ℕ) : Pprod (k + 1) = Pprod k * Qprod k := by
  dsimp [Pprod, Qprod, Pset, Qset]
  have hdisj : Disjoint ((Icc 1 (S k)).filter Nat.Prime) ((Ioc (S k) (S (k + 1))).filter Nat.Prime) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    rw [mem_filter, mem_Icc] at h1; rw [mem_filter, mem_Ioc] at h2; omega
  rw [← Finset.prod_union hdisj]
  congr 1; ext p
  simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]
  have hlt := S_lt_succ k
  by_cases hp : p.Prime
  · simp [hp]; omega
  · simp [hp]

lemma coprime_Pprod_Qprod (k : ℕ) : Nat.Coprime (Pprod k) (Qprod k) := by
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  rw [Pset, mem_filter, mem_Icc] at hp
  rw [Qset, mem_filter, mem_Ioc] at hq
  exact (hp.2.coprime_iff_not_dvd.mpr fun hdvd => by
    have := (Nat.prime_dvd_prime_iff_eq hp.2 hq.2).mp hdvd
    omega)

/- CRT counting lemmas on Finset.range (a * b) -/

lemma card_filter_coprime_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hP₁ : ∀ x, P₁ (x % a) ↔ P₁ x) (hP₂ : ∀ x, P₂ (x % b) ↔ P₂ x) :
    ((Finset.range (a * b)).filter (fun n => P₁ n ∧ P₂ n)).card =
      ((Finset.range a).filter P₁).card * ((Finset.range b).filter P₂).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij (fun n _ => (n % a, n % b)) ?_ ?_ ?_
  · intro n hn
    rw [mem_filter, Finset.mem_range] at hn
    rw [mem_product, mem_filter, mem_filter, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt n ha, (hP₁ n).mpr hn.2.1⟩, ⟨Nat.mod_lt n hb, (hP₂ n).mpr hn.2.2⟩⟩
  · intro n₁ hn₁ n₂ hn₂ hEq
    rw [mem_filter, Finset.mem_range] at hn₁ hn₂
    simp only [Prod.mk.injEq] at hEq
    have hmod : n₁ ≡ n₂ [MOD a * b] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hEq.1, hEq.2⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt hn₁.1, Nat.mod_eq_of_lt hn₂.1] at hmod
    exact hmod
  · intro ⟨r₁, r₂⟩ hr
    rw [mem_product, mem_filter, mem_filter, Finset.mem_range, Finset.mem_range] at hr
    obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder hcop r₁ r₂
    refine ⟨n % (a * b), ?_, ?_⟩
    · rw [mem_filter, Finset.mem_range]
      have hma : (n % (a * b)) % a = r₁ := by
        rw [Nat.mod_mul_right_mod, hn1, Nat.mod_eq_of_lt hr.1.1]
      have hmb : (n % (a * b)) % b = r₂ := by
        rw [Nat.mod_mul_left_mod, hn2, Nat.mod_eq_of_lt hr.2.1]
      refine ⟨Nat.mod_lt n (mul_pos ha hb), ?_, ?_⟩
      · rw [← hP₁, hma]; exact hr.1.2
      · rw [← hP₂, hmb]; exact hr.2.2
    · simp only [Prod.mk.injEq]
      exact ⟨by rw [Nat.mod_mul_right_mod, hn1, Nat.mod_eq_of_lt hr.1.1],
             by rw [Nat.mod_mul_left_mod, hn2, Nat.mod_eq_of_lt hr.2.1]⟩

lemma card_filter_not_dvd_primes (B A : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (hAB : A ⊆ B) :
    ((Finset.range (∏ p ∈ B, p)).filter (fun n => ∀ p ∈ A, ¬ p ∣ n)).card =
      (∏ p ∈ B \ A, p) * ∏ p ∈ A, (p - 1) := by
  classical
  induction B using Finset.induction_on generalizing A with
  | empty =>
    have hA : A = ∅ := Finset.subset_empty.mp hAB
    subst hA; simp
  | @insert p s hps ih =>
    have hp : p.Prime := hB p (mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hB q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq => hp.coprime_iff_not_dvd.mpr fun hdvd =>
        hps ((Nat.prime_dvd_prime_iff_eq hp (hs q hq)).mp hdvd ▸ hq)
    have hs_pos : 0 < ∏ q ∈ s, q := Finset.prod_pos fun q hq => (hs q hq).pos
    rw [Finset.prod_insert hps]
    by_cases hpA : p ∈ A
    · set A' := A.erase p
      have hA'sub : A' ⊆ s := by
        intro q hq; have := mem_erase.mp hq
        have hmem := hAB this.2
        exact (mem_insert.mp hmem).resolve_left this.1
      have hiff : ∀ n, (∀ q ∈ A, ¬ q ∣ n) ↔ (¬ p ∣ n ∧ ∀ q ∈ A', ¬ q ∣ n) := by
        intro n; constructor
        · intro h; exact ⟨h p hpA, fun q hq => h q (mem_erase.mp hq).2⟩
        · rintro ⟨h1, h2⟩ q hq
          by_cases hqp : q = p
          · exact hqp ▸ h1
          · exact h2 q (mem_erase.mpr ⟨hqp, hq⟩)
      have hcongr : (Finset.range (p * ∏ q ∈ s, q)).filter (fun n => ∀ q ∈ A, ¬ q ∣ n) =
          (Finset.range (p * ∏ q ∈ s, q)).filter (fun n => ¬ p ∣ n ∧ ∀ q ∈ A', ¬ q ∣ n) :=
        Finset.filter_congr fun n _ => hiff n
      rw [hcongr, card_filter_coprime_mul hp.pos hs_pos hcop
          (fun n => ¬ p ∣ n) (fun n => ∀ q ∈ A', ¬ q ∣ n)
          (fun x => by simp [Nat.dvd_iff_mod_eq_zero])
          (fun x => by
            refine forall₂_congr fun q hq => ?_
            have hdvd : q ∣ ∏ r ∈ s, r := Finset.dvd_prod_of_mem _ (hA'sub hq)
            simp [Nat.dvd_mod_iff hdvd])]
      have hcard_p : ((Finset.range p).filter (fun n => ¬ p ∣ n)).card = p - 1 := by
        have hfeq : (Finset.range p).filter (fun n => ¬ p ∣ n) = Ico 1 p := by
          ext n; simp only [mem_filter, Finset.mem_range, mem_Ico]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨?_, h1⟩
            by_contra h0; push Not at h0
            have : n = 0 := by omega
            subst this; exact h2 (dvd_zero p)
          · rintro ⟨h1, h2⟩
            exact ⟨h2, fun hdvd => by have := Nat.le_of_dvd (by omega) hdvd; omega⟩
        rw [hfeq, Nat.card_Ico]
      rw [hcard_p, ih A' hs hA'sub]
      have hsdiff : insert p s \ A = s \ A' := by
        ext q
        by_cases hqp : q = p
        · subst hqp; simp [A', hpA, hps]
        · simp [A', hqp]
      have hAeq : ∏ q ∈ A, (q - 1) = (p - 1) * ∏ q ∈ A', (q - 1) :=
        (Finset.mul_prod_erase A (fun q => q - 1) hpA).symm
      rw [hsdiff, hAeq]; ring
    · have hAsub : A ⊆ s := by
        intro q hq
        have hmem := hAB hq
        exact (mem_insert.mp hmem).resolve_left (fun h => hpA (h ▸ hq))
      have hcongr : (Finset.range (p * ∏ q ∈ s, q)).filter (fun n => ∀ q ∈ A, ¬ q ∣ n) =
          (Finset.range (p * ∏ q ∈ s, q)).filter (fun n => True ∧ ∀ q ∈ A, ¬ q ∣ n) :=
        Finset.filter_congr fun _ _ => by simp
      rw [hcongr, card_filter_coprime_mul hp.pos hs_pos hcop
          (fun _ => True) (fun n => ∀ q ∈ A, ¬ q ∣ n)
          (fun _ => Iff.rfl)
          (fun x => by
            refine forall₂_congr fun q hq => ?_
            have hdvd : q ∣ ∏ r ∈ s, r := Finset.dvd_prod_of_mem _ (hAsub hq)
            simp [Nat.dvd_mod_iff hdvd])]
      simp only [Finset.filter_true, Finset.card_range, ih A hs hAsub]
      have hsdiff : insert p s \ A = insert p (s \ A) := by
        ext q
        by_cases hqp : q = p
        · subst hqp; simp [hpA]
        · simp [hqp]
      have hpnot : p ∉ s \ A := fun h => hps (mem_sdiff.mp h).1
      rw [hsdiff, Finset.prod_insert hpnot]; ring

/- Greedy prime chain selector stepPrime k n -/

noncomputable def stepPrime : ℕ → ℕ → Option ℕ
  | 0, n => if 2 ∣ n then some 2 else none
  | k + 1, n =>
    match stepPrime k n with
    | none => none
    | some q =>
      let cand := (Qset k).filter (fun p => p ≡ 1 [MOD q] ∧ p ∣ n)
      if h : cand.Nonempty then some (cand.min' h) else none

lemma stepPrime_mod (k n : ℕ) : stepPrime k (n % Pprod k) = stepPrime k n := by
  induction k generalizing n with
  | zero =>
    have h2 : 2 ∈ Pset 0 := mem_filter.mpr ⟨mem_Icc.mpr ⟨by decide, by decide⟩, Nat.prime_two⟩
    have hdvd : 2 ∣ Pprod 0 := Finset.dvd_prod_of_mem _ h2
    simp only [stepPrime, Nat.dvd_mod_iff hdvd]
  | succ k ih =>
    have hPk_dvd : Pprod k ∣ Pprod (k + 1) := by rw [Pprod_succ]; exact dvd_mul_right _ _
    have hmod_k : (n % Pprod (k + 1)) % Pprod k = n % Pprod k := Nat.mod_mod_of_dvd n hPk_dvd
    simp only [stepPrime]
    rw [← ih (n % Pprod (k + 1)), hmod_k, ih n]
    cases stepPrime k n with
    | none => rfl
    | some q =>
      have hcand_eq : (Qset k).filter (fun p => p ≡ 1 [MOD q] ∧ p ∣ n % Pprod (k + 1)) =
          (Qset k).filter (fun p => p ≡ 1 [MOD q] ∧ p ∣ n) := by
        refine Finset.filter_congr fun p hp => ?_
        have hp_dvd : p ∣ Pprod (k + 1) := by
          rw [Pprod_succ]
          exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) _
        rw [Nat.dvd_mod_iff hp_dvd]
      simp only [hcand_eq]

lemma stepPrime_spec (k n q : ℕ) (hq : stepPrime k n = some q) :
    q.Prime ∧ q ≤ S k ∧
      ∃ s : List ℕ, s.length = k + 1 ∧ ValidChain n Nat.Prime s ∧ s.getLast? = some q := by
  induction k generalizing q with
  | zero =>
    simp only [stepPrime] at hq
    split_ifs at hq with h2
    · injection hq with hq2; subst hq2
      refine ⟨Nat.prime_two, le_rfl, [2], rfl, ?_, rfl⟩
      exact ⟨by simp, fun d hd => by simp at hd; subst hd; exact ⟨h2, Nat.prime_two⟩⟩
  | succ k ih =>
    simp only [stepPrime] at hq
    cases hprev : stepPrime k n with
    | none => rw [hprev] at hq; cases hq
    | some q₀ =>
      rw [hprev] at hq
      dsimp only at hq
      split_ifs at hq with hne
      · injection hq with hq_eq; subst hq_eq
        set p := ((Qset k).filter (fun p => p ≡ 1 [MOD q₀] ∧ p ∣ n)).min' hne
        have hp_mem : p ∈ (Qset k).filter (fun p => p ≡ 1 [MOD q₀] ∧ p ∣ n) := Finset.min'_mem _ hne
        rw [mem_filter, Qset, mem_filter, mem_Ioc] at hp_mem
        obtain ⟨⟨⟨hp_gt, hp_le⟩, hp_prime⟩, hp_mod, hp_dvd⟩ := hp_mem
        obtain ⟨hq₀_prime, hq₀_le, s, hslen, hsvalid, hslast⟩ := ih q₀ hprev
        refine ⟨hp_prime, hp_le, s ++ [p], by simp [hslen], ?_, by simp⟩
        refine ⟨?_, ?_⟩
        · have hsne : s ≠ [] := by intro he; rw [he] at hslen; simp at hslen
          have hlast_eq : s.getLast hsne = q₀ := by
            rw [List.getLast?_eq_some_getLast hsne] at hslast
            exact Option.some.inj hslast
          rw [List.isChain_append]
          refine ⟨hsvalid.1, by simp, fun x hx y hy => ?_⟩
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          rw [List.getLast?_eq_some_getLast hsne, Option.mem_def, Option.some.injEq] at hx
          subst hy; rw [← hx, hlast_eq]
          exact ⟨lt_of_le_of_lt hq₀_le hp_gt, hp_mod⟩
        · intro d hd
          rcases List.mem_append.mp hd with hds | hdp
          · exact hsvalid.2 d hds
          · simp at hdp; subst hdp; exact ⟨hp_dvd, hp_prime⟩

lemma validChain_length_le_n {n : ℕ} (hn : 1 ≤ n) {P : ℕ → Prop} {s : List ℕ}
    (hs : ValidChain n P s) : s.length ≤ n := by
  have hs_lt : s.Pairwise (· < ·) := by
    have : IsTrans ℕ (· < ·) := ⟨fun _ _ _ => lt_trans⟩
    exact List.isChain_iff_pairwise.mp (hs.1.imp fun _ _ h => h.1)
  have hnodup : s.Nodup := hs_lt.imp ne_of_lt
  have hsub : s.toFinset ⊆ Icc 1 n := by
    intro d hd
    rw [List.mem_toFinset] at hd
    have hdvd := (hs.2 d hd).1
    rw [mem_Icc]
    exact ⟨Nat.pos_of_dvd_of_pos hdvd (by omega), Nat.le_of_dvd (by omega) hdvd⟩
  calc s.length = s.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (Icc 1 n).card := Finset.card_le_card hsub
    _ = n := by simp

lemma stepPrime_implies_h_ge {k n : ℕ} (hn : 1 ≤ n) (hgood : (stepPrime k n).isSome) :
    k + 1 ≤ h n := by
  classical
  cases hsp : stepPrime k n with
  | none => simp [hsp] at hgood
  | some q =>
    obtain ⟨_, _, s, hslen, hsvalid, _⟩ := stepPrime_spec k n q hsp
    have hle : k + 1 ≤ n := hslen ▸ validChain_length_le_n hn hsvalid
    exact Nat.le_findGreatest hle ⟨s, hslen, hsvalid⟩

/- Density recurrence for good residues mod Pprod k -/

lemma good_residue_density_step (k : ℕ) :
    (((Finset.range (Pprod (k + 1))).filter (fun r => (stepPrime (k + 1) r).isSome)).card : ℝ) /
        (Pprod (k + 1) : ℝ) ≥
      (((Finset.range (Pprod k)).filter (fun r => (stepPrime k r).isSome)).card : ℝ) /
        (Pprod k : ℝ) - Real.exp (-2 * ((k + 2 : ℕ) : ℝ)) := by
  have hPk_pos : 0 < Pprod k := Pprod_pos k
  have hQk_pos : 0 < Qprod k := Qprod_pos k
  have hcop : Nat.Coprime (Pprod k) (Qprod k) := coprime_Pprod_Qprod k
  let goodK := (Finset.range (Pprod k)).filter (fun r => (stepPrime k r).isSome)
  -- Partition good residues mod P(k+1) by their residue r₁ mod P(k)
  have hcard_eq : ((Finset.range (Pprod (k + 1))).filter (fun r => (stepPrime (k + 1) r).isSome)).card =
      ∑ r₁ ∈ goodK, ((Finset.range (Qprod k)).filter (fun r₂ =>
        ∃ p ∈ Qset k, p ≡ 1 [MOD (stepPrime k r₁).getD 2] ∧ p ∣ r₂)).card := by
    rw [Pprod_succ]
    have hbij : ((Finset.range (Pprod k * Qprod k)).filter (fun r => (stepPrime (k + 1) r).isSome)).card =
        ∑ r₁ ∈ goodK, ((Finset.range (Pprod k * Qprod k)).filter
          (fun r => r % Pprod k = r₁ ∧ (stepPrime (k + 1) r).isSome)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext r
        simp only [mem_filter, Finset.mem_range, mem_biUnion, goodK]
        constructor
        · intro ⟨hr, hsp⟩
          have hspk : (stepPrime k r).isSome := by
            simp only [stepPrime] at hsp
            cases h0 : stepPrime k r <;> simp [h0] at hsp ⊢
          refine ⟨r % Pprod k, ⟨Nat.mod_lt r hPk_pos, ?_⟩, hr, rfl, hsp⟩
          rwa [stepPrime_mod]
        · rintro ⟨r₁, _, hr, _, hsp⟩; exact ⟨hr, hsp⟩
      · intro r₁ _ r₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]; intro r h1 h2
        rw [mem_filter] at h1 h2; exact hne (h1.2.1.symm.trans h2.2.1)
    rw [hbij]
    refine sum_congr rfl fun r₁ hr₁ => ?_
    rw [mem_filter] at hr₁
    cases hq : stepPrime k r₁ with
    | none => simp [hq] at hr₁
    | some q =>
      have hcongr : (Finset.range (Pprod k * Qprod k)).filter
          (fun r => r % Pprod k = r₁ ∧ (stepPrime (k + 1) r).isSome) =
          (Finset.range (Pprod k * Qprod k)).filter
            (fun r => r % Pprod k = r₁ ∧ ∃ p ∈ Qset k, p ≡ 1 [MOD q] ∧ p ∣ r) := by
        refine Finset.filter_congr fun r _ => ?_
        constructor <;> rintro ⟨hrmod, h2⟩
        · refine ⟨hrmod, ?_⟩
          have hspr : stepPrime k r = some q := by rw [← stepPrime_mod, hrmod, hq]
          simp only [stepPrime, hspr] at h2
          split_ifs at h2 with hne
          · obtain ⟨p, hp⟩ := hne
            rw [mem_filter] at hp
            exact ⟨p, hp.1, hp.2.1, hp.2.2⟩
          · simp at h2
        · refine ⟨hrmod, ?_⟩
          have hspr : stepPrime k r = some q := by rw [← stepPrime_mod, hrmod, hq]
          simp only [stepPrime, hspr]
          obtain ⟨p, hpQ, hpmod, hpdvd⟩ := h2
          have hne : ((Qset k).filter (fun p => p ≡ 1 [MOD q] ∧ p ∣ r)).Nonempty :=
            ⟨p, mem_filter.mpr ⟨hpQ, hpmod, hpdvd⟩⟩
          simp [hne]
      rw [hcongr, card_filter_coprime_mul hPk_pos hQk_pos hcop
          (fun r => r % Pprod k = r₁)
          (fun r => ∃ p ∈ Qset k, p ≡ 1 [MOD q] ∧ p ∣ r)
          (fun x => by simp)
          (fun x => by
            refine exists_congr fun p => and_congr_right fun hp => and_congr_right fun _ => ?_
            exact Nat.dvd_mod_iff (Finset.dvd_prod_of_mem _ hp))]
      have h1 : ((Finset.range (Pprod k)).filter (fun r => r % Pprod k = r₁)).card = 1 := by
        have hr₁_lt : r₁ < Pprod k := Finset.mem_range.mp hr₁.1
        have : (Finset.range (Pprod k)).filter (fun r => r % Pprod k = r₁) = {r₁} := by
          ext r; simp only [mem_filter, Finset.mem_range, mem_singleton]
          constructor
          · rintro ⟨hr, hmod⟩; rw [Nat.mod_eq_of_lt hr] at hmod; exact hmod
          · rintro rfl; exact ⟨hr₁_lt, Nat.mod_eq_of_lt hr₁_lt⟩
        rw [this, card_singleton]
      rw [h1, one_mul]
      simp
  -- Bound each inner fiber card >= (1 - exp(-2*(k+2))) * Qprod k
  have hfiber : ∀ r₁ ∈ goodK,
      (1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) * (Qprod k : ℝ) ≤
        (((Finset.range (Qprod k)).filter (fun r₂ =>
          ∃ p ∈ Qset k, p ≡ 1 [MOD (stepPrime k r₁).getD 2] ∧ p ∣ r₂)).card : ℝ) := by
    intro r₁ hr₁
    rw [mem_filter] at hr₁
    cases hq : stepPrime k r₁ with
    | none => simp [hq] at hr₁
    | some q =>
      simp only [Option.getD_some]
      obtain ⟨hq_prime, hq_le, _, _, _, _⟩ := stepPrime_spec k r₁ q hq
      set A := (Qset k).filter (fun p => p ≡ 1 [MOD q])
      have hAsub : A ⊆ Qset k := filter_subset _ _
      have hcomp : ((Finset.range (Qprod k)).filter (fun r₂ => ∃ p ∈ Qset k, p ≡ 1 [MOD q] ∧ p ∣ r₂)).card +
          ((Finset.range (Qprod k)).filter (fun r₂ => ∀ p ∈ A, ¬ p ∣ r₂)).card = Qprod k := by
        have hfeq : (Finset.range (Qprod k)).filter (fun r₂ => ∀ p ∈ A, ¬ p ∣ r₂) =
            (Finset.range (Qprod k)).filter (fun r₂ => ¬ ∃ p ∈ Qset k, p ≡ 1 [MOD q] ∧ p ∣ r₂) := by
          refine Finset.filter_congr fun r₂ _ => ?_
          simp only [A, mem_filter, not_exists, not_and]
          exact ⟨fun h p hp hmod hdvd => h p ⟨hp, hmod⟩ hdvd,
                 fun h p ⟨hp, hmod⟩ hdvd => h p hp hmod hdvd⟩
        rw [hfeq]
        have hsum := Finset.sum_filter_add_sum_filter_not (Finset.range (Qprod k))
          (fun r₂ => ∃ p ∈ Qset k, p ≡ 1 [MOD q] ∧ p ∣ r₂) (fun _ => (1 : ℕ))
        simpa using hsum
      have hbad_card := card_filter_not_dvd_primes (Qset k) A (fun p hp => (mem_filter.mp hp).2) hAsub
      have hbad_ratio : (((Finset.range (Qprod k)).filter (fun r₂ => ∀ p ∈ A, ¬ p ∣ r₂)).card : ℝ) /
          (Qprod k : ℝ) = ∏ p ∈ A, (1 - (1 : ℝ) / p) := by
        dsimp [Qprod]
        rw [hbad_card]
        have hQsplit : (∏ p ∈ Qset k, p) = (∏ p ∈ Qset k \ A, p) * ∏ p ∈ A, p :=
          (Finset.prod_sdiff hAsub).symm
        rw [hQsplit, Nat.cast_mul, Nat.cast_mul]
        have hpos1 : ((∏ p ∈ Qset k \ A, p : ℕ) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Finset.prod_pos fun p hp => (mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.pos).ne'
        rw [mul_div_mul_left _ _ hpos1, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (mem_filter.mp (hAsub hp)).2.pos
        have hp1 : 1 ≤ p := (mem_filter.mp (hAsub hp)).2.pos
        rw [Nat.cast_sub hp1, Nat.cast_one, sub_div, div_self hp_pos.ne']
      have hprod_le_exp : ∏ p ∈ A, (1 - (1 : ℝ) / p) ≤ Real.exp (- ∑ p ∈ A, (1 : ℝ) / p) := by
        rw [← Finset.sum_neg_distrib, Real.exp_sum]
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
        · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp (hAsub hp)).2.pos
          have : (1 : ℝ) / p ≤ 1 := div_le_one_of_le₀ hp1 (by positivity)
          linarith
        · have := Real.add_one_le_exp (-((1 : ℝ) / p))
          linarith
      have hsum_ge : 2 * ((k + 2 : ℕ) : ℝ) ≤ ∑ p ∈ A, (1 : ℝ) / p := by
        have hAeq : A = (Ioc (S k) (S (k + 1))).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]) := by
          ext p; simp only [A, Qset, mem_filter]; tauto
        rw [hAeq]
        have h1 := prime_ap_sum_ge hq_prime hq_le
        have hS : S (k + 1) = 2 ^ (2 ^ (400 * (S k) ^ 2)) := rfl
        have h2 : ((k + 2 : ℕ) : ℝ) ≤ (S k : ℝ) := by exact_mod_cast add_two_le_S k
        rw [hS]; linarith
      have hexp_le : ∏ p ∈ A, (1 - (1 : ℝ) / p) ≤ Real.exp (-2 * ((k + 2 : ℕ) : ℝ)) :=
        hprod_le_exp.trans (Real.exp_le_exp.mpr (by linarith))
      have hbad_le : (((Finset.range (Qprod k)).filter (fun r₂ => ∀ p ∈ A, ¬ p ∣ r₂)).card : ℝ) ≤
          Real.exp (-2 * ((k + 2 : ℕ) : ℝ)) * (Qprod k : ℝ) := by
        rw [← div_le_iff₀ (Nat.cast_pos.mpr hQk_pos), hbad_ratio]
        exact hexp_le
      have hcomp_r : (((Finset.range (Qprod k)).filter (fun r₂ => ∃ p ∈ Qset k, p ≡ 1 [MOD q] ∧ p ∣ r₂)).card : ℝ) +
          (((Finset.range (Qprod k)).filter (fun r₂ => ∀ p ∈ A, ¬ p ∣ r₂)).card : ℝ) = (Qprod k : ℝ) := by
        exact_mod_cast hcomp
      linarith
  have hsum_fiber : (goodK.card : ℝ) * ((1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) * (Qprod k : ℝ)) ≤
      (((Finset.range (Pprod (k + 1))).filter (fun r => (stepPrime (k + 1) r).isSome)).card : ℝ) := by
    rw [hcard_eq, Nat.cast_sum]
    calc (goodK.card : ℝ) * ((1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) * (Qprod k : ℝ))
        = ∑ _r₁ ∈ goodK, ((1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) * (Qprod k : ℝ)) := by simp
      _ ≤ ∑ r₁ ∈ goodK, (((Finset.range (Qprod k)).filter (fun r₂ =>
            ∃ p ∈ Qset k, p ≡ 1 [MOD (stepPrime k r₁).getD 2] ∧ p ∣ r₂)).card : ℝ) :=
          sum_le_sum hfiber
  have hPk_r : (0 : ℝ) < Pprod k := Nat.cast_pos.mpr hPk_pos
  have hQk_r : (0 : ℝ) < Qprod k := Nat.cast_pos.mpr hQk_pos
  have hratio_le1 : (goodK.card : ℝ) / (Pprod k : ℝ) ≤ 1 := by
    rw [div_le_one hPk_r]
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hdiv : ((goodK.card : ℝ) / (Pprod k : ℝ)) * (1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) ≤
      (((Finset.range (Pprod (k + 1))).filter (fun r => (stepPrime (k + 1) r).isSome)).card : ℝ) /
        (Pprod (k + 1) : ℝ) := by
    have hP_r : (Pprod (k + 1) : ℝ) = (Pprod k : ℝ) * (Qprod k : ℝ) := by
      rw [Pprod_succ]; push_cast; rfl
    rw [hP_r, le_div_iff₀ (mul_pos hPk_r hQk_r)]
    have hident : ((goodK.card : ℝ) / (Pprod k : ℝ)) * (1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) *
        ((Pprod k : ℝ) * (Qprod k : ℝ)) =
        (goodK.card : ℝ) * ((1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) * (Qprod k : ℝ)) := by
      field_simp [hPk_r.ne']
    linarith
  have hge : (goodK.card : ℝ) / (Pprod k : ℝ) - Real.exp (-2 * ((k + 2 : ℕ) : ℝ)) ≤
      ((goodK.card : ℝ) / (Pprod k : ℝ)) * (1 - Real.exp (-2 * ((k + 2 : ℕ) : ℝ))) := by
    nlinarith [Real.exp_pos (-2 * ((k + 2 : ℕ) : ℝ))]
  exact ge_iff_le.mpr (hge.trans hdiv)

lemma good_residue_density_ge (k : ℕ) :
    (45 / 100 : ℝ) ≤
      (((Finset.range (Pprod k)).filter (fun r => (stepPrime k r).isSome)).card : ℝ) / (Pprod k : ℝ) := by
  have hbase : (1 / 2 : ℝ) ≤
      (((Finset.range (Pprod 0)).filter (fun r => (stepPrime 0 r).isSome)).card : ℝ) / (Pprod 0 : ℝ) := by
    have hP0 : Pprod 0 = 2 := by
      have : Pset 0 = {2} := by
        ext p; simp only [Pset, S, mem_filter, mem_Icc, mem_singleton]
        constructor
        · rintro ⟨⟨h1, h2⟩, hp⟩; have := hp.two_le; omega
        · rintro rfl; exact ⟨⟨by decide, by decide⟩, Nat.prime_two⟩
      simp [Pprod, this]
    rw [hP0]
    have h0mem : 0 ∈ (Finset.range 2).filter (fun r => (stepPrime 0 r).isSome) := by
      simp [stepPrime]
    have h1 : 1 ≤ ((Finset.range 2).filter (fun r => (stepPrime 0 r).isSome)).card :=
      Finset.card_pos.mpr ⟨0, h0mem⟩
    have h1r : (1 : ℝ) ≤ (((Finset.range 2).filter (fun r => (stepPrime 0 r).isSome)).card : ℝ) := by
      exact_mod_cast h1
    push_cast; linarith
  have hind : ∀ m : ℕ, (1 / 2 : ℝ) - ∑ j ∈ Finset.range m, Real.exp (-2 * ((j + 2 : ℕ) : ℝ)) ≤
      (((Finset.range (Pprod m)).filter (fun r => (stepPrime m r).isSome)).card : ℝ) / (Pprod m : ℝ) := by
    intro m
    induction m with
    | zero => simpa using hbase
    | succ m ih =>
      rw [Finset.sum_range_succ]
      linarith [good_residue_density_step m]
  have hgeom : ∑ j ∈ Finset.range k, Real.exp (-2 * ((j + 2 : ℕ) : ℝ)) ≤ 1 / 20 := by
    have he2 : Real.exp (-2 : ℝ) ≤ 1 / 6 := by
      rw [Real.exp_neg, ← one_div, one_div_le_one_div (Real.exp_pos 2) (by norm_num)]
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
      norm_num [Finset.sum_range_succ, Nat.factorial] at h
      linarith
    have hterm : ∀ j ∈ Finset.range k,
        Real.exp (-2 * ((j + 2 : ℕ) : ℝ)) ≤ (1 / 36 : ℝ) * (1 / 6 : ℝ) ^ j := by
      intro j _
      have hexp : Real.exp (-2 * ((j + 2 : ℕ) : ℝ)) = Real.exp (-2 : ℝ) ^ 2 * Real.exp (-2 : ℝ) ^ j := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1; push_cast; ring
      rw [hexp]
      have hsq : Real.exp (-2 : ℝ) ^ 2 ≤ (1 / 6 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_nonneg _) he2 2
      have hpow : Real.exp (-2 : ℝ) ^ j ≤ (1 / 6 : ℝ) ^ j :=
        pow_le_pow_left₀ (Real.exp_nonneg _) he2 j
      calc Real.exp (-2 : ℝ) ^ 2 * Real.exp (-2 : ℝ) ^ j
          ≤ (1 / 6 : ℝ) ^ 2 * (1 / 6 : ℝ) ^ j := mul_le_mul hsq hpow (by positivity) (by positivity)
        _ = (1 / 36 : ℝ) * (1 / 6 : ℝ) ^ j := by norm_num
    calc ∑ j ∈ Finset.range k, Real.exp (-2 * ((j + 2 : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.range k, (1 / 36 : ℝ) * (1 / 6 : ℝ) ^ j := sum_le_sum hterm
      _ = (1 / 36 : ℝ) * ∑ j ∈ Finset.range k, (1 / 6 : ℝ) ^ j := by rw [← mul_sum]
      _ ≤ (1 / 36 : ℝ) * (6 / 5 : ℝ) := by
          gcongr
          rw [geom_sum_eq (by norm_num : (1 / 6 : ℝ) ≠ 1)]
          have h0 : (0 : ℝ) ≤ (1 / 6 : ℝ) ^ k := by positivity
          have heq : ((1 / 6 : ℝ) ^ k - 1) / (1 / 6 - 1) = (6 / 5 : ℝ) * (1 - (1 / 6 : ℝ) ^ k) := by ring
          linarith
      _ ≤ 1 / 20 := by norm_num
  linarith [hind k]

lemma Pprod_le_div_100 (k : ℕ) : 100 * Pprod k ≤ S (k + 1) := by
  have hP_le : Pprod k ≤ (S k) ^ (S k) := by
    dsimp [Pprod]
    calc ∏ p ∈ Pset k, p
        ≤ ∏ _p ∈ Pset k, S k := Finset.prod_le_prod' fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2
      _ = (S k) ^ (Pset k).card := by simp
      _ ≤ (S k) ^ (S k) := by
          apply Nat.pow_le_pow_right (by linarith [S_ge_two k])
          calc (Pset k).card ≤ (Icc 1 (S k)).card := Finset.card_le_card (filter_subset _ _)
            _ = S k := by simp
  have hSk : 2 ≤ S k := S_ge_two k
  have hSk_le_pow : S k ≤ 2 ^ (S k) := (Nat.lt_two_pow_self).le
  have h1 : (S k) ^ (S k) ≤ 2 ^ ((S k) ^ 2) := by
    calc (S k) ^ (S k) ≤ (2 ^ (S k)) ^ (S k) := Nat.pow_le_pow_left hSk_le_pow _
      _ = 2 ^ ((S k) * (S k)) := (Nat.pow_mul 2 _ _).symm
      _ = 2 ^ ((S k) ^ 2) := by rw [sq]
  have h100 : 100 ≤ 2 ^ 7 := by decide
  have h2 : 100 * (S k) ^ (S k) ≤ 2 ^ (7 + (S k) ^ 2) := by
    calc 100 * (S k) ^ (S k) ≤ 2 ^ 7 * 2 ^ ((S k) ^ 2) := Nat.mul_le_mul h100 h1
      _ = 2 ^ (7 + (S k) ^ 2) := (Nat.pow_add 2 _ _).symm
  have h3 : 7 + (S k) ^ 2 ≤ 2 ^ (400 * (S k) ^ 2) := by
    have hlt := Nat.lt_two_pow_self (n := 400 * (S k) ^ 2)
    nlinarith
  exact (Nat.mul_le_mul_left 100 hP_le).trans (h2.trans (Nat.pow_le_pow_right (by decide) h3))

lemma S_succ_ge_1000 (k : ℕ) : 1000 ≤ S (k + 1) := by
  rw [S]
  have h1 : 10 ≤ 400 * (S k) ^ 2 := by nlinarith [S_ge_two k]
  have h2 : 10 ≤ 2 ^ (400 * (S k) ^ 2) := h1.trans (Nat.lt_two_pow_self).le
  exact (show 1000 ≤ 2 ^ 10 by norm_num).trans (Nat.pow_le_pow_right (by decide) h2)

lemma card_h_ge_lower (k : ℕ) :
    (43 / 100 : ℝ) * (S (k + 1) : ℝ) ≤
      (((Finset.range (S (k + 1))).filter (fun n => 1 ≤ n ∧ k + 1 ≤ h n)).card : ℝ) := by
  set P := Pprod k
  set N := S (k + 1)
  have hP_pos : 0 < P := Pprod_pos k
  have h100P : 100 * P ≤ N := Pprod_le_div_100 k
  set q := N / P
  have hqP_le : q * P ≤ N := Nat.div_mul_le_self N P
  have hqP_ge : N - P ≤ q * P := by
    have hdiv := Nat.div_add_mod N P
    have hmod := Nat.mod_lt N hP_pos
    have hcomm : P * (N / P) = q * P := by dsimp [q]; ring
    omega
  -- Count good n in [0, q * P) by splitting into q blocks of length P
  have hgood_blocks :
      q * ((Finset.range P).filter (fun r => (stepPrime k r).isSome)).card ≤
        ((Finset.range N).filter (fun n => (stepPrime k n).isSome)).card := by
    let emb : ℕ → ℕ ↪ ℕ := fun j => ⟨fun r => P * j + r, fun _ _ h => Nat.add_left_cancel h⟩
    have hsub : (Finset.range q).biUnion (fun j =>
        ((Finset.range P).filter (fun r => (stepPrime k r).isSome)).map (emb j)) ⊆
        (Finset.range N).filter (fun n => (stepPrime k n).isSome) := by
      intro n hn
      rcases mem_biUnion.mp hn with ⟨j, hj, hnr⟩
      rcases Finset.mem_map.mp hnr with ⟨r, hr, rfl⟩
      rw [Finset.mem_range] at hj
      rw [mem_filter, Finset.mem_range] at hr ⊢
      change P * j + r < N ∧ (stepPrime k (P * j + r)).isSome
      refine ⟨?_, ?_⟩
      · have h1 : P * j + r < P * (j + 1) := by rw [Nat.mul_add, mul_one]; omega
        have h2 : P * (j + 1) ≤ P * q := Nat.mul_le_mul_left P hj
        have h3 : P * q = q * P := mul_comm P q
        omega
      · rw [← stepPrime_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hr.1]
        exact hr.2
    have hdisj : Set.PairwiseDisjoint (Finset.range q : Set ℕ) (fun j =>
        ((Finset.range P).filter (fun r => (stepPrime k r).isSome)).map (emb j)) := by
      intro j₁ _ j₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro n h1 h2
      rcases Finset.mem_map.mp h1 with ⟨r₁, hr₁, rfl⟩
      rcases Finset.mem_map.mp h2 with ⟨r₂, hr₂, hEq⟩
      rw [mem_filter, Finset.mem_range] at hr₁ hr₂
      change P * j₂ + r₂ = P * j₁ + r₁ at hEq
      have hdiv1 : (P * j₁ + r₁) / P = j₁ := by
        rw [Nat.mul_add_div hP_pos, Nat.div_eq_of_lt hr₁.1, add_zero]
      have hdiv2 : (P * j₂ + r₂) / P = j₂ := by
        rw [Nat.mul_add_div hP_pos, Nat.div_eq_of_lt hr₂.1, add_zero]
      exact hne (by rw [← hdiv1, ← hdiv2, hEq])
    have hcard_u := Finset.card_biUnion hdisj
    calc q * ((Finset.range P).filter (fun r => (stepPrime k r).isSome)).card
        = ∑ _j ∈ Finset.range q, ((Finset.range P).filter (fun r => (stepPrime k r).isSome)).card := by simp
      _ = ((Finset.range q).biUnion (fun j =>
            ((Finset.range P).filter (fun r => (stepPrime k r).isSome)).map (emb j))).card := by
          rw [hcard_u]; refine sum_congr rfl fun _ _ => (Finset.card_map _).symm
      _ ≤ ((Finset.range N).filter (fun n => (stepPrime k n).isSome)).card := Finset.card_le_card hsub
  have hremove0 : ((Finset.range N).filter (fun n => (stepPrime k n).isSome)).card ≤
      ((Finset.range N).filter (fun n => 1 ≤ n ∧ k + 1 ≤ h n)).card + 1 := by
    have hsub : (Finset.range N).filter (fun n => (stepPrime k n).isSome) ⊆
        insert 0 ((Finset.range N).filter (fun n => 1 ≤ n ∧ k + 1 ≤ h n)) := by
      intro n hn
      rw [mem_filter, Finset.mem_range] at hn
      by_cases hn0 : n = 0
      · subst hn0; exact mem_insert_self 0 _
      · exact mem_insert_of_mem (mem_filter.mpr ⟨Finset.mem_range.mpr hn.1, by omega,
          stepPrime_implies_h_ge (by omega) hn.2⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hdens := good_residue_density_ge k
  have hP_r : (0 : ℝ) < P := Nat.cast_pos.mpr hP_pos
  have hgood_r : (45 / 100 : ℝ) * (P : ℝ) ≤
      (((Finset.range P).filter (fun r => (stepPrime k r).isSome)).card : ℝ) := by
    rwa [le_div_iff₀ hP_r] at hdens
  have hqP_r : (99 / 100 : ℝ) * (N : ℝ) ≤ (q : ℝ) * (P : ℝ) := by
    have h100_r : 100 * (P : ℝ) ≤ (N : ℝ) := by exact_mod_cast h100P
    have hge_r : (N : ℝ) - (P : ℝ) ≤ (q : ℝ) * (P : ℝ) := by
      have : N ≤ q * P + P := by omega
      have hcast : (N : ℝ) ≤ (q : ℝ) * (P : ℝ) + (P : ℝ) := by exact_mod_cast this
      linarith
    linarith
  have hN_big : (1000 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast S_succ_ge_1000 k
  have hblocks_r : (q : ℝ) * (((Finset.range P).filter (fun r => (stepPrime k r).isSome)).card : ℝ) ≤
      (((Finset.range N).filter (fun n => (stepPrime k n).isSome)).card : ℝ) := by
    exact_mod_cast hgood_blocks
  have hrem_r : (((Finset.range N).filter (fun n => (stepPrime k n).isSome)).card : ℝ) ≤
      (((Finset.range N).filter (fun n => 1 ≤ n ∧ k + 1 ≤ h n)).card : ℝ) + 1 := by
    exact_mod_cast hremove0
  have hmul : (q : ℝ) * ((45 / 100 : ℝ) * (P : ℝ)) ≤
      (q : ℝ) * (((Finset.range P).filter (fun r => (stepPrime k r).isSome)).card : ℝ) :=
    mul_le_mul_of_nonneg_left hgood_r (Nat.cast_nonneg q)
  nlinarith

/- ### Part 3: Elementary tower upper bound on H(n) -/

def T : ℕ → ℕ
  | 0 => 10 ^ 6
  | k + 1 => 2 ^ (Nat.sqrt (T k))

lemma T_ge_base (k : ℕ) : 10 ^ 6 ≤ T k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [T]
    have hsq : 1000 ≤ Nat.sqrt (T k) := by
      rw [Nat.le_sqrt]; nlinarith
    exact le_trans (by decide : 10 ^ 6 ≤ 2 ^ 20) (Nat.pow_le_pow_right (by decide) (by omega))

lemma four_mul_T_le_succ (k : ℕ) : 4 * T k ≤ T (k + 1) := by
  have hbase : 10 ^ 6 ≤ T k := T_ge_base k
  set t := Nat.sqrt (T k)
  have ht1000 : 1000 ≤ t := by rw [Nat.le_sqrt]; nlinarith
  have hTk_lt : T k < (t + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt (T k)
  have hpoly : ∀ m : ℕ, 20 ≤ m → 4 * (m + 1) ^ 2 ≤ 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => decide
    | succ m hm ih =>
      have h2p : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; ring
      have : 4 * (m + 1 + 1) ^ 2 ≤ 2 * (4 * (m + 1) ^ 2) := by nlinarith
      omega
  have h1 : 4 * T k ≤ 4 * (t + 1) ^ 2 := by nlinarith
  exact h1.trans (hpoly t (by omega))

lemma sqrt_T_ge (k : ℕ) : 1000 * 2 ^ k ≤ Nat.sqrt (T k) := by
  induction k with
  | zero =>
    simp only [pow_zero, mul_one, T]
    rw [Nat.le_sqrt]; decide
  | succ k ih =>
    rw [Nat.le_sqrt]
    have h1 : (1000 * 2 ^ k) ^ 2 ≤ T k := by simpa [sq] using Nat.le_sqrt.mp ih
    have h2 : 4 * T k ≤ T (k + 1) := four_mul_T_le_succ k
    have h3 : (1000 * 2 ^ (k + 1)) ^ 2 = 4 * (1000 * 2 ^ k) ^ 2 := by ring
    nlinarith

lemma T_strictMono : StrictMono T :=
  strictMono_nat_of_lt_succ fun k => by
    have h1 := four_mul_T_le_succ k
    have h2 := T_ge_base k
    omega

def isBad (m n : ℕ) : Prop :=
  ∃ k < m, ∃ d d' : ℕ, T k ≤ d ∧ d < d' ∧ d' ≤ T (k + 1) ∧ d' ≡ 1 [MOD d] ∧ d ∣ n ∧ d' ∣ n

lemma list_length_filter_add_not {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : p a <;> simp [h] <;> omega

lemma H_le_of_not_bad {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hnT : n ≤ T m) (hnb : ¬ isBad m n) :
    H n ≤ T 0 + m := by
  classical
  by_contra hgt; push Not at hgt
  set u := H n
  have hu_spec : ∃ s : List ℕ, s.length = u ∧ ValidChain n (fun _ => True) s := by
    refine Nat.findGreatest_spec (P := fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n (fun _ => True) s)
      (m := 1) hn ?_
    exact ⟨[1], rfl, by simp, fun d hd => by simp at hd; subst hd; exact ⟨one_dvd n, trivial⟩⟩
  rcases hu_spec with ⟨s, hslen, hsvalid⟩
  -- Split s into elements < T 0 and elements >= T 0
  let sSmall := s.filter (fun x => decide (x < T 0))
  let sBig := s.filter (fun x => decide (T 0 ≤ x))
  have hlen_split : s.length = sSmall.length + sBig.length := by
    have h1 := list_length_filter_add_not s (fun x => decide (x < T 0))
    have h2 : sBig = s.filter (fun x => !decide (x < T 0)) := by
      dsimp [sBig]
      congr 1; funext x
      by_cases hx : x < T 0
      · have hnot : ¬ T 0 ≤ x := not_le.mpr hx
        simp [hx, hnot]
      · have hle : T 0 ≤ x := not_lt.mp hx
        simp [hx, hle]
    rw [h2]; exact h1.symm
  have hs_lt : s.Pairwise (· < ·) := by
    have htrans : IsTrans ℕ (· < ·) := ⟨fun _ _ _ => lt_trans⟩
    exact List.isChain_iff_pairwise.mp (hsvalid.1.imp fun _ _ h => h.1)
  have hSmall_le : sSmall.length ≤ T 0 := by
    have hnodup : sSmall.Nodup := (hs_lt.imp ne_of_lt).filter _
    have hsub : sSmall.toFinset ⊆ Finset.range (T 0) := by
      intro x hx
      rw [List.mem_toFinset, List.mem_filter] at hx
      exact Finset.mem_range.mpr (of_decide_eq_true hx.2)
    calc sSmall.length = sSmall.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
      _ ≤ (Finset.range (T 0)).card := Finset.card_le_card hsub
      _ = T 0 := Finset.card_range _
  have hBig_le : sBig.length ≤ m := by
    by_contra hgt_big; push Not at hgt_big
    have hBig_ne : sBig ≠ [] := by intro h; rw [h] at hgt_big; simp at hgt_big
    have hex_ge : ∃ i, ∃ hi : i < s.length, T 0 ≤ s[i] := by
      have ⟨x, hx⟩ := List.exists_mem_of_ne_nil sBig hBig_ne
      rw [List.mem_filter] at hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx.1
      exact ⟨i, hi, of_decide_eq_true hx.2⟩
    let i0 := Nat.find hex_ge
    obtain ⟨hi0_lt, hi0_ge⟩ := Nat.find_spec hex_ge
    have hdrop_eq : sBig = s.drop i0 := by
      have hge_all : ∀ j (hj : j < s.length), i0 ≤ j → T 0 ≤ s[j] := by
        intro j hj hle
        rcases eq_or_lt_of_le hle with rfl | hlt
        · exact hi0_ge
        · exact le_trans hi0_ge (List.pairwise_iff_getElem.mp hs_lt i0 j hi0_lt hj hlt).le
      have hlt_all : ∀ j (hj : j < s.length), j < i0 → s[j] < T 0 := by
        intro j hj hlt
        by_contra hge; push Not at hge
        exact Nat.find_min hex_ge hlt ⟨hj, hge⟩
      have hsplit : s = s.take i0 ++ s.drop i0 := (List.take_append_drop i0 s).symm
      dsimp [sBig]
      conv_lhs => rw [hsplit, List.filter_append]
      have htake_empty : (s.take i0).filter (fun x => decide (T 0 ≤ x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have hj' : j < i0 := by rw [List.length_take] at hj; omega
        have hj_s : j < s.length := by omega
        rw [List.getElem_take]
        simp only [decide_eq_true_eq, not_le]
        exact hlt_all j hj_s hj'
      have hdrop_all : (s.drop i0).filter (fun x => decide (T 0 ≤ x)) = s.drop i0 := by
        rw [List.filter_eq_self]
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        rw [List.length_drop] at hj
        rw [List.getElem_drop, decide_eq_true_eq]
        exact hge_all (i0 + j) (by omega) (Nat.le_add_right i0 j)
      rw [htake_empty, hdrop_all, List.nil_append]
    have hlen_rem : i0 + m < s.length := by
      rw [hdrop_eq, List.length_drop] at hgt_big; omega
    have hstep_ge : ∀ (j : ℕ) (hj : j ≤ m), T j ≤ s[i0 + j]'(by omega) := by
      intro j
      induction j with
      | zero => intro _; simpa using hi0_ge
      | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        have hchain_rel := List.isChain_iff_getElem.mp hsvalid.1 (i0 + j) (by omega)
        have hdvd1 : s[i0 + j]'(by omega) ∣ n := (hsvalid.2 _ (List.getElem_mem _)).1
        have hdvd2 : s[i0 + j + 1]'(by omega) ∣ n := (hsvalid.2 _ (List.getElem_mem _)).1
        by_contra hlt_T; push Not at hlt_T
        exact hnb ⟨j, by omega, s[i0 + j]'(by omega), s[i0 + j + 1]'(by omega),
          hprev, hchain_rel.1, hlt_T.le, hchain_rel.2, hdvd1, hdvd2⟩
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have hprev := hstep_ge m' (by omega)
    have hchain_rel := List.isChain_iff_getElem.mp hsvalid.1 (i0 + m') (by omega)
    have hdvd1 : s[i0 + m']'(by omega) ∣ n := (hsvalid.2 _ (List.getElem_mem _)).1
    have hdvd2 : s[i0 + m' + 1]'(by omega) ∣ n := (hsvalid.2 _ (List.getElem_mem _)).1
    have hle_n : s[i0 + m' + 1]'(by omega) ≤ n := Nat.le_of_dvd (by omega) hdvd2
    exact hnb ⟨m', by omega, s[i0 + m']'(by omega), s[i0 + m' + 1]'(by omega),
      hprev, hchain_rel.1, hle_n.trans hnT, hchain_rel.2, hdvd1, hdvd2⟩
  omega

lemma sum_inv_two_pow_le (b : ℕ) :
    ∑ r ∈ (Icc 1 (2 ^ b) : Finset ℕ), (1 : ℝ) / (r : ℝ) ≤ (b : ℝ) + 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hsplit : (Icc 1 (2 ^ (b + 1)) : Finset ℕ) = Icc 1 (2 ^ b) ∪ Ioc (2 ^ b) (2 ^ (b + 1)) := by
      ext r; simp only [mem_Icc, mem_union, mem_Ioc]
      have : 2 ^ b ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ b)
      omega
    have hdisj : Disjoint (Icc 1 (2 ^ b) : Finset ℕ) (Ioc (2 ^ b) (2 ^ (b + 1))) := by
      rw [Finset.disjoint_left]; intro r h1 h2; rw [mem_Icc] at h1; rw [mem_Ioc] at h2; omega
    rw [hsplit, sum_union hdisj]
    have hblock : ∑ r ∈ (Ioc (2 ^ b) (2 ^ (b + 1)) : Finset ℕ), (1 : ℝ) / (r : ℝ) ≤ 1 := by
      calc ∑ r ∈ (Ioc (2 ^ b) (2 ^ (b + 1)) : Finset ℕ), (1 : ℝ) / (r : ℝ)
          ≤ ∑ _r ∈ (Ioc (2 ^ b) (2 ^ (b + 1)) : Finset ℕ), (1 : ℝ) / ((2 ^ b : ℕ) : ℝ) := by
            refine sum_le_sum fun r hr => ?_
            rw [mem_Ioc] at hr
            exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hr.1.le)
        _ = (((Ioc (2 ^ b) (2 ^ (b + 1)) : Finset ℕ).card) : ℝ) * ((1 : ℝ) / ((2 ^ b : ℕ) : ℝ)) := by simp
        _ = 1 := by
            have hcard : (Ioc (2 ^ b) (2 ^ (b + 1)) : Finset ℕ).card = 2 ^ b := by
              rw [Nat.card_Ioc, Nat.pow_succ]; omega
            rw [hcard, mul_one_div, div_self (by positivity)]
    push_cast; linarith

open Classical in
lemma card_bad_level_le (k N : ℕ) :
    (((Ico 1 N).filter (fun n => ∃ d d' : ℕ,
        T k ≤ d ∧ d < d' ∧ d' ≤ T (k + 1) ∧ d' ≡ 1 [MOD d] ∧ d ∣ n ∧ d' ∣ n)).card : ℝ) ≤
      (4 / (Nat.sqrt (T k) : ℝ)) * (N : ℝ) := by
  let pairs := (Icc (T k) (T (k + 1))).sigma (fun d => Icc 1 (T (k + 1) / d))
  have hcover : (Ico 1 N).filter (fun n => ∃ d d' : ℕ,
      T k ≤ d ∧ d < d' ∧ d' ≤ T (k + 1) ∧ d' ≡ 1 [MOD d] ∧ d ∣ n ∧ d' ∣ n) ⊆
      pairs.biUnion (fun p => (Ico 1 N).filter (fun n => (p.1 * (p.2 * p.1 + 1)) ∣ n)) := by
    intro n hn
    rw [mem_filter] at hn
    obtain ⟨hn_Ico, d, d', hdT, hlt, hd'T, hmod, hd_dvd, hd'_dvd⟩ := hn
    have hd_pos : 0 < d := by linarith [T_ge_base k]
    have hd_le : d ≤ T (k + 1) := hlt.le.trans hd'T
    have hr_ex : ∃ r : ℕ, 1 ≤ r ∧ d' = r * d + 1 := by
      have h1 : d' % d = 1 % d := hmod
      have h1d : 1 % d = 1 := Nat.mod_eq_of_lt (by linarith [T_ge_base k])
      rw [h1d] at h1
      have hdiv := Nat.div_add_mod d' d
      rw [h1] at hdiv
      refine ⟨d' / d, Nat.div_pos hlt.le hd_pos, ?_⟩
      rw [mul_comm] at hdiv; exact hdiv.symm
    obtain ⟨r, hr1, rfl⟩ := hr_ex
    have hr_le : r ≤ T (k + 1) / d := by
      rw [Nat.le_div_iff_mul_le hd_pos]
      exact (Nat.le_succ (r * d)).trans hd'T
    have hcop : Nat.Coprime d (r * d + 1) := by
      rw [Nat.coprime_comm]
      have := Nat.coprime_add_mul_right_left 1 d r
      simp [mul_comm]
    have hmul_dvd : d * (r * d + 1) ∣ n := hcop.mul_dvd_of_dvd_of_dvd hd_dvd hd'_dvd
    exact mem_biUnion.mpr ⟨⟨d, r⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨hdT, hd_le⟩, mem_Icc.mpr ⟨hr1, hr_le⟩⟩,
      mem_filter.mpr ⟨hn_Ico, hmul_dvd⟩⟩
  have hcard_mul : ∀ m : ℕ, 0 < m →
      (((Ico 1 N).filter (fun n => m ∣ n)).card : ℝ) ≤ (N : ℝ) / m := by
    intro m hm
    have hsub : (Ico 1 N).filter (fun n => m ∣ n) ⊆ (Icc 1 (N / m)).image (fun j => m * j) := by
      intro n hn
      rw [mem_filter, mem_Ico] at hn
      obtain ⟨j, rfl⟩ := hn.2
      refine mem_image.mpr ⟨j, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · by_contra h0; push Not at h0
        have hj0 : j = 0 := by omega
        rw [hj0, mul_zero] at hn
        omega
      · rw [Nat.le_div_iff_mul_le hm, mul_comm]; exact hn.1.2.le
    have hle : ((Ico 1 N).filter (fun n => m ∣ n)).card ≤ N / m :=
      (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))
    exact (Nat.cast_le.mpr hle).trans Nat.cast_div_le
  have hsum_le : (((Ico 1 N).filter (fun n => ∃ d d' : ℕ,
      T k ≤ d ∧ d < d' ∧ d' ≤ T (k + 1) ∧ d' ≡ 1 [MOD d] ∧ d ∣ n ∧ d' ∣ n)).card : ℝ) ≤
      (N : ℝ) * (∑ d ∈ Icc (T k) (T (k + 1)), (1 : ℝ) / (d : ℝ) ^ 2) *
        (∑ r ∈ Icc 1 (T (k + 1)), (1 : ℝ) / (r : ℝ)) := by
    calc (((Ico 1 N).filter _).card : ℝ)
        ≤ ((pairs.biUnion (fun p => (Ico 1 N).filter (fun n => (p.1 * (p.2 * p.1 + 1)) ∣ n))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcover
      _ ≤ ∑ p ∈ pairs, (((Ico 1 N).filter (fun n => (p.1 * (p.2 * p.1 + 1)) ∣ n)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ pairs, (N : ℝ) / ((p.1 * (p.2 * p.1 + 1) : ℕ) : ℝ) := by
          refine sum_le_sum fun p hp => hcard_mul _ ?_
          rw [mem_sigma, mem_Icc, mem_Icc] at hp
          have : 0 < p.1 := by linarith [T_ge_base k]
          positivity
      _ ≤ ∑ p ∈ pairs, (N : ℝ) * ((1 : ℝ) / (p.1 : ℝ) ^ 2) * ((1 : ℝ) / (p.2 : ℝ)) := by
          refine sum_le_sum fun p hp => ?_
          rw [mem_sigma, mem_Icc, mem_Icc] at hp
          have hd0 : (0 : ℝ) < p.1 := by exact_mod_cast (by linarith [T_ge_base k] : 0 < p.1)
          have hr0 : (0 : ℝ) < p.2 := by exact_mod_cast (by omega : 0 < p.2)
          have hden : (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ≤ ((p.1 * (p.2 * p.1 + 1) : ℕ) : ℝ) := by
            push_cast; nlinarith
          have hrhs : (N : ℝ) * ((1 : ℝ) / (p.1 : ℝ) ^ 2) * ((1 : ℝ) / (p.2 : ℝ)) =
              (N : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ)) := by ring
          rw [hrhs]
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hden
      _ = ∑ d ∈ Icc (T k) (T (k + 1)), ∑ r ∈ Icc 1 (T (k + 1) / d),
            (N : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) * ((1 : ℝ) / (r : ℝ)) := by
          dsimp [pairs]; rw [Finset.sum_sigma']
      _ ≤ ∑ d ∈ Icc (T k) (T (k + 1)), ∑ r ∈ Icc 1 (T (k + 1)),
            (N : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2) * ((1 : ℝ) / (r : ℝ)) := by
          refine sum_le_sum fun d _ => sum_le_sum_of_subset_of_nonneg
            (Icc_subset_Icc_right (Nat.div_le_self _ _)) fun _ _ _ => by positivity
      _ = ∑ d ∈ Icc (T k) (T (k + 1)),
            ((N : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2)) * ∑ r ∈ Icc 1 (T (k + 1)), (1 : ℝ) / (r : ℝ) :=
          sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
      _ = (∑ d ∈ Icc (T k) (T (k + 1)), (N : ℝ) * ((1 : ℝ) / (d : ℝ) ^ 2)) *
            (∑ r ∈ Icc 1 (T (k + 1)), (1 : ℝ) / (r : ℝ)) :=
          (Finset.sum_mul _ _ _).symm
      _ = (N : ℝ) * (∑ d ∈ Icc (T k) (T (k + 1)), (1 : ℝ) / (d : ℝ) ^ 2) *
            (∑ r ∈ Icc 1 (T (k + 1)), (1 : ℝ) / (r : ℝ)) := by rw [← Finset.mul_sum]
  have hinv_sq : ∑ d ∈ Icc (T k) (T (k + 1)), (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 / (T k : ℝ) := by
    have hTk2 : 2 ≤ T k := le_trans (by decide) (T_ge_base k)
    have hTlt : T k < T (k + 1) := T_strictMono (show k < k + 1 by omega)
    calc ∑ d ∈ Icc (T k) (T (k + 1)), (1 : ℝ) / (d : ℝ) ^ 2
        ≤ ∑ d ∈ Icc (T k) (T (k + 1)), (1 / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ)) := by
          refine sum_le_sum fun d hd => ?_
          rw [mem_Icc] at hd
          have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
          have hd1 : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (by omega : 0 < d - 1)
          have hdiff : (d : ℝ) - ((d - 1 : ℕ) : ℝ) = 1 := by
            have : (d : ℝ) = ((d - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (show d = (d - 1) + 1 by omega)
            linarith
          have hrhs : 1 / ((d - 1 : ℕ) : ℝ) - 1 / (d : ℝ) = 1 / (((d - 1 : ℕ) : ℝ) * (d : ℝ)) := by
            rw [div_sub_div _ _ hd1.ne' hd0.ne', one_mul, mul_one, hdiff]
          rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = ∑ j ∈ Ico (T k - 1) (T (k + 1)), (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
          · intro d hd; rw [mem_Icc] at hd; rw [mem_Ico]; omega
          · intro d₁ hd₁ d₂ hd₂ h; rw [mem_Icc] at hd₁ hd₂; omega
          · intro j hj; rw [mem_Ico] at hj; exact ⟨j + 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro d hd; rw [mem_Icc] at hd; rw [Nat.sub_add_cancel (by omega)]
      _ = 1 / ((T k - 1 : ℕ) : ℝ) - 1 / ((T (k + 1) : ℕ) : ℝ) :=
          sum_sub_succ_Ico (fun j => 1 / (j : ℝ)) (by omega)
      _ ≤ 1 / ((T k - 1 : ℕ) : ℝ) := by linarith [show (0 : ℝ) ≤ 1 / (T (k + 1) : ℝ) by positivity]
      _ ≤ 2 / (T k : ℝ) := by
          rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < T k - 1)) (by exact_mod_cast (by omega : 0 < T k))]
          have : (T k : ℝ) = ((T k - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (show T k = (T k - 1) + 1 by omega)
          have : (2 : ℝ) ≤ T k := by exact_mod_cast hTk2
          linarith
  have hharm : ∑ r ∈ Icc 1 (T (k + 1)), (1 : ℝ) / (r : ℝ) ≤ (Nat.sqrt (T k) : ℝ) + 1 := by
    simpa [T] using sum_inv_two_pow_le (Nat.sqrt (T k))
  have hprod_le : (2 / (T k : ℝ)) * ((Nat.sqrt (T k) : ℝ) + 1) ≤ 4 / (Nat.sqrt (T k) : ℝ) := by
    have hsq_pos : (0 : ℝ) < Nat.sqrt (T k) := by
      exact_mod_cast (by linarith [sqrt_T_ge k, Nat.one_le_two_pow (n := k)] : 0 < Nat.sqrt (T k))
    have hTk_pos : (0 : ℝ) < T k := by exact_mod_cast (by linarith [T_ge_base k] : 0 < T k)
    have hsq_ge : (Nat.sqrt (T k) : ℝ) ^ 2 ≤ (T k : ℝ) := by
      exact_mod_cast (by simpa [sq] using Nat.sqrt_le (T k))
    have hsq1 : (1 : ℝ) ≤ Nat.sqrt (T k) := by
      exact_mod_cast (by linarith [sqrt_T_ge k, Nat.one_le_two_pow (n := k)] : 1 ≤ Nat.sqrt (T k))
    have hlhs : (2 / (T k : ℝ)) * ((Nat.sqrt (T k) : ℝ) + 1) =
        2 * ((Nat.sqrt (T k) : ℝ) + 1) / (T k : ℝ) := by ring
    rw [hlhs, div_le_div_iff₀ hTk_pos hsq_pos]
    nlinarith
  calc (((Ico 1 N).filter _).card : ℝ)
      ≤ (N : ℝ) * (∑ d ∈ Icc (T k) (T (k + 1)), (1 : ℝ) / (d : ℝ) ^ 2) *
          (∑ r ∈ Icc 1 (T (k + 1)), (1 : ℝ) / (r : ℝ)) := hsum_le
    _ ≤ (N : ℝ) * (2 / (T k : ℝ)) * ((Nat.sqrt (T k) : ℝ) + 1) := by
        have h1 : 0 ≤ ∑ d ∈ Icc (T k) (T (k + 1)), (1 : ℝ) / (d : ℝ) ^ 2 :=
          sum_nonneg fun _ _ => by positivity
        have h2 : 0 ≤ ∑ r ∈ Icc 1 (T (k + 1)), (1 : ℝ) / (r : ℝ) :=
          sum_nonneg fun _ _ => by positivity
        gcongr
    _ = (N : ℝ) * ((2 / (T k : ℝ)) * ((Nat.sqrt (T k) : ℝ) + 1)) := by ring
    _ ≤ (N : ℝ) * (4 / (Nat.sqrt (T k) : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod_le (Nat.cast_nonneg N)
    _ = (4 / (Nat.sqrt (T k) : ℝ)) * (N : ℝ) := by ring

open Classical in
lemma card_bad_le (m N : ℕ) :
    (((Ico 1 N).filter (isBad m)).card : ℝ) ≤ (1 / 100 : ℝ) * (N : ℝ) := by
  classical
  have hcover : (Ico 1 N).filter (isBad m) ⊆
      (Finset.range m).biUnion (fun k => (Ico 1 N).filter (fun n => ∃ d d' : ℕ,
        T k ≤ d ∧ d < d' ∧ d' ≤ T (k + 1) ∧ d' ≡ 1 [MOD d] ∧ d ∣ n ∧ d' ∣ n)) := by
    intro n hn
    rw [mem_filter] at hn
    obtain ⟨hnI, k, hk, d, d', h1, h2, h3, h4, h5, h6⟩ := hn
    exact mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, mem_filter.mpr ⟨hnI, d, d', h1, h2, h3, h4, h5, h6⟩⟩
  calc (((Ico 1 N).filter (isBad m)).card : ℝ)
      ≤ ∑ k ∈ Finset.range m, (((Ico 1 N).filter (fun n => ∃ d d' : ℕ,
          T k ≤ d ∧ d < d' ∧ d' ≤ T (k + 1) ∧ d' ≡ 1 [MOD d] ∧ d ∣ n ∧ d' ∣ n)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range m, (4 / (Nat.sqrt (T k) : ℝ)) * (N : ℝ) :=
        sum_le_sum fun k _ => card_bad_level_le k N
    _ = (∑ k ∈ Finset.range m, 4 / (Nat.sqrt (T k) : ℝ)) * (N : ℝ) := by rw [← sum_mul]
    _ ≤ (1 / 100 : ℝ) * (N : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
        calc ∑ k ∈ Finset.range m, 4 / (Nat.sqrt (T k) : ℝ)
            ≤ ∑ k ∈ Finset.range m, (4 / 1000 : ℝ) * (1 / 2 : ℝ) ^ k := by
              refine sum_le_sum fun k _ => ?_
              have hge : (1000 * 2 ^ k : ℝ) ≤ (Nat.sqrt (T k) : ℝ) := by exact_mod_cast sqrt_T_ge k
              calc 4 / (Nat.sqrt (T k) : ℝ)
                  ≤ 4 / (1000 * 2 ^ k : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hge
                _ = (4 / 1000 : ℝ) * (1 / 2 : ℝ) ^ k := by rw [one_div_pow]; ring
          _ = (4 / 1000 : ℝ) * ∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ k := by rw [← mul_sum]
          _ ≤ (4 / 1000 : ℝ) * 2 := by
              gcongr
              rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
              have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
              have heq : ((1 / 2 : ℝ) ^ m - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ m) := by ring
              linarith
          _ ≤ 1 / 100 := by norm_num

/- ### Part 4: Tower comparison S k <= T (3 * k) and main contradiction -/

lemma poly_le_two_pow_half (t : ℕ) (ht : 1000 ≤ t) : 3200 * t ^ 4 ≤ 2 ^ (t / 2) := by
  suffices ∀ m : ℕ, 60 ≤ m → 3200 * (2 * m + 1) ^ 4 ≤ 2 ^ m by
    have hm : 60 ≤ t / 2 := by omega
    have ht_le : t ≤ 2 * (t / 2) + 1 := by omega
    exact (Nat.mul_le_mul_left 3200 (Nat.pow_le_pow_left ht_le 4)).trans (this (t / 2) hm)
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; ring
    have hstep : (2 * (m + 1) + 1) ^ 4 ≤ 2 * (2 * m + 1) ^ 4 := by
      have hu : 121 ≤ 2 * m + 1 := by omega
      have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
      rw [h1]
      set u := 2 * m + 1
      have hsq : (u + 2) ^ 2 ≤ u ^ 2 + 5 * u := by nlinarith
      have h4 : ((u + 2) ^ 2) ^ 2 ≤ 2 * (u ^ 2) ^ 2 := by nlinarith [sq_nonneg u]
      have heq1 : (u + 2) ^ 4 = ((u + 2) ^ 2) ^ 2 := by ring
      have heq2 : u ^ 4 = (u ^ 2) ^ 2 := by ring
      linarith
    nlinarith

lemma S_le_T_three_mul (k : ℕ) : S k ≤ T (3 * k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    set x := T (3 * k)
    have hx : 10 ^ 6 ≤ x := T_ge_base (3 * k)
    have h1 : S (k + 1) ≤ 2 ^ (2 ^ (400 * x ^ 2)) := by
      simp only [S]
      exact Nat.pow_le_pow_right (by decide)
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 400 (Nat.pow_le_pow_left ih 2)))
    have h3 : 3 * (k + 1) = 3 * k + 1 + 1 + 1 := by omega
    rw [h3]
    refine h1.trans ?_
    -- Show 2^(400 * x^2) <= Nat.sqrt (T (3*k + 2))
    simp only [T]
    apply Nat.pow_le_pow_right (by decide)
    rw [Nat.le_sqrt]
    have hsq : 2 ^ (400 * x ^ 2) * 2 ^ (400 * x ^ 2) = 2 ^ (800 * x ^ 2) := by
      rw [← Nat.pow_add]; ring_nf
    rw [hsq]
    apply Nat.pow_le_pow_right (by decide)
    -- Show 800 * x^2 <= Nat.sqrt (2 ^ (Nat.sqrt x))
    rw [Nat.le_sqrt]
    set t := Nat.sqrt x
    have ht1000 : 1000 ≤ t := by rw [Nat.le_sqrt]; nlinarith
    have hx_lt : x < (t + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt x
    have hx_le : x ≤ 2 * t ^ 2 := by nlinarith
    have h800 : 800 * x ^ 2 ≤ 3200 * t ^ 4 := by
      have : x ^ 2 ≤ (2 * t ^ 2) ^ 2 := Nat.pow_le_pow_left hx_le 2
      nlinarith
    have hhalf : 800 * x ^ 2 ≤ 2 ^ (t / 2) := h800.trans (poly_le_two_pow_half t ht1000)
    calc (800 * x ^ 2) * (800 * x ^ 2)
        ≤ 2 ^ (t / 2) * 2 ^ (t / 2) := Nat.mul_le_mul hhalf hhalf
      _ = 2 ^ (t / 2 + t / 2) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)

end Erdos696Proof

/-- Main solution to Erdos Problem 696: the ratio H(n) / h(n) does not diverge to infinity
on a set of natural density 1. -/
theorem OMA.solution : type_of% @Erdos696.erdos_696 := by
  classical
  open Erdos696 Erdos696Proof Filter Finset in
  intro hAll
  have hd : {n : ℕ | (0 : ℝ) < (h n : ℝ) ∧ (H n : ℝ) / (h n : ℝ) > 4}.HasDensity 1 := hAll 4
  have hev : ∀ᶠ N : ℕ in atTop,
      (7 / 10 : ℝ) < ({n : ℕ | (0 : ℝ) < (h n : ℝ) ∧ (H n : ℝ) / (h n : ℝ) > 4}).partialDensity Set.univ N :=
    hd.eventually (eventually_gt_nhds (by norm_num : (7 / 10 : ℝ) < 1))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  let L : ℕ := max (10 ^ 6) N₀
  have hL_big : 10 ^ 6 ≤ L := le_max_left _ _
  have hSL_ge : N₀ ≤ S (L + 1) := by
    have h1 : L + 1 + 2 ≤ S (L + 1) := add_two_le_S (L + 1)
    have h2 : N₀ ≤ L := le_max_right _ _
    omega
  set N := S (L + 1)
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by linarith [S_ge_two (L + 1)])
  have hdens_gt : (7 / 10 : ℝ) <
      ({n : ℕ | (0 : ℝ) < (h n : ℝ) ∧ (H n : ℝ) / (h n : ℝ) > 4}).partialDensity Set.univ N :=
    hN₀ N hSL_ge
  -- Compare with the count of good n < N having 1 <= n, L + 1 <= h n, and not isBad (3 * (L + 1)) n
  let m := 3 * (L + 1)
  have hN_le_T : N ≤ T m := S_le_T_three_mul (L + 1)
  let A := (Finset.range N).filter (fun n => 1 ≤ n ∧ L + 1 ≤ h n)
  let B := (Ico 1 N).filter (isBad m)
  let Good := A \ B
  have hA_card : (43 / 100 : ℝ) * (N : ℝ) ≤ (A.card : ℝ) := card_h_ge_lower L
  have hB_card : (B.card : ℝ) ≤ (1 / 100 : ℝ) * (N : ℝ) := card_bad_le m N
  have hGood_card : (42 / 100 : ℝ) * (N : ℝ) ≤ (Good.card : ℝ) := by
    have hle : A.card ≤ Good.card + B.card := by
      have : A ⊆ Good ∪ B := fun x hx => by
        by_cases hxB : x ∈ B
        · exact mem_union_right _ hxB
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxB⟩)
      exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    have hle_r : (A.card : ℝ) ≤ (Good.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hle
    linarith
  -- Every n in Good is NOT in the divergence set {h n > 0 ∧ H n / h n > 4}
  let DivSet := {n : ℕ | (0 : ℝ) < (h n : ℝ) ∧ (H n : ℝ) / (h n : ℝ) > 4}
  have hdisj : Disjoint (Good : Set ℕ) (DivSet ∩ Set.Iio N) := by
    rw [Set.disjoint_left]
    intro n hnG hnD
    rw [Finset.mem_coe] at hnG
    dsimp only [Good] at hnG
    rw [Finset.mem_sdiff] at hnG
    obtain ⟨hnA, hnB⟩ := hnG
    rw [mem_filter, Finset.mem_range] at hnA
    obtain ⟨hnN, hn1, hh_ge⟩ := hnA
    have hnb : ¬ isBad m n := fun hbad => hnB (mem_filter.mpr ⟨mem_Ico.mpr ⟨hn1, hnN⟩, hbad⟩)
    have hH_le : H n ≤ T 0 + m := H_le_of_not_bad (by omega) hn1 (hnN.le.trans hN_le_T) hnb
    have hH_le_4h : H n ≤ 4 * h n := by
      have hT0 : T 0 = 10 ^ 6 := rfl
      omega
    have hdiv_gt : (4 : ℝ) < (H n : ℝ) / (h n : ℝ) := hnD.1.2
    have hh_pos : (0 : ℝ) < (h n : ℝ) := hnD.1.1
    rw [lt_div_iff₀ hh_pos] at hdiv_gt
    have hH_r : (H n : ℝ) ≤ 4 * (h n : ℝ) := by exact_mod_cast hH_le_4h
    linarith
  -- Hence (DivSet ∩ Iio N).ncard + Good.card <= N
  have hncard_add : (DivSet ∩ Set.Iio N).ncard + Good.card ≤ N := by
    have hsub : (Good : Set ℕ) ∪ (DivSet ∩ Set.Iio N) ⊆ (Finset.range N : Set ℕ) := by
      intro n hn
      rcases hn with hnG | hnD
      · rw [Finset.mem_coe] at hnG ⊢
        exact (mem_filter.mp (mem_sdiff.mp hnG).1).1
      · rw [Finset.mem_coe, Finset.mem_range]
        exact hnD.2
    have hfinD : (DivSet ∩ Set.Iio N).Finite := (Set.finite_Iio N).subset Set.inter_subset_right
    have hfinG : (Good : Set ℕ).Finite := Good.finite_toSet
    have hunion := Set.ncard_union_eq hdisj hfinG hfinD
    have hle := Set.ncard_le_ncard hsub (Finset.range N).finite_toSet
    rw [Set.ncard_coe_finset, Finset.card_range] at hle
    rw [hunion, Set.ncard_coe_finset] at hle
    omega
  have hpd_eq : DivSet.partialDensity Set.univ N = ((DivSet ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    congr 1
    have hIio : Set.Iio N = (Finset.range N : Set ℕ) := by ext x; simp
    rw [hIio, Set.ncard_coe_finset, Finset.card_range]
  rw [hpd_eq] at hdens_gt
  have hncard_r : ((DivSet ∩ Set.Iio N).ncard : ℝ) + (Good.card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hncard_add
  have hpd_le : ((DivSet ∩ Set.Iio N).ncard : ℝ) / (N : ℝ) ≤ 58 / 100 := by
    rw [div_le_iff₀ hN_pos]
    linarith
  linarith


