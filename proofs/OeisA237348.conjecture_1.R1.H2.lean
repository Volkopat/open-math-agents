import OMAReductions.R_OeisA237348_conjecture_1_R1
import Mathlib

/-! Chebyshev bounds prime counting below each chosen exponential scale. -/

open Filter Topology

private theorem eventually_pi_lower :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) / (4 * Real.log x) ≤ (Nat.primeCounting x : ℝ) := by
  have hloglim : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsmall : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) / x < 1 / 8 :=
    (hloglim.comp tendsto_natCast_atTop_atTop).eventually_lt_const (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (8 : ℕ)] with x hs hx
  have hx8 : (8 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2 : ℝ)) using 1
    norm_num
  have hlog2₁ : Real.log 2 ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hlogx : Real.log (x : ℝ) ≤ (x : ℝ) / 8 := by
    have h := (div_lt_iff₀ hx0).1 hs
    linarith
  have hlogp : Real.log ((x : ℝ) + 1) ≤ (x : ℝ) / 4 := by
    calc
      _ ≤ Real.log (2 * (x : ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log (x : ℝ) := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ _ := by linarith
  calc
    _ = ((x : ℝ) / 4) / Real.log x := by rw [div_div]
    _ ≤ ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlog.le
      have := mul_le_mul_of_nonneg_left hlog2 hx0.le
      linarith
    _ ≤ _ := Chebyshev.pi_ge x

private theorem exponential_prime_count (A B C : ℕ) (hAB : A < B) (hB : 1 < B) :
    ∀ᶠ t : ℕ in atTop, C*A^t ≤ Nat.primeCounting (B^t) := by
  have hBR : (1:ℝ) < B := by exact_mod_cast hB
  have hB0 : (0:ℝ) < B := lt_trans zero_lt_one hBR
  have hAR : (A:ℝ) < B := by exact_mod_cast hAB
  have hab : |(A:ℝ)/(B:ℝ)| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_lt_one hB0).2 hAR
  have hlimit : Tendsto (fun t : ℕ => (4*(C:ℝ)*Real.log (B:ℝ))*
      ((t:ℝ)*((A:ℝ)/(B:ℝ))^t)) atTop (𝓝 0) := by
    simpa only [pow_one,mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hab).const_mul (4*(C:ℝ)*Real.log (B:ℝ))
  have hsmall := hlimit.eventually_lt_const (show (0:ℝ) < 1 by norm_num)
  have hgrow : Tendsto (fun t : ℕ => B^t) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hB
  filter_upwards [hgrow.eventually eventually_pi_lower, hsmall, eventually_ge_atTop (1:ℕ)] with t hl hs ht
  have htR : (0:ℝ) < t := by exact_mod_cast ht
  have hlog : 0 < Real.log (B:ℝ) := Real.log_pos hBR
  have hratio : (C:ℝ)*(A:ℝ)^t*(4*((t:ℝ)*Real.log (B:ℝ))) / (B:ℝ)^t < 1 := by
    have he : (C:ℝ)*(A:ℝ)^t*(4*((t:ℝ)*Real.log (B:ℝ))) / (B:ℝ)^t =
        (4*(C:ℝ)*Real.log (B:ℝ))*((t:ℝ)*((A:ℝ)/(B:ℝ))^t) := by
      rw [div_pow]
      ring
    exact he ▸ hs
  have hbpow : (0:ℝ) < (B:ℝ)^t := pow_pos hB0 _
  have hmul : (C:ℝ)*(A:ℝ)^t*(4*((t:ℝ)*Real.log (B:ℝ))) ≤ (B:ℝ)^t := by
    have h := (div_lt_iff₀ hbpow).1 hratio
    simpa only [one_mul] using h.le
  have hbound : (C:ℝ)*(A:ℝ)^t ≤ (Nat.primeCounting (B^t):ℝ) := by
    refine le_trans ((le_div_iff₀ (by positivity : 0 < 4*((t:ℝ)*Real.log (B:ℝ)))).2 hmul) ?_
    simpa only [Nat.cast_pow,Real.log_pow] using hl
  exact_mod_cast hbound

private theorem nth_le_count {j n : ℕ} (hj : 0 < j) (h : j ≤ Nat.primeCounting n) :
    Nat.nth Nat.Prime (j-1) ≤ n := by
  have hh : j-1 < Nat.count Nat.Prime (n+1) := by
    change j-1 < Nat.primeCounting n
    omega
  exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hh)

private theorem growth :
    ∀ d : ℕ, 1 ≤ d → ∃ T : ℕ, ∀ t ≥ T,
      let p := fun j : ℕ => Nat.nth Nat.Prime (j-1)
      p (p (16^(t+1))) + 2*d ≤ 64^t := by
  intro d _
  have h₁ := exponential_prime_count 16 32 16 (by decide) (by decide)
  have h₂ := exponential_prime_count 32 48 1 (by decide) (by decide)
  have h₃ : Tendsto (fun t : ℕ => (16:ℕ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hh : ∀ᶠ t : ℕ in atTop,
      let p := fun j : ℕ => Nat.nth Nat.Prime (j-1)
      p (p (16^(t+1)))+2*d≤64^t := by
    filter_upwards [h₁,h₂,h₃.eventually (eventually_ge_atTop (2*d)),
      eventually_ge_atTop (1:ℕ)] with t ht₁ ht₂ hd ht
    let p := fun j : ℕ => Nat.nth Nat.Prime (j-1)
    change p (p (16^(t+1))) + 2*d ≤ 64^t
    have hfirst : p (16^(t+1)) ≤ 32^t := by
      exact nth_le_count (by positivity) (by simpa only [pow_succ'] using ht₁)
    have hsecond : p (p (16^(t+1))) ≤ 48^t := by
      exact nth_le_count (Nat.prime_nth_prime _).pos
        (hfirst.trans (by simpa only [one_mul] using ht₂))
    exact (Nat.add_le_add hsecond hd).trans (pow_add_pow_le (by decide) (by decide) (by omega))
  exact eventually_atTop.1 hh

theorem OMA.solution : OMA.R_OeisA237348_conjecture_1_R1.H2 := growth