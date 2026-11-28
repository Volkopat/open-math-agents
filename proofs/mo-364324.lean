import OMAStatements.S_mo_364324
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.FieldSimp

namespace OMA.Pell364324

def step (p : ℕ × ℕ) : ℕ × ℕ := (5 * p.1 + 4 * p.2, 6 * p.1 + 5 * p.2)

def iterate : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, z => z
  | k + 1, z => step (iterate k z)

def pair (k j : ℕ) : ℕ × ℕ := iterate k (j, 1)

def A (k : ℕ) : ℕ := (iterate k (1, 0)).1

def B (k : ℕ) : ℕ := (iterate k (0, 1)).1

noncomputable def rho : ℝ := Real.sqrt 6 / 2

theorem step_gcd (z : ℕ × ℕ) : (step z).1.gcd (step z).2 = z.1.gcd z.2 := by
  rcases z with ⟨a, b⟩
  change Nat.gcd (5 * a + 4 * b) (6 * a + 5 * b) = Nat.gcd a b
  apply Nat.dvd_antisymm
  · have h₁ := Nat.gcd_dvd_left (5 * a + 4 * b) (6 * a + 5 * b)
    have h₂ := Nat.gcd_dvd_right (5 * a + 4 * b) (6 * a + 5 * b)
    have ha : 5 * (5 * a + 4 * b) - 4 * (6 * a + 5 * b) = a := by omega
    have hb : 5 * (6 * a + 5 * b) - 6 * (5 * a + 4 * b) = b := by omega
    apply Nat.dvd_gcd
    · simpa only [ha] using Nat.dvd_sub (dvd_mul_of_dvd_right h₁ 5) (dvd_mul_of_dvd_right h₂ 4)
    · simpa only [hb] using Nat.dvd_sub (dvd_mul_of_dvd_right h₂ 5) (dvd_mul_of_dvd_right h₁ 6)
  · have ha := Nat.gcd_dvd_left a b
    have hb := Nat.gcd_dvd_right a b
    exact Nat.dvd_gcd
      (Nat.dvd_add (dvd_mul_of_dvd_right ha 5) (dvd_mul_of_dvd_right hb 4))
      (Nat.dvd_add (dvd_mul_of_dvd_right ha 6) (dvd_mul_of_dvd_right hb 5))

theorem pair_gcd (k j : ℕ) : (pair k j).1.gcd (pair k j).2 = 1 := by
  induction k with
  | zero => simp [pair, iterate]
  | succ k ih => simpa only [pair, iterate, step_gcd] using ih

theorem iterate_linear (k j l : ℕ) :
    iterate k (j, l) =
      ((iterate k (1, 0)).1 * j + (iterate k (0, 1)).1 * l,
        (iterate k (1, 0)).2 * j + (iterate k (0, 1)).2 * l) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    simp only [iterate, ih, step, Prod.mk.injEq]
    constructor <;> ring

theorem pair_fst (k j : ℕ) : (pair k j).1 = A k * j + B k := by
  simpa [pair, A, B] using congrArg Prod.fst (iterate_linear k j 1)

@[simp] theorem A_zero : A 0 = 1 := rfl

@[simp] theorem A_one : A 1 = 5 := rfl

theorem A_recurrence (k : ℕ) : (A (k + 2) : ℤ) = 10 * (A (k + 1) : ℤ) - A k := by
  have h : A (k + 2) + A k = 10 * A (k + 1) := by
    simp only [A, iterate, step]
    omega
  have h' : (A (k + 2) : ℤ) + A k = 10 * (A (k + 1) : ℤ) := by exact_mod_cast h
  omega

theorem B_ge (k : ℕ) : k ≤ B k := by
  have hs (l : ℕ) : 1 ≤ (iterate l (0, 1)).2 := by
    induction l with
    | zero => decide
    | succ l ih =>
      simp only [iterate, step]
      omega
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hz := hs k
    simp only [B] at ih
    simp only [B, iterate, step]
    omega

theorem rho_sq : rho ^ 2 = 3 / 2 := by
  rw [rho, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num

theorem step_error (z : ℕ × ℕ) :
    ((step z).2 : ℝ) - rho * (step z).1 = (5 - 4 * rho) * ((z.2 : ℝ) - rho * z.1) := by
  simp only [step, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linear_combination -(4 * (z.1 : ℝ)) * rho_sq

theorem iterate_error (k : ℕ) (z : ℕ × ℕ) :
    ((iterate k z).2 : ℝ) - rho * (iterate k z).1 =
      (5 - 4 * rho) ^ k * ((z.2 : ℝ) - rho * z.1) := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    rw [iterate, step_error, ih, pow_succ]
    ring

theorem pair_error (k j : ℕ) :
    ((pair k j).2 : ℝ) - rho * (pair k j).1 = (5 - 4 * rho) ^ k * (1 - rho * j) := by
  simpa [pair] using iterate_error k (j, 1)

end OMA.Pell364324

namespace OMA.Rotate364324

private theorem phaseApprox (D : ℕ) (ρ a : ℝ) (hρ : 0 < ρ)
    (hscale : (1 : ℝ) / 24 ≤ (D : ℝ) * ρ) :
    ∃ t : ℕ, t ≤ 24 * D ∧ ∃ f : ℤ,
      0 ≤ a - (f : ℝ) - (t : ℝ) * ρ ∧ a - (f : ℝ) - (t : ℝ) * ρ < ρ := by
  let u := Int.fract a
  have hu : 0 ≤ u := Int.fract_nonneg a
  have hu' : u < 1 := Int.fract_lt_one a
  let t : ℕ := ⌊u / ρ⌋₊
  have hlow : (t : ℝ) * ρ ≤ u :=
    (le_div_iff₀ hρ).mp (Nat.floor_le (div_nonneg hu hρ.le))
  have hhigh : u < ((t : ℝ) + 1) * ρ :=
    (div_lt_iff₀ hρ).mp (Nat.lt_floor_add_one (u / ρ))
  have hscale' : (1 : ℝ) ≤ ((24 * D : ℕ) : ℝ) * ρ := by
    push_cast
    linarith only [hscale]
  have ht' : (t : ℝ) ≤ ((24 * D : ℕ) : ℝ) :=
    le_of_mul_le_mul_right (hlow.trans (hu'.le.trans hscale')) hρ
  have ht : t ≤ 24 * D := by exact_mod_cast ht'
  refine ⟨t, ht, ⌊a⌋, ?_⟩
  change 0 ≤ u - (t : ℝ) * ρ ∧ u - (t : ℝ) * ρ < ρ
  constructor <;> linarith only [hlow, hhigh]

theorem boundedRotation (D : ℕ) (hD : ∀ h : ℕ, 0 < h → h ≤ 24 → h ∣ D)
    (θ η : ℝ) (hsep : ∀ z : ℤ, (1 : ℝ) / 24 ≤ |(D : ℝ) * θ - (z : ℝ)|) :
    ∃ j : ℕ, j ≤ (24 * D) * 24 ∧ ∃ n : ℤ,
      (1 : ℝ) / 4 ≤ (n : ℝ) - (η + θ * j) ∧
        (n : ℝ) - (η + θ * j) ≤ (1 : ℝ) / 3 := by
  obtain ⟨h, hpos, hle, hclose⟩ :=
    Real.exists_nat_abs_mul_sub_round_le θ (n := 24) (by decide)
  let z : ℤ := round ((h : ℝ) * θ)
  let step : ℝ := (h : ℝ) * θ - (z : ℝ)
  have hnear : |step| ≤ (1 : ℝ) / 24 := by
    refine (show |step| ≤ (1 : ℝ) / 25 from ?_).trans (by norm_num)
    simpa only [step, z, Nat.cast_ofNat, show (24 : ℝ) + 1 = 25 by norm_num] using hclose
  obtain ⟨m, hm⟩ := hD h hpos hle
  have hscaledEq : (D : ℝ) * θ - (((m : ℤ) * z : ℤ) : ℝ) = (m : ℝ) * step := by
    rw [hm]
    push_cast
    dsimp only [step]
    ring
  have hmScale := hsep ((m : ℤ) * z)
  rw [hscaledEq, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)] at hmScale
  have hmult : (m : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (hm ▸ Nat.le_mul_of_pos_left m hpos)
  have hscale : (1 : ℝ) / 24 ≤ (D : ℝ) * |step| :=
    hmScale.trans (mul_le_mul_of_nonneg_right hmult (abs_nonneg step))
  have hstep : 0 < |step| := by
    by_contra! hz
    have hz' := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg D : 0 ≤ (D : ℝ)) hz
    linarith only [hscale, hz']
  by_cases hp : 0 ≤ step
  · obtain ⟨t, ht, f, hlow, hhigh⟩ := phaseApprox D |step| ((17 : ℝ) / 24 - η) hstep hscale
    let n : ℤ := (t : ℤ) * z - f + 1
    have heval : (n : ℝ) - (η + θ * ((t * h : ℕ) : ℝ)) =
        7 / 24 + (17 / 24 - η - (f : ℝ) - (t : ℝ) * |step|) := by
      rw [abs_of_nonneg hp]
      dsimp only [n, step]
      push_cast
      ring
    refine ⟨t * h, Nat.mul_le_mul ht hle, n, ?_⟩
    rw [heval]
    constructor <;> linarith only [hlow, hhigh, hnear]
  · obtain ⟨t, ht, f, hlow, hhigh⟩ := phaseApprox D |step| (η - (17 : ℝ) / 24) hstep hscale
    let n : ℤ := (t : ℤ) * z + f + 1
    have heval : (n : ℝ) - (η + θ * ((t * h : ℕ) : ℝ)) =
        7 / 24 - (η - 17 / 24 - (f : ℝ) - (t : ℝ) * |step|) := by
      rw [abs_of_neg (lt_of_not_ge hp)]
      dsimp only [n, step]
      push_cast
      ring
    refine ⟨t * h, Nat.mul_le_mul ht hle, n, ?_⟩
    rw [heval]
    constructor <;> linarith only [hlow, hhigh, hnear]

end OMA.Rotate364324

namespace OMA.Mo364324Rounding

open Filter

theorem close_recurrence (a b : ℕ → ℤ) (c : ℝ) (K : ℕ)
    (ha : ∀ k, a (k + 2) = 10 * a (k + 1) - a k)
    (hclose : ∀ k, K ≤ k → |c * (a k : ℝ) - (b k : ℝ)| < 1 / 24) :
    (b (K + 1) : ℝ) - (5 - 2 * Real.sqrt 6) * b K =
      c * ((a (K + 1) : ℝ) - (5 - 2 * Real.sqrt 6) * a K) := by
  let e : ℕ → ℝ := fun k => c * (a k : ℝ) - (b k : ℝ)
  have he (k : ℕ) (hk : K ≤ k) : |e k| < 1 / 24 := hclose k hk
  have ha' (k : ℕ) : (a (k + 2) : ℝ) = 10 * (a (k + 1) : ℝ) - a k := by
    exact_mod_cast ha k
  have hrec (k : ℕ) (hk : K ≤ k) : e (k + 2) = 10 * e (k + 1) - e k := by
    let z : ℤ := b (k + 2) - 10 * b (k + 1) + b k
    have hz : (z : ℝ) = -(e (k + 2) - 10 * e (k + 1) + e k) := by
      push_cast [z]
      dsimp [e]
      rw [ha']
      ring
    have h0 := abs_lt.mp (he k hk)
    have h1 := abs_lt.mp (he (k + 1) (by omega))
    have h2 := abs_lt.mp (he (k + 2) (by omega))
    have hzlo : (-1 : ℝ) < z := by linarith [h0.2, h1.1, h2.2]
    have hzhi : (z : ℝ) < 1 := by linarith [h0.1, h1.2, h2.1]
    have hzlo' : (-1 : ℤ) < z := by exact_mod_cast hzlo
    have hzhi' : z < 1 := by exact_mod_cast hzhi
    have hz0 : z = 0 := by omega
    rw [hz0, Int.cast_zero] at hz
    linarith
  let mu : ℝ := 5 - 2 * Real.sqrt 6
  let lam : ℝ := 5 + 2 * Real.sqrt 6
  let r : ℕ → ℝ := fun k => e (k + 1) - mu * e k
  have hs : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have hmu : |mu| ≤ 5 := by
    dsimp [mu]
    apply abs_le.mpr
    constructor <;> nlinarith
  have hlam : 1 < lam := by dsimp [lam]; linarith
  have hsum : 10 - mu = lam := by dsimp [mu, lam]; ring
  have hprod : lam * mu = 1 := by dsimp [lam, mu]; nlinarith
  have hr (k : ℕ) (hk : K ≤ k) : r (k + 1) = lam * r k := by
    change e (k + 2) - mu * e (k + 1) = lam * (e (k + 1) - mu * e k)
    rw [hrec k hk]
    calc
      10 * e (k + 1) - e k - mu * e (k + 1) = (10 - mu) * e (k + 1) - e k := by ring
      _ = lam * e (k + 1) - (lam * mu) * e k := by rw [hsum, hprod, one_mul]
      _ = _ := by ring
  have hrbound (k : ℕ) (hk : K ≤ k) : |r k| < 1 := by
    have h0 := he k hk
    have h1 := he (k + 1) (by omega)
    calc
      |r k| ≤ |e (k + 1)| + |mu * e k| := by
        simpa [r, sub_eq_add_neg] using abs_add_le (e (k + 1)) (-(mu * e k))
      _ ≤ |e (k + 1)| + 5 * |e k| := by
        rw [abs_mul]
        exact add_le_add_right (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)) _
      _ < 1 := by linarith
  have hrpow (n : ℕ) : r (K + n) = lam ^ n * r K := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.add_succ, hr (K + n) (by omega), ih, pow_succ]
        ring
  have hr0 : r K = 0 := by
    by_contra hne
    have habs : 0 < |r K| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / |r K|) hlam
    have hlarge : 1 < lam ^ n * |r K| := (div_lt_iff₀ habs).mp hn
    have hsmall := hrbound (K + n) (by omega)
    rw [hrpow, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt (by linarith : 0 < lam)) n)] at hsmall
    linarith
  change e (K + 1) - mu * e K = 0 at hr0
  dsimp [e, mu] at hr0
  linarith

private theorem irrational_sqrt_six : Irrational (Real.sqrt 6) := by
  apply irrational_sqrt_ofNat_iff.mpr
  rintro ⟨x, hx⟩
  have hxlt : x < 3 := by
    by_contra! hxge
    have h := Nat.mul_le_mul hxge hxge
    omega
  have hxsmall : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  rcases hxsmall with h | h | h <;> simp [h] at hx

private theorem sqrt_two_ne_combination (u v : ℚ) :
    Real.sqrt 2 ≠ (u : ℝ) + (v : ℝ) * Real.sqrt 6 := by
  intro h
  by_cases hv : v = 0
  · exact irrational_sqrt_two ⟨u, by simpa [hv] using h.symm⟩
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  by_cases hu : u = 0
  · have h23 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    have ht : Real.sqrt 2 ≠ 0 := by positivity
    have hthree : 1 = (v : ℝ) * Real.sqrt 3 := by
      apply mul_left_cancel₀ ht
      simp only [mul_one]
      simpa [hu, h23, mul_left_comm] using h
    have hthreeirr : Irrational (Real.sqrt 3) := by
      simpa using Nat.prime_three.irrational_sqrt
    apply hthreeirr
    refine ⟨1 / v, ?_⟩
    push_cast
    exact (div_eq_iff hv').mpr (by simpa [mul_comm] using hthree)
  have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have htwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsix : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hmix : 2 - (u : ℝ) ^ 2 - 6 * (v : ℝ) ^ 2 =
      Real.sqrt 6 * (2 * (u : ℝ) * (v : ℝ)) := by
    calc
      2 - (u : ℝ) ^ 2 - 6 * (v : ℝ) ^ 2 =
          ((u : ℝ) + (v : ℝ) * Real.sqrt 6) ^ 2 - (u : ℝ) ^ 2 -
            (Real.sqrt 6) ^ 2 * (v : ℝ) ^ 2 := by rw [← h, htwo, hsix]
      _ = _ := by ring
  apply irrational_sqrt_six
  refine ⟨(2 - u ^ 2 - 6 * v ^ 2) / (2 * u * v), ?_⟩
  push_cast
  exact (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) hu') hv')).mpr hmix

private theorem sqrt_two_mul_ne (A B C D : ℚ)
    (hnt : (C : ℝ) + (D : ℝ) * Real.sqrt 6 ≠ 0) :
    Real.sqrt 2 * ((C : ℝ) + (D : ℝ) * Real.sqrt 6) ≠
      (A : ℝ) + (B : ℝ) * Real.sqrt 6 := by
  intro h
  let den : ℚ := C ^ 2 - 6 * D ^ 2
  have hsix : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hnorm : (den : ℝ) =
      ((C : ℝ) + D * Real.sqrt 6) * ((C : ℝ) - D * Real.sqrt 6) := by
    dsimp [den]
    push_cast
    calc
      (C : ℝ) ^ 2 - 6 * (D : ℝ) ^ 2 = (C : ℝ) ^ 2 - Real.sqrt 6 ^ 2 * (D : ℝ) ^ 2 := by rw [hsix]
      _ = _ := by ring
  have hconj : (C : ℝ) - D * Real.sqrt 6 ≠ 0 := by
    intro hc
    by_cases hd : D = 0
    · simp [hd] at hc hnt
      exact hnt hc
    have hd' : (D : ℝ) ≠ 0 := by exact_mod_cast hd
    apply irrational_sqrt_six
    refine ⟨C / D, ?_⟩
    push_cast
    exact (div_eq_iff hd').mpr (by linarith [hc, mul_comm (Real.sqrt 6) (D : ℝ)])
  have hden : (den : ℝ) ≠ 0 := by rw [hnorm]; exact mul_ne_zero hnt hconj
  apply sqrt_two_ne_combination ((A * C - 6 * B * D) / den) ((B * C - A * D) / den)
  calc
    Real.sqrt 2 =
        ((A : ℝ) * C - 6 * B * D + ((B : ℝ) * C - A * D) * Real.sqrt 6) / (den : ℝ) := by
      apply (eq_div_iff hden).mpr
      calc
        Real.sqrt 2 * (den : ℝ) =
            (Real.sqrt 2 * ((C : ℝ) + (D : ℝ) * Real.sqrt 6)) *
              ((C : ℝ) - (D : ℝ) * Real.sqrt 6) := by rw [hnorm]; ring
        _ = ((A : ℝ) + (B : ℝ) * Real.sqrt 6) * ((C : ℝ) - D * Real.sqrt 6) := by rw [h]
        _ = (A : ℝ) * C - Real.sqrt 6 ^ 2 * B * D +
            ((B : ℝ) * C - A * D) * Real.sqrt 6 := by ring
        _ = _ := by rw [hsix]
    _ = _ := by push_cast; ring

theorem infinitely_often_far (a : ℕ → ℤ) (ha0 : a 0 = 1) (ha1 : a 1 = 5)
    (ha : ∀ k, a (k + 2) = 10 * a (k + 1) - a k) (d : ℤ) (hd : 0 < d) :
    ∃ᶠ k in atTop, ∀ z : ℤ, (1 : ℝ) / 24 ≤ |(d : ℝ) / Real.sqrt 2 * (a k : ℝ) - z| := by
  classical
  apply frequently_atTop.mpr
  intro K
  by_contra! h
  have hex (k : ℕ) : ∃ z : ℤ,
      K ≤ k → |(d : ℝ) / Real.sqrt 2 * (a k : ℝ) - z| < 1 / 24 := by
    by_cases hk : K ≤ k
    · obtain ⟨z, hz⟩ := h k hk
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun hk' => (hk hk').elim⟩
  choose b hb using hex
  have hcmp := close_recurrence a b ((d : ℝ) / Real.sqrt 2) K ha hb
  have hpos (k : ℕ) : 0 < a k ∧ a k < a (k + 1) := by
    induction k with
    | zero => rw [ha0, show 0 + 1 = 1 by rfl, ha1]; decide
    | succ k ih =>
        change 0 < a (k + 1) ∧ a (k + 1) < a (k + 2)
        rw [ha]
        omega
  have hpos0 : 0 < (a K : ℝ) := by exact_mod_cast (hpos K).1
  have hgrow : (a K : ℝ) < (a (K + 1) : ℝ) := by exact_mod_cast (hpos K).2
  have hmu : 5 - 2 * Real.sqrt 6 ≤ 1 := by
    have hs : (2 : ℝ) ≤ Real.sqrt 6 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hA : 0 < (a (K + 1) : ℝ) - (5 - 2 * Real.sqrt 6) * a K := by
    have hle := mul_le_mul_of_nonneg_right hmu hpos0.le
    linarith
  have htwo : 0 < Real.sqrt 2 := by positivity
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hB : 0 < (b (K + 1) : ℝ) - (5 - 2 * Real.sqrt 6) * b K := by
    rw [hcmp]
    exact mul_pos (div_pos hd' htwo) hA
  let A : ℚ := (d : ℚ) * ((a (K + 1) : ℚ) - 5 * (a K : ℚ))
  let B : ℚ := (d : ℚ) * (2 * (a K : ℚ))
  let C : ℚ := (b (K + 1) : ℚ) - 5 * (b K : ℚ)
  let D : ℚ := 2 * (b K : ℚ)
  have hleft : (C : ℝ) + (D : ℝ) * Real.sqrt 6 =
      (b (K + 1) : ℝ) - (5 - 2 * Real.sqrt 6) * b K := by
    dsimp [C, D]
    push_cast
    ring
  have hright : (A : ℝ) + (B : ℝ) * Real.sqrt 6 =
      (d : ℝ) * ((a (K + 1) : ℝ) - (5 - 2 * Real.sqrt 6) * a K) := by
    dsimp [A, B]
    push_cast
    ring
  apply sqrt_two_mul_ne A B C D (by rw [hleft]; exact hB.ne')
  rw [hleft, hright, hcmp, mul_comm (Real.sqrt 2), mul_right_comm, div_mul_cancel₀ _ htwo.ne']

end OMA.Mo364324Rounding

namespace OMA.Mo364324Assembly

open Filter Topology

private theorem sqrts :
    1 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 ∧
    1 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ 2 :=
  ⟨by have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
      simpa only [Real.sqrt_one] using h,
   by have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 2 ^ 2 by norm_num)
      simpa only [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] using h,
   by have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num)
      simpa only [Real.sqrt_one] using h,
   by have h := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ 2 ^ 2 by norm_num)
      simpa only [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] using h⟩

private theorem sqrt_ratio : Real.sqrt 3 = (Real.sqrt 6 / 2) * Real.sqrt 2 := by
  have hp : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [← hp]
  calc
    Real.sqrt 3 = (Real.sqrt 2 ^ 2 / 2) * Real.sqrt 3 := by rw [hs]; ring
    _ = (Real.sqrt 2 * Real.sqrt 3 / 2) * Real.sqrt 2 := by ring

private theorem floors_of_phase (m a b : ℕ) (n : ℤ)
    (hlow : (1 : ℝ) / 4 ≤ (n : ℝ) - (m : ℝ) / Real.sqrt 2 * a)
    (hhigh : (n : ℝ) - (m : ℝ) / Real.sqrt 2 * a ≤ 1 / 3)
    (herr : |(m : ℝ) * ((b : ℝ) - (Real.sqrt 6 / 2) * a)| < 1 / 8) :
    0 < n ∧
      ⌊(n.toNat : ℝ) * Real.sqrt 2⌋₊ = m * a ∧
      ⌊(n.toNat : ℝ) * Real.sqrt 3⌋₊ = m * b := by
  obtain ⟨h2l, h2u, h3l, h3u⟩ := sqrts
  have h2 : 0 < Real.sqrt 2 := by linarith
  have hn : 0 < n := by
    have hz : 0 ≤ (m : ℝ) / Real.sqrt 2 * a := by positivity
    exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hnat : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn.le
  have hd2 : (n : ℝ) * Real.sqrt 2 - (m : ℝ) * a =
      ((n : ℝ) - (m : ℝ) / Real.sqrt 2 * a) * Real.sqrt 2 := by
    field_simp [h2.ne']
  have hd3 : (n : ℝ) * Real.sqrt 3 - (m : ℝ) * b =
      ((n : ℝ) - (m : ℝ) / Real.sqrt 2 * a) * Real.sqrt 3 -
      (m : ℝ) * ((b : ℝ) - (Real.sqrt 6 / 2) * a) := by
    rw [sqrt_ratio]
    field_simp [h2.ne']
    ring
  have hlow2 := mul_le_mul hlow h2l (by norm_num) (by linarith)
  have hupp2 := mul_le_mul hhigh h2u h2.le (by norm_num)
  have hlow3 := mul_le_mul hlow h3l (by norm_num) (by linarith)
  have hupp3 := mul_le_mul hhigh h3u (by linarith) (by norm_num)
  obtain ⟨he₁, he₂⟩ := abs_lt.mp herr
  refine ⟨hn, (Nat.floor_eq_iff (by positivity)).2 ?_,
    (Nat.floor_eq_iff (by positivity)).2 ?_⟩
  · push_cast
    rw [hnat]
    constructor <;> linarith
  · push_cast
    rw [hnat]
    constructor <;> linarith

private theorem uniform_error (m J : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, j ≤ J →
      |(m : ℝ) * (5 - 4 * (Real.sqrt 6 / 2)) ^ k *
        (1 - (Real.sqrt 6 / 2) * j)| < 1 / 8 := by
  let rho : ℝ := Real.sqrt 6 / 2
  have hr₀ : 0 ≤ rho := by positivity
  have hr1 : Real.sqrt 6 < 5 / 2 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 6)
      (by norm_num : (6 : ℝ) < (5 / 2) ^ 2)
    simpa only [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 2)] using h
  have hr2 : 2 < Real.sqrt 6 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2 ^ 2)
      (by norm_num : (2 : ℝ) ^ 2 < 6)
    simpa only [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hu₀ : 0 ≤ 5 - 4 * rho := by dsimp [rho]; linarith
  have hu1 : 5 - 4 * rho < 1 := by dsimp [rho]; linarith
  have ht : Tendsto (fun k : ℕ => (m : ℝ) * (5 - 4 * rho) ^ k * (1 + rho * J))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hu₀ hu1).const_mul (m : ℝ)
      |>.mul_const (1 + rho * J)
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8)] with k hk j hj
  change |(m : ℝ) * (5 - 4 * rho) ^ k * (1 - rho * j)| < _
  rw [abs_mul, abs_of_nonneg (by positivity)]
  apply lt_of_le_of_lt _ hk
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hj' : (j : ℝ) ≤ J := by exact_mod_cast hj
  have hmul := mul_le_mul_of_nonneg_left hj' hr₀
  have hnon : 0 ≤ rho * j := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

open OMA.Pell364324

theorem whole (m : ℕ) (hm : 0 < m) :
    {n : ℕ | 0 < n ∧ Nat.gcd ⌊(n : ℝ) * Real.sqrt 2⌋₊
      ⌊(n : ℝ) * Real.sqrt 3⌋₊ = m}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  let D := Nat.factorial 24
  let J := (24 * D) * 24
  have hD : ∀ h : ℕ, 0 < h → h ≤ 24 → h ∣ D :=
    fun _ hpos hle => Nat.dvd_factorial hpos hle
  let d : ℤ := (D : ℤ) * m
  have hd : 0 < d := by
    have hDpos : 0 < D := Nat.factorial_pos _
    exact mul_pos (by exact_mod_cast hDpos) (by exact_mod_cast hm)
  have hfar := OMA.Mo364324Rounding.infinitely_often_far
    (fun k => (A k : ℤ)) (by simp [A_zero]) (by simp [A_one]) A_recurrence d hd
  have hev := (eventually_ge_atTop (2 * N + 1)).and (uniform_error m J)
  obtain ⟨k, hk, hsize, he⟩ := (hfar.and_eventually hev).exists
  have hsep : ∀ z : ℤ, (1 : ℝ) / 24 ≤ |(D : ℝ) *
      ((m : ℝ) / Real.sqrt 2 * A k) - z| := by
    intro z
    specialize hk z
    dsimp [d] at hk
    push_cast at hk
    have heq : (D : ℝ) * ((m : ℝ) / Real.sqrt 2 * A k) =
        ((D : ℝ) * m) / Real.sqrt 2 * A k := by ring
    simpa only [heq] using hk
  obtain ⟨j, hj, n, hn₁, hn₂⟩ :=
    OMA.Rotate364324.boundedRotation D hD ((m : ℝ) / Real.sqrt 2 * A k)
      ((m : ℝ) / Real.sqrt 2 * B k) hsep
  let a := (pair k j).1
  let b := (pair k j).2
  have hphase : (m : ℝ) / Real.sqrt 2 * a =
      (m : ℝ) / Real.sqrt 2 * B k + (m : ℝ) / Real.sqrt 2 * A k * j := by
    dsimp [a]
    rw [pair_fst]
    push_cast
    ring
  rw [← hphase] at hn₁ hn₂
  have herr : |(m : ℝ) * ((b : ℝ) - (Real.sqrt 6 / 2) * a)| < 1 / 8 := by
    change |(m : ℝ) * (((pair k j).2 : ℝ) - rho * (pair k j).1)| < _
    rw [pair_error]
    simpa only [rho, mul_assoc] using he j hj
  obtain ⟨hn, ha, hb⟩ := floors_of_phase m a b n hn₁ hn₂ herr
  have hab : Nat.gcd a b = 1 := pair_gcd k j
  have hngcd : Nat.gcd ⌊(n.toNat : ℝ) * Real.sqrt 2⌋₊
      ⌊(n.toNat : ℝ) * Real.sqrt 3⌋₊ = m := by
    rw [ha, hb, Nat.gcd_mul_left, hab, mul_one]
  refine ⟨n.toNat, ⟨by omega, hngcd⟩, ?_⟩
  have hka : k ≤ a := by
    dsimp [a]
    rw [pair_fst]
    have := B_ge k
    omega
  have hkam : k ≤ m * a := by
    have hm₁ : 1 ≤ m := hm
    exact hka.trans (by simpa using Nat.mul_le_mul_right a hm₁)
  have hkreal : (k : ℝ) ≤ ((m * a : ℕ) : ℝ) := by exact_mod_cast hkam
  have hscale : ((m * a : ℕ) : ℝ) ≤ (n.toNat : ℝ) * Real.sqrt 2 :=
    ((Nat.floor_eq_iff (by positivity)).mp ha).1
  have hsqrt : (n.toNat : ℝ) * Real.sqrt 2 ≤ (n.toNat : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left sqrts.2.1 (by positivity)
  have hsize' : (2 : ℝ) * N + 1 ≤ k := by exact_mod_cast hsize
  exact_mod_cast (show (N : ℝ) < n.toNat by linarith)

end OMA.Mo364324Assembly

theorem OMA.solution : type_of% @OMA.S_mo_364324.main :=
  OMA.Mo364324Assembly.whole
