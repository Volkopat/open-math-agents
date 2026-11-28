import OMAReductions.R_oeis_a182749_R1
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

-- Credit: @FransDevelopment
namespace OMA.R_oeis_a182749_R1_H2_R1
def H1 : Prop := ∀ x : ℝ, 396738 < x → x < 7713133854 →
  ∃ q : ℕ, q.Prime ∧ x < q ∧ (q:ℝ) ≤ x*(1+1/(25*(Real.log x)^2))

def H2 : Prop := ∀ z : ℝ, 7713133853 < z →
  |Chebyshev.theta z - z| < (1/100 : ℝ)*z/(Real.log z)^2


/-- A strict rise of the Chebyshev theta function detects a prime in (x,y]. -/
theorem prime_of_theta_rise {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hrise : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) ≤ y := by
  classical
  by_contra hnone
  have heq : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊y⌋₊ := by
    ext p
    constructor
    · exact fun hp => Nat.primesLE_mono (Nat.floor_le_floor hxy) hp
    · intro hp
      obtain ⟨hp_le, hp_prime⟩ := Nat.mem_primesLE.mp hp
      have hpy := (Nat.le_floor_iff (hx.trans hxy)).mp hp_le
      have hpx : (p : ℝ) ≤ x := le_of_not_gt fun h => hnone ⟨p, hp_prime, h, hpy⟩
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx).mpr hpx, hp_prime⟩
  rw [Chebyshev.theta_eq_sum_primesLE x, Chebyshev.theta_eq_sum_primesLE y, heq] at hrise
  exact (lt_irrefl _ hrise)

/-- Analytic part of Dusart (2010), Proposition 6.8. The hypothesis is the
two-sided theta estimate used in its proof, with coefficient 0.0195.
The finite prime-gap calculation up to the start of that estimate is separate. -/
theorem prime_interval_of_theta_error (x : ℝ) (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (herr : ∀ z : ℝ, x ≤ z →
      |Chebyshev.theta z - z| ≤ (39 / 2000 : ℝ) * z / (Real.log z)^2) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x)^2)) := by
  let d : ℝ := 1 / (25 * (Real.log x)^2)
  let y : ℝ := x * (1 + d)
  have hL : 0 < Real.log x := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hdmax : d ≤ 1 / 25 := by
    dsimp [d]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith [sq_nonneg (Real.log x - 1)]
  have hxy : x ≤ y := by dsimp [y]; nlinarith [mul_pos hx hd]
  have hy : 0 < y := hx.trans_le hxy
  have hll : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hden : (Real.log x)^2 ≤ (Real.log y)^2 :=
    pow_le_pow_left₀ hL.le hll 2
  have conv (z : ℝ) :
      (39 / 2000 : ℝ) * z / (Real.log x)^2 = (39 / 80 : ℝ)*z*d := by
    dsimp [d]
    field_simp [hL.ne']
    ring
  have upper := (abs_le.mp (herr x le_rfl)).2
  rw [conv x] at upper
  have lower := (abs_le.mp (herr y hxy)).1
  have hyerr : (39/2000 : ℝ)*y/(Real.log y)^2 ≤ (39/80 : ℝ)*y*d := by
    rw [← conv]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hys : y ≤ (26/25 : ℝ)*x := by
    dsimp [y]
    nlinarith [mul_le_mul_of_nonneg_left hdmax hx.le]
  have hr : Chebyshev.theta x < Chebyshev.theta y := by
    have hbudget := mul_le_mul_of_nonneg_right hys hd.le
    have hy_eq : y = x + x*d := by dsimp [y]; ring
    nlinarith [mul_pos hx hd]
  exact prime_of_theta_rise hx.le hxy hr


/-- Exact tail supplied by the k=2, eta=0.01 row of Dusart's Theorem 5.2.
The remaining finite interval runs from 396738 through 7713133853 inclusive. -/
theorem prime_interval_of_table_row
    (thetaRow : ∀ z : ℝ, 7713133853 < z →
      |Chebyshev.theta z - z| < (1 / 100 : ℝ) * z / (Real.log z)^2)
    (x : ℝ) (hx : 7713133853 < x) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) ≤ x * (1 + 1 / (25 * (Real.log x)^2)) := by
  have xpos : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le xpos).mpr
    (by linarith [Real.exp_one_lt_three])
  apply prime_interval_of_theta_error x xpos hlog
  intro z hz
  apply (thetaRow z (hx.trans_le hz)).le.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right (by norm_num) (xpos.le.trans hz)

theorem main : H1 → H2 → OMA.R_oeis_a182749_R1.H2 := by
  intro finite theta x hx
  by_cases h : x < 7713133854
  · exact finite x hx h
  · exact prime_interval_of_table_row theta x (by linarith)

end OMA.R_oeis_a182749_R1_H2_R1
