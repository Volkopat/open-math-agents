import OMAStatements.S_oeis_a022163
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

open OMA.S_oeis_a022163
namespace OMA.Spectral

noncomputable def b : ℝ := 3 + Real.sqrt 6

lemma sqrt_bounds : 2 < Real.sqrt 6 ∧ Real.sqrt 6 < 3 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg (6:ℝ)]

lemma slope_eq : OMA.S_oeis_a022163.slope = (b - 3) / 2 := by
  unfold OMA.S_oeis_a022163.slope b
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have h' := Real.sq_sqrt (show (0:ℝ) ≤ 3/2 by norm_num)
  have hs := Real.sqrt_nonneg (3/2:ℝ)
  have hp := Real.sqrt_nonneg (6:ℝ)
  have hp' := sqrt_bounds.1
  have hz : (Real.sqrt (3/2:ℝ) - Real.sqrt 6 / 2) *
      (Real.sqrt (3/2:ℝ) + Real.sqrt 6 / 2) = 0 := by nlinarith
  have := (mul_eq_zero.mp hz).resolve_right (by linarith)
  linarith

lemma upper_slope : OMA.S_oeis_a022163.slope / (OMA.S_oeis_a022163.slope - 1) = b := by
  rw [slope_eq]
  have hb : 5 < b := by unfold b; linarith [sqrt_bounds.1]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  apply (div_eq_iff (by linarith : (b - 3) / 2 - 1 ≠ 0)).2
  unfold b
  nlinarith

lemma upper_bounds (u : ℕ) :
    (upper u : ℝ) ≤ b * u ∧ b * u < (upper u : ℝ) + 1 := by
  unfold upper
  rw [upper_slope, mul_comm (u : ℝ)]
  have hb : 0 ≤ b := by unfold b; linarith [sqrt_bounds.1]
  have hz : 0 ≤ ⌊b * (u : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
  have hcast : (((⌊b * (u : ℝ)⌋).toNat : ℕ) : ℝ) = (⌊b * (u : ℝ)⌋ : ℤ) := by
    exact_mod_cast (Int.toNat_of_nonneg hz)
  rw [hcast]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- The floor error for a second upper step is multiplied by the conjugate, which lies between zero and one. -/
lemma upper_rec (u : ℕ) :
    (upper (upper u) : ℤ) = 6 * (upper u : ℤ) - 3 * (u : ℤ) := by
  obtain ⟨h1,h2⟩ := upper_bounds u
  obtain ⟨h3,h4⟩ := upper_bounds (upper u)
  have hγ0 : 0 ≤ 6-b := by unfold b; linarith [sqrt_bounds.2]
  have hγ1 : 6-b < 1 := by unfold b; linarith [sqrt_bounds.1]
  have hsq : b*b-6*b+3=0 := by
    unfold b
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)]
  have he : b * (upper u : ℝ) - (6 * (upper u : ℝ) - 3 * (u : ℝ)) =
      (6-b) * (b * (u : ℝ) - (upper u : ℝ)) := by
    linear_combination (u : ℝ) * hsq
  have hl : 6 * (upper u : ℝ) - 3 * (u : ℝ) ≤ b * (upper u : ℝ) := by
    have := mul_nonneg hγ0 (sub_nonneg.2 h1)
    linarith
  have hu : b * (upper u : ℝ) < 6 * (upper u : ℝ) - 3 * (u : ℝ) + 1 := by
    have := mul_le_mul_of_nonneg_left (show b * (u : ℝ) - (upper u : ℝ) ≤ 1 by linarith) hγ0
    linarith
  have heq : ⌊b * (upper u : ℝ)⌋ = 6 * (upper u : ℤ) - 3 * (u : ℤ) :=
    (Int.floor_eq_iff).2 (by push_cast; exact ⟨hl,hu⟩)
  have heq' : ⌊b * (upper u : ℝ)⌋ = (upper (upper u) : ℤ) :=
    (Int.floor_eq_iff).2 (by push_cast; exact ⟨h3,h4⟩)
  exact heq'.symm.trans heq

/-- On same-parity consecutive upper terms, the lower term is half their indicated difference. -/
lemma lower_rel (u : ℕ) (h : (upper u : ℤ) % 2 = (u : ℤ) % 2) :
    2 * (lower u : ℤ) = (upper u : ℤ) - 3 * (u : ℤ) := by
  obtain ⟨h1,h2⟩ := upper_bounds u
  let t : ℤ := ((upper u : ℤ) - 3 * (u : ℤ)) / 2
  have ht : 2 * t = (upper u : ℤ) - 3 * (u : ℤ) := by dsimp [t]; omega
  have ht' : 2 * (t : ℝ) = (upper u : ℝ) - 3 * (u : ℝ) := by exact_mod_cast ht
  have hs : (u : ℝ) * OMA.S_oeis_a022163.slope = (b * (u : ℝ) - 3 * (u : ℝ)) / 2 := by rw [slope_eq]; ring
  have hb0 : 0 ≤ (u : ℝ) * OMA.S_oeis_a022163.slope := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hf : ⌊(u : ℝ) * OMA.S_oeis_a022163.slope⌋ = t :=
    Int.floor_eq_iff.2 (by constructor <;> linarith)
  unfold lower
  rw [Int.toNat_of_nonneg (Int.floor_nonneg.2 hb0), hf]
  exact ht

lemma lower_one : lower 1 = 1 := by
  have hz : ⌊(1:ℝ) * OMA.S_oeis_a022163.slope⌋ = 1 := Int.floor_eq_iff.2 (by
    rw [slope_eq]; unfold b
    have h := sqrt_bounds
    push_cast
    constructor <;> linarith)
  unfold lower
  norm_num at hz ⊢
  rw [hz]
  rfl

lemma upper_one : upper 1 = 5 := by
  have hz : ⌊(1:ℝ) * (OMA.S_oeis_a022163.slope / (OMA.S_oeis_a022163.slope-1))⌋ = 5 := Int.floor_eq_iff.2 (by
    rw [upper_slope]; unfold b
    have h := sqrt_bounds
    push_cast
    constructor <;> linarith)
  unfold upper
  norm_num at hz ⊢
  rw [hz]
  rfl

noncomputable def u : ℕ → ℕ
  | 0 => 1
  | n+1 => upper (u n)

lemma u_rec (n : ℕ) :
    (u (n+2) : ℤ) = 6 * (u (n+1) : ℤ) - 3 * (u n : ℤ) := upper_rec (u n)

lemma u_parity (n : ℕ) : (u (n+1) : ℤ) % 2 = (u n : ℤ) % 2 := by
  induction n with
  | zero => norm_num [u,upper_one]
  | succ n =>
    change (u (n+2) : ℤ) % 2 = (u (n+1) : ℤ) % 2
    rw [u_rec]
    omega

lemma pair_eq (n : ℕ) : rowPair n = (lower (u n),u (n+1)) := by
  induction n with
  | zero => simp [rowPair,u,lower_one]
  | succ n ih => simp only [rowPair, ih]; rfl

lemma even_term (k : ℕ) : term (2*k) = lower (u k) := by
  unfold term
  rw [if_pos (by omega), show 2*k/2=k by omega,pair_eq]

lemma odd_term (k : ℕ) : term (2*k+1) = u (k+1) := by
  unfold term
  rw [if_neg (by omega), show (2*k+1)/2=k by omega,pair_eq]

lemma rec (n : ℕ) :
    (term (n+4) : ℤ) = 6 * (term (n+2) : ℤ) - 3 * (term n : ℤ) := by
  by_cases h : n % 2 = 0
  · obtain ⟨k,rfl⟩ : ∃ k, n=2*k := ⟨n/2,by omega⟩
    rw [show 2*k+4=2*(k+2) by omega, show 2*k+2=2*(k+1) by omega]
    simp only [even_term]
    have h0 := lower_rel (u k) (u_parity k)
    have h1 := lower_rel (u (k+1)) (u_parity (k+1))
    have h2 := lower_rel (u (k+2)) (u_parity (k+2))
    have hr0 := u_rec k
    have hr1 := u_rec (k+1)
    change (u (k+3) : ℤ) = 6*(u (k+2) : ℤ) - 3*(u (k+1) : ℤ) at hr1
    change 2 * (lower (u k) : ℤ) = (u (k+1) : ℤ) - 3 * (u k : ℤ) at h0
    change 2 * (lower (u (k+1)) : ℤ) = (u (k+2) : ℤ) - 3 * (u (k+1) : ℤ) at h1
    change 2 * (lower (u (k+2)) : ℤ) = (u (k+3) : ℤ) - 3 * (u (k+2) : ℤ) at h2
    linarith
  · obtain ⟨k,rfl⟩ : ∃ k, n=2*k+1 := ⟨n/2,by omega⟩
    rw [show 2*k+1+4=2*(k+2)+1 by omega,show 2*k+1+2=2*(k+1)+1 by omega]
    simpa only [odd_term] using u_rec (k+1)

lemma term_zero : (term 0 : ℤ) = 1 := by
  rw [show (0:ℕ) = 2 * 0 by decide, even_term]
  simp [u,lower_one]

lemma term_one : (term 1 : ℤ) = 5 := by
  rw [show (1:ℕ) = 2 * 0 + 1 by decide, odd_term]
  simp [u,upper_one]

lemma u_two : (u 2 : ℤ) = 27 := by
  have h := u_rec 0
  change (u 2 : ℤ) = 6 * (u 1 : ℤ) - 3 * (u 0 : ℤ) at h
  rw [h]
  norm_num [u,upper_one]

lemma term_two : (term 2 : ℤ) = 6 := by
  rw [show (2:ℕ) = 2 * 1 by decide, even_term]
  have h := lower_rel (u 1) (u_parity 1)
  change 2 * (lower (u 1) : ℤ) = (u 2 : ℤ) - 3 * (u 1 : ℤ) at h
  have h' : (u 1 : ℤ) = 5 := by simp [u,upper_one]
  rw [u_two,h'] at h
  omega

lemma term_three : (term 3 : ℤ) = 27 := by
  rw [show (3:ℕ) = 2 * 1 + 1 by decide, odd_term]
  exact u_two

end OMA.Spectral

namespace OMA.SpectralGF
open PowerSeries

lemma of_recurrence (s : ℕ → ℤ) (h0 : s 0 = 1) (h1 : s 1 = 5)
    (h2 : s 2 = 6) (h3 : s 3 = 27)
    (h : ∀ n, s (n+4) = 6*s (n+2) - 3*s n) :
    (3 * X^4 - 6 * X^2 + 1 : PowerSeries ℤ) * mk s =
      1 + 5 * X - 3 * X^3 := by
  have lhs : (3 * X^4 - 6 * X^2 + 1 : PowerSeries ℤ) * mk s =
      C (3:ℤ) * (X^4 * mk s) - C (6:ℤ) * (X^2 * mk s) + mk s := by
    simp only [map_ofNat]
    ring
  have rhs : (1 + 5 * X - 3 * X^3 : PowerSeries ℤ) =
      1 + C (5:ℤ) * X - C (3:ℤ) * X^3 := by
    simp only [map_ofNat]
    <;> rfl
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk,
    coeff_one, coeff_X, coeff_X_pow]
  cases n with
  | zero => norm_num [h0]
  | succ n =>
    cases n with
    | zero => norm_num [h1]
    | succ n =>
      cases n with
      | zero => norm_num [h0,h2]
      | succ n =>
        cases n with
        | zero => norm_num [h1,h3]
        | succ n =>
          change _ = _
          simp [h, show n+1+1+1+1 = n+4 by omega,
            show n+4 ≠ 1 by omega, show n+4 ≠ 3 by omega]
          <;> ring

end OMA.SpectralGF

open OMA.S_oeis_a022163 OMA.Spectral in
theorem OMA.solution : type_of% @OMA.S_oeis_a022163.main :=
  ⟨rec, OMA.SpectralGF.of_recurrence
    (fun n => (term n : ℤ)) term_zero term_one term_two term_three rec⟩
