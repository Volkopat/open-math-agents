import OMAStatements.S_oeis_a138467
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

open OMA.S_oeis_a138467

namespace NestedFloor

private lemma slope_properties (p : ℕ) (hp : 2 < p) :
    0 < slope p ∧ slope p < 1 ∧ (slope p)^2 + p * slope p = p ∧ Irrational (slope p) := by
  have hpR : (2:ℝ) < p := by exact_mod_cast hp
  have hs := Real.sq_sqrt (show 0 ≤ (p:ℝ)*((p:ℝ)+4) by positivity)
  have lo : (p:ℝ) < Real.sqrt ((p:ℝ)*((p:ℝ)+4)) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hi : Real.sqrt ((p:ℝ)*((p:ℝ)+4)) < (p:ℝ)+2 :=
    (Real.sqrt_lt' (by positivity)).2 (by nlinarith)
  have ns : ¬ IsSquare (p*(p+4)) := by
    rintro ⟨k, he⟩
    by_cases h : k ≤ p+1
    · have := Nat.mul_le_mul h h
      nlinarith
    · have hk : p+2 ≤ k := by omega
      have := Nat.mul_le_mul hk hk
      nlinarith
  have irr : Irrational (Real.sqrt ((p:ℝ)*((p:ℝ)+4))) := by
    simpa using (irrational_sqrt_natCast_iff.mpr ns)
  refine ⟨?_, ?_, ?_, (irr.sub_natCast p).div_natCast (by decide : (2:ℕ) ≠ 0)⟩ <;>
    unfold slope <;> nlinarith

private noncomputable def F (c : ℝ) (n : ℕ) : ℕ := ⌊c*((n:ℝ)+1)⌋₊

-- The threshold at t = 1-c determines both floors. Irrationality excludes equality.
private lemma complementary (p N : ℕ) (hp : 2 < p) (hN : 0 < N) (c : ℝ)
    (hc : 0 < c) (hc1 : c < 1) (eqn : c^2+(p:ℝ)*c=p) (irr : Irrational c) :
    ⌊c*((N:ℝ)+1)⌋₊ + ⌊c*((⌊c*(N:ℝ)⌋₊:ℝ)+1)/(p:ℝ)⌋₊ = N := by
  let k := ⌊c*(N:ℝ)⌋₊
  let t := c*(N:ℝ) - (k:ℝ)
  let v := c*((k:ℝ)+1)/(p:ℝ)
  have hp2 : (2:ℝ) < p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hn0 : (0:ℝ) < N := by exact_mod_cast hN
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hx : 0 ≤ c*((N:ℝ)+1) := by positivity
  have hk0 : (k:ℝ) ≤ c*N := Nat.floor_le (by positivity)
  have hk1 : c*N < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hkN : k < N := by
    have hsmall : c*N < (N:ℝ) := by nlinarith only [mul_pos (sub_pos.mpr hc1) hn0]
    exact_mod_cast hk0.trans_lt hsmall
  have ht0 : 0 ≤ t := sub_nonneg.mpr hk0
  have ht1 : t < 1 := by dsimp [t]; linarith
  have shift : v-((N:ℝ)-k) = (c*(1-t)-(p:ℝ)*t)/(p:ℝ) := by
    dsimp [v,t]
    field_simp [hp0.ne']
    linear_combination (N:ℝ)*eqn
  have threshold : c*(1-t)-(p:ℝ)*t = ((p:ℝ)+c)*(1-c-t) := by
    nlinarith only [eqn]
  have lower : -1 < v-((N:ℝ)-k) := by
    rw [shift]; apply (lt_div_iff₀ hp0).2
    nlinarith only [mul_pos hp0 (sub_pos.mpr ht1), mul_nonneg hc.le (sub_nonneg.mpr ht1.le)]
  have upper : v-((N:ℝ)-k) < 1 := by
    rw [shift]; apply (div_lt_iff₀ hp0).2
    nlinarith only [hp2, hc1, mul_nonneg hc.le ht0, mul_nonneg hp0.le ht0]
  have cut : t+c ≠ 1 := by
    intro h
    have hz := (irr.mul_natCast (Nat.succ_ne_zero N)).ne_nat (k+1)
    simp only [Nat.cast_succ] at hz
    apply hz
    dsimp [t] at h
    linarith
  change ⌊c*((N:ℝ)+1)⌋₊ + ⌊v⌋₊ = N
  rcases lt_or_gt_of_ne cut with low | high
  · have pos : 0 < v-((N:ℝ)-k) := by
      rw [shift, threshold]; exact div_pos (mul_pos (by linarith) (by linarith)) hp0
    have fy : ⌊c*((N:ℝ)+1)⌋₊ = k := (Nat.floor_eq_iff hx).2 (by
      dsimp [t] at low
      constructor <;> linarith)
    have fv : ⌊v⌋₊ = N-k := (Nat.floor_eq_iff hv).2 (by
      rw [Nat.cast_sub hkN.le]
      constructor <;> linarith)
    omega
  · have neg : v-((N:ℝ)-k) < 0 := by
      rw [shift, threshold]; exact div_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by linarith) (by linarith)) hp0
    have fy : ⌊c*((N:ℝ)+1)⌋₊ = k+1 := (Nat.floor_eq_iff hx).2 (by
      dsimp [t] at high
      push_cast
      constructor <;> linarith)
    have fv : ⌊v⌋₊ = N-k-1 := (Nat.floor_eq_iff hv).2 (by
      rw [Nat.cast_sub (by omega : 1 ≤ N-k), Nat.cast_sub hkN.le, Nat.cast_one]
      constructor <;> linarith)
    omega

private lemma rec_formula (p n : ℕ) (hp : 2 < p) :
    F (slope p) (n+1) = n+1 - F (slope p) (F (slope p) n)/p := by
  obtain ⟨hc, hu, he, hi⟩ := slope_properties p hp
  have h := complementary p (n+1) hp (by omega) _ hc hu he hi
  rw [Nat.floor_div_natCast] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  simp only [F, Nat.cast_add, Nat.cast_one]
  omega

private lemma step (p n : ℕ) : a p (n+1) = n+1 - a p (a p n)/p := by
  unfold a
  rw [bounded]

private lemma formula (p : ℕ) (hp : 2 < p) (n : ℕ) : a p n = F (slope p) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have hu := (slope_properties p hp).2.1
      simp [a, bounded, F, Nat.floor_eq_zero.mpr hu]
    | succ n =>
      rw [step, ih (a p n) (bounded p n).isLt, ih n (Nat.lt_succ_self _), rec_formula p n hp]

end NestedFloor

theorem OMA.solution : type_of% @OMA.S_oeis_a138467.main := by
  intro p hp n _
  exact NestedFloor.formula p hp n
