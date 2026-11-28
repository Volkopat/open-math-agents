import OMAReductions.R_OeisA115257_conjecture_R1
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Factor degrees of central-binomial truncations

For the even truncations of the Catalan-weighted series, every rational divisor has
even degree. The coefficient ratios increase, so each consecutive triple gives a
nonnegative quadratic on the real line. Pairing the triples leaves half the constant
term as a uniform positive lower bound. The remaining questions concern even-degree
factors, and odd-degree factors of odd truncations.
-/

namespace OMA.R_OeisA115257_conjecture_R1_H2_R1

open Polynomial OeisA115257

lemma even_truncation_pos (m : ℕ) (x : ℝ) :
    0 < ((polyQ (2 * m)).map (algebraMap ℚ ℝ)).eval x := by
  let c (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) ^ 2 / ((k : ℝ) + 1)
  let r (k : ℕ) : ℝ := 4 * (2 * (k : ℝ) + 1) ^ 2 / (((k : ℝ) + 1) * (k + 2))
  have hc (k : ℕ) : 0 ≤ c k := by dsimp [c]; positivity
  have hr (k : ℕ) : c (k + 1) = r k * c k := by
    have h : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have h' : (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) / ((k : ℝ) + 1) :=
      (eq_div_iff hk).2 (by linarith only [h])
    dsimp [c, r]
    push_cast
    rw [h']
    field_simp
    ring
  have hmono (k : ℕ) : r k ≤ r (k + 1) := by
    dsimp [r]
    push_cast
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [show 0 ≤ (8 * (k : ℝ) + 6) * ((k : ℝ) + 2) by positivity]
  have triple (k : ℕ) : 0 ≤ c k + 2 * c (k + 1) * x + c (k + 2) * x ^ 2 := by
    have h : 0 ≤ c k * (1 + r k * x) ^ 2 +
        ((r (k + 1) - r k) * c (k + 1)) * x ^ 2 :=
      add_nonneg (mul_nonneg (hc k) (sq_nonneg _))
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr (hmono k)) (hc _)) (sq_nonneg _))
    rw [hr (k + 1), hr k]
    rw [hr k] at h
    linarith only [h]
  have lower (j : ℕ) : 1 + c (2*j) * x ^ (2*j) ≤
      2 * ∑ k ∈ Finset.range (2*j + 1), c k * x ^ k := by
    induction j with
    | zero => norm_num [c, Nat.centralBinom]
    | succ j ih =>
      rw [Nat.mul_succ, show 2*j + 2 + 1 = (2*j+1) + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
      have hx : 0 ≤ x ^ (2*j) := by rw [pow_mul]; positivity
      have h := mul_nonneg hx (triple (2*j))
      rw [show 2*j+1+1 = 2*j+2 by omega]
      simp only [pow_add, pow_one]
      linarith only [ih, h]
  have hv : ((polyQ (2*m)).map (algebraMap ℚ ℝ)).eval x =
      ∑ k ∈ Finset.range (2*m + 1), c k * x ^ k := by
    simp [polyQ, c]
  rw [hv]
  have hx : 0 ≤ x ^ (2*m) := by rw [pow_mul]; positivity
  linarith [lower m, mul_nonneg (hc (2*m)) hx]

lemma even_degree_of_no_real_root (p : ℝ[X]) :
    (∀ x : ℝ, p.eval x ≠ 0) → Even p.natDegree := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu => simp [natDegree_eq_zero_of_isUnit hu]
  | mul a i ha hi ih =>
    intro h
    have ha' := ih (fun x hx => h x (by simp [hx]))
    have h1 : i.natDegree ≠ 1 := by
      intro hdeg
      obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one
        (show i.degree = 1 by rw [degree_eq_natDegree hi.ne_zero, hdeg]; rfl)
      exact h x (by simp [IsRoot.def.mp hx])
    have h2 := hi.natDegree_le_two
    have he : Even i.natDegree := by
      rcases (show i.natDegree = 0 ∨ i.natDegree = 2 by omega) with h₀ | h₂
      · simp [h₀]
      · simp [h₂]
    rw [natDegree_mul hi.ne_zero ha]
    exact he.add ha'

lemma divisor_degree_even (m : ℕ) {g : ℚ[X]} (hg : g ∣ polyQ (2*m)) :
    Even g.natDegree := by
  obtain ⟨f, hf⟩ := hg
  have h := even_degree_of_no_real_root (g.map (algebraMap ℚ ℝ)) (by
    intro x hx
    have hp := even_truncation_pos m x
    rw [hf, Polynomial.map_mul, Polynomial.eval_mul, hx, zero_mul] at hp
    exact (lt_irrefl _ hp))
  simpa using h

/-- The possible even-degree factors, at all remaining indices. -/
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → (¬ ∃ r : ℕ, n = 2^r) →
  ∀ g : ℚ[X], g.Monic → 2 ≤ g.natDegree → g.natDegree ≤ (polyQ n).natDegree / 2 →
    Even g.natDegree → ¬ g ∣ polyQ n

/-- Odd-degree factors need to be considered only at odd indices. -/
def H2 : Prop := ∀ n : ℕ, Odd n → 1 ≤ n → (¬ ∃ r : ℕ, n = 2^r) →
  ∀ g : ℚ[X], g.Monic → 2 ≤ g.natDegree → g.natDegree ≤ (polyQ n).natDegree / 2 →
    Odd g.natDegree → ¬ g ∣ polyQ n

theorem main : H1 → H2 → OMA.R_OeisA115257_conjecture_R1.H2 := by
  intro evenFactors oddFactors n hn hn' g hg hd hd' hdiv
  rcases Nat.even_or_odd g.natDegree with he | ho
  · exact evenFactors n hn hn' g hg hd hd' he hdiv
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | hno
    · rw [hm, ← two_mul] at hdiv
      exact (Nat.not_even_iff_odd.mpr ho) (divisor_degree_even m hdiv)
    · exact oddFactors n hno hn hn' g hg hd hd' ho hdiv

end OMA.R_OeisA115257_conjecture_R1_H2_R1
