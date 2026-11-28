import FormalConjectures.Arxiv.«2602.05192».FirstProof4

-- Problem: First Proof, Theorem 4 — four 2
-- Upstream: formal-conjectures FormalConjectures/Arxiv/2602.05192/FirstProof4.lean:167 (declaration Arxiv.«2602.05192».four_2)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAFour2
open Polynomial ENNReal Arxiv.«2602.05192»

theorem invPhi (a b : ℝ) : 1 / Φ ((X - C a) * (X - C b)) = ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  have hroots : ((X - C a) * (X - C b)).roots = {a, b} := by
    rw [roots_mul (by exact mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)),
      roots_X_sub_C, roots_X_sub_C]; rfl
  unfold Φ
  rw [hroots]
  by_cases hab : a = b
  · subst hab
    have : ¬ ({a, a} : Multiset ℝ).Nodup := by simp
    simp
  · have hnd : ({a, b} : Multiset ℝ).Nodup := by simp [hab]
    rw [if_pos hnd]
    have ht : ({a, b} : Multiset ℝ).toFinset = {a, b} := by ext; simp
    simp only [ht]
    have erase_root {x y : ℝ} (h : x ≠ y) : ({x, y} : Finset ℝ).erase x = {y} :=
      Finset.erase_insert (by simpa using h)
    rw [Finset.sum_pair hab, erase_root hab, Finset.pair_comm a b, erase_root (Ne.symm hab)]
    simp only [Finset.sum_singleton]
    have hd : (a - b) ≠ 0 := sub_ne_zero.mpr hab
    have hpos : 0 < (a - b) ^ 2 := by positivity
    have heq : (1 / (a - b)) ^ 2 + (1 / (b - a)) ^ 2 = 2 / (a - b) ^ 2 := by
      have : b - a = -(a - b) := by ring
      rw [this]; field_simp; ring
    rw [heq]
    have h2 : (0 : ℝ) < 2 / (a - b) ^ 2 := by positivity
    rw [one_div, ← ENNReal.ofReal.eq_def, ← ENNReal.ofReal_inv_of_pos h2]
    congr 1
    field_simp

theorem quad_eq (a b : ℝ) : (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
  simp only [C_add, C_mul]; ring

theorem coeffs (s p : ℝ) : (X ^ 2 - C s * X + C p : ℝ[X]).coeff 2 = 1 ∧
    (X ^ 2 - C s * X + C p : ℝ[X]).coeff 1 = -s ∧ (X ^ 2 - C s * X + C p : ℝ[X]).coeff 0 = p := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_X, coeff_C]

theorem conv2 (s p t q : ℝ) :
    finiteAdditiveConvolution 2 (X ^ 2 - C s * X + C p : ℝ[X]) (X ^ 2 - C t * X + C q) =
      X ^ 2 - C (s + t) * X + C (p + q + s * t / 2) := by
  obtain ⟨h2, h1, h0⟩ := coeffs s p
  obtain ⟨g2, g1, g0⟩ := coeffs t q
  simp only [finiteAdditiveConvolution, Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_map, Finset.sum_singleton]
  simp [h2, h1, h0, g2, g1, g0, Nat.factorial, smul_eq_C_mul]
  rw [show s * t / 2 = 2⁻¹ * s * t by ring, C_mul, C_mul]
  ring

theorem main (p q : ℝ[X]) : FourProp p q 2 := by
  intro hpd hpr hqd hqr hpm hqm
  have hpn : p.natDegree = 2 := natDegree_eq_of_degree_eq_some hpd
  have hqn : q.natDegree = 2 := natDegree_eq_of_degree_eq_some hqd
  have hp := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm (by rw [hpr, hpn])
  have hq := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hqm (by rw [hqr, hqn])
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp (by exact_mod_cast hpr)
  obtain ⟨c, d, hcd⟩ := Multiset.card_eq_two.mp (by exact_mod_cast hqr)
  rw [hab] at hp
  rw [hcd] at hq
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton] at hp hq
  rw [← hp, ← hq, invPhi, invPhi, quad_eq, quad_eq, conv2]
  set S := a + b + (c + d)
  set D := (a - b) ^ 2 + (c - d) ^ 2
  have hD : 0 ≤ D := by positivity
  have hfac : (X ^ 2 - C S * X + C (a * b + c * d + (a + b) * (c + d) / 2) : ℝ[X]) =
      (X - C ((S + √D) / 2)) * (X - C ((S - √D) / 2)) := by
    rw [quad_eq]
    have e1 : (S + √D) / 2 + (S - √D) / 2 = S := by ring
    have e2 : (S + √D) / 2 * ((S - √D) / 2) = a * b + c * d + (a + b) * (c + d) / 2 := by
      have : √D ^ 2 = D := Real.sq_sqrt hD
      nlinarith [this]
    rw [e1, e2]
  rw [hfac, invPhi, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq
  congr 1
  have : √D ^ 2 = D := Real.sq_sqrt hD
  have e3 : ((S + √D) / 2 - (S - √D) / 2) = √D := by ring
  rw [e3, this]
  ring

end OMAFour2

theorem OMA.solution : type_of% @Arxiv.«2602.05192».four_2 := OMAFour2.main
