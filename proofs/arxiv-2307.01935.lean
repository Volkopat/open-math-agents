import OMAStatements.S_arxiv_2307_01935

namespace OMA.P2307

open OMA.S_arxiv_2307_01935

noncomputable def s : ℝ := Real.sqrt 2

def bodyOf : Fin 5 → Fin 3 := ![0, 0, 1, 2, 2]

def m : Fin 5 → ℝ := fun _ => 1

def r : Fin 5 → Fin 2 → ℝ := ![![-1, -1], ![1, -1], ![1, 1], ![-1, 1], ![0, 0]]

noncomputable def lam : ℝ := 1 / 4 + 5 * s / 16

lemma hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)

lemma hlam : 0 < lam := by
  have := hs0
  unfold lam
  positivity

lemma dist_eq (u v : Fin 2 → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 = c ^ 2) : euclidDist u v = c := by
  unfold euclidDist
  rw [h]
  exact Real.sqrt_sq hc

lemma hs4 : s ^ 4 = 4 := by
  rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]
  norm_num

lemma e0 : (1 : ℝ) * 1 / 0 ^ 3 = 0 := by norm_num

lemma e1 : (1 : ℝ) * 1 / 2 ^ 3 = 1 / 8 := by norm_num

lemma e2 : (1 : ℝ) * 1 / (2 * s) ^ 3 = s / 32 := by
  have := hs0
  rw [div_eq_iff (by positivity)]
  rw [show s / 32 * (2 * s) ^ 3 = s ^ 4 / 4 by ring, hs4]
  norm_num

lemma e3 : (1 : ℝ) * 1 / s ^ 3 = s / 4 := by
  have := hs0
  rw [div_eq_iff (by positivity)]
  rw [show s / 4 * s ^ 3 = s ^ 4 / 4 by ring, hs4]
  norm_num

lemma force0 : gravForce m r 1 0 = (-lam) • r 0 := by
  unfold gravForce
  rw [Fin.sum_univ_five]
  rw [dist_eq (r 0) (r 0) 0 le_rfl (by simp [r] <;> nlinarith [hs2]), dist_eq (r 1) (r 0) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 2) (r 0) (2 * s) (by have := hs0; positivity) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 3) (r 0) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 4) (r 0) s hs0.le (by simp [r] <;> nlinarith [hs2])]
  simp only [m, e0, e1, e2, e3]
  funext c
  fin_cases c <;> simp [r, lam] <;> ring

lemma force1 : gravForce m r 1 1 = (-lam) • r 1 := by
  unfold gravForce
  rw [Fin.sum_univ_five]
  rw [dist_eq (r 0) (r 1) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 1) (r 1) 0 le_rfl (by simp [r] <;> nlinarith [hs2]), dist_eq (r 2) (r 1) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 3) (r 1) (2 * s) (by have := hs0; positivity) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 4) (r 1) s hs0.le (by simp [r] <;> nlinarith [hs2])]
  simp only [m, e0, e1, e2, e3]
  funext c
  fin_cases c <;> simp [r, lam] <;> ring

lemma force2 : gravForce m r 1 2 = (-lam) • r 2 := by
  unfold gravForce
  rw [Fin.sum_univ_five]
  rw [dist_eq (r 0) (r 2) (2 * s) (by have := hs0; positivity) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 1) (r 2) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 2) (r 2) 0 le_rfl (by simp [r] <;> nlinarith [hs2]), dist_eq (r 3) (r 2) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 4) (r 2) s hs0.le (by simp [r] <;> nlinarith [hs2])]
  simp only [m, e0, e1, e2, e3]
  funext c
  fin_cases c <;> simp [r, lam] <;> ring

lemma force3 : gravForce m r 1 3 = (-lam) • r 3 := by
  unfold gravForce
  rw [Fin.sum_univ_five]
  rw [dist_eq (r 0) (r 3) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 1) (r 3) (2 * s) (by have := hs0; positivity) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 2) (r 3) 2 (by norm_num) (by simp [r] <;> nlinarith [hs2]), dist_eq (r 3) (r 3) 0 le_rfl (by simp [r] <;> nlinarith [hs2]), dist_eq (r 4) (r 3) s hs0.le (by simp [r] <;> nlinarith [hs2])]
  simp only [m, e0, e1, e2, e3]
  funext c
  fin_cases c <;> simp [r, lam] <;> ring

lemma force4 : gravForce m r 1 4 = (-lam) • r 4 := by
  unfold gravForce
  rw [Fin.sum_univ_five]
  rw [dist_eq (r 0) (r 4) s hs0.le (by simp [r] <;> nlinarith [hs2]), dist_eq (r 1) (r 4) s hs0.le (by simp [r] <;> nlinarith [hs2]), dist_eq (r 2) (r 4) s hs0.le (by simp [r] <;> nlinarith [hs2]), dist_eq (r 3) (r 4) s hs0.le (by simp [r] <;> nlinarith [hs2]), dist_eq (r 4) (r 4) 0 le_rfl (by simp [r] <;> nlinarith [hs2])]
  simp only [m, e0, e1, e2, e3]
  funext c
  fin_cases c <;> simp [r, lam] <;> ring

lemma force : ∀ i, gravForce m r 1 i = (-lam) • r i := by
  intro i
  fin_cases i
  exacts [force0, force1, force2, force3, force4]

lemma hb0 : bodyMasses bodyOf (0 : Fin 3) = {0, 1} := by decide

lemma hb1 : bodyMasses bodyOf (1 : Fin 3) = {2} := by decide

lemma hb2 : bodyMasses bodyOf (2 : Fin 3) = {3, 4} := by decide

lemma torque0 : (∑ i ∈ bodyMasses bodyOf (0 : Fin 3),
    cross2 (r i - bodyCenter bodyOf m r 0) (gravForce m r 1 i)) = 0 := by
  rw [bodyCenter, bodyMass, hb0]
  simp only [force]
  simp [cross2, m, r, Finset.sum_pair]
  ring

lemma torque1 : (∑ i ∈ bodyMasses bodyOf (1 : Fin 3),
    cross2 (r i - bodyCenter bodyOf m r 1) (gravForce m r 1 i)) = 0 := by
  rw [bodyCenter, bodyMass, hb1]
  simp [force, cross2, m, r]

lemma torque2 : (∑ i ∈ bodyMasses bodyOf (2 : Fin 3),
    cross2 (r i - bodyCenter bodyOf m r 2) (gravForce m r 1 i)) = 0 := by
  rw [bodyCenter, bodyMass, hb2]
  simp only [force]
  simp [cross2, m, r, Finset.sum_pair]
  ring

lemma hRE : IsRelativeEquilibrium bodyOf m r 1 := by
  refine ⟨Real.sqrt lam, (Real.sqrt_pos.mpr hlam).ne', ?_, ?_⟩
  · rw [Fin.sum_univ_five]
    funext c
    fin_cases c <;> simp [m, r]
  · intro k
    rw [Real.sq_sqrt hlam.le]
    constructor
    · simp only [force]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [m]
    · fin_cases k
      exacts [torque0, torque1, torque2]

lemma hinj : Function.Injective r := by
  intro i j hij
  have h0 := congrFun hij 0
  have h1 := congrFun hij 1
  fin_cases i <;> fin_cases j <;> simp [r] at h0 h1 ⊢ <;>
    (try (first | (norm_num at h0; done) | (norm_num at h1; done)))

lemma hfirst : ∀ i ∈ bodyMasses bodyOf (1 : Fin 3), InFirstCone (r 0) (r 1) (r i) := by
  rw [hb1]
  intro i hi
  rw [Finset.mem_singleton] at hi
  subst hi
  unfold InFirstCone axialCoord perpCoord dot2 cross2 dumbbellMidpoint
  simp [r]
  norm_num

lemma hsec1 : ¬ InSecondCone (r 0) (r 1) (r 2) := by
  unfold InSecondCone axialCoord perpCoord dot2 cross2 dumbbellMidpoint
  simp [r]
  norm_num

lemma hsec2 : ¬ InSecondCone (r 0) (r 1) (r 4) := by
  unfold InSecondCone axialCoord perpCoord dot2 cross2 dumbbellMidpoint
  simp [r]

end OMA.P2307

open OMA.P2307 OMA.S_arxiv_2307_01935 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2307_01935.main) := by
  intro h
  have hmain := h 3 (Fin 5) bodyOf m r 1 0 1 (by norm_num) one_pos (by intro i; simp [m]) hinj
    (by decide) rfl rfl (by decide) (by decide) hRE
  obtain ⟨k, hk0, hk⟩ := hmain.1 ⟨1, by decide, hfirst⟩
  fin_cases k
  · exact hk0 rfl
  · exact hsec1 (hk 2 (by decide))
  · exact hsec2 (hk 4 (by decide))
