import OMAStatements.S_mse_199784

namespace AsymmetricGame

open Finset Matrix OMA.S_mse_199784

abbrev V := Fin 7 → ℝ
abbrev M := Matrix (Fin 7) (Fin 7) ℝ

def A : M :=
  !![1, 1, -1, 1, -1, 1, -1;
     1, -1, 1, 1, 1, -1, -1;
     -1, 1, -1, 1, -1, -1, 1;
     1, 1, 1, -1, -1, -1, 1;
     -1, 1, -1, -1, 1, 1, -1;
     1, -1, -1, -1, 1, -1, 1;
     -1, -1, 1, 1, -1, 1, -1]

noncomputable def w : V := fun i => ((i.val : ℝ) + 1) / 28
noncomputable def v : ℝ := -1 / 14

lemma symm (i j : Fin 7) : A i j = A j i := by
  fin_cases i <;> fin_cases j <;> rfl

lemma aw (i : Fin 7) : (A *ᵥ w) i = v := by
  fin_cases i <;> norm_num [A, w, v, mulVec, dotProduct, Fin.sum_univ_succ]

lemma wpos (i : Fin 7) : 0 < w i := by
  unfold w
  positivity

lemma simplex : w ∈ stdSimplex ℝ (Fin 7) := by
  refine ⟨fun i => (wpos i).le, ?_⟩
  norm_num [w, Fin.sum_univ_succ]

lemma injective : Function.Injective A.mulVec := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  simp [A, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6
  funext i
  fin_cases i <;> linarith!

lemma payoff_rows (x y : V) : payoff A x y = ∑ i, x i * (A *ᵥ y) i := by
  simp only [payoff, mulVec, dotProduct, mul_sum, mul_assoc]

lemma payoff_symm (x y : V) : payoff A x y = payoff A y x := by
  unfold payoff
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  rw [symm i j]
  ring

lemma payoff_w (x : V) (hx : x ∈ stdSimplex ℝ (Fin 7)) : payoff A x w = v := by
  rw [payoff_rows]
  simp only [aw, ← sum_mul, hx.2, one_mul]

lemma payoff_pure (i : Fin 7) (y : V) : payoff A (Pi.single i 1) y = (A *ᵥ y) i := by
  rw [payoff_rows]
  simp [Pi.single_apply, ite_mul, eq_comm]

lemma forced (x : V) (hx : x ∈ stdSimplex ℝ (Fin 7)) (s : ℝ) (hs : s ≠ 0)
    (h : ∀ i, 0 ≤ s * ((A *ᵥ x) i - v)) : x = w := by
  have hsum : (∑ i, s * (w i * ((A *ᵥ x) i - v))) = 0 := by
    rw [← mul_sum]
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← payoff_rows, payoff_symm, payoff_w x hx,
      ← sum_mul, simplex.2, one_mul, sub_self, mul_zero]
  apply injective
  funext i
  rw [aw]
  have hi := (sum_eq_zero_iff_of_nonneg (fun j _ => by
    rw [mul_left_comm]
    exact mul_nonneg (wpos j).le (h j))).mp hsum i (mem_univ i)
  simpa only [mul_eq_zero, hs, (wpos i).ne', false_or, sub_eq_zero] using hi

lemma perm_unique (σ τ : Equiv.Perm (Fin 7)) (h : ∀ i j, A (σ i) (τ j) = A i j) :
    τ = 1 := by
  have e : (fun j => w (τ j)) = w := by
    apply injective
    funext i
    rw [aw, ← aw (σ i)]
    change (∑ j, A i j * w (τ j)) = ∑ j, A (σ i) j * w j
    simp_rw [← h i]
    exact Equiv.sum_comp τ (fun j => A (σ i) j * w j)
  ext j
  have hj := congrFun e j
  simp only [w] at hj
  exact_mod_cast (show ((τ j).val : ℝ) = (j.val : ℝ) by linarith)

lemma unique (x y : V) (h : IsNashEquilibrium A x y) : x = w ∧ y = w := by
  obtain ⟨hx, hy, hrow, hcol⟩ := h
  have hu : payoff A x y = v := le_antisymm
    (by simpa only [payoff_w x hx] using hcol w simplex)
    (by simpa only [payoff_symm w y, payoff_w y hy] using hrow w simplex)
  constructor
  · apply forced x hx 1 (by norm_num)
    intro i
    have hi := hcol (Pi.single i 1) (single_mem_stdSimplex ℝ i)
    rw [hu, payoff_symm x, payoff_pure] at hi
    linarith
  · apply forced y hy (-1) (by norm_num)
    intro i
    have hi := hrow (Pi.single i 1) (single_mem_stdSimplex ℝ i)
    rw [hu, payoff_pure] at hi
    linarith

end AsymmetricGame

open AsymmetricGame in
theorem OMA.solution : type_of% @OMA.S_mse_199784.main := by
  refine ⟨7, 7, A, by decide, by decide, ?_, ?_, w, w, ⟨simplex, simplex, ?_, ?_⟩, wpos, wpos, unique⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [A]
  · intro σ τ h
    exact ⟨perm_unique τ σ (fun i j => by rw [symm, h, symm]), perm_unique σ τ h⟩
  · intro x hx
    rw [payoff_w x hx, payoff_w w simplex]
  · intro y hy
    rw [payoff_w w simplex, payoff_symm w y, payoff_w y hy]
