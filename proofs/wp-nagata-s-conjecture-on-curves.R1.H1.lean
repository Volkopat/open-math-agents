import OMAReductions.R_wp_nagata_s_conjecture_on_curves_R1
import Mathlib

private theorem dense_nonvanishing {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℂ) (hP : P ≠ 0) :
    Dense {x : ι → ℂ | MvPolynomial.eval x P ≠ 0} := by
  classical
  apply Metric.dense_iff.mpr
  intro x ε hε
  by_contra h
  apply hP
  apply MvPolynomial.funext_set (fun i => Metric.ball (x i) ε)
    (fun i => infinite_of_mem_nhds (x i) (Metric.ball_mem_nhds _ hε))
  intro y hy
  rw [map_zero]
  by_contra hn
  apply h
  exact ⟨y, Metric.mem_ball.mpr ((dist_pi_lt_iff hε).mpr
    (fun i => Metric.mem_ball.mp (hy i (Set.mem_univ i)))), hn⟩

theorem OMA.solution : OMA.R_wp_nagata_s_conjecture_on_curves_R1.H1 := by
  classical
  intro r E hE
  -- The extra polynomials separate the first coordinates of the marked points.
  let F : ℕ ⊕ (Fin r × Fin r) → MvPolynomial (Fin r × Fin 2) ℂ
    | .inl n => E n
    | .inr (i, j) => if i = j then 1 else MvPolynomial.X (i, 0) - MvPolynomial.X (j, 0)
  have hF (k) : F k ≠ 0 := by
    cases k with
    | inl n => exact hE n
    | inr ij =>
      rcases ij with ⟨i, j⟩
      by_cases h : i = j
      · simp [F, h]
      · simp only [F, h, if_false]
        exact sub_ne_zero.mpr (fun he => h (congrArg Prod.fst (MvPolynomial.X_injective he)))
  let U (k) := {x : (Fin r × Fin 2) → ℂ | MvPolynomial.eval x (F k) ≠ 0}
  have hd : Dense (⋂ k, U k) := dense_iInter_of_isOpen
    (fun k => isOpen_ne_fun (MvPolynomial.continuous_eval (F k)) continuous_const)
    (fun k => dense_nonvanishing (F k) (hF k))
  obtain ⟨x, hx⟩ := hd.nonempty
  have hall (k) : MvPolynomial.eval x (F k) ≠ 0 := Set.mem_iInter.mp hx k
  refine ⟨fun i j => x (i, j), ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hc : x (i, 0) = x (j, 0) := congrFun hij 0
    apply hall (.inr (i, j))
    simp only [F, if_neg hne, map_sub, MvPolynomial.eval_X, hc, sub_self]
  · intro n
    exact hall (.inl n)
