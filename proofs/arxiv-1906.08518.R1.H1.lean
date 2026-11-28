import OMAReductions.R_arxiv_1906_08518_R1
import Mathlib

theorem OMA.solution : OMA.R_arxiv_1906_08518_R1.H1 := by
  classical
  intro r G hG
  let line (ij : Fin r × Fin 2) : Set ℂ :=
    Set.range (fun t : ℝ => (⟨(ij.1.val : ℝ), t⟩ : ℂ))
  have inf (ij : Fin r × Fin 2) : (line ij).Infinite := by
    apply Set.infinite_range_of_injective
    intro t u h
    exact congrArg Complex.im h
  by_contra! none
  apply hG
  apply MvPolynomial.funext_set line inf
  intro x hx
  let p : Fin r → Fin 2 → ℂ := fun i j => x (i, j)
  have re (i : Fin r) : (p i 0).re = (i.val : ℝ) := by
    obtain ⟨t, ht⟩ := hx (i, 0) (Set.mem_univ _)
    exact (congrArg Complex.re ht).symm
  have inj : Function.Injective p := by
    intro i j h
    have hr := congrArg (fun f : Fin 2 → ℂ => (f 0).re) h
    change (p i 0).re = (p j 0).re at hr
    rw [re, re] at hr
    exact Fin.ext (by exact_mod_cast hr)
  have ev : MvPolynomial.eval x G = 0 := by
    by_contra hn
    exact none p ⟨inj, by simpa [p] using hn⟩
  simpa using ev