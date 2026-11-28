import OMAStatements.S_wp_nagata_s_conjecture_on_curves

namespace OMA.R_wp_nagata_s_conjecture_on_curves_R1
open OMA.S_wp_nagata_s_conjecture_on_curves
-- Countable avoidance, square incidence, and nonsquare incidence.
def H1 : Prop := ∀ {r : ℕ} (E : ℕ → MvPolynomial (Fin r × Fin 2) ℂ), (∀ n, E n ≠ 0) → ∃ p, outside E p

def H2 : Prop := ∀ (r : ℕ), 10 ≤ r → IsSquare r → ∀ (d : ℕ) (m : Fin r → ℕ), 0 < d → (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ) →
      ∃ q : MvPolynomial (Fin r × Fin 2) ℂ, q ≠ 0 ∧
        ∀ p : Fin r → Fin 2 → ℂ, Function.Injective p → ∀ F : PlanePoly, F ≠ 0 →
        F.totalDegree = d → (∀ i, F ∈ pointIdeal (p i) ^ m i) →
        MvPolynomial.eval (fun ij => p ij.1 ij.2) q = 0

def H3 : Prop := ∀ (r : ℕ), 10 ≤ r → ¬ IsSquare r → ∀ (d : ℕ) (m : Fin r → ℕ), 0 < d → (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ) →
      ∃ q : MvPolynomial (Fin r × Fin 2) ℂ, q ≠ 0 ∧
        ∀ p : Fin r → Fin 2 → ℂ, Function.Injective p → ∀ F : PlanePoly, F ≠ 0 →
        F.totalDegree = d → (∀ i, F ∈ pointIdeal (p i) ^ m i) →
        MvPolynomial.eval (fun ij => p ij.1 ij.2) q = 0

theorem main : H1 → H2 → H3 → type_of% @OMA.S_wp_nagata_s_conjecture_on_curves.main := by
  intro avoid sq nsq r hr
  have h : ∀ (d : ℕ) (m : Fin r → ℕ), 0 < d → (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ) →
      ∃ q : MvPolynomial (Fin r × Fin 2) ℂ, q ≠ 0 ∧
        ∀ p : Fin r → Fin 2 → ℂ, Function.Injective p → ∀ F : PlanePoly, F ≠ 0 →
        F.totalDegree = d → (∀ i, F ∈ pointIdeal (p i) ^ m i) →
        MvPolynomial.eval (fun ij => p ij.1 ij.2) q = 0 := by
    by_cases hs : IsSquare r
    · exact sq r hr hs
    · exact nsq r hr hs
  classical
  let T := ℕ × (Fin r → ℕ)
  obtain ⟨enum, surj⟩ := exists_surjective_nat T
  let Bad (t : T) := 0 < t.1 ∧ (t.1 : ℝ)*Real.sqrt r ≤ ∑ i, (t.2 i : ℝ)
  let w (t : T) (b : Bad t) := h t.1 t.2 b.1 b.2
  let q (t : T) := if b : Bad t then Classical.choose (w t b) else 1
  have nq (t : T) : q t ≠ 0 := by
    by_cases b : Bad t
    · simpa [q,b] using (Classical.choose_spec (w t b)).1
    · simp [q,b]
  refine ⟨fun n => q (enum n), fun n => nq _, avoid _ (fun n => nq _), ?_⟩
  intro p hp F hF hd m hm
  by_contra! hb
  let t : T := (F.totalDegree, m)
  have b : Bad t := ⟨hd, hb⟩
  obtain ⟨n, hn⟩ := surj t
  apply hp.2 n
  change MvPolynomial.eval (fun ij : Fin r × Fin 2 => p ij.1 ij.2) (q (enum n)) = 0
  rw [hn]
  simpa [q,b] using (Classical.choose_spec (w t b)).2 p hp.1 F hF rfl hm
end OMA.R_wp_nagata_s_conjecture_on_curves_R1
