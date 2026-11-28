import OMAStatements.S_arxiv_1906_08518

-- Fixed-degree incidence interfaces adapted from the shared Nagata port of
-- openai/math@3344da59991ed94f9ba711217b29c1d760badfa6.
namespace OMA.R_arxiv_1906_08518_R1
open MvPolynomial OMA.S_arxiv_1906_08518
-- Countable avoidance, square incidence, and nonsquare incidence.
def H1 : Prop := ∀ {r : ℕ} (G : MvPolynomial (Fin r × Fin 2) ℂ), G ≠ 0 → ∃ p, inOpen G p

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

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_1906_08518.main := by
  intro avoid sq nsq r hr l _hl
  have h : ∀ (d : ℕ) (m : Fin r → ℕ), 0 < d → (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ) →
      ∃ q : MvPolynomial (Fin r × Fin 2) ℂ, q ≠ 0 ∧
        ∀ p : Fin r → Fin 2 → ℂ, Function.Injective p → ∀ F : PlanePoly, F ≠ 0 →
        F.totalDegree = d → (∀ i, F ∈ pointIdeal (p i) ^ m i) →
        MvPolynomial.eval (fun ij => p ij.1 ij.2) q = 0 := by
    by_cases hs : IsSquare r
    · exact sq r hr hs
    · exact nsq r hr hs
  classical
  let B := Real.sqrt (r : ℝ) * l
  let S := (Finset.range (⌊B⌋₊ + 1)).filter (fun d : ℕ => 0 < d ∧ (d : ℝ) ≤ B)
  have cert (d : ℕ) (hd : d ∈ S) := by
    have hb := (Finset.mem_filter.mp hd).2
    have hm := mul_le_mul_of_nonneg_right hb.2 (Real.sqrt_nonneg (r:ℝ))
    have eqn : B * Real.sqrt (r:ℝ) = (r:ℝ)*l := by
      dsimp [B]; nlinarith [Real.sq_sqrt (Nat.cast_nonneg r), mul_assoc (Real.sqrt (r:ℝ)) (l:ℝ) (Real.sqrt (r:ℝ)), show (Real.sqrt (r:ℝ) * (l:ℝ) * Real.sqrt (r:ℝ)) = (Real.sqrt (r:ℝ))^2 * l by ring, congrArg (fun x : ℝ => x * l) (Real.sq_sqrt (Nat.cast_nonneg r))]
    exact h d (fun _ => l) hb.1 (by simpa [eqn] using hm)
  let q (d : ℕ) := if hd : d ∈ S then (cert d hd).choose else 1
  let G := ∏ d ∈ S, q d
  have hn : G ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun d hd => by simpa [q, hd] using (cert d hd).choose_spec.1)
  refine ⟨G, avoid G hn, ?_⟩
  intro p hp F hF hpos hord
  by_contra! hle
  have hd : F.totalDegree ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hle)), hpos, hle⟩
  apply hp.2
  change eval _ (∏ d ∈ S, q d) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero hd (by simpa [q,hd] using (cert _ hd).choose_spec.2 p hp.1 F hF rfl hord)
end OMA.R_arxiv_1906_08518_R1
