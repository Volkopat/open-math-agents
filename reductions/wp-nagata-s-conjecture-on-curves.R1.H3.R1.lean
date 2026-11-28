import OMAReductions.R_wp_nagata_s_conjecture_on_curves_R1
import Mathlib
-- Elliptic marked-section construction and obstruction adapted from OpenAI openai/math
-- 3344da59991ed94f9ba711217b29c1d760badfa6. Test written inline: reduction format allows only H definitions.
namespace OMA.R_wp_nagata_s_conjecture_on_curves_R1_H3_R1
open Filter Topology OMA.S_wp_nagata_s_conjecture_on_curves
def H1 : Prop := ∀ (r : ℕ), 10 ≤ r → ¬ IsSquare r → ∀ (d : ℕ) (m : Fin r → ℕ), 0 < d → (d : ℝ)*Real.sqrt r ≤ ∑ i, (m i : ℝ) →
  ¬ (∃ q : MvPolynomial (Fin r × Fin 2) ℂ, q ≠ 0 ∧ ∀ p : Fin r → Fin 2 → ℂ, Function.Injective p → ∀ F : PlanePoly, F ≠ 0 → F.totalDegree = d → (∀ i, F ∈ pointIdeal (p i)^m i) → MvPolynomial.eval (fun ij => p ij.1 ij.2) q = 0) →
  ∃ D M : ℕ, 0 < M ∧ 3 < (D : ℝ)/M ∧ (D : ℝ)/M < Real.sqrt r ∧ ∀ (n : ℕ) (x : Fin 9 → ℝ), Function.Injective x → (∀ i, 0 < x i ∧ x i < 1/2) →
    ∀ᶠ t : ℝ in 𝓝[>] 0, let T := (t : ℂ); let e := fun s : ℝ => ((t ^ s : ℝ) : ℂ);
    let d := ((n*D : ℕ) : ℤ); let m := ((n*M : ℕ) : ℤ); let s := ∑ i, x i;
    let L := e ((s+3*(Real.sqrt r-3))/3); let A := fun (b : ℤ) (c : ℂ) (f : ℂ → ℂ) => f 0 = 0 ∧ (∀ z ≠ 0, DifferentiableAt ℂ f z) ∧ ∀ z ≠ 0, f (T*z) = c*z^(-b)*f z;
    let θ := fun z : ℂ => ∏' k : ℕ, (1-T^k*z);
    let P := fun z : ℂ => if z = 0 then 0 else ∏ i, (θ (z/e (x i))*θ (T*(z/e (x i))⁻¹));
    0 < t ∧ t < 1 ∧ ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧ ∀ p : Fin (r-9) → ℂ,
      Function.Injective p → (∀ i, p i ∈ U) → ∃ F : Polynomial (ℂ → ℂ), F ≠ 0 ∧
      (∀ j > (d/3).toNat, F.coeff j = 0) ∧ (∀ j : ℕ, if (j : ℤ) ≤ m then
        A (3*(d-3*m)) (L^(d-3*m)*(L^3/(-e s))^(m-j)) (F.coeff j) else
        ∃ f, A (3*(d-3*j)) (L^(d-3*j)) f ∧ (fun z => P z ^ ((j : ℤ)-m).toNat * f z) = F.coeff j) ∧
      ∀ i, ∃ S : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
        HasFPowerSeriesAt (fun z => F.sum fun j f => f (e (1/2)*Complex.exp z.1)*(Complex.exp z.2)^j) S (p i,0) ∧ ∀ k < n*M, S k = 0

def H2 : Prop := ∀ (r : ℕ), 10 ≤ r → ¬ IsSquare r → ∀ D M : ℕ, 0 < M → 3 < (D : ℝ)/M → (D : ℝ)/M < Real.sqrt r → ¬ (∀ (n : ℕ) (x : Fin 9 → ℝ), Function.Injective x → (∀ i, 0 < x i ∧ x i < 1/2) →
    ∀ᶠ t : ℝ in 𝓝[>] 0, let T := (t : ℂ); let e := fun s : ℝ => ((t ^ s : ℝ) : ℂ);
    let d := ((n*D : ℕ) : ℤ); let m := ((n*M : ℕ) : ℤ); let s := ∑ i, x i;
    let L := e ((s+3*(Real.sqrt r-3))/3); let A := fun (b : ℤ) (c : ℂ) (f : ℂ → ℂ) => f 0 = 0 ∧ (∀ z ≠ 0, DifferentiableAt ℂ f z) ∧ ∀ z ≠ 0, f (T*z) = c*z^(-b)*f z;
    let θ := fun z : ℂ => ∏' k : ℕ, (1-T^k*z);
    let P := fun z : ℂ => if z = 0 then 0 else ∏ i, (θ (z/e (x i))*θ (T*(z/e (x i))⁻¹));
    0 < t ∧ t < 1 ∧ ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧ ∀ p : Fin (r-9) → ℂ,
      Function.Injective p → (∀ i, p i ∈ U) → ∃ F : Polynomial (ℂ → ℂ), F ≠ 0 ∧
      (∀ j > (d/3).toNat, F.coeff j = 0) ∧ (∀ j : ℕ, if (j : ℤ) ≤ m then
        A (3*(d-3*m)) (L^(d-3*m)*(L^3/(-e s))^(m-j)) (F.coeff j) else
        ∃ f, A (3*(d-3*j)) (L^(d-3*j)) f ∧ (fun z => P z ^ ((j : ℤ)-m).toNat * f z) = F.coeff j) ∧
      ∀ i, ∃ S : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
        HasFPowerSeriesAt (fun z => F.sum fun j f => f (e (1/2)*Complex.exp z.1)*(Complex.exp z.2)^j) S (p i,0) ∧ ∀ k < n*M, S k = 0)

theorem main : H1 → H2 → OMA.R_wp_nagata_s_conjecture_on_curves_R1.H3 := by
  intro build obstruct r hr hs d m hd hb
  by_contra hn
  obtain ⟨D,M,hm,hl,hu,h⟩ := build r hr hs d m hd hb hn
  exact obstruct r hr hs D M hm hl hu h
end OMA.R_wp_nagata_s_conjecture_on_curves_R1_H3_R1
