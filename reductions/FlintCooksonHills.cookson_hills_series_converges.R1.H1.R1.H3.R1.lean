import OMAReductions.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1

/-!
The rows of the truncated logarithmic interpolation matrix prescribe weighted
Taylor coefficients at the rational centers. Geometry supplies full row rank
at cofinally many degree bounds. Arithmetic and analysis force rank loss at
all sufficiently large bounds if every selected rational approximates pi.
-/ 

namespace OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1_H3_R1

def H1 : Prop :=
  ∀ ν : ℝ, 2 < ν → ∀ (θ A B C σ : ℚ) (η ε F : ℝ) (m : ℕ),
    let K : ℕ := ⌊(C : ℝ) ^ m⌋₊
    let w : ℝ := ((B : ℝ) ^ m)⁻¹
    let v : ℝ := 2 * K * (θ : ℝ) ^ m * w
    (0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
    1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧ (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 ∧
    0 < η ∧ η < 1 ∧ 0 < ε ∧ ε ≤ 1/2 ∧
    ε < ν * ((A : ℝ) * (1-η) - θ) - (1 - θ) ∧ 2 / (θ : ℝ) < F ∧
    ν / F < ε / 3 ∧ 1 ≤ m ∧
    ((Real.log 4 + 4) * F * m + 2 * Real.log 2) / v + 100 * K / w < ε / 3 ∧
    2 < Real.log 2 / 4 * (η^2 * (K : ℝ) * (θ : ℝ)^m / ((m+1 : ℝ) * v * (A : ℝ)^m)) ∧
    0 < (σ : ℝ) ∧ (1 + 3 * (σ : ℝ))^(m+1) * (1/2 : ℝ) < 1 ∧
    (1 + 3 * (σ : ℝ))^m * (K * (θ : ℝ)^m) < 1 ∧ (1 + (σ : ℝ)) * θ < 1) →
    let S := (θ : ℝ) + Real.log 4 + Real.log (2*K) + ν + Real.log (200*K)
    let X := max 1 (((Real.log 4 + 4) * m + S) / (ε/3))
    let D := 2 * (m+2 : ℝ)^(m+2) * (1 + (m+2 : ℝ) / σ)^(m+2) *
      (max 1 (max v (1 / θ) / min w 1))^(m+1)
    ∀ (p : ℕ → ℤ) (q : ℕ → ℕ),
      let wt := fun i : ℕ => (Nat.ceil (Real.log (q i)) : ℝ)
      (∀ i < m, 2 ≤ q i ∧ p i ≠ 0 ∧ X < wt i ∧
        D * ((List.range i).reverse.map wt).prod < wt i) →
      ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧
      let R := {b : Fin (m+1) → ℕ // v*b 0 + (∑ i : Fin m, wt i*b i.succ)/θ < H}
      let T := {a : Fin (m+1) → ℕ // w*a 0 + ∑ i : Fin m, wt i*a i.succ ≤ H}
      LinearIndependent ℂ (fun r : Fin K × R => fun t : T =>
        let b := r.2.val
        let a := t.val
        ((MvPolynomial.C (σ := Fin m) ((1+(Polynomial.X : Polynomial ℂ))^a 0) * ∏ i : Fin m,
          (MvPolynomial.C (σ := Fin m) (Polynomial.C ((r.1.val : ℂ)*(2*Complex.I*(p i : ℂ)/q i)) +
            PowerSeries.trunc ⌈F*wt i/v⌉₊ (PowerSeries.log ℂ)) +
            MvPolynomial.X (R := Polynomial ℂ) i)^a i.succ).coeff
              (Finsupp.equivFunOnFinite.symm (fun i : Fin m => b i.succ))).coeff (b 0))

def H2 : Prop :=
  ∀ ν : ℝ, 2 < ν → ∀ (θ A B C σ : ℚ) (η ε F : ℝ) (m : ℕ),
    let K : ℕ := ⌊(C : ℝ) ^ m⌋₊
    let w : ℝ := ((B : ℝ) ^ m)⁻¹
    let v : ℝ := 2 * K * (θ : ℝ) ^ m * w
    (0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
    1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧ (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 ∧
    0 < η ∧ η < 1 ∧ 0 < ε ∧ ε ≤ 1/2 ∧
    ε < ν * ((A : ℝ) * (1-η) - θ) - (1 - θ) ∧ 2 / (θ : ℝ) < F ∧
    ν / F < ε / 3 ∧ 1 ≤ m ∧
    ((Real.log 4 + 4) * F * m + 2 * Real.log 2) / v + 100 * K / w < ε / 3 ∧
    2 < Real.log 2 / 4 * (η^2 * (K : ℝ) * (θ : ℝ)^m / ((m+1 : ℝ) * v * (A : ℝ)^m)) ∧
    0 < (σ : ℝ) ∧ (1 + 3 * (σ : ℝ))^(m+1) * (1/2 : ℝ) < 1 ∧
    (1 + 3 * (σ : ℝ))^m * (K * (θ : ℝ)^m) < 1 ∧ (1 + (σ : ℝ)) * θ < 1) →
    let S := (θ : ℝ) + Real.log 4 + Real.log (2*K) + ν + Real.log (200*K)
    let X := max 1 (((Real.log 4 + 4) * m + S) / (ε/3))
    let D := 2 * (m+2 : ℝ)^(m+2) * (1 + (m+2 : ℝ) / σ)^(m+2) *
      (max 1 (max v (1 / θ) / min w 1))^(m+1)
    ∀ (p : ℕ → ℤ) (q : ℕ → ℕ),
      let wt := fun i : ℕ => (Nat.ceil (Real.log (q i)) : ℝ)
      (∀ i < m, 2 ≤ q i ∧ p i ≠ 0 ∧ X < wt i ∧
        D * ((List.range i).reverse.map wt).prod < wt i) →
      (∀ i < m, |Real.pi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν)) →
      ∃ L : ℝ, ∀ H : ℝ, L ≤ H → ¬
      let R := {b : Fin (m+1) → ℕ // v*b 0 + (∑ i : Fin m, wt i*b i.succ)/θ < H}
      let T := {a : Fin (m+1) → ℕ // w*a 0 + ∑ i : Fin m, wt i*a i.succ ≤ H}
      LinearIndependent ℂ (fun r : Fin K × R => fun t : T =>
        let b := r.2.val
        let a := t.val
        ((MvPolynomial.C (σ := Fin m) ((1+(Polynomial.X : Polynomial ℂ))^a 0) * ∏ i : Fin m,
          (MvPolynomial.C (σ := Fin m) (Polynomial.C ((r.1.val : ℂ)*(2*Complex.I*(p i : ℂ)/q i)) +
            PowerSeries.trunc ⌈F*wt i/v⌉₊ (PowerSeries.log ℂ)) +
            MvPolynomial.X (R := Polynomial ℂ) i)^a i.succ).coeff
              (Finsupp.equivFunOnFinite.symm (fun i : Fin m => b i.succ))).coeff (b 0))

theorem main : H1 → H2 → OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1.H3 := by
  intro hfull hloss ν hν θ A B C σ η ε F m
  dsimp only
  intro hpar p q hblock
  by_contra h
  push Not at h
  obtain ⟨L, hL⟩ := hloss ν hν θ A B C σ η ε F m hpar p q hblock h
  obtain ⟨H, hHL, hH⟩ := hfull ν hν θ A B C σ η ε F m hpar p q hblock L
  exact hL H hHL hH

end OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1_H3_R1
