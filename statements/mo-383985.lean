import Mathlib

-- Credit: MathOverflow question 383985 by Vladimir Zolotov,
-- "Why is (Lip([0,1]^2))* finitely representable in 1-Wasserstein space over
-- the plane?", https://mathoverflow.net/questions/383985 (CC BY-SA). The
-- question quotes Andoni–Naor–Neiman, "Snowflake universality of Wasserstein
-- spaces", who in turn cite Naor–Schechtman, "Planar earthmover is not in
-- L1" [71] for the assertion formalized here: every finite subset of
-- Z = (Lip([0,1]^2))* embeds into P_1(R^2) with distortion arbitrarily
-- close to 1.
--
-- Readings (the source fixes these conventions; Mathlib has none of the
-- objects, so all are defined concretely below):
-- * As the source fixes, the norm on Lipschitz functions is the Lipschitz
--   constant. With that (semi)norm, a continuous linear functional vanishes
--   on constant functions, so the dual Z is modelled as the dual of Lip_0:
--   Lipschitz functions on the square vanishing at the base point 0, normed
--   by their least Lipschitz constant. This matches the source text, which
--   itself passes to Lip_0(X) (functions vanishing at a fixed base point)
--   when describing the finite case. Elements of Z are bundled as linear
--   maps with an explicit boundedness witness, with the operator norm.
-- * P_1(R^2) is the space of probability measures on the plane with finite
--   first moment, and W_1 is defined by Kantorovich–Rubinstein duality:
--   the supremum of |∫ f dμ - ∫ f dν| over 1-Lipschitz f. (For such
--   measures the supremum is finite and each 1-Lipschitz f is integrable;
--   this is the standard dual formula for W_1.)
-- * "Distortion arbitrarily close to 1" is stated in the standard
--   normalized form: for every ε > 0 there is a map φ defined on the finite
--   set with  d(x, y) ≤ W_1(φx, φy) ≤ (1 + ε) · d(x, y)  throughout.

open MeasureTheory
open scoped NNReal MeasureTheory

namespace OMA.S_mo_383985

noncomputable section

/-- The square `[0,1]^2` as a subtype of the Euclidean plane. -/
abbrev Square : Type := {x : EuclideanSpace ℝ (Fin 2) // ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The base point `0` of the square, where functions in `Lip₀` vanish. -/
def squareZero : Square := ⟨0, by intro i; simp⟩

/-- A real-valued Lipschitz function on the square vanishing at `0`, bundled with
a Lipschitz constant. The norm (see `lipNorm`) is the least Lipschitz constant,
as fixed in the source. -/
structure LipZeroFun where
  toFun : Square → ℝ
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K toFun
  vanishes : toFun squareZero = 0

/-- Addition of Lipschitz functions vanishing at `0`. -/
def lipAdd (f g : LipZeroFun) : LipZeroFun where
  toFun := f.toFun + g.toFun
  lipschitz := by
    obtain ⟨K, hK⟩ := f.lipschitz
    obtain ⟨L, hL⟩ := g.lipschitz
    exact ⟨K + L, hK.add hL⟩
  vanishes := by simp [f.vanishes, g.vanishes]

/-- The zero Lipschitz function. -/
def lipZero : LipZeroFun where
  toFun := fun _ => 0
  lipschitz := ⟨0, fun x y => by simp⟩
  vanishes := rfl

/-- Negation of a Lipschitz function vanishing at `0`. -/
def lipNeg (f : LipZeroFun) : LipZeroFun where
  toFun := -f.toFun
  lipschitz := by
    obtain ⟨K, hK⟩ := f.lipschitz
    exact ⟨K, hK.neg⟩
  vanishes := by simp [f.vanishes]

/-- Scalar multiplication of a Lipschitz function vanishing at `0`. -/
def lipSmul (c : ℝ) (f : LipZeroFun) : LipZeroFun where
  toFun := c • f.toFun
  lipschitz := by
    obtain ⟨K, hK⟩ := f.lipschitz
    refine ⟨‖c‖₊ * K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    have h := hK.dist_le_mul x y
    rw [Pi.smul_apply, Pi.smul_apply, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      ← dist_eq_norm]
    have h2 : ((‖c‖₊ * K : ℝ≥0) : ℝ) = |c| * (K : ℝ) := by simp
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg c)
  vanishes := by simp [f.vanishes]

/-- The norm on `Lip₀`: the least Lipschitz constant. -/
def lipNorm (f : LipZeroFun) : ℝ :=
  sInf {x : ℝ | ∃ K : ℝ≥0, (K : ℝ) = x ∧ LipschitzWith K f.toFun}

/-- An element of the dual space `𝒵 = (Lip([0,1]^2))*`: a bounded linear
functional on `Lip₀`, with the linearity and boundedness as data. -/
structure ZDual where
  toFun : LipZeroFun → ℝ
  map_add : ∀ f g : LipZeroFun, toFun (lipAdd f g) = toFun f + toFun g
  map_smul : ∀ (c : ℝ) (f : LipZeroFun), toFun (lipSmul c f) = c * toFun f
  bdd : ∃ C : ℝ, ∀ f : LipZeroFun, |toFun f| ≤ C * lipNorm f

/-- The operator norm on `𝒵`. -/
def zNorm (φ : ZDual) : ℝ :=
  sSup {y : ℝ | ∃ f : LipZeroFun, lipNorm f ≤ 1 ∧ y = |φ.toFun f|}

/-- Subtraction of dual elements, pointwise. -/
def zSub (φ ψ : ZDual) : ZDual where
  toFun := fun f => φ.toFun f - ψ.toFun f
  map_add := by
    intro f g
    rw [φ.map_add, ψ.map_add]
    ring
  map_smul := by
    intro c f
    rw [φ.map_smul, ψ.map_smul]
    ring
  bdd := by
    obtain ⟨C₁, hC₁⟩ := φ.bdd
    obtain ⟨C₂, hC₂⟩ := ψ.bdd
    refine ⟨C₁ + C₂, fun f => ?_⟩
    calc |φ.toFun f - ψ.toFun f| ≤ |φ.toFun f| + |ψ.toFun f| := abs_sub _ _
      _ ≤ C₁ * lipNorm f + C₂ * lipNorm f := add_le_add (hC₁ f) (hC₂ f)
      _ = (C₁ + C₂) * lipNorm f := by ring

/-- The distance on `𝒵` from the operator norm. -/
def zDist (φ ψ : ZDual) : ℝ := zNorm (zSub φ ψ)

/-- An element of the 1-Wasserstein space `𝒫₁(ℝ²)`: a probability measure on
the plane with finite first moment. -/
structure ProbW1 where
  measure : Measure (EuclideanSpace ℝ (Fin 2))
  isProbability : IsProbabilityMeasure measure
  firstMoment : (∫⁻ x, ENNReal.ofReal ‖x‖ ∂measure) < ⊤

/-- The 1-Wasserstein distance, defined by Kantorovich–Rubinstein duality as
the supremum of `|∫ f dμ - ∫ f dν|` over all 1-Lipschitz `f`. For probability
measures with finite first moment this supremum is finite, and every
1-Lipschitz `f` is integrable against such measures. -/
def w1Dist (μ ν : ProbW1) : ℝ :=
  sSup {y : ℝ | ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, LipschitzWith 1 f ∧
    y = |∫ x, f x ∂μ.measure - ∫ x, f x ∂ν.measure|}

theorem main : ∀ (F : Finset ZDual) (ε : ℝ), 0 < ε →
    ∃ φ : ZDual → ProbW1, ∀ x ∈ F, ∀ y ∈ F,
      zDist x y ≤ w1Dist (φ x) (φ y) ∧ w1Dist (φ x) (φ y) ≤ (1 + ε) * zDist x y := by
  sorry

end

end OMA.S_mo_383985
