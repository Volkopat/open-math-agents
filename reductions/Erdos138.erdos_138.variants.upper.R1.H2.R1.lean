import OMAReductions.R_Erdos138_erdos_138_variants_upper_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Reduction of `Erdos138.erdos_138.variants.upper.R1.H2` (Gowers' Density Increment from Large $U^{k-1}$ Norm)

Following Section 18 of W. T. Gowers, *A new proof of Szemerédi's theorem*, Geom. Funct. Anal. 11
(2001), 465–588, we reduce Gowers' quantitative density increment theorem
(`OMA.R_Erdos138_erdos_138_variants_upper_R1.H2`) to its two structural pillars:

1. (`H1`) **Gowers' local inverse theorem for the $U^{k-1}$ norm** (Gowers 2001, Theorem 18.1):
   if a $1$-bounded function $f : \mathbb{Z}/P\mathbb{Z} \to [-1, 1]$ ($2N < P \le 4N$ prime,
   $N \ge 2^{2^{2^{2^{k+8}}}}$) has $\|f\|_{U^{k-1}(\mathbb{Z}/P\mathbb{Z})} \ge (256 k^2 2^k)^{-1}$,
   then $\{1, \dots, N\}$ can be partitioned into arithmetic progressions $Q_t$ of length
   $L_t \ge N^{\eta_1}$ ($\eta_1 = 2^{-2^{2^{k+7}}}$) carrying degree-$(k-2)$ phase
   polynomials $\varphi_t$ whose weighted correlations with $f$ sum to at least $4 \eta N$
   ($\eta = 2^{-2^{3 \cdot 2^{k+7}}}$).
2. (`H2`) **Polynomial phase-freezing partition (Weyl / Dirichlet simultaneous Diophantine
   approximation)** (Gowers 2001, Lemma 18.2 / Corollary 18.3): for every degree $d \ge 1$,
   tolerance $\varepsilon \in (0, 1]$, and $L \ge (2/\varepsilon)^{2^{2^{d+4}}}$, any degree-$d$
   real polynomial $\varphi$ admits a partition of $\{1, \dots, L\}$ into arithmetic progressions
   of length $M_s \ge L^{2^{-2^{d+4}}}$ on each of which $e(\varphi(x)) = \exp(2\pi i \varphi(x))$
   varies by at most $\varepsilon$ from a unimodular constant $\theta_s$.

Inside `main`, we prove the entire Section 18 polynomial-to-density-increment argument from scratch:
- Verify the four-exponential length threshold $N^{\eta_1} \ge (2/\eta)^{2^{2^{k+2}}}$ and exponent
  comparison $\eta \le \eta_1 \cdot 2^{-2^{k+2}}$.
- Partition each progression $Q_t$ into subprogressions $R_{t,s}$ via `H2` with $\varepsilon = \eta$
  and compose the affine maps $j \mapsto a_t + (b_{t,s} + j r_{t,s}) d_t$.
- Freeze each phase $e(\varphi_t)$ to $\theta_{t,s}$ via the triangle inequality to obtain
  $3 \eta N \le \sum_{t,s} |\sum_{x \in R_{t,s}} f(x)|$.
- Use the exact zero-mean identity $\sum_{x \in [1, N]} f(x) = 0$ and $|S| + S \le 2 \max(S, 0)$ to
  extract a single subprogression $R_{t,s} \subseteq \{1, \dots, N\}$ of length $M \ge N^\eta$ on
  which $A$ achieves density at least $\delta + \eta$.
-/

-- Reduction Erdos138.erdos_138.variants.upper.R1.H2.R1 of Erdos138.erdos_138.variants.upper.R1.H2
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

open Finset
open scoped Classical BigOperators

namespace OMA.R_Erdos138_erdos_138_variants_upper_R1_H2_R1

/- ### Helper 1: Sum reindexing over a disjoint partition of `Finset.Icc 1 N` -/

private lemma sum_eq_sum_partition {α : Type*} [AddCommMonoid α]
    {N m : ℕ} (a d L : Fin m → ℕ)
    (hmem : ∀ t : Fin m, ∀ i ∈ Finset.Icc 1 (L t), a t + i * d t ∈ Finset.Icc 1 N)
    (hpart : ∀ x ∈ Finset.Icc 1 N,
      ∃! p : Σ t : Fin m, Finset.Icc 1 (L t), a p.1 + p.2.1 * d p.1 = x)
    (g : ℕ → α) :
    ∑ x ∈ Finset.Icc 1 N, g x = ∑ t : Fin m, ∑ i ∈ Finset.Icc 1 (L t), g (a t + i * d t) := by
  have h1 : ∑ t : Fin m, ∑ i ∈ Finset.Icc 1 (L t), g (a t + i * d t) =
      ∑ p : Σ t : Fin m, Finset.Icc 1 (L t), g (a p.1 + p.2.1 * d p.1) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact (Finset.sum_attach (Finset.Icc 1 (L t)) (fun i => g (a t + i * d t))).symm
  rw [h1]
  symm
  refine Finset.sum_bij (fun (p : Σ t : Fin m, Finset.Icc 1 (L t)) _ => a p.1 + p.2.1 * d p.1)
    ?_ ?_ ?_ ?_
  · intro p _
    exact hmem p.1 p.2.1 p.2.2
  · intro p₁ _ p₂ _ hEq
    have hx : a p₁.1 + p₁.2.1 * d p₁.1 ∈ Finset.Icc 1 N := hmem p₁.1 p₁.2.1 p₁.2.2
    obtain ⟨q, _, huniq⟩ := hpart (a p₁.1 + p₁.2.1 * d p₁.1) hx
    exact (huniq p₁ rfl).trans (huniq p₂ hEq.symm).symm
  · intro x hx
    obtain ⟨p, hp, _⟩ := hpart x hx
    exact ⟨p, Finset.mem_univ p, hp⟩
  · intro _ _; rfl

/- ### Helper 2: Phase freezing on a single progression -/

private lemma norm_sum_mul_phase_le {M : ℕ} (v : ℕ → ℝ) (hv : ∀ j ∈ Finset.Icc 1 M, |v j| ≤ 1)
    (ψ : ℕ → ℂ) (θ : ℂ) (hθ : ‖θ‖ = 1) {ε : ℝ}
    (hclose : ∀ j ∈ Finset.Icc 1 M, ‖ψ j - θ‖ ≤ ε) :
    ‖∑ j ∈ Finset.Icc 1 M, (v j : ℂ) * ψ j‖ ≤ |∑ j ∈ Finset.Icc 1 M, v j| + ε * (M : ℝ) := by
  have hsplit : ∑ j ∈ Finset.Icc 1 M, (v j : ℂ) * ψ j =
      ((∑ j ∈ Finset.Icc 1 M, v j : ℝ) : ℂ) * θ +
      ∑ j ∈ Finset.Icc 1 M, (v j : ℂ) * (ψ j - θ) := by
    rw [Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  have h1 : ‖((∑ j ∈ Finset.Icc 1 M, v j : ℝ) : ℂ) * θ‖ = |∑ j ∈ Finset.Icc 1 M, v j| := by
    rw [norm_mul, hθ, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖∑ j ∈ Finset.Icc 1 M, (v j : ℂ) * (ψ j - θ)‖ ≤ ε * (M : ℝ) := by
    calc ‖∑ j ∈ Finset.Icc 1 M, (v j : ℂ) * (ψ j - θ)‖
        ≤ ∑ j ∈ Finset.Icc 1 M, ‖(v j : ℂ) * (ψ j - θ)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 M, ε := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc |v j| * ‖ψ j - θ‖ ≤ 1 * ‖ψ j - θ‖ :=
                mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
            _ = ‖ψ j - θ‖ := one_mul _
            _ ≤ ε := hclose j hj
      _ = ε * (M : ℝ) := by simp [Nat.card_Icc, mul_comm]
  calc ‖((∑ j ∈ Finset.Icc 1 M, v j : ℝ) : ℂ) * θ + ∑ j ∈ Finset.Icc 1 M, (v j : ℂ) * (ψ j - θ)‖
      ≤ ‖((∑ j ∈ Finset.Icc 1 M, v j : ℝ) : ℂ) * θ‖ +
          ‖∑ j ∈ Finset.Icc 1 M, (v j : ℂ) * (ψ j - θ)‖ := norm_add_le _ _
    _ ≤ |∑ j ∈ Finset.Icc 1 M, v j| + ε * (M : ℝ) := by linarith

/- ### Helper 3: Tower arithmetic for Gowers' Section 18 exponents -/

private lemma tower_exponents {k N : ℕ} (hk : 3 ≤ k)
    (hN : 2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) ≤ N) :
    let η : ℝ := ((2 : ℝ) ^ (2 ^ (3 * 2 ^ (k + 7))))⁻¹
    let η₁ : ℝ := ((2 : ℝ) ^ (2 ^ (2 ^ (k + 7))))⁻¹
    η ≤ η₁ * ((2 : ℝ) ^ (2 ^ (k + 2)))⁻¹ ∧
      (2 / η) ^ (2 ^ (2 ^ (k + 2))) ≤ (N : ℝ) ^ η₁ := by
  intro η η₁
  have hpow_le : 2 ^ (2 ^ (k + 7)) + 2 ^ (k + 2) ≤ 2 ^ (3 * 2 ^ (k + 7)) := by
    have h1 : 2 ^ (k + 2) ≤ 2 ^ (2 ^ (k + 7)) := by
      refine Nat.pow_le_pow_right (by omega) ?_
      have : k + 7 < 2 ^ (k + 7) := Nat.lt_two_pow_self
      omega
    have h2 : 2 ^ (2 ^ (k + 7)) + 2 ^ (2 ^ (k + 7)) = 2 ^ (2 ^ (k + 7) + 1) := by
      rw [pow_succ 2 (2 ^ (k + 7))]; ring
    have h3 : 2 ^ (k + 7) + 1 ≤ 3 * 2 ^ (k + 7) := by
      have : 1 ≤ 2 ^ (k + 7) := Nat.one_le_pow _ 2 (by omega)
      omega
    exact (Nat.add_le_add_left h1 _).trans (h2 ▸ Nat.pow_le_pow_right (by omega) h3)
  refine ⟨?_, ?_⟩
  · dsimp [η, η₁]
    rw [← mul_inv, ← pow_add]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hpow_le)
  · -- Show `(2 / η) ^ (2 ^ (2 ^ (k + 2))) ≤ N ^ η₁`
    have hA : 2 / η = (2 : ℝ) ^ (2 ^ (3 * 2 ^ (k + 7)) + 1) := by
      dsimp [η]
      rw [div_inv_eq_mul, mul_comm]
      exact (pow_succ (2 : ℝ) _).symm
    have hLHS : (2 / η) ^ (2 ^ (2 ^ (k + 2))) =
        (2 : ℝ) ^ ((2 ^ (3 * 2 ^ (k + 7)) + 1) * 2 ^ (2 ^ (k + 2))) := by
      rw [hA, ← pow_mul]
    have hLHS_exp : (2 ^ (3 * 2 ^ (k + 7)) + 1) * 2 ^ (2 ^ (k + 2)) ≤ 2 ^ (2 ^ (k + 9)) := by
      have h1 : 2 ^ (3 * 2 ^ (k + 7)) + 1 ≤ 2 ^ (3 * 2 ^ (k + 7) + 1) := by
        have : 1 ≤ 2 ^ (3 * 2 ^ (k + 7)) := Nat.one_le_pow _ 2 (by omega)
        rw [pow_succ 2 (3 * 2 ^ (k + 7))]; omega
      have h2 : 3 * 2 ^ (k + 7) + 1 + 2 ^ (k + 2) ≤ 2 ^ (k + 9) := by
        have h9 : 2 ^ (k + 9) = 4 * 2 ^ (k + 7) := by
          rw [show k + 9 = (k + 7) + 2 by omega, pow_add]; ring
        have h7 : 2 ^ (k + 7) = 32 * 2 ^ (k + 2) := by
          rw [show k + 7 = (k + 2) + 5 by omega, pow_add]; ring
        have hpos : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ 2 (by omega)
        omega
      calc (2 ^ (3 * 2 ^ (k + 7)) + 1) * 2 ^ (2 ^ (k + 2))
          ≤ 2 ^ (3 * 2 ^ (k + 7) + 1) * 2 ^ (2 ^ (k + 2)) := Nat.mul_le_mul_right _ h1
        _ = 2 ^ (3 * 2 ^ (k + 7) + 1 + 2 ^ (k + 2)) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ (2 ^ (k + 9)) := Nat.pow_le_pow_right (by omega) h2
    -- Lower bound `N ^ η₁`
    let B : ℕ := 2 ^ (2 ^ (2 ^ (k + 7)))
    have htop_ge : 2 ^ (k + 9) + 2 ^ (2 ^ (k + 7)) ≤ 2 ^ (2 ^ (k + 8)) := by
      have h9_le : k + 9 ≤ 2 ^ (k + 7) := by
        have h1 : k + 6 < 2 ^ (k + 6) := Nat.lt_two_pow_self
        have h2 : 2 ^ (k + 7) = 2 * 2 ^ (k + 6) := by
          rw [show k + 7 = (k + 6) + 1 by omega, pow_succ]; ring
        omega
      have hpow9 : 2 ^ (k + 9) ≤ 2 ^ (2 ^ (k + 7)) := Nat.pow_le_pow_right (by omega) h9_le
      have hsum : 2 ^ (2 ^ (k + 7)) + 2 ^ (2 ^ (k + 7)) = 2 ^ (2 ^ (k + 7) + 1) := by
        rw [pow_succ 2 (2 ^ (k + 7))]; ring
      have hexp : 2 ^ (k + 7) + 1 ≤ 2 ^ (k + 8) := by
        have h8 : 2 ^ (k + 8) = 2 * 2 ^ (k + 7) := by
          rw [show k + 8 = (k + 7) + 1 by omega, pow_succ]; ring
        have hpos : 1 ≤ 2 ^ (k + 7) := Nat.one_le_pow _ 2 (by omega)
        omega
      calc 2 ^ (k + 9) + 2 ^ (2 ^ (k + 7))
          ≤ 2 ^ (2 ^ (k + 7)) + 2 ^ (2 ^ (k + 7)) := Nat.add_le_add_right hpow9 _
        _ = 2 ^ (2 ^ (k + 7) + 1) := hsum
        _ ≤ 2 ^ (2 ^ (k + 8)) := Nat.pow_le_pow_right (by omega) hexp
    have hdiv_ge : (2 : ℝ) ^ (2 ^ (k + 9)) ≤ ((2 ^ (2 ^ (2 ^ (k + 8))) : ℕ) : ℝ) * η₁ := by
      have h1 : 2 ^ (2 ^ (k + 9)) * B ≤ 2 ^ (2 ^ (2 ^ (k + 8))) := by
        dsimp [B]
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by omega) htop_ge
      have h1R : (2 : ℝ) ^ (2 ^ (k + 9)) * (B : ℝ) ≤ ((2 ^ (2 ^ (2 ^ (k + 8))) : ℕ) : ℝ) := by
        have hcast : ((2 ^ (2 ^ (k + 9)) * B : ℕ) : ℝ) ≤ ((2 ^ (2 ^ (2 ^ (k + 8))) : ℕ) : ℝ) := by
          exact_mod_cast h1
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
        exact hcast
      have hB_cast : (B : ℝ) = (2 : ℝ) ^ (2 ^ (2 ^ (k + 7))) := by
        dsimp [B]
        rw [Nat.cast_pow, Nat.cast_ofNat]
      have hBpos : (0 : ℝ) < (B : ℝ) := by rw [hB_cast]; positivity
      have hη₁_eq : η₁ = (B : ℝ)⁻¹ := by dsimp [η₁]; rw [hB_cast]
      rw [hη₁_eq]
      exact (le_mul_inv_iff₀ hBpos).mpr h1R
    have hN_cast : (2 : ℝ) ^ (((2 ^ (2 ^ (2 ^ (k + 8))) : ℕ) : ℝ)) ≤ (N : ℝ) := by
      rw [Real.rpow_natCast]
      have h1 : ((2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      rwa [Nat.cast_pow, Nat.cast_ofNat] at h1
    have hη₁_nn : 0 ≤ η₁ := by dsimp [η₁]; positivity
    calc (2 / η) ^ (2 ^ (2 ^ (k + 2)))
        = (2 : ℝ) ^ ((2 ^ (3 * 2 ^ (k + 7)) + 1) * 2 ^ (2 ^ (k + 2))) := hLHS
      _ ≤ (2 : ℝ) ^ (2 ^ (2 ^ (k + 9))) :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hLHS_exp
      _ = (2 : ℝ) ^ ((2 : ℝ) ^ (2 ^ (k + 9))) := by
          rw [← Real.rpow_natCast]
          congr 1
          rw [Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ (2 : ℝ) ^ (((2 ^ (2 ^ (2 ^ (k + 8))) : ℕ) : ℝ) * η₁) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hdiv_ge
      _ = ((2 : ℝ) ^ (((2 ^ (2 ^ (2 ^ (k + 8))) : ℕ) : ℝ))) ^ η₁ := by
          rw [← Real.rpow_mul (by norm_num)]
      _ ≤ (N : ℝ) ^ η₁ := Real.rpow_le_rpow (by positivity) hN_cast hη₁_nn

/- ### Hypotheses -/

/-- **Hypothesis 1 (Gowers' local inverse theorem for the $U^{k-1}$ norm)**:
for $k \ge 3$, $N \ge 2^{2^{2^{2^{k+8}}}}$, prime $P \in (2N, 4N]$, and any $1$-bounded function
$f : \mathbb{Z}/P\mathbb{Z} \to [-1, 1]$ with $\|f\|_{U^{k-1}(\mathbb{Z}/P\mathbb{Z})} \ge
(256 k^2 2^k)^{-1}$, $\{1, \dots, N\}$ can be partitioned into arithmetic progressions of length
at least $N^{\eta_1}$ ($\eta_1 = 2^{-2^{2^{k+7}}}$) carrying degree-$(k-2)$ polynomial
phases whose correlations with $f$ sum to at least $4 \eta N$ ($\eta = 2^{-2^{3 \cdot 2^{k+7}}}$). -/
def H1 : Prop :=
  ∀ (k N P : ℕ) [NeZero P], 3 ≤ k → 2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) ≤ N →
    P.Prime → 2 * N < P → P ≤ 4 * N →
    ∀ (f : ZMod P → ℝ), (∀ x, |f x| ≤ 1) →
      (1 / (256 * (k : ℝ) ^ 2 * (2 : ℝ) ^ k)) ^ (2 ^ (k - 1)) ≤
        ((P : ℝ) ^ k)⁻¹ * ∑ x : ZMod P, ∑ h : Fin (k - 1) → ZMod P,
          ∏ ω : Fin (k - 1) → Bool,
            f (x + ∑ i : Fin (k - 1), if ω i then h i else 0) →
      let η : ℝ := ((2 : ℝ) ^ (2 ^ (3 * 2 ^ (k + 7))))⁻¹
      let η₁ : ℝ := ((2 : ℝ) ^ (2 ^ (2 ^ (k + 7))))⁻¹
      ∃ (m : ℕ) (a d L : Fin m → ℕ) (φ : Fin m → Fin (k - 1) → ℝ),
        (∀ t, 1 ≤ d t ∧ 1 ≤ L t ∧ (N : ℝ) ^ η₁ ≤ (L t : ℝ)) ∧
        (∀ t, ∀ i ∈ Finset.Icc 1 (L t), a t + i * d t ∈ Finset.Icc 1 N) ∧
        (∀ x ∈ Finset.Icc 1 N,
          ∃! p : Σ t : Fin m, Finset.Icc 1 (L t), a p.1 + p.2.1 * d p.1 = x) ∧
        4 * η * (N : ℝ) ≤ ∑ t : Fin m,
          ‖∑ i ∈ Finset.Icc 1 (L t), (f ((a t + i * d t : ℕ) : ZMod P) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I *
              ((∑ u : Fin (k - 1), φ t u * (i : ℝ) ^ u.1 : ℝ) : ℂ))‖

/-- **Hypothesis 2 (Polynomial phase-freezing partition via Weyl / Dirichlet simultaneous
approximation)**: for every degree $d \ge 1$, tolerance $\varepsilon \in (0, 1]$, and
$L \ge (2/\varepsilon)^{2^{2^{d+4}}}$, any degree-$d$ real polynomial $\varphi$ admits a partition
of $\{1, \dots, L\}$ into arithmetic progressions of length at least $L^{2^{-2^{d+4}}}$ on each
of which $\exp(2\pi i \varphi(x))$ stays within $\varepsilon$ of a unimodular constant $\theta$. -/
def H2 : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (L : ℕ), (2 / ε) ^ (2 ^ (2 ^ (d + 4))) ≤ (L : ℝ) →
      ∀ (φ : Fin (d + 1) → ℝ),
        ∃ (m : ℕ) (b r M : Fin m → ℕ),
          (∀ s, 1 ≤ r s ∧ 1 ≤ M s ∧ (L : ℝ) ^ (((2 : ℝ) ^ (2 ^ (d + 4)))⁻¹) ≤ (M s : ℝ)) ∧
          (∀ s, ∀ j ∈ Finset.Icc 1 (M s), b s + j * r s ∈ Finset.Icc 1 L) ∧
          (∀ i ∈ Finset.Icc 1 L,
            ∃! p : Σ s : Fin m, Finset.Icc 1 (M s), b p.1 + p.2.1 * r p.1 = i) ∧
          (∀ s, ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ j ∈ Finset.Icc 1 (M s),
            ‖Complex.exp (2 * Real.pi * Complex.I *
              ((∑ u : Fin (d + 1), φ u * ((b s + j * r s : ℕ) : ℝ) ^ u.1 : ℝ) : ℂ)) - θ‖ ≤ ε)

/- ### Main Reduction Theorem -/

theorem main : H1 → H2 → OMA.R_Erdos138_erdos_138_variants_upper_R1.H2 := by
  intro hInv hWeyl
  dsimp only [OMA.R_Erdos138_erdos_138_variants_upper_R1.H2]
  intro k hk N P hNeP hN_floor hP_prime hP_lo hP_hi A hA_sub hA_half hU
  let δ : ℝ := (A.card : ℝ) / (N : ℝ)
  let f : ZMod P → ℝ := fun x =>
    (if x.val ∈ A then (1 : ℝ) else 0) - δ * (if x.val ∈ Finset.Icc 1 N then (1 : ℝ) else 0)
  let η : ℝ := ((2 : ℝ) ^ (2 ^ (3 * 2 ^ (k + 7))))⁻¹
  let η₁ : ℝ := ((2 : ℝ) ^ (2 ^ (2 ^ (k + 7))))⁻¹
  have hN_pos : 0 < N := by
    have : 1 ≤ 2 ^ (2 ^ (2 ^ (2 ^ (k + 8)))) := Nat.one_le_pow _ 2 (by omega)
    omega
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hη_pos : 0 < η := by dsimp [η]; positivity
  have hη_le1 : η ≤ 1 := by
    dsimp [η]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hA_le_N : A.card ≤ N :=
    (Finset.card_le_card hA_sub).trans (by rw [Nat.card_Icc]; omega)
  have hδ_nn : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ_le1 : δ ≤ 1 := by
    dsimp [δ]; rw [div_le_one hN_real_pos]; exact_mod_cast hA_le_N
  have hf_bd : ∀ x : ZMod P, |f x| ≤ 1 := by
    intro x; dsimp [f]
    by_cases hxA : x.val ∈ A
    · have hxI : x.val ∈ Finset.Icc 1 N := hA_sub hxA
      simp only [hxA, hxI, ↓reduceIte, mul_one]
      rw [abs_le]; constructor <;> linarith
    · split_ifs
      · rw [zero_sub, mul_one, abs_neg, abs_of_nonneg hδ_nn]; exact hδ_le1
      · simp
  have hf_Icc : ∀ x ∈ Finset.Icc 1 N,
      f ((x : ℕ) : ZMod P) = (if x ∈ A then (1 : ℝ) else 0) - δ := by
    intro x hx
    have hx_le : x ≤ N := (Finset.mem_Icc.mp hx).2
    have hx_lt : x < P := by omega
    dsimp [f]
    rw [ZMod.val_natCast_of_lt hx_lt, if_pos hx, mul_one]
  -- Exact zero-mean property of `f` on `Icc 1 N`
  have hf_mean_zero : ∑ x ∈ Finset.Icc 1 N, f ((x : ℕ) : ZMod P) = 0 := by
    have h1 : ∑ x ∈ Finset.Icc 1 N, f ((x : ℕ) : ZMod P) =
        (∑ x ∈ Finset.Icc 1 N, (if x ∈ A then (1 : ℝ) else 0)) -
        ∑ _x ∈ Finset.Icc 1 N, δ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x hx => hf_Icc x hx
    rw [h1, Finset.sum_boole, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hfilt : (Finset.Icc 1 N).filter (fun x => x ∈ A) = A := by
      ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hA_sub h, h⟩⟩
    rw [hfilt]
    dsimp [δ]
    field_simp [hN_real_pos.ne']
    ring
  -- Step 1: Apply Gowers' local inverse theorem (`H1`)
  obtain ⟨m, a, d, L, φ, hL_props, hQ_mem, hQ_part, hcorr⟩ :=
    hInv k N P hk hN_floor hP_prime hP_lo hP_hi f hf_bd hU
  -- Step 2: Verify tower arithmetic for `H2` with degree `d_deg = k - 2` and tolerance `η`
  obtain ⟨hη_exp, hL_thresh⟩ := tower_exponents hk hN_floor
  have hd_deg : 1 ≤ k - 2 := by omega
  have hd_succ : k - 2 + 1 = k - 1 := by omega
  have hd_add4 : k - 2 + 4 = k + 2 := by omega
  -- Apply `H2` to each progression `t : Fin m`
  have hsub_ex : ∀ t : Fin m,
      ∃ (m' : ℕ) (b r M : Fin m' → ℕ),
        (∀ s, 1 ≤ r s ∧ 1 ≤ M s ∧ (L t : ℝ) ^ (((2 : ℝ) ^ (2 ^ (k + 2)))⁻¹) ≤ (M s : ℝ)) ∧
        (∀ s, ∀ j ∈ Finset.Icc 1 (M s), b s + j * r s ∈ Finset.Icc 1 (L t)) ∧
        (∀ i ∈ Finset.Icc 1 (L t),
          ∃! p : Σ s : Fin m', Finset.Icc 1 (M s), b p.1 + p.2.1 * r p.1 = i) ∧
        (∀ s, ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ j ∈ Finset.Icc 1 (M s),
          ‖Complex.exp (2 * Real.pi * Complex.I *
            ((∑ u : Fin (k - 1), φ t u * ((b s + j * r s : ℕ) : ℝ) ^ u.1 : ℝ) : ℂ)) - θ‖ ≤ η) := by
    intro t
    have hLt_ge : (2 / η) ^ (2 ^ (2 ^ (k - 2 + 4))) ≤ (L t : ℝ) := by
      rw [hd_add4]; exact hL_thresh.trans (hL_props t).2.2
    let φ' : Fin (k - 2 + 1) → ℝ := fun u => φ t (u.cast hd_succ)
    obtain ⟨m', b, r, M, hM_props, hR_mem, hR_part, hθ⟩ :=
      hWeyl (k - 2) hd_deg η hη_pos hη_le1 (L t) hLt_ge φ'
    refine ⟨m', b, r, M, fun s => ?_, hR_mem, hR_part, fun s => ?_⟩
    · rw [← hd_add4]; exact hM_props s
    · obtain ⟨θ, hθ_norm, hθ_bd⟩ := hθ s
      refine ⟨θ, hθ_norm, fun j hj => ?_⟩
      have hsum_eq : ∑ u : Fin (k - 2 + 1), φ' u * ((b s + j * r s : ℕ) : ℝ) ^ u.1 =
          ∑ u : Fin (k - 1), φ t u * ((b s + j * r s : ℕ) : ℝ) ^ u.1 := by
        refine Finset.sum_equiv (finCongr hd_succ) (fun _ => by simp) fun u _ => ?_
        simp [φ', finCongr]
      simpa only [hsum_eq] using hθ_bd j hj
  choose m' b r M hM_props hR_mem hR_part hθ using hsub_ex
  -- Step 3: Phase-freeze every subprogression `R_{t, s}`
  let S : ∀ t : Fin m, Fin (m' t) → ℝ := fun t s =>
    ∑ j ∈ Finset.Icc 1 (M t s), f ((a t + (b t s + j * r t s) * d t : ℕ) : ZMod P)
  have hcorr_sub : ∀ t : Fin m,
      ‖∑ i ∈ Finset.Icc 1 (L t), (f ((a t + i * d t : ℕ) : ZMod P) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I *
          ((∑ u : Fin (k - 1), φ t u * (i : ℝ) ^ u.1 : ℝ) : ℂ))‖ ≤
      ∑ s : Fin (m' t), (|S t s| + η * (M t s : ℝ)) := by
    intro t
    rw [sum_eq_sum_partition (b t) (r t) (M t) (hR_mem t) (hR_part t)]
    calc ‖∑ s : Fin (m' t), ∑ j ∈ Finset.Icc 1 (M t s),
            (f ((a t + (b t s + j * r t s) * d t : ℕ) : ZMod P) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I *
                ((∑ u : Fin (k - 1), φ t u * ((b t s + j * r t s : ℕ) : ℝ) ^ u.1 : ℝ) : ℂ))‖
        ≤ ∑ s : Fin (m' t), ‖∑ j ∈ Finset.Icc 1 (M t s),
            (f ((a t + (b t s + j * r t s) * d t : ℕ) : ZMod P) : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I *
                ((∑ u : Fin (k - 1), φ t u * ((b t s + j * r t s : ℕ) : ℝ) ^ u.1 : ℝ) : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ s : Fin (m' t), (|S t s| + η * (M t s : ℝ)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          obtain ⟨θ, hθ_norm, hθ_bd⟩ := hθ t s
          exact norm_sum_mul_phase_le
            (fun j => f ((a t + (b t s + j * r t s) * d t : ℕ) : ZMod P))
            (fun j _ => hf_bd _)
            (fun j => Complex.exp (2 * Real.pi * Complex.I *
              ((∑ u : Fin (k - 1), φ t u * ((b t s + j * r t s : ℕ) : ℝ) ^ u.1 : ℝ) : ℂ)))
            θ hθ_norm hθ_bd
  -- Total length and zero mean across all refined subprogressions
  have hsum_M : ∑ t : Fin m, ∑ s : Fin (m' t), (M t s : ℝ) = (N : ℝ) := by
    have hL_sum : ∀ t : Fin m, ∑ s : Fin (m' t), (M t s : ℝ) = (L t : ℝ) := fun t => by
      have := sum_eq_sum_partition (b t) (r t) (M t) (hR_mem t) (hR_part t) (fun _ => (1 : ℝ))
      simpa [Nat.card_Icc] using this.symm
    simp_rw [hL_sum]
    have := sum_eq_sum_partition a d L hQ_mem hQ_part (fun _ => (1 : ℝ))
    simpa [Nat.card_Icc] using this.symm
  have hsum_S_zero : ∑ t : Fin m, ∑ s : Fin (m' t), S t s = 0 := by
    have h1 : ∀ t : Fin m, ∑ s : Fin (m' t), S t s =
        ∑ i ∈ Finset.Icc 1 (L t), f ((a t + i * d t : ℕ) : ZMod P) := fun t => by
      exact (sum_eq_sum_partition (b t) (r t) (M t) (hR_mem t) (hR_part t)
        (fun i => f ((a t + i * d t : ℕ) : ZMod P))).symm
    simp_rw [h1]
    rw [← sum_eq_sum_partition a d L hQ_mem hQ_part (fun x => f ((x : ℕ) : ZMod P))]
    exact hf_mean_zero
  -- Step 4: Combine with `hf_mean_zero` to extract a subprogression with density increment `≥ η`
  have hsum_abs_ge : 3 * η * (N : ℝ) ≤ ∑ t : Fin m, ∑ s : Fin (m' t), (|S t s| + S t s) := by
    have h1 : 4 * η * (N : ℝ) ≤
        (∑ t : Fin m, ∑ s : Fin (m' t), |S t s|) + η * (N : ℝ) := by
      calc 4 * η * (N : ℝ)
          ≤ ∑ t : Fin m, ∑ s : Fin (m' t), (|S t s| + η * (M t s : ℝ)) :=
            hcorr.trans (Finset.sum_le_sum fun t _ => hcorr_sub t)
        _ = (∑ t : Fin m, ∑ s : Fin (m' t), |S t s|) +
            η * ∑ t : Fin m, ∑ s : Fin (m' t), (M t s : ℝ) := by
            simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = (∑ t : Fin m, ∑ s : Fin (m' t), |S t s|) + η * (N : ℝ) := by rw [hsum_M]
    have h2 : ∑ t : Fin m, ∑ s : Fin (m' t), (|S t s| + S t s) =
        ∑ t : Fin m, ∑ s : Fin (m' t), |S t s| := by
      simp_rw [Finset.sum_add_distrib]
      rw [hsum_S_zero, add_zero]
    linarith
  have hexists_inc : ∃ (t : Fin m) (s : Fin (m' t)), η * (M t s : ℝ) ≤ S t s := by
    by_contra hall
    push Not at hall
    have hpt : ∀ t : Fin m, ∀ s : Fin (m' t), |S t s| + S t s ≤ 2 * η * (M t s : ℝ) := by
      intro t s
      have hlt := hall t s
      by_cases hnn : 0 ≤ S t s
      · rw [abs_of_nonneg hnn]; linarith
      · rw [abs_of_neg (lt_of_not_ge hnn)]
        have : 0 ≤ 2 * η * (M t s : ℝ) := by positivity
        linarith
    have hle : ∑ t : Fin m, ∑ s : Fin (m' t), (|S t s| + S t s) ≤ 2 * η * (N : ℝ) := by
      calc ∑ t : Fin m, ∑ s : Fin (m' t), (|S t s| + S t s)
          ≤ ∑ t : Fin m, ∑ s : Fin (m' t), (2 * η * (M t s : ℝ)) :=
            Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ => hpt t s
        _ = 2 * η * ∑ t : Fin m, ∑ s : Fin (m' t), (M t s : ℝ) := by
            simp_rw [← Finset.mul_sum]
        _ = 2 * η * (N : ℝ) := by rw [hsum_M]
    have hηN : 0 < η * (N : ℝ) := mul_pos hη_pos hN_real_pos
    linarith
  -- Step 5: Package the winning composed subprogression
  obtain ⟨t, s, hS_ge⟩ := hexists_inc
  refine ⟨a t + b t s * d t, r t s * d t, M t s, ?_, (hM_props t s).2.1, ?_, ?_, ?_⟩
  · exact Nat.mul_pos (hM_props t s).1 (hL_props t).1
  · -- Length lower bound `N ^ η ≤ M t s`
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos
    calc (N : ℝ) ^ η
        ≤ (N : ℝ) ^ (η₁ * ((2 : ℝ) ^ (2 ^ (k + 2)))⁻¹) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hη_exp
      _ = ((N : ℝ) ^ η₁) ^ (((2 : ℝ) ^ (2 ^ (k + 2)))⁻¹) :=
          Real.rpow_mul hN_real_pos.le _ _
      _ ≤ (L t : ℝ) ^ (((2 : ℝ) ^ (2 ^ (k + 2)))⁻¹) :=
          Real.rpow_le_rpow (by positivity) (hL_props t).2.2 (by positivity)
      _ ≤ (M t s : ℝ) := (hM_props t s).2.2
  · intro j hj
    have hrew : a t + b t s * d t + j * (r t s * d t) = a t + (b t s + j * r t s) * d t := by ring
    rw [hrew]
    exact hQ_mem t (b t s + j * r t s) (hR_mem t s j hj)
  · -- Translate `η * M ≤ S t s` to `(δ + η) * M ≤ #{j ∈ Icc 1 M | a' + j * d' ∈ A}`
    have hS_eq : S t s =
        (((Finset.Icc 1 (M t s)).filter fun j => a t + b t s * d t + j * (r t s * d t) ∈ A).card : ℝ) -
        δ * (M t s : ℝ) := by
      dsimp [S]
      have h1 : ∀ j ∈ Finset.Icc 1 (M t s),
          f ((a t + (b t s + j * r t s) * d t : ℕ) : ZMod P) =
            (if a t + b t s * d t + j * (r t s * d t) ∈ A then (1 : ℝ) else 0) - δ := by
        intro j hj
        have hrew : a t + b t s * d t + j * (r t s * d t) = a t + (b t s + j * r t s) * d t := by ring
        rw [hrew]
        exact hf_Icc _ (hQ_mem t (b t s + j * r t s) (hR_mem t s j hj))
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const,
        Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring
    linarith

end OMA.R_Erdos138_erdos_138_variants_upper_R1_H2_R1
