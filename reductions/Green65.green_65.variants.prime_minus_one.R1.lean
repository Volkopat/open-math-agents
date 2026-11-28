import FormalConjectures.GreensOpenProblems.«65»

-- Reduction Green65.green_65.variants.prime_minus_one.R1 of Ben Green's Open Problem 65 — prime minus one
-- Credit: @MathNoobie
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Reduction following B. Green, On Sarkozy's theorem for shifted primes, arXiv:2206.08001
(J. Amer. Math. Soc. 37 (2024)).

* The bridge from cosine polynomials to sets without differences p - 1 (first half of Green's
  Proposition 2.1, Fourier analysis modulo 2N+1) is proved below in full: `cyclic_avoid_bound`.
  `main` then only does exponent bookkeeping.
* H1 is Green's Proposition 12.1 (Section 12, the archimedean weight) for his explicit weight
  w(n) = W(n/Y), W(x) = x^(-1/2) e^(-x), Y = N / (2 log N): items (2), (1), (3), (4), (5), (6)
  in this order, with the implied constants made explicit (C, and D for the N^o(1) of (6)).
  It is self-contained real and complex analysis (Fourier transform of W, Gamma bounds,
  Kuzmin-Landau and van der Corput); no primes appear in it.
* H2 is Green's Theorem 2.2 (the analytic core, Sections 4-11 and 13-15) under the additional
  assumption that the weight of Proposition 12.1 has the properties of H1. It is slightly
  weakened with respect to the paper: only for N large, support condition only on [1, N],
  and 0 < kappa2 is not required.
Both hypotheses are true: H1 is implied by Green's Proposition 12.1 and H2 by his Theorem 2.2.
-/

namespace OMA.R_Green65_green_65_variants_prime_minus_one_R1

open Real Finset Filter
open scoped Pointwise

-- Green, Proposition 12.1, for w(n) = W(n/Y), with explicit constants.
def H1 : Prop := ∃ C : ℝ, ∀ ε > (0 : ℝ), ∃ D : ℝ, ∀ᶠ N : ℕ in atTop,
  let M : ℝ := N
  let Y := M / (2 * log M)
  let w : ℕ → ℝ := fun n => exp (-(n / Y)) / √(n / Y)
  let e : ℝ → ℂ := fun t => Complex.exp (2 * π * Complex.I * t)
  let S := Icc 1 N
  let R := C * M ^ (11 / 12 : ℝ)
  M / log M ≤ C * ∑ n ∈ S, w n ∧
  (∀ σ γ η : ℝ, 0 ≤ σ → σ ≤ 1 / 48 → |γ| ≤ M ^ (1 / 8 : ℝ) →
    let F : ℂ := ∑ n ∈ S, (n : ℂ) ^ (⟨-σ, γ⟩ : ℂ) * w n * e (η * n)
    let K := ∑ n ∈ S, w n * cos (2 * π * η * n)
    ∑ n ∈ S, (n : ℝ) ^ (-σ) * w n ≤ C * M ^ (1 - σ) ∧
    (M ^ (-(1 / 2) : ℝ) < |η - round η| → ‖F‖ ≤ R) ∧
    ‖F‖ ≤ 11 * M ^ (-σ / 4) * K + R ∧
    (γ = 0 → F.re ≤ M ^ (-σ / 4) * K + R)) ∧
  ∀ X : ℝ, 1 ≤ X → X ≤ M → ∃ v : ℕ → ℝ, ∃ a : ℝ → ℂ, MeasureTheory.Integrable a ∧
    ∑ n ∈ S, |v n| ≤ C * M / X ∧ ∫ ξ, ‖a ξ‖ ≤ D * M ^ ε * X ∧
    ∀ n ∈ S, ((w n - v n : ℝ) : ℂ) = ∫ ξ, a ξ * e (ξ * n / Y)

-- Green, Theorem 2.2, assuming the conclusion of Proposition 12.1 (as in H1).
def H2 : Prop := (∃ C : ℝ, ∀ ε > (0 : ℝ), ∃ D : ℝ, ∀ᶠ N : ℕ in atTop,
  let M : ℝ := N
  let Y := M / (2 * log M)
  let w : ℕ → ℝ := fun n => exp (-(n / Y)) / √(n / Y)
  let e : ℝ → ℂ := fun t => Complex.exp (2 * π * Complex.I * t)
  let S := Icc 1 N
  let R := C * M ^ (11 / 12 : ℝ)
  M / log M ≤ C * ∑ n ∈ S, w n ∧
  (∀ σ γ η : ℝ, 0 ≤ σ → σ ≤ 1 / 48 → |γ| ≤ M ^ (1 / 8 : ℝ) →
    let F : ℂ := ∑ n ∈ S, (n : ℂ) ^ (⟨-σ, γ⟩ : ℂ) * w n * e (η * n)
    let K := ∑ n ∈ S, w n * cos (2 * π * η * n)
    ∑ n ∈ S, (n : ℝ) ^ (-σ) * w n ≤ C * M ^ (1 - σ) ∧
    (M ^ (-(1 / 2) : ℝ) < |η - round η| → ‖F‖ ≤ R) ∧
    ‖F‖ ≤ 11 * M ^ (-σ / 4) * K + R ∧
    (γ = 0 → F.re ≤ M ^ (-σ / 4) * K + R)) ∧
  ∀ X : ℝ, 1 ≤ X → X ≤ M → ∃ v : ℕ → ℝ, ∃ a : ℝ → ℂ, MeasureTheory.Integrable a ∧
    ∑ n ∈ S, |v n| ≤ C * M / X ∧ ∫ ξ, ‖a ξ‖ ≤ D * M ^ ε * X ∧
    ∀ n ∈ S, ((w n - v n : ℝ) : ℂ) = ∫ ξ, a ξ * e (ξ * n / Y)) →
  ∃ κ κ' : ℝ, κ' < κ ∧ ∀ᶠ N : ℕ in atTop, ∃ Ψ : ℕ → ℝ,
    (∀ n ∈ Icc 1 N, Ψ n ≠ 0 → (n + 1).Prime) ∧
    (∀ θ : ℝ, -(N : ℝ) ^ (1 - κ) ≤ ∑ n ∈ Icc 1 N, Ψ n * cos (2 * π * n * θ)) ∧
    (N : ℝ) ^ (1 - κ') ≤ ∑ n ∈ Icc 1 N, Ψ n

/-- Orthogonality of cosines on the grid r/M. -/
lemma cos_grid_orth (M : ℕ) (hM : 0 < M) (k : ℤ) (hk0 : k ≠ 0) (hk1 : -(M : ℤ) < k)
    (hk2 : k < M) (t : ℝ) (ht : t = (k : ℝ)) :
    ∑ r ∈ Finset.range M, Real.cos (2 * Real.pi * t * ((r : ℝ) / M)) = 0 := by
  subst ht
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / M) with hz
  have hzM : z ^ M = 1 := by
    rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    field_simp
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h2 : (k : ℂ) = n * M := by
      have h3 : 2 * Real.pi * Complex.I * k = (n * (2 * Real.pi * Complex.I)) * M := by
        rw [← hn]; field_simp
      apply mul_left_cancel₀ hpi
      linear_combination h3
    have h3 : k = n * M := by exact_mod_cast h2
    rcases lt_trichotomy n 0 with h | h | h
    · have : n ≤ -1 := by omega
      nlinarith
    · simp [h] at h3; exact hk0 h3
    · have : 1 ≤ n := by omega
      nlinarith
  have hsum : ∑ r ∈ Finset.range M, z ^ r = 0 := by
    have := geom_sum_mul z M
    rw [hzM, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hz1)
  have hre := congrArg Complex.re hsum
  rw [Complex.re_sum, Complex.zero_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hz, ← Complex.exp_nat_mul]
  have : (r : ℂ) * (2 * Real.pi * Complex.I * k / M) =
      ((2 * Real.pi * (k : ℝ) * ((r : ℝ) / M) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- Green, Proposition 2.1 (first half), with real cosines on the grid r/(2N+1): if the cosine
polynomial `E + sum_{n=1}^N Psi n cos(2 pi n theta)` is nonnegative everywhere and no positive
difference of `A` lies in the support of `Psi`, then `|A| * T(0) <= (2N+1) * E`. -/
lemma cyclic_avoid_bound (N : ℕ) (Ψ : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hT : ∀ θ : ℝ, 0 ≤ E + ∑ n ∈ Finset.Icc 1 N, Ψ n * Real.cos (2 * Real.pi * n * θ))
    (A : Finset ℤ) (hA : A ⊆ Finset.Icc 1 (N : ℤ))
    (havoid : ∀ x ∈ A, ∀ y ∈ A, ∀ n ∈ Finset.Icc 1 N, x - y = (n : ℤ) → Ψ n = 0) :
    (A.card : ℝ) * (E + ∑ n ∈ Finset.Icc 1 N, Ψ n) ≤ (2 * (N : ℝ) + 1) * E := by
  classical
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · simp [hAe]; positivity
  have hMpos : 0 < 2 * N + 1 := by omega
  -- Q θ = |S(θ)|^2 written with real cosines
  have hQnn : ∀ θ : ℝ,
      0 ≤ ∑ x ∈ A, ∑ y ∈ A, Real.cos (2 * Real.pi * ((x - y : ℤ) : ℝ) * θ) := by
    intro θ
    have : ∑ x ∈ A, ∑ y ∈ A, Real.cos (2 * Real.pi * ((x - y : ℤ) : ℝ) * θ) =
        (∑ x ∈ A, Real.cos (2 * Real.pi * (x : ℝ) * θ)) ^ 2 +
          (∑ x ∈ A, Real.sin (2 * Real.pi * (x : ℝ) * θ)) ^ 2 := by
      simp only [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [show 2 * Real.pi * ((x - y : ℤ) : ℝ) * θ =
          2 * Real.pi * (x : ℝ) * θ - 2 * Real.pi * (y : ℝ) * θ by push_cast; ring]
      rw [Real.cos_sub]
    rw [this]; positivity
  -- product-to-sum expansion of T θ * Q θ
  have hexp : ∀ θ : ℝ,
      (E + ∑ n ∈ Finset.Icc 1 N, Ψ n * Real.cos (2 * Real.pi * n * θ)) *
        (∑ x ∈ A, ∑ y ∈ A, Real.cos (2 * Real.pi * ((x - y : ℤ) : ℝ) * θ)) =
      ∑ x ∈ A, ∑ y ∈ A, (E * Real.cos (2 * Real.pi * ((x - y : ℤ) : ℝ) * θ) +
        ∑ n ∈ Finset.Icc 1 N,
          (Ψ n / 2 * Real.cos (2 * Real.pi * (((x - y : ℤ) : ℝ) + n) * θ) +
           Ψ n / 2 * Real.cos (2 * Real.pi * (((x - y : ℤ) : ℝ) - n) * θ))) := by
    intro θ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 2 * Real.pi * (((x - y : ℤ) : ℝ) + n) * θ =
        2 * Real.pi * ((x - y : ℤ) : ℝ) * θ + 2 * Real.pi * n * θ by ring]
    rw [show 2 * Real.pi * (((x - y : ℤ) : ℝ) - n) * θ =
        2 * Real.pi * ((x - y : ℤ) : ℝ) * θ - 2 * Real.pi * n * θ by ring]
    rw [Real.cos_add, Real.cos_sub]
    ring
  -- orthogonality applied to each pair
  have hG : ∀ x ∈ A, ∀ y ∈ A,
      ∑ r ∈ Finset.range (2 * N + 1),
        (E * Real.cos (2 * Real.pi * ((x - y : ℤ) : ℝ) * ((r : ℝ) / (2 * N + 1 : ℕ))) +
        ∑ n ∈ Finset.Icc 1 N,
          (Ψ n / 2 * Real.cos (2 * Real.pi * (((x - y : ℤ) : ℝ) + n) *
              ((r : ℝ) / (2 * N + 1 : ℕ))) +
           Ψ n / 2 * Real.cos (2 * Real.pi * (((x - y : ℤ) : ℝ) - n) *
              ((r : ℝ) / (2 * N + 1 : ℕ))))) =
      if x = y then E * (2 * N + 1 : ℕ) else 0 := by
    intro x hx y hy
    have hx' := Finset.mem_Icc.mp (hA hx)
    have hy' := Finset.mem_Icc.mp (hA hy)
    rw [Finset.sum_add_distrib]
    have hzero : ∑ r ∈ Finset.range (2 * N + 1), ∑ n ∈ Finset.Icc 1 N,
          (Ψ n / 2 * Real.cos (2 * Real.pi * (((x - y : ℤ) : ℝ) + n) *
              ((r : ℝ) / (2 * N + 1 : ℕ))) +
           Ψ n / 2 * Real.cos (2 * Real.pi * (((x - y : ℤ) : ℝ) - n) *
              ((r : ℝ) / (2 * N + 1 : ℕ)))) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun n hn => ?_
      have hn' := Finset.mem_Icc.mp hn
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have h1 : Ψ n * ∑ r ∈ Finset.range (2 * N + 1), Real.cos (2 * Real.pi *
          (((x - y : ℤ) : ℝ) + n) * ((r : ℝ) / (2 * N + 1 : ℕ))) = 0 := by
        by_cases h : x - y + (n : ℤ) = 0
        · rw [havoid y hy x hx n hn (by omega), zero_mul]
        · rw [cos_grid_orth (2 * N + 1) hMpos (x - y + n) h (by push_cast; omega)
            (by push_cast; omega) _ (by push_cast; ring), mul_zero]
      have h2 : Ψ n * ∑ r ∈ Finset.range (2 * N + 1), Real.cos (2 * Real.pi *
          (((x - y : ℤ) : ℝ) - n) * ((r : ℝ) / (2 * N + 1 : ℕ))) = 0 := by
        by_cases h : x - y - (n : ℤ) = 0
        · rw [havoid x hx y hy n hn (by omega), zero_mul]
        · rw [cos_grid_orth (2 * N + 1) hMpos (x - y - n) h (by push_cast; omega)
            (by push_cast; omega) _ (by push_cast; ring), mul_zero]
      linear_combination h1 / 2 + h2 / 2
    rw [hzero, add_zero, ← Finset.mul_sum]
    split_ifs with hxy
    · subst hxy
      simp
    · rw [cos_grid_orth (2 * N + 1) hMpos (x - y) (sub_ne_zero.mpr hxy) (by push_cast; omega)
        (by push_cast; omega) _ rfl, mul_zero]
  -- the full identity
  have hid : ∑ r ∈ Finset.range (2 * N + 1),
      (E + ∑ n ∈ Finset.Icc 1 N, Ψ n * Real.cos (2 * Real.pi * n * ((r : ℝ) / (2 * N + 1 : ℕ)))) *
        (∑ x ∈ A, ∑ y ∈ A, Real.cos (2 * Real.pi * ((x - y : ℤ) : ℝ) *
          ((r : ℝ) / (2 * N + 1 : ℕ)))) =
      (A.card : ℝ) * (E * (2 * N + 1 : ℕ)) := by
    simp only [hexp]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun x hx => (Finset.sum_comm)]
    rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hG x hx y hy]
    rw [Finset.sum_congr rfl fun x hx => by rw [Finset.sum_ite_eq, if_pos hx]]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hle := Finset.single_le_sum (f := fun r : ℕ =>
      (E + ∑ n ∈ Finset.Icc 1 N, Ψ n * Real.cos (2 * Real.pi * n * ((r : ℝ) / (2 * N + 1 : ℕ)))) *
        (∑ x ∈ A, ∑ y ∈ A, Real.cos (2 * Real.pi * ((x - y : ℤ) : ℝ) *
          ((r : ℝ) / (2 * N + 1 : ℕ)))))
    (fun r _ => mul_nonneg (hT _) (hQnn _)) (Finset.mem_range.mpr hMpos)
  rw [hid] at hle
  simp only [Nat.cast_zero, zero_div, mul_zero, Real.cos_zero, mul_one,
    Finset.sum_const, nsmul_eq_mul] at hle
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  push_cast at hle
  have : (A.card : ℝ) * ((A.card : ℝ) * (E + ∑ n ∈ Finset.Icc 1 N, Ψ n)) ≤
      (A.card : ℝ) * ((2 * (N : ℝ) + 1) * E) := by nlinarith
  exact le_of_mul_le_mul_left this hcard

/-- The target from Green's Theorem 2.2 (in the form of the conclusion of H2) and the bridge. -/
lemma target_of_cosine_majorant
    (hgreen : ∃ κ₁ κ₂ : ℝ, κ₂ < κ₁ ∧ ∀ᶠ N : ℕ in atTop, ∃ Ψ : ℕ → ℝ,
      (∀ n ∈ Finset.Icc 1 N, Ψ n ≠ 0 → (n + 1).Prime) ∧
      (∀ θ : ℝ, -(N : ℝ) ^ (1 - κ₁) ≤
        ∑ n ∈ Finset.Icc 1 N, Ψ n * Real.cos (2 * Real.pi * n * θ)) ∧
      (N : ℝ) ^ (1 - κ₂) ≤ ∑ n ∈ Finset.Icc 1 N, Ψ n) :
    Green65.LargeDifferencePattern Green65.IsPrimeMinusOne := by
  obtain ⟨κ₁, κ₂, hκ, hev⟩ := hgreen
  set δ : ℝ := κ₁ - κ₂ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set c : ℝ := min (δ / 2) (1 / 2) with hcdef
  have hc0 : 0 < c := lt_min (by linarith) (by norm_num)
  have hc1 : c < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hcδ : c ≤ δ / 2 := min_le_left _ _
  have hgap : 0 < δ - c := by linarith
  refine ⟨c, hc0, hc1, ?_⟩
  have hpow : ∀ᶠ N : ℕ in atTop, (3 : ℝ) < (N : ℝ) ^ (δ - c) :=
    ((tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (3 : ℝ))
  filter_upwards [hev, hpow, eventually_ge_atTop (1 : ℕ)] with N hΨ hp hN1
  intro A hA hcard
  obtain ⟨Ψ, hsupp, hcos, hsum⟩ := hΨ
  by_contra hbad
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set E : ℝ := (N : ℝ) ^ (1 - κ₁) with hEdef
  have hE : 0 < E := Real.rpow_pos_of_pos hNpos _
  have hT : ∀ θ : ℝ, 0 ≤ E + ∑ n ∈ Finset.Icc 1 N, Ψ n * Real.cos (2 * Real.pi * n * θ) := by
    intro θ
    have := hcos θ
    linarith
  have havoid : ∀ x ∈ A, ∀ y ∈ A, ∀ n ∈ Finset.Icc 1 N, x - y = (n : ℤ) → Ψ n = 0 := by
    intro x hx y hy n hn hxy
    by_contra hne
    apply hbad
    refine ⟨x - y, Finset.sub_mem_sub hx hy, n + 1, hsupp n hn hne, ?_⟩
    rw [hxy]
    push_cast
    ring
  have hL1 := cyclic_avoid_bound N Ψ E hE.le hT A hA havoid
  have hcardnn : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have key1 : (A.card : ℝ) * (N : ℝ) ^ (1 - κ₂) ≤ (2 * (N : ℝ) + 1) * E :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) hcardnn) hL1
  have key2 : (N : ℝ) ^ (1 - c) * (N : ℝ) ^ (1 - κ₂) ≤ (A.card : ℝ) * (N : ℝ) ^ (1 - κ₂) :=
    mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hNpos.le _)
  have key3 : (2 * (N : ℝ) + 1) * E ≤ 3 * ((N : ℝ) * E) := by nlinarith
  have key4 : (N : ℝ) ^ (1 - c) * (N : ℝ) ^ (1 - κ₂) = (N : ℝ) ^ (δ - c) * ((N : ℝ) * E) := by
    rw [hEdef, ← Real.rpow_add hNpos]
    conv_rhs => rw [show ((N : ℝ) * (N : ℝ) ^ (1 - κ₁)) = (N : ℝ) ^ ((1 : ℝ) + (1 - κ₁)) by
      rw [Real.rpow_add hNpos, Real.rpow_one]]
    rw [← Real.rpow_add hNpos]
    congr 1
    rw [hδdef]
    ring
  have hX : 0 < (N : ℝ) * E := mul_pos hNpos hE
  have hfinal : (N : ℝ) ^ (δ - c) * ((N : ℝ) * E) ≤ 3 * ((N : ℝ) * E) := by
    rw [← key4]
    linarith
  have h3 := mul_lt_mul_of_pos_right hp hX
  linarith

theorem main : H1 → H2 → type_of% @Green65.green_65.variants.prime_minus_one := by
  intro h1 h2
  exact target_of_cosine_majorant (h2 h1)

end OMA.R_Green65_green_65_variants_prime_minus_one_R1
