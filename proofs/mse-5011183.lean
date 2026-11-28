import OMAStatements.S_mse_5011183
import Mathlib

-- Problem mse-5011183: the statement claims that for every prime p there is a ring R whose group of units is
-- isomorphic to the p-Pruefer group (the p-power roots of unity).
-- Upstream: statements/mse-5011183.lean (declaration OMA.S_mse_5011183.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: there is no such ring for p = 5. Suppose the units of R form the 5-Pruefer group, so every unit
-- has order a power of 5.
-- (1) The unit -1 satisfies (-1)^(5^n) = -1 = 1, so 2 = 0 in R.
-- (2) Let u be a unit of order 5 and v = 1 + u + u^4. Over the integers,
--     (1 + X + X^4)^3 = 1 + (X^5 - 1) q(X) + 2 r(X) for explicit polynomials q, r, so v^3 = 1 in R.
--     Hence v is a unit with v^3 = 1; its order is also a power of 5, so v = 1.
-- (3) Then u + u^4 = 0; multiplying by u gives u^2 + 1 = 0, so u^2 = -1 = 1. With u^5 = 1 this gives u = 1,
--     a contradiction.

open OMA.S_mse_5011183 Polynomial

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5011183.main) := by
  intro hmain
  obtain ⟨R, hR, ⟨e⟩⟩ := hmain 5 (by norm_num)
  have hP : ∀ g : ℂˣ, g ∈ pruferGroup 5 → ∃ n : ℕ, g ^ (5 ^ n) = 1 := by
    intro g hg
    unfold pruferGroup at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, one_pow _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨m, hm⟩ := hy
      have h1 : x ^ (5 ^ (n + m)) = 1 := by rw [pow_add, pow_mul, hn, one_pow]
      have h2 : y ^ (5 ^ (n + m)) = 1 := by rw [pow_add, mul_comm, pow_mul, hm, one_pow]
      exact ⟨n + m, by rw [mul_pow, h1, h2, one_mul]⟩
    | inv x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, by rw [inv_pow, hn, inv_one]⟩
  have hU : ∀ x : Rˣ, ∃ n : ℕ, x ^ (5 ^ n) = 1 := by
    intro x
    obtain ⟨n, hn⟩ := hP (e x : ℂˣ) (e x).2
    refine ⟨n, e.injective ?_⟩
    apply Subtype.ext
    rw [map_pow, map_one]
    simpa using hn
  have hneg : (-1 : R) = 1 := by
    obtain ⟨n, hn⟩ := hU (-1)
    have hodd : Odd (5 ^ n) := Odd.pow (by decide)
    rw [Odd.neg_one_pow hodd] at hn
    have h3 := congrArg Units.val hn
    rw [Units.val_neg, Units.val_one] at h3
    exact h3
  have h2 : (2 : R) = 0 := by
    rw [← one_add_one_eq_two, ← add_neg_cancel (1 : R)]
    rw [hneg]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ 5 := ⟨_, Complex.isPrimitiveRoot_exp 5 (by norm_num)⟩
  have hζ5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0] at hζ5
    norm_num at hζ5
  have hz5 : (Units.mk0 ζ hζ0) ^ 5 = 1 := Units.ext (by simpa using hζ5)
  have hzmem : Units.mk0 ζ hζ0 ∈ pruferGroup 5 :=
    Subgroup.subset_closure ⟨1, by rw [pow_one]; exact hz5⟩
  obtain ⟨w, hw⟩ : ∃ w : pruferGroup 5, (w : ℂˣ) = Units.mk0 ζ hζ0 := ⟨⟨_, hzmem⟩, rfl⟩
  have hw5 : w ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hw, hz5, Subgroup.coe_one])
  have hw1 : w ≠ 1 := by
    intro h
    have h' := congrArg (fun t : pruferGroup 5 => ((t : ℂˣ) : ℂ)) h
    simp only [hw, Units.val_mk0, Subgroup.coe_one, Units.val_one] at h'
    exact hζ1 h'
  obtain ⟨u, hu⟩ : ∃ u : Rˣ, e u = w := ⟨e.symm w, e.apply_symm_apply w⟩
  have hu5 : u ^ 5 = 1 := e.injective (by rw [map_pow, hu, hw5, map_one])
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, map_one] at hu
    exact hw1 hu.symm
  have hu5R : (u : R) ^ 5 = 1 := by rw [← Units.val_pow_eq_pow_val, hu5, Units.val_one]
  have key : ((1 : ℤ[X]) + X + X ^ 4) ^ 3 = 1 + (X ^ 5 - 1) *
      (6 + 3 * X + X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 + X ^ 7) +
      2 * (3 + 3 * X + 2 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4) := by ring
  have hv3 : ((1 : R) + (u : R) + (u : R) ^ 4) ^ 3 = 1 := by
    have h := congrArg (Polynomial.aeval (u : R)) key
    simp only [map_pow, map_add, map_one, map_mul, map_sub, Polynomial.aeval_X, map_ofNat] at h
    rw [h]
    simp only [hu5R, h2, sub_self, zero_mul, add_zero]
  obtain ⟨v, hv⟩ : ∃ v : R, v = 1 + (u : R) + (u : R) ^ 4 := ⟨_, rfl⟩
  rw [← hv] at hv3
  obtain ⟨V, hV⟩ : ∃ V : Rˣ, (V : R) = v :=
    ⟨⟨v, v ^ 2, by rw [← pow_succ']; exact hv3, by rw [← pow_succ]; exact hv3⟩, rfl⟩
  have hV3 : V ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hV, hv3, Units.val_one])
  obtain ⟨n, hn⟩ := hU V
  have hV1 : V = 1 := by
    have hc : Nat.gcd 3 (5 ^ n) = 1 := Nat.Coprime.pow_right n (by decide)
    have h := pow_gcd_eq_one.mpr ⟨hV3, hn⟩
    rwa [hc, pow_one] at h
  have hv1 : (1 : R) + ((u : R) + (u : R) ^ 4) = 1 + 0 := by
    rw [← add_assoc, ← hv, ← hV, hV1, Units.val_one, add_zero]
  have h4 : (u : R) + (u : R) ^ 4 = 0 := add_left_cancel hv1
  have h6 : (u : R) ^ 2 + 1 = 0 := by
    have h5 : (u : R) * ((u : R) + (u : R) ^ 4) = 0 := by rw [h4, mul_zero]
    have e1 : (u : R) * ((u : R) + (u : R) ^ 4) = (u : R) ^ 2 + (u : R) ^ 5 := by noncomm_ring
    rw [e1, hu5R] at h5
    exact h5
  have hu2 : (u : R) ^ 2 = 1 := by rw [eq_neg_of_add_eq_zero_left h6, hneg]
  have hU2 : u ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hu2, Units.val_one])
  have hfin := pow_gcd_eq_one.mpr ⟨hU2, hu5⟩
  have hg : Nat.gcd 2 5 = 1 := by norm_num
  rw [hg, pow_one] at hfin
  exact hu1 hfin
