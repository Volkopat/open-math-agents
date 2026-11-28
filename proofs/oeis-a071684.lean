import OMAStatements.S_oeis_a071684

-- Problem: A071684: Number of plane trees with n edges and having an odd number of leaves (Mathar's recurrence).
-- Upstream: formal-conjectures statements/oeis-a071684.lean:0 (declaration OMA.S_oeis_a071684.main)
-- Credit: @thatoneguy006 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Write theta = X * d/dX. The recurrence for n >= 4 says exactly that
L = sum_j X^j f_j(theta) G, with f_j(m) = p_j(m + j), has no terms of degree >= 4.
Differentiating T^2 = 1 - 4X, W^2 = 1 + 4X^2 and 4XG = W - T - 2X three times gives twelve
identities. The product 262144 T^5 W^5 X^4 (L - (-54X + 6X^2)) is an explicit linear combination
of them (found by pseudo-division), so L = -54X + 6X^2 in the domain Q[[X]].
The coefficient of X^n then gives the recurrence.
-/

open PowerSeries

namespace A071684P

lemma d_ofNat (k : ℕ) [k.AtLeastTwo] : d⁄dX ℚ (OfNat.ofNat k : ℚ⟦X⟧) = 0 := by
  rw [show (OfNat.ofNat k : ℚ⟦X⟧) = C (OfNat.ofNat k : ℚ) from (map_ofNat C k).symm]
  exact derivative_C

lemma big_ne_zero : (262144 : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have h' : (C (262144 : ℚ) : ℚ⟦X⟧) = 0 := (map_ofNat C 262144).trans h
  have := congrArg (coeff 0) h'
  rw [coeff_zero_C, map_zero] at this
  norm_num at this

lemma ne_zero_of_coeff {f : ℚ⟦X⟧} (h : coeff 0 f = 1) : f ≠ 0 := by
  intro hf; rw [hf] at h; simp at h

lemma coeff_X_mul_deriv (f : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * d⁄dX ℚ f) = (k : ℚ) * coeff k f := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast; ring

theorem key (T W G : ℚ⟦X⟧) (hT0' : T ^ 2 = 1 - 4 * X) (hTc : coeff 0 T = 1)
    (hW0' : W ^ 2 = 1 + 4 * X ^ 2) (hWc : coeff 0 W = 1)
    (hG0' : 4 * X * G = W - T - 2 * X) :
    X ^ 0 * ((-37 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-27 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (10 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 1 * ((108 : ℚ⟦X⟧) * G + (44 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-54 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (10 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 2 * ((-12 : ℚ⟦X⟧) * G + (160 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (120 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (-160 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 3 * ((80 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-96 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (40 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 4 * ((-784 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-1968 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (-800 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) = -54 * X + 6 * X ^ 2 := by
  have d2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := d_ofNat 2
  have d4 : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := d_ofNat 4
  have d8 : d⁄dX ℚ (8 : ℚ⟦X⟧) = 0 := d_ofNat 8
  have d12 : d⁄dX ℚ (12 : ℚ⟦X⟧) = 0 := d_ofNat 12
  have d6 : d⁄dX ℚ (6 : ℚ⟦X⟧) = 0 := d_ofNat 6
  have hT0 : T ^ 2 - (1 - 4 * X) = 0 := by rw [hT0']; ring
  have hW0 : W ^ 2 - (1 + 4 * X ^ 2) = 0 := by rw [hW0']; ring
  have hG0 : 4 * X * G - (W - T - 2 * X) = 0 := by rw [hG0']; ring
  have hT1 : 2 * T * d⁄dX ℚ T + 4 = 0 := by
    have h := congrArg (d⁄dX ℚ) hT0
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_zero, derivative_X,
      derivative_one, smul_eq_mul, nsmul_eq_mul, d2, d4] at h
    push_cast at h
    linear_combination h
  have hT2 : 2 * d⁄dX ℚ T * d⁄dX ℚ T + 2 * T * d⁄dX ℚ (d⁄dX ℚ T) = 0 := by
    have h := congrArg (d⁄dX ℚ) hT1
    simp only [Derivation.leibniz, map_add, map_zero, smul_eq_mul, d2, d4] at h
    linear_combination h
  have hT3 : 6 * d⁄dX ℚ T * d⁄dX ℚ (d⁄dX ℚ T)
      + 2 * T * d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ T)) = 0 := by
    have h := congrArg (d⁄dX ℚ) hT2
    simp only [Derivation.leibniz, map_add, map_zero, smul_eq_mul, d2] at h
    linear_combination h
  have hW1 : 2 * W * d⁄dX ℚ W - 8 * X = 0 := by
    have h := congrArg (d⁄dX ℚ) hW0
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add, map_zero,
      derivative_X, derivative_one, smul_eq_mul, nsmul_eq_mul, d2, d4] at h
    push_cast at h
    linear_combination h
  have hW2 : 2 * d⁄dX ℚ W * d⁄dX ℚ W + 2 * W * d⁄dX ℚ (d⁄dX ℚ W) - 8 = 0 := by
    have h := congrArg (d⁄dX ℚ) hW1
    simp only [Derivation.leibniz, map_sub, map_zero, derivative_X, smul_eq_mul, d2, d8] at h
    linear_combination h
  have hW3 : 6 * d⁄dX ℚ W * d⁄dX ℚ (d⁄dX ℚ W)
      + 2 * W * d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ W)) = 0 := by
    have h := congrArg (d⁄dX ℚ) hW2
    simp only [Derivation.leibniz, map_add, map_sub, map_zero, smul_eq_mul, d2, d8] at h
    linear_combination h
  have hG1 : 4 * G + 4 * X * d⁄dX ℚ G - (d⁄dX ℚ W - d⁄dX ℚ T - 2) = 0 := by
    have h := congrArg (d⁄dX ℚ) hG0
    simp only [Derivation.leibniz, map_sub, map_zero, derivative_X, smul_eq_mul, d2, d4] at h
    linear_combination h
  have hG2 : 8 * d⁄dX ℚ G + 4 * X * d⁄dX ℚ (d⁄dX ℚ G)
      - (d⁄dX ℚ (d⁄dX ℚ W) - d⁄dX ℚ (d⁄dX ℚ T)) = 0 := by
    have h := congrArg (d⁄dX ℚ) hG1
    simp only [Derivation.leibniz, map_add, map_sub, map_zero, derivative_X, smul_eq_mul,
      d2, d4] at h
    linear_combination h
  have hG3 : 12 * d⁄dX ℚ (d⁄dX ℚ G) + 4 * X * d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G))
      - (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ W)) - d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ T))) = 0 := by
    have h := congrArg (d⁄dX ℚ) hG2
    simp only [Derivation.leibniz, map_add, map_sub, map_zero, derivative_X, smul_eq_mul,
      d4, d8] at h
    linear_combination h
  have ht2 : X * d⁄dX ℚ (X * d⁄dX ℚ G) = X * d⁄dX ℚ G + X ^ 2 * d⁄dX ℚ (d⁄dX ℚ G) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul]; ring
  have ht3 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G))
      = X * d⁄dX ℚ G + 3 * X ^ 2 * d⁄dX ℚ (d⁄dX ℚ G)
        + X ^ 3 * d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ G)) := by
    simp only [Derivation.leibniz, derivative_X, derivative_one, smul_eq_mul, map_add]; ring
  rw [ht3, ht2]
  set T1 := d⁄dX ℚ T
  set T2 := d⁄dX ℚ T1
  set T3 := d⁄dX ℚ T2
  set W1 := d⁄dX ℚ W
  set W2 := d⁄dX ℚ W1
  set W3 := d⁄dX ℚ W2
  set G1 := d⁄dX ℚ G
  set G2 := d⁄dX ℚ G1
  set G3 := d⁄dX ℚ G2
  have hM : (262144 * T ^ 5 * W ^ 5 * X ^ 4 : ℚ⟦X⟧) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero big_ne_zero
      (pow_ne_zero 5 (ne_zero_of_coeff hTc))) (pow_ne_zero 5 (ne_zero_of_coeff hWc)))
      (pow_ne_zero 4 X_ne_zero)
  refine mul_right_cancel₀ hM ?_
  linear_combination
      (25165824*T^4*W^5*X^7 + 14155776*T^4*W^5*X^6 - 7077888*T^4*W^5*X^5 - 25165824*T^3*W^6*X^7 - 14155776*T^3*W^6*X^6 + 7077888*T^3*W^6*X^5 - 415236096*T^3*W^4*X^9 + 31457280*T^3*W^4*X^8 + 14155776*T^3*W^4*X^6 - 7077888*T^3*W^4*X^5 + 4580179968*T^3*W^2*X^11 - 25165824*T^3*W^2*X^10 + 377487360*T^3*W^2*X^9 + 25165824*T^3*W^2*X^8 - 3145728*T^3*W^2*X^7 - 10066329600*T^3*X^13 + 503316480*T^3*X^12 - 2013265920*T^3*X^11 + 125829120*T^3*X^10 + 125829120*T^3*X^9 - 50331648*T^2*W^5*X^8 - 3145728*T^2*W^5*X^7 + 26738688*T^2*W^5*X^6 + 7077888*T^2*W^5*X^5 + 100663296*T*W^6*X^8 + 31457280*T*W^6*X^7 - 42467328*T*W^6*X^6 + 7077888*T*W^6*X^5 + 1660944384*T*W^4*X^10 - 541065216*T*W^4*X^9 + 31457280*T*W^4*X^8 - 56623104*T*W^4*X^7 + 42467328*T*W^4*X^6 - 7077888*T*W^4*X^5 - 18320719872*T*W^2*X^12 + 4680843264*T*W^2*X^11 - 1535115264*T*W^2*X^10 + 276824064*T*W^2*X^9 + 37748736*T*W^2*X^8 - 3145728*T*W^2*X^7 + 40265318400*T*X^14 - 12079595520*T*X^13 + 8556380160*T*X^12 - 2516582400*T*X^11 - 377487360*T*X^10 + 125829120*T*X^9 - 314572800*W^5*X^9 - 62914560*W^5*X^8 - 78643200*W^5*X^7 - 15728640*W^5*X^6) * hT0 +
      (-12582912*T^4*W^5*X^8 - 7077888*T^4*W^5*X^7 + 3932160*T^4*W^5*X^6 - 3538944*T^4*W^5*X^5 - 64487424*T^3*T1*W^5*X^9 - 3145728*T^3*T1*W^5*X^8 + 3932160*T^3*T1*W^5*X^7 - 1769472*T^3*T1*W^5*X^6 - 884736*T^3*T1*W^5*X^5 + 78643200*T^2*T1^2*W^5*X^10 - 3932160*T^2*T1^2*W^5*X^9 + 15728640*T^2*T1^2*W^5*X^8 - 983040*T^2*T1^2*W^5*X^7 - 983040*T^2*T1^2*W^5*X^6 + 128974848*T^2*W^5*X^9 + 6291456*T^2*W^5*X^8 - 7864320*T^2*W^5*X^7 + 3538944*T^2*W^5*X^6 + 1769472*T^2*W^5*X^5 - 157286400*T*T1*W^5*X^10 + 7864320*T*T1*W^5*X^9 - 31457280*T*T1*W^5*X^8 + 1966080*T*T1*W^5*X^7 + 1966080*T*T1*W^5*X^6 + 314572800*W^5*X^10 - 15728640*W^5*X^9 + 62914560*W^5*X^8 - 3932160*W^5*X^7 - 3932160*W^5*X^6) * hT1 +
      (64487424*T^4*W^5*X^9 + 3145728*T^4*W^5*X^8 - 3932160*T^4*W^5*X^7 + 1769472*T^4*W^5*X^6 + 884736*T^4*W^5*X^5 - 78643200*T^3*T1*W^5*X^10 + 3932160*T^3*T1*W^5*X^9 - 15728640*T^3*T1*W^5*X^8 + 983040*T^3*T1*W^5*X^7 + 983040*T^3*T1*W^5*X^6) * hT2 +
      (26214400*T^4*W^5*X^10 - 1310720*T^4*W^5*X^9 + 5242880*T^4*W^5*X^8 - 327680*T^4*W^5*X^7 - 327680*T^4*W^5*X^6) * hT3 +
      (-402653184*T*W^4*X^9 - 25165824*T*W^4*X^8 + 201326592*T*W^4*X^7 - 70778880*T*W^4*X^6 + 7077888*T*W^4*X^5 - 8254390272*T*W^2*X^11 + 3724541952*T*W^2*X^10 - 264241152*T*W^2*X^9 - 50331648*T*W^2*X^8 + 3145728*T*W^2*X^7 + 40265318400*T*X^13 - 22145925120*T*X^12 + 1509949440*T*X^11 + 880803840*T*X^10 - 125829120*T*X^9) * hW0 +
      (12582912*T^5*W^4*X^8 + 7077888*T^5*W^4*X^7 - 3932160*T^5*W^4*X^6 + 3538944*T^5*W^4*X^5 + 64487424*T^5*W^3*W1*X^9 + 3145728*T^5*W^3*W1*X^8 - 3932160*T^5*W^3*W1*X^7 + 1769472*T^5*W^3*W1*X^6 + 884736*T^5*W^3*W1*X^5 - 78643200*T^5*W^2*W1^2*X^10 + 3932160*T^5*W^2*W1^2*X^9 - 15728640*T^5*W^2*W1^2*X^8 + 983040*T^5*W^2*W1^2*X^7 + 983040*T^5*W^2*W1^2*X^6 + 572522496*T^5*W^2*X^10 - 3145728*T^5*W^2*X^9 + 47185920*T^5*W^2*X^8 + 3145728*T^5*W^2*X^7 - 393216*T^5*W^2*X^6 - 314572800*T^5*W*W1*X^11 + 15728640*T^5*W*W1*X^10 - 62914560*T^5*W*W1*X^9 + 3932160*T^5*W*W1*X^8 + 3932160*T^5*W*W1*X^7 - 1258291200*T^5*X^12 + 62914560*T^5*X^11 - 251658240*T^5*X^10 + 15728640*T^5*X^9 + 15728640*T^5*X^8) * hW1 +
      (-64487424*T^5*W^4*X^9 - 3145728*T^5*W^4*X^8 + 3932160*T^5*W^4*X^7 - 1769472*T^5*W^4*X^6 - 884736*T^5*W^4*X^5 + 78643200*T^5*W^3*W1*X^10 - 3932160*T^5*W^3*W1*X^9 + 15728640*T^5*W^3*W1*X^8 - 983040*T^5*W^3*W1*X^7 - 983040*T^5*W^3*W1*X^6) * hW2 +
      (-26214400*T^5*W^4*X^10 + 1310720*T^5*W^4*X^9 - 5242880*T^5*W^4*X^8 + 327680*T^5*W^4*X^7 + 327680*T^5*W^4*X^6) * hW3 +
      (-25165824*T^5*W^5*X^7 - 14155776*T^5*W^5*X^6 + 7077888*T^5*W^5*X^5) * hG0 +
      (25165824*T^5*W^5*X^8 + 14155776*T^5*W^5*X^7 - 7864320*T^5*W^5*X^6 + 7077888*T^5*W^5*X^5) * hG1 +
      (-128974848*T^5*W^5*X^9 - 6291456*T^5*W^5*X^8 + 7864320*T^5*W^5*X^7 - 3538944*T^5*W^5*X^6 - 1769472*T^5*W^5*X^5) * hG2 +
      (-52428800*T^5*W^5*X^10 + 2621440*T^5*W^5*X^9 - 10485760*T^5*W^5*X^8 + 655360*T^5*W^5*X^7 + 655360*T^5*W^5*X^6) * hG3

theorem final : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 W = 1 →
    4 * X * G = W - T - 2 * X →
    coeff 0 G = 0 →
    ∀ n : ℕ, 4 ≤ n →
      (-37 * (n : ℚ) - 27 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3) * coeff n G + (182 * (n : ℚ) - 84 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (1428 - 2240 * (n : ℚ) + 1080 * (n : ℚ) ^ 2 - 160 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-2184 + 1736 * (n : ℚ) - 456 * (n : ℚ) ^ 2 + 40 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (22848 - 23440 * (n : ℚ) + 7632 * (n : ℚ) ^ 2 - 800 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  intro T W G hT hTc hW hWc hG _ n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hk := key T W G hT hTc hW hWc hG
  have hC : X ^ 0 * ((-37 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-27 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (10 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 1 * ((108 : ℚ⟦X⟧) * G + (44 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-54 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (10 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 2 * ((-12 : ℚ⟦X⟧) * G + (160 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (120 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (-160 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 3 * ((80 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-96 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (40 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 4 * ((-784 : ℚ⟦X⟧) * (X * d⁄dX ℚ G) + (-1968 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + (-800 : ℚ⟦X⟧) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G))))
      = X ^ 0 * (C (-37 : ℚ) * (X * d⁄dX ℚ G) + C (-27 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + C (10 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 1 * (C (108 : ℚ) * G + C (44 : ℚ) * (X * d⁄dX ℚ G) + C (-54 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + C (10 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 2 * (C (-12 : ℚ) * G + C (160 : ℚ) * (X * d⁄dX ℚ G) + C (120 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + C (-160 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 3 * (C (80 : ℚ) * (X * d⁄dX ℚ G) + C (-96 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + C (40 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) + X ^ 4 * (C (-784 : ℚ) * (X * d⁄dX ℚ G) + C (-1968 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) + C (-800 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))) := by
    simp only [map_neg, map_ofNat]
  have hQ : (-54 * X + 6 * X ^ 2 : ℚ⟦X⟧) = C (-54 : ℚ) * X + C (6 : ℚ) * X ^ 2 := by
    simp only [map_neg, map_ofNat]
  rw [hC, hQ] at hk
  have hc := congrArg (coeff (m + 4)) hk
  have c1 : ∀ N : ℕ, coeff N (X * d⁄dX ℚ G) = (N : ℚ) * coeff N G := coeff_X_mul_deriv G
  have c2 : ∀ N : ℕ, coeff N (X * d⁄dX ℚ (X * d⁄dX ℚ G)) = (N : ℚ) * ((N : ℚ) * coeff N G) :=
    fun N => by rw [coeff_X_mul_deriv, c1]
  have c3 : ∀ N : ℕ, coeff N (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ G)))
      = (N : ℚ) * ((N : ℚ) * ((N : ℚ) * coeff N G)) :=
    fun N => by rw [coeff_X_mul_deriv, c2]
  have x0 : ∀ F : ℚ⟦X⟧, coeff (m + 4) (X ^ 0 * F) = coeff (m + 4) F :=
    fun F => by rw [pow_zero, one_mul]
  have x1 : ∀ F : ℚ⟦X⟧, coeff (m + 4) (X ^ 1 * F) = coeff (m + 3) F :=
    fun F => coeff_X_pow_mul F 1 (m + 3)
  have x2 : ∀ F : ℚ⟦X⟧, coeff (m + 4) (X ^ 2 * F) = coeff (m + 2) F :=
    fun F => coeff_X_pow_mul F 2 (m + 2)
  have x3 : ∀ F : ℚ⟦X⟧, coeff (m + 4) (X ^ 3 * F) = coeff (m + 1) F :=
    fun F => coeff_X_pow_mul F 3 (m + 1)
  have x4 : ∀ F : ℚ⟦X⟧, coeff (m + 4) (X ^ 4 * F) = coeff m F :=
    fun F => coeff_X_pow_mul F 4 m
  have q1 : coeff (m + 4) (C (-54 : ℚ) * X) = 0 := by rw [coeff_C_mul, coeff_X]; simp
  have q2 : coeff (m + 4) (C (6 : ℚ) * X ^ 2) = 0 := by rw [coeff_C_mul, coeff_X_pow]; simp
  simp only [map_add, x0, x1, x2, x3, x4, coeff_C_mul, c1, c2, c3, q1, q2, add_zero] at hc
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  push_cast at hc ⊢
  linear_combination hc

end A071684P

theorem OMA.solution : type_of% @OMA.S_oeis_a071684.main := by
  exact A071684P.final
