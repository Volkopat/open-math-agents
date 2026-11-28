import OMAStatements.S_oeis_a401548

/-!
# Optimal greedy sums of squares

We prove Abo Khmiss's conjecture in OEIS A401548 and compute the leading
coefficient `(16/525) * 2^(17/8)`. The proof counts greedy expansions
by their first square and establishes equidistribution of finite ordered
root residues. Lengths below four are negligible. Legendre's theorem
classifies the optimal four-root cases. Their dyadic layers give the
proportion `(1/8 + 1/64) / (1 - 1/16) = 3/20`.

Source: https://oeis.org/A401548
Prior lattice-counting and congruence plan: @rkka02, LeftToSolve desk note #115985.
The next section credits and preserves the full license of the ATLAS
formalization reused for Legendre's theorem.
-/


/-!
# Legendre's three-square theorem for the optimal greedy-square criterion

This is the three-square section of the accepted project proof of A004215,
as recorded in open-math-agents commit 4d26678698d2d59849d9dda317e3c40dc27ff625
(PR #8183). The theorem body is unchanged.

The following three-square proof in namespace Nat is adapted from ATLAS,
MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean, commit
dcb77c85757e945810657e5dce688ae82ff8eb25. The module header was removed
and conditional rewrite lemmas were updated for this Mathlib version.

Source: https://github.com/Deicyde/atlas-lean/blob/dcb77c85757e945810657e5dce688ae82ff8eb25/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
The upstream license is reproduced at the end of this file.
-/

namespace Nat

/-- Divisibility step of Ankeny's proof: a small nonzero lattice value divisible
by both `m` and `k` (which are coprime since `m ∣ k + 1`) and below `2 * m * k`
must equal `m * k`. -/
private theorem ankeny_lattice_value_eq {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hmk : m ∣ k + 1) {b : ℤ} (hb : (k : ℤ) ∣ b ^ 2 + (m : ℤ))
    {R X T : ℤ} (hne : ¬ (R = 0 ∧ X = 0 ∧ T = 0))
    (hRX : (m : ℤ) ∣ R - X) (hXT : (k : ℤ) ∣ X - b * T)
    (hlt : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 < 2 * (m : ℤ) * (k : ℤ)) :
    (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 = (m : ℤ) * (k : ℤ) := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hVnn : (0 : ℤ) ≤ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    positivity
  have hVne : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 ≠ 0 := by
    intro hV0
    have e1 : (0 : ℤ) ≤ (k : ℤ) * R ^ 2 := by positivity
    have e2 : (0 : ℤ) ≤ X ^ 2 := by positivity
    have e3 : (0 : ℤ) ≤ (m : ℤ) * T ^ 2 := by positivity
    have g1 : (k : ℤ) * R ^ 2 = 0 := le_antisymm (by linarith) e1
    have g2 : X ^ 2 = 0 := le_antisymm (by linarith) e2
    have g3 : (m : ℤ) * T ^ 2 = 0 := le_antisymm (by linarith) e3
    obtain ⟨hR, hX, hT⟩ : (k : ℤ) * R ^ 2 = 0 ∧ X ^ 2 = 0 ∧ (m : ℤ) * T ^ 2 = 0 :=
      ⟨g1, g2, g3⟩
    have hR0 : R = 0 := by
      by_contra hR
      have hpos2 : (0 : ℤ) < (k : ℤ) * R ^ 2 :=
        mul_pos hkZ (sq_pos_of_ne_zero hR)
      linarith
    have hX0 : X = 0 := by
      by_contra hX
      have hpos : (0 : ℤ) < X ^ 2 := sq_pos_of_ne_zero hX
      linarith
    have hT0 : T = 0 := by
      by_contra hT
      have hpos2 : (0 : ℤ) < (m : ℤ) * T ^ 2 :=
        mul_pos hmZ (sq_pos_of_ne_zero hT)
      linarith
    exact hne ⟨hR0, hX0, hT0⟩
  have hVpos : (0 : ℤ) < (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 :=
    lt_of_le_of_ne hVnn (Ne.symm hVne)
  -- `k` divides the value, via `X ≡ b * T`.
  have hX : b * T ≡ X [ZMOD (k : ℤ)] := Int.modEq_iff_dvd.mpr hXT
  have hkV : (k : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    have e1 : (b * T) ^ 2 ≡ X ^ 2 [ZMOD (k : ℤ)] := hX.pow 2
    have e2 : (b * T) ^ 2 + (m : ℤ) * T ^ 2 ≡ X ^ 2 + (m : ℤ) * T ^ 2
        [ZMOD (k : ℤ)] := e1.add_right _
    have hrr : (b * T) ^ 2 + (m : ℤ) * T ^ 2 = (b ^ 2 + (m : ℤ)) * T ^ 2 := by
      ring
    rw [hrr] at e2
    have hzero : (b ^ 2 + (m : ℤ)) * T ^ 2 ≡ 0 [ZMOD (k : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hb _)
    have hfin : X ^ 2 + (m : ℤ) * T ^ 2 ≡ 0 [ZMOD (k : ℤ)] := e2.symm.trans hzero
    have hdvd : (k : ℤ) ∣ X ^ 2 + (m : ℤ) * T ^ 2 := by
      have h := hfin.dvd
      rwa [zero_sub, dvd_neg] at h
    have h1 : (k : ℤ) ∣ (k : ℤ) * R ^ 2 := dvd_mul_right _ _
    have h := h1.add hdvd
    rwa [← add_assoc] at h
  -- `m` divides the value, via `R ≡ X` and `k + 1 ≡ 0`.
  have hR : X ≡ R [ZMOD (m : ℤ)] := Int.modEq_iff_dvd.mpr hRX
  have hmV : (m : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := by
    have e1 : (k : ℤ) * X ^ 2 ≡ (k : ℤ) * R ^ 2 [ZMOD (m : ℤ)] :=
      (Int.ModEq.refl _).mul (hR.pow 2)
    have hmid : (k : ℤ) * X ^ 2 + X ^ 2 ≡ (k : ℤ) * R ^ 2 + X ^ 2
        [ZMOD (m : ℤ)] := e1.add (Int.ModEq.refl _)
    have hring : (k : ℤ) * X ^ 2 + X ^ 2 = ((k : ℤ) + 1) * X ^ 2 := by ring
    rw [hring] at hmid
    have hkm : ((k : ℤ) + 1) * X ^ 2 ≡ 0 [ZMOD (m : ℤ)] := by
      have hcast : (m : ℤ) ∣ ((k : ℤ) + 1) := by exact_mod_cast hmk
      exact Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hcast _)
    have hfin : (k : ℤ) * R ^ 2 + X ^ 2 ≡ 0 [ZMOD (m : ℤ)] :=
      hmid.symm.trans hkm
    have hdvd : (m : ℤ) ∣ (k : ℤ) * R ^ 2 + X ^ 2 := by
      have h := hfin.dvd
      rwa [zero_sub, dvd_neg] at h
    have h2 : (m : ℤ) ∣ (m : ℤ) * T ^ 2 := dvd_mul_right _ _
    exact hdvd.add h2
  -- `(m : ℤ)` and `(k : ℤ)` are coprime since `m ∣ k + 1`, so their product
  -- divides the value.
  have hiso : IsCoprime (m : ℤ) (k : ℤ) := by
    obtain ⟨t, ht⟩ := hmk
    refine ⟨(t : ℤ), -1, ?_⟩
    have h2 : ((k + 1 : ℕ) : ℤ) = ((m * t : ℕ) : ℤ) := by exact_mod_cast ht
    push_cast at h2
    linear_combination -h2
  have hmkV : (m : ℤ) * (k : ℤ)
      ∣ (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 := hiso.mul_dvd hmV hkV
  have hmkZ : (0 : ℤ) < (m : ℤ) * (k : ℤ) := mul_pos hmZ hkZ
  obtain ⟨j, hj⟩ := hmkV
  have hjpos : 0 < j := by
    by_contra h
    push Not at h
    have hle : (m : ℤ) * (k : ℤ) * j ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hmkZ) h
    linarith
  have hjlt : j < 2 := by
    by_contra h
    push Not at h
    have hle : 2 * ((m : ℤ) * (k : ℤ)) ≤ (m : ℤ) * (k : ℤ) * j := by
      calc 2 * ((m : ℤ) * (k : ℤ)) = ((m : ℤ) * (k : ℤ)) * 2 := by ring
        _ ≤ ((m : ℤ) * (k : ℤ)) * j :=
          mul_le_mul_of_nonneg_left h (le_of_lt hmkZ)
    linarith
  have hj1 : j = 1 := by omega
  rw [hj1, mul_one] at hj
  exact hj

/-- Valuation step: if `-d` is not a square in `ZMod p`, then every value of
`X ^ 2 + d * T ^ 2` has even `p`-adic valuation. -/
private theorem even_padicValInt_sq_add_mul_sq_of_not_isSquare {p : ℕ} [Fact p.Prime]
    {d : ℤ} (hd : ¬ IsSquare (-(d : ZMod p))) (X T : ℤ) :
    Even (padicValInt p (X ^ 2 + d * T ^ 2)) := by
  have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have key : ∀ N : ℕ, ∀ X T : ℤ, X.natAbs + T.natAbs = N →
      Even (padicValInt p (X ^ 2 + d * T ^ 2)) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro X T hNT
      by_cases h0 : X ^ 2 + d * T ^ 2 = 0
      · rw [h0, padicValInt.zero]
        exact ⟨0, rfl⟩
      by_cases hdvd : (p : ℤ) ∣ X ^ 2 + d * T ^ 2
      · have hT : (p : ℤ) ∣ T := by
          by_contra hT
          have hTz : (T : ZMod p) ≠ 0 := fun hz =>
            hT ((ZMod.intCast_zmod_eq_zero_iff_dvd T p).mp hz)
          have hcast : (X : ZMod p) ^ 2 + (d : ZMod p) * (T : ZMod p) ^ 2 = 0 := by
            have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
            push_cast at h
            exact h
          set x : ZMod p := (X : ZMod p) with hx
          set t : ZMod p := (T : ZMod p) with ht
          set δ : ZMod p := (d : ZMod p) with hδ
          have hx2 : x ^ 2 = -(δ * t ^ 2) := by linear_combination hcast
          have e2 : (t⁻¹) ^ 2 * t ^ 2 = 1 := by
            rw [← mul_pow, inv_mul_cancel₀ hTz, one_pow]
          have e3 : -(δ * t ^ 2) * (t⁻¹) ^ 2 = -δ := by
            have e4 : -(δ * t ^ 2) * (t⁻¹) ^ 2 = -δ * ((t⁻¹) ^ 2 * t ^ 2) := by
              ring
            rw [e4, e2, mul_one]
          have hsq : -(δ) = (x * t⁻¹) * (x * t⁻¹) := by
            have e : (x * t⁻¹) * (x * t⁻¹) = x ^ 2 * (t⁻¹) ^ 2 := by ring
            rw [e, hx2, e3]
          exact hd ⟨x * t⁻¹, hsq⟩
        have hT2 : (p : ℤ) ∣ d * T ^ 2 :=
          dvd_mul_of_dvd_right (dvd_pow hT two_ne_zero) _
        have hX2 : (p : ℤ) ∣ X ^ 2 := (dvd_add_left hT2).mp hdvd
        have hX : (p : ℤ) ∣ X := hpZ.dvd_of_dvd_pow hX2
        obtain ⟨X', hX'⟩ := hX
        obtain ⟨T', hT'⟩ := hT
        have hfactor : X ^ 2 + d * T ^ 2
            = (p : ℤ) ^ 2 * (X' ^ 2 + d * T' ^ 2) := by
          rw [hX', hT']
          ring
        have hSne : X' ^ 2 + d * T' ^ 2 ≠ 0 := by
          intro hcon
          apply h0
          rw [hfactor, hcon, mul_zero]
        have hpp : padicValInt p ((p : ℤ) ^ 2) = 2 := by
          have h1 : (p : ℤ) ^ 2 = (p : ℤ) * (p : ℤ) := by ring
          have hp0 : (p : ℤ) ≠ 0 := by
            have := hp2
            omega
          rw [h1, padicValInt.mul hp0 hp0, padicValInt.self hp2]
        have hval : padicValInt p (X ^ 2 + d * T ^ 2)
            = 2 + padicValInt p (X' ^ 2 + d * T' ^ 2) := by
          rw [hfactor, padicValInt.mul (by positivity) hSne, hpp]
        have eX : X.natAbs = p * X'.natAbs := by
          rw [hX', Int.natAbs_mul, Int.natAbs_natCast]
        have eT : T.natAbs = p * T'.natAbs := by
          rw [hT', Int.natAbs_mul, Int.natAbs_natCast]
        have hXle : X'.natAbs ≤ X.natAbs := by
          rw [eX]
          exact le_mul_of_one_le_left (Nat.zero_le _) hp2.le
        have hTle : T'.natAbs ≤ T.natAbs := by
          rw [eT]
          exact le_mul_of_one_le_left (Nat.zero_le _) hp2.le
        have hne00 : X ≠ 0 ∨ T ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply h0
          rw [hcon.1, hcon.2]
          simp
        have hltN : X'.natAbs + T'.natAbs < N := by
          have hXlt : X ≠ 0 → X'.natAbs < X.natAbs := by
            intro hneX
            have hneX' : X' ≠ 0 := by
              intro hcon
              apply hneX
              rw [hX', hcon, mul_zero]
            rw [eX]
            have hpos : 0 < X'.natAbs := Int.natAbs_pos.mpr hneX'
            calc X'.natAbs = 1 * X'.natAbs := (one_mul _).symm
              _ < p * X'.natAbs := by
                rw [one_mul]
                exact lt_mul_of_one_lt_left hpos hp2
          have hTlt : T ≠ 0 → T'.natAbs < T.natAbs := by
            intro hneT
            have hneT' : T' ≠ 0 := by
              intro hcon
              apply hneT
              rw [hT', hcon, mul_zero]
            rw [eT]
            have hpos : 0 < T'.natAbs := Int.natAbs_pos.mpr hneT'
            calc T'.natAbs = 1 * T'.natAbs := (one_mul _).symm
              _ < p * T'.natAbs := by
                rw [one_mul]
                exact lt_mul_of_one_lt_left hpos hp2
          rcases hne00 with hneX | hneT
          · have := hXlt hneX
            omega
          · have := hTlt hneT
            omega
        have ihE := ih _ hltN X' T' rfl
        rw [hval]
        obtain ⟨r, hr⟩ := ihE
        exact ⟨r + 1, by omega⟩
      · rw [padicValInt.eq_zero_of_not_dvd hdvd]
        exact ⟨0, rfl⟩
  exact key _ X T rfl

/-- Two-square step: from `m = R ^ 2 + N` and `k * N = X ^ 2 + m * T ^ 2`,
with `m` squarefree and no prime factor of `k` congruent to `3 mod 4`,
conclude `N` is a sum of two natural squares. -/
private theorem ankeny_exists_two_sq_of_rep {m k : ℕ} (hm : Squarefree m)
    (hk : 0 < k) (hmk : m ∣ k + 1)
    (hk4 : ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3)
    {R X T : ℤ} {N : ℕ} (hRm : (m : ℤ) = R ^ 2 + (N : ℤ))
    (hrep : (k : ℤ) * (N : ℤ) = X ^ 2 + (m : ℤ) * T ^ 2) :
    ∃ a c : ℕ, N = a ^ 2 + c ^ 2 := by
  by_cases hN0 : N = 0
  · subst hN0
    exact ⟨0, 0, by simp⟩
  rw [Nat.eq_sq_add_sq_iff]
  intro q hq hq4
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdvdN : q ∣ N := Nat.dvd_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqprime⟩
  have hpZq : _root_.Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqprime
  have hqN : (q : ℤ) ∣ (N : ℤ) := by exact_mod_cast hqdvdN
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqprime.ne_zero
  by_cases hqm : (q : ℤ) ∣ (m : ℤ)
  · -- Case `q ∣ m`: derive a contradiction from `-1` being a square mod `q`.
    have hqmN : q ∣ m := Int.natCast_dvd_natCast.mp hqm
    have hqk1 : q ∣ k + 1 := dvd_trans hqmN hmk
    rcases hqmN with ⟨m₁, hm₁⟩
    have hqm1 : ¬ q ∣ m₁ := by
      intro hd
      obtain ⟨t, ht⟩ := hd
      have hqq : q * q ∣ m := ⟨t, by rw [hm₁, ht]; ring⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hm) q hqprime hqq
    have hR2 : (q : ℤ) ∣ R ^ 2 := by
      have e : R ^ 2 = (m : ℤ) - (N : ℤ) := by omega
      rw [e]
      obtain ⟨a, ha⟩ := hqm
      obtain ⟨b, hb⟩ := hqN
      exact ⟨a - b, by linear_combination ha - hb⟩
    have hR : (q : ℤ) ∣ R := hpZq.dvd_of_dvd_pow hR2
    have hX2 : (q : ℤ) ∣ X ^ 2 := by
      have e : X ^ 2 = (k : ℤ) * (N : ℤ) - (m : ℤ) * T ^ 2 := by omega
      rw [e]
      obtain ⟨a, ha⟩ := dvd_mul_of_dvd_right hqN ((k : ℤ))
      obtain ⟨b, hb⟩ := dvd_mul_of_dvd_right hqm (T ^ 2)
      exact ⟨a - b, by linear_combination ha - hb⟩
    have hX : (q : ℤ) ∣ X := hpZq.dvd_of_dvd_pow hX2
    obtain ⟨R₁, hR₁⟩ := hR
    obtain ⟨X₁, hX₁⟩ := hX
    obtain ⟨N₁, hN₁⟩ := hqdvdN
    have hdiv : (k : ℤ) * (N₁ : ℤ) = (q : ℤ) * X₁ ^ 2 + (m₁ : ℤ) * T ^ 2 := by
      have h := hrep
      rw [hN₁, hm₁, hX₁] at h
      push_cast at h
      have h2 : ((k : ℤ) * (N₁ : ℤ)) * (q : ℤ)
          = ((q : ℤ) * X₁ ^ 2 + (m₁ : ℤ) * T ^ 2) * (q : ℤ) := by
        linear_combination h
      exact mul_right_cancel₀ hq0 h2
    have hNm : (N₁ : ℤ) = (m₁ : ℤ) - (q : ℤ) * R₁ ^ 2 := by
      have h := hRm
      rw [hN₁, hm₁, hR₁] at h
      push_cast at h
      have hcan : ((m₁ : ℤ) - (N₁ : ℤ)) * (q : ℤ)
          = ((q : ℤ) * R₁ ^ 2) * (q : ℤ) := by
        linear_combination h
      have hcan2 := mul_right_cancel₀ hq0 hcan
      omega
    have hdivZ : (k : ZMod q) * ((N₁ : ℕ) : ZMod q)
        = ((m₁ : ℕ) : ZMod q) * (T : ZMod q) ^ 2 := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hdiv
      simpa using h
    have hNmZ : ((N₁ : ℕ) : ZMod q) = ((m₁ : ℕ) : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hNm
      simpa using h
    rw [hNmZ] at hdivZ
    have hm1z : ((m₁ : ℕ) : ZMod q) ≠ 0 := by
      intro hz
      apply hqm1
      have hz' : ((((m₁ : ℕ)) : ℤ) : ZMod q) = 0 := by exact_mod_cast hz
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz'
      exact Int.natCast_dvd_natCast.mp hdvd
    have hkT : (k : ZMod q) = (T : ZMod q) ^ 2 := by
      have h := hdivZ
      rw [mul_comm ((m₁ : ℕ) : ZMod q) _] at h
      exact mul_right_cancel₀ hm1z h
    have hk1 : ((k : ℕ) : ZMod q) = -1 := by
      have hdvd : (q : ℤ) ∣ ((k : ℕ) : ℤ) + 1 := by exact_mod_cast hqk1
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
      have hz2 : ((k : ℕ) : ZMod q) + 1 = 0 := by
        simpa using hz
      linear_combination hz2
    have hsqN : IsSquare (-1 : ZMod q) := ⟨(T : ZMod q), by rw [← hk1, hkT, pow_two]⟩
    exact absurd hq4 (ZMod.exists_sq_eq_neg_one_iff.mp hsqN)
  · -- Case `¬ q ∣ m`: the valuation of `N` is even.
    have hqmB : ¬ q ∣ m := fun hd => hqm (by exact_mod_cast hd)
    have hqk : ¬ q ∣ k := fun hd => (hk4 q hqprime hd) hq4
    have hNq : ((N : ℕ) : ZMod q) = 0 := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hqN
      exact_mod_cast h
    have hRmZ : ((m : ℕ) : ZMod q) = (R : ZMod q) ^ 2 + ((N : ℕ) : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) hRm
      simpa using h
    have hnsqB : ¬ IsSquare (-((((m : ℕ)) : ℤ) : ZMod q)) := by
      intro hs
      have hRz : (R : ZMod q) ≠ 0 := by
        intro hz
        apply hqmB
        have h : ((m : ℕ) : ZMod q) = 0 := by
          rw [hRmZ, hz, hNq]
          simp
        have h' : ((((m : ℕ)) : ℤ) : ZMod q) = 0 := by exact_mod_cast h
        have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
        exact Int.natCast_dvd_natCast.mp hdvd
      obtain ⟨s, hs⟩ := hs
      have hRmz : (R : ZMod q) ^ 2 = ((((m : ℕ)) : ℤ) : ZMod q) := by
        have h := hRmZ
        rw [hNq, add_zero] at h
        exact_mod_cast h.symm
      have hsq1 : (-1 : ZMod q)
          = (s * (R : ZMod q)⁻¹) * (s * (R : ZMod q)⁻¹) := by
        have eR : (R : ZMod q) * (R : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hRz
        have e : (s * (R : ZMod q)⁻¹) * (s * (R : ZMod q)⁻¹)
            = (s * s) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) := by ring
        have e3 : ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2 = 1 := by
          have e4 : ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2
              = ((R : ZMod q) * (R : ZMod q)⁻¹) ^ 2 := by ring
          rw [e4, eR, one_pow]
        have e6 : -((R : ZMod q) ^ 2) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹)
            = -1 := by
          have e7 : -((R : ZMod q) ^ 2) * ((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹)
              = -(((R : ZMod q)⁻¹ * (R : ZMod q)⁻¹) * (R : ZMod q) ^ 2) := by
            ring
          rw [e7, e3]
        rw [e, ← hs, ← hRmz]
        exact e6.symm
      exact (ZMod.exists_sq_eq_neg_one_iff.mp ⟨_, hsq1⟩) hq4
    have hmul : padicValInt q ((k : ℤ) * (N : ℤ))
        = padicValNat q k + padicValNat q N := by
      have hk0 : (k : ℤ) ≠ 0 := by
        have := hk
        omega
      have hN0' : (N : ℤ) ≠ 0 := by
        have := hN0
        omega
      rw [padicValInt.mul hk0 hN0', padicValInt.of_nat, padicValInt.of_nat]
    have heven := even_padicValInt_sq_add_mul_sq_of_not_isSquare (p := q) hnsqB X T
    rw [← hrep, hmul, padicValNat.eq_zero_of_not_dvd hqk, zero_add] at heven
    exact heven

/-- Jacobi step, case `m ≡ 1 (mod 4)`: `-m` is a nonzero square in `ZMod q`. -/
private theorem isSquare_neg_of_one_mod_four_case {q m : ℕ} [Fact q.Prime]
    (hq : q % 4 = 1) (hm : m % 4 = 1) (hdvd : m ∣ q + 1) :
    IsSquare (-((m : ℕ) : ZMod q)) ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 1, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  -- `q ≡ -1 (mod m)` as integers.
  have hmod : (q : ℤ) % ((m : ℕ) : ℤ) = (-1 : ℤ) % ((m : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hcast : ((m : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hdvd
    have h0 : ((q : ℤ) + 1) % ((m : ℕ) : ℤ) = 0 := Int.emod_eq_zero_of_dvd hcast
    have heq : (q : ℤ) - (-1) = (q : ℤ) + 1 := by ring
    rw [heq]
    exact h0
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq
  have hchim : ZMod.χ₄ (↑m : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hm
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hqodd, hchiq, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four hm hqodd,
      jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hmodd, hchim]
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hsq, by simpa using hqm0⟩

/-- Jacobi step, case `m ≡ 3 (mod 8)`: `-m` is a nonzero square in `ZMod q`. -/
private theorem isSquare_neg_of_three_mod_eight_case {q m : ℕ} [Fact q.Prime]
    (hq : q % 4 = 1) (hm : m % 8 = 3) (hdvd : m ∣ 2 * q + 1) :
    IsSquare (-((m : ℕ) : ZMod q)) ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ 2 * q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ 2 * (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 2, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  -- `-2 * q ≡ 1 (mod m)` as integers.
  have hmod2 : (-2 * (q : ℤ)) % ((m : ℕ) : ℤ) = (1 : ℤ) % ((m : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdvd2 : ((m : ℕ) : ℤ) ∣ (-2 * (q : ℤ)) - 1 := by
      have hcast : ((m : ℕ) : ℤ) ∣ 2 * (q : ℤ) + 1 := by exact_mod_cast hdvd
      obtain ⟨a, ha⟩ := hcast
      exact ⟨-a, by linear_combination -ha⟩
    exact Int.emod_eq_zero_of_dvd hdvd2
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq
  have hchi8 : ZMod.χ₈' (↑m : ZMod 8) = 1 := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg (by omega : ¬ m % 2 = 0),
      if_pos (Or.inr hm)]
  have hJq : jacobiSym ((q : ℤ)) m = 1 := by
    have h2q1 : jacobiSym (-2 * (q : ℤ)) m = 1 := by
      rw [jacobiSym.mod_left' hmod2, jacobiSym.one_left]
    have hsplit := jacobiSym.mul_left (-2 : ℤ) ((q : ℤ)) m
    have hneg2 : jacobiSym (-2 : ℤ) m = 1 := by
      rw [jacobiSym.at_neg_two hmodd]
      exact hchi8
    rw [hsplit, hneg2, one_mul] at h2q1
    exact h2q1
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg _ hqodd, hchiq, one_mul,
      (jacobiSym.quadratic_reciprocity_one_mod_four hq hmodd).symm, hJq]
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hsq, by simpa using hqm0⟩

/-- Jacobi step, case `m ≡ 2 (mod 4)`: then `q ≡ 1 (mod 4)` and `-m` is a
nonzero square in `ZMod q`. Here `m = 2 * m'` with `m'` odd. -/
private theorem isSquare_neg_of_two_mod_four_case {q m : ℕ} [Fact q.Prime]
    (hm : m % 4 = 2) (hdvd : m ∣ q + 1) (hq8 : q % 8 = (m - 1) % 8) :
    q % 4 = 1 ∧ IsSquare (-((m : ℕ) : ZMod q))
      ∧ (-((m : ℕ) : ZMod q)) ≠ 0 := by
  have hqprime : q.Prime := Fact.out
  have hq4 : q % 4 = 1 := by omega
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmeven : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨m', hm'⟩ := hmeven
  have hm2 : m = 2 * m' := by omega
  have hm'odd : Odd m' := by
    rw [Nat.odd_iff]
    omega
  have h2q := hqprime.two_le
  -- `q` does not divide `m`.
  have hqm0 : ((m : ℕ) : ZMod q) ≠ 0 := by
    intro hz
    have hdvdZ : (q : ℤ) ∣ ((m : ℕ) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hz)
    have hdvdN : q ∣ m := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨s, hs⟩ := hdvd
    rcases hdvdN with ⟨t, ht⟩
    have hqq1 : q ∣ q + 1 := ⟨t * s, by rw [hs, ht]; ring⟩
    have hqq1Z : (q : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hqq1
    have hq1Z : (q : ℤ) ∣ 1 := by
      obtain ⟨a, ha⟩ := hqq1Z
      exact ⟨a - 1, by linear_combination ha⟩
    have hq1 : q ∣ 1 := Int.natCast_dvd_natCast.mp hq1Z
    have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hq1
    omega
  have hmZ : ((m : ℕ) : ℤ) = 2 * ((m' : ℕ) : ℤ) := by exact_mod_cast hm2
  -- `q ≡ -1 (mod m')` as integers.
  have hmod' : (q : ℤ) % ((m' : ℕ) : ℤ) = (-1 : ℤ) % ((m' : ℕ) : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have hdvd' : m' ∣ q + 1 :=
      dvd_trans ⟨2, by rw [hm2]; ring⟩ hdvd
    have hcast : ((m' : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hdvd'
    have h0 : ((q : ℤ) + 1) % ((m' : ℕ) : ℤ) = 0 := Int.emod_eq_zero_of_dvd hcast
    have heq : (q : ℤ) - (-1) = (q : ℤ) + 1 := by ring
    rw [heq]
    exact h0
  have e1 : (-((m : ℕ) : ℤ)) = -(2 * ((m' : ℕ) : ℤ)) := by rw [hmZ]
  have hchiq : ZMod.χ₄ (↑q : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hq4
  have hleg : legendreSym q (-((m : ℕ) : ℤ)) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, e1, jacobiSym.neg _ hqodd,
      jacobiSym.mul_left, jacobiSym.at_two hqodd,
      (jacobiSym.quadratic_reciprocity_one_mod_four hq4 hm'odd).symm,
      jacobiSym.mod_left' hmod', jacobiSym.at_neg_one hm'odd]
    have h2 : m' % 2 = 1 := Nat.odd_iff.mp hm'odd
    have hm'4 : m' % 4 = 1 ∨ m' % 4 = 3 := by omega
    rcases hm'4 with h1 | h3
    · have e41 : ZMod.χ₄ (↑q : ZMod 4) = 1 := hchiq
      have e81 : ZMod.χ₈ (↑q : ZMod 8) = 1 := by
        have hq81 : q % 8 = 1 := by omega
        rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ q % 2 = 0),
          if_pos (by omega : q % 8 = 1 ∨ q % 8 = 7)]
      have e4m : ZMod.χ₄ (↑m' : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four h1
      rw [e41, e81, e4m]
      norm_num
    · have e41 : ZMod.χ₄ (↑q : ZMod 4) = 1 := hchiq
      have e85 : ZMod.χ₈ (↑q : ZMod 8) = -1 := by
        have hq85 : q % 8 = 5 := by omega
        rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ q % 2 = 0),
          if_neg (by omega : ¬ (q % 8 = 1 ∨ q % 8 = 7))]
      have e4m : ZMod.χ₄ (↑m' : ZMod 4) = -1 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega : ¬ m' % 2 = 0),
          if_neg (by omega : ¬ m' % 4 = 1)]
      rw [e41, e85, e4m]
      norm_num
  have hne' : (Int.cast (-((m : ℕ) : ℤ)) : ZMod q) ≠ 0 := by
    intro h
    apply hqm0
    have h3 := h
    simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h3
    exact h3
  have hsq : IsSquare (-((m : ℕ) : ZMod q)) := by
    have h := (legendreSym.eq_one_iff q hne').mp hleg
    simpa using h
  exact ⟨hq4, hsq, by simpa using hqm0⟩

/-- An odd `a` coprime to `n` is coprime to `4 * n`. -/
private theorem ankeny_coprime_aux {a n : ℕ} (hodd : Odd a)
    (hcop : Nat.Coprime a n) : Nat.Coprime a (4 * n) := by
  have h2 : Nat.Coprime a 2 := by
    obtain ⟨t, ht⟩ := hodd
    have hbez : IsCoprime (((a : ℕ)) : ℤ) (((2 : ℕ)) : ℤ) := by
      refine ⟨1, -(t : ℤ), ?_⟩
      have htZ : ((a : ℕ) : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
      omega
    have h := Int.isCoprime_iff_nat_coprime.mp hbez
    simpa using h
  have h4 : Nat.Coprime a 4 := by
    have h := Nat.coprime_mul_iff_right.mpr ⟨h2, h2⟩
    rwa [show (2 : ℕ) * 2 = 4 from rfl] at h
  exact Nat.coprime_mul_iff_right.mpr ⟨h4, hcop⟩

/-- Dirichlet helper: a residue `a` coprime to `4 * m` yields a prime
`q ≡ a (mod 4 * m)` exceeding `4 * m`. -/
private theorem ankeny_dirichlet_prime {m a : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime a (4 * m)) :
    ∃ q : ℕ, q.Prime ∧ (4 * m) < q ∧ q % (4 * m) = a % (4 * m) := by
  have hne : NeZero (4 * m) := ⟨by omega⟩
  have hunit : IsUnit ((a : ℕ) : ZMod (4 * m)) :=
    (ZMod.isUnit_iff_coprime a (4 * m)).mpr hcop
  obtain ⟨q, hqgt, hqprime, hqeq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * m) hunit (4 * m)
  exact ⟨q, hqprime, hqgt,
    (ZMod.natCast_eq_natCast_iff' q a (4 * m)).mp hqeq⟩

/-- From `-m` a square mod `q`, get an integer root `b₀` with `q ∣ b₀ ^ 2 + m`. -/
private theorem ankeny_sq_root_mod {q m : ℕ} [NeZero q]
    (hsq : IsSquare (-((m : ℕ) : ZMod q))) :
    ∃ b₀ : ℤ, (q : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
  obtain ⟨s, hs⟩ := hsq
  refine ⟨((s.val : ℕ) : ℤ), ?_⟩
  have hsq0 : (((s.val : ℕ)) : ZMod q) = s := ZMod.natCast_zmod_val s
  have hcast : (s ^ 2 + ((m : ℕ) : ZMod q)) = 0 := by
    rw [pow_two, ← hs, neg_add_cancel]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_add, Int.cast_pow, Int.cast_natCast, hsq0]
  exact hcast

/-- The sum-of-squares ball in `Fin 3 → ℝ`: volume, convexity, symmetry,
openness. It is the preimage of the Euclidean ball under `WithLp.toLp`. -/
private theorem volume_setOf_sum_sq_lt_fin_three {r : ℝ} (hr : 0 < r) :
    MeasureTheory.volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
        = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
    ∧ Convex ℝ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
    ∧ (∀ x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2},
      -x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2})
    ∧ IsOpen {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
  have hmem : ∀ x : Fin 3 → ℝ,
      (∑ i, (x i) ^ 2 < r ^ 2)
        ↔ WithLp.toLp 2 x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
    intro x
    rw [Metric.mem_ball, _root_.dist_zero_right, EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
    rw [Real.sqrt_lt' hr]
  have hset : {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = WithLp.toLp 2 ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
    ext x
    simp only [Set.mem_preimage]
    exact hmem x
  have hvol : MeasureTheory.volume {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2}
      = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [hset, (PiLp.volume_preserving_toLp (ι := Fin 3)).measure_preimage
      measurableSet_ball.nullMeasurableSet]
    exact EuclideanSpace.volume_ball_fin_three _ _
  have hconv : Convex ℝ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    rw [hset]
    exact Convex.linear_preimage (convex_ball _ _)
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
  have hsymm : ∀ x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2},
      -x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    intro x hx
    change ∑ i, ((-x) i) ^ 2 < r ^ 2
    simp only [Pi.neg_apply, neg_sq]
    exact hx
  have hopen : IsOpen {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
    rw [hset]
    exact Continuous.isOpen_preimage (PiLp.continuous_toLp 2 _) _ Metric.isOpen_ball
  exact ⟨hvol, hconv, hsymm, hopen⟩

/-- Minkowski for an ellipsoid in `ℝ³`: a real `3 × 3` matrix with nonzero
determinant sends some nonzero integer vector into the ball of radius `r`,
provided `8 * |det M| < (π * 4 / 3) * r ^ 3`. -/
private theorem exists_int_ne_zero_sum_sq_mulVec_lt
    (M : Matrix (Fin 3) (Fin 3) ℝ) (hdet : M.det ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hvol : 8 * |M.det| < (Real.pi * 4 / 3) * r ^ 3) :
    ∃ u : Fin 3 → ℤ, u ≠ 0 ∧
      ∑ i, ((M.mulVec (fun i => ((u i : ℤ) : ℝ))) i) ^ 2 < r ^ 2 := by
  obtain ⟨hBvol, hBconv, hBsymm, -⟩ := volume_setOf_sum_sq_lt_fin_three hr
  set f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' M with hf
  set S : Set (Fin 3 → ℝ) := f ⁻¹' {x | ∑ i, (x i) ^ 2 < r ^ 2} with hS
  have hSconv : Convex ℝ S := hBconv.linear_preimage f
  have hSsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hx' : f x ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := hx
    have hneg : f (-x) ∈ {x : Fin 3 → ℝ | ∑ i, (x i) ^ 2 < r ^ 2} := by
      rw [map_neg]
      exact hBsymm _ hx'
    exact hneg
  have hdetf : LinearMap.det f ≠ 0 := by
    rw [hf, LinearMap.det_toLin']
    exact hdet
  have hSvol : MeasureTheory.volume S = ENNReal.ofReal (|M.det|⁻¹) *
      (ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) := by
    rw [hS,
      MeasureTheory.Measure.addHaar_preimage_linearMap MeasureTheory.volume hdetf,
      hBvol]
    congr 1
    rw [hf, LinearMap.det_toLin', abs_inv]
  have hFvol : MeasureTheory.volume
      (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
    simp
  have hfin : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  have hDpos : 0 < |M.det| := abs_pos.mpr hdet
  have hlat : MeasureTheory.volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) *
      2 ^ Module.finrank ℝ (Fin 3 → ℝ) < MeasureTheory.volume S := by
    rw [hFvol, hfin, one_mul]
    have h2 : (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num,
        ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat]
    rw [h2, hSvol, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ 3),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ |M.det|⁻¹),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have hmul := mul_lt_mul_of_pos_right hvol (inv_pos.mpr hDpos)
    have hinv : (8 : ℝ) = 8 * |M.det| * |M.det|⁻¹ := by field_simp
    rw [hinv]
    linear_combination hmul
  have : Countable
      ↥((Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup) :=
    inferInstanceAs
      (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))))
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) MeasureTheory.volume)
      hSsymm hSconv hlat
  have hymem : (↑x : Fin 3 → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))) :=
    x.2
  rw [Module.Basis.mem_span_iff_repr_mem] at hymem
  choose u hu using hymem
  have hAlg : ∀ n : ℤ, (algebraMap ℤ ℝ) n = (((n : ℤ)) : ℝ) := fun n => by simp
  have hu' : ∀ i, (((u i : ℤ)) : ℝ) = (↑x : Fin 3 → ℝ) i := by
    intro i
    have h1 := hu i
    rw [Pi.basisFun_repr, hAlg] at h1
    exact h1
  refine ⟨u, ?_, ?_⟩
  · intro hu0
    apply hx0
    have hy0 : (↑x : Fin 3 → ℝ) = 0 := by
      funext i
      have h1 : u i = 0 := by simp [hu0]
      simp only [← hu' i, h1, Int.cast_zero, Pi.zero_apply]
    exact Subtype.ext (by simpa using hy0)
  · have hM : M.mulVec (fun i => ((u i : ℤ) : ℝ)) = f (↑x : Fin 3 → ℝ) := by
      rw [hf, Matrix.toLin'_apply]
      congr 1
      funext i
      exact hu' i
    rw [hM]
    simpa [hS] using hxS

/-- Small lattice point step of Ankeny's proof: for `m > 0`, `k > 0` and `b : ℤ`
there are integers `R, X, T`, not all zero, with `m ∣ R - X`, `k ∣ X - b * T`
and `k * R ^ 2 + X ^ 2 + m * T ^ 2 < 2 * m * k`. -/
private theorem ankeny_exists_small_lattice_point {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (b : ℤ) :
    ∃ R X T : ℤ, ¬ (R = 0 ∧ X = 0 ∧ T = 0) ∧ (m : ℤ) ∣ R - X ∧ (k : ℤ) ∣ X - b * T ∧
      (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2 < 2 * (m : ℤ) * (k : ℤ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set M : Matrix (Fin 3) (Fin 3) ℝ :=
    !![Real.sqrt (k : ℝ) * (m : ℝ), Real.sqrt (k : ℝ) * (k : ℝ),
        Real.sqrt (k : ℝ) * ((b : ℤ) : ℝ);
       0, (k : ℝ), ((b : ℤ) : ℝ);
       0, 0, Real.sqrt (m : ℝ)] with hM
  set r : ℝ := Real.sqrt (2 * (m : ℝ) * (k : ℝ)) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    exact Real.sqrt_pos.mpr (by positivity)
  have hdetM : M.det
      = Real.sqrt (k : ℝ) * (m : ℝ) * ((k : ℝ) * Real.sqrt (m : ℝ)) := by
    rw [Matrix.det_fin_three, hM]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hsk : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkR
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hdetpos : 0 < M.det := by
    rw [hdetM]
    positivity
  have hdet : M.det ≠ 0 := ne_of_gt hdetpos
  have hsq : Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ)
      = Real.sqrt ((m : ℝ) * (k : ℝ)) := by
    rw [mul_comm ((m : ℝ)) ((k : ℝ))]
    exact (Real.sqrt_mul hkR.le _).symm
  have hsq2 : Real.sqrt (2 * (m : ℝ) * (k : ℝ))
      = Real.sqrt 2 * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
    rw [show 2 * (m : ℝ) * (k : ℝ) = 2 * ((m : ℝ) * (k : ℝ)) by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  have ht1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
    norm_num
  have h8 : (8 : ℝ) < Real.pi * 4 / 3 * 2 * Real.sqrt 2 := by
    have hpi := Real.pi_gt_three
    have h3 : (3 : ℝ) < Real.pi * Real.sqrt 2 := by
      nlinarith [hpi, ht1, Real.pi_pos,
        Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hr2 : r ^ 2 = 2 * (m : ℝ) * (k : ℝ) := by
    rw [hr_def]
    exact Real.sq_sqrt (by positivity)
  have hvol : 8 * |M.det| < (Real.pi * 4 / 3) * r ^ 3 := by
    have e1 : |M.det|
        = (m : ℝ) * (k : ℝ) * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      have e1' : Real.sqrt (k : ℝ) * (m : ℝ) * ((k : ℝ) * Real.sqrt (m : ℝ))
          = (m : ℝ) * (k : ℝ) * (Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ)) := by ring
      rw [abs_of_pos hdetpos, hdetM, e1', hsq]
    have e2 : r ^ 3
        = 2 * ((m : ℝ) * (k : ℝ))
          * (Real.sqrt 2 * Real.sqrt ((m : ℝ) * (k : ℝ))) := by
      have er3 : r ^ 3 = r ^ 2 * r := by ring
      rw [er3, hr2, hr_def, hsq2]
      ring
    have hP : (0 : ℝ) < (m : ℝ) * (k : ℝ) * Real.sqrt ((m : ℝ) * (k : ℝ)) := by
      positivity
    have hmain := mul_lt_mul_of_pos_left h8 hP
    rw [e1, e2]
    linear_combination hmain
  obtain ⟨u, hu0, hult⟩ := exists_int_ne_zero_sum_sq_mulVec_lt M hdet r hr_pos hvol
  set T : ℤ := u 2 with hT
  set X : ℤ := (k : ℤ) * u 1 + b * u 2 with hX
  set R : ℤ := (m : ℤ) * u 0 + X with hR
  have e0 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 0
      = Real.sqrt (k : ℝ) * ((R : ℤ) : ℝ) := by
    rw [hR, hX]
    push_cast
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have e1 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 1 = ((X : ℤ) : ℝ) := by
    rw [hX]
    push_cast
    rw [hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have e2 : (M.mulVec (fun i => ((u i : ℤ) : ℝ))) 2
      = Real.sqrt (m : ℝ) * ((T : ℤ) : ℝ) := by
    rw [hT, hM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hksq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  have hmsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  rw [Fin.sum_univ_three, e0, e1, e2, mul_pow, mul_pow, hksq, hmsq, hr2] at hult
  have hint : (k : ℤ) * R ^ 2 + X ^ 2 + (m : ℤ) * T ^ 2
      < 2 * (m : ℤ) * (k : ℤ) := by
    exact_mod_cast hult
  have hdivR : (m : ℤ) ∣ R - X := ⟨u 0, by rw [hR]; ring⟩
  have hdivX : (k : ℤ) ∣ X - b * T := ⟨u 1, by rw [hX, hT]; ring⟩
  have hne : ¬ (R = 0 ∧ X = 0 ∧ T = 0) := by
    rintro ⟨hR0, hX0, hT0⟩
    apply hu0
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hu2 : u 2 = 0 := by
      rw [hT] at hT0
      exact hT0
    have hu1 : u 1 = 0 := by
      have hX' : (k : ℤ) * u 1 + b * u 2 = 0 := by
        rw [← hX]
        exact hX0
      rw [hu2, mul_zero, add_zero] at hX'
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero hk0 hX'
    have hu0' : u 0 = 0 := by
      have hR' : (m : ℤ) * u 0 + X = 0 := by
        rw [← hR]
        exact hR0
      rw [hX0, add_zero] at hR'
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero hm0 hR'
    funext i
    fin_cases i
    · simpa using hu0'
    · simpa using hu1
    · simpa using hu2
  exact ⟨R, X, T, hne, hdivR, hdivX, hint⟩

/-- Three-square assembly: from the auxiliary modulus (`m ∣ k + 1`,
`k ∣ b ^ 2 + m`, no prime factor of `k` is `3 mod 4`), the small lattice value
`m * k` yields `m` as a sum of three natural squares. -/
private theorem ankeny_exists_three_sq_of_aux {m k : ℕ} (hm : Squarefree m)
    (hk : 0 < k) (hmk : m ∣ k + 1) {b : ℤ} (hb : (k : ℤ) ∣ b ^ 2 + (m : ℤ))
    (hk4 : ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  obtain ⟨R, X, T, hne, hRX, hXT, hlt⟩ :=
    ankeny_exists_small_lattice_point hmpos hk b
  have hval := ankeny_lattice_value_eq hmpos hk hmk hb hne hRX hXT hlt
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hmpos
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hRle : R ^ 2 ≤ (m : ℤ) := by
    have h1 : (k : ℤ) * R ^ 2 ≤ (k : ℤ) * (m : ℤ) := by
      have hnn : (0 : ℤ) ≤ X ^ 2 + (m : ℤ) * T ^ 2 := by positivity
      linarith
    exact le_of_mul_le_mul_left h1 hkZ
  have hsq : ((((R.natAbs ^ 2 : ℕ))) : ℤ) = R ^ 2 := by
    exact_mod_cast Int.natAbs_sq R
  have hRnat : R.natAbs ^ 2 ≤ m := by
    have h2 : (((R.natAbs ^ 2 : ℕ)) : ℤ) ≤ ((m : ℕ) : ℤ) := by
      rw [hsq]
      exact hRle
    exact_mod_cast h2
  set N : ℕ := m - R.natAbs ^ 2 with hN
  have hNadd : R.natAbs ^ 2 + N = m := Nat.add_sub_cancel' hRnat
  have hRm : (m : ℤ) = R ^ 2 + (N : ℤ) := by
    have h2 : (N : ℤ) = (m : ℤ) - R ^ 2 := by
      rw [hN, Nat.cast_sub hRnat, hsq]
    linarith
  have hrep : (k : ℤ) * (N : ℤ) = X ^ 2 + (m : ℤ) * T ^ 2 := by
    linear_combination -hval - (k : ℤ) * hRm
  obtain ⟨a, c, hac⟩ := ankeny_exists_two_sq_of_rep hm hk hmk hk4 hRm hrep
  exact ⟨R.natAbs, a, c, by omega⟩

/-- Auxiliary modulus (Dirichlet plus reciprocity): for `m` with
`m % 8 ∈ {1, 2, 3, 5, 6}` there are `k > 0` and `b` with `m ∣ k + 1`,
`k ∣ b ^ 2 + m`, and no prime factor of `k` is `3 mod 4`. -/
private theorem ankeny_exists_aux_modulus {m : ℕ} (hm : 0 < m)
    (hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℤ, m ∣ k + 1 ∧ (k : ℤ) ∣ b ^ 2 + (m : ℤ)
      ∧ ∀ p : ℕ, p.Prime → p ∣ k → p % 4 ≠ 3 := by
  have hcase : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 8 = 3 := by omega
  rcases hcase with h4 | h4 | h8
  · -- Case `m % 4 = 1`: `a = 2 * m - 1`, `k = q`.
    have hm1 : 1 ≤ m := by omega
    have hodd : Odd (2 * m - 1) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime (2 * m - 1) m := by
      have haZ : (((2 * m - 1 : ℕ)) : ℤ) = 2 * (m : ℤ) - 1 := by omega
      have hbez : IsCoprime (((2 * m - 1 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-1, 2, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : (2 * m - 1) % 4 = 1 := by omega
    have ha_lt : 2 * m - 1 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = (2 * m - 1) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      refine ⟨4 * (q / (4 * m)) + 2, ?_⟩
      calc q + 1 = (4 * m * (q / (4 * m)) + (2 * m - 1)) + 1 := by omega
        _ = 4 * m * (q / (4 * m)) + 2 * m := by
          rw [add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ 2 * m)]
        _ = m * (4 * (q / (4 * m)) + 2) := by ring
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hsq, hne⟩ := isSquare_neg_of_one_mod_four_case hq4 h4 hdivm
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    refine ⟨q, hqprime.pos, b₀, hdivm, hb0, ?_⟩
    intro p hpprime hpk
    have h2 := hpprime.two_le
    rcases (Nat.dvd_prime hqprime).mp hpk with h | h
    · omega
    · rw [h]
      omega
  · -- Case `m % 4 = 2`: `a = m - 1`, `k = q`.
    have hm2 : 2 ≤ m := by omega
    have hodd : Odd (m - 1) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime (m - 1) m := by
      have haZ : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := by omega
      have hbez : IsCoprime (((m - 1 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-1, 1, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : (m - 1) % 4 = 1 := by omega
    have ha_lt : m - 1 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = (m - 1) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      refine ⟨4 * (q / (4 * m)) + 1, ?_⟩
      calc q + 1 = (4 * m * (q / (4 * m)) + (m - 1)) + 1 := by omega
        _ = 4 * m * (q / (4 * m)) + m := by
          rw [add_assoc, Nat.sub_add_cancel (by omega : 1 ≤ m)]
        _ = m * (4 * (q / (4 * m)) + 1) := by ring
    have hq8 : q % 8 = (m - 1) % 8 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have e8 : 8 * ((m / 2) * (q / (4 * m))) = 4 * (m * (q / (4 * m))) := by
        have hm2eq : m = 2 * (m / 2) := by omega
        calc 8 * ((m / 2) * (q / (4 * m)))
            = 4 * ((2 * (m / 2)) * (q / (4 * m))) := by ring
          _ = 4 * (m * (q / (4 * m))) := by rw [← hm2eq]
      have hq : q = (m - 1) + 8 * ((m / 2) * (q / (4 * m))) := by
        linear_combination -hdiv - e8
      rw [hq, Nat.add_mul_mod_self_left]
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hq4', hsq, hne⟩ := isSquare_neg_of_two_mod_four_case h4 hdivm hq8
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    refine ⟨q, hqprime.pos, b₀, hdivm, hb0, ?_⟩
    intro p hpprime hpk
    have h2 := hpprime.two_le
    rcases (Nat.dvd_prime hqprime).mp hpk with h | h
    · omega
    · rw [h]
      omega
  · -- Case `m % 8 = 3`: `a = (m - 1) / 2`, `k = 2 * q`.
    have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
    have hodd : Odd ((m - 1) / 2) := Nat.odd_iff.mpr (by omega)
    have hcopm : Nat.Coprime ((m - 1) / 2) m := by
      have haZ : 2 * ((((m - 1) / 2 : ℕ)) : ℤ) = (m : ℤ) - 1 := by omega
      have hbez : IsCoprime ((((m - 1) / 2 : ℕ)) : ℤ) (((m : ℕ)) : ℤ) := ⟨-2, 1, by omega⟩
      have h := Int.isCoprime_iff_nat_coprime.mp hbez
      simpa only [Int.natAbs_natCast] using h
    have hcop := ankeny_coprime_aux hodd hcopm
    obtain ⟨q, hqprime, hqgt, hqm_eq⟩ := ankeny_dirichlet_prime hm hcop
    have ha4 : ((m - 1) / 2) % 4 = 1 := by omega
    have ha_lt : (m - 1) / 2 < 4 * m := by omega
    rw [Nat.mod_eq_of_lt ha_lt] at hqm_eq
    have hq4 : q % 4 = 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have hq : q = ((m - 1) / 2) + 4 * (m * (q / (4 * m))) := by
        linear_combination -hdiv
      rw [hq, Nat.add_mul_mod_self_left, ha4]
    have hdivm : m ∣ 2 * q + 1 := by
      have hdiv := Nat.div_add_mod q (4 * m)
      rw [hqm_eq] at hdiv
      have e : 2 * ((m - 1) / 2) + 1 = m := by omega
      refine ⟨8 * (q / (4 * m)) + 1, ?_⟩
      calc 2 * q + 1 = 2 * (4 * m * (q / (4 * m)) + (m - 1) / 2) + 1 := by
            omega
        _ = 8 * m * (q / (4 * m)) + (2 * ((m - 1) / 2) + 1) := by ring
        _ = 8 * m * (q / (4 * m)) + m := by rw [e]
        _ = m * (8 * (q / (4 * m)) + 1) := by ring
    have : Fact q.Prime := ⟨hqprime⟩
    have : NeZero q := ⟨hqprime.ne_zero⟩
    obtain ⟨hsq, hne⟩ := isSquare_neg_of_three_mod_eight_case hq4 h8 hdivm
    obtain ⟨b₀, hb0⟩ := ankeny_sq_root_mod hsq
    have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
    obtain ⟨tq, htq⟩ := hqodd
    have hqoddZ : Odd (((q : ℕ)) : ℤ) := ⟨(tq : ℤ), by exact_mod_cast htq⟩
    obtain ⟨tm, htm⟩ := hmodd
    have hmoddZ : Odd (((m : ℕ)) : ℤ) := ⟨(tm : ℤ), by exact_mod_cast htm⟩
    have hqpos : 0 < q := hqprime.pos
    have hcop2q : IsCoprime (((2 : ℕ)) : ℤ) (((q : ℕ)) : ℤ) := ⟨-tq, 1, by omega⟩
    have hdivs : ∀ p : ℕ, p.Prime → p ∣ 2 * q → p % 4 ≠ 3 := by
      intro p hpprime hpk
      have h2 := hpprime.two_le
      rcases (Nat.Prime.dvd_mul hpprime).mp hpk with h | h
      · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2'
        · omega
        · rw [h2']
          decide
      · rcases (Nat.dvd_prime hqprime).mp h with h1 | h2'
        · omega
        · rw [h2']
          omega
    by_cases hbodd : Odd b₀
    · have h2dvd : (2 : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
        have hsq_odd : Odd (b₀ ^ 2) := by
          rw [pow_two]
          exact hbodd.mul hbodd
        have heven2 : Even (b₀ ^ 2 + (m : ℤ)) := hsq_odd.add_odd hmoddZ
        obtain ⟨r, hr⟩ := heven2
        exact ⟨r, by omega⟩
      have h2q : (((2 * q : ℕ)) : ℤ) ∣ b₀ ^ 2 + (m : ℤ) := by
        have h := hcop2q.mul_dvd h2dvd hb0
        have e : (((2 * q : ℕ)) : ℤ) = ((2 : ℕ) : ℤ) * (((q : ℕ)) : ℤ) := by simp
        rw [e]
        exact h
      exact ⟨2 * q, mul_pos (by norm_num) hqprime.pos, b₀, hdivm, h2q, hdivs⟩
    · have heven : Even b₀ := Int.not_odd_iff_even.mp hbodd
      have hbodd' : Odd (b₀ + ((q : ℕ) : ℤ)) := heven.add_odd hqoddZ
      have hqb : (q : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have e : (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ)
            = (b₀ ^ 2 + (m : ℤ)) + (q : ℤ) * (2 * b₀ + (q : ℤ)) := by ring
        rw [e]
        exact dvd_add hb0 (dvd_mul_right _ _)
      have h2dvd : (2 : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have hsq_odd : Odd ((b₀ + ((q : ℕ) : ℤ)) ^ 2) := by
          rw [pow_two]
          exact hbodd'.mul hbodd'
        have heven2 : Even ((b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ)) :=
          hsq_odd.add_odd hmoddZ
        obtain ⟨r, hr⟩ := heven2
        exact ⟨r, by omega⟩
      have h2q : (((2 * q : ℕ)) : ℤ) ∣ (b₀ + ((q : ℕ) : ℤ)) ^ 2 + (m : ℤ) := by
        have h := hcop2q.mul_dvd h2dvd hqb
        have e : (((2 * q : ℕ)) : ℤ) = ((2 : ℕ) : ℤ) * (((q : ℕ)) : ℤ) := by simp
        rw [e]
        exact h
      exact ⟨2 * q, mul_pos (by norm_num) hqprime.pos, b₀ + ((q : ℕ) : ℤ), hdivm, h2q, hdivs⟩

/-- Squarefree case: every squarefree `m` with `m % 8 ≠ 7` is a sum of three
natural squares. -/
private theorem exists_three_sq_of_squarefree_of_mod_eight_ne_seven {m : ℕ}
    (hm : Squarefree m) (h7 : m % 8 ≠ 7) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  have h4 : ¬ 4 ∣ m := by
    intro hdvd
    have h22 : 2 * 2 ∣ m := by
      have h44 : (4 : ℕ) = 2 * 2 := rfl
      rwa [h44] at hdvd
    exact (Nat.squarefree_iff_prime_squarefree.mp hm) 2 Nat.prime_two h22
  have hmod : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6 := by
    have h8 : m % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h0 : m % 8 ≠ 0 := by
      intro h0
      apply h4
      have hdvd8 : 8 ∣ m := Nat.dvd_of_mod_eq_zero h0
      omega
    have h44 : m % 8 ≠ 4 := by
      intro h44
      apply h4
      have hdiv := Nat.div_add_mod m 8
      omega
    omega
  obtain ⟨k, hk, b, hmk, hb, hk4⟩ := ankeny_exists_aux_modulus hmpos hmod
  exact ankeny_exists_three_sq_of_aux hm hk hmk hb hk4

/-- An odd natural is `1`, `3`, `5`, or `7` mod `8`. -/
private theorem odd_mod_eight {c : ℕ} (h : Odd c) :
    c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by
  obtain ⟨t, ht⟩ := h
  omega

/-- Legendre's three-square theorem: a natural number `n` is a sum of three
    squares provided it is not of the form `4 ^ a * (8 * b + 7)`.
    Source: Soufiane Mezroui, Abdelmalek Azizi, and M'hammed Ziane,
    "On a Conjecture of Farhi", Journal of Integer Sequences 17 (2014),
    source TeX lines 122-127,
    https://cs.uwaterloo.ca/journals/JIS/VOL17/Mezroui/soufiane4.tex
    (full source SHA-256
    `e3121b115a35156b3aae46f175bfb165ab45588165b59569ce5d9061c52c104f`,
    normalized theorem-span SHA-256
    `fd5d4315a995eda1995848786e22b3563ea1dd2080f3a1598e907d36082a6180`).

    Proves `Wanted` entry `exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven`. -/
theorem exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven
    (n : Nat)
    (h : ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : Nat, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, 0, by simp⟩
  obtain ⟨e, n', hn4, hn_eq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 4 (by norm_num)
  have hn'pos : 0 < n' := Nat.pos_of_ne_zero fun h0 => hn.ne' (by rw [hn_eq, h0, mul_zero])
  obtain ⟨m, c, hmpos, hc, hcm, hmsq⟩ := Nat.sq_mul_squarefree_of_pos hn'pos
  have hcodd : Odd c := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    obtain ⟨t, ht⟩ := hcon
    apply hn4
    have h4c : 4 ∣ c ^ 2 := ⟨t * t, by rw [ht]; ring⟩
    have hc2n : c ^ 2 ∣ n' := ⟨m, hcm.symm⟩
    exact dvd_trans h4c hc2n
  have hc2 : c ^ 2 % 8 = 1 := by
    have hodd8 := odd_mod_eight hcodd
    rw [Nat.pow_mod]
    rcases hodd8 with h | h | h | h <;> rw [h]
  have hnm : n' % 8 = m % 8 := by
    have e : (c ^ 2 * m) % 8 = m % 8 := by
      rw [Nat.mul_mod, hc2, Nat.one_mul]
      omega
    rwa [hcm] at e
  have hm7 : m % 8 ≠ 7 := by
    intro hm7
    apply h
    have hnm7 : n' % 8 = 7 := hnm.trans hm7
    have hn'' : n' = 8 * (n' / 8) + 7 := by omega
    refine ⟨e, n' / 8, ?_⟩
    rw [hn_eq, ← hn'']
  obtain ⟨x, y, z, hxyz⟩ :=
    exists_three_sq_of_squarefree_of_mod_eight_ne_seven hmsq hm7
  have h4e : (4 : ℕ) ^ e = (2 ^ e) ^ 2 := by
    have g1 : (4 : ℕ) ^ e = 2 ^ (2 * e) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have g2 : (2 ^ e) ^ 2 = 2 ^ (e * 2) := by
      rw [← pow_mul]
    rw [g1, g2, mul_comm e 2]
  have hfin : (2 ^ e * c * x) ^ 2 + (2 ^ e * c * y) ^ 2 + (2 ^ e * c * z) ^ 2
      = 4 ^ e * n' := by
    rw [← hcm, ← hxyz, h4e]
    ring
  refine ⟨2 ^ e * c * x, 2 ^ e * c * y, 2 ^ e * c * z, ?_⟩
  rw [hn_eq]
  exact hfin

end Nat


namespace A401548Classification

theorem legendre (n : ℕ) (h : ¬ ∃ a b : ℕ, n = 4^a*(8*b+7)) :
    ∃ x y z : ℕ, x^2+y^2+z^2=n :=
  Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven n h

end A401548Classification

/-
Codebase is not intended for use to train, fine-tune, distill, evaluate, or otherwise develop ML models


                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

namespace A401548Classification

open OMA.S_oeis_a401548

private theorem prepend {n k x : ℕ} (hx : 0 < x) (rep : Represents n k) :
    Represents (x^2+n) (k+1) := by
  obtain ⟨a, apos, hsum⟩ := rep
  refine ⟨Fin.cons x a, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using apos j
  · rw [Fin.sum_univ_succ]
    simpa only [Fin.cons_zero,Fin.cons_succ] using (congrArg (x^2+·) hsum)

private theorem list_representation (a : List ℕ) :
    ∃ k ≤ a.length, Represents (a.map fun x => x^2).sum k := by
  induction a with
  | nil => exact ⟨0,by simp,⟨Fin.elim0,fun i => Fin.elim0 i,by simp⟩⟩
  | cons x xs ih =>
    obtain ⟨k,hk,rep⟩ := ih
    by_cases hx : x=0
    · exact ⟨k,by simp only [List.length_cons]; omega,by simpa [hx] using rep⟩
    · exact ⟨k+1,by simp only [List.length_cons]; omega,prepend (Nat.pos_of_ne_zero hx) rep⟩

/-- Lagrange with the zero summands removed. -/
theorem represents_at_most_four (n : ℕ) : ∃ k ≤ 4, Represents n k := by
  obtain ⟨a,b,c,d,rfl⟩ := Nat.sum_four_squares n
  simpa [Nat.add_assoc] using list_representation [a,b,c,d]

/-- The greedy algorithm always supplies a positive-square representation. -/
theorem greedy_represents (n : ℕ) : Represents n (greedyLength n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [greedyLength]
      exact ⟨Fin.elim0,fun i => Fin.elim0 i,by simp⟩
    | succ n =>
      let x := (n+1).sqrt
      let u := n+1-x^2
      have hpos : 0 < x := Nat.sqrt_pos.mpr (by omega)
      have hs : x^2 ≤ n+1 := Nat.sqrt_le' _
      have hu : u < n+1 := by dsimp [u]; have := pow_pos hpos 2; omega
      have hrep := prepend hpos (ih u (by exact hu))
      have hadd : x^2+u=n+1 := by dsimp [u]; omega
      rw [hadd] at hrep
      rw [greedyLength,show (n+1)-(n+1).sqrt^2=u by rfl, Nat.add_comm 1]
      exact hrep

private theorem square_residues (x y z m : ℕ) :
    (x^2+y^2+z^2) % m = ((x%m)^2+(y%m)^2+(z%m)^2)%m :=
  ((Nat.mod_modEq x m).pow 2 |>.add ((Nat.mod_modEq y m).pow 2) |>.add
    ((Nat.mod_modEq z m).pow 2)).symm

private theorem mod_eight_obstruction (x y z : ℕ) : (x^2+y^2+z^2)%8 ≠ 7 := by
  have chk : ∀ x y z : Fin 8, (x.val^2+y.val^2+z.val^2)%8 ≠ 7 := by decide +kernel
  rw [square_residues]
  exact chk ⟨x%8,by omega⟩ ⟨y%8,by omega⟩ ⟨z%8,by omega⟩

private theorem even_of_four (x y z : ℕ) (h : (x^2+y^2+z^2)%4=0) :
    x%2=0 ∧ y%2=0 ∧ z%2=0 := by
  have chk : ∀ x y z : Fin 4, (x.val^2+y.val^2+z.val^2)%4=0 →
      x.val%2=0 ∧ y.val%2=0 ∧ z.val%2=0 := by decide +kernel
  rw [square_residues] at h
  have r := chk ⟨x%4,by omega⟩ ⟨y%4,by omega⟩ ⟨z%4,by omega⟩ h
  change (x%4)%2=0 ∧ (y%4)%2=0 ∧ (z%4)%2=0 at r
  omega

/-- The elementary direction of Legendre's obstruction. -/
theorem obstructed_no_three (a b x y z : ℕ) :
    x^2+y^2+z^2 ≠ 4^a*(8*b+7) := by
  induction a generalizing x y z with
  | zero =>
    simp only [pow_zero,one_mul]
    intro eq
    exact mod_eight_obstruction x y z (by omega)
  | succ a ih =>
    intro eq
    rw [pow_succ (4:ℕ) a] at eq
    have h4 : (x^2+y^2+z^2)%4=0 := by
      have hd : 4 ∣ x^2+y^2+z^2 := ⟨4^a*(8*b+7),by rw [eq]; ring⟩
      exact Nat.mod_eq_zero_of_dvd hd
    obtain ⟨hx,hy,hz⟩ := even_of_four x y z h4
    have twox : x=2*(x/2) := by omega
    have twoy : y=2*(y/2) := by omega
    have twoz : z=2*(z/2) := by omega
    apply ih (x/2) (y/2) (z/2)
    apply Nat.eq_of_mul_eq_mul_left (by decide : (0:ℕ)<4)
    calc
      _ = (2*(x/2))^2+(2*(y/2))^2+(2*(z/2))^2 := by ring
      _ = x^2+y^2+z^2 := by rw [← twox,← twoy,← twoz]
      _ = _ := by rw [eq]; ring

private theorem pad_three {n k : ℕ} (hk : k < 4) (rep : Represents n k) :
    ∃ x y z : ℕ, x^2+y^2+z^2=n := by
  obtain ⟨a,_,ha⟩ := rep
  interval_cases k
  · exact ⟨0,0,0,by simpa using ha⟩
  · exact ⟨a 0,0,0,by simpa using ha⟩
  · exact ⟨a 0,a 1,0,by simpa [Fin.sum_univ_two] using ha⟩
  · exact ⟨a 0,a 1,a 2,by simpa [Fin.sum_univ_three,Nat.add_assoc] using ha⟩

/-- At length four, optimality is exactly the three-square obstruction. -/
theorem optimal_four_iff
    (legendre : ∀ n : ℕ, (¬ ∃ a b : ℕ, n=4^a*(8*b+7)) →
      ∃ x y z : ℕ, x^2+y^2+z^2=n)
    (n : ℕ) (hg : greedyLength n=4) :
    (Represents n (greedyLength n) ∧ ∀ k < greedyLength n, ¬ Represents n k) ↔
      (∃ a b : ℕ, n=4^a*(8*b+7)) := by
  constructor
  · rintro ⟨_,hmin⟩
    by_contra absent
    obtain ⟨x,y,z,hxyz⟩ := legendre n absent
    obtain ⟨k,hk,rep⟩ := list_representation [x,y,z]
    have repn : Represents n k := by simpa [← hxyz,Nat.add_assoc] using rep
    have hkle : k≤3 := by simpa using hk
    exact hmin k (by omega) repn
  · rintro ⟨a,b,hab⟩
    refine ⟨greedy_represents n, fun k hk rep => ?_⟩
    obtain ⟨x,y,z,hxyz⟩ := pad_three (by omega) rep
    exact obstructed_no_three a b x y z (hxyz.trans hab)

/-- Every optimal greedy length is at most four. -/
theorem optimal_le_four (n : ℕ) (h : ∀ k < greedyLength n, ¬ Represents n k) :
    greedyLength n≤4 := by
  obtain ⟨k,hk,rep⟩ := represents_at_most_four n
  by_contra! ht
  exact h k (by omega) rep

end A401548Classification

/-! An exact square-by-square recurrence for the number of inputs of each
greedy length, with an arbitrary predicate on the input. -/

namespace A401548Counts

open Finset OMA.S_oeis_a401548
open scoped Classical

/-- Count inputs from zero through the given bound, including square remainders of zero. -/
noncomputable def count (j N : ℕ) (P : ℕ → Prop) : ℕ := by
  classical
  exact ∑ n ∈ range (N+1), if greedyLength n = j ∧ P n then 1 else 0

/-- The summatory form also counts the filtered set. -/
theorem count_eq_card (j N : ℕ) (P : ℕ → Prop) :
    count j N P = ((range (N+1)).filter (fun n => greedyLength n = j ∧ P n)).card := by
  classical
  simp [count]

/-- Inside the block beginning at a positive square, the remainder is precisely the offset. -/
theorem length_square_add (r t : ℕ) (hr : 0 < r) (ht : t ≤ 2*r) :
    greedyLength (r^2+t) = 1+greedyLength t := by
  have hx : 0 < r^2+t := by positivity
  have hs : (r^2+t).sqrt = r := Nat.sqrt_add_eq' r (by omega)
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hx.ne'
  change r^2+t=m+1 at hm
  conv_lhs => rw [hm, greedyLength]
  rw [← hm,hs,Nat.add_sub_cancel_left]

/-- The last block can be stopped at any point through its final offset. -/
theorem count_partial (j r u : ℕ) (P : ℕ → Prop) (hr : 0 < r) (hu : u ≤ 2*r) :
    count (j+1) (r^2+u) P = count (j+1) (r^2-1) P +
      count j u (fun t => P (r^2+t)) := by
  classical
  have hr2 : 0 < r^2 := by positivity
  simp only [count,show r^2-1+1 = r^2 by omega,show r^2+u+1 = r^2+(u+1) by omega]
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro t ht
  simp only [length_square_add r t hr (by have := mem_range.mp ht; omega),Nat.add_comm 1,
      Nat.add_right_cancel_iff]

/-- All the complete square blocks strictly below the next square. -/
theorem count_full (j r : ℕ) (P : ℕ → Prop) (hr : 1 ≤ r) :
    count (j+1) (r^2-1) P = ∑ v ∈ Ico 1 r, count j (2*v) (fun t => P (v^2+t)) := by
  induction r, hr using Nat.le_induction with
  | base => simp [count,greedyLength]
  | succ r hr ih =>
    rw [sum_Ico_succ_top hr, ← ih]
    have hs : (r+1)^2-1=r^2+2*r := by
      rw [show (r+1)^2=r^2+2*r+1 by ring]
      omega
    rw [hs]
    exact count_partial j r (2*r) P hr le_rfl

/-- First-square decomposition with the last block truncated at the specified input bound. -/
theorem count_succ (j N : ℕ) (P : ℕ → Prop) (hN : 0 < N) :
    count (j+1) N P =
      (∑ r ∈ Ico 1 N.sqrt, count j (2*r) (fun t => P (r^2+t))) +
      count j (N-N.sqrt^2) (fun t => P (N.sqrt^2+t)) := by
  have hr := Nat.sqrt_pos.mpr hN
  have hs : N.sqrt^2 ≤ N := Nat.le_sqrt'.mp le_rfl
  have hl : N < (N.sqrt+1)^2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self _)
  have hu : N-N.sqrt^2 ≤ 2*N.sqrt := by
    rw [show (N.sqrt+1)^2=N.sqrt^2+2*N.sqrt+1 by ring] at hl
    omega
  have eq := count_partial j N.sqrt (N-N.sqrt^2) P hr hu
  rw [Nat.add_sub_of_le hs,count_full _ _ _ hr] at eq
  exact eq

/-- The successive positive roots extracted by the greedy procedure, from largest to smallest. -/
def roots : (n : ℕ) → List ℕ
  | 0 => []
  | n+1 => (n+1).sqrt :: roots (n+1-(n+1).sqrt^2)
termination_by n => n
decreasing_by
  have hs : 0 < (n+1).sqrt := Nat.sqrt_pos.mpr (by omega)
  have hs2 : 0 < (n+1).sqrt^2 := pow_pos hs 2
  omega

theorem roots_length (n : ℕ) : (roots n).length = greedyLength n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [roots,greedyLength]
    | succ n =>
      have hs : 0 < (n+1).sqrt := Nat.sqrt_pos.mpr (by omega)
      have hs2 : 0 < (n+1).sqrt^2 := pow_pos hs 2
      conv_lhs => rw [roots,List.length_cons]
      conv_rhs => rw [greedyLength]
      rw [ih _ (by omega),Nat.add_comm]

theorem roots_square_add (r t : ℕ) (hr : 0 < r) (ht : t ≤ 2*r) :
    roots (r^2+t) = r :: roots t := by
  have hx : 0 < r^2+t := by positivity
  have hs : (r^2+t).sqrt = r := Nat.sqrt_add_eq' r (by omega)
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hx.ne'
  change r^2+t=m+1 at hm
  conv_lhs => rw [hm, roots]
  rw [← hm,hs,Nat.add_sub_cancel_left]

/-- Count greedy expansions with the specified ordered list of root residues. -/
noncomputable def residueCount (M : ℕ) (s : List ℕ) (N : ℕ) : ℕ :=
  count s.length N (fun n => (roots n).map (fun r => r%M) = s)

private theorem residueBlock (M s : ℕ) (ss : List ℕ) (r u : ℕ) (hr : 0 < r) (hu : u ≤ 2*r) :
    count ss.length u (fun t => (roots (r^2+t)).map (fun x => x%M) = s :: ss) =
      if r%M = s then residueCount M ss u else 0 := by
  classical
  by_cases he : r%M = s
  · simp only [he,if_true,residueCount,count]
    apply sum_congr rfl
    intro t ht
    simp [roots_square_add r t hr (by have := mem_range.mp ht; omega),he]
  · simp only [he,if_false,count]
    apply sum_eq_zero
    intro t ht
    simp [roots_square_add r t hr (by have := mem_range.mp ht; omega),he]

/-- A complete block for each admissible first-root residue and an exact final partial block. -/
theorem residueCount_cons (M s : ℕ) (ss : List ℕ) (N : ℕ) (hN : 0<N) :
    residueCount M (s::ss) N =
      (∑ r ∈ (Ico 1 N.sqrt).filter (fun r => r%M=s), residueCount M ss (2*r)) +
      (if N.sqrt%M=s then residueCount M ss (N-N.sqrt^2) else 0) := by
  classical
  unfold residueCount
  rw [List.length_cons,count_succ _ _ _ hN,sum_filter]
  congr 1
  · apply sum_congr rfl
    intro r hr
    exact residueBlock M s ss r (2*r) (mem_Ico.mp hr).1 le_rfl
  · apply residueBlock
    · exact Nat.sqrt_pos.mpr hN
    · have hs : N.sqrt^2 ≤ N := Nat.le_sqrt'.mp le_rfl
      have hl : N < (N.sqrt+1)^2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self _)
      rw [show (N.sqrt+1)^2=N.sqrt^2+2*N.sqrt+1 by ring] at hl
      omega

/-- The empty tuple counts only the input zero. -/
theorem residueCount_nil (M N : ℕ) : residueCount M [] N = 1 := by
  classical
  unfold residueCount count
  rw [sum_eq_single 0]
  · simp [roots,greedyLength]
  · intro n _ hn
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hn
    subst n
    simp [greedyLength]
  · simp

/-- Increasing the cutoff preserves all previously counted inputs. -/
theorem count_mono (j : ℕ) (P : ℕ → Prop) : Monotone (fun N => count j N P) := by
  intro a b hab
  change count j a P ≤ count j b P
  rw [count_eq_card,count_eq_card]
  apply card_le_card
  intro t ht
  simp only [mem_filter,mem_range] at ht ⊢
  exact ⟨by omega, ht.2⟩

/-- Counts for a fixed tuple are nondecreasing with the cutoff. -/
theorem residueCount_mono (M : ℕ) (s : List ℕ) : Monotone (residueCount M s) :=
  count_mono _ _

/-- The discrepancy between the full-block sum and the exact total is at most one
unrestricted block at the largest first root. -/
theorem residueCount_error (M s : ℕ) (ss : List ℕ) (N : ℕ) (hN : 0<N) :
    let full := ∑ r ∈ (Ico 1 N.sqrt).filter (fun r => r%M=s), residueCount M ss (2*r)
    full ≤ residueCount M (s::ss) N ∧
      residueCount M (s::ss) N ≤ full + residueCount M ss (2*N.sqrt) := by
  dsimp only
  rw [residueCount_cons _ _ _ _ hN]
  have hl : N < (N.sqrt+1)^2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self _)
  have hs : N.sqrt^2 ≤ N := Nat.le_sqrt'.mp le_rfl
  rw [show (N.sqrt+1)^2=N.sqrt^2+2*N.sqrt+1 by ring] at hl
  have hm := residueCount_mono M ss (show N-N.sqrt^2 ≤ 2*N.sqrt by omega)
  split_ifs <;> omega

/-- The single-root term counts the positive roots in the chosen residue class. -/
theorem residueCount_singleton (M s N : ℕ) :
    residueCount M [s] N = ((Icc 1 N.sqrt).filter (fun r => r%M=s)).card := by
  classical
  by_cases hn : 0<N
  · have hr := Nat.sqrt_pos.mpr hn
    have hi : Icc 1 N.sqrt = Ico 1 (N.sqrt+1) := by ext x; simp
    rw [residueCount_cons _ _ [] _ hn,hi,card_filter,sum_Ico_succ_top hr,sum_filter]
    simp only [residueCount_nil]
  · have hN : N=0 := by omega
    subst N
    simp [residueCount,count,roots,greedyLength]

end A401548Counts

open Finset Filter
open scoped Topology

namespace GreedyPowerSum

private def offset (M s n : ℕ) : ℝ :=
  (if s < n % M then (M : ℝ) else 0) - (n % M : ℕ)

private theorem offset_bound {M s : ℕ} (hM : 0 < M) (n : ℕ) :
    |offset M s n| ≤ (M : ℝ) := by
  have hr : ((n % M : ℕ) : ℝ) ≤ M := by exact_mod_cast (Nat.mod_lt n hM).le
  have hz : (0 : ℝ) ≤ ↑(n % M) := by positivity
  have hm : (0 : ℝ) ≤ M := by positivity
  dsimp [offset]
  split <;> apply abs_le.mpr <;> constructor <;> linarith

private theorem offset_succ {M s : ℕ} (hM : 0 < M) (hs : s < M) (n : ℕ) :
    offset M s (n+1) - offset M s n = (if n % M = s then (M:ℝ) else 0) - 1 := by
  have hr := Nat.mod_lt n hM
  rw [offset, offset, ← Nat.mod_add_mod n M 1]
  by_cases hw : n % M + 1 = M
  · rw [hw, Nat.mod_self]
    simp only [Nat.not_lt_zero, ↓reduceIte, Nat.cast_zero, sub_self]
    have he : (↑(n % M) : ℝ) + 1 = M := by exact_mod_cast hw
    split_ifs <;> first | omega | linarith
  · have hn : n % M + 1 < M := by omega
    rw [Nat.mod_eq_of_lt hn, Nat.cast_add, Nat.cast_one]
    split_ifs <;> first | omega | ring

private def discrepancy (M s : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (M : ℝ) * (∑ r ∈ (range n).filter (fun r => r % M = s), f r) - ∑ r ∈ range n, f r

private theorem discrepancy_succ (M s : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    discrepancy M s f (n+1) = discrepancy M s f n +
      ((if n % M = s then (M : ℝ) else 0) - 1) * f n := by
  simp only [discrepancy, sum_filter, sum_range_succ]
  split_ifs <;> ring

private theorem discrepancy_bound {M s : ℕ} (hM : 0 < M) (hs : s < M)
    (f : ℕ → ℝ) (hf : Monotone f) (hz : 0 ≤ f 0) (n : ℕ) :
    |discrepancy M s f n| ≤ 2 * M * f n := by
  have aux (k : ℕ) :
      |discrepancy M s f k - offset M s k * f k| ≤ M * (f k - f 0) := by
    induction k with
    | zero => simp [discrepancy, offset]
    | succ k ih =>
      have he : discrepancy M s f (k+1) - offset M s (k+1) * f (k+1) =
          (discrepancy M s f k - offset M s k * f k) +
          offset M s (k+1) * (f k - f (k+1)) := by
        rw [discrepancy_succ, ← offset_succ hM hs]
        ring
      rw [he]
      refine (abs_add_le ..).trans ?_
      rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hf (Nat.le_succ k)))]
      have hx := mul_le_mul_of_nonneg_right (offset_bound (s := s) hM (k+1))
        (neg_nonneg.mpr (sub_nonpos.mpr (hf (Nat.le_succ k))))
      linarith
  have hn := hz.trans (hf (Nat.zero_le n))
  calc
    _ = |(discrepancy M s f n - offset M s n * f n) + offset M s n * f n| := by ring_nf
    _ ≤ |discrepancy M s f n - offset M s n * f n| + |offset M s n * f n| := abs_add_le ..
    _ ≤ M * (f n - f 0) + M * f n := by
      rw [abs_mul, abs_of_nonneg hn]
      exact add_le_add (aux n) (mul_le_mul_of_nonneg_right (offset_bound hM n) hn)
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hz]

private theorem ordinary_error (α : ℝ) (hα : 0 ≤ α) (n : ℕ) :
    |(∑ r ∈ range n, (r : ℝ)^α) - (n:ℝ)^(α+1)/(α+1)| ≤ (n:ℝ)^α := by
  let f := fun (r : ℕ) => (r : ℝ)^α
  have hm : MonotoneOn (fun x : ℝ => x^α) (Set.Icc 0 (0+(n:ℝ))) :=
    fun _ hx _ _ hxy => Real.rpow_le_rpow hx.1 hxy hα
  have hlow := hm.sum_le_integral
  have hhigh := hm.integral_le_sum
  simp only [zero_add, integral_rpow (Or.inl (show -1 < α by linarith)),
    Real.zero_rpow (show α+1 ≠ 0 by linarith), sub_zero] at hlow hhigh
  have hshift := (sum_range_succ f n).symm.trans (sum_range_succ' f n)
  change (∑ i ∈ range n, f i) + f n = (∑ i ∈ range n, f (i+1)) + f 0 at hshift
  have hf0 : 0 ≤ f 0 := Real.rpow_nonneg (by simp) _
  change _ ≤ ∑ i ∈ range n, f (i+1) at hhigh
  change (∑ i ∈ range n, f i) ≤ _ at hlow
  change |(∑ i ∈ range n, f i) - _| ≤ f n
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith

theorem power_progression (M s : ℕ) (hM : 0 < M) (hs : s < M)
    (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun R : ℕ => (∑ r ∈ (range R).filter (fun r => r % M = s), (r:ℝ)^α) /
      (R:ℝ)^(α+1)) atTop (𝓝 (1/((M:ℝ)*(α+1)))) := by
  let f := fun r : ℕ => (r:ℝ)^α
  have hf : Monotone f := fun i j hij => Real.rpow_le_rpow (by positivity) (by exact_mod_cast hij) hα
  have hf0 : 0 ≤ f 0 := Real.rpow_nonneg (by simp) _
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  have ha : 0 < α + 1 := by linarith
  let b := fun R : ℕ => ∑ r ∈ (range R).filter (fun r => r%M=s), f r
  let C : ℝ := (2*M+1)/M
  have herr (R : ℕ) :
      |(M:ℝ) * b R - (R:ℝ)^(α+1)/(α+1)| ≤ (2*M+1)*f R := by
    have h := abs_sub_le ((M:ℝ)*b R) (∑ r ∈ range R, f r) ((R:ℝ)^(α+1)/(α+1))
    have h1 := discrepancy_bound hM hs f hf hf0 R
    change |(M:ℝ)*b R - _| ≤ _ at h1
    have h2 := ordinary_error α hα R
    change |(∑ r ∈ range R, f r) - _| ≤ f R at h2
    linarith
  have hzero : Tendsto (fun R : ℕ => C/(R:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hzero
  filter_upwards [eventually_gt_atTop 0] with R hR
  have hr : 0 < (R:ℝ) := by exact_mod_cast hR
  have hpow : 0 < (R:ℝ)^(α+1) := Real.rpow_pos_of_pos hr _
  have hab : b R/(R:ℝ)^(α+1) - 1/((M:ℝ)*(α+1)) =
      ((M:ℝ)*b R - (R:ℝ)^(α+1)/(α+1)) / ((M:ℝ)*(R:ℝ)^(α+1)) := by
    field_simp
  change ‖b R/(R:ℝ)^(α+1) - _‖ ≤ C/(R:ℝ)
  rw [Real.norm_eq_abs, hab, abs_div, abs_of_pos (mul_pos hm hpow)]
  refine (div_le_div_of_nonneg_right (herr R) (mul_pos hm hpow).le).trans_eq ?_
  dsimp [C, f]
  rw [Real.rpow_add_one hr.ne']
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hr α)]


open Asymptotics

theorem weighted_progression (M s : ℕ) (hM : 0 < M) (hs : s < M)
    (α b : ℝ) (hα : 0 ≤ α) (f : ℕ → ℝ)
    (hf : Tendsto (fun r : ℕ => f r/(r:ℝ)^α) atTop (𝓝 b)) :
    Tendsto (fun R : ℕ => (∑ r ∈ (range R).filter (fun r => r%M=s), f r) /
      (R:ℝ)^(α+1)) atTop (𝓝 (b/((M:ℝ)*(α+1)))) := by
  let g : ℕ → ℝ := fun r => if r%M=s then (r:ℝ)^α else 0
  let w : ℕ → ℝ := fun r => if r%M=s then f r else 0
  let A := fun R => ∑ r ∈ range R, g r
  let B := fun R : ℕ => (R:ℝ)^(α+1)
  let c : ℝ := 1/((M:ℝ)*(α+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hB : Tendsto B atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < α+1)).comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun R => A R / B R) atTop (𝓝 c) := by
    simpa only [A, B, c, g, sum_filter] using power_progression M s hM hs α hα
  have hA : Tendsto A atTop atTop := by
    apply (hp.pos_mul_atTop hc hB).congr'
    filter_upwards [eventually_gt_atTop 0] with R hR
    have hbr : 0 < B R := Real.rpow_pos_of_pos (by exact_mod_cast hR) _
    exact div_mul_cancel₀ _ hbr.ne'
  have hplain : (fun r : ℕ => f r - b*(r:ℝ)^α) =o[atTop] (fun r : ℕ => (r:ℝ)^α) := by
    apply (isLittleO_iff_tendsto' ?_).2
    · apply (tendsto_sub_nhds_zero_iff.mpr hf).congr'
      filter_upwards [eventually_gt_atTop 0] with r hr
      have hpw := (Real.rpow_pos_of_pos (by exact_mod_cast hr : (0:ℝ) < r) α).ne'
      simp [sub_div, hpw]
    · filter_upwards [eventually_gt_atTop 0] with r hr
      exact fun h => False.elim ((Real.rpow_pos_of_pos (by exact_mod_cast hr : (0:ℝ) < r) α).ne' h)
  have hres : (fun r => w r - b*g r) =o[atTop] g := by
    apply IsLittleO.of_bound
    intro d hd
    filter_upwards [isLittleO_iff.mp hplain hd] with r hr
    by_cases hrm : r%M=s
    · simpa only [w, g, if_pos hrm] using hr
    · simp [w, g, hrm]
  have hg : 0 ≤ g := by
    intro r
    dsimp [g]
    split <;> positivity
  have hsum := (hres.sum_range hg hA).tendsto_div_nhds_zero
  have hlim := (hsum.mul hp).add (hp.const_mul b)
  have hc' : 0*c+b*c = b/((M:ℝ)*(α+1)) := by dsimp [c]; ring
  rw [hc'] at hlim
  apply hlim.congr'
  filter_upwards [hA.eventually_gt_atTop 0] with R hR
  have hsumEq : (∑ r ∈ range R, (w r - b*g r)) = (∑ r ∈ range R, w r) - b*A R := by
    rw [sum_sub_distrib, mul_sum]
  rw [sum_filter]
  change ((∑ r ∈ range R, (w r - b*g r))/A R) * (A R/B R) + b*(A R/B R) =
    (∑ r ∈ range R, w r)/B R
  rw [hsumEq]
  field_simp [hR.ne']
  simp

theorem weighted_progression_Ico (M s : ℕ) (hM : 0 < M) (hs : s < M)
    (α b : ℝ) (hα : 0 ≤ α) (f : ℕ → ℝ)
    (hf : Tendsto (fun r : ℕ => f r/(r:ℝ)^α) atTop (𝓝 b)) :
    Tendsto (fun R : ℕ => (∑ r ∈ (Ico 1 R).filter (fun r => r%M=s), f r) /
      (R:ℝ)^(α+1)) atTop (𝓝 (b/((M:ℝ)*(α+1)))) := by
  let w := fun r => if r%M=s then f r else 0
  have hterm : Tendsto (fun R : ℕ => w 0 / (R:ℝ)^(α+1)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact (tendsto_rpow_atTop (by linarith : 0 < α+1)).comp tendsto_natCast_atTop_atTop
  have hlim := (weighted_progression M s hM hs α b hα f hf).sub hterm
  rw [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with R hR
  rw [sum_filter, sum_filter, ← sub_div]
  congr 1
  have he := sum_range_add_sum_Ico w hR
  simpa only [sum_range_one] using (eq_sub_of_add_eq' he).symm

end GreedyPowerSum

/-! Scaling the square-block recurrence from cutoffs in the first root to cutoffs
in the original integer. -/

namespace A401548Counts
open Filter Topology Finset

noncomputable def exponent : ℕ → ℝ
  | 0 => 0
  | j+1 => (exponent j+1)/2

noncomputable def volume : ℕ → ℝ
  | 0 => 1
  | j+1 => 2^(exponent j)*volume j/(exponent j+1)

theorem exponent_nonneg (j : ℕ) : 0 ≤ exponent j := by
  induction j with
  | zero => simp [exponent]
  | succ j ih => simp only [exponent]; positivity

theorem volume_pos (j : ℕ) : 0 < volume j := by
  induction j with
  | zero => simp [volume]
  | succ j ih =>
    have := exponent_nonneg j
    simp only [volume]
    positivity

theorem sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop.mpr (fun b => ?_)
  filter_upwards [eventually_ge_atTop (b^2)] with N hN
  exact Nat.le_sqrt'.mpr hN

private theorem sqrt_ratio : Tendsto (fun n : ℕ => (n.sqrt : ℝ) / Real.sqrt n)
    atTop (𝓝 1) := by
  have hzero : Tendsto (fun n : ℕ => 1 / Real.sqrt (n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun n : ℕ => 1 - 1 / Real.sqrt (n:ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hN : n < (n.sqrt+1)^2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self _)
    have hR : Real.sqrt (n:ℝ) ≤ (n.sqrt:ℝ)+1 := Real.sqrt_le_iff.mpr
      ⟨by positivity,by exact_mod_cast hN.le⟩
    rw [le_div_iff₀ hpos,sub_mul,one_mul,div_mul_cancel₀ _ hpos.ne']
    linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hs : n.sqrt^2 ≤ n := Nat.le_sqrt'.mp le_rfl
    rw [div_le_iff₀ hpos,one_mul]
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast hs)

theorem sqrt_power_ratio (p : ℝ) : Tendsto (fun n : ℕ =>
    (n.sqrt:ℝ)^p / (n:ℝ)^(p/2)) atTop (𝓝 1) := by
  have h := sqrt_ratio.rpow_const (p:=p) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at h
  apply h.congr'
  filter_upwards [] with n
  rw [Real.div_rpow (by positivity) (by positivity),Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity),show (1/2:ℝ)*p=p/2 by ring]

private theorem double_limit {α b : ℝ} {f : ℕ → ℝ}
    (hf : Tendsto (fun n : ℕ => f n/(n:ℝ)^α) atTop (𝓝 b)) :
    Tendsto (fun r : ℕ => f (2*r)/(r:ℝ)^α) atTop (𝓝 ((2:ℝ)^α*b)) := by
  have ht : Tendsto (fun r : ℕ => 2*r) atTop atTop := by
    refine tendsto_atTop.mpr (fun r => ?_)
    filter_upwards [eventually_ge_atTop r] with n hn
    omega
  apply ((hf.comp ht).const_mul ((2:ℝ)^α)).congr'
  filter_upwards [] with r
  simp only [Function.comp_apply,Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by positivity : (0:ℝ)≤2)
    (by positivity : (0:ℝ)≤r)]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) α)]

private theorem tail_limit {α b : ℝ} {f : ℕ → ℝ}
    (hf : Tendsto (fun n : ℕ => f n/(n:ℝ)^α) atTop (𝓝 b)) :
    Tendsto (fun r : ℕ => f r/(r:ℝ)^(α+1)) atTop (𝓝 0) := by
  have hz : Tendsto (fun r : ℕ => 1/(r:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := hf.mul hz
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hR : 0 < (r:ℝ) := by exact_mod_cast hr
  rw [Real.rpow_add_one hR.ne']
  ring

/-- The induction step, parametrized by the weighted progression summation theorem. -/
theorem residueCount_step (M s : ℕ) (ss : List ℕ) (α b : ℝ)
    (hp : ∀ (f : ℕ → ℝ) (c : ℝ), Tendsto (fun r : ℕ => f r/(r:ℝ)^α) atTop (𝓝 c) →
      Tendsto (fun R : ℕ => (∑ r ∈ (Ico 1 R).filter (fun r => r%M=s), f r) /
        (R:ℝ)^(α+1)) atTop (𝓝 (c/((M:ℝ)*(α+1)))))
    (hf : Tendsto (fun N : ℕ => (residueCount M ss N:ℝ)/(N:ℝ)^α) atTop (𝓝 b)) :
    Tendsto (fun N : ℕ => (residueCount M (s::ss) N:ℝ)/(N:ℝ)^((α+1)/2)) atTop
      (𝓝 ((2:ℝ)^α*b/((M:ℝ)*(α+1)))) := by
  let f (r : ℕ) := (residueCount M ss (2*r):ℝ)
  let A (R : ℕ) := ∑ r ∈ (Ico 1 R).filter (fun r => r%M=s), f r
  let c := (2:ℝ)^α*b/((M:ℝ)*(α+1))
  have hh : Tendsto (fun r : ℕ => f r/(r:ℝ)^α) atTop (𝓝 ((2:ℝ)^α*b)) := double_limit hf
  have hm : Tendsto (fun R : ℕ => A R/(R:ℝ)^(α+1)) atTop (𝓝 c) := hp _ _ hh
  have he := tail_limit hh
  have hu : Tendsto (fun R : ℕ => (A R+f R)/(R:ℝ)^(α+1)) atTop (𝓝 c) := by
    simpa [add_div] using hm.add he
  have hlow := hm.comp sqrt_atTop
  have hhigh := hu.comp sqrt_atTop
  have hb : ∀ᶠ N : ℕ in atTop, A N.sqrt ≤ (residueCount M (s::ss) N:ℝ) ∧
      (residueCount M (s::ss) N:ℝ) ≤ A N.sqrt + f N.sqrt := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have ht := residueCount_error M s ss N hN
    dsimp only at ht
    dsimp only [A,f]
    exact ⟨by exact_mod_cast ht.1,by exact_mod_cast ht.2⟩
  have hmid : Tendsto (fun N : ℕ => (residueCount M (s::ss) N:ℝ)/(N.sqrt:ℝ)^(α+1))
      atTop (𝓝 c) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
    · filter_upwards [hb] with N hN
      exact div_le_div_of_nonneg_right hN.1 (by positivity)
    · filter_upwards [hb] with N hN
      exact div_le_div_of_nonneg_right hN.2 (by positivity)
  have h := hmid.mul (sqrt_power_ratio (α+1))
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hR : 0 < (N.sqrt:ℝ) := by exact_mod_cast Nat.sqrt_pos.mpr hN
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hR (α+1))]

end A401548Counts

/-! Equidistribution for each fixed list of greedy square-root residues. -/

namespace A401548Counts
open Filter Topology Finset OMA.S_oeis_a401548

/-- Every ordered tuple of residue classes has the same leading asymptotic. -/
theorem residueCount_limit (M : ℕ) (hM : 0<M) (ss : List ℕ) (hs : ∀ s ∈ ss,s<M) :
    Tendsto (fun N : ℕ => (residueCount M ss N:ℝ)/(N:ℝ)^(exponent ss.length)) atTop
      (𝓝 (volume ss.length / (M:ℝ)^ss.length)) := by
  induction ss with
  | nil => simp [residueCount_nil,exponent,volume]
  | cons s ss ih =>
    have hh := ih (fun r hr => hs r (List.mem_cons_of_mem _ hr))
    have ha := exponent_nonneg ss.length
    have hs' : s<M := hs s List.mem_cons_self
    have h := residueCount_step M s ss (exponent ss.length)
      (volume ss.length / (M:ℝ)^ss.length)
      (fun f c hf => GreedyPowerSum.weighted_progression_Ico M s hM hs' _ c ha f hf) hh
    simp only [List.length_cons,exponent,volume,pow_succ]
    convert h using 2
    have hm : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hp : exponent ss.length + 1 ≠ 0 := by linarith
    field_simp [hm,hp]

theorem exponent_lt_one (j : ℕ) : exponent j < 1 := by
  induction j with
  | zero => norm_num [exponent]
  | succ j ih => rw [exponent]; linarith

theorem exponent_strictMono : StrictMono exponent := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [exponent]
  linarith [exponent_lt_one j]

theorem exponent_four : exponent 4 = 15/16 := by norm_num [exponent]

/-- The explicit coefficient for all four-root expansions. -/
theorem volume_four : volume 4 = (64/315:ℝ)*(2:ℝ)^(17/8:ℝ) := by
  have he : (17/8:ℝ)=7/8+(3/4+1/2) := by norm_num
  rw [he,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_add (by norm_num : (0:ℝ)<2)]
  norm_num [volume,exponent]
  ring

/-- Modulus one records precisely the unrestricted greedy length. -/
theorem count_all_eq_residue (j N : ℕ) :
    count j N (fun _ => True) = residueCount 1 (List.replicate j 0) N := by
  classical
  unfold residueCount
  simp only [List.length_replicate,count]
  apply sum_congr rfl
  intro n _
  have hmap : (roots n).map (fun r => r % 1) = List.replicate (greedyLength n) 0 := by
    simp only [Nat.mod_one,List.map_const',roots_length]
  by_cases hn : greedyLength n = j <;> simp [hn,hmap]

/-- The leading coefficient for length alone is the unrestricted volume. -/
theorem count_length_limit (j : ℕ) :
    Tendsto (fun N : ℕ => (count j N (fun _ => True):ℝ)/(N:ℝ)^(exponent j))
      atTop (𝓝 (volume j)) := by
  have hr : ∀ s ∈ List.replicate j 0,s<1 :=
    fun s hs => by rw [List.eq_of_mem_replicate hs]; decide
  have h := residueCount_limit 1 (by decide) (List.replicate j 0) hr
  simpa only [List.length_replicate,Nat.cast_one,one_pow,div_one,← count_all_eq_residue] using h

/-- Shorter greedy expansions have zero density on the four-root scale. -/
theorem count_short_limit (j : ℕ) (hj : j<4) :
    Tendsto (fun N : ℕ => (count j N (fun _ => True):ℝ)/(N:ℝ)^(15/16:ℝ))
      atTop (𝓝 0) := by
  have he := exponent_strictMono hj
  rw [exponent_four] at he
  have hz := (tendsto_rpow_neg_atTop (sub_pos.mpr he)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h := (count_length_limit j).mul hz
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  simp only [Function.comp_apply,neg_sub,Real.rpow_sub hp]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hp (exponent j))]

/-- On the four-root scale the combined contribution of zero through three terms tends to zero. -/
theorem shorter_count_limit :
    Tendsto (fun N : ℕ => (((range (N+1)).filter (fun n => greedyLength n ≤ 3)).card : ℝ) /
      (N:ℝ)^(15/16:ℝ)) atTop (𝓝 0) := by
  classical
  have eq (N : ℕ) : ((range (N+1)).filter (fun n => greedyLength n ≤ 3)).card =
      ∑ j ∈ range 4, count j N (fun _ => True) := by
    rw [card_filter]
    simp only [count,and_true]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    simp [Nat.lt_succ_iff]
  have ht := tendsto_finsetSum (range 4) (fun j hj => count_short_limit j (mem_range.mp hj))
  simpa only [eq,Nat.cast_sum,sum_div,sum_const_zero] using ht

end A401548Counts

/-! Dyadic residue classes for four-square sums in the Legendre obstruction. -/
namespace A401548Density

def obstructed (n : ℕ) : Prop := ∃ j b : ℕ, n = 4^j*(8*b+7)

def value (x y z w : ℕ) : ℕ := x^2+y^2+z^2+w^2

def allEven (x y z w : ℕ) : Prop := x%2=0 ∧ y%2=0 ∧ z%2=0 ∧ w%2=0

instance (x y z w : ℕ) : Decidable (allEven x y z w) := by unfold allEven; infer_instance

/-- The primitive classes are periodic in each root modulo sixteen. -/
def primitive (x y z w : ℕ) : Prop :=
  ¬allEven x y z w ∧ (value x y z w % 8=7 ∨ value x y z w % 32=28)

instance (x y z w : ℕ) : Decidable (primitive x y z w) := by unfold primitive; infer_instance

theorem obstructed_four (n : ℕ) : obstructed (4*n) ↔ obstructed n := by
  constructor
  · rintro ⟨j,b,h⟩
    cases j with
    | zero => simp at h; omega
    | succ j =>
      refine ⟨j,b,?_⟩
      rw [pow_succ', Nat.mul_assoc] at h
      omega
  · rintro ⟨j,b,rfl⟩
    exact ⟨j+1,b,by rw [pow_succ']; ring⟩

private theorem primitive_obstruction {n : ℕ} (h8 : n%8≠0) :
    obstructed n ↔ n%8=7 ∨ n%32=28 := by
  constructor
  · rintro ⟨j,b,rfl⟩
    cases j with
    | zero => left; simp
    | succ j =>
      cases j with
      | zero => right; simp; omega
      | succ j =>
        have hd : 8 ∣ 4^(j+1+1)*(8*b+7) := ⟨2*(4^j*(8*b+7)),by rw [pow_succ', pow_succ']; ring⟩
        exact False.elim (h8 (Nat.mod_eq_zero_of_dvd hd))
  · rintro (h|h)
    · exact ⟨0,n/8,by simp; omega⟩
    · exact ⟨1,n/32,by simp; omega⟩

private theorem square_split (x : ℕ) :
    x^2=(x%16)^2+32*((x%16+8*(x/16))*(x/16)) := by
  conv_lhs => rw [← Nat.mod_add_div x 16]
  ring

private theorem value_split (x y z w : ℕ) :
    ∃ t, value x y z w = value (x%16) (y%16) (z%16) (w%16) + 32*t := by
  refine ⟨((x%16+8*(x/16))*(x/16))+((y%16+8*(y/16))*(y/16))+
    ((z%16+8*(z/16))*(z/16))+((w%16+8*(w/16))*(w/16)),?_⟩
  unfold value
  nth_rewrite 1 [square_split x]
  nth_rewrite 1 [square_split y]
  nth_rewrite 1 [square_split z]
  nth_rewrite 1 [square_split w]
  ring

theorem primitive_mod (x y z w : ℕ) :
    primitive x y z w ↔ primitive (x%16) (y%16) (z%16) (w%16) := by
  obtain ⟨t,h⟩ := value_split x y z w
  unfold primitive allEven
  omega

private theorem square_mod_four (x : ℕ) : x^2%8=(x%4)^2%8 := by
  have h : x^2=(x%4)^2+8*((x%4+2*(x/4))*(x/4)) := by
    conv_lhs => rw [← Nat.mod_add_div x 4]
    ring
  omega

private theorem primitive_mod_eight :
    ∀ x y z w : Fin 4, ¬allEven x y z w → value x y z w % 8≠0 := by decide

theorem obstruction_split (x y z w : ℕ) :
    obstructed (value x y z w) ↔ primitive x y z w ∨
       (allEven x y z w ∧ obstructed (value (x/2) (y/2) (z/2) (w/2))) := by
  by_cases he : allEven x y z w
  · have shape : value x y z w = 4*value (x/2) (y/2) (z/2) (w/2) := by
      obtain ⟨hx,hy,hz,hw⟩ := he
      obtain ⟨a,ha⟩ := Nat.dvd_of_mod_eq_zero hx
      obtain ⟨b,hb⟩ := Nat.dvd_of_mod_eq_zero hy
      obtain ⟨c,hc⟩ := Nat.dvd_of_mod_eq_zero hz
      obtain ⟨d,hd⟩ := Nat.dvd_of_mod_eq_zero hw
      subst x; subst y; subst z; subst w
      simp [value]
      ring
    simpa [primitive,he,shape] using obstructed_four (value (x/2) (y/2) (z/2) (w/2))
  · have hfinite := primitive_mod_eight ⟨x%4,by omega⟩ ⟨y%4,by omega⟩
        ⟨z%4,by omega⟩ ⟨w%4,by omega⟩ (by unfold allEven at he ⊢; dsimp only; omega)
    have h8 : value x y z w%8≠0 := by
      unfold value at hfinite ⊢
      dsimp only at hfinite
      have h1 := square_mod_four x
      have h2 := square_mod_four y
      have h3 := square_mod_four z
      have h4 := square_mod_four w
      omega
    simpa [primitive,he] using primitive_obstruction h8

def cube [AddCommMonoid α] (n : ℕ) (f : ℕ → ℕ → ℕ → ℕ → α) : α :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n, ∑ w ∈ Finset.range n, f x y z w

theorem primitive_count : cube 16 (fun x y z w => if primitive x y z w then 1 else 0) = 9216 := by
  decide +kernel

end A401548Density

namespace A401548Density
open Finset

abbrev Kernel := ℕ → ℕ → ℕ → ℕ → ℕ

private def iterateSum (T : (ℕ → ℕ) → ℕ) (f : Kernel) : ℕ :=
  T (fun x => T (fun y => T (fun z => T (f x y z))))

private theorem range_mod (k n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (k*n), f (i%k) = n*∑ i ∈ range k, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,sum_range_add,ih,Nat.succ_mul]
    congr 1
    apply sum_congr rfl
    intro i h
    rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (mem_range.mp h)]

theorem cube_mod (k n : ℕ) (f : Kernel) :
    cube (k*n) (fun x y z w => f (x%k) (y%k) (z%k) (w%k)) = n^4*cube k f := by
  change iterateSum (fun g => ∑ i ∈ range (k*n),g (i%k)) f = _
  rw [show (fun g : ℕ → ℕ => ∑ i ∈ range (k*n),g (i%k)) =
    (fun g => n*∑ i ∈ range k,g i) from funext (range_mod k n)]
  simp only [iterateSum,cube,←mul_sum]
  ring

def primitiveMask (x y z w : ℕ) : ℕ := if primitive x y z w then 1 else 0

theorem cube_primitive (n : ℕ) : cube (16*n) primitiveMask = n^4*9216 := by
  rw [← primitive_count,←cube_mod]
  congr 1
  funext x y z w
  simp only [primitiveMask]
  by_cases h : primitive x y z w
  · simp [h,(primitive_mod x y z w).mp h]
  · simp [h,mt (primitive_mod x y z w).mpr h]

def evenWeight (i : ℕ) : ℕ := if i%2=0 then 1 else 0

def lift (f : Kernel) : Kernel := fun x y z w =>
  evenWeight x*(evenWeight y*(evenWeight z*(evenWeight w*f (x/2) (y/2) (z/2) (w/2))))

private theorem sum_even (n : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (2*n),evenWeight i*f (i/2) = ∑ i ∈ range n,f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]
    simp [sum_range_succ, evenWeight]

theorem cube_lift (n : ℕ) (f : Kernel) : cube (2*n) (lift f)=cube n f := by
  calc cube (2*n) (lift f) =
        iterateSum (fun g => ∑ i ∈ range (2*n),evenWeight i*g (i/2)) f := by
          simp only [cube,lift,iterateSum,mul_sum]
    _ = cube n f := by
      rw [show (fun g : ℕ → ℕ => ∑ i ∈ range (2*n),evenWeight i*g (i/2)) =
              (fun g => ∑ i ∈ range n,g i) from funext (sum_even n)]
      rfl

def layer : ℕ → Kernel
  | 0 => primitiveMask
  | j+1 => lift (layer j)

def tail : ℕ → Kernel
  | 0 => fun _ _ _ _ => 1
  | j+1 => lift (tail j)

theorem cube_layer (j n : ℕ) : cube (2^j*(16*n)) (layer j)=n^4*9216 := by
  induction j with
  | zero => simpa [layer] using cube_primitive n
  | succ j ih => simpa only [pow_succ',Nat.mul_assoc,layer,cube_lift] using ih

theorem cube_tail (j n : ℕ) : cube (2^j*n) (tail j)=n^4 := by
  induction j with
  | zero => simp [cube,tail]; ring
  | succ j ih => simpa only [pow_succ',Nat.mul_assoc,tail,cube_lift] using ih

/-- Among residues modulo 16·2^L, the good primitive classes after exactly j
dyadic divisions have density (9/64)·16⁻ʲ. -/
theorem layer_mass (j L : ℕ) (hj : j≤L) :
    ((cube (2^L*16) (layer j):ℕ):ℝ) / ((2:ℝ)^L*16)^4 =
      (9/64:ℝ)*(1/16:ℝ)^j := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show (2:ℕ)^(j+d)*16=2^j*(16*2^d) by rw [pow_add]; ring, cube_layer]
  push_cast
  rw [pow_add]
  have h : (16:ℝ)^j=(2^j)^4 := by rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [one_div_pow,h]
  field_simp
  ring

theorem tail_mass (L : ℕ) : ((cube (2^L*16) (tail L):ℕ):ℝ)/((2:ℝ)^L*16)^4 = (1/16:ℝ)^L := by
  rw [cube_tail]
  push_cast
  have h : (16:ℝ)^L=(2^L)^4 := by rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [one_div_pow,h]
  field_simp
  ring

open Filter Topology

theorem limiting_mass :
    Tendsto (fun L : ℕ => ∑ j ∈ range L, (9/64:ℝ)*(1/16:ℝ)^j) atTop (𝓝 (3/20)) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/16)
    (by norm_num : (1/16:ℝ)<1)).mul_left (9/64:ℝ)
  convert h.tendsto_sum_nat using 1
  norm_num

end A401548Density

namespace A401548Density

open Finset

noncomputable def obstructionMask : Kernel := by
  classical
  exact fun x y z w => if obstructed (value x y z w) then 1 else 0

theorem lift_apply (f : Kernel) (x y z w : ℕ) :
    lift f x y z w = if allEven x y z w then f (x/2) (y/2) (z/2) (w/2) else 0 := by
  simp only [lift,evenWeight,allEven]
  split_ifs <;> simp_all

private theorem obstruction_recurrence (x y z w : ℕ) :
    obstructionMask x y z w = primitiveMask x y z w + lift obstructionMask x y z w := by
  classical
  rw [lift_apply]
  unfold obstructionMask primitiveMask
  by_cases h : allEven x y z w
  · have n : ¬primitive x y z w := fun hp => hp.1 h
    simpa [h,n] using congrArg (fun p : Prop => if p then 1 else 0)
      (propext (obstruction_split x y z w))
  · simpa [h] using congrArg (fun p : Prop => if p then 1 else 0)
      (propext (obstruction_split x y z w))

theorem cutoff_bounds (L x y z w : ℕ) :
    (∑ j ∈ range L, layer j x y z w) ≤ obstructionMask x y z w ∧
    obstructionMask x y z w ≤ (∑ j ∈ range L,layer j x y z w) + tail L x y z w := by
  induction L generalizing x y z w with
  | zero =>
    classical
    simp [obstructionMask,tail]
    split_ifs <;> omega
  | succ L ih =>
    rw [sum_range_succ',obstruction_recurrence x y z w]
    simp only [layer,tail,lift_apply]
    by_cases he : allEven x y z w
    · simp [he]
      obtain ⟨lo,hi⟩ := ih (x/2) (y/2) (z/2) (w/2)
      omega
    · simp [he]

private theorem parity_mod (n m : ℕ) : (n%(2*m))%2=n%2 :=
  Nat.mod_mod_of_dvd n (dvd_mul_right 2 m)

private theorem half_mod (n m : ℕ) : (n%(2*m))/2=(n/2)%m := by
  rw [Nat.mul_comm 2, Nat.mod_mul_left_div_self]

/-- The j-th layer can be read from the roots modulo a single common period. -/
theorem layer_periodic (j L : ℕ) (h : j≤L) (x y z w : ℕ) :
    layer j (x%(2^L*16)) (y%(2^L*16)) (z%(2^L*16)) (w%(2^L*16)) =
    layer j x y z w := by
  induction j generalizing L x y z w with
  | zero =>
    have dvd : 16∣2^L*16 := dvd_mul_left 16 _
    have heq : primitive (x%(2^L*16)) (y%(2^L*16)) (z%(2^L*16)) (w%(2^L*16)) ↔ primitive x y z w := by
      rw [primitive_mod (x%(2^L*16)), primitive_mod x y z w]
      simp only [Nat.mod_mod_of_dvd _ dvd]
    simp only [layer,primitiveMask,heq]
  | succ j ih =>
    obtain ⟨L,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L≠0)
    simp only [layer,lift_apply,pow_succ',Nat.mul_assoc,allEven, parity_mod,half_mod,
      ih L (by omega)]

theorem tail_periodic (L x y z w : ℕ) :
    tail L (x%(2^L*16)) (y%(2^L*16)) (z%(2^L*16)) (w%(2^L*16)) = tail L x y z w := by
  induction L generalizing x y z w with
  | zero => rfl
  | succ L ih =>
    simp only [tail,lift_apply,pow_succ',Nat.mul_assoc,allEven,parity_mod,half_mod,ih]

end A401548Density

open Filter Finset
open scoped Topology

namespace A401548Squeeze

/-- Successively finer lower and upper estimates determine the limit. -/
theorem by_truncation (f a b : ℕ → ℝ) (c : ℝ)
    (ha : Tendsto a atTop (𝓝 c)) (hb : Tendsto b atTop (𝓝 c))
    (hbound : ∀ L : ℕ, ∃ g h : ℕ → ℝ,
      Tendsto g atTop (𝓝 (a L)) ∧ Tendsto h atTop (𝓝 (b L)) ∧
      ∀ᶠ n in atTop, g n ≤ f n ∧ f n ≤ h n) :
    Tendsto f atTop (𝓝 c) := by
  apply tendsto_order.mpr
  constructor
  · intro d hd
    obtain ⟨L,hL⟩ := ((tendsto_order.mp ha).1 d hd).exists
    obtain ⟨g,h,hg,_,hle⟩ := hbound L
    filter_upwards [(tendsto_order.mp hg).1 d hL, hle] with n hn hn'
    exact hn.trans_le hn'.1
  · intro d hd
    obtain ⟨L,hL⟩ := ((tendsto_order.mp hb).2 d hd).exists
    obtain ⟨g,h,_,hh,hle⟩ := hbound L
    filter_upwards [(tendsto_order.mp hh).2 d hL, hle] with n hn hn'
    exact hn'.2.trans_lt hn

/-- For each fixed cutoff L, one lower sum and one geometric tail suffice. -/
theorem by_dyadic_layers (f : ℕ → ℝ) (v : ℝ)
    (hbound : ∀ L : ℕ, ∃ g h : ℕ → ℝ,
      Tendsto g atTop (𝓝 (v * ∑ j ∈ range L, (9/64:ℝ)*(1/16:ℝ)^j)) ∧
      Tendsto h atTop (𝓝 (v * (1/16:ℝ)^L)) ∧
      ∀ᶠ n in atTop, g n ≤ f n ∧ f n ≤ g n + h n) :
    Tendsto f atTop (𝓝 (v * (3/20))) := by
  have ha := A401548Density.limiting_mass.const_mul v
  have hq := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/16)
    (by norm_num : (1:ℝ)/16<1)).const_mul v
  rw [mul_zero] at hq
  have hb := ha.add hq
  rw [add_zero] at hb
  apply by_truncation _ _ _ _ ha hb
  intro L
  obtain ⟨g,h,hg,hh,hle⟩ := hbound L
  exact ⟨g,fun n => g n+h n,hg,hg.add hh,hle⟩

end A401548Squeeze

namespace A401548Squeeze

open Finset Filter Topology A401548Counts A401548Density

def rootWeight (W : Kernel) : List ℕ → ℕ
  | [x,y,z,w] => W x y z w
  | _ => 0

def maskedCount (W : Kernel) (N : ℕ) : ℕ :=
  ∑ n ∈ range (N+1), rootWeight W (roots n)

private theorem cube_exchange (M : ℕ) (S : Finset ℕ) (f : ℕ → Kernel) :
    cube M (fun x y z w => ∑ r ∈ S, f r x y z w) = ∑ r ∈ S, cube M (f r) := by
  induction S using Finset.induction_on with
  | empty => simp [cube]
  | insert k S h ih =>
    simp only [sum_insert h] at *
    simpa only [cube, sum_add_distrib] using congrArg (cube M (f k) + ·) ih

private theorem cube_select (M : ℕ) (hM : 0 < M) (W : Kernel) (l : List ℕ) :
    cube M (fun x y z w => if l.map (·%M)=[x,y,z,w] then W x y z w else 0) =
      rootWeight (fun x y z w => W (x%M) (y%M) (z%M) (w%M)) l := by
  rcases l with _ | ⟨a,l⟩ <;> [simp [cube,rootWeight]; skip]
  rcases l with _ | ⟨b,l⟩ <;> [simp [cube,rootWeight]; skip]
  rcases l with _ | ⟨c,l⟩ <;> [simp [cube,rootWeight]; skip]
  rcases l with _ | ⟨d,l⟩ <;> [simp [cube,rootWeight]; skip]
  cases l with
  | nil =>
    simp only [cube, List.map_cons, List.map_nil, List.cons.injEq, and_true, rootWeight]
    rw [sum_eq_single (a%M)]
    · simp only [true_and]
      rw [sum_eq_single (b%M)]
      · simp only [true_and]
        rw [sum_eq_single (c%M)]
        · simp [Nat.mod_lt _ hM]
        · intro z _ hz
          simp [Ne.symm hz]
        · simp [Nat.mod_lt _ hM]
      · intro y _ hy
        simp [Ne.symm hy]
      · simp [Nat.mod_lt _ hM]
    · intro x _ hx
      simp [Ne.symm hx]
    · simp [Nat.mod_lt _ hM]
  | cons e es => simp [cube,rootWeight]

theorem masked_count_eq_cube (M : ℕ) (hM : 0 < M) (W : Kernel)
    (hW : ∀ x y z w, W (x%M) (y%M) (z%M) (w%M) = W x y z w) (N : ℕ) :
    maskedCount W N =
      cube M (fun x y z w => W x y z w * residueCount M [x,y,z,w] N) := by
  classical
  have term (x y z w : ℕ) :
      W x y z w * residueCount M [x,y,z,w] N =
      ∑ n ∈ range (N+1), if (roots n).map (·%M)=[x,y,z,w] then W x y z w else 0 := by
    simp only [residueCount, count, mul_sum]
    apply sum_congr rfl
    intro n _
    by_cases he : (roots n).map (·%M)=[x,y,z,w]
    · have hlen := congrArg List.length he
      have hl : OMA.S_oeis_a401548.greedyLength n = 4 := by simpa [roots_length] using hlen
      simp [he, hl]
    · simp [he]
  simp_rw [term]
  rw [cube_exchange]
  unfold maskedCount
  apply sum_congr rfl
  intro n _
  rw [cube_select M hM]
  congr 1
  funext x y z w
  exact (hW x y z w).symm

theorem masked_count_limit (M : ℕ) (hM : 0 < M) (W : Kernel)
    (hW : ∀ x y z w, W (x%M) (y%M) (z%M) (w%M) = W x y z w) :
    Tendsto (fun N : ℕ => (maskedCount W N : ℝ)/(N:ℝ)^(exponent 4)) atTop
      (𝓝 (volume 4 * ((cube M W : ℕ):ℝ)/(M:ℝ)^4)) := by
  have hh := fun x (hx : x ∈ range M) y (hy : y ∈ range M) z (hz : z ∈ range M) w (hw : w ∈ range M) =>
    (residueCount_limit M hM [x,y,z,w] (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact mem_range.mp ‹_›)).const_mul (W x y z w : ℝ)
  have hh' := tendsto_finsetSum (range M) (fun x hx =>
    tendsto_finsetSum (range M) (fun y hy =>
    tendsto_finsetSum (range M) (fun z hz =>
    tendsto_finsetSum (range M) (fun w hw => hh x hx y hy z hz w hw))))
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hh'
  convert hh' using 1
  · funext N
    rw [masked_count_eq_cube M hM W hW]
    simp only [cube, Nat.cast_sum, Nat.cast_mul, sum_div, mul_div_assoc]
  · congr 1
    simp only [cube,Nat.cast_sum,←sum_mul]
    ring


private theorem cutoff_list (L : ℕ) (l : List ℕ) :
    (∑ j ∈ range L, rootWeight (layer j) l) ≤ rootWeight obstructionMask l ∧
    rootWeight obstructionMask l ≤ (∑ j ∈ range L, rootWeight (layer j) l) + rootWeight (tail L) l := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e,es⟩⟩⟩⟩⟩ <;>
    first | exact cutoff_bounds L a b c d | simp [rootWeight]

private theorem cutoff_count (L N : ℕ) :
    (∑ j ∈ range L, maskedCount (layer j) N) ≤ maskedCount obstructionMask N ∧
    maskedCount obstructionMask N ≤ (∑ j ∈ range L, maskedCount (layer j) N) + maskedCount (tail L) N := by
  have hlo := sum_le_sum (s := range (N+1)) (fun n _ => (cutoff_list L (roots n)).1)
  have hhi := sum_le_sum (s := range (N+1)) (fun n _ => (cutoff_list L (roots n)).2)
  rw [sum_add_distrib] at hhi
  rw [sum_comm] at hlo
  nth_rw 1 [sum_comm (s := range (N+1)) (t := range L)] at hhi
  exact ⟨hlo,hhi⟩

theorem masked_obstruction_limit :
    Tendsto (fun N : ℕ => (maskedCount obstructionMask N : ℝ)/(N:ℝ)^(exponent 4))
      atTop (𝓝 (volume 4 * (3/20))) := by
  apply by_dyadic_layers
  intro L
  let f := fun (W : Kernel) (N : ℕ) => (maskedCount W N:ℝ)/(N:ℝ)^(exponent 4)
  have hM : 0 < 2^L*16 := by positivity
  have ht : Tendsto (f (tail L)) atTop (𝓝 (volume 4*(1/16:ℝ)^L)) := by
    have ht' := masked_count_limit (2^L*16) hM (tail L) (tail_periodic L)
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, tail_mass] using ht'
  have hl (j : ℕ) (hj : j ∈ range L) :
      Tendsto (f (layer j)) atTop (𝓝 (volume 4*((9/64:ℝ)*(1/16:ℝ)^j))) := by
    have hj' := (mem_range.mp hj).le
    have hl' := masked_count_limit (2^L*16) hM (layer j) (layer_periodic j L hj')
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, layer_mass j L hj'] using hl'
  have hg := tendsto_finsetSum (range L) hl
  rw [←mul_sum] at hg
  refine ⟨fun N => ∑ j ∈ range L, f (layer j) N, f (tail L), hg, ht, ?_⟩
  apply Eventually.of_forall
  intro N
  obtain ⟨lo,hi⟩ := cutoff_count L N
  have den : 0 ≤ (N:ℝ)^(exponent 4) := Real.rpow_nonneg (by positivity) _
  simp only [f, ←sum_div, ←add_div]
  constructor <;> apply div_le_div_of_nonneg_right _ den
  · exact_mod_cast lo
  · exact_mod_cast hi

end A401548Squeeze

namespace A401548Optimal

open Finset OMA.S_oeis_a401548 A401548Counts A401548Density A401548Classification
open scoped Classical

private theorem roots_value (n : ℕ) : ((roots n).map (fun x => x^2)).sum = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [roots]
    | succ n =>
      have hs : (n+1).sqrt^2 ≤ n+1 := Nat.sqrt_le' _
      have hp : 0 < (n+1).sqrt^2 := pow_pos (Nat.sqrt_pos.mpr (by omega)) 2
      conv_lhs => rw [roots,List.map_cons,List.sum_cons]
      rw [ih _ (by omega), Nat.add_sub_of_le hs]

/-- The mask is applied only to tuples of exactly four greedy roots. -/
theorem four_weight (n : ℕ) :
    (match roots n with
    | [x,y,z,w] => obstructionMask x y z w
    | _ => 0) =
      if greedyLength n = 4 ∧ obstructed n then 1 else 0 := by
  have hl := roots_length n
  have hv := roots_value n
  match eq : roots n with
  | [x,y,z,w] =>
    have he : value x y z w = n := by
      simpa [eq,value,Nat.add_assoc] using hv
    simp [obstructionMask,← hl,eq,he]
  | [] => simp [← hl,eq]
  | [_] => simp [← hl,eq]
  | [_,_] => simp [← hl,eq]
  | [_,_,_] => simp [← hl,eq]
  | _ :: _ :: _ :: _ :: _ :: xs => simp [← hl,eq,List.length_cons]

/-- Four-root obstructions are optimal, and every remaining optimal input has at most three roots. -/
theorem count_bounds
    (legendre : ∀ n : ℕ, (¬ ∃ a b : ℕ, n=4^a*(8*b+7)) →
      ∃ x y z : ℕ, x^2+y^2+z^2=n) (N : ℕ) :
    count 4 N obstructed ≤ optimalCount N ∧
    optimalCount N ≤ count 4 N obstructed +
      ((range (N+1)).filter (fun n => greedyLength n ≤ 3)).card := by
  classical
  rw [count_eq_card]
  unfold optimalCount
  constructor
  · apply card_le_card
    intro n hn
    obtain ⟨hr,hg,ho⟩ := mem_filter.mp hn
    have hp : 1 ≤ n := by
      by_contra! h
      have hz : n=0 := by omega
      simp [hz,greedyLength] at hg
    have hm : n ≤ N := by have := mem_range.mp hr; omega
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp,hm⟩,(optimal_four_iff legendre n hg).mpr ho⟩
  · apply le_trans (card_le_card ?_) (card_union_le _ _)
    intro n hn
    obtain ⟨hi,ho⟩ := mem_filter.mp hn
    have hr : n ∈ range (N+1) := by
      have := (mem_Icc.mp hi).2
      exact mem_range.mpr (by omega)
    have hle := optimal_le_four n ho.2
    by_cases hg : greedyLength n = 4
    · exact mem_union.mpr (Or.inl (mem_filter.mpr
        ⟨hr,hg,(optimal_four_iff legendre n hg).mp ho⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hr,by omega⟩))

end A401548Optimal

namespace A401548Optimal

open Filter Topology Finset OMA.S_oeis_a401548
open A401548Counts A401548Density A401548Squeeze A401548Classification

private theorem obstruction_count (N : ℕ) : maskedCount obstructionMask N = count 4 N obstructed := by
  classical
  unfold maskedCount count
  apply sum_congr rfl
  intro n _
  have hw := four_weight n
  have hr : rootWeight obstructionMask (roots n) =
      (match roots n with | [x,y,z,w] => obstructionMask x y z w | _ => 0) := by
    generalize roots n = l
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e,es⟩⟩⟩⟩⟩ <;> rfl
  rw [hr]
  exact hw

/-- The leading term includes the limiting three-square obstruction among four greedy roots. -/
theorem explicit_limit :
    Tendsto (fun N : ℕ => (optimalCount N : ℝ) / (N : ℝ) ^ (15 / 16 : ℝ))
      atTop (𝓝 ((16/525:ℝ) * (2:ℝ)^(17/8:ℝ))) := by
  have coefficient : volume 4 * (3/20) = (16/525:ℝ)*(2:ℝ)^(17/8:ℝ) := by
    rw [volume_four]
    ring
  have hfour := masked_obstruction_limit
  simp only [obstruction_count,exponent_four,coefficient] at hfour
  have hupper := hfour.add shorter_count_limit
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hfour hupper
  · intro N
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact_mod_cast (count_bounds legendre N).1
  · intro N
    dsimp only
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact_mod_cast (count_bounds legendre N).2

end A401548Optimal

theorem OMA.solution : type_of% @OMA.S_oeis_a401548.main :=
  ⟨(16/525:ℝ)*(2:ℝ)^(17/8:ℝ),by positivity,A401548Optimal.explicit_limit⟩
