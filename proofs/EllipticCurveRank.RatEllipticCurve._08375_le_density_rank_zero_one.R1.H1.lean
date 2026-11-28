import OMAReductions.R_EllipticCurveRank_RatEllipticCurve__08375_le_density_rank_zero_one_R1

/-!
# Proof of `EllipticCurveRank.RatEllipticCurve._08375_le_density_rank_zero_one.R1.H1`

For every `H ≥ 4`, the set `heightLE H` of reduced rational elliptic curves with naïve height at
most `H` is finite (since `(E.A, E.B)` injects `RatEllipticCurve` into `[-H, H] × [-H, H]`) and
nonempty (witnessed by `y² = x³ + x`, which has naïve height `4`).
-/

open Filter EllipticCurveRank EllipticCurveRank.RatEllipticCurve

private def baseCurve : RatEllipticCurve where
  A := 1
  B := 0
  reduced p hp := by
    rintro ⟨hA, -⟩
    have h1 : p ^ 4 ∣ 1 := by
      have := Int.natAbs_dvd_natAbs.mpr hA
      simpa using this
    have hle : p ^ 4 ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith [pow_le_pow_left₀ (by norm_num) hp2 4]
  Δ_ne_zero := by norm_num

private lemma heightLE_finite (H : ℕ) : (heightLE H).Finite := by
  let f : RatEllipticCurve → ℤ × ℤ := fun E => (E.A, E.B)
  have hf : Function.Injective f := by
    intro E₁ E₂ h
    cases E₁
    cases E₂
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  let box : Set (ℤ × ℤ) := Set.Icc (-(H : ℤ)) (H : ℤ) ×ˢ Set.Icc (-(H : ℤ)) (H : ℤ)
  have hbox : box.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  have hsub : heightLE H ⊆ f ⁻¹' box := by
    intro E hE
    simp only [heightLE, Set.mem_setOf_eq, naiveHeight, max_le_iff] at hE
    have hA : E.A.natAbs ≤ H := by
      have : E.A.natAbs ≤ E.A.natAbs ^ 3 := Nat.le_self_pow (by norm_num) _
      omega
    have hB : E.B.natAbs ≤ H := by
      have : E.B.natAbs ≤ E.B.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    have hAz : -(H : ℤ) ≤ E.A ∧ E.A ≤ (H : ℤ) := by
      have := abs_le.mp (show |E.A| ≤ (H : ℤ) by rw [← Int.natCast_natAbs]; exact_mod_cast hA)
      exact this
    have hBz : -(H : ℤ) ≤ E.B ∧ E.B ≤ (H : ℤ) := by
      have := abs_le.mp (show |E.B| ≤ (H : ℤ) by rw [← Int.natCast_natAbs]; exact_mod_cast hB)
      exact this
    exact ⟨hAz, hBz⟩
  exact (hbox.preimage hf.injOn).subset hsub

theorem OMA.solution :
    OMA.R_EllipticCurveRank_RatEllipticCurve__08375_le_density_rank_zero_one_R1.H1 := by
  refine Filter.eventually_atTop.mpr ⟨4, fun H hH => ?_⟩
  refine ⟨heightLE_finite H, ⟨baseCurve, ?_⟩⟩
  show baseCurve.naiveHeight ≤ H
  have h4 : baseCurve.naiveHeight = 4 := by decide
  omega
