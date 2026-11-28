import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_8

/-! The p-adic Littlewood conjecture for quadratic irrationals via Pell's equation. -/

open Polynomial

theorem OMA.solution : type_of% @Bugeaud08.problem_10_8.variants.quadratic := by
  intro ξ p hp hξ
  have := Fact.mk hp
  have hint : IsIntegral ℚ ξ := by_contra fun hc => by rw [minpoly.eq_zero hc] at hξ; simp at hξ
  have h0 := minpoly.aeval ℚ ξ
  rw [aeval_eq_sum_range, hξ] at h0
  have h2 : (minpoly ℚ ξ).coeff 2 = 1 := by have := (minpoly.monic hint).leadingCoeff; rwa [leadingCoeff, hξ] at this
  let b := (minpoly ℚ ξ).coeff 1; let c := (minpoly ℚ ξ).coeff 0
  have hbc : ξ ^ 2 + (b : ℝ) * ξ + c = 0 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h2, Algebra.smul_def, eq_ratCast] at h0
    push_cast at h0; linear_combination h0
  have hirr (r : ℚ) : ξ ≠ r := fun h => by
    have := minpoly.eq_X_sub_C ℝ r; rw [eq_ratCast, ← h] at this; rw [this] at hξ; simp at hξ
  set δ : ℚ := b ^ 2 - 4 * c with hδ
  set d : ℕ := δ.den with hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast δ.pos
  set D : ℤ := δ.num * d with hD
  set θ : ℝ := (d : ℝ) * (2 * ξ + b) with hθ
  have hθsq : θ ^ 2 = D := by
    have hδd : (δ : ℝ) * d = δ.num := by exact_mod_cast Rat.mul_den_eq_num δ
    have : θ ^ 2 = (d : ℝ) * ((δ : ℝ) * d) := by
      simp only [hθ, hδ]; push_cast; linear_combination (4 * (d : ℝ) ^ 2) * hbc
    rw [this, hδd, hD]; push_cast; ring
  have hξθ : ξ = (θ / d - b) / 2 := by simp only [hθ]; field_simp; ring
  have hθrat (r : ℚ) : θ ≠ r := fun hr => hirr ((r / d - b) / 2) (by rw [hξθ, hr]; push_cast; ring)
  have hθpos : 0 < |θ| := abs_pos.2 (by simpa using hθrat 0)
  clear_value θ D d δ
  have hbden : (0 : ℝ) < b.den := by exact_mod_cast b.pos
  set S := {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧ x = q * padicNorm p q * distToNearestInt (q * ξ)}
  have hnn : ∀ x ∈ S, 0 ≤ x := by
    rintro _ ⟨q, -, rfl⟩
    have : (0 : ℝ) ≤ (padicNorm p (q : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
    have : 0 ≤ distToNearestInt (q * ξ) := abs_nonneg _
    positivity
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (le_csInf ⟨_, 1, le_rfl, rfl⟩ hnn)
  rw [zero_add]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * d * (b.den : ℝ) ^ 2 / (|θ| * ε))
    (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
  have hDpos : 0 < D := by exact_mod_cast (show (0 : ℝ) < D by rw [← hθsq, ← sq_abs]; positivity)
  have hnsq : ¬ IsSquare (D * (p : ℤ) ^ (2 * k)) := by
    rintro ⟨m, hm⟩
    have hm' : (|θ| * (p : ℝ) ^ k) ^ 2 = |(m : ℝ)| ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs, hθsq, ← pow_mul, mul_comm k 2]
      have : ((D * (p : ℤ) ^ (2 * k) : ℤ) : ℝ) = ((m * m : ℤ) : ℝ) := by rw [hm]
      push_cast at this; rw [this]; ring
    have hm2 : |θ| * (p : ℝ) ^ k = |(m : ℝ)| := (sq_eq_sq₀ (by positivity) (abs_nonneg _)).1 hm'
    have hθa : |θ| = (((((|m| : ℤ) : ℚ) / (p : ℚ) ^ k) : ℚ) : ℝ) := by
      have : (0 : ℝ) < (p : ℝ) ^ k := by exact_mod_cast pow_pos hp.pos k
      push_cast; rw [← hm2]; field_simp
    rcases abs_choice θ with h | h
    · exact hθrat _ (by rw [← h, hθa])
    · exact hθrat (-(((|m| : ℤ) : ℚ) / (p : ℚ) ^ k)) (by rw [show θ = -|θ| by linarith, hθa]; push_cast; ring)
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare (mul_pos hDpos (pow_pos (by exact_mod_cast hp.pos) _)) hnsq
  set N : ℕ := p ^ k * y.natAbs with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (Int.natAbs_ne_zero.2 hy))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hxN : (x : ℝ) ^ 2 - θ ^ 2 * (N : ℝ) ^ 2 = 1 := by
    have hNR : (N : ℝ) = (p : ℝ) ^ k * |(y : ℝ)| := by simp only [hN]; push_cast; simp [Nat.cast_natAbs]
    rw [hNR, mul_pow, sq_abs, hθsq]
    have : ((x ^ 2 - D * (p : ℤ) ^ (2 * k) * y ^ 2 : ℤ) : ℝ) = 1 := by rw [hxy]; simp
    push_cast at this; rw [← this, pow_mul]; ring
  have ⟨n, hn⟩ : ∃ n : ℤ, |θ * N - n| ≤ 1 / (|θ| * N) := by
    have hpos : 0 < |θ| * N := mul_pos hθpos hN0
    set u := (x : ℝ) - θ * N; set v := (x : ℝ) + θ * N
    have huv : u * v = 1 := by dsimp [u, v]; linear_combination hxN
    have habs : |u| * |v| = 1 := by rw [← abs_mul, huv]; simp
    have hsum : 2 * (|θ| * N) ≤ |u| + |v| := by
      have h1 : |v - u| ≤ |u| + |v| := (abs_sub _ _).trans_eq (add_comm _ _)
      rw [show v - u = 2 * (θ * N) by dsimp [u, v]; ring, abs_mul, abs_mul, abs_of_pos hN0] at h1
      simpa using h1
    rcases le_total (|θ| * N) |v| with hv | hv
    · refine ⟨x, ?_⟩; rw [abs_sub_comm, le_div_iff₀ hpos]; nlinarith [abs_nonneg u]
    · refine ⟨-x, ?_⟩
      have : |θ * N - ((-x : ℤ) : ℝ)| = |v| := by push_cast; dsimp [v]; ring_nf
      rw [this, le_div_iff₀ hpos]; nlinarith [abs_nonneg u, abs_nonneg v]
  set q : ℕ := 2 * d * b.den * N with hq
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by have : 0 < d := hd ▸ δ.pos; have := b.pos; positivity)
  refine csInf_le_of_le ⟨0, hnn⟩ ⟨q, hq1, rfl⟩ ?_
  have hpad : (padicNorm p (q : ℚ) : ℝ) ≤ ((p : ℝ) ^ k)⁻¹ := by
    have hdvd : ((p ^ k : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (by simp only [hq, hN]; exact Dvd.dvd.mul_left (dvd_mul_right _ _) _)
    have h' : (padicNorm p (q : ℚ) : ℝ) ≤ (((p : ℚ) ^ (-(k : ℤ)) : ℚ) : ℝ) := by
      exact_mod_cast padicNorm.dvd_iff_norm_le.1 hdvd
    simpa [zpow_neg] using h'
  have hdist : distToNearestInt (q * ξ) ≤ b.den / (|θ| * N) := by
    set m : ℤ := b.den * n - d * N * b.num
    have hqξ : (q : ℝ) * ξ - m = b.den * (θ * N - n) := by
      have hb : (b : ℝ) * b.den = b.num := by exact_mod_cast Rat.mul_den_eq_num b
      have h1 : (q : ℝ) * ξ = b.den * (θ * N) - d * N * ((b : ℝ) * b.den) := by
        rw [hξθ]; simp only [hq]; push_cast; field_simp
      rw [h1, hb]; simp only [m]; push_cast; ring
    calc distToNearestInt (q * ξ) ≤ |(q : ℝ) * ξ - m| := round_le _ _
      _ = b.den * |θ * N - n| := by rw [hqξ, abs_mul, abs_of_pos hbden]
      _ ≤ b.den * (1 / (|θ| * N)) := by gcongr
      _ = b.den / (|θ| * N) := by ring
  have hpn : (0 : ℝ) ≤ (padicNorm p (q : ℚ) : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have hdn : 0 ≤ distToNearestInt (q * ξ) := abs_nonneg _
  have hqR : (q : ℝ) = 2 * d * b.den * N := by simp only [hq]; push_cast; ring
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by exact_mod_cast pow_pos hp.pos k
  calc (q : ℝ) * (padicNorm p (q : ℚ) : ℝ) * distToNearestInt (q * ξ)
      ≤ (q : ℝ) * ((p : ℝ) ^ k)⁻¹ * (b.den / (|θ| * N)) := by gcongr
    _ = 2 * d * (b.den : ℝ) ^ 2 / (|θ| * (p : ℝ) ^ k) := by rw [hqR]; field_simp
    _ ≤ ε := by rw [div_le_iff₀ (by positivity)]; rw [div_lt_iff₀ (by positivity)] at hk; nlinarith
