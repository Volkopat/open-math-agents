import OMAStatements.S_oeis_a010503

/-!
# Proof of OEIS A010503: `∑' k, c(k) / exp (k * π) = 1 / √2`

1. Define the real theta functions `θ₃(t) = ∑' n : ℤ, exp (-t n²)`,
   `θ₄(t) = ∑' n : ℤ, (-1)^|n| exp (-t n²)`, `θ₂(t) = ∑' n : ℤ, exp (-t (n + 1/2)²)`.
2. From `jacobiTheta_S_smul` at `τ = 4i`, `θ₃(π/4) = 2 θ₃(4π)`. Splitting `ℤ` into even and odd
   integers gives `θ₃(π/4) = θ₃(π) + θ₂(π)` and `θ₃(π) + θ₄(π) = 2 θ₃(4π)`, hence `θ₂(π) = θ₄(π)`.
3. Splitting `ℤ × ℤ` by parity of `x + y` via `(u, v) ↦ (u + v, u - v)` and `(u + v + 1, u - v)`
   yields `θ₃(t)² + θ₄(t)² = 2 θ₃(2t)²`, `θ₃(t)² - θ₄(t)² = 2 θ₂(2t)²`, and
   `θ₂(t)² = 2 θ₃(2t) θ₂(2t)`, hence Jacobi's identity `θ₃(t)⁴ = θ₂(t)⁴ + θ₄(t)⁴`.
   At `t = π` this gives `θ₃(π)⁴ = 2 θ₄(π)⁴`, so `θ₃(π)² / θ₄(π)² = √2`.
4. Grouping `ℤ × ℤ` by `k = x² + y²` gives `∑' k, r₃(k) q^k = θ₃(π)²` and
   `∑' k, r₄(k) q^k = θ₄(π)²` at `q = exp (-π)`. Since `q < 1/10`, `M = θ₃(π)² - 1 < 1/2`, and
   the partial sums `S_N = ∑_{k ≤ N} |b(k)| q^k` satisfy `S_N ≤ 1 + M + M S_N`, so `S_N ≤ 3`.
   Thus `b(k) q^k` is absolutely summable, and the Cauchy product gives
   `(∑' k, b(k) q^k) * θ₄(π)² = θ₃(π)²`, i.e., `∑' k, b(k) / exp (k * π) = √2`.
-/

namespace OMA.OeisA010503Proof

open Real Finset OMA.S_oeis_a010503

private noncomputable def θ₃ (t : ℝ) : ℝ := ∑' n : ℤ, exp (-t * (n : ℝ) ^ 2)
private noncomputable def θ₄ (t : ℝ) : ℝ := ∑' n : ℤ, (-1 : ℝ) ^ n.natAbs * exp (-t * (n : ℝ) ^ 2)
private noncomputable def θ₂ (t : ℝ) : ℝ := ∑' n : ℤ, exp (-t * ((n : ℝ) + 1 / 2) ^ 2)

private lemma summable_exp_neg_sq {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => exp (-t * (n : ℝ) ^ 2)) := by
  have hgeom : Summable (fun m : ℕ => (exp (-t)) ^ m) :=
    summable_geometric_of_lt_one (exp_pos _).le (exp_lt_one_iff.mpr (by linarith))
  have hnat : Summable (fun m : ℕ => exp (-t * (m : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) (fun m => ?_) hgeom
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      rcases m with _ | m
      · simp
      · have h1 : (1 : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos m
        push_cast
        nlinarith
    nlinarith
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hnat, ?_⟩
  have : (fun m : ℕ => exp (-t * ((-(m : ℤ) : ℤ) : ℝ) ^ 2)) =
      (fun m : ℕ => exp (-t * (m : ℝ) ^ 2)) := by
    ext m; push_cast; ring_nf
  rw [this]
  exact hnat

private lemma summable_θ₄ {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => (-1 : ℝ) ^ n.natAbs * exp (-t * (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded (summable_exp_neg_sq ht) fun n => ?_
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_of_nonneg (exp_pos _).le]

private lemma summable_θ₂ {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => exp (-t * ((n : ℝ) + 1 / 2) ^ 2)) := by
  have hgeom : Summable (fun m : ℕ => (exp (-t)) ^ m) :=
    summable_geometric_of_lt_one (exp_pos _).le (exp_lt_one_iff.mpr (by linarith))
  have hpos : Summable (fun m : ℕ => exp (-t * ((m : ℝ) + 1 / 2) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) (fun m => ?_) hgeom
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    have hm : (m : ℝ) ≤ ((m : ℝ) + 1 / 2) ^ 2 := by nlinarith
    nlinarith
  have hneg : Summable (fun m : ℕ => exp (-t * ((-(m : ℤ) : ℝ) + 1 / 2) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) (fun m => ?_)
      (hgeom.mul_left (exp t))
    rw [← exp_nat_mul, ← exp_add]
    apply exp_le_exp.mpr
    have hm : (m : ℝ) - 1 ≤ (-(m : ℝ) + 1 / 2) ^ 2 := by nlinarith
    push_cast
    nlinarith
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨by simpa using hpos, by simpa using hneg⟩

private def intEvenOddEquiv : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun k => 2 * k) (fun k => 2 * k + 1)
  invFun := fun n => if n % 2 = 0 then Sum.inl (n / 2) else Sum.inr (n / 2)
  left_inv := fun x => by
    cases x with
    | inl k => simp
    | inr k => simp [Int.add_ediv_of_dvd_left]
  right_inv := fun n => by
    dsimp only
    split_ifs with h <;> simp <;> omega

private lemma tsum_sum_same {α : Type*} {f : α ⊕ α → ℝ} (hf : Summable f) :
    ∑' x : α ⊕ α, f x = (∑' a : α, f (Sum.inl a)) + (∑' b : α, f (Sum.inr b)) := by
  have h1 : Summable (fun a : α => f (Sum.inl a)) := hf.comp_injective Sum.inl_injective
  have h2 : Summable (fun b : α => f (Sum.inr b)) := hf.comp_injective Sum.inr_injective
  have hsig : Summable (fun p : (b : Bool) × cond b α α => f ((Equiv.sumEquivSigmaBool α α).symm p)) :=
    hf.comp_injective (Equiv.sumEquivSigmaBool α α).symm.injective
  rw [← (Equiv.sumEquivSigmaBool α α).symm.tsum_eq,
    hsig.tsum_sigma' (fun b => by cases b <;> simpa using ‹_›),
    tsum_fintype, Fintype.sum_bool]
  simp [Equiv.sumEquivSigmaBool, add_comm]

private lemma tsum_int_even_odd {f : ℤ → ℝ} (hf : Summable f) :
    ∑' n : ℤ, f n = (∑' k : ℤ, f (2 * k)) + (∑' k : ℤ, f (2 * k + 1)) := by
  rw [← intEvenOddEquiv.tsum_eq]
  have hsum : Summable (f ∘ intEvenOddEquiv) := hf.comp_injective intEvenOddEquiv.injective
  simpa [Function.comp_def, intEvenOddEquiv] using tsum_sum_same hsum

private lemma θ₃_div_four : θ₃ (π / 4) = θ₃ π + θ₂ π := by
  unfold θ₃ θ₂
  rw [tsum_int_even_odd (summable_exp_neg_sq (by positivity))]
  congr 1
  · refine tsum_congr fun k => ?_; push_cast; congr 1; ring
  · refine tsum_congr fun k => ?_; push_cast; congr 1; ring

private lemma θ₃_add_θ₄ : θ₃ π + θ₄ π = 2 * θ₃ (4 * π) := by
  unfold θ₃ θ₄
  have h3 := tsum_int_even_odd (summable_exp_neg_sq pi_pos)
  have h4 := tsum_int_even_odd (summable_θ₄ pi_pos)
  have heven : ∀ k : ℤ, (-1 : ℝ) ^ (2 * k).natAbs = 1 := by
    intro k
    have : Even (2 * k).natAbs := by
      rw [Nat.even_iff]; omega
    exact this.neg_one_pow
  have hodd : ∀ k : ℤ, (-1 : ℝ) ^ (2 * k + 1).natAbs = -1 := by
    intro k
    have : Odd (2 * k + 1).natAbs := by
      rw [Nat.odd_iff]; omega
    exact this.neg_one_pow
  have h4_eq : (∑' k : ℤ, (-1 : ℝ) ^ (2 * k).natAbs * exp (-π * ((2 * k : ℤ) : ℝ) ^ 2)) =
      ∑' k : ℤ, exp (-4 * π * (k : ℝ) ^ 2) := by
    refine tsum_congr fun k => ?_
    rw [heven k, one_mul]; push_cast; congr 1; ring
  have h4_odd : (∑' k : ℤ, (-1 : ℝ) ^ (2 * k + 1).natAbs * exp (-π * ((2 * k + 1 : ℤ) : ℝ) ^ 2)) =
      -(∑' k : ℤ, exp (-π * ((2 * k + 1 : ℤ) : ℝ) ^ 2)) := by
    rw [← tsum_neg]
    refine tsum_congr fun k => ?_
    rw [hodd k, neg_one_mul]
  have h3_even : (∑' k : ℤ, exp (-π * ((2 * k : ℤ) : ℝ) ^ 2)) =
      ∑' k : ℤ, exp (-4 * π * (k : ℝ) ^ 2) := by
    refine tsum_congr fun k => ?_; push_cast; congr 1; ring
  rw [h3, h4, h3_even, h4_eq, h4_odd]
  ring

private lemma jacobiTheta_ofReal_I {t : ℝ} :
    jacobiTheta ((t : ℂ) * Complex.I) = (θ₃ (π * t) : ℂ) := by
  unfold jacobiTheta θ₃
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (π : ℂ) * (n : ℂ) ^ 2 * (t : ℂ) * hI

private lemma θ₃_quarter_eq_two_mul : θ₃ (π / 4) = 2 * θ₃ (4 * π) := by
  let τ : UpperHalfPlane := ⟨4 * Complex.I, by simp⟩
  have hS := jacobiTheta_S_smul τ
  have hS_val : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = ((1 / 4 : ℝ) : ℂ) * Complex.I := by
    rw [UpperHalfPlane.modular_S_smul]
    simp only [τ]
    push_cast
    field_simp
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination -hI
  have hmul : (-Complex.I * (τ : ℂ)) = (4 : ℂ) := by
    simp only [τ]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination -4 * hI
  have hpow : (4 : ℂ) ^ (1 / 2 : ℂ) = (2 : ℂ) := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 4)]
    have : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow]
      norm_num
    rw [this]; norm_num
  rw [hS_val, hmul, hpow] at hS
  have hτ_val : (τ : ℂ) = ((4 : ℝ) : ℂ) * Complex.I := by simp [τ]
  rw [hτ_val, jacobiTheta_ofReal_I, jacobiTheta_ofReal_I] at hS
  have hreal : θ₃ (π * (1 / 4)) = 2 * θ₃ (π * 4) := by
    exact_mod_cast hS
  have h1 : π * (1 / 4) = π / 4 := by ring
  have h2 : π * 4 = 4 * π := by ring
  rwa [h1, h2] at hreal

private lemma θ₂_eq_θ₄ : θ₂ π = θ₄ π := by
  have h1 := θ₃_div_four
  have h2 := θ₃_add_θ₄
  have h3 := θ₃_quarter_eq_two_mul
  linarith

private def intProdParityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun p => (p.1 + p.2, p.1 - p.2)) (fun p => (p.1 + p.2 + 1, p.1 - p.2))
  invFun := fun p =>
    if (p.1 + p.2) % 2 = 0 then Sum.inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
    else Sum.inr ((p.1 + p.2 - 1) / 2, (p.1 - p.2 - 1) / 2)
  left_inv := fun x => by
    cases x with
    | inl p =>
      rcases p with ⟨u, v⟩
      dsimp only [Sum.elim_inl]
      rw [if_pos (by omega)]
      congr 1; ext <;> omega
    | inr p =>
      rcases p with ⟨u, v⟩
      dsimp only [Sum.elim_inr]
      rw [if_neg (by omega)]
      congr 1; ext <;> omega
  right_inv := fun ⟨x, y⟩ => by
    dsimp only
    split_ifs with h <;> simp <;> omega

private lemma tsum_intProd_parity {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    ∑' p : ℤ × ℤ, f p =
      (∑' p : ℤ × ℤ, f (p.1 + p.2, p.1 - p.2)) +
      (∑' p : ℤ × ℤ, f (p.1 + p.2 + 1, p.1 - p.2)) := by
  rw [← intProdParityEquiv.tsum_eq]
  have hsum : Summable (f ∘ intProdParityEquiv) := hf.comp_injective intProdParityEquiv.injective
  simpa [Function.comp_def, intProdParityEquiv] using tsum_sum_same hsum

private lemma tsum_fiberwise_real {α β : Type*} {f : α → ℝ} (hf : Summable f) (g : α → β) :
    ∑' b : β, ∑' x : g ⁻¹' {b}, f x.1 = ∑' a : α, f a := by
  have hsig : Summable (fun p : (b : β) × {a : α // g a = b} => f p.2.1) :=
    hf.comp_injective (Equiv.sigmaFiberEquiv g).injective
  have h1 : ∑' p : (b : β) × {a : α // g a = b}, f p.2.1 = ∑' a : α, f a :=
    (Equiv.sigmaFiberEquiv g).tsum_eq f
  rw [← h1, hsig.tsum_sigma' (fun b => hf.comp_injective Subtype.val_injective)]
  rfl

private lemma neg_one_pow_natAbs_add (x y : ℤ) :
    (-1 : ℝ) ^ x.natAbs * (-1 : ℝ) ^ y.natAbs = (-1 : ℝ) ^ (x + y).natAbs := by
  rw [← pow_add]
  have hmod : (x.natAbs + y.natAbs) % 2 = (x + y).natAbs % 2 := by omega
  rcases Nat.even_or_odd (x + y).natAbs with h | h
  · have h1 : Even (x.natAbs + y.natAbs) := by
      rw [Nat.even_iff] at h ⊢; omega
    rw [h.neg_one_pow, h1.neg_one_pow]
  · have h1 : Odd (x.natAbs + y.natAbs) := by
      rw [Nat.odd_iff] at h ⊢; omega
    rw [h.neg_one_pow, h1.neg_one_pow]

private lemma θ₃_sq_eq {t : ℝ} (ht : 0 < t) :
    θ₃ t ^ 2 = ∑' p : ℤ × ℤ, exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hs3 := summable_exp_neg_sq ht
  have hnn3 : ∀ n : ℤ, 0 ≤ exp (-t * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  rw [sq, θ₃, hs3.tsum_mul_tsum hs3 (hs3.mul_of_nonneg hs3 hnn3 hnn3)]
  refine tsum_congr fun ⟨x, y⟩ => ?_
  rw [← exp_add]; congr 1; ring

private lemma θ₄_sq_eq {t : ℝ} (ht : 0 < t) :
    θ₄ t ^ 2 = ∑' p : ℤ × ℤ, (-1 : ℝ) ^ (p.1 + p.2).natAbs *
      exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hs3 := summable_exp_neg_sq ht
  have hs4 := summable_θ₄ ht
  have hnn3 : ∀ n : ℤ, 0 ≤ exp (-t * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  have hmul : Summable (fun p : ℤ × ℤ =>
      ((-1 : ℝ) ^ p.1.natAbs * exp (-t * (p.1 : ℝ) ^ 2)) *
      ((-1 : ℝ) ^ p.2.natAbs * exp (-t * (p.2 : ℝ) ^ 2))) :=
    Summable.of_norm_bounded (hs3.mul_of_nonneg hs3 hnn3 hnn3) fun ⟨x, y⟩ => by
      simp [norm_mul, norm_pow, abs_of_pos (exp_pos _)]
  rw [sq, θ₄, hs4.tsum_mul_tsum hs4 hmul]
  refine tsum_congr fun ⟨x, y⟩ => ?_
  calc ((-1 : ℝ) ^ x.natAbs * exp (-t * (x : ℝ) ^ 2)) *
        ((-1 : ℝ) ^ y.natAbs * exp (-t * (y : ℝ) ^ 2))
      = ((-1 : ℝ) ^ x.natAbs * (-1 : ℝ) ^ y.natAbs) *
          (exp (-t * (x : ℝ) ^ 2) * exp (-t * (y : ℝ) ^ 2)) := by ring
    _ = (-1 : ℝ) ^ (x + y).natAbs * exp (-t * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2)) := by
        rw [neg_one_pow_natAbs_add, ← exp_add]; congr 2; ring

private lemma θ₃_sq_add_sub_θ₄_sq {t : ℝ} (ht : 0 < t) :
    θ₃ t ^ 2 + θ₄ t ^ 2 = 2 * θ₃ (2 * t) ^ 2 ∧
    θ₃ t ^ 2 - θ₄ t ^ 2 = 2 * θ₂ (2 * t) ^ 2 := by
  have hs3 := summable_exp_neg_sq ht
  have hs3_2 := summable_exp_neg_sq (by linarith : 0 < 2 * t)
  have hs2_2 := summable_θ₂ (by linarith : 0 < 2 * t)
  have hnn3 : ∀ n : ℤ, 0 ≤ exp (-t * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  have hnn3_2 : ∀ n : ℤ, 0 ≤ exp (-(2 * t) * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  have hnn2_2 : ∀ n : ℤ, 0 ≤ exp (-(2 * t) * ((n : ℝ) + 1 / 2) ^ 2) := fun _ => (exp_pos _).le
  have h3_prod_summ : Summable (fun p : ℤ × ℤ => exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    have : (fun p : ℤ × ℤ => exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
        fun p => exp (-t * (p.1 : ℝ) ^ 2) * exp (-t * (p.2 : ℝ) ^ 2) := by
      ext ⟨x, y⟩; rw [← exp_add]; congr 1; ring
    rw [this]; exact hs3.mul_of_nonneg hs3 hnn3 hnn3
  have h4_prod_summ : Summable (fun p : ℤ × ℤ => (-1 : ℝ) ^ (p.1 + p.2).natAbs *
      exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) :=
    Summable.of_norm_bounded h3_prod_summ fun ⟨x, y⟩ => by
      simp [norm_mul, norm_pow, abs_of_pos (exp_pos _)]
  have h32sq : θ₃ (2 * t) ^ 2 = ∑' p : ℤ × ℤ, exp (-t * (((p.1 + p.2 : ℤ) : ℝ) ^ 2 + ((p.1 - p.2 : ℤ) : ℝ) ^ 2)) := by
    rw [sq, θ₃, hs3_2.tsum_mul_tsum hs3_2 (hs3_2.mul_of_nonneg hs3_2 hnn3_2 hnn3_2)]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    rw [← exp_add]; push_cast; congr 1; ring
  have h22sq : θ₂ (2 * t) ^ 2 = ∑' p : ℤ × ℤ, exp (-t * (((p.1 + p.2 + 1 : ℤ) : ℝ) ^ 2 + ((p.1 - p.2 : ℤ) : ℝ) ^ 2)) := by
    rw [sq, θ₂, hs2_2.tsum_mul_tsum hs2_2 (hs2_2.mul_of_nonneg hs2_2 hnn2_2 hnn2_2)]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    rw [← exp_add]; push_cast; congr 1; ring
  have h3_split := tsum_intProd_parity h3_prod_summ
  have h4_split := tsum_intProd_parity h4_prod_summ
  have h4_even : (∑' p : ℤ × ℤ, (-1 : ℝ) ^ ((p.1 + p.2) + (p.1 - p.2)).natAbs *
      exp (-t * (((p.1 + p.2 : ℤ) : ℝ) ^ 2 + ((p.1 - p.2 : ℤ) : ℝ) ^ 2))) = θ₃ (2 * t) ^ 2 := by
    rw [h32sq]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    have hev : Even ((u + v) + (u - v)).natAbs := by
      rw [show (u + v) + (u - v) = 2 * u by ring, Int.natAbs_mul]; simp
    rw [hev.neg_one_pow, one_mul]
  have h4_odd : (∑' p : ℤ × ℤ, (-1 : ℝ) ^ ((p.1 + p.2 + 1) + (p.1 - p.2)).natAbs *
      exp (-t * (((p.1 + p.2 + 1 : ℤ) : ℝ) ^ 2 + ((p.1 - p.2 : ℤ) : ℝ) ^ 2))) = -θ₂ (2 * t) ^ 2 := by
    rw [h22sq, ← tsum_neg]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    have hod : Odd ((u + v + 1) + (u - v)).natAbs := by
      rw [Nat.odd_iff]; omega
    rw [hod.neg_one_pow, neg_one_mul]
  rw [θ₃_sq_eq ht, θ₄_sq_eq ht, h3_split, h4_split, ← h32sq, ← h22sq, h4_even, h4_odd]
  constructor <;> ring

private lemma θ₂_sq_odd {t : ℝ} (ht : 0 < t) :
    (∑' p : ℤ × ℤ, exp (-t * ((((p.1 + p.2 + 1 : ℤ) : ℝ) + 1 / 2) ^ 2 +
      (((p.1 - p.2 : ℤ) : ℝ) + 1 / 2) ^ 2))) = θ₃ (2 * t) * θ₂ (2 * t) := by
  have hs3_2 := summable_exp_neg_sq (by linarith : 0 < 2 * t)
  have hs2_2 := summable_θ₂ (by linarith : 0 < 2 * t)
  have hnn2_2 : ∀ n : ℤ, 0 ≤ exp (-(2 * t) * ((n : ℝ) + 1 / 2) ^ 2) := fun _ => (exp_pos _).le
  have hsh1 : Summable (fun u : ℤ => exp (-(2 * t) * (((u + 1 : ℤ) : ℝ)) ^ 2)) :=
    hs3_2.comp_injective (Equiv.addRight (1 : ℤ)).injective
  have hmul : Summable (fun p : ℤ × ℤ =>
      exp (-(2 * t) * (((p.1 + 1 : ℤ) : ℝ)) ^ 2) * exp (-(2 * t) * ((p.2 : ℝ) + 1 / 2) ^ 2)) :=
    hsh1.mul_of_nonneg hs2_2 (fun _ => (exp_pos _).le) hnn2_2
  have hshift : (∑' p : ℤ × ℤ, exp (-t * ((((p.1 + p.2 + 1 : ℤ) : ℝ) + 1 / 2) ^ 2 +
      (((p.1 - p.2 : ℤ) : ℝ) + 1 / 2) ^ 2))) =
      ∑' p : ℤ × ℤ, exp (-(2 * t) * (((p.1 + 1 : ℤ) : ℝ)) ^ 2) *
        exp (-(2 * t) * ((p.2 : ℝ) + 1 / 2) ^ 2) := by
    refine tsum_congr fun ⟨u, v⟩ => ?_
    rw [← exp_add]; push_cast; congr 1; ring
  rw [hshift, ← hsh1.tsum_mul_tsum hs2_2 hmul]
  unfold θ₃ θ₂
  congr 1
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun u : ℤ => exp (-(2 * t) * (u : ℝ) ^ 2))

private lemma θ₂_sq_eq {t : ℝ} (ht : 0 < t) :
    θ₂ t ^ 2 = 2 * θ₃ (2 * t) * θ₂ (2 * t) := by
  have hs2 := summable_θ₂ ht
  have hs3_2 := summable_exp_neg_sq (by linarith : 0 < 2 * t)
  have hs2_2 := summable_θ₂ (by linarith : 0 < 2 * t)
  have hnn2 : ∀ n : ℤ, 0 ≤ exp (-t * ((n : ℝ) + 1 / 2) ^ 2) := fun _ => (exp_pos _).le
  have hnn3_2 : ∀ n : ℤ, 0 ≤ exp (-(2 * t) * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  have hnn2_2 : ∀ n : ℤ, 0 ≤ exp (-(2 * t) * ((n : ℝ) + 1 / 2) ^ 2) := fun _ => (exp_pos _).le
  have h2sq : θ₂ t ^ 2 = ∑' p : ℤ × ℤ, exp (-t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
    rw [sq, θ₂, hs2.tsum_mul_tsum hs2 (hs2.mul_of_nonneg hs2 hnn2 hnn2)]
    refine tsum_congr fun ⟨x, y⟩ => ?_
    rw [← exp_add]; congr 1; ring
  have h2_prod_summ : Summable (fun p : ℤ × ℤ =>
      exp (-t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2))) := by
    have : (fun p : ℤ × ℤ => exp (-t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2))) =
        fun p => exp (-t * ((p.1 : ℝ) + 1 / 2) ^ 2) * exp (-t * ((p.2 : ℝ) + 1 / 2) ^ 2) := by
      ext ⟨x, y⟩; rw [← exp_add]; congr 1; ring
    rw [this]; exact hs2.mul_of_nonneg hs2 hnn2 hnn2
  have h2_split := tsum_intProd_parity h2_prod_summ
  have h2_even : (∑' p : ℤ × ℤ, exp (-t * ((((p.1 + p.2 : ℤ) : ℝ) + 1 / 2) ^ 2 +
      (((p.1 - p.2 : ℤ) : ℝ) + 1 / 2) ^ 2))) = θ₂ (2 * t) * θ₃ (2 * t) := by
    rw [θ₂, θ₃, hs2_2.tsum_mul_tsum hs3_2 (hs2_2.mul_of_nonneg hs3_2 hnn2_2 hnn3_2)]
    refine tsum_congr fun ⟨u, v⟩ => ?_
    rw [← exp_add]; push_cast; congr 1; ring
  rw [h2sq, h2_split, h2_even, θ₂_sq_odd ht]
  ring

private lemma jacobi_quartic {t : ℝ} (ht : 0 < t) :
    θ₃ t ^ 4 = θ₂ t ^ 4 + θ₄ t ^ 4 := by
  obtain ⟨hsum34, hsub34⟩ := θ₃_sq_add_sub_θ₄_sq ht
  have h2_eq := θ₂_sq_eq ht
  have h4_eq : θ₃ t ^ 4 - θ₄ t ^ 4 = (θ₃ t ^ 2 + θ₄ t ^ 2) * (θ₃ t ^ 2 - θ₄ t ^ 2) := by ring
  rw [hsum34, hsub34] at h4_eq
  have : θ₂ t ^ 4 = (θ₂ t ^ 2) ^ 2 := by ring
  rw [this, h2_eq]
  linarith

private lemma θ₃_pos : 0 < θ₃ π := by
  unfold θ₃
  have hs := summable_exp_neg_sq pi_pos
  have hle := Summable.le_tsum hs 0 (fun _ _ => (exp_pos _).le)
  have h0 : exp (-π * ((0 : ℤ) : ℝ) ^ 2) = 1 := by simp
  rw [h0] at hle
  linarith

private lemma θ₄_pos : 0 < θ₄ π := by
  rw [← θ₂_eq_θ₄]
  unfold θ₂
  have hs := summable_θ₂ pi_pos
  have hle := Summable.le_tsum hs 0 (fun _ _ => (exp_pos _).le)
  have h0 : 0 < exp (-π * (((0 : ℤ) : ℝ) + 1 / 2) ^ 2) := exp_pos _
  linarith

private lemma θ₃_sq_div_θ₄_sq : θ₃ π ^ 2 / θ₄ π ^ 2 = √2 := by
  have hjac := jacobi_quartic pi_pos
  rw [θ₂_eq_θ₄] at hjac
  have hsq : (θ₃ π ^ 2 / θ₄ π ^ 2) ^ 2 = 2 := by
    have h4 : θ₄ π ^ 2 ≠ 0 := (pow_pos θ₄_pos 2).ne'
    rw [div_pow]
    rw [div_eq_iff (pow_ne_zero 2 h4)]
    linarith
  have hnonneg : 0 ≤ θ₃ π ^ 2 / θ₄ π ^ 2 := by positivity
  rw [← Real.sqrt_sq hnonneg, hsq]

private lemma fiber_eq_reps (k : ℕ) :
    ((fun p : ℤ × ℤ => p.1.natAbs ^ 2 + p.2.natAbs ^ 2) ⁻¹' {k}) = (reps k : Set (ℤ × ℤ)) := by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe, reps, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h
    have hsq : x ^ 2 + y ^ 2 = (k : ℤ) := by
      have hx : (x.natAbs : ℤ) ^ 2 = x ^ 2 := Int.natAbs_sq x
      have hy : (y.natAbs : ℤ) ^ 2 = y ^ 2 := Int.natAbs_sq y
      have hk : (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast h
      linarith
    have hxk : -(k : ℤ) ≤ x ∧ x ≤ k := by
      have h1 : x ^ 2 ≤ k := by nlinarith
      constructor <;> nlinarith
    have hyk : -(k : ℤ) ≤ y ∧ y ≤ k := by
      have h1 : y ^ 2 ≤ k := by nlinarith
      constructor <;> nlinarith
    exact ⟨⟨hxk, hyk⟩, hsq⟩
  · intro ⟨_, hsq⟩
    have : ((x.natAbs ^ 2 + y.natAbs ^ 2 : ℕ) : ℤ) = (k : ℤ) := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Int.natAbs_sq, Int.natAbs_sq]
      exact hsq
    exact_mod_cast this

private lemma tsum_r₃ : ∑' k : ℕ, (r₃ k : ℝ) * exp (-π) ^ k = θ₃ π ^ 2 := by
  have hs3 := summable_exp_neg_sq pi_pos
  have hnn3 : ∀ n : ℤ, 0 ≤ exp (-π * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  have hprod : Summable (fun p : ℤ × ℤ => exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    have : (fun p : ℤ × ℤ => exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
        fun p => exp (-π * (p.1 : ℝ) ^ 2) * exp (-π * (p.2 : ℝ) ^ 2) := by
      ext ⟨x, y⟩; rw [← exp_add]; congr 1; ring
    rw [this]; exact hs3.mul_of_nonneg hs3 hnn3 hnn3
  rw [θ₃_sq_eq pi_pos]
  let g : ℤ × ℤ → ℕ := fun p => p.1.natAbs ^ 2 + p.2.natAbs ^ 2
  rw [← tsum_fiberwise_real hprod g]
  refine tsum_congr fun k => ?_
  have hfib := fiber_eq_reps k
  rw [tsum_congr_set_coe (f := fun p : ℤ × ℤ => exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) hfib,
    tsum_fintype]
  have hsum : (∑ p : (reps k : Set (ℤ × ℤ)), exp (-π * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2))) =
      ∑ _p : (reps k : Set (ℤ × ℤ)), exp (-π) ^ k := by
    refine Finset.sum_congr rfl fun ⟨⟨x, y⟩, hmem⟩ _ => ?_
    simp only [Finset.mem_coe, reps, Finset.mem_filter] at hmem
    have hsq : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = (k : ℝ) := by exact_mod_cast hmem.2
    rw [hsq, ← exp_nat_mul]; congr 1; ring
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (reps k : Set (ℤ × ℤ)) = (reps k).card := Fintype.card_coe (reps k)
  rw [hcard]
  rfl

private lemma summable_r₃ : Summable (fun k : ℕ => (r₃ k : ℝ) * exp (-π) ^ k) := by
  have hs3 := summable_exp_neg_sq pi_pos
  have hnn3 : ∀ n : ℤ, 0 ≤ exp (-π * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  have hprod : Summable (fun p : ℤ × ℤ => exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    have : (fun p : ℤ × ℤ => exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
        fun p => exp (-π * (p.1 : ℝ) ^ 2) * exp (-π * (p.2 : ℝ) ^ 2) := by
      ext ⟨x, y⟩; rw [← exp_add]; congr 1; ring
    rw [this]; exact hs3.mul_of_nonneg hs3 hnn3 hnn3
  refine summable_of_sum_range_le (fun k => by
    unfold r₃; positivity) (c := θ₃ π ^ 2) fun n => ?_
  rw [θ₃_sq_eq pi_pos]
  let S : Finset (ℤ × ℤ) := (Finset.range n).biUnion reps
  have hdisj : Set.PairwiseDisjoint (Finset.range n : Set ℕ) reps := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpi hpj
    simp only [reps, Finset.mem_filter] at hpi hpj
    have : (i : ℤ) = (j : ℤ) := hpi.2.symm.trans hpj.2
    exact hij (by exact_mod_cast this)
  have hsum_eq : ∑ k ∈ Finset.range n, (r₃ k : ℝ) * exp (-π) ^ k =
      ∑ p ∈ S, exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hconst : ∀ p ∈ reps k, exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) = exp (-π) ^ k := by
      intro ⟨x, y⟩ hmem
      simp only [reps, Finset.mem_filter] at hmem
      have hsq : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = (k : ℝ) := by exact_mod_cast hmem.2
      rw [hsq, ← exp_nat_mul]; congr 1; ring
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [hsum_eq]
  exact hprod.sum_le_tsum S (fun _ _ => (exp_pos _).le)

private lemma abs_r₄_le_r₃ (k : ℕ) : |(r₄ k : ℝ)| ≤ (r₃ k : ℝ) := by
  unfold r₄ r₃
  push_cast
  calc |∑ m ∈ reps k, (-1 : ℝ) ^ (m.1 + m.2).natAbs|
      ≤ ∑ m ∈ reps k, |(-1 : ℝ) ^ (m.1 + m.2).natAbs| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _m ∈ reps k, (1 : ℝ) := by refine Finset.sum_congr rfl fun _ _ => by simp
    _ = ((reps k).card : ℝ) := by simp

private lemma summable_r₄ : Summable (fun k : ℕ => (r₄ k : ℝ) * exp (-π) ^ k) := by
  refine Summable.of_norm_bounded summable_r₃ fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos (exp_pos _) _)]
  exact mul_le_mul_of_nonneg_right (abs_r₄_le_r₃ k) (pow_nonneg (exp_pos _).le _)

private lemma tsum_r₄ : ∑' k : ℕ, (r₄ k : ℝ) * exp (-π) ^ k = θ₄ π ^ 2 := by
  have hs3 := summable_exp_neg_sq pi_pos
  have hnn3 : ∀ n : ℤ, 0 ≤ exp (-π * (n : ℝ) ^ 2) := fun _ => (exp_pos _).le
  have hprod3 : Summable (fun p : ℤ × ℤ => exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    have : (fun p : ℤ × ℤ => exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
        fun p => exp (-π * (p.1 : ℝ) ^ 2) * exp (-π * (p.2 : ℝ) ^ 2) := by
      ext ⟨x, y⟩; rw [← exp_add]; congr 1; ring
    rw [this]; exact hs3.mul_of_nonneg hs3 hnn3 hnn3
  have hprod4 : Summable (fun p : ℤ × ℤ => (-1 : ℝ) ^ (p.1 + p.2).natAbs *
      exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) :=
    Summable.of_norm_bounded hprod3 fun ⟨x, y⟩ => by
      simp [norm_mul, norm_pow, abs_of_pos (exp_pos _)]
  rw [θ₄_sq_eq pi_pos]
  let g : ℤ × ℤ → ℕ := fun p => p.1.natAbs ^ 2 + p.2.natAbs ^ 2
  rw [← tsum_fiberwise_real hprod4 g]
  refine tsum_congr fun k => ?_
  have hfib := fiber_eq_reps k
  rw [tsum_congr_set_coe (f := fun p : ℤ × ℤ => (-1 : ℝ) ^ (p.1 + p.2).natAbs *
      exp (-π * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) hfib, tsum_fintype]
  have hsum : (∑ p : (reps k : Set (ℤ × ℤ)), (-1 : ℝ) ^ (p.1.1 + p.1.2).natAbs *
      exp (-π * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2))) =
      ∑ p : (reps k : Set (ℤ × ℤ)), (-1 : ℝ) ^ (p.1.1 + p.1.2).natAbs * exp (-π) ^ k := by
    refine Finset.sum_congr rfl fun ⟨⟨x, y⟩, hmem⟩ _ => ?_
    simp only [Finset.mem_coe, reps, Finset.mem_filter] at hmem
    have hsq : (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = (k : ℝ) := by exact_mod_cast hmem.2
    rw [hsq, ← exp_nat_mul]; congr 2; ring
  rw [hsum, ← Finset.sum_mul]
  congr 1
  unfold r₄
  push_cast
  exact (Finset.sum_coe_sort (reps k) (fun m => (-1 : ℝ) ^ (m.1 + m.2).natAbs)).symm

private lemma r₃_zero : r₃ 0 = 1 := by
  unfold r₃ reps
  have : ((Finset.Icc (0 : ℤ) 0 ×ˢ Finset.Icc (0 : ℤ) 0).filter
      fun m => m.1 ^ 2 + m.2 ^ 2 = 0) = {(0, 0)} := by decide
  simpa using congrArg Finset.card this

private lemma r₄_zero : r₄ 0 = 1 := by
  unfold r₄ reps
  have : ((Finset.Icc (0 : ℤ) 0 ×ˢ Finset.Icc (0 : ℤ) 0).filter
      fun m => m.1 ^ 2 + m.2 ^ 2 = 0) = {(0, 0)} := by decide
  simp [Finset.filter_singleton]

private lemma cList_length (k : ℕ) : (cList k).length = k + 1 := by
  induction k with
  | zero => simp [cList]
  | succ k ih => simp [cList, ih]

private lemma cList_getD_eq_c (k i : ℕ) (hi : i ≤ k) : (cList k).getD i 0 = c i := by
  induction k with
  | zero =>
    have : i = 0 := by omega
    subst this; rfl
  | succ k ih =>
    by_cases h : i ≤ k
    · have hlt : i < (cList k).length := by rw [cList_length]; omega
      have : (cList (k + 1)).getD i 0 = (cList k).getD i 0 := by
        simp [cList, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [this, ih h]
    · have : i = k + 1 := by omega
      subst this; rfl

private lemma c_zero : c 0 = 1 := by
  simp [c, cList, r₄_zero]

private lemma c_succ (k : ℕ) :
    c (k + 1) = r₄ (k + 1) - ∑ i ∈ range (k + 1), c i * r₃ (k + 1 - i) := by
  have hlen : (cList k).length = k + 1 := cList_length k
  have hget : c (k + 1) =
      r₄ (k + 1) - ∑ i ∈ range (k + 1), (cList k).getD i 0 * r₃ (k + 1 - i) := by
    simp [c, cList, List.getD_eq_getElem?_getD, hlen]
  rw [hget]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cList_getD_eq_c k i (by have := mem_range.mp hi; omega)]

private lemma c_conv_r₃ (k : ℕ) :
    ∑ i ∈ range (k + 1), c i * r₃ (k - i) = r₄ k := by
  cases k with
  | zero => simp [c_zero, r₃_zero, r₄_zero]
  | succ k =>
    rw [sum_range_succ, Nat.sub_self, r₃_zero, mul_one, c_succ]
    ring

private lemma θ₃_sq_sub_one_lt_half : θ₃ π ^ 2 - 1 < 1 / 2 := by
  have hexp3 : (10 : ℝ) < exp π := by
    have hpi : (3 : ℝ) < π := Real.pi_gt_three
    have h1 : (10 : ℝ) < exp 3 := by
      have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 4
      simp [Finset.sum_range_succ, Nat.factorial] at hsum
      linarith
    exact lt_trans h1 (exp_lt_exp.mpr hpi)
  have hq : exp (-π) < 1 / 10 := by
    rw [exp_neg, inv_lt_comm₀ (exp_pos _) (by norm_num)]
    linarith
  have hθ3_le : θ₃ π < 11 / 9 := by
    have hs := summable_exp_neg_sq pi_pos
    have hnat : Summable (fun m : ℕ => exp (-π * ((m : ℝ) + 1) ^ 2)) := by
      have := (summable_nat_add_iff 1).mpr
        (hs.comp_injective (Nat.cast_injective (R := ℤ)))
      simpa [Function.comp_def] using this
    have hsplit : θ₃ π = 1 + 2 * ∑' m : ℕ, exp (-π * ((m : ℝ) + 1) ^ 2) := by
      unfold θ₃
      have h1 := tsum_of_nat_of_neg_add_one
        (f := fun n : ℤ => exp (-π * (n : ℝ) ^ 2))
        (hs.comp_injective Nat.cast_injective)
        (hs.comp_injective (fun a b h => by omega))
      rw [h1]
      have hpos_split : (∑' n : ℕ, exp (-π * ((n : ℤ) : ℝ) ^ 2)) =
          exp (-π * ((0 : ℤ) : ℝ) ^ 2) + ∑' n : ℕ, exp (-π * (((n + 1 : ℕ) : ℤ) : ℝ) ^ 2) := by
        simpa [Function.comp_def] using (hs.comp_injective Nat.cast_injective).tsum_eq_zero_add
      have hneg_eq'' : (∑' m : ℕ, exp (-π * ((-((m : ℤ) + 1) : ℤ) : ℝ) ^ 2)) =
          ∑' m : ℕ, exp (-π * ((m : ℝ) + 1) ^ 2) := by
        refine tsum_congr fun m => ?_; push_cast; ring_nf
      have hpos_eq : (∑' m : ℕ, exp (-π * (((m + 1 : ℕ) : ℤ) : ℝ) ^ 2)) =
          ∑' m : ℕ, exp (-π * ((m : ℝ) + 1) ^ 2) := by
        refine tsum_congr fun m => ?_; push_cast; ring_nf
      rw [hpos_split, hpos_eq, hneg_eq'']
      simp only [Int.cast_zero, sq, mul_zero, exp_zero]
      ring
    have hgeom : Summable (fun m : ℕ => exp (-π) ^ (m + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (exp_pos _).le (by linarith))
    have hle_sum : ∑' m : ℕ, exp (-π * ((m : ℝ) + 1) ^ 2) ≤ ∑' m : ℕ, exp (-π) ^ (m + 1) := by
      refine Summable.tsum_le_tsum (fun m => ?_) hnat hgeom
      rw [← exp_nat_mul]
      apply exp_le_exp.mpr
      have hm : ((m + 1 : ℕ) : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
        push_cast
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      nlinarith [pi_pos]
    have hgeom_val : ∑' m : ℕ, exp (-π) ^ (m + 1) = exp (-π) * (1 - exp (-π))⁻¹ := by
      have : (fun m : ℕ => exp (-π) ^ (m + 1)) = fun m => exp (-π) * exp (-π) ^ m := by
        ext m; rw [pow_succ']
      rw [this, tsum_mul_left, tsum_geometric_of_lt_one (exp_pos _).le (by linarith)]
    have hbound : exp (-π) * (1 - exp (-π))⁻¹ < 1 / 9 := by
      rw [← div_eq_mul_inv, div_lt_iff₀ (by linarith)]
      linarith
    linarith
  have hpos := θ₃_pos
  nlinarith

private lemma summable_abs_c : Summable (fun k : ℕ => |(c k : ℝ) * exp (-π) ^ k|) := by
  let q := exp (-π)
  have hq_pos : 0 < q := exp_pos _
  let M : ℝ := θ₃ π ^ 2 - 1
  have hM_lt : M < 1 / 2 := θ₃_sq_sub_one_lt_half
  have hM_sum : ∑' k : ℕ, (r₃ (k + 1) : ℝ) * q ^ (k + 1) = M := by
    have h := summable_r₃.tsum_eq_zero_add
    rw [tsum_r₃] at h
    simp only [r₃_zero, Int.cast_one, pow_zero, mul_one] at h
    linarith
  have hM_summ : Summable (fun k : ℕ => (r₃ (k + 1) : ℝ) * q ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr summable_r₃
  refine summable_of_sum_range_le (fun _ => abs_nonneg _) (c := 3) fun N => ?_
  cases N with
  | zero => simp
  | succ N =>
    have hS_split : ∑ k ∈ range (N + 1), |(c k : ℝ) * q ^ k| =
        1 + ∑ k ∈ range N, |(c (k + 1) : ℝ) * q ^ (k + 1)| := by
      rw [Finset.sum_range_succ']
      simp [c_zero, add_comm]
    have hstep : ∀ k : ℕ, |(c (k + 1) : ℝ) * q ^ (k + 1)| ≤
        (r₃ (k + 1) : ℝ) * q ^ (k + 1) +
        ∑ i ∈ range (k + 1), |(c i : ℝ) * q ^ i| * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i)) := by
      intro k
      rw [abs_mul, abs_of_pos (pow_pos hq_pos _)]
      have hc : (c (k + 1) : ℝ) = (r₄ (k + 1) : ℝ) -
          ∑ i ∈ range (k + 1), (c i : ℝ) * (r₃ (k + 1 - i) : ℝ) := by
        exact_mod_cast c_succ k
      rw [hc]
      have htri : |(r₄ (k + 1) : ℝ) - ∑ i ∈ range (k + 1), (c i : ℝ) * (r₃ (k + 1 - i) : ℝ)| ≤
          (r₃ (k + 1) : ℝ) + ∑ i ∈ range (k + 1), |(c i : ℝ)| * (r₃ (k + 1 - i) : ℝ) := by
        calc |(r₄ (k + 1) : ℝ) - ∑ i ∈ range (k + 1), (c i : ℝ) * (r₃ (k + 1 - i) : ℝ)|
            ≤ |(r₄ (k + 1) : ℝ)| + |∑ i ∈ range (k + 1), (c i : ℝ) * (r₃ (k + 1 - i) : ℝ)| :=
              abs_sub _ _
          _ ≤ (r₃ (k + 1) : ℝ) + ∑ i ∈ range (k + 1), |(c i : ℝ) * (r₃ (k + 1 - i) : ℝ)| := by
              gcongr
              · exact abs_r₄_le_r₃ (k + 1)
              · exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ (r₃ (k + 1) : ℝ) + ∑ i ∈ range (k + 1), |(c i : ℝ)| * (r₃ (k + 1 - i) : ℝ) := by
              gcongr with i
              rw [abs_mul, abs_of_nonneg (a := (r₃ (k + 1 - i) : ℝ)) (by unfold r₃; positivity)]
      calc |(r₄ (k + 1) : ℝ) - ∑ i ∈ range (k + 1), (c i : ℝ) * (r₃ (k + 1 - i) : ℝ)| * q ^ (k + 1)
          ≤ ((r₃ (k + 1) : ℝ) + ∑ i ∈ range (k + 1), |(c i : ℝ)| * (r₃ (k + 1 - i) : ℝ)) * q ^ (k + 1) :=
            mul_le_mul_of_nonneg_right htri (pow_nonneg hq_pos.le _)
        _ = (r₃ (k + 1) : ℝ) * q ^ (k + 1) +
            ∑ i ∈ range (k + 1), |(c i : ℝ) * q ^ i| * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i)) := by
            rw [add_mul, Finset.sum_mul]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            have hik : i ≤ k + 1 := by have := mem_range.mp hi; omega
            rw [abs_mul, abs_of_pos (pow_pos hq_pos _)]
            have hpow : q ^ i * q ^ (k + 1 - i) = q ^ (k + 1) := by
              rw [← pow_add, Nat.add_sub_cancel' hik]
            calc |(c i : ℝ)| * (r₃ (k + 1 - i) : ℝ) * q ^ (k + 1)
                = |(c i : ℝ)| * (r₃ (k + 1 - i) : ℝ) * (q ^ i * q ^ (k + 1 - i)) := by rw [hpow]
              _ = |(c i : ℝ)| * q ^ i * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i)) := by ring
    have hsum_le : ∑ k ∈ range N, |(c (k + 1) : ℝ) * q ^ (k + 1)| ≤
        M + (∑ k ∈ range (N + 1), |(c k : ℝ) * q ^ k|) * M := by
      have h1 : ∑ k ∈ range N, |(c (k + 1) : ℝ) * q ^ (k + 1)| ≤
          (∑ k ∈ range N, (r₃ (k + 1) : ℝ) * q ^ (k + 1)) +
          ∑ k ∈ range N, ∑ i ∈ range (k + 1),
            |(c i : ℝ) * q ^ i| * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun k _ => hstep k
      have h2 : ∑ k ∈ range N, (r₃ (k + 1) : ℝ) * q ^ (k + 1) ≤ M := by
        rw [← hM_sum]
        exact hM_summ.sum_le_tsum (range N) (fun _ _ => by unfold r₃; positivity)
      have h3 : ∑ k ∈ range N, ∑ i ∈ range (k + 1),
            |(c i : ℝ) * q ^ i| * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i)) ≤
          (∑ i ∈ range (N + 1), |(c i : ℝ) * q ^ i|) * M := by
        have hsub : ∑ k ∈ range N, ∑ i ∈ range (k + 1),
              |(c i : ℝ) * q ^ i| * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i)) ≤
            ∑ i ∈ range (N + 1), ∑ j ∈ range N,
              |(c i : ℝ) * q ^ i| * ((r₃ (j + 1) : ℝ) * q ^ (j + 1)) := by
          let f : ℕ × ℕ → ℝ := fun p => |(c p.1 : ℝ) * q ^ p.1| * ((r₃ (p.2 + 1) : ℝ) * q ^ (p.2 + 1))
          have hlhs : (∑ k ∈ range N, ∑ i ∈ range (k + 1),
              |(c i : ℝ) * q ^ i| * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i))) =
              ∑ p ∈ (range N).sigma (fun k => range (k + 1)), f (p.2, p.1 - p.2) := by
            rw [Finset.sum_sigma]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
            have hik : i ≤ k := by have := mem_range.mp hi; omega
            have hsub : k - i + 1 = k + 1 - i := by omega
            simp only [f, hsub]
          have hrhs : (∑ i ∈ range (N + 1), ∑ j ∈ range N,
              |(c i : ℝ) * q ^ i| * ((r₃ (j + 1) : ℝ) * q ^ (j + 1))) =
              ∑ p ∈ range (N + 1) ×ˢ range N, f p :=
            (Finset.sum_product (range (N + 1)) (range N) f).symm
          rw [hlhs, hrhs]
          let emb : (k : ℕ) × ℕ → ℕ × ℕ := fun p => (p.2, p.1 - p.2)
          have hinj : Set.InjOn emb ((range N).sigma (fun k => range (k + 1)) : Set ((k : ℕ) × ℕ)) := by
            rintro ⟨k1, i1⟩ h1 ⟨k2, i2⟩ h2 heq
            simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at h1 h2
            simp only [emb, Prod.mk.injEq] at heq
            have hk : k1 = k2 := by omega
            subst hk; congr 1; exact heq.1
          have himg_sub : ((range N).sigma (fun k => range (k + 1))).image emb ⊆ range (N + 1) ×ˢ range N := by
            intro q hq
            obtain ⟨⟨k, i⟩, hki, rfl⟩ := Finset.mem_image.mp hq
            simp only [Finset.mem_sigma, Finset.mem_range] at hki
            simp only [emb, Finset.mem_product, Finset.mem_range]
            omega
          rw [← Finset.sum_image hinj]
          exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by
            unfold f r₃; positivity
        calc ∑ k ∈ range N, ∑ i ∈ range (k + 1),
              |(c i : ℝ) * q ^ i| * ((r₃ (k + 1 - i) : ℝ) * q ^ (k + 1 - i))
            ≤ ∑ i ∈ range (N + 1), ∑ j ∈ range N,
                |(c i : ℝ) * q ^ i| * ((r₃ (j + 1) : ℝ) * q ^ (j + 1)) := hsub
          _ = (∑ i ∈ range (N + 1), |(c i : ℝ) * q ^ i|) *
                (∑ j ∈ range N, (r₃ (j + 1) : ℝ) * q ^ (j + 1)) := by
              simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
          _ ≤ (∑ i ∈ range (N + 1), |(c i : ℝ) * q ^ i|) * M := by
              exact mul_le_mul_of_nonneg_left h2 (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      linarith
    have hS_nonneg : 0 ≤ ∑ k ∈ range (N + 1), |(c k : ℝ) * q ^ k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith

end OMA.OeisA010503Proof

open Real Finset OMA.S_oeis_a010503 OMA.OeisA010503Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a010503.main := by
  have hterm : ∀ k : ℕ, (c k : ℝ) / exp (k * π) = (c k : ℝ) * exp (-π) ^ k := by
    intro k
    rw [div_eq_mul_inv, ← exp_neg, ← exp_nat_mul]
    congr 2; ring
  simp_rw [hterm]
  have hc_summ : Summable (fun k : ℕ => (c k : ℝ) * exp (-π) ^ k) :=
    summable_abs_c.of_abs
  have hprod : (∑' k : ℕ, (c k : ℝ) * exp (-π) ^ k) * (∑' k : ℕ, (r₃ k : ℝ) * exp (-π) ^ k) =
      ∑' k : ℕ, (r₄ k : ℝ) * exp (-π) ^ k := by
    have hmul_summ : Summable (fun p : ℕ × ℕ =>
        ((c p.1 : ℝ) * exp (-π) ^ p.1) * ((r₃ p.2 : ℝ) * exp (-π) ^ p.2)) := by
      refine Summable.of_norm_bounded
        (summable_abs_c.mul_of_nonneg summable_r₃ (fun _ => abs_nonneg _)
          (fun _ => by unfold r₃; positivity)) fun p => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_of_nonneg (by unfold r₃; positivity)]
    rw [hc_summ.tsum_mul_tsum_eq_tsum_sum_range summable_r₃ hmul_summ]
    refine tsum_congr fun k => ?_
    have hpow : ∀ i ∈ range (k + 1),
        ((c i : ℝ) * exp (-π) ^ i) * ((r₃ (k - i) : ℝ) * exp (-π) ^ (k - i)) =
        ((c i : ℝ) * (r₃ (k - i) : ℝ)) * exp (-π) ^ k := by
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      have hp : exp (-π) ^ i * exp (-π) ^ (k - i) = exp (-π) ^ k := by
        rw [← pow_add, Nat.add_sub_cancel' hik]
      calc ((c i : ℝ) * exp (-π) ^ i) * ((r₃ (k - i) : ℝ) * exp (-π) ^ (k - i))
          = ((c i : ℝ) * (r₃ (k - i) : ℝ)) * (exp (-π) ^ i * exp (-π) ^ (k - i)) := by ring
        _ = ((c i : ℝ) * (r₃ (k - i) : ℝ)) * exp (-π) ^ k := by rw [hp]
    rw [Finset.sum_congr rfl hpow, ← Finset.sum_mul]
    congr 1
    exact_mod_cast c_conv_r₃ k
  rw [tsum_r₃, tsum_r₄] at hprod
  have h3ne : θ₃ π ^ 2 ≠ 0 := (pow_pos θ₃_pos 2).ne'
  have hinv : θ₄ π ^ 2 / θ₃ π ^ 2 = 1 / √2 := by
    rw [← θ₃_sq_div_θ₄_sq, one_div_div]
  rw [← hinv, eq_div_iff h3ne]
  exact hprod
