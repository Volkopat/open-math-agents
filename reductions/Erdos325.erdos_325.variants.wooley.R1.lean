import FormalConjectures.ErdosProblems.«325»
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.SmoothNumbers

/-! Wooley, Sums of three cubes, II (2015), Theorems 1.1–1.2,
https://arxiv.org/abs/1502.01944. Fourier orthogonality converts the mixed
sixth moment to a collision count. Cauchy–Schwarz and a rounded cube root
give the exact decimal exponent in the natural counting function. -/

namespace OMA.R_Erdos325_erdos_325_variants_wooley_R1

open scoped BigOperators
open MeasureTheory Finset AddCircle Asymptotics Filter
private instance periodOnePositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem integral_character (k : ℤ) :
    (∫ t : AddCircle 1, fourier k t ∂haarAddCircle) = if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

private theorem mixed_moment_generic {A : Type} [DecidableEq A]
    (s : Finset A) (f : A → ℤ) :
    (∫ t : AddCircle 1, ‖∑ a ∈ s, fourier (f a) t‖ ^ 2 ∂haarAddCircle) =
      ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card := by
  have pointwise (t : AddCircle 1) :
      ((‖∑ a ∈ s, fourier (f a) t‖ ^ 2 : ℝ) : ℂ) =
        ∑ a ∈ s, ∑ b ∈ s, fourier (f a - f b) t := by
    rw [Complex.sq_norm, ← Complex.mul_conj]
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [sub_eq_add_neg, fourier_add, fourier_neg]
  have hc (a : A) : Continuous (fun t : AddCircle 1 =>
      ∑ b ∈ s, fourier (f a - f b) t) :=
    continuous_finsetSum _ fun b _ => (fourier (f a - f b)).continuous
  have hi :
      (∫ t : AddCircle 1, (∑ a ∈ s, ∑ b ∈ s, fourier (f a - f b) t) ∂haarAddCircle) =
        (∑ a ∈ s, ∑ b ∈ s, if f a = f b then (1 : ℂ) else 0) := by
    rw [integral_finsetSum _ fun a _ => (hc a).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum _ fun b _ =>
      (fourier (f a - f b)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)]
    simp_rw [integral_character, sub_eq_zero]
  have hcard :
      (∑ a ∈ s, ∑ b ∈ s, if f a = f b then (1 : ℂ) else 0) =
        (((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card : ℂ) := by
    rw [← Finset.sum_product s s (fun p : A × A => if f p.1 = f p.2 then (1 : ℂ) else 0)]
    simp
  have ht := hi.trans hcard
  simp_rw [← pointwise] at ht
  rw [integral_complex_ofReal (f := fun t : AddCircle 1 => ‖∑ a ∈ s, fourier (f a) t‖ ^ 2)] at ht
  simpa using congrArg Complex.re ht

private theorem mixed_cubic_moment (s t : Finset ℕ) :
    (∫ z : AddCircle 1, ‖∑ a ∈ s, fourier ((a : ℤ)^3) z‖^2 *
        ‖∑ b ∈ t, fourier ((b : ℤ)^3) z‖^4 ∂haarAddCircle) =
      ((((s ×ˢ (t ×ˢ t)) ×ˢ (s ×ˢ (t ×ˢ t))).filter
        (fun p => p.1.1^3 + p.1.2.1^3 + p.1.2.2^3 =
                  p.2.1^3 + p.2.2.1^3 + p.2.2.2^3)).card : ℝ) := by
  let f (p : ℕ × ℕ × ℕ) : ℤ := (p.1 : ℤ)^3 + (p.2.1 : ℤ)^3 + (p.2.2 : ℤ)^3
  have hf (p q : ℕ × ℕ × ℕ) : f p = f q ↔
      p.1^3 + p.2.1^3 + p.2.2^3 = q.1^3 + q.2.1^3 + q.2.2^3 := by
    dsimp only [f]
    exact_mod_cast Iff.rfl
  have h := mixed_moment_generic (s ×ˢ (t ×ˢ t)) f
  simp_rw [hf] at h
  rw [← h]
  congr 1
  funext z
  have hsum :
      (∑ p ∈ s ×ˢ (t ×ˢ t), fourier (f p) z) =
        (∑ a ∈ s, fourier ((a : ℤ)^3) z) *
          (∑ b ∈ t, fourier ((b : ℤ)^3) z) *
          (∑ c ∈ t, fourier ((c : ℤ)^3) z) := by
    simp only [f, Finset.sum_product, fourier_add, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hsum, norm_mul, norm_mul]
  ring
private theorem collision_cauchy {A : Type} [DecidableEq A] (s : Finset A) (f : A → ℕ) :
    (s.card : ℝ)^2 ≤ (s.image f).card *
      ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card := by
  let fiber (n : ℕ) := s.filter (fun a => f a = n)
  have hsize : s.card = ∑ n ∈ s.image f, (fiber n).card :=
    card_eq_sum_card_fiberwise fun a ha => mem_image_of_mem f ha
  have hcollision : ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card =
      ∑ n ∈ s.image f, (fiber n).card ^ 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun p : A × A => f p.1) (t := s.image f)]
    · apply sum_congr rfl
      intro n hn
      rw [sq, ← card_product]
      congr 1
      ext p
      simp only [fiber, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hn⟩
        exact ⟨⟨ha, hn⟩, hb, hab.symm.trans hn⟩
      · rintro ⟨⟨ha, hna⟩, hb, hnb⟩
        exact ⟨⟨⟨ha, hb⟩, hna.trans hnb.symm⟩, hna⟩
    · intro p hp
      exact mem_image_of_mem f (mem_product.mp (mem_filter.mp hp).1).1
  have h : s.card ^ 2 ≤ (s.image f).card * ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card := by
    rw [hcollision]
    conv_lhs => rw [hsize]
    exact sq_sum_le_card_mul_sum_sq (s := s.image f) (f := fun n => (fiber n).card)
  exact_mod_cast h

private theorem card_cube_image_le (P x : ℕ) (t : Finset ℕ) (ht : ∀ n ∈ t, n ≤ P)
    (hx : 3 * P^3 ≤ x) :
    (((Icc 1 P) ×ˢ (t ×ˢ t)).image
      (fun a : ℕ × ℕ × ℕ => a.1^3 + a.2.1^3 + a.2.2^3)).card ≤
      Erdos325.cardIsSumThreePowerBelow 3 x := by
  unfold Erdos325.cardIsSumThreePowerBelow
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ ((Set.finite_Iic x).subset fun _ hn => hn.1)
  intro n hn
  obtain ⟨⟨a,b,c⟩, hp, rfl⟩ := mem_image.mp hn
  obtain ⟨ha, hbc⟩ := mem_product.mp hp
  obtain ⟨hb, hc⟩ := mem_product.mp hbc
  have haP : a ≤ P := (mem_Icc.mp ha).2
  have h1 := Nat.pow_le_pow_left haP 3
  have h2 := Nat.pow_le_pow_left (ht b hb) 3
  have h3 := Nat.pow_le_pow_left (ht c hc) 3
  exact ⟨show a^3 + b^3 + c^3 ≤ x by omega, a, b, c, rfl⟩

private theorem cube_scale (M x : ℕ) (hx : (4 * max M 1)^3 ≤ x) :
    ∃ P : ℕ, M ≤ P ∧ 1 ≤ P ∧ 3 * P^3 ≤ x ∧
      (x : ℝ) ^ (0.91709477 : ℝ) ≤ (4 : ℝ) ^ (2.75128431 : ℝ) * (P : ℝ) ^ (2.75128433 : ℝ) := by
  let y := (x : ℝ) ^ (1 / 3 : ℝ)
  let P := ⌊y / 2⌋₊
  have hycube : y^3 = (x : ℝ) := by
    simpa [y] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg x) (by decide : (3 : ℕ) ≠ 0)
  have hM : ((4 : ℝ) * (max M 1 : ℕ)) ≤ y := by
    have hpow : (((4 : ℝ) * (max M 1 : ℕ))^3) ≤ (x : ℝ) := by exact_mod_cast hx
    exact le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity) (hpow.trans_eq hycube.symm)
  have hMone : (1 : ℝ) ≤ (max M 1 : ℕ) := by exact_mod_cast le_max_right M 1
  have hy4 : 4 ≤ y := by linarith
  have hpfloor : (P : ℝ) ≤ y / 2 := Nat.floor_le (by positivity)
  have hfloorp : y / 2 < (P : ℝ) + 1 := Nat.lt_floor_add_one _
  have hP : y ≤ 4 * (P : ℝ) := by linarith
  have hlow : max M 1 ≤ P := by
    exact_mod_cast (show ((max M 1 : ℕ) : ℝ) ≤ P by linarith)
  refine ⟨P, (le_max_left _ _).trans hlow, (le_max_right _ _).trans hlow, ?_, ?_⟩
  · have he : (2 * (P : ℝ)) ^ 3 ≤ y ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have hp3 : 0 ≤ (P : ℝ)^3 := by positivity
    rw [hycube, mul_pow] at he
    norm_num at he
    exact_mod_cast (show (3 : ℝ) * (P : ℝ)^3 ≤ x by linarith)
  · have hexp : (x : ℝ) ^ (0.91709477 : ℝ) = y ^ (2.75128431 : ℝ) := by
      rw [show (0.91709477 : ℝ) = (1 / 3) * 2.75128431 by norm_num, Real.rpow_mul (by positivity)]
    rw [hexp]
    calc
      _ ≤ (4 * (P : ℝ)) ^ (2.75128431 : ℝ) := Real.rpow_le_rpow (by positivity) hP (by norm_num)
      _ = (4 : ℝ) ^ (2.75128431 : ℝ) * (P : ℝ) ^ (2.75128431 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (le_max_right M 1).trans hlow) (by norm_num)) (by positivity)

/-- Fixed-power smooth numbers have positive lower density. Mathlib's
strict smooth cutoff is one more than the floor of the real cutoff. -/
def H1 : Prop := ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
  ∀ᶠ P : ℕ in atTop,
    c * P ≤ ((P.smoothNumbersUpTo (⌊(P : ℝ) ^ η⌋₊ + 1)).card : ℝ)

private theorem mixed_moment_eq_interval (s t : Finset ℕ) :
    (∫ z : AddCircle 1, ‖∑ a ∈ s, fourier ((a : ℤ)^3) z‖^2 *
      ‖∑ b ∈ t, fourier ((b : ℤ)^3) z‖^4 ∂haarAddCircle) =
      (∫ z in (0 : ℝ)..1, ‖∑ a ∈ s, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)^3 * z)‖^2 *
        ‖∑ b ∈ t, Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)^3 * z)‖^4) := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  have h := (AddCircle.intervalIntegral_preimage 1 0 (fun z : AddCircle 1 =>
    ‖∑ a ∈ s, fourier ((a : ℤ)^3) z‖^2 * ‖∑ b ∈ t, fourier ((b : ℤ)^3) z‖^4)).symm
  simp only [zero_add, fourier_coe_apply, Complex.ofReal_one, div_one] at h
  push_cast at h
  exact h

/-- Wooley's mixed sixth-moment bound in its interval-integral form. -/
def H2 : Prop := ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ᶠ P : ℕ in atTop,
  let s := Icc 1 P
  let t := P.smoothNumbersUpTo (⌊(P : ℝ) ^ η⌋₊ + 1)
  (∫ z in (0 : ℝ)..1, ‖∑ a ∈ s, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)^3 * z)‖^2 *
    ‖∑ b ∈ t, Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)^3 * z)‖^4) ≤
    C * (P : ℝ) ^ (3.24871567 : ℝ)

theorem main : H1 → H2 → type_of% @Erdos325.erdos_325.variants.wooley := by
  intro density moment
  obtain ⟨η, C, hη, hC, hMoment⟩ := moment
  obtain ⟨c, hc, hDensity⟩ := density η hη
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hDensity.and hMoment)
  refine IsBigO.of_bound ((4 : ℝ) ^ (2.75128431 : ℝ) * (C / c^4)) ?_
  filter_upwards [eventually_ge_atTop ((4 * max M 1)^3)] with x hx
  obtain ⟨P, hPM, hP, hPx, hScale⟩ := cube_scale M x hx
  obtain ⟨hd, hm⟩ := hM P hPM
  let s := Icc 1 P
  let t := P.smoothNumbersUpTo (⌊(P : ℝ) ^ η⌋₊ + 1)
  let S := s ×ˢ (t ×ˢ t)
  let f (a : ℕ × ℕ × ℕ) := a.1^3 + a.2.1^3 + a.2.2^3
  let m := ((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card
  let Q : ℝ := Erdos325.cardIsSumThreePowerBelow 3 x
  change c * P ≤ (t.card : ℝ) at hd
  have hPc : (0 : ℝ) < P := by exact_mod_cast Nat.zero_lt_of_lt hP
  change (∫ z in (0 : ℝ)..1,
    ‖∑ a ∈ s, Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)^3 * z)‖^2 *
    ‖∑ b ∈ t, Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)^3 * z)‖^4) ≤ _ at hm
  rw [← mixed_moment_eq_interval s t, mixed_cubic_moment s t] at hm
  change (m : ℝ) ≤ _ at hm
  have hcard : (S.card : ℝ) = (P : ℝ) * (t.card : ℝ)^2 := by
    simp only [S, s, card_product, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul]
    ring
  have hImg : ((S.image f).card : ℝ) ≤ Q := by
    dsimp only [S, s, f, Q]
    exact_mod_cast card_cube_image_le P x t (fun n hn => (Nat.mem_smoothNumbersUpTo.mp hn).1) hPx
  have hCauchy : (S.card : ℝ)^2 ≤ ((S.image f).card : ℝ) * m := collision_cauchy S f
  have hbound : c^4 * (P : ℝ)^6 ≤ Q * (C * (P : ℝ) ^ (3.24871567 : ℝ)) := by
    calc
      _ = ((P : ℝ) * (c * P)^2)^2 := by ring
      _ ≤ (S.card : ℝ)^2 := by
        rw [hcard]
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hd 2) hPc.le) 2
      _ ≤ ((S.image f).card : ℝ) * m := hCauchy
      _ ≤ _ := mul_le_mul hImg hm (by positivity) (by positivity)
  have hpow : (P : ℝ)^6 = (P : ℝ) ^ (2.75128433 : ℝ) * (P : ℝ) ^ (3.24871567 : ℝ) := by
    rw [← Real.rpow_add hPc, show (2.75128433 + 3.24871567 : ℝ) = (6 : ℕ) by norm_num,
      Real.rpow_natCast]
  rw [hpow, ← mul_assoc, ← mul_assoc] at hbound
  have hcanc := (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hPc (3.24871567 : ℝ))).mp hbound
  have hlocal : (P : ℝ) ^ (2.75128433 : ℝ) ≤ (C / c^4) * Q := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (pow_pos hc 4)).mpr (by simpa only [mul_comm] using hcanc)
  change ‖(x : ℝ) ^ (0.91709477 : ℝ)‖ ≤
    ((4 : ℝ) ^ (2.75128431 : ℝ) * (C / c^4)) * ‖Q‖
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _),
    Real.norm_of_nonneg (by positivity : 0 ≤ Q)]
  exact hScale.trans ((mul_le_mul_of_nonneg_left hlocal (by positivity)).trans_eq (mul_assoc _ _ _).symm)

end OMA.R_Erdos325_erdos_325_variants_wooley_R1
