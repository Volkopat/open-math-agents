import OMAReductions.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_uniform_R1

/-!
# Finite Fourier bound for the shift correlations

Averaging short shifts moves the boundary by at most a quadratic error.
The smoothed sum is bounded by finite Cauchy–Schwarz. Its convolution
energy is estimated by Parseval on the cyclic group of size twice the
window length, with zero padding for the sign sequence.

For the Fourier approach to the averaged Chowla theorem, see Matomäki,
Radziwiłł and Tao, *An averaged form of Chowla's conjecture* (2015),
Lemma 1.4 and Section 4. https://arxiv.org/abs/1503.05121
-/

namespace OMA.ChowlaFiniteFourier

open Finset
open scoped BigOperators

/-- Shifting the window by `y` loses at most `2*y` for a function bounded by one. -/
theorem sum_range_le_shift_add (F : ℕ → ℝ) (hF : ∀ x, |F x| ≤ 1) (N y : ℕ) :
    (∑ x ∈ range N, F x) ≤ (∑ x ∈ range N, F (x+y)) + 2 * (y : ℝ) := by
  have hLeft : (∑ x ∈ range y, F x) ≤ (y : ℝ) := by
    calc
      _ ≤ ∑ x ∈ range y, (1 : ℝ) := sum_le_sum fun x _ => (abs_le.mp (hF x)).2
      _ = _ := by simp
  have hRight : -(y : ℝ) ≤ ∑ x ∈ range y, F (N+x) := by
    calc
      _ = ∑ x ∈ range y, (-1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum fun x _ => (abs_le.mp (hF (N+x))).1
  have hBalance : (∑ x ∈ range N, F x) + (∑ x ∈ range y, F (N+x)) =
      (∑ x ∈ range y, F x) + (∑ x ∈ range N, F (x+y)) := by
    calc
      _ = ∑ x ∈ range (N+y), F x := (sum_range_add F N y).symm
      _ = ∑ x ∈ range (y+N), F x := by rw [Nat.add_comm N y]
      _ = _ := by simpa only [Nat.add_comm y] using sum_range_add F y N
  linarith only [hLeft, hRight, hBalance]

private theorem sum_double_range (m : ℕ) :
    (∑ y ∈ range m, 2 * (y : ℝ)) + (m : ℝ) = (m : ℝ)^2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    push_cast
    nlinarith only [ih]

/-- Fix the signs before averaging translated windows of bounded correlations. -/
theorem exists_signs_shift_smoothing (f g : ℕ → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hg : ∀ x, |g x| ≤ 1) (N m b : ℕ) (hm : 0 < m) (_hmN : m ≤ N) :
    ∃ a : ℕ → ℝ, (∀ h, |a h| ≤ 1) ∧
      (∑ h ∈ range m, |∑ x ∈ range N, f (x+1) * g (b+x+h+1)|) ≤
        (∑ x ∈ range N, ∑ y ∈ range m,
          f (x+y+1) * (∑ h ∈ range m, a h * g (b+x+y+h+1))) / (m : ℝ) + (m : ℝ)^2 := by
  let corr (h : ℕ) : ℝ := ∑ x ∈ range N, f (x+1) * g (b+x+h+1)
  let a (h : ℕ) : ℝ := if 0 ≤ corr h then 1 else -1
  have ha (h : ℕ) : |a h| ≤ 1 := by
    by_cases hh : 0 ≤ corr h <;> simp [a, hh]
  have habs (h : ℕ) : |corr h| = a h * corr h := by
    by_cases hh : 0 ≤ corr h
    · simp [a, hh, abs_of_nonneg hh]
    · simp [a, hh, abs_of_neg (lt_of_not_ge hh)]
  refine ⟨a, ha, ?_⟩
  let F (h x : ℕ) : ℝ := a h * (f (x+1) * g (b+x+h+1))
  have hF (h x : ℕ) : |F h x| ≤ 1 := by
    have hfg : |f (x+1)| * |g (b+x+h+1)| ≤ (1 : ℝ) := by
      simpa only [one_mul] using mul_le_mul (hf (x+1)) (hg (b+x+h+1))
        (abs_nonneg (g (b+x+h+1))) (zero_le_one : (0 : ℝ) ≤ 1)
    simp only [F, abs_mul]
    simpa only [one_mul] using mul_le_mul (ha h) hfg
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (zero_le_one : (0 : ℝ) ≤ 1)
  let total : ℝ := ∑ h ∈ range m, |corr h|
  let shifted (y : ℕ) : ℝ := ∑ x ∈ range N,
    f (x+y+1) * (∑ h ∈ range m, a h * g (b+x+y+h+1))
  have hInterchange (y : ℕ) : (∑ h ∈ range m, ∑ x ∈ range N, F h (x+y)) = shifted y := by
    rw [sum_comm]
    unfold shifted
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    apply sum_congr rfl
    intro h _
    simp only [F, Nat.add_assoc]
    ring
  have hShift (y : ℕ) : total ≤ shifted y + (m : ℝ) * (2 * (y : ℝ)) := by
    calc
      total = ∑ h ∈ range m, ∑ x ∈ range N, F h x := by
        unfold total
        simp only [habs, corr, mul_sum, F]
      _ ≤ ∑ h ∈ range m, ((∑ x ∈ range N, F h (x+y)) + 2 * (y : ℝ)) :=
        sum_le_sum fun h _ => sum_range_le_shift_add (F h) (hF h) N y
      _ = _ := by simp only [sum_add_distrib, hInterchange, sum_const, card_range, nsmul_eq_mul]
  have hSum : (m : ℝ) * total ≤ (∑ y ∈ range m, shifted y) +
      (m : ℝ) * ∑ y ∈ range m, 2 * (y : ℝ) := by
    simpa only [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, ← mul_sum] using
      sum_le_sum (s := range m) (fun y _ => hShift y)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hError : (∑ y ∈ range m, 2 * (y : ℝ)) ≤ (m : ℝ)^2 := by
    linarith only [sum_double_range m, hmR.le]
  have hFinal : (m : ℝ) * total ≤ (∑ y ∈ range m, shifted y) + (m : ℝ) * (m : ℝ)^2 :=
    hSum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hError hmR.le))
  calc
    total ≤ ((∑ y ∈ range m, shifted y) + (m : ℝ) * (m : ℝ)^2) / (m : ℝ) :=
      (le_div_iff₀ hmR).2 (by simpa only [mul_comm total] using hFinal)
    _ = _ := by
      rw [add_div, mul_div_cancel_left₀ _ hmR.ne']
      unfold shifted
      rw [sum_comm]

end OMA.ChowlaFiniteFourier

namespace OMA.ChowlaFiniteFourier

open Finset
open scoped BigOperators

theorem smoothed_le_of_energy (f B : ℕ → ℕ → ℝ) (N m : ℕ) (e : ℝ)
    (hm : 0 < m) (hf : ∀ x y, |f x y| ≤ 1) (he : 0 ≤ e)
    (hE : ∑ x ∈ range N, ∑ y ∈ range m, B x y ^ 2 ≤ e * (m : ℝ)^3 * (N : ℝ)) :
    (∑ x ∈ range N, ∑ y ∈ range m, f x y * B x y) / (m : ℝ) ≤
      Real.sqrt e * (m : ℝ) * (N : ℝ) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hNR : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hF : (∑ x ∈ range N, ∑ y ∈ range m, f x y ^ 2) ≤ (N : ℝ) * (m : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ range N, ∑ _y ∈ range m, (1 : ℝ) := by
        apply sum_le_sum
        intro x _
        apply sum_le_sum
        intro y _
        have h : f x y ^ 2 ≤ (1 : ℝ)^2 := sq_le_sq.mpr (by simpa using hf x y)
        simpa using h
      _ = _ := by simp
  have hB : 0 ≤ ∑ x ∈ range N, ∑ y ∈ range m, B x y ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hCS : (∑ x ∈ range N, ∑ y ∈ range m, f x y * B x y)^2 ≤
      (∑ x ∈ range N, ∑ y ∈ range m, f x y ^ 2) *
        (∑ x ∈ range N, ∑ y ∈ range m, B x y ^ 2) := by
    simpa only [sum_product] using sum_mul_sq_le_sq_mul_sq
      ((range N) ×ˢ (range m)) (fun p => f p.1 p.2) (fun p => B p.1 p.2)
  have hs : (∑ x ∈ range N, ∑ y ∈ range m, f x y * B x y)^2 ≤
      (Real.sqrt e * (m : ℝ) * (N : ℝ) * (m : ℝ))^2 := by
    refine hCS.trans ((mul_le_mul hF hE hB (mul_nonneg hNR hmR.le)).trans_eq ?_)
    simp only [mul_pow, Real.sq_sqrt he]
    ring
  apply (div_le_iff₀ hmR).2
  refine (le_abs_self _).trans ?_
  have htarget : 0 ≤ Real.sqrt e * (m : ℝ) * (N : ℝ) * (m : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hmR.le) hNR) hmR.le
  simpa only [abs_of_nonneg htarget] using sq_le_sq.mp hs

end OMA.ChowlaFiniteFourier

namespace OMA.ChowlaFiniteFourier

open Finset
open scoped BigOperators ComplexConjugate

variable {Q : ℕ} [NeZero Q]

private noncomputable def transform (f : ZMod Q → ℂ) (k : ZMod Q) : ℂ :=
  ∑ r : ZMod Q, f r * ZMod.stdAddChar (r * k)

private theorem char_sum (n : ZMod Q) :
    ∑ k : ZMod Q, ZMod.stdAddChar (n * k) = if n = 0 then (Q : ℂ) else 0 := by
  split_ifs with hn
  · simp [hn, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar Q hn)

private theorem conj_char (a : ZMod Q) :
    conj (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

private theorem parseval_cyclic (f : ZMod Q → ℂ) :
    ∑ k : ZMod Q, ‖transform f k‖ ^ 2 = (Q : ℝ) * ∑ r : ZMod Q, ‖f r‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  calc
    _ = ∑ k : ZMod Q, ∑ r : ZMod Q, ∑ s : ZMod Q,
        (f r * conj (f s)) * ZMod.stdAddChar ((r - s) * k) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [transform, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, conj_char]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    _ = ∑ r : ZMod Q, ∑ s : ZMod Q, (f r * conj (f s)) *
        ∑ k : ZMod Q, ZMod.stdAddChar ((r - s) * k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp only [char_sum, sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

private theorem transform_correlation (a g : ZMod Q → ℂ) (k : ZMod Q) :
    transform (fun y => ∑ h : ZMod Q, a h * g (y + h)) k =
      transform g k * transform a (-k) := by
  calc
    _ = ∑ h : ZMod Q, ∑ y : ZMod Q, a h * g (y + h) * ZMod.stdAddChar (y * k) := by
      simp only [transform, Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ h : ZMod Q, ∑ z : ZMod Q,
        a h * g z * ZMod.stdAddChar ((z - h) * k) := by
      apply Finset.sum_congr rfl
      intro h _
      exact Fintype.sum_equiv (Equiv.addRight h) _ _ (fun y => by simp)
    _ = _ := by
      simp only [transform, Finset.mul_sum, Finset.sum_mul, mul_neg]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro z _
      rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

private theorem cyclic_energy_bound (a : ZMod Q → ℂ) (g : ℕ → ZMod Q → ℂ)
    (N : ℕ) (M : ℝ) (hG : ∀ k, (∑ x ∈ range N, ‖transform (g x) k‖ ^ 2) ≤ M) :
    (∑ x ∈ range N, ∑ y : ZMod Q, ‖∑ h : ZMod Q, a h * g x (y + h)‖ ^ 2) ≤
      M * ∑ h : ZMod Q, ‖a h‖ ^ 2 := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne Q))
  refine le_of_mul_le_mul_left ?_ hQ
  calc
    _ = ∑ x ∈ range N, ∑ k : ZMod Q,
        ‖transform (fun y => ∑ h : ZMod Q, a h * g x (y + h)) k‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => (parseval_cyclic _).symm)
    _ = ∑ k : ZMod Q, (∑ x ∈ range N, ‖transform (g x) k‖ ^ 2) *
        ‖transform a (-k)‖ ^ 2 := by
      simp only [transform_correlation, norm_mul, mul_pow, Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ ∑ k : ZMod Q, M * ‖transform a (-k)‖ ^ 2 := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hG k) (sq_nonneg _))
    _ = M * ((Q : ℝ) * ∑ h : ZMod Q, ‖a h‖ ^ 2) := by
      rw [← Finset.mul_sum, ← parseval_cyclic]
      congr 1
      exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
    _ = _ := by ring

private theorem sum_zmod_range {β : Type*} [AddCommMonoid β] (f : ZMod Q → β) :
    ∑ z : ZMod Q, f z = ∑ r ∈ range Q, f (r : ZMod Q) := by
  let e : ZMod Q ≃ Fin Q :=
    { toFun := fun z => ⟨z.val, z.val_lt⟩
      invFun := fun r => r.val
      left_inv := ZMod.natCast_zmod_val
      right_inv := fun r => Fin.ext (ZMod.val_natCast_of_lt r.isLt) }
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv e _ _ (fun z => congrArg f (ZMod.natCast_zmod_val z).symm)

private theorem char_nat_phase (k : ZMod Q) (r : ℕ) :
    ZMod.stdAddChar ((r : ZMod Q) * k) =
      Complex.exp ((2 * Real.pi * ((k.val : ℝ) / Q) * r : ℝ) * Complex.I) := by
  calc
    _ = ZMod.stdAddChar (((r * k.val : ℕ) : ℤ) : ZMod Q) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    _ = _ := by
      rw [ZMod.stdAddChar_coe]
      congr 1
      push_cast
      ring

/-- Padding the short sign sequence by zero lets the (2m)-point transform
control the smoothed correlations. The indices (y+h<2m) do not wrap. -/
theorem energy_from_spectrum (a g : ℕ → ℝ) (N m b : ℕ) (e : ℝ)
    (hm : 0 < m) (he : 0 ≤ e) (ha : ∀ h, |a h| ≤ 1)
    (hg : ∀ α : ℝ, (∑ x ∈ range N, ‖∑ r ∈ range (2*m),
      (g (b+x+r+1) : ℂ) * Complex.exp ((2 * Real.pi * α * r : ℝ) * Complex.I)‖^2) ≤
      e * (m : ℝ)^2 * (N : ℝ)) :
    (∑ x ∈ range N, ∑ y ∈ range m, (∑ h ∈ range m, a h * g (b+x+y+h+1))^2) ≤
      e * (m : ℝ)^3 * (N : ℝ) := by
  let _ : NeZero (2*m) := ⟨by omega⟩
  let A (z : ZMod (2*m)) : ℂ := if z.val < m then (a z.val : ℂ) else 0
  let G (x : ℕ) (z : ZMod (2*m)) : ℂ := (g (b+x+z.val+1) : ℂ)
  let M := e * (m : ℝ)^2 * (N : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hphase (x : ℕ) (k : ZMod (2*m)) :
      transform (G x) k = ∑ r ∈ range (2*m), (g (b+x+r+1) : ℂ) *
        Complex.exp ((2 * Real.pi * ((k.val : ℝ) / (2*m : ℕ)) * r : ℝ) * Complex.I) := by
    rw [transform, sum_zmod_range]
    apply Finset.sum_congr rfl
    intro r hr
    rw [char_nat_phase]
    simp [G, ZMod.val_natCast_of_lt (Finset.mem_range.mp hr)]
  have hG (k : ZMod (2*m)) : (∑ x ∈ range N, ‖transform (G x) k‖^2) ≤ M := by
    simp only [hphase]
    exact hg _
  have hsub : range m ⊆ range (2*m) := range_mono (by omega)
  have hA (h : ℕ) (hh : h ∈ range m) : A (h : ZMod (2*m)) = (a h : ℂ) := by
    have hh' := Finset.mem_range.mp hh
    simp [A, ZMod.val_natCast_of_lt (show h < 2*m by omega), hh']
  have hAz (h : ℕ) (hh : h ∈ range (2*m)) (hn : h ∉ range m) :
      A (h : ZMod (2*m)) = 0 := by
    simpa only [A, ZMod.val_natCast_of_lt (Finset.mem_range.mp hh), Finset.mem_range,
      if_neg] using (show (if h < m then (a h : ℂ) else 0) = 0 from if_neg (mt Finset.mem_range.mpr hn))
  have hsign : ∑ h : ZMod (2*m), ‖A h‖^2 ≤ (m : ℝ) := by
    rw [sum_zmod_range]
    rw [← Finset.sum_subset hsub (f := fun h : ℕ => ‖A (h : ZMod (2*m))‖^2)
      (fun h hh hn => by simp [hAz h hh hn])]
    calc
      _ ≤ ∑ _h ∈ range m, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        rw [hA h hh, Complex.norm_real, Real.norm_eq_abs]
        simpa using (sq_le_sq.mpr (by simpa using ha h) : (a h)^2 ≤ (1:ℝ)^2)
      _ = _ := by simp
  have hcorr (x y : ℕ) (hy : y ∈ range m) :
      (∑ h : ZMod (2*m), A h * G x ((y : ZMod (2*m)) + h)) =
        ((∑ h ∈ range m, a h * g (b+x+y+h+1) : ℝ) : ℂ) := by
    rw [sum_zmod_range, Complex.ofReal_sum]
    rw [← Finset.sum_subset hsub (f := fun h : ℕ => A (h : ZMod (2*m)) *
        G x ((y : ZMod (2*m)) + (h : ZMod (2*m))))
      (fun h hh hn => by simp [hAz h hh hn])]
    apply Finset.sum_congr rfl
    intro h hh
    have hlt : y+h < 2*m := by
      have := Finset.mem_range.mp hy
      have := Finset.mem_range.mp hh
      omega
    rw [hA h hh, ← Nat.cast_add, Complex.ofReal_mul]
    simp only [G, ZMod.val_natCast_of_lt hlt]
    ring_nf
  have henergy := cyclic_energy_bound A G N M hG
  calc
    _ ≤ ∑ x ∈ range N, ∑ y : ZMod (2*m), ‖∑ h : ZMod (2*m), A h * G x (y+h)‖^2 := by
      apply Finset.sum_le_sum
      intro x _
      rw [sum_zmod_range]
      calc
        _ = ∑ y ∈ range m, ‖∑ h : ZMod (2*m), A h * G x ((y : ZMod (2*m))+h)‖^2 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hcorr x y hy, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ M * ∑ h : ZMod (2*m), ‖A h‖^2 := henergy
    _ ≤ M * m := mul_le_mul_of_nonneg_left hsign hM
    _ = _ := by dsimp [M]; ring

end OMA.ChowlaFiniteFourier

open OMA.ChowlaFiniteFourier

theorem OMA.solution : OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_uniform_R1.H2 := by
  intro f g hf hg N m b e hm hmN he hSpectrum
  obtain ⟨a, ha, hSmoothing⟩ := exists_signs_shift_smoothing f g hf hg N m b hm hmN
  have hEnergy := energy_from_spectrum a g N m b e hm he ha hSpectrum
  have hBound := smoothed_le_of_energy (fun x y => f (x+y+1))
    (fun x y => ∑ h ∈ Finset.range m, a h * g (b+x+y+h+1)) N m e hm
    (fun x y => hf (x+y+1)) he hEnergy
  exact hSmoothing.trans (add_le_add hBound le_rfl)
