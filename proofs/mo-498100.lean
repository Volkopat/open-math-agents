import OMAStatements.S_mo_498100

-- Credit: @city-ships for the complete mathematical construction and Lean proof.
-- Same-day source: https://github.com/city-ships/open-math-agents/blob/c367476e4a24d01cb8f3c4cb93e6f398b9756629/proofs/mo-498100.lean
-- Assembly, independent argument review, and pinned-version verification: @CubeJerry.
-- uses note #75835

/-!
# Unbounded zero-energy multiplicity for finite three-dimensional point arrays

Place K coaxial rings at successive heights separated by 1/t. At t = 0 the ring
blocks decouple. Their distinct angular eigenvalues give an invertible diagonal
Jacobian for the equations det B_i = 0. These equations consequently have a
simultaneous solution for positive t. One real cosine mode per sector then
supplies an independent, zero-sum kernel vector of the physical matrix.

The argument below proves the unboundedness asked in MathOverflow 498100.
The conversion of a neutral kernel vector to a square-integrable threshold
eigenfunction is Theorem 1 of Grinevich and Novikov, arXiv:1610.02319.
-/

namespace Scandone

/-- Fourier coefficient of reciprocal chord length on the regular unit q-gon.
The zero offset contributes zero because division by zero in ℝ is zero. -/
noncomputable def polygonMode (q k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q, Real.cos (2 * k * (j * (Real.pi / q))) /
    (2 * Real.sin (j * (Real.pi / q)))

private theorem sineSumTelescopes (b : ℝ) (q : ℕ) :
    (2 * Real.sin (b / 2)) * ∑ j ∈ Finset.range q, Real.sin (j * b) =
      Real.cos (b / 2) - Real.cos (q * b - b / 2) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    rw [show ((q + 1 : ℕ) : ℝ) * b - b / 2 = q * b + b / 2 by push_cast; ring]
    nlinarith only [Real.two_mul_sin_mul_sin ((q : ℝ) * b) (b / 2)]

/-- The finite Fourier coefficients of the Coulomb interaction on a ring have
a positive cotangent gap up to the Nyquist frequency. -/
theorem polygonMode_gap (q k : ℕ) (hk : 2*k+1 < q) :
    polygonMode q k - polygonMode q (k+1) =
      Real.cot (((2 * (k : ℝ) + 1) * (Real.pi / q)) / 2) := by
  let t := Real.pi / (q : ℝ)
  let b := (2 * (k : ℝ) + 1) * t
  have hq : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have ht : 0 < t := div_pos Real.pi_pos hq
  have hb : 0 < b := mul_pos (by positivity) ht
  have hqt : (q : ℝ) * t = Real.pi := by dsimp [t]; field_simp
  have hqb : (q : ℝ) * b = (2 * (k : ℝ) + 1) * Real.pi := by
    dsimp [b]; rw [mul_left_comm, hqt]
  have hbpi : b < Real.pi := by
    rw [← hqt]; exact mul_lt_mul_of_pos_right (by exact_mod_cast hk) ht
  have hsum : polygonMode q k - polygonMode q (k+1) =
      ∑ j ∈ Finset.range q, Real.sin (j * b) := by
    unfold polygonMode
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hz : j = 0
    · simp [hz]
    have hjlt : (j : ℝ) < q := by exact_mod_cast Finset.mem_range.mp hj
    have hs : 0 < Real.sin (j * t) := Real.sin_pos_of_pos_of_lt_pi
      (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hz) ht)
      (hqt ▸ mul_lt_mul_of_pos_right hjlt ht)
    change Real.cos (2 * (k : ℝ) * (j * t)) / (2 * Real.sin (j * t)) -
      Real.cos (2 * ((k+1 : ℕ) : ℝ) * (j * t)) / (2 * Real.sin (j * t)) = _
    rw [← sub_div, div_eq_iff (mul_ne_zero (by norm_num) hs.ne')]
    have h := Real.two_mul_sin_mul_sin (j * b) (j * t)
    rw [show (j : ℝ) * b - j * t = 2 * k * (j * t) by dsimp [b]; ring,
      show (j : ℝ) * b + j * t = 2 * ((k + 1 : ℕ) : ℝ) * (j * t) by
        dsimp [b]; push_cast; ring] at h
    nlinarith only [h]
  have hc : Real.cos (q * b - b / 2) = - Real.cos (b / 2) := by
    rw [hqb, show (2 * (k : ℝ) + 1) * Real.pi - b / 2 =
      (Real.pi - b / 2) + k * (2 * Real.pi) by ring,
      Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub]
  have htel := sineSumTelescopes b q
  rw [hc] at htel
  rw [hsum, Real.cot_eq_cos_div_sin]
  change _ = Real.cos (b / 2) / Real.sin (b / 2)
  apply (eq_div_iff (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne').2
  linarith

theorem polygonMode_succ_lt (q k : ℕ) (hk : 2*k+1 < q) :
    polygonMode q (k+1) < polygonMode q k := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hb : 0 < ((2 * (k : ℝ) + 1) * (Real.pi / q)) / 2 := by positivity
  have hb' : ((2 * (k : ℝ) + 1) * (Real.pi / q)) / 2 < Real.pi / 2 := by
    have h : (2 * (k : ℝ) + 1) < q := by exact_mod_cast hk
    rw [← mul_div_assoc, div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ)<2),
      div_lt_iff₀ hq]
    nlinarith only [mul_lt_mul_of_pos_left h Real.pi_pos]
  have hgap := polygonMode_gap q k hk
  rw [Real.cot_eq_cos_div_sin] at hgap
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb'⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hb (by linarith [Real.pi_pos])
  linarith only [hgap, div_pos hc hs]

/-- Different physical modes up to half the ring size have different isolated
eigenvalues. This separates the diagonal roots in the stacked-ring construction. -/
theorem polygonMode_lt (q k l : ℕ) (hkl : k < l) (hl : 2*l ≤ q) :
    polygonMode q l < polygonMode q k := by
  induction l with
  | zero => omega
  | succ l ih =>
    have hstep := polygonMode_succ_lt q l (by omega)
    rcases Nat.eq_or_lt_of_le (show k ≤ l by omega) with h | h
    · simpa [h] using hstep
    · exact hstep.trans (ih h (by omega))

end Scandone

namespace ScandoneBlocks

variable {M : ℕ} [NeZero M]

noncomputable def angularChar (k j : ZMod M) : ℂ := ZMod.stdAddChar (k * j)

lemma re_angularChar_nat (k j : ℕ) :
    (angularChar (k : ZMod M) (j : ZMod M)).re =
      Real.cos (2 * (k : ℝ) * ((j : ℝ) * (Real.pi / M))) := by
  unfold angularChar
  rw [show (k : ZMod M) * (j : ZMod M) = (((k : ℤ) * j : ℤ) : ZMod M) by push_cast; rfl,
    ZMod.stdAddChar_coe, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

noncomputable def chord (j : ZMod M) : ℝ :=
  2 * Real.sin (j.val * (Real.pi / M))

lemma chord_mode_sum (k : ℕ) :
    ∑ j : ZMod M, (chord j)⁻¹ * (angularChar (k : ZMod M) j).re =
      ∑ j ∈ Finset.range M, Real.cos (2 * (k : ℝ) * (j * (Real.pi / M))) /
        (2 * Real.sin (j * (Real.pi / M))) := by
  cases M with
  | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
  | succ m =>
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have h := re_angularChar_nat (M := m+1) k j.val
    rw [ZMod.natCast_zmod_val] at h
    rw [h, div_eq_mul_inv, mul_comm]
    rfl

lemma angular_neg (k j : ZMod M) : angularChar k (-j) = star (angularChar k j) := by
  unfold angularChar
  rw [mul_neg]
  change (ZMod.toCircle (-(k*j)) : ℂ) = (starRingEnd ℂ) (ZMod.toCircle (k*j) : ℂ)
  rw [← Circle.coe_inv_eq_conj, AddChar.map_neg_eq_inv]

lemma char_sum (k : ZMod M) : ∑ j, angularChar k j = if k = 0 then (M : ℂ) else 0 := by
  split_ifs with h
  · simp [angularChar, h, AddChar.map_zero_eq_one, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M h)

lemma shifted_char_sum (w : ZMod M → ℂ) (k j : ZMod M) :
    ∑ l, w (l-j) * angularChar k l =
      angularChar k j * ∑ h, w h * angularChar k h := by
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.addRight j)
  intro h
  simp only [show (Equiv.addRight j) h = h+j from rfl, add_sub_cancel_right, angularChar, mul_add,
    AddChar.map_add_eq_mul]
  ring

lemma sin_sum_even (w : ZMod M → ℝ) (hw : ∀ j, w (-j) = w j) (k : ZMod M) :
    ∑ j, w j * (angularChar k j).im = 0 := by
  have h : (∑ j, w j * (angularChar k j).im) =
      ∑ j, -(w j * (angularChar k j).im) := by
    apply Fintype.sum_equiv (Equiv.neg _)
    intro j
    simp [hw, angular_neg]
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- Convolution with an even cyclic kernel acts on a real cosine by one scalar. -/
lemma shifted_cos_sum (w : ZMod M → ℝ) (hw : ∀ j, w (-j) = w j) (k j : ZMod M) :
    ∑ l, w (l-j) * (angularChar k l).re =
      (angularChar k j).re * ∑ h, w h * (angularChar k h).re := by
  have h := congrArg Complex.re (shifted_char_sum (fun h => (w h : ℂ)) k j)
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.im_sum, Complex.mul_im, add_zero,
    sin_sum_even w hw k] at h
  simpa using h

variable {R : Type*} [Fintype R]

noncomputable def siteMatrix (w : R → R → ZMod M → ℝ) :
    Matrix (R × ZMod M) (R × ZMod M) ℝ := fun a b => w a.1 b.1 (b.2 - a.2)

noncomputable def modeMatrix (w : R → R → ZMod M → ℝ) (k : ZMod M) :
    Matrix R R ℝ := fun a b => ∑ j, w a b j * (angularChar k j).re

noncomputable def cosineMode (k : ZMod M) (u : R → ℝ) (a : R × ZMod M) : ℝ :=
  u a.1 * (angularChar k a.2).re

lemma siteMatrix_cosineMode (w : R → R → ZMod M → ℝ)
    (hw : ∀ a b j, w a b (-j) = w a b j) (k : ZMod M) (u : R → ℝ) :
    (siteMatrix w).mulVec (cosineMode k u) = cosineMode k ((modeMatrix w k).mulVec u) := by
  funext ⟨a,j⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, siteMatrix,
    modeMatrix, cosineMode, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  have h := congrArg (u b * ·) (shifted_cos_sum (w a b) (hw a b) k j)
  simp only [Finset.mul_sum] at h
  simpa only [mul_left_comm, mul_comm, mul_assoc, Finset.mul_sum, Finset.sum_mul] using h

lemma cosineMode_zero_sum (k : ZMod M) (hk : k ≠ 0) (u : R → ℝ) :
    ∑ x, cosineMode k u x = 0 := by
  have h := congrArg Complex.re (char_sum k)
  simp only [hk, ite_false, Complex.zero_re, Complex.re_sum] at h
  simp [Fintype.sum_prod_type, cosineMode, ← Finset.mul_sum, h]

end ScandoneBlocks

namespace ScandoneBlocks

variable {M : ℕ} [NeZero M] {R I : Type*}

/-- An auxiliary convolution acts on each ring independently. Its distinct
eigenvalues separate angular sectors, even when their radial profiles differ. -/
theorem cosineModes_independent (w : ZMod M → ℝ) (hw : ∀ j, w (-j) = w j)
    (freq : I → ZMod M) (u : I → R → ℝ) (hu : ∀ i, u i ≠ 0)
    (hdist : Function.Injective (fun i => ∑ j, w j * (angularChar (freq i) j).re)) :
    LinearIndependent ℝ (fun i => cosineMode (freq i) (u i)) := by
  classical
  let T : Module.End ℝ (R × ZMod M → ℝ) :=
    { toFun := fun v a => ∑ j, w (j - a.2) * v (a.1, j)
      map_add' := fun v z => by
        funext a
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        funext a
        simp [Finset.mul_sum, mul_left_comm] }
  apply T.eigenvectors_linearIndependent' _ hdist
  intro i
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    funext a
    change (∑ j, w (j - a.2) * (u i a.1 * (angularChar (freq i) j).re)) =
      (∑ j, w j * (angularChar (freq i) j).re) * (u i a.1 * (angularChar (freq i) a.2).re)
    calc
      _ = u i a.1 * ∑ j, w (j - a.2) * (angularChar (freq i) j).re := by
        simp only [Finset.mul_sum, mul_left_comm]
      _ = _ := by rw [shifted_cos_sum w hw]; ring
  · intro h
    apply hu i
    funext r
    simpa [cosineMode, angularChar, AddChar.map_zero_eq_one] using congrFun h (r, 0)

end ScandoneBlocks

namespace ScandoneTuning

open Filter
open scoped Topology

variable {K : ℕ}

private noncomputable def diagonal (d : Fin K → ℝ) :
    (Fin K → ℝ) →L[ℝ] (Fin K → ℝ) :=
  ContinuousLinearMap.pi fun i => d i • ContinuousLinearMap.proj i

private theorem diagonal_invertible (d : Fin K → ℝ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := diagonal (fun i => (d i)⁻¹))
  · ext a i
    change d i * ((d i)⁻¹ * a i) = a i
    rw [← mul_assoc, mul_inv_cancel₀ (hd i), one_mul]
  · ext a i
    change (d i)⁻¹ * (d i * a i) = a i
    rw [← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]

/-- A differentiable perturbation of the decoupled determinant equations
keeps a simultaneous zero, depending continuously on the perturbation. -/
theorem tune_simple_modes (μ : Fin K → ℝ) (hμ : Function.Injective μ)
    (G : ℝ × (Fin K → ℝ) → (Fin K → ℝ))
    (hG : ContDiffAt ℝ 1 G (0, fun i => -μ i))
    (hdec : ∀ (a : Fin K → ℝ) (i : Fin K), G (0, a) i = ∏ j, (a j + μ i)) :
    ∃ a : ℝ → (Fin K → ℝ), a 0 = (fun i => -μ i) ∧
      ContinuousAt a 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ), G (t, a t) = 0 := by
  let a₀ := fun i => -μ i
  let d := fun i => ∏ j ∈ Finset.univ.erase i, (a₀ j + μ i)
  have h0 : G (0, a₀) = 0 := by
    funext i
    rw [hdec]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [a₀])
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    exact fun h => hji (hμ (by dsimp [a₀] at h; linarith))
  have hslice : HasFDerivAt (fun a => G (0,a)) (diagonal d) a₀ := by
    unfold diagonal
    apply hasFDerivAt_pi.mpr
    intro i
    let rest := fun a : Fin K → ℝ => ∏ j ∈ Finset.univ.erase i, (a j + μ i)
    have hr : DifferentiableAt ℝ rest a₀ := by dsimp [rest]; fun_prop
    have hp := ((hasFDerivAt_apply (𝕜 := ℝ) i a₀).add_const (μ i)).mul hr.hasFDerivAt
    have heq : (fun a : Fin K → ℝ => G (0,a) i) =
        (fun a : Fin K → ℝ => a i + μ i) * rest := by
      funext a
      exact (hdec a i).trans (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [heq]
    simpa only [a₀, neg_add_cancel, zero_smul, zero_add, rest, d] using hp
  have hcomp := (hG.differentiableAt (by norm_num)).hasFDerivAt.comp a₀
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) 0 a₀)
  have heq : fderiv ℝ G (0, a₀) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin K → ℝ) =
      diagonal d := hcomp.unique hslice
  have hinv : (fderiv ℝ G (0, a₀) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin K → ℝ)).IsInvertible :=
    heq ▸ diagonal_invertible d hd
  have h1 : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  refine ⟨hG.implicitFunction h1 hinv, hG.implicitFunction_apply_self h1 hinv,
    (hG.contDiffAt_implicitFunction h1 hinv).continuousAt, ?_⟩
  exact (hG.eventually_apply_implicitFunction h1 hinv).mono fun t ht => ht.trans h0

variable {q : ℕ}

/-- Fourier blocks of separated rings, parametrized by their chord lengths,
cosines of relative angles, and isolated-ring eigenvalues. -/
noncomputable def ringBlock (μ : Fin K → ℝ) (d : Fin q → ℝ)
    (c : Fin K → Fin q → ℝ) (i : Fin K) (t : ℝ) (b : Fin K → ℝ) :
    Matrix (Fin K) (Fin K) ℝ := fun r s =>
  if r = s then b r + μ i else ∑ j : Fin q,
    (t / Real.sqrt (((r.val : ℝ) - (s.val : ℝ)) ^ 2 + t ^ 2 * (d j) ^ 2)) * c i j

lemma ringBlock_zero (μ : Fin K → ℝ) (d : Fin q → ℝ)
    (c : Fin K → Fin q → ℝ) (i : Fin K) (b : Fin K → ℝ) :
    ringBlock μ d c i 0 b = Matrix.diagonal (fun r => b r + μ i) := by
  ext r s
  by_cases h : r = s
  · subst s
    simp [ringBlock]
  · simp [ringBlock, h]

lemma ringBlock_entry_smooth (μ : Fin K → ℝ) (d : Fin q → ℝ)
    (c : Fin K → Fin q → ℝ) (i r s : Fin K) (b : Fin K → ℝ) :
    ContDiffAt ℝ 1 (fun x : ℝ × (Fin K → ℝ) => ringBlock μ d c i x.1 x.2 r s) (0,b) := by
  by_cases h : r = s
  · subst s
    simp [ringBlock]
    fun_prop
  · have hne : (r.val : ℝ) ≠ (s.val : ℝ) := by
      exact_mod_cast fun hv => h (Fin.ext hv)
    have hsq : 0 < ((r.val : ℝ) - (s.val : ℝ)) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    simp [ringBlock, h]
    apply ContDiffAt.sum
    intro j hj
    have hden : ((r.val : ℝ) - (s.val : ℝ)) ^ 2 + (0 : ℝ) ^ 2 * (d j)^2 ≠ 0 := by
      simpa using hsq.ne'
    have hroot := Real.sqrt_ne_zero'.2 hsq
    fun_prop (disch := first | exact hden | simpa using hroot)

lemma ringBlock_det_smooth (μ : Fin K → ℝ) (d : Fin q → ℝ)
    (c : Fin K → Fin q → ℝ) (i : Fin K) (b : Fin K → ℝ) :
    ContDiffAt ℝ 1 (fun x : ℝ × (Fin K → ℝ) => (ringBlock μ d c i x.1 x.2).det) (0,b) := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ hσ
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro j hj
  exact ringBlock_entry_smooth μ d c i (σ j) j b

theorem tune_ring_blocks (μ : Fin K → ℝ) (hμ : Function.Injective μ) (d : Fin q → ℝ)
    (c : Fin K → Fin q → ℝ) :
    ∃ b : ℝ → (Fin K → ℝ), b 0 = (fun i => -μ i) ∧ ContinuousAt b 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, (ringBlock μ d c i t (b t)).det = 0 := by
  let G := fun (x : ℝ × (Fin K → ℝ)) (i : Fin K) => (ringBlock μ d c i x.1 x.2).det
  have hG : ContDiffAt ℝ 1 G (0,fun i => -μ i) :=
    contDiffAt_pi.mpr fun i => ringBlock_det_smooth μ d c i _
  have hdec (b : Fin K → ℝ) (i : Fin K) : G (0,b) i = ∏ j, (b j + μ i) := by
    simp only [G, ringBlock_zero, Matrix.det_diagonal]
  obtain ⟨b, hb0, hbc, hall⟩ := tune_simple_modes μ hμ G hG hdec
  exact ⟨b, hb0, hbc, hall.mono fun t ht i => congrFun ht i⟩

theorem exists_positive_ring_tuning (μ : Fin K → ℝ) (hμ : Function.Injective μ) (d : Fin q → ℝ)
    (c : Fin K → Fin q → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ Set.Ioo 0 ε, ∃ b, ∀ i, (ringBlock μ d c i t b).det = 0 := by
  obtain ⟨b, _, _, h⟩ := tune_ring_blocks μ hμ d c
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h
  let t := min ε δ / 2
  have ht : 0 < t := half_pos (lt_min hε hδ)
  have hlt : t < min ε δ := half_lt_self (lt_min hε hδ)
  refine ⟨t, ⟨ht, hlt.trans_le (min_le_left ..)⟩, b t, hball ?_⟩
  simpa [Real.dist_eq, abs_of_pos ht] using hlt.trans_le (min_le_right ε δ)

end ScandoneTuning

namespace ScandoneSites

variable {q : ℕ} [NeZero q]

noncomputable def chord (j : ZMod q) : ℝ := ‖ZMod.stdAddChar j - 1‖

lemma norm_char_sub (i j : ZMod q) :
    ‖ZMod.stdAddChar j - ZMod.stdAddChar i‖ = chord (j-i) := by
  have h := (ZMod.stdAddChar (N := q)).map_add_eq_mul (j-i) i
  rw [sub_add_cancel] at h
  rw [show ZMod.stdAddChar j - ZMod.stdAddChar i =
        (ZMod.stdAddChar (j-i) - 1) * ZMod.stdAddChar i by rw [sub_mul, one_mul, ← h]]
  simp [ZMod.stdAddChar_apply, chord, Circle.norm_coe]

lemma chord_neg (j : ZMod q) : chord (-j) = chord j := by
  have h := norm_char_sub j (0 : ZMod q)
  simpa [AddChar.map_zero_eq_one, chord, norm_sub_rev] using h.symm

lemma chord_trig (j : ZMod q) : chord j = 2 * Real.sin ((j.val : ℝ) * (Real.pi / q)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hj : (j.val : ℝ) < q := by exact_mod_cast ZMod.val_lt j
  let x := (j.val : ℝ) * (Real.pi / q)
  have hx : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi
    (by dsimp [x]; positivity) (by dsimp [x]; rw [← mul_div_assoc]; exact (div_le_iff₀ hq).2 (by nlinarith [mul_lt_mul_of_pos_right hj Real.pi_pos]))
  have hexp : ZMod.stdAddChar j = Complex.exp (Complex.I * ((2*x : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    dsimp [x]
    push_cast
    ring_nf
  rw [chord, hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
  change ‖2 * Real.sin (2 * x / 2)‖ = 2 * Real.sin x
  rw [show 2*x/2 = x by ring, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

noncomputable def point {K : ℕ} (t : ℝ) (u : Fin K × ZMod q) : EuclideanSpace ℝ (Fin 3) :=
  !₂[(ZMod.stdAddChar u.2).re, (ZMod.stdAddChar u.2).im, (u.1.val : ℝ)/t]

lemma point_injective {K : ℕ} {t : ℝ} (ht : 0<t) :
    Function.Injective (point (K := K) (q := q) t) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ h
  have height := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
  change (r.val : ℝ)/t = (s.val : ℝ)/t at height
  have heq : (r.val : ℝ) = s.val := by
    simpa only [div_mul_cancel₀ _ ht.ne'] using congrArg (fun x : ℝ => x*t) height
  have hrs : r=s := Fin.ext (by exact_mod_cast heq)
  have hij : i=j := by
    apply ZMod.injective_stdAddChar
    exact Complex.ext (congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h)
      (congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h)
  exact Prod.ext hrs hij

lemma point_dist_sq {K : ℕ} (t : ℝ) (r s : Fin K) (i j : ZMod q) :
    dist (point t (r,i)) (point t (s,j)) ^ 2 =
      chord (j-i)^2 + ((r.val : ℝ)/t - (s.val : ℝ)/t)^2 := by
  rw [EuclideanSpace.dist_sq_eq, ← norm_char_sub, Complex.sq_norm, Complex.normSq_apply]
  simp [point, Fin.sum_univ_succ, Real.dist_eq, sq_abs, Complex.sub_re, Complex.sub_im]
  ring

lemma inverse_same_ring {K : ℕ} (t : ℝ) (r : Fin K) (i j : ZMod q) :
    (dist (point t (r,i)) (point t (r,j)))⁻¹ = (chord (j-i))⁻¹ := by
  have h := point_dist_sq t r r i j
  rw [sub_self, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  exact congrArg (·⁻¹) ((sq_eq_sq₀ dist_nonneg (norm_nonneg _)).mp h)

lemma inverse_rings {K : ℕ} (t : ℝ) (ht : 0 < t) (r s : Fin K) (i j : ZMod q) :
    (dist (point t (r,i)) (point t (s,j)))⁻¹ =
      t / Real.sqrt (((r.val : ℝ)-s.val)^2 + t^2 * chord (j-i)^2) := by
  have hsq : (dist (point t (r,i)) (point t (s,j)) * t)^2 =
      ((r.val : ℝ)-s.val)^2 + t^2 * chord (j-i)^2 := by
    rw [mul_pow, point_dist_sq]
    field_simp [ht.ne']
    ring
  have hroot := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (mul_nonneg dist_nonneg ht.le)] at hroot
  rw [← hroot]
  simp [div_eq_mul_inv, mul_inv_rev, ht.ne']

end ScandoneSites

namespace ScandonePhysical

open ScandoneBlocks

variable {K q : ℕ}

lemma chord_even [NeZero q] (j : ZMod q) : chord (-j) = chord j := by
  by_cases hj : j = 0
  · simp [hj]
  have : NeZero j := ⟨hj⟩
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold chord
  rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub (ZMod.val_lt j).le]
  rw [show ((q : ℝ) - (j.val : ℝ)) * (Real.pi / q) =
      Real.pi - (j.val : ℝ) * (Real.pi / q) by field_simp]
  rw [Real.sin_pi_sub]

noncomputable def weight [NeZero q] (t : ℝ) (a : Fin K → ℝ)
    (r s : Fin K) (j : ZMod q) : ℝ :=
  if r = s then (if j = 0 then a r else (chord j)⁻¹)
  else t / Real.sqrt (((r.val : ℝ) - (s.val : ℝ))^2 + t^2 * (chord j)^2)

lemma weight_even [NeZero q] (t : ℝ) (a : Fin K → ℝ) (r s : Fin K) (j : ZMod q) :
    weight t a r s (-j) = weight t a r s j := by
  simp [weight, chord_even]

lemma modeMatrix_weight (Q : ℕ) (t : ℝ) (a : Fin K → ℝ) (i : Fin K) :
    modeMatrix (weight (q := Q+1) t a) ((i.val+1 : ℕ) : ZMod (Q+1)) =
      ScandoneTuning.ringBlock
        (fun h : Fin K => Scandone.polygonMode (Q+1) (h.val+1))
        (fun j : Fin (Q+1) => chord (M := Q+1) j)
        (fun h j => (angularChar ((h.val+1 : ℕ) : ZMod (Q+1)) j).re) i t a := by
  classical
  ext r s
  by_cases hrs : r = s
  · subst s
    simp only [modeMatrix, weight, ite_true, ScandoneTuning.ringBlock]
    rw [← show (∑ j : ZMod (Q+1), (chord j)⁻¹ *
        (angularChar ((i.val+1 : ℕ) : ZMod (Q+1)) j).re) =
        Scandone.polygonMode (Q+1) (i.val+1) from chord_mode_sum (i.val+1)]
    calc
      _ = ∑ j : ZMod (Q+1), ((if j = 0 then a r else 0) +
          (chord j)⁻¹ * (angularChar ((i.val+1 : ℕ) : ZMod (Q+1)) j).re) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = 0 <;> simp [hj, chord, angularChar, AddChar.map_zero_eq_one]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  · simp [modeMatrix, weight, ScandoneTuning.ringBlock, hrs]
    apply Finset.sum_congr rfl
    intro j _
    rfl

end ScandonePhysical

namespace ScandoneChoice

abbrev period (K : ℕ) := 2*K + 1

noncomputable def freq {K : ℕ} (i : Fin K) : ZMod (period K) := (i.val + 1 : ℕ)

noncomputable def spectralValue {K : ℕ} (i : Fin K) : ℝ :=
  Scandone.polygonMode (period K) (i.val + 1)

lemma value_injective (K : ℕ) : Function.Injective (spectralValue (K := K)) := by
  intro i j he
  apply Fin.ext
  change Scandone.polygonMode (period K) (i.val+1) = Scandone.polygonMode (period K) (j.val+1) at he
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hlt := Scandone.polygonMode_lt (period K) (i.val+1) (j.val+1) (by omega)
      (by dsimp [period]; omega)
    exact (ne_of_gt hlt he).elim
  · exact h
  · have hlt := Scandone.polygonMode_lt (period K) (j.val+1) (i.val+1) (by omega)
      (by dsimp [period]; omega)
    exact (ne_of_lt hlt he).elim

lemma freq_ne_zero {K : ℕ} (i : Fin K) : freq i ≠ 0 := by
  intro hz
  have hv := congrArg ZMod.val hz
  have hi : i.val+1 < period K := by dsimp [period]; omega
  simp only [freq, ZMod.val_natCast_of_lt hi, ZMod.val_zero] at hv
  omega

noncomputable def cosWeights {K : ℕ} (i : Fin K) (j : Fin (period K)) : ℝ :=
  (ScandoneBlocks.angularChar (freq i) j).re

lemma tuning (K : ℕ) :
    ∃ (t : ℝ) (_ : 0 < t) (b : Fin K → ℝ), ∀ i : Fin K,
      (ScandoneTuning.ringBlock spectralValue
        (fun j : Fin (period K) => ScandoneBlocks.chord (M := period K) j)
        cosWeights i t b).det = 0 := by
  obtain ⟨t, ht, b, hb⟩ := ScandoneTuning.exists_positive_ring_tuning
    spectralValue (value_injective K)
    (fun j : Fin (period K) => ScandoneBlocks.chord (M := period K) j)
    cosWeights 1 zero_lt_one
  exact ⟨t, ht.1, b, hb⟩

end ScandoneChoice

namespace OMA.S_mo_498100

/-- Transfer a construction with any finite site labels to the numbered sites
of the problem statement, preserving each neutral eigenvector. -/
theorem numbered_witness {S : Type*} [Fintype S] [DecidableEq S] {K : ℕ}
    (hn : 2 ≤ Fintype.card S) (Y : S → Position) (hY : Function.Injective Y)
    (a : S → ℝ) (A : Matrix S S ℝ)
    (hA : ∀ r s, A r s = if r = s then a r else (dist (Y r) (Y s))⁻¹)
    (v : Fin K → S → ℝ) (hind : LinearIndependent ℝ v)
    (hker : ∀ i, A.mulVec (v i) = 0) (hsum : ∀ i, ∑ j, v i j = 0) :
    ∃ (N : ℕ) (y : Fin N → Position) (α : Fin N → ℝ), 2 ≤ N ∧
      Function.Injective y ∧ K ≤ Module.finrank ℝ (modes y α) := by
  classical
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨_, Y ∘ e, a ∘ e, hn, hY.comp e.injective, ?_⟩
  let L : (S → ℝ) →ₗ[ℝ] (Fin (Fintype.card S) → ℝ) :=
    { toFun := fun w r => w (e r)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    intro u w h
    funext r
    obtain ⟨r, rfl⟩ := e.surjective r
    exact congrFun h r
  have hentry (r s : Fin (Fintype.card S)) :
      interaction (Y ∘ e) (a ∘ e) r s = A (e r) (e s) := by
    rw [hA]
    simp [interaction]
  have hm (i : Fin K) : L (v i) ∈ modes (Y ∘ e) (a ∘ e) := by
    constructor
    · funext r
      calc
        _ = ∑ s, A (e r) (e s) * v i (e s) := by
          simp only [Matrix.mulVec, dotProduct, hentry]; rfl
        _ = ∑ s, A (e r) s * v i s := e.sum_comp (fun s => A (e r) s * v i s)
        _ = 0 := congrFun (hker i) (e r)
    · exact (e.sum_comp (v i)).trans (hsum i)
  let v' : Fin K → modes (Y ∘ e) (a ∘ e) := fun i => ⟨L (v i), hm i⟩
  have hi : LinearIndependent ℝ v' :=
    LinearIndependent.of_comp (modes (Y ∘ e) (a ∘ e)).subtype
      (hind.map' L (LinearMap.ker_eq_bot_of_injective hL))
  simpa using hi.fintype_card_le_finrank

end OMA.S_mo_498100

namespace ScandoneAssembly

open ScandoneChoice ScandoneBlocks

lemma entries {K : ℕ} (t : ℝ) (ht : 0 < t) (b : Fin K → ℝ)
    (u v : Fin K × ZMod (period K)) :
    siteMatrix (ScandonePhysical.weight t b) u v =
      if u = v then b u.1 else (dist (ScandoneSites.point t u) (ScandoneSites.point t v))⁻¹ := by
  obtain ⟨r,i⟩ := u
  obtain ⟨s,j⟩ := v
  change ScandonePhysical.weight t b r s (j-i) = _
  by_cases hrs : r=s
  · subst s
    by_cases hij : i=j
    · subst j
      simp [ScandonePhysical.weight]
    · have hji : j-i ≠ 0 := sub_ne_zero.mpr (fun h => hij h.symm)
      simp [ScandonePhysical.weight, hij, hji, ScandoneSites.inverse_same_ring, ScandoneSites.chord_trig,
        ScandoneBlocks.chord]
  · simp [ScandonePhysical.weight, hrs, ScandoneSites.inverse_rings _ ht, ScandoneSites.chord_trig,
      ScandoneBlocks.chord]

lemma many_modes (K : ℕ) (hK : 0 < K) :
    ∃ (N : ℕ) (y : Fin N → OMA.S_mo_498100.Position) (α : Fin N → ℝ),
      2 ≤ N ∧ Function.Injective y ∧ K ≤ Module.finrank ℝ (OMA.S_mo_498100.modes y α) := by
  classical
  obtain ⟨t, ht, b, hdet⟩ := tuning K
  let w : Fin K → Fin K → ZMod (period K) → ℝ := ScandonePhysical.weight t b
  have hsing (i : Fin K) : (modeMatrix w (freq i)).det = 0 := by
    rw [show modeMatrix w (freq i) = _ from ScandonePhysical.modeMatrix_weight (2*K) t b i]
    exact hdet i
  choose u hu hkernel using fun i => Matrix.exists_mulVec_eq_zero_iff.mpr (hsing i)
  let v (i : Fin K) := cosineMode (freq i) (u i)
  have hd : Function.Injective (fun i : Fin K => ∑ j : ZMod (period K),
      (ScandoneBlocks.chord j)⁻¹ * (angularChar (freq i) j).re) := by
    have hh (i : Fin K) : (∑ j : ZMod (period K), (ScandoneBlocks.chord j)⁻¹ *
        (angularChar (freq i) j).re) = spectralValue i := chord_mode_sum (i.val+1)
    simpa only [hh] using value_injective K
  have hind : LinearIndependent ℝ v := cosineModes_independent
    (fun j => (ScandoneBlocks.chord j)⁻¹) (fun j => by rw [ScandonePhysical.chord_even])
    freq u hu hd
  have hv (i : Fin K) : (siteMatrix w).mulVec (v i) = 0 := by
    rw [show v i = cosineMode (freq i) (u i) from rfl,
      siteMatrix_cosineMode w (ScandonePhysical.weight_even t b) _ _, hkernel]
    ext x
    simp [cosineMode]
  have hn : 2 ≤ Fintype.card (Fin K × ZMod (period K)) := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
    dsimp [period]
    nlinarith
  exact OMA.S_mo_498100.numbered_witness hn (ScandoneSites.point t)
    (ScandoneSites.point_injective ht) (fun x => b x.1) (siteMatrix w) (entries t ht b)
    v hind hv (fun i => cosineMode_zero_sum (freq i) (freq_ne_zero i) (u i))

end ScandoneAssembly

theorem OMA.solution : type_of% @OMA.S_mo_498100.main := by
  intro M
  obtain ⟨N,y,α,hN,hy,hd⟩ := ScandoneAssembly.many_modes (M+1) (Nat.succ_pos M)
  exact ⟨N,y,α,hN,hy,(Nat.le_succ M).trans hd⟩
