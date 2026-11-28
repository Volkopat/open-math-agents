import OMAStatements.S_oeis_a056828
import Mathlib

/-!
Mollin and Walsh conjectured that six positive integers are missing from sums of at most three
powerful numbers (OEIS A056828). Decomposing a positive integer as a square times a squarefree
kernel reduces the conjecture to two families. This file checks the small squarefree candidates
and small prime-square multiples explicitly.

The proof of Legendre's three-square theorem below is Ankeny's argument, formalized by
@amurthy04 in proofs/OeisA241898.conjecture_2.lean (PR 1166) and extracted by @ivillar in
proofs/OeisA280831.conjecture.R1.H1.lean. Their proof is reused with its namespace renamed.
-/

-- Credit: @dwilfand-sys for the reduction, square scaling, and finite witnesses.
open MeasureTheory

namespace MollinWalshThreeSquares

private def S3 (k : ℕ) : Prop := ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = k

lemma dvd_of_dvd_sq_add (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (m R : ℤ)
    (hmR : (p : ℤ) ∣ m - R ^ 2) (hpm : ¬ (p : ℤ) ∣ m) (e y : ℤ)
    (h : (p : ℤ) ∣ e ^ 2 + m * y ^ 2) : (p : ℤ) ∣ e ∧ (p : ℤ) ∣ y := by
  have hm' : (m : ZMod p) = (R : ZMod p) ^ 2 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (m - R ^ 2) p).mpr hmR
    push_cast at h0
    linear_combination h0
  have hR : (R : ZMod p) ≠ 0 := by
    intro hR
    apply hpm
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hm', hR]
    simp
  have h' : (e : ZMod p) ^ 2 + (R : ZMod p) ^ 2 * (y : ZMod p) ^ 2 = 0 := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (e ^ 2 + m * y ^ 2) p).mpr h
    push_cast at h0
    rw [hm'] at h0
    exact h0
  have hy : (y : ZMod p) = 0 := by
    by_contra hy
    have hRy : (R : ZMod p) * (y : ZMod p) ≠ 0 := mul_ne_zero hR hy
    have hsq : IsSquare (-1 : ZMod p) := by
      refine ⟨(e : ZMod p) * ((R : ZMod p) * (y : ZMod p))⁻¹, ?_⟩
      field_simp
      linear_combination -h'
    exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp
  have he : (e : ZMod p) = 0 := by
    rw [hy] at h'
    simpa using h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd e p).mp he,
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy⟩

lemma even_padicValNat_sq_add (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (m R : ℤ)
    (hmR : (p : ℤ) ∣ m - R ^ 2) (hpm : ¬ (p : ℤ) ∣ m) :
    ∀ (N : ℕ) (e y : ℤ), (N : ℤ) = e ^ 2 + m * y ^ 2 → Even (padicValNat p N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro e y hN
    by_cases hN0 : N = 0
    · subst hN0; simp
    by_cases hpN : p ∣ N
    · have hpN' : (p : ℤ) ∣ e ^ 2 + m * y ^ 2 := by rw [← hN]; exact_mod_cast hpN
      obtain ⟨⟨e', rfl⟩, ⟨y', rfl⟩⟩ := dvd_of_dvd_sq_add p hp m R hmR hpm e y hpN'
      have hpp : p.Prime := Fact.out
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      have hdvd : (p ^ 2 : ℕ) ∣ N := by
        have : ((p ^ 2 : ℕ) : ℤ) ∣ (N : ℤ) :=
          ⟨e' ^ 2 + m * y' ^ 2, by rw [hN]; push_cast; ring⟩
        exact_mod_cast this
      obtain ⟨N', rfl⟩ := hdvd
      have hN'0 : N' ≠ 0 := by rintro rfl; simp at hN0
      have hN' : (N' : ℤ) = e' ^ 2 + m * y' ^ 2 := by
        have h2 : (p : ℤ) ^ 2 * (N' : ℤ) = (p : ℤ) ^ 2 * (e' ^ 2 + m * y' ^ 2) := by
          have := hN; push_cast at this; linear_combination this
        exact mul_left_cancel₀ (pow_ne_zero 2 hp0) h2
      have hlt : N' < p ^ 2 * N' := by
        have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hpp.one_lt
        nlinarith [Nat.pos_of_ne_zero hN'0]
      have hev := ih N' hlt e' y' hN'
      rw [padicValNat.mul (pow_ne_zero 2 hpp.ne_zero) hN'0, padicValNat.prime_pow]
      exact Even.add even_two hev
    · rw [padicValNat.eq_zero_of_not_dvd hpN]; exact Even.zero

lemma form_is_two_squares (m Q : ℕ) (hQ0 : 0 < Q) (hm : Squarefree m) (hQm : m ∣ Q + 1)
    (hQ : ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ Q) (G : ℕ) (R e y : ℤ)
    (h1 : (m : ℤ) = R ^ 2 + G) (h2 : (Q : ℤ) * G = e ^ 2 + m * y ^ 2) (h3 : (m : ℤ) ∣ R - e) :
    ∃ u w : ℕ, G = u ^ 2 + w ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro p hp hp4
  obtain ⟨hpp, hpG, hG0⟩ := Nat.mem_primeFactors.mp hp
  have : Fact p.Prime := ⟨hpp⟩
  have hpG' : (p : ℤ) ∣ (G : ℤ) := by exact_mod_cast hpG
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have hp0 : (p : ℤ) ≠ 0 := hprime.ne_zero
  have hpm : ¬ (p : ℤ) ∣ m := by
    intro hpm
    have hpR : (p : ℤ) ∣ R := by
      have hR2 : (p : ℤ) ∣ R ^ 2 := by
        have : R ^ 2 = m - G := by linear_combination -h1
        rw [this]; exact dvd_sub hpm hpG'
      exact hprime.dvd_of_dvd_pow hR2
    have hpe : (p : ℤ) ∣ e := by
      have hRe : (p : ℤ) ∣ R - e := dvd_trans hpm h3
      have h := dvd_sub hpR hRe
      simpa using h
    obtain ⟨R', rfl⟩ := hpR
    obtain ⟨e', rfl⟩ := hpe
    obtain ⟨G', hG'⟩ := hpG'
    obtain ⟨m', hm'⟩ := hpm
    have e1 : m' = p * R' ^ 2 + G' := by
      apply mul_left_cancel₀ hp0
      rw [← hm', h1, hG']; ring
    have e2 : G' * (Q - y ^ 2) = p * (e' ^ 2 + R' ^ 2 * y ^ 2) := by
      apply mul_left_cancel₀ hp0
      have h2' := h2
      rw [hG', hm', e1] at h2'
      linear_combination h2'
    have hdvd : (p : ℤ) ∣ G' * (Q - y ^ 2) := ⟨_, e2⟩
    rcases hprime.dvd_or_dvd hdvd with hG'p | hQy
    · have hm'p : (p : ℤ) ∣ m' := by rw [e1]; exact dvd_add (dvd_mul_right _ _) hG'p
      obtain ⟨m'', rfl⟩ := hm'p
      have hsq : p * p ∣ m := by
        have : ((p * p : ℕ) : ℤ) ∣ (m : ℤ) := ⟨m'', by rw [hm']; push_cast; ring⟩
        exact_mod_cast this
      have hu := hm p hsq
      rw [Nat.isUnit_iff] at hu
      exact hpp.one_lt.ne' hu
    · have hQ1 : (p : ℤ) ∣ (Q : ℤ) + 1 := by
        have hmQ : (m : ℤ) ∣ ((Q + 1 : ℕ) : ℤ) := by exact_mod_cast hQm
        have hpm' : (p : ℤ) ∣ (m : ℤ) := ⟨m', hm'⟩
        have := dvd_trans hpm' hmQ
        simpa using this
      have hy1 : (p : ℤ) ∣ y ^ 2 + 1 := by
        have h := dvd_sub hQ1 hQy
        have e : (Q : ℤ) + 1 - (Q - y ^ 2) = y ^ 2 + 1 := by ring
        rwa [e] at h
      have hz : ((y : ZMod p)) ^ 2 + 1 = 0 := by
        have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (y ^ 2 + 1) p).mpr hy1
        push_cast at h; exact h
      have hsq : IsSquare (-1 : ZMod p) := ⟨(y : ZMod p), by linear_combination -hz⟩
      exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp4
  have hmR : (p : ℤ) ∣ m - R ^ 2 := by
    have : (m : ℤ) - R ^ 2 = G := by linear_combination h1
    rw [this]; exact hpG'
  have hev := even_padicValNat_sq_add p hp4 m R hmR hpm (Q * G) e y (by push_cast; exact h2)
  rw [padicValNat.mul hQ0.ne' hG0, padicValNat.eq_zero_of_not_dvd (hQ p hpp hp4), zero_add] at hev
  exact hev



lemma mink (m Q : ℕ) (b : ℤ) (hm0 : 0 < m) (hQ0 : 0 < Q) :
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (Q : ℤ) * (Q * x + b * y + m * z) ^ 2 + (Q * x + b * y) ^ 2 + m * y ^ 2 < 2 * m * Q := by
  classical
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨a, ha0, ha2⟩ : ∃ a : ℝ, 0 < a ∧ a ^ 2 = Q :=
    ⟨Real.sqrt Q, Real.sqrt_pos.mpr hQr, Real.sq_sqrt hQr.le⟩
  obtain ⟨c, hc0, hc2⟩ : ∃ c : ℝ, 0 < c ∧ c ^ 2 = m :=
    ⟨Real.sqrt m, Real.sqrt_pos.mpr hmr, Real.sq_sqrt hmr.le⟩
  obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = 2 * m * Q :=
    ⟨Real.sqrt (2 * m * Q), Real.sqrt_pos.mpr (by positivity), Real.sq_sqrt (by positivity)⟩
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![a * Q, a * b, a * m; Q, b, 0; 0, c, 0]
  have hdet : M.det = a * c * m * Q := by
    simp [M, Matrix.det_fin_three]
    ring
  let f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' M
  have hfdet : LinearMap.det f = a * c * m * Q := by
    rw [LinearMap.det_toLin', hdet]
  have hdpos : 0 < a * c * m * Q := by positivity
  let g : (Fin 3 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap
  let B : Set (Fin 3 → ℝ) := g ⁻¹' (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)
  let s : Set (Fin 3 → ℝ) := f ⁻¹' B
  have hBvol : volume B = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
    have h1 := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
      (measurableSet_ball (x := (0 : EuclideanSpace ℝ (Fin 3))) (ε := r)).nullMeasurableSet
    rw [EuclideanSpace.volume_ball_fin_three] at h1
    exact h1
  have hsvol : volume s =
      ENNReal.ofReal |(a * c * m * Q)⁻¹| * (ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) := by
    have h1 := Measure.addHaar_preimage_linearMap (volume : Measure (Fin 3 → ℝ)) (f := f)
      (by rw [hfdet]; exact hdpos.ne') B
    rw [hfdet, hBvol] at h1
    exact h1
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) (volume : Measure (Fin 3 → ℝ))
  have hF : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp
  have h_symm : ∀ v ∈ s, -v ∈ s := by
    intro v hv
    simp only [s, B, Set.mem_preimage, mem_ball_zero_iff, map_neg, norm_neg] at hv ⊢
    exact hv
  have h_conv : Convex ℝ s :=
    ((convex_ball (0 : EuclideanSpace ℝ (Fin 3)) r).linear_preimage g).linear_preimage f
  have hvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) *
      2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume s := by
    rw [hF, hsvol, Module.finrank_fin_fun, one_mul, ← ENNReal.ofReal_pow hr0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have h8 : (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 := by norm_num
    rw [h8, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    rw [abs_of_pos (by positivity)]
    have hac : (a * c) ^ 2 = m * Q := by rw [mul_pow, ha2, hc2]; ring
    have hr3 : r ^ 3 = 2 * (a * c) ^ 2 * r := by
      have : r ^ 3 = r ^ 2 * r := by ring
      rw [this, hr2, hac]; ring
    have hrac : 14 / 10 * (a * c) < r := by
      have h0 : 0 < a * c := by positivity
      by_contra hcon
      have hcon' := not_lt.mp hcon
      have h1 : r ^ 2 ≤ (14 / 10 * (a * c)) ^ 2 := by gcongr
      have h2 : (14 / 10 * (a * c)) ^ 2 = 196 / 100 * ((m : ℝ) * Q) := by
        rw [mul_pow, hac]; norm_num
      have hmQ : 0 < (m : ℝ) * Q := by positivity
      rw [hr2, h2] at h1
      nlinarith
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hden : a * c * m * Q = (a * c) ^ 3 := by
      have : a * c * m * Q = (a * c) * (m * Q) := by ring
      rw [this, ← hac]; ring
    rw [hden, hr3]
    have h0 : 0 < a * c := by positivity
    rw [show ((a * c) ^ 3)⁻¹ * (2 * (a * c) ^ 2 * r * (Real.pi * 4 / 3)) =
      (8 * (r * Real.pi)) / (3 * (a * c)) by field_simp; ring]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hcount : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))))
    infer_instance
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv hvol
  have hxmem := x.2
  have hint := ((Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ (x : Fin 3 → ℝ)).mp hxmem
  obtain ⟨n0, hn0⟩ := hint 0
  obtain ⟨n1, hn1⟩ := hint 1
  obtain ⟨n2, hn2⟩ := hint 2
  rw [Pi.basisFun_repr] at hn0 hn1 hn2
  simp only [algebraMap_int_eq, eq_intCast] at hn0 hn1 hn2
  refine ⟨n0, n1, n2, ?_, ?_⟩
  · rintro ⟨h0, h1, h2⟩
    apply hx0
    apply Subtype.ext
    funext i
    fin_cases i
    · simp [← hn0, h0]
    · simp [← hn1, h1]
    · simp [← hn2, h2]
  · have hnorm : ‖g (f (x : Fin 3 → ℝ))‖ < r := by
      simpa [s, B] using hxs
    have hsq : ‖g (f (x : Fin 3 → ℝ))‖ ^ 2 < r ^ 2 := by
      gcongr
    rw [EuclideanSpace.real_norm_sq_eq, hr2, Fin.sum_univ_three] at hsq
    have e0 : (g (f (x : Fin 3 → ℝ))) 0 = a * Q * n0 + a * b * n1 + a * m * n2 := by
      simp [g, f, M, dotProduct, Fin.sum_univ_three, hn0, hn1, hn2]
    have e1 : (g (f (x : Fin 3 → ℝ))) 1 = Q * n0 + b * n1 := by
      simp [g, f, M, dotProduct, Fin.sum_univ_three, hn0, hn1]
    have e2 : (g (f (x : Fin 3 → ℝ))) 2 = c * n1 := by
      simp [g, f, M, dotProduct, Fin.sum_univ_three, hn1]
    rw [e0, e1, e2] at hsq
    have key : ((Q : ℝ) * (Q * n0 + b * n1 + m * n2) ^ 2 + (Q * n0 + b * n1) ^ 2 + m * n1 ^ 2) <
        2 * m * Q := by
      have : (a * Q * n0 + a * b * n1 + a * m * n2) ^ 2 + (Q * n0 + b * n1) ^ 2 + (c * n1) ^ 2 =
          (Q : ℝ) * (Q * n0 + b * n1 + m * n2) ^ 2 + (Q * n0 + b * n1) ^ 2 + m * n1 ^ 2 := by
        rw [← ha2, ← hc2]; ring
      rw [← this]; exact hsq
    exact_mod_cast key

/-- The heart of the three-square theorem: from the auxiliary data `Q, b, h` to a
representation of the squarefree number `m`. -/
lemma three_squares_core (m Q : ℕ) (b h : ℤ) (hm0 : 0 < m) (hQ0 : 0 < Q) (hm : Squarefree m)
    (hQm : m ∣ Q + 1) (hQ : ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ Q)
    (hb : (Q : ℤ) * h = b ^ 2 + m) : S3 m := by
  obtain ⟨x, y, z, hne, hlt⟩ := mink m Q b hm0 hQ0
  have hQz : (0 : ℤ) < Q := by exact_mod_cast hQ0
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm0
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = Q * x + b * y := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℤ, R = e + m * z := ⟨_, rfl⟩
  obtain ⟨Gi, hGi⟩ : ∃ Gi : ℤ, Gi = Q * x ^ 2 + 2 * b * x * y + h * y ^ 2 := ⟨_, rfl⟩
  have hlt' : (Q : ℤ) * R ^ 2 + e ^ 2 + m * y ^ 2 < 2 * m * Q := by
    rw [hR, he]; exact hlt
  have hQG : (Q : ℤ) * Gi = e ^ 2 + m * y ^ 2 := by
    rw [hGi, he]; linear_combination y ^ 2 * hb
  have hG0 : 0 ≤ Gi := by
    by_contra hneg
    have h1 : (Q : ℤ) * Gi < 0 := mul_neg_of_pos_of_neg hQz (lt_of_not_ge hneg)
    have h2 : 0 ≤ e ^ 2 + (m : ℤ) * y ^ 2 := by positivity
    linarith
  have hF2 : R ^ 2 + Gi < 2 * m := by
    by_contra hcon
    have h1 : (Q : ℤ) * (2 * m) ≤ Q * (R ^ 2 + Gi) :=
      mul_le_mul_of_nonneg_left (not_lt.mp hcon) hQz.le
    nlinarith
  have hFpos : 0 < R ^ 2 + Gi := by
    by_contra hcon
    have hR2 : R ^ 2 = 0 := by nlinarith [sq_nonneg R]
    have hGi0 : Gi = 0 := by nlinarith [sq_nonneg R]
    have hR0 : R = 0 := by simpa using hR2
    have hsum : e ^ 2 + (m : ℤ) * y ^ 2 = 0 := by rw [← hQG, hGi0]; ring
    have hy0 : y = 0 := by
      by_contra hy
      have h1 : 0 < y ^ 2 := by positivity
      have h2 : 0 < (m : ℤ) * y ^ 2 := mul_pos hmz h1
      nlinarith [sq_nonneg e]
    have he0 : e = 0 := by
      rw [hy0] at hsum
      have : e ^ 2 = 0 := by linarith
      simpa using this
    have hx0 : x = 0 := by
      rw [he0, hy0] at he
      have h1 : (Q : ℤ) * x = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hQz.ne'
      · exact h2
    have hz0 : z = 0 := by
      rw [hR0, he0] at hR
      have h1 : (m : ℤ) * z = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hmz.ne'
      · exact h2
    exact hne ⟨hx0, hy0, hz0⟩
  obtain ⟨k, hk⟩ := hQm
  have hk' : (Q : ℤ) + 1 = m * k := by exact_mod_cast hk
  have hmF : (m : ℤ) ∣ R ^ 2 + Gi := by
    have h1 : (m : ℤ) ∣ Q * (R ^ 2 + Gi) := by
      refine ⟨k * e ^ 2 + 2 * Q * e * z + Q * m * z ^ 2 + y ^ 2, ?_⟩
      rw [hR]
      linear_combination hQG + e ^ 2 * hk'
    have hcop : IsCoprime (m : ℤ) (Q : ℤ) := ⟨k, -1, by linear_combination -hk'⟩
    exact hcop.dvd_of_dvd_mul_left h1
  have hFm : R ^ 2 + Gi = m := by
    obtain ⟨t, ht⟩ := hmF
    have ht0 : 0 < t := by
      by_contra hcon
      have : (m : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmz.le (not_lt.mp hcon)
      linarith
    have ht2 : t < 2 := by
      by_contra hcon
      have : (m : ℤ) * 2 ≤ m * t := mul_le_mul_of_nonneg_left (not_lt.mp hcon) hmz.le
      linarith
    have ht1 : t = 1 := by omega
    rw [ht, ht1, mul_one]
  obtain ⟨G, hG⟩ : ∃ G : ℕ, (G : ℤ) = Gi := ⟨Gi.toNat, Int.toNat_of_nonneg hG0⟩
  obtain ⟨u, w, huw⟩ := form_is_two_squares m Q hQ0 hm ⟨k, hk⟩ hQ G R e y
    (by rw [hG]; exact hFm.symm) (by rw [hG]; exact hQG) ⟨z, by rw [hR]; ring⟩
  refine ⟨R.natAbs, u, w, ?_⟩
  have hcast : ((R.natAbs ^ 2 + u ^ 2 + w ^ 2 : ℕ) : ℤ) = (m : ℤ) := by
    have hG' : (G : ℤ) = (u : ℤ) ^ 2 + (w : ℤ) ^ 2 := by exact_mod_cast huw
    push_cast
    rw [sq_abs]
    linarith
  exact_mod_cast hcast

/-- A square root of `-m` modulo `q` gives an integer `b` with `q ∣ b ^ 2 + m`. -/
lemma exists_sq_add_dvd (q : ℕ) (m : ℤ) (hsq : IsSquare ((-m : ℤ) : ZMod q)) :
    ∃ b : ℤ, (q : ℤ) ∣ b ^ 2 + m := by
  obtain ⟨r, hr⟩ := hsq
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective r
  refine ⟨b, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at hr ⊢
  linear_combination -hr

/-- If `m ∣ a + 1` then the Jacobi symbols of `a` and `-1` over `m` agree. -/
lemma jacobi_eq_neg_one (a : ℤ) (m : ℕ) (hdvd : (m : ℤ) ∣ a + 1) :
    jacobiSym a m = jacobiSym (-1) m := by
  apply jacobiSym.mod_left'
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  apply Int.emod_eq_zero_of_dvd
  have : a - -1 = a + 1 := by ring
  rw [this]; exact hdvd

/-- Case `m ≡ 1 (mod 4)`. -/
lemma exists_aux_one (m : ℕ) (hm4 : m % 4 = 1) :
    ∃ (Q : ℕ) (b h : ℤ), 0 < Q ∧ m ∣ Q + 1 ∧ (∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ Q) ∧
      (Q : ℤ) * h = b ^ 2 + m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 1 := ⟨m / 4, by omega⟩
  have hcop : IsCoprime (8 * (j : ℤ) + 1) ((4 * (4 * j + 1) : ℕ) : ℤ) :=
    ⟨-(8 * j + 3), 4 * j + 1, by push_cast; ring⟩
  obtain ⟨q, -, hq, hqc⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 (by omega) hcop
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hqc
  push_cast at ht
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = (4 * j + 1) * t := ⟨_, rfl⟩
  have hq4 : q % 4 = 1 := by
    have : (q : ℤ) = 8 * j + 1 - 4 * T := by rw [hT]; linear_combination -ht
    omega
  have hdvd : ((4 * j + 1 : ℕ) : ℤ) ∣ (q : ℤ) + 1 :=
    ⟨2 - 4 * t, by push_cast; linear_combination -ht⟩
  have : Fact q.Prime := ⟨hq⟩
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd (4 * j + 1) := Nat.odd_iff.mpr (by omega)
  have hJ : jacobiSym (-((4 * j + 1 : ℕ) : ℤ)) q = 1 := by
    have h1 : -((4 * j + 1 : ℕ) : ℤ) = (-1) * ((4 * j + 1 : ℕ) : ℤ) := by ring
    rw [h1, jacobiSym.mul_left, jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_one_mod_four hq4,
      jacobiSym.quadratic_reciprocity_one_mod_four' hmodd hq4,
      jacobi_eq_neg_one _ _ hdvd, jacobiSym.at_neg_one hmodd,
      ZMod.χ₄_nat_one_mod_four (by omega)]
    norm_num
  obtain ⟨b, h, hbh⟩ := exists_sq_add_dvd q _ (ZMod.isSquare_of_jacobiSym_eq_one hJ)
  refine ⟨q, b, h, hq.pos, ?_, ?_, by rw [hbh]⟩
  · have : ((4 * j + 1 : ℕ) : ℤ) ∣ ((q + 1 : ℕ) : ℤ) := by push_cast; push_cast at hdvd; exact hdvd
    exact_mod_cast this
  · intro p hp hp4 hpq
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    omega

/-- Case `m ≡ 2 (mod 4)`. -/
lemma exists_aux_two (m : ℕ) (hm4 : m % 4 = 2) :
    ∃ (Q : ℕ) (b h : ℤ), 0 < Q ∧ m ∣ Q + 1 ∧ (∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ Q) ∧
      (Q : ℤ) * h = b ^ 2 + m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 2 := ⟨m / 4, by omega⟩
  have hcop : IsCoprime (4 * (j : ℤ) + 1) ((4 * (4 * j + 2) : ℕ) : ℤ) :=
    ⟨4 * j + 1, -j, by push_cast; ring⟩
  obtain ⟨q, -, hq, hqc⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 (by omega) hcop
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hqc
  push_cast at ht
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = (2 * j + 1) * t := ⟨_, rfl⟩
  have hqT : (q : ℤ) = 4 * j + 1 - 8 * T := by rw [hT]; linear_combination -ht
  have hq4 : q % 4 = 1 := by omega
  have hdvd : ((4 * j + 2 : ℕ) : ℤ) ∣ (q : ℤ) + 1 :=
    ⟨1 - 4 * t, by push_cast; linear_combination -ht⟩
  have hdvd1 : ((2 * j + 1 : ℕ) : ℤ) ∣ (q : ℤ) + 1 :=
    ⟨2 * (1 - 4 * t), by push_cast; linear_combination -ht⟩
  have : Fact q.Prime := ⟨hq⟩
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hm1odd : Odd (2 * j + 1) := Nat.odd_iff.mpr (by omega)
  have hJ : jacobiSym (-((4 * j + 2 : ℕ) : ℤ)) q = 1 := by
    have h1 : -((4 * j + 2 : ℕ) : ℤ) = (-1) * (2 * ((2 * j + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [h1, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_neg_one hqodd,
      ZMod.χ₄_nat_one_mod_four hq4, jacobiSym.at_two hqodd,
      jacobiSym.quadratic_reciprocity_one_mod_four' hm1odd hq4,
      jacobi_eq_neg_one _ _ hdvd1, jacobiSym.at_neg_one hm1odd,
      ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hj with hj | hj
    · have e1 : q % 8 = 1 := by omega
      have e2 : (2 * j + 1) % 4 = 1 := by omega
      have e3 : q % 2 = 1 := by omega
      have e4 : (2 * j + 1) % 2 = 1 := by omega
      simp [e1, e2, e3, e4]
    · have e1 : q % 8 = 5 := by omega
      have e2 : (2 * j + 1) % 4 = 3 := by omega
      have e3 : q % 2 = 1 := by omega
      have e4 : (2 * j + 1) % 2 = 1 := by omega
      simp [e1, e2, e3, e4]
  obtain ⟨b, h, hbh⟩ := exists_sq_add_dvd q _ (ZMod.isSquare_of_jacobiSym_eq_one hJ)
  refine ⟨q, b, h, hq.pos, ?_, ?_, by rw [hbh]⟩
  · have : ((4 * j + 2 : ℕ) : ℤ) ∣ ((q + 1 : ℕ) : ℤ) := by push_cast; push_cast at hdvd; exact hdvd
    exact_mod_cast this
  · intro p hp hp4 hpq
    have := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    omega

/-- Case `m ≡ 3 (mod 8)`. -/
lemma exists_aux_three (m : ℕ) (hm8 : m % 8 = 3) :
    ∃ (Q : ℕ) (b h : ℤ), 0 < Q ∧ m ∣ Q + 1 ∧ (∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ Q) ∧
      (Q : ℤ) * h = b ^ 2 + m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = 8 * j + 3 := ⟨m / 8, by omega⟩
  have hcop : IsCoprime (4 * (j : ℤ) + 1) ((4 * (8 * j + 3) : ℕ) : ℤ) :=
    ⟨8 * j + 1, -j, by push_cast; ring⟩
  obtain ⟨q, -, hq, hqc⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 (by omega) hcop
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hqc
  push_cast at ht
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = (8 * j + 3) * t := ⟨_, rfl⟩
  have hqT : (q : ℤ) = 4 * j + 1 - 4 * T := by rw [hT]; linear_combination -ht
  have hq4 : q % 4 = 1 := by omega
  have hdvd : ((8 * j + 3 : ℕ) : ℤ) ∣ 2 * (q : ℤ) + 1 :=
    ⟨1 - 8 * t, by push_cast; linear_combination -2 * ht⟩
  have : Fact q.Prime := ⟨hq⟩
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have hmodd : Odd (8 * j + 3) := Nat.odd_iff.mpr (by omega)
  have hJq : jacobiSym (q : ℤ) (8 * j + 3) = 1 := by
    have h2 : jacobiSym (2 * (q : ℤ)) (8 * j + 3) = jacobiSym (-1) (8 * j + 3) :=
      jacobi_eq_neg_one _ _ hdvd
    rw [jacobiSym.mul_left, jacobiSym.at_two hmodd, jacobiSym.at_neg_one hmodd,
      ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four] at h2
    have e1 : (8 * j + 3) % 8 = 3 := by omega
    have e2 : (8 * j + 3) % 4 = 3 := by omega
    have e3 : (8 * j + 3) % 2 = 1 := by omega
    simp [e1, e2, e3] at h2
    linarith
  have hJ : jacobiSym (-((8 * j + 3 : ℕ) : ℤ)) q = 1 := by
    have h1 : -((8 * j + 3 : ℕ) : ℤ) = (-1) * ((8 * j + 3 : ℕ) : ℤ) := by ring
    rw [h1, jacobiSym.mul_left, jacobiSym.at_neg_one hqodd, ZMod.χ₄_nat_one_mod_four hq4,
      jacobiSym.quadratic_reciprocity_one_mod_four' hmodd hq4, hJq]
    norm_num
  obtain ⟨b0, hb0⟩ := exists_sq_add_dvd q _ (ZMod.isSquare_of_jacobiSym_eq_one hJ)
  -- make `b` odd
  obtain ⟨b, hbodd, hb⟩ : ∃ b : ℤ, b % 2 = 1 ∧ (q : ℤ) ∣ b ^ 2 + ((8 * j + 3 : ℕ) : ℤ) := by
    by_cases hpar : b0 % 2 = 1
    · exact ⟨b0, hpar, hb0⟩
    · refine ⟨b0 + q, by omega, ?_⟩
      obtain ⟨c, hc⟩ := hb0
      exact ⟨c + 2 * b0 + q, by linear_combination hc⟩
  have h2dvd : (2 : ℤ) ∣ b ^ 2 + ((8 * j + 3 : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
    exact ⟨2 * k ^ 2 + 2 * k + 4 * j + 2, by rw [hk]; push_cast; ring⟩
  have hcop2 : IsCoprime (2 : ℤ) (q : ℤ) := by
    obtain ⟨s, hs⟩ : ∃ s : ℤ, (q : ℤ) = 2 * s + 1 := ⟨(q : ℤ) / 2, by omega⟩
    exact ⟨-s, 1, by rw [hs]; ring⟩
  obtain ⟨h, hh⟩ := hcop2.mul_dvd h2dvd hb
  refine ⟨2 * q, b, h, by have := hq.pos; omega, ?_, ?_, by push_cast at hh ⊢; linarith⟩
  · have : ((8 * j + 3 : ℕ) : ℤ) ∣ ((2 * q + 1 : ℕ) : ℤ) := by
      push_cast; push_cast at hdvd; exact hdvd
    exact_mod_cast this
  · intro p hp hp4 hpq
    rcases (Nat.Prime.dvd_mul hp).mp hpq with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp hq).mp h2
      omega

/-- **Legendre's three-square theorem** for squarefree numbers. -/
theorem three_squares_squarefree (m : ℕ) (hm : Squarefree m)
    (h8 : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) : S3 m := by
  have hm0 : 0 < m := by omega
  have hcases : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 8 = 3 := by omega
  rcases hcases with h | h | h
  · obtain ⟨Q, b, c, hQ0, hQm, hQ, hb⟩ := exists_aux_one m h
    exact three_squares_core m Q b c hm0 hQ0 hm hQm hQ hb
  · obtain ⟨Q, b, c, hQ0, hQm, hQ, hb⟩ := exists_aux_two m h
    exact three_squares_core m Q b c hm0 hQ0 hm hQm hQ hb
  · obtain ⟨Q, b, c, hQ0, hQm, hQ, hb⟩ := exists_aux_three m h
    exact three_squares_core m Q b c hm0 hQ0 hm hQm hQ hb

end MollinWalshThreeSquares

namespace OMA.R_oeis_a056828_R1

open OMA.S_oeis_a056828

private def exceptions : Finset ℕ := {7, 15, 23, 87, 111, 119}

private def Atom (x : ℕ) : Prop := x = 0 ∨ IsPowerful x

private def Rep (n : ℕ) : Prop :=
  ∃ x y z : ℕ, Atom x ∧ Atom y ∧ Atom z ∧ x + y + z = n

private lemma product_powerful {x y : ℕ} (hx : IsPowerful x) (hy : IsPowerful y) :
    IsPowerful (x * y) := by
  refine ⟨Nat.mul_pos hx.1 hy.1, ?_⟩
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact dvd_mul_of_dvd_left (hx.2 p hp h) y
  · exact dvd_mul_of_dvd_right (hy.2 p hp h) x

private lemma square_powerful {x : ℕ} (hx : 0 < x) : IsPowerful (x ^ 2) := by
  refine ⟨pow_pos hx _, ?_⟩
  intro p hp hd
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2

private lemma cube_powerful {x : ℕ} (hx : 0 < x) : IsPowerful (x ^ 3) := by
  refine ⟨pow_pos hx _, ?_⟩
  intro p hp hd
  have h : p ^ 2 ∣ x ^ 2 := pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2
  exact h.trans (pow_dvd_pow x (by decide : 2 ≤ 3))

private lemma atom_sq_cube (x y : ℕ) : Atom (x ^ 2 * y ^ 3) := by
  by_cases hx : x = 0
  · exact Or.inl (by simp [hx])
  by_cases hy : y = 0
  · exact Or.inl (by simp [hy])
  exact Or.inr (product_powerful (square_powerful (Nat.pos_of_ne_zero hx))
    (cube_powerful (Nat.pos_of_ne_zero hy)))

private lemma lift_rep {n : ℕ} (h : Rep n) (k : ℕ) (hk : 0 < k) : Rep (k^2 * n) := by
  have lift {x : ℕ} (hx : Atom x) : Atom (k ^ 2 * x) := by
    rcases hx with rfl | h
    · exact Or.inl (Nat.mul_zero _)
    · exact Or.inr (product_powerful (square_powerful hk) h)
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := h
  exact ⟨_, _, _, lift hx, lift hy, lift hz, by ring⟩

private lemma of_three_squares {m : ℕ} (h : MollinWalshThreeSquares.S3 m) : Rep m := by
  obtain ⟨x, y, z, hxyz⟩ := h
  have sq (u : ℕ) : Atom (u ^ 2) := by simpa using atom_sq_cube u 1
  exact ⟨_, _, _, sq x, sq y, sq z, hxyz⟩

private def singletonOrEmpty (x : ℕ) : List ℕ := if x = 0 then [] else [x]

private lemma as_list {n : ℕ} (h : Rep n) :
    ∃ s : List ℕ, s.length ≤ 3 ∧ (∀ x ∈ s, IsPowerful x) ∧ s.sum = n := by
  obtain ⟨x, y, z, hx, hy, hz, he⟩ := h
  have len (u : ℕ) : (singletonOrEmpty u).length ≤ 1 := by
    by_cases h : u = 0 <;> simp [singletonOrEmpty, h]
  have total (u : ℕ) : (singletonOrEmpty u).sum = u := by
    by_cases h : u = 0 <;> simp [singletonOrEmpty, h]
  have ok {u v : ℕ} (h : Atom u) (hv : v ∈ singletonOrEmpty u) : IsPowerful v := by
    rcases h with rfl | hu
    · simp [singletonOrEmpty] at hv
    · have hne : u ≠ 0 := Nat.ne_of_gt hu.1
      have h' : v = u := by simpa [singletonOrEmpty, hne] using hv
      simpa only [h'] using hu
  refine ⟨(singletonOrEmpty x ++ singletonOrEmpty y) ++ singletonOrEmpty z, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    have lx := len x
    have ly := len y
    have lz := len z
    omega
  · intro v hv
    simp only [List.mem_append] at hv
    rcases hv with (h | h) | h
    · exact ok hx h
    · exact ok hy h
    · exact ok hz h
  · simpa only [List.sum_append, total] using he

private lemma from_list {n : ℕ} {s : List ℕ} (hl : s.length ≤ 3)
    (ha : ∀ x ∈ s, IsPowerful x) (hs : s.sum = n) : Rep n := by
  have az : Atom 0 := Or.inl rfl
  cases s with
  | nil => exact ⟨0, 0, 0, az, az, az, by simpa using hs⟩
  | cons a t =>
    have aa : Atom a := Or.inr (ha a (by simp))
    cases t with
    | nil => exact ⟨a, 0, 0, aa, az, az, by simpa using hs⟩
    | cons b u =>
      have bb : Atom b := Or.inr (ha b (by simp))
      cases u with
      | nil => exact ⟨a, b, 0, aa, bb, az, by simpa using hs⟩
      | cons c v =>
        have cc : Atom c := Or.inr (ha c (by simp))
        cases v with
        | nil => exact ⟨a, b, c, aa, bb, cc, by simpa [Nat.add_assoc] using hs⟩
        | cons d rest => simp only [List.length_cons] at hl; omega

private structure Witness where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  e : ℕ
  f : ℕ

private def Witness.value (w : Witness) : ℕ :=
  w.a ^ 2 * w.b ^ 3 + w.c ^ 2 * w.d ^ 3 + w.e ^ 2 * w.f ^ 3

private lemma of_table {n : ℕ} {ws : List Witness} (h : n ∈ ws.map Witness.value) : Rep n := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp h
  exact ⟨_, _, _, atom_sq_cube w.a w.b, atom_sq_cube w.c w.d, atom_sq_cube w.e w.f, rfl⟩

private def smallKernels : List Witness := [
    ⟨0, 0, 2, 1, 1, 3⟩, ⟨2, 1, 1, 2, 1, 3⟩, ⟨2, 1, 4, 1, 1, 3⟩,
    ⟨1, 1, 1, 3, 1, 3⟩, ⟨0, 0, 1, 3, 6, 1⟩, ⟨1, 2, 1, 3, 6, 1⟩,
    ⟨4, 1, 1, 3, 6, 1⟩, ⟨2, 1, 1, 3, 8, 1⟩, ⟨2, 1, 1, 3, 3, 2⟩,
    ⟨0, 0, 1, 3, 10, 1⟩, ⟨0, 0, 1, 3, 2, 3⟩, ⟨1, 2, 1, 3, 2, 3⟩,
    ⟨1, 1, 5, 1, 1, 5⟩, ⟨2, 1, 1, 3, 4, 2⟩, ⟨1, 3, 2, 2, 2, 3⟩,
    ⟨1, 1, 7, 1, 1, 5⟩, ⟨3, 1, 7, 1, 1, 5⟩, ⟨1, 3, 6, 1, 4, 2⟩,
    ⟨5, 1, 7, 1, 1, 5⟩, ⟨1, 1, 9, 1, 1, 5⟩, ⟨3, 1, 9, 1, 1, 5⟩,
    ⟨0, 0, 1, 3, 14, 1⟩, ⟨2, 1, 1, 3, 5, 2⟩, ⟨4, 1, 1, 3, 14, 1⟩,
    ⟨0, 0, 2, 1, 3, 3⟩, ⟨2, 1, 1, 2, 3, 3⟩, ⟨2, 1, 4, 1, 3, 3⟩,
    ⟨1, 1, 1, 3, 3, 3⟩, ⟨0, 0, 6, 1, 3, 3⟩, ⟨2, 1, 1, 3, 16, 1⟩,
    ⟨1, 1, 1, 5, 13, 1⟩, ⟨3, 1, 1, 5, 13, 1⟩, ⟨2, 1, 8, 1, 3, 3⟩,
    ⟨2, 1, 1, 3, 6, 2⟩, ⟨1, 3, 10, 1, 5, 2⟩, ⟨1, 3, 2, 3, 5, 2⟩,
    ⟨0, 0, 0, 0, 1, 7⟩, ⟨0, 0, 1, 2, 1, 7⟩, ⟨0, 0, 4, 1, 1, 7⟩,
    ⟨1, 2, 4, 1, 1, 7⟩, ⟨0, 0, 2, 2, 1, 7⟩, ⟨2, 1, 6, 1, 1, 7⟩,
    ⟨2, 1, 12, 1, 3, 3⟩, ⟨7, 1, 1, 5, 15, 1⟩, ⟨0, 0, 8, 1, 1, 7⟩,
    ⟨0, 0, 3, 2, 1, 7⟩, ⟨2, 1, 1, 3, 7, 2⟩, ⟨2, 1, 1, 3, 20, 1⟩,
    ⟨0, 0, 14, 1, 3, 3⟩, ⟨2, 1, 10, 1, 1, 7⟩, ⟨2, 1, 2, 3, 1, 7⟩,
    ⟨2, 1, 1, 3, 4, 3⟩, ⟨0, 0, 4, 2, 1, 7⟩, ⟨1, 2, 4, 2, 1, 7⟩,
    ⟨0, 0, 12, 1, 1, 7⟩, ⟨1, 2, 12, 1, 1, 7⟩, ⟨2, 1, 3, 3, 16, 1⟩,
    ⟨0, 0, 1, 3, 22, 1⟩]

private def smallPrimeMultiples : List Witness := [
    ⟨0, 0, 1, 1, 1, 3⟩, ⟨0, 0, 1, 3, 6, 1⟩, ⟨1, 1, 7, 1, 1, 5⟩,
    ⟨0, 0, 0, 0, 1, 7⟩, ⟨2, 1, 1, 7, 2, 5⟩, ⟨0, 0, 1, 3, 34, 1⟩,
    ⟨4, 1, 3, 3, 42, 1⟩, ⟨0, 0, 1, 3, 50, 1⟩, ⟨2, 1, 3, 3, 4, 6⟩,
    ⟨1, 1, 3, 5, 69, 1⟩, ⟨2, 1, 9, 2, 15, 3⟩, ⟨1, 1, 1, 3, 2, 2⟩,
    ⟨0, 0, 1, 3, 2, 3⟩, ⟨0, 0, 2, 2, 1, 7⟩, ⟨0, 0, 1, 7, 7, 2⟩,
    ⟨0, 0, 22, 1, 1, 11⟩, ⟨1, 2, 1, 3, 50, 1⟩, ⟨2, 2, 46, 1, 9, 3⟩,
    ⟨4, 1, 17, 2, 3, 7⟩, ⟨2, 1, 4, 2, 17, 3⟩, ⟨4, 1, 4, 3, 1, 23⟩,
    ⟨2, 1, 4, 2, 23, 3⟩, ⟨1, 1, 1, 3, 8, 1⟩, ⟨1, 1, 9, 1, 1, 5⟩,
    ⟨1, 2, 3, 3, 18, 1⟩, ⟨0, 0, 1, 7, 28, 1⟩, ⟨1, 2, 1, 11, 38, 1⟩,
    ⟨0, 0, 8, 2, 1, 15⟩, ⟨0, 0, 7, 3, 2, 11⟩, ⟨0, 0, 2, 5, 17, 3⟩,
    ⟨0, 0, 0, 0, 1, 23⟩, ⟨1, 3, 2, 3, 49, 2⟩, ⟨2, 1, 14, 3, 7, 7⟩,
    ⟨1, 1, 2, 1, 1, 7⟩, ⟨0, 0, 2, 3, 5, 3⟩, ⟨5, 1, 1, 5, 45, 1⟩,
    ⟨2, 1, 1, 3, 23, 2⟩, ⟨1, 2, 3, 6, 5, 7⟩, ⟨4, 1, 9, 3, 10, 5⟩,
    ⟨5, 1, 27, 1, 1, 29⟩, ⟨1, 1, 7, 5, 159, 1⟩, ⟨0, 0, 1, 23, 184, 1⟩,
    ⟨2, 1, 13, 3, 5, 14⟩, ⟨2, 1, 64, 1, 1, 43⟩, ⟨1, 1, 10, 1, 1, 7⟩,
    ⟨0, 0, 1, 3, 6, 3⟩, ⟨0, 0, 1, 11, 38, 1⟩, ⟨2, 1, 1, 3, 26, 2⟩,
    ⟨0, 0, 1, 11, 110, 1⟩, ⟨2, 1, 1, 11, 132, 1⟩, ⟨2, 1, 7, 3, 62, 2⟩,
    ⟨3, 2, 82, 1, 5, 11⟩, ⟨2, 1, 31, 3, 64, 2⟩, ⟨1, 1, 165, 1, 23, 5⟩,
    ⟨5, 1, 39, 1, 29, 5⟩, ⟨2, 1, 3, 2, 20, 1⟩, ⟨2, 1, 7, 2, 5, 3⟩,
    ⟨1, 1, 3, 5, 43, 1⟩, ⟨0, 0, 1, 7, 4, 7⟩, ⟨0, 0, 1, 11, 22, 3⟩,
    ⟨1, 3, 4, 3, 2, 17⟩, ⟨1, 2, 7, 7, 1, 26⟩, ⟨0, 0, 1, 19, 190, 1⟩,
    ⟨0, 0, 23, 3, 2, 23⟩, ⟨1, 2, 78, 1, 59, 3⟩, ⟨2, 1, 66, 2, 1, 43⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private lemma kernel_small {m : ℕ} (hm : m ≤ 511) (hmod : m % 8 = 7)
    (hgood : m ∉ exceptions) : Rep m := by
  have cert : ∀ i : Fin 512, i.val % 8 = 7 → i.val ∉ exceptions →
      i.val ∈ smallKernels.map Witness.value := by decide +kernel
  exact of_table (cert ⟨m, by omega⟩ hmod hgood)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private lemma prime_small {m p : ℕ} (hm : m ∈ exceptions) (hp : p.Prime)
    (hb : p ≤ 31) : Rep (p ^ 2 * m) := by
  have hmb : m < 120 := by
    simp only [exceptions, Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have cert : ∀ i : Fin 120, ∀ j : Fin 32, i.val ∈ exceptions → j.val.Prime →
      j.val ^ 2 * i.val ∈ smallPrimeMultiples.map Witness.value := by decide +kernel
  exact of_table (cert ⟨m, hmb⟩ ⟨p, by omega⟩ hm hp)

private def smallAtoms : List ℕ := [0, 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, 64, 72, 81, 100, 108]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private lemma atom_mem {x : ℕ} (hx : Atom x) (hb : x < 120) : x ∈ smallAtoms := by
  rcases hx with rfl | hx
  · decide
  have cert : ∀ i : Fin 120, (∀ j : Fin 120,
      j.val.Prime → j.val ∣ i.val → j.val ^ 2 ∣ i.val) → i.val ∈ smallAtoms := by decide +kernel
  exact cert ⟨x, hb⟩ (fun j => hx.2 j.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private lemma missing {n : ℕ} (hn : n ∈ exceptions) : ¬ Rep n := by
  have hb : n < 120 := by
    simp only [exceptions, Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  rintro ⟨a, b, c, ha, hb', hc, he⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp (atom_mem ha (by omega))
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (atom_mem hb' (by omega))
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp (atom_mem hc (by omega))
  have cert : ∀ i j k : Fin smallAtoms.length,
      smallAtoms.get i + smallAtoms.get j + smallAtoms.get k ∉ exceptions := by decide +kernel
  exact (cert i j k) (by rwa [hi, hj, hk, he])

/-- Only squarefree kernels in this residue class remain. -/
def H1 : Prop := ∀ m : ℕ, Squarefree m → m % 8 = 7 → 511 < m →
  ∃ x y z : ℕ, (x = 0 ∨ IsPowerful x) ∧ (y = 0 ∨ IsPowerful y) ∧
    (z = 0 ∨ IsPowerful z) ∧ x + y + z = m

/-- For an exceptional kernel it suffices to adjoin the square of a single large prime. -/
def H2 : Prop := ∀ m ∈ ({7, 15, 23, 87, 111, 119} : Finset ℕ),
  ∀ p : ℕ, p.Prime → 31 < p → ∃ x y z : ℕ, (x = 0 ∨ IsPowerful x) ∧
    (y = 0 ∨ IsPowerful y) ∧ (z = 0 ∨ IsPowerful z) ∧ x + y + z = p ^ 2 * m

lemma represent {n : ℕ} (hn : 0 < n) (hne : n ∉ exceptions)
    (h1 : H1) (h2 : H2) : Rep n := by
  obtain ⟨m, s, he, hm⟩ := Nat.sq_mul_squarefree n
  have hs : 0 < s := by by_contra! h; simp [show s = 0 by omega] at he; omega
  by_cases bad : m ∈ exceptions
  · have hs1 : s ≠ 1 := by
      intro h
      have hmn : m = n := by simpa [h] using he
      exact hne (hmn ▸ bad)
    obtain ⟨p, hp, k, hsk⟩ := Nat.exists_prime_and_dvd hs1
    have hk : 0 < k := by by_contra! h; simp [show k = 0 by omega] at hsk; omega
    have hbase : Rep (p ^ 2 * m) := by
      by_cases hb : 31 < p
      · exact h2 m bad p hp hb
      · exact prime_small bad hp (by omega)
    have hn' : k ^ 2 * (p ^ 2 * m) = n := by rw [← he, hsk]; ring
    exact hn' ▸ lift_rep hbase k hk
  · have hbase : Rep m := by
      by_cases h7 : m % 8 = 7
      · by_cases hlarge : 511 < m
        · exact h1 m hm h7 hlarge
        · exact kernel_small (by omega) h7 bad
      · have hs4 : ¬ 4 ∣ m := fun h => Nat.prime_two.not_isUnit (hm 2 h)
        have hm4 : m % 4 ≠ 0 := fun h => hs4 (Nat.dvd_of_mod_eq_zero h)
        apply of_three_squares
        exact MollinWalshThreeSquares.three_squares_squarefree m hm (by omega)
    exact he ▸ lift_rep hbase s hs

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a056828.main := by
  intro h1 h2
  ext n
  have hset : n ∈ ({7, 15, 23, 87, 111, 119} : Set ℕ) ↔ n ∈ exceptions := by
    simp [exceptions]
  rw [hset]
  constructor
  · rintro ⟨hn, hno⟩
    by_contra h
    exact hno (as_list (represent hn h h1 h2))
  · intro hn
    have hp : 1 ≤ n := by
      simp only [exceptions, Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    refine ⟨hp, ?_⟩
    rintro ⟨s, hl, ha, hs⟩
    exact missing hn (from_list hl ha hs)

end OMA.R_oeis_a056828_R1

