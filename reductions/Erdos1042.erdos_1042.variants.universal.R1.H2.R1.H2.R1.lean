import OMAReductions.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1
import Mathlib.RingTheory.Polynomial.Dickson

/-!
An affine image of a Dickson root sample yields admissible zeros whenever its
critical-value modulus is at least one. This handles sets containing such samples
in arbitrarily large degrees. The remaining cases are connected and disconnected.
-/

open Polynomial Complex Set Filter Metric Erdos1042

namespace OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1_H2_R1

private theorem degree_dickson (a : ℂ) :
    ∀ n : ℕ, (dickson 1 a n).natDegree = n ∧ (0 < n → (dickson 1 a n).Monic)
  | 0 => by
    norm_num [dickson_zero, show (3 : ℂ[X]) - 1 = 2 by ring]
  | 1 => by simp
  | n + 2 => by
    have h := degree_dickson a (n + 1)
    have hm := h.2 (by omega)
    have hleft : (X * dickson 1 a (n + 1)).natDegree = n + 2 := by
      rw [natDegree_X_mul hm.ne_zero, h.1]
    have hright : (C a * dickson 1 a n).natDegree ≤ n :=
      (natDegree_C_mul_le _ _).trans_eq (degree_dickson a n).1
    have hlt : (C a * dickson 1 a n).natDegree <
        (X * dickson 1 a (n + 1)).natDegree := by omega
    rw [dickson_add_two]
    exact ⟨(natDegree_sub_eq_left_of_natDegree_lt hlt).trans hleft,
      fun _ => (monic_X.mul hm).sub_of_left (degree_lt_degree hlt)⟩

private theorem dickson_eval_sum (x y : ℂ) :
    ∀ n : ℕ, (dickson 1 (x * y) n).eval (x + y) = x ^ n + y ^ n
  | 0 => by norm_num
  | 1 => by simp
  | n + 2 => by
    simp only [dickson_add_two, eval_sub, eval_mul, eval_X, eval_C,
      dickson_eval_sum x y (n + 1), dickson_eval_sum x y n]
    rw [show n + 2 = n + 1 + 1 by omega]
    simp only [pow_succ]
    ring

private theorem dickson_deriv_sum (x y : ℂ) :
    ∀ n : ℕ, (dickson 1 (x * y) n).derivative.eval (x + y) * (x - y) =
      (n : ℂ) * (x ^ n - y ^ n)
  | 0 => by simp [show (3 : ℂ[X]) - 1 = 2 by ring]
  | 1 => by simp
  | n + 2 => by
    have h₁ := dickson_deriv_sum x y (n + 1)
    have h₂ := dickson_deriv_sum x y n
    simp only [dickson_add_two, derivative_sub, derivative_mul, derivative_X, derivative_C,
      zero_mul, zero_add, one_mul, eval_sub, eval_add, eval_mul, eval_X, eval_C, sub_mul,
      add_mul, mul_assoc, h₁, h₂, dickson_eval_sum x y (n + 1)]
    push_cast
    simp only [pow_succ]
    ring

private theorem paired_factors (a z : ℂ) : ∃ x y : ℂ, x + y = z ∧ x * y = a := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (z ^ 2 - 4 * a) (by decide : 0 < 2)
  refine ⟨(z + s) / 2, (z - s) / 2, by ring, ?_⟩
  calc
    _ = (z ^ 2 - s ^ 2) / 4 := by ring
    _ = a := by rw [hs]; ring

private theorem root_of_ellipse_poly (a : ℝ) (n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : (dickson 1 (a : ℂ) n).eval z = I * (1 - (a : ℂ) ^ n)) :
    ∃ w : ℂ, w ^ n = I ∧ z = w + (a : ℂ) / w := by
  obtain ⟨x, y, hsum, hprod⟩ := paired_factors (a : ℂ) z
  have hxy : x ^ n + y ^ n = I * (1 - (a : ℂ) ^ n) := by
    rw [← dickson_eval_sum x y, hprod, hsum]
    exact hz
  have hpn : x ^ n * y ^ n = (a : ℂ) ^ n := by rw [← mul_pow, hprod]
  have hzero : (x ^ n - I) * (y ^ n - I) = 0 := by
    calc
      _ = x ^ n * y ^ n - I * (x ^ n + y ^ n) + I ^ 2 := by ring
      _ = 0 := by rw [hpn, hxy, ← mul_assoc I I, ← pow_two, I_sq]; ring
  have key (x y : ℂ) (hs : x + y = z) (hp : x * y = a) (hx : x ^ n = I) :
      x ^ n = I ∧ z = x + (a : ℂ) / x := by
    have hx0 : x ≠ 0 := by
      intro h
      exact Complex.I_ne_zero (by simpa [h, hn.ne'] using hx.symm)
    refine ⟨hx, ?_⟩
    rw [← hp, mul_comm, mul_div_cancel_right₀ _ hx0, hs]
  rcases mul_eq_zero.mp hzero with h | h
  · exact ⟨x, key x y hsum hprod (sub_eq_zero.mp h)⟩
  · exact ⟨y, key y x (by simpa only [add_comm] using hsum)
      (by simpa only [mul_comm] using hprod) (sub_eq_zero.mp h)⟩

private theorem critical_ellipse_norm (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n)
    (z : ℂ) (hz : (dickson 1 (a : ℂ) n).derivative.eval z = 0) :
    ‖(dickson 1 (a : ℂ) n).eval z - I * (1 - (a : ℂ) ^ n)‖ = 1 + a ^ n := by
  obtain ⟨x, y, hsum, hprod⟩ := paired_factors (a : ℂ) z
  have hd := dickson_deriv_sum x y n
  rw [hprod, hsum, hz, zero_mul] at hd
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hxy : x ^ n = y ^ n :=
    sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left hn0)
  let w := (dickson 1 (a : ℂ) n).eval z
  have hw : w = x ^ n + y ^ n := by
    rw [← dickson_eval_sum x y, hprod, hsum]
  have hw2 : w ^ 2 = (4 : ℂ) * (a : ℂ) ^ n := by
    rw [hw, ← hprod, pow_two]
    calc
      _ = 4 * (x ^ n * y ^ n) := by rw [hxy]; ring
      _ = 4 * (x * y) ^ n := by rw [mul_pow]
  have haN : 0 ≤ a ^ n := pow_nonneg ha _
  have hre : w.re ^ 2 - w.im ^ 2 = 4 * a ^ n := by
    have h := congrArg Complex.re hw2
    simpa [pow_two, Complex.mul_re, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul] using h
  have him : w.im = 0 := by
    have h := congrArg Complex.im hw2
    have h0 : w.re * w.im + w.im * w.re = 0 := by
      have hR : (4 : ℂ) * (a : ℂ)^n = ((4 * a^n : ℝ) : ℂ) := by push_cast; ring
      rw [pow_two, Complex.mul_im, hR, Complex.ofReal_im] at h
      exact h
    have hmul : w.re * w.im = 0 := by linarith [mul_comm (w.im) (w.re)]
    rcases mul_eq_zero.mp hmul with h | h
    · rw [h] at hre
      nlinarith [sq_nonneg w.im]
    · exact h
  let s : ℂ := w - I * (1 - (a : ℂ) ^ n)
  have hsre : s.re = w.re := by simp [s, ← Complex.ofReal_pow, Complex.mul_re]
  have hsim : s.im = -(1 - a ^ n) := by simp [s, him, ← Complex.ofReal_pow, Complex.mul_im]
  have hnrm : ‖s‖ ^ 2 = (1 + a ^ n) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]
    rw [him] at hre
    nlinarith
  exact (pow_left_inj₀ (norm_nonneg s) (by positivity : 0 ≤ 1 + a ^ n)
    (by decide : (2 : ℕ) ≠ 0)).mp hnrm

/-- The Joukowski image of the roots of X^n - I gives the admissible degree-n sample. -/
theorem of_dickson_sample (G : Set ℂ) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n)
    (hG : ∀ w : ℂ, w ^ n = I → w + (a : ℂ) / w ∈ G) :
    ∃ p : ℂ[X], Erdos1042.MonicWithRootsIn G n p ∧
      ∀ z, p.derivative.eval z = 0 → ‖p.eval z‖ = 1 + a ^ n := by
  let d := dickson 1 (a : ℂ) n
  let b := I * (1 - (a : ℂ) ^ n)
  have hd : d.natDegree = n := (degree_dickson a n).1
  have hm : d.Monic := (degree_dickson a n).2 hn
  have hlt : (C b).natDegree < d.natDegree := by simp [hd, hn]
  have hmon : (d - C b).Monic := hm.sub_of_left (degree_lt_degree hlt)
  refine ⟨d - C b, ⟨hmon, (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd, ?_⟩, ?_⟩
  · intro z hz
    have h := (mem_roots hmon.ne_zero).mp hz
    have he : d.eval z = b := sub_eq_zero.mp (by simpa [Polynomial.IsRoot] using h)
    obtain ⟨w, hw, hz'⟩ := root_of_ellipse_poly a n hn z he
    rw [hz']
    exact hG w hw
  · intro z hz
    have hf : d.derivative.eval z = 0 := by simpa using hz
    simpa [d, b] using critical_ellipse_norm a ha n hn z hf

/-- A complex similarity multiplies the critical-value moduli by its scale to the degree. -/
theorem of_similar_dickson_sample (G : Set ℂ) (a : ℝ) (ha : 0 ≤ a)
    (c u : ℂ) (n : ℕ) (hn : 0 < n) (hu : 1 ≤ ‖u‖ ^ n * (1 + a ^ n))
    (hG : ∀ w : ℂ, w ^ n = I → c + u * (w + (a : ℂ) / w) ∈ G) :
    ∃ p : ℂ[X], Erdos1042.MonicWithRootsIn G n p ∧
      ∀ z, p.derivative.eval z = 0 → 1 ≤ ‖p.eval z‖ := by
  let K := (fun z : ℂ => c + u * z) ⁻¹' G
  obtain ⟨q, ⟨hmon, hdeg, hK⟩, hcrit⟩ := of_dickson_sample K a ha n hn hG
  have hu0 : u ≠ 0 := by
    intro h
    have hh : (1 : ℝ) ≤ 0 := by simpa [h, hn.ne'] using hu
    linarith
  have hun0 : u ^ n ≠ 0 := pow_ne_zero n hu0
  have hui0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
  let lin := C u⁻¹ * (X - C c)
  have hlin : lin.natDegree = 1 := by simp [lin, natDegree_C_mul hui0]
  let p := C (u ^ n) * q.comp lin
  have hpm : p.Monic := by
    unfold Polynomial.Monic
    dsimp [p]
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hun0),
      leadingCoeff_comp (by rw [hlin]; decide), hmon.leadingCoeff, hdeg,
      (monic_X_sub_C c).leadingCoeff_C_mul]
    rw [one_mul, inv_pow, mul_inv_cancel₀ hun0]
  have hpd : p.natDegree = n := by
    change (C (u ^ n) * q.comp lin).natDegree = n
    rw [natDegree_C_mul hun0, natDegree_comp, hdeg, hlin, mul_one]
  have hl (z : ℂ) : lin.eval z = u⁻¹ * (z - c) := by simp [lin]
  have hpe (z : ℂ) : p.eval z = u ^ n * q.eval (lin.eval z) := by simp [p, eval_comp]
  refine ⟨p, ⟨hpm, hpd, ?_⟩, ?_⟩
  · intro z hz
    have h := (mem_roots hpm.ne_zero).mp hz
    change p.eval z = 0 at h
    rw [hpe] at h
    have hq := (mul_eq_zero.mp h).resolve_left hun0
    have hmem := hK (lin.eval z) ((mem_roots hmon.ne_zero).mpr hq)
    change c + u * lin.eval z ∈ G at hmem
    rw [hl, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul] at hmem
    simpa [add_comm c] using hmem
  · intro z hz
    have hder : lin.derivative = C u⁻¹ := by simp [lin]
    have hpq : p.derivative.eval z = u ^ n * (u⁻¹ * q.derivative.eval (lin.eval z)) := by
      change (C (u ^ n) * q.comp lin).derivative.eval z = _
      rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp, hder]
      simp only [eval_mul, eval_C, eval_comp]
    have hzero : q.derivative.eval (lin.eval z) = 0 := by
      rw [hpq] at hz
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hun0)).resolve_left hui0
    rwa [hpe, norm_mul, norm_pow, hcrit _ hzero]

/-- The remaining connected sets. -/
def H1 : Prop :=
  ∀ (G : Set ℂ) (r : ℝ), 2 < r → IsConnected G →
    IsCompact G → transfiniteDiameter G = 1 → (0 : ℂ) ∈ G → (r : ℂ) ∈ G →
    (∀ z ∈ G, ∀ w ∈ G, dist z w ≤ r) → (∃ z ∈ G, z.im ≠ 0) →
    ((¬ ∃ c u : ℂ, ‖u‖ = 1 ∧ ∀ t ∈ Icc (-2 : ℝ) 2, c + u * (t : ℂ) ∈ G) ∧
    (¬ ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ), ‖u‖ = 1 ∧ 1 ≤ s ∧
      ∀ z : ℂ, z ^ n = (s : ℂ) ^ n → c + u * z ∈ G) ∧
    ¬ ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧ ∀ z, ‖P.eval z‖ = 1 → z ∈ G) →
    (¬ ∃ᶠ n : ℕ in atTop, ∃ (a : ℝ) (c u : ℂ),
      0 ≤ a ∧ 1 ≤ ‖u‖ ^ n * (1 + a ^ n) ∧
        ∀ w : ℂ, w ^ n = I → c + u * (w + (a : ℂ) / w) ∈ G) →
    ∃ᶠ n : ℕ in atTop, ∃ p : ℂ[X], MonicWithRootsIn G n p ∧
      ∀ z, p.derivative.eval z = 0 → 1 ≤ ‖p.eval z‖

/-- The remaining disconnected sets. -/
def H2 : Prop :=
  ∀ (G : Set ℂ) (r : ℝ), 2 < r → ¬ IsConnected G →
    IsCompact G → transfiniteDiameter G = 1 → (0 : ℂ) ∈ G → (r : ℂ) ∈ G →
    (∀ z ∈ G, ∀ w ∈ G, dist z w ≤ r) → (∃ z ∈ G, z.im ≠ 0) →
    ((¬ ∃ c u : ℂ, ‖u‖ = 1 ∧ ∀ t ∈ Icc (-2 : ℝ) 2, c + u * (t : ℂ) ∈ G) ∧
    (¬ ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ), ‖u‖ = 1 ∧ 1 ≤ s ∧
      ∀ z : ℂ, z ^ n = (s : ℂ) ^ n → c + u * z ∈ G) ∧
    ¬ ∃ P : ℂ[X], P.Monic ∧ 0 < P.natDegree ∧ ∀ z, ‖P.eval z‖ = 1 → z ∈ G) →
    (¬ ∃ᶠ n : ℕ in atTop, ∃ (a : ℝ) (c u : ℂ),
      0 ≤ a ∧ 1 ≤ ‖u‖ ^ n * (1 + a ^ n) ∧
        ∀ w : ℂ, w ^ n = I → c + u * (w + (a : ℂ) / w) ∈ G) →
    ∃ᶠ n : ℕ in atTop, ∃ p : ℂ[X], MonicWithRootsIn G n p ∧
      ∀ z, p.derivative.eval z = 0 → 1 ≤ ‖p.eval z‖

theorem main : H1 → H2 → OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1.H2 := by
  intro connected disconnected G r hr hc hcap hzero hrG hdiam hoff exclusions
  by_cases hs : ∃ᶠ n : ℕ in atTop, ∃ (a : ℝ) (c u : ℂ),
      0 ≤ a ∧ 1 ≤ ‖u‖ ^ n * (1 + a ^ n) ∧
        ∀ w : ℂ, w ^ n = I → c + u * (w + (a : ℂ) / w) ∈ G
  · rw [frequently_atTop] at hs ⊢
    intro N
    obtain ⟨n, hn, a, c, u, ha, hu, hG⟩ := hs (max N 1)
    exact ⟨n, by omega, of_similar_dickson_sample G a ha c u n (by omega) hu hG⟩
  · by_cases hconn : IsConnected G
    · exact connected G r hr hconn hc hcap hzero hrG hdiam hoff exclusions hs
    · exact disconnected G r hr hconn hc hcap hzero hrG hdiam hoff exclusions hs

end OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H2_R1_H2_R1
