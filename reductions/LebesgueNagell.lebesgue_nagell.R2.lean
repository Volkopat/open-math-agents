import FormalConjectures.Wikipedia.Catalan
import Mathlib.NumberTheory.Pell
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# A quadratic descent and congruence sieve for the Lebesgue–Nagell equation

The descent follows Theorem 3.1 of Ethan Katz and Kyle Pratt, arXiv:2507.12397,
which in turn credits Bugeaud, Mignotte, and Siksek. The exponent range in the
hypotheses comes from Theorems 1.2–1.4 of Katz and Pratt, including Chen's
congruence exclusion. For each split prime q = kp + 1, evaluate the factorization at both square
roots of 2 modulo q. Each pth power belongs to zero together with the kth
roots of unity. The finite certificates below use this constraint at both
evaluations.
-/

-- Credit: @MrSeizy

open Zsqrtd

namespace OMA.R_LebesgueNagell_lebesgue_nagell_R2

private abbrev R := Zsqrtd 2

private theorem nonsq (n : ℤ) : (2 : ℤ) ≠ n * n := by
  intro h
  have h' : n % 4 * (n % 4) % 4 = 2 := by
    rw [← Int.mul_emod, ← h]
    decide
  have hlo := Int.emod_nonneg n (by decide : (4 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos n (by decide : (0 : ℤ) < 4)
  interval_cases n % 4 <;> norm_num at h'

private theorem norm_ne {z : R} (hz : z ≠ 0) : z.norm ≠ 0 :=
  (Zsqrtd.norm_eq_zero nonsq z).not.mpr hz

private def quotient (x y : R) : R :=
  ⟨round ((x * star y).re / (y.norm : ℚ)), round ((x * star y).im / (y.norm : ℚ))⟩

private theorem round_error (n c : ℤ) (hn : n ≠ 0) :
    |(c : ℚ) - n * (round (c / (n : ℚ)) : ℚ)| ≤ |(n : ℚ)| / 2 := by
  have h := abs_sub_round ((c : ℚ) / (n : ℚ))
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have he : (c : ℚ) - n * (round (c / (n : ℚ)) : ℚ) =
      (n : ℚ) * ((c : ℚ) / (n : ℚ) - round (c / (n : ℚ))) := by
    rw [mul_sub, mul_div_cancel₀ _ hn']
  rw [he, abs_mul]
  calc
    |(n : ℚ)| * |(c : ℚ) / (n : ℚ) - round (c / (n : ℚ))| ≤ |(n : ℚ)| * (1 / 2) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

private theorem norm_remainder (x y : R) (hy : y ≠ 0) :
    (x - y * quotient x y).norm.natAbs < y.norm.natAbs := by
  let r := x - y * quotient x y
  let t := r * star y
  have ht : t = x * star y - (y.norm : R) * quotient x y := by
    dsimp [t, r]
    rw [sub_mul, mul_right_comm y, ← Zsqrtd.norm_eq_mul_conj]
  have hRe : |(t.re : ℚ)| ≤ |(y.norm : ℚ)| / 2 := by
    rw [ht]
    simpa [quotient, Zsqrtd.re_sub, Zsqrtd.re_mul] using
      round_error y.norm (x * star y).re (norm_ne hy)
  have hIm : |(t.im : ℚ)| ≤ |(y.norm : ℚ)| / 2 := by
    rw [ht]
    simpa [quotient, Zsqrtd.im_sub, Zsqrtd.im_mul] using
      round_error y.norm (x * star y).im (norm_ne hy)
  have hn : (0 : ℚ) < |(y.norm : ℚ)| := by
    apply abs_pos.mpr
    exact_mod_cast norm_ne hy
  have hRe2 : (t.re : ℚ) ^ 2 ≤ (|(y.norm : ℚ)| / 2) ^ 2 := by
    apply sq_le_sq.mpr
    rwa [abs_of_nonneg (by positivity : 0 ≤ |(y.norm : ℚ)| / 2)]
  have hIm2 : (t.im : ℚ) ^ 2 ≤ (|(y.norm : ℚ)| / 2) ^ 2 := by
    apply sq_le_sq.mpr
    rwa [abs_of_nonneg (by positivity : 0 ≤ |(y.norm : ℚ)| / 2)]
  have hb : |(t.norm : ℚ)| < |(y.norm : ℚ)| * |(y.norm : ℚ)| := by
    rw [Zsqrtd.norm_def, Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_ofNat]
    exact abs_lt.mpr ⟨by nlinarith [sq_pos_of_pos hn, sq_nonneg (t.re : ℚ)],
      by nlinarith [sq_pos_of_pos hn, sq_nonneg (t.im : ℚ)]⟩
  rw [show t.norm = r.norm * y.norm by rw [show t = r * star y from rfl, norm_mul, norm_conj],
    Int.cast_mul, abs_mul, mul_lt_mul_iff_of_pos_right hn] at hb
  exact_mod_cast (show (r.norm.natAbs : ℚ) < (y.norm.natAbs : ℚ) by simpa using hb)

private instance : EuclideanDomain R where
  __ := Zsqrtd.commRing
  __ := Zsqrtd.nontrivial
  quotient := quotient
  quotient_zero a := by ext <;> simp [quotient]
  remainder a b := a - b * quotient a b
  quotient_mul_add_remainder_eq a b := by abel
  r a b := a.norm.natAbs < b.norm.natAbs
  r_wellFounded := (measure fun a : R => a.norm.natAbs).wf
  remainder_lt := norm_remainder
  mul_left_not_lt a b hb := by
    rw [norm_mul, Int.natAbs_mul]
    exact not_lt_of_ge (Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr (norm_ne hb)))

private theorem odd_x {p : ℕ} (hp : 2 ≤ p) {x y : ℤ}
    (h : x ^ 2 - 2 = y ^ p) : Odd x := by
  rw [Int.odd_iff]
  by_contra! hx
  have hx' : 2 ∣ x := Int.dvd_iff_emod_eq_zero.mpr (by omega)
  obtain ⟨a, ha⟩ := hx'
  have h₂ : (2 : ℤ) ∣ y ^ p := by
    rw [← h, ha]
    exact ⟨2 * a ^ 2 - 1, by ring⟩
  have hy : (2 : ℤ) ∣ y :=
    (Nat.prime_iff_prime_int.mp Nat.prime_two).dvd_of_dvd_pow h₂
  obtain ⟨b, rfl⟩ := hy
  have h₄ : (4 : ℤ) ∣ (2 * b) ^ p := by
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = 2 + k := ⟨p - 2, by omega⟩
    rw [pow_add]
    exact ⟨b ^ 2 * (2 * b) ^ k, by ring⟩
  obtain ⟨c, hc⟩ := h₄
  have h' : 4 * (a ^ 2 - c) = 2 := by rw [ha, hc] at h; linarith
  omega

private theorem factor_identity (x : ℤ) :
    ((⟨x, 1⟩ : R) * ⟨x, -1⟩) = Int.cast (R := R) (x ^ 2 - 2) := by
  apply Zsqrtd.ext
  · rw [re_intCast, re_mul]
    change x * x + 2 * (1 * -1) = x ^ 2 - 2
    ring
  · rw [im_intCast, im_mul]
    change x * -1 + 1 * x = 0
    ring

private theorem factors_coprime {x : ℤ} (hx : Odd x) :
    IsCoprime (⟨x, 1⟩ : R) (⟨x, -1⟩ : R) := by
  obtain ⟨a, ha⟩ := hx
  have h₂ : IsCoprime (2 : ℤ) (x ^ 2 - 2) :=
    ⟨1 - 2 * a * (a + 1), 1, by rw [ha]; ring⟩
  have h₈ : IsCoprime (8 : ℤ) (x ^ 2 - 2) := by
    simpa using h₂.pow_left (m := 3)
  obtain ⟨c, d, hd⟩ := h₈.map (Int.castRingHom R)
  change c * (↑(8 : ℤ) : R) + d * (↑(x ^ 2 - 2 : ℤ) : R) = 1 at hd
  norm_num at hd
  let u : R := ⟨x, 1⟩
  let v : R := ⟨x, -1⟩
  have huv : (u - v) * (u - v) = 8 := by
    apply Zsqrtd.ext <;> norm_num [u, v, Zsqrtd.re_sub, Zsqrtd.im_sub,
      Zsqrtd.re_mul, Zsqrtd.im_mul]
  change IsCoprime u v
  refine ⟨c * (u - v) + d * v, -(c * (u - v)), ?_⟩
  calc
    _ = c * ((u - v) * (u - v)) + d * (u * v) := by ring
    _ = 1 := by rw [huv, factor_identity x]; push_cast; exact hd

private def epsilon : Rˣ where
  val := ⟨1, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by decide
  inv_val := by decide

private theorem norm_epsilon : (epsilon : R).norm = -1 := by decide

private theorem pell_fundamental : Pell.IsFundamental
    (Pell.Solution₁.mk 3 2 (by decide) : Pell.Solution₁ 2) := by
  refine ⟨by decide, by decide, ?_⟩
  intro b hb
  by_contra! hh
  change b.x < 3 at hh
  have hb₂ : b.x = 2 := by omega
  have h := b.prop
  rw [hb₂] at h
  norm_num at h
  omega

private theorem unit_generator (u : Rˣ) :
    ∃ r : ℤ, u = epsilon ^ r ∨ (u : R) = -(↑(epsilon ^ r) : R) := by
  have hun : IsUnit (u : R).norm :=
    (Zsqrtd.isUnit_iff_norm_isUnit _).mp u.isUnit
  have hpm : (u : R).norm = 1 ∨ (u : R).norm = -1 := Int.isUnit_iff.mp hun
  obtain ⟨v, hv, hvu⟩ : ∃ v : Rˣ, (v : R).norm = 1 ∧ (u = v ∨ u = v * epsilon) := by
    rcases hpm with hp | hp
    · exact ⟨u, hp, Or.inl rfl⟩
    · refine ⟨u * epsilon⁻¹, ?_, Or.inr (by simp)⟩
      change ((u : R) * (↑epsilon⁻¹ : R)).norm = 1
      rw [norm_mul, hp]
      decide
  let a : Pell.Solution₁ 2 := ⟨v, Zsqrtd.norm_eq_one_iff_mem_unitary.mp hv⟩
  let f : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by decide)
  have hf : Pell.IsFundamental f := pell_fundamental
  obtain ⟨n, hn⟩ := hf.eq_zpow_or_neg_zpow a
  change (show unitary (Zsqrtd 2) from a) = (show unitary (Zsqrtd 2) from f) ^ n ∨
    (show unitary (Zsqrtd 2) from a) = -(show unitary (Zsqrtd 2) from f) ^ n at hn
  let g : unitary (Zsqrtd 2) := f
  have hfunit : Unitary.toUnits g = epsilon ^ (2 : ℤ) := by decide
  have hpow : Unitary.toUnits (g ^ n) = epsilon ^ (2 * n) := by
    rw [map_zpow, hfunit, ← zpow_mul]
  have hvpow : v = epsilon ^ (2 * n) ∨ (v : R) = -(↑(epsilon ^ (2 * n)) : R) := by
    rcases hn with hp | hp
    · left
      have hav : Unitary.toUnits (show unitary (Zsqrtd 2) from a) = v := Units.ext rfl
      exact hav.symm.trans ((congrArg Unitary.toUnits hp).trans hpow)
    · right
      have hh := congrArg Subtype.val hp
      rw [Unitary.coe_neg] at hh
      have hm := congrArg Units.val hpow
      exact hh.trans (congrArg Neg.neg hm)
  rcases hvu with rfl | rfl
  · exact ⟨2 * n, hvpow⟩
  · refine ⟨2 * n + 1, ?_⟩
    rw [zpow_add, zpow_one]
    rcases hvpow with rfl | hn
    · exact Or.inl rfl
    · exact Or.inr (by push_cast; rw [hn, neg_mul])

private theorem unit_power_factor {p : ℕ} (hp : 2 ≤ p) (ho : Odd p) {x y : ℤ}
    (h : x ^ 2 - 2 = y ^ p) :
    ∃ (r : ℤ) (z : R), (⟨x, 1⟩ : R) = (↑(epsilon ^ r) : R) * z ^ p := by
  have hprod : (⟨x, 1⟩ : R) * ⟨x, -1⟩ = (y : R) ^ p := by
    rw [factor_identity, h, Int.cast_pow]
  obtain ⟨z, u, hu⟩ :=
    exists_associated_pow_of_mul_eq_pow' (factors_coprime (odd_x hp h)) hprod
  obtain ⟨r, hr | hr⟩ := unit_generator u
  · exact ⟨r, z, by rw [← hu, hr, mul_comm]⟩
  · exact ⟨r, -z, by rw [← hu, hr, ho.neg_pow, mul_neg, mul_comm (z ^ p), mul_neg]⟩

private theorem bounded_factor {p : ℕ} (hp : 2 ≤ p) (ho : Odd p) {x y : ℤ}
    (h : x ^ 2 - 2 = y ^ p) :
    ∃ (r : ℕ) (z : R) (x' : ℤ), r ≤ p / 2 ∧
      x' ^ 2 - 2 = y ^ p ∧
      (⟨x', 1⟩ : R) = (⟨1, 1⟩ : R) ^ r * z ^ p := by
  obtain ⟨e, z, hz⟩ := unit_power_factor hp ho h
  let m : ℤ := ((p / 2 : ℕ) : ℤ)
  let k := (e + m) / (p : ℤ)
  let t := (e + m) % (p : ℤ) - m
  have htp : t + k * p = e := by
    have hh := Int.emod_add_ediv_mul (e + m) (p : ℤ)
    dsimp [t, k]
    linarith
  have htlo : -m ≤ t := by
    dsimp [t]
    linarith only [Int.emod_nonneg (e + m) (by omega : (p : ℤ) ≠ 0)]
  have hthi : t ≤ m := by
    have hh := Int.emod_lt_of_pos (e + m) (by omega : (0 : ℤ) < p)
    have hm : (p : ℤ) ≤ 2 * m + 1 := by dsimp [m]; omega
    dsimp [t]
    omega
  let w : R := (↑(epsilon ^ k) : R) * z
  have hw : (⟨x, 1⟩ : R) = (↑(epsilon ^ t) : R) * w ^ p := by
    rw [hz, ← htp, zpow_add, zpow_mul, zpow_natCast]
    push_cast
    dsimp [w]
    rw [mul_pow, mul_assoc]
  by_cases ht : 0 ≤ t
  · have htc : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht
    refine ⟨t.toNat, w, x, by omega, h, ?_⟩
    rw [hw, ← htc, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  · let r := (-t).toNat
    have hrc : (r : ℤ) = -t := Int.toNat_of_nonneg (by omega)
    have htr : t = -(r : ℤ) := by omega
    have hst : star ((↑(epsilon ^ t) : R)) = (-(⟨1, 1⟩ : R)) ^ r := by
      rw [htr, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, star_pow]
      rfl
    have hh := congrArg (fun q : R => -star q) hw
    change (⟨-x, 1⟩ : R) = -star ((↑(epsilon ^ t) : R) * w ^ p) at hh
    rw [star_mul, star_pow, hst, neg_pow] at hh
    refine ⟨r, (-1 : R) ^ (r + 1) * star w, -x, by omega, by simpa using h, ?_⟩
    rw [hh, mul_pow, ← pow_mul, mul_comm (r + 1) p, pow_mul, ho.neg_one_pow, pow_succ]
    ring

private theorem odd_power_coefficients (z : R) (hb : z.im ≠ 0) (n : ℕ) :
    ∃ A B : ℤ, 0 ≤ A ∧ (n : ℤ) + 1 ≤ B ∧
      z ^ (2 * n + 1) = ⟨z.re * A, z.im * B⟩ := by
  let a := z.re
  let b := z.im
  let T := a ^ 2 + 2 * b ^ 2
  have hT : 2 ≤ T := by
    have hb2 : (1 : ℤ) ≤ b ^ 2 := Int.add_one_le_of_lt (sq_pos_of_ne_zero hb)
    dsimp [T]
    linarith [sq_nonneg a]
  have hz2 : z ^ 2 = ⟨T, 2 * a * b⟩ := by
    rw [pow_two]
    apply Zsqrtd.ext
    · rw [re_mul]
      change a * a + 2 * b * b = T
      dsimp [T]
      ring
    · rw [im_mul]
      change a * b + b * a = 2 * a * b
      ring
  induction n with
  | zero => exact ⟨1, 1, by decide, by norm_num, by simp⟩
  | succ n ih =>
      obtain ⟨A, B, hA, hB, hrec⟩ := ih
      have hB0 : (0 : ℤ) ≤ B := by omega
      refine ⟨A * T + 4 * b ^ 2 * B, 2 * a ^ 2 * A + B * T, ?_, ?_, ?_⟩
      · positivity
      · have hB2 := mul_le_mul_of_nonneg_left hT hB0
        have hA2 : (0 : ℤ) ≤ 2 * a ^ 2 * A := by positivity
        push_cast
        linarith
      · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add, hrec, hz2]
        apply Zsqrtd.ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private theorem nonzero_exponent {p : ℕ} (hp : 3 ≤ p) (ho : Odd p) (z : R)
    (h : (z ^ p).im = 1) : False := by
  have hb : z.im ≠ 0 := by
    intro hz
    have hh : z = (z.re : R) := by
      apply Zsqrtd.ext <;> simp [hz]
    have hzpow : z ^ p = ((z.re ^ p : ℤ) : R) := by rw [Int.cast_pow, ← hh]
    rw [hzpow, im_intCast] at h
    omega
  obtain ⟨n, rfl⟩ := ho
  obtain ⟨A, B, _, hB, hn⟩ := odd_power_coefficients z hb n
  rw [hn] at h
  change z.im * B = 1 at h
  have hB' : 2 ≤ B := by omega
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp h) with ⟨_, hb'⟩ | ⟨_, hb'⟩ <;> omega

private theorem odd_base {p : ℕ} (hp : 2 ≤ p) {x y : ℤ} (h : x ^ 2 - 2 = y ^ p) : Odd y := by
  apply (Int.odd_pow' (by omega : p ≠ 0)).mp
  rw [← h, odd_sub_two]
  exact (odd_x hp h).pow

private theorem odd_square {x : ℤ} (hx : Odd x) : (x : ZMod 8) ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := hx
  push_cast
  exact (by decide : ∀ a : ZMod 8, (2 * a + 1) ^ 2 = 1) a

private theorem base_mod_eight {p : ℕ} (hp : 2 ≤ p) (ho : Odd p) {x y : ℤ}
    (h : x ^ 2 - 2 = y ^ p) : (y : ZMod 8) = -1 := by
  have hh := congrArg (Int.castRingHom (ZMod 8)) h
  change (↑(x ^ 2 - 2 : ℤ) : ZMod 8) = (↑(y ^ p : ℤ) : ZMod 8) at hh
  push_cast at hh
  rw [odd_square (odd_x hp h)] at hh
  obtain ⟨n, rfl⟩ := ho
  rw [pow_add, pow_mul,
    odd_square (odd_base hp h), one_pow, one_mul, pow_one] at hh
  linear_combination -hh

private theorem positive_base {p : ℕ} (hp : 2 ≤ p) (ho : Odd p) {x y : ℤ}
    (h : x ^ 2 - 2 = y ^ p) (hy : y ≠ -1) : 1 < y := by
  obtain ⟨a, ha⟩ := odd_base hp h
  have hlow : -1 ≤ y := by
    by_contra! hlt
    have hh : y ^ p < (-2 : ℤ) ^ p := ho.pow_lt_pow.mpr (by omega)
    have hp' : (2 : ℤ) ^ 2 ≤ 2 ^ p := pow_le_pow_right₀ (by decide) hp
    rw [ho.neg_pow] at hh
    nlinarith [sq_nonneg x]
  by_contra! hy'
  have he : y = 1 := by omega
  have hm := base_mod_eight hp ho h
  rw [he] at hm
  contradiction

private theorem normalized_norm {p : ℕ} (ho : Odd p) {x y : ℤ} {z : R}
    (h : x ^ 2 - 2 = y ^ p) (hz : (⟨x, 1⟩ : R) = (⟨1, 1⟩ : R) * z ^ p) :
    z.norm = -y := by
  have hh := congrArg Zsqrtd.norm hz
  change x * x - 2 * 1 * 1 = _ at hh
  rw [norm_mul, show (⟨1, 1⟩ : R).norm = -1 by decide,
    show (z ^ p).norm = z.norm ^ p from map_pow (normMonoidHom : R →* ℤ) z p,
    ← neg_eq_neg_one_mul, ← ho.neg_pow] at hh
  have hh' : y ^ p = (-z.norm) ^ p := by rw [← h, ← hh]; ring
  have hh'' := ho.pow_inj.mp hh'
  omega

private theorem normalized_even {p : ℕ} (hp : 2 ≤ p) (ho : Odd p) {x y : ℤ} {z : R}
    (h : x ^ 2 - 2 = y ^ p) (hz : (⟨x, 1⟩ : R) = (⟨1, 1⟩ : R) * z ^ p) :
    Odd z.re ∧ Even z.im := by
  have hnorm := normalized_norm ho h hz
  have ha : Odd z.re := by
    have ha' : Odd z.norm := by
      rw [hnorm, odd_neg]
      exact odd_base hp h
    have ho' : Even (2 * z.im * z.im) := ⟨z.im * z.im, by ring⟩
    rw [norm_def, Int.odd_sub] at ha'
    simp only [ho', iff_true] at ha'
    exact (Int.odd_mul.mp ha').1
  refine ⟨ha, ?_⟩
  by_contra he
  have hb : Odd z.im := Int.not_even_iff_odd.mp he
  have hh := congrArg (Int.castRingHom (ZMod 8)) hnorm
  change (↑(z.re * z.re - 2 * z.im * z.im : ℤ) : ZMod 8) =
    (↑(-y : ℤ) : ZMod 8) at hh
  push_cast at hh
  rw [← pow_two, show (2 : ZMod 8) * z.im * z.im = 2 * (z.im : ZMod 8) ^ 2 by ring,
    odd_square ha, odd_square hb, base_mod_eight hp ho h] at hh
  have hbad : (1 : ZMod 8) - 2 * 1 ≠ -(-1) := by decide
  exact hbad hh

private theorem small_positive (n : ℕ) :
    let z := (⟨1, 1⟩ : R) * (⟨1, 2⟩ : R) ^ (2 * n + 3)
    0 < z.re ∧ 1 < z.im := by
  induction n with
  | zero => decide
  | succ n ih =>
      let t := (⟨1, 1⟩ : R) * (⟨1, 2⟩ : R) ^ (2 * n + 3)
      change 0 < t.re ∧ 1 < t.im at ih
      dsimp only
      rw [show 2 * (n + 1) + 3 = (2 * n + 3) + 2 by omega, pow_add, ← mul_assoc,
        show ((⟨1, 2⟩ : R) ^ 2) = ⟨9, 4⟩ by decide]
      change 0 < (t * ⟨9, 4⟩).re ∧ 1 < (t * ⟨9, 4⟩).im
      rw [re_mul, im_mul]
      change 0 < t.re * 9 + 2 * t.im * 4 ∧ 1 < t.re * 4 + t.im * 9
      rcases ih with ⟨hu, hv⟩
      constructor <;> linarith

private theorem small_negative (n : ℕ) :
    let z := (⟨1, 1⟩ : R) * (⟨1, -2⟩ : R) ^ (2 * n + 3)
    z.re < 0 ∧ 1 < z.im := by
  induction n with
  | zero => decide
  | succ n ih =>
      let t := (⟨1, 1⟩ : R) * (⟨1, -2⟩ : R) ^ (2 * n + 3)
      change t.re < 0 ∧ 1 < t.im at ih
      dsimp only
      rw [show 2 * (n + 1) + 3 = (2 * n + 3) + 2 by omega, pow_add, ← mul_assoc,
        show ((⟨1, -2⟩ : R) ^ 2) = ⟨9, -4⟩ by decide]
      change (t * ⟨9, -4⟩).re < 0 ∧ 1 < (t * ⟨9, -4⟩).im
      rw [re_mul, im_mul]
      change t.re * 9 + 2 * t.im * (-4) < 0 ∧ 1 < t.re * (-4) + t.im * 9
      rcases ih with ⟨hu, hv⟩
      constructor <;> linarith

private theorem normalized_large {p : ℕ} (hp : 3 ≤ p) (ho : Odd p) {x y : ℤ} {z : R}
    (h : x ^ 2 - 2 = y ^ p) (hy : 1 < y)
    (hz : (⟨x, 1⟩ : R) = (⟨1, 1⟩ : R) * z ^ p) : 4 ≤ z.im.natAbs := by
  obtain ⟨ha, hb⟩ := normalized_even (by omega) ho h hz
  have hnorm := normalized_norm ho h hz
  obtain ⟨a, b⟩ := z
  change Odd a at ha
  change Even b at hb
  change a * a - 2 * b * b = -y at hnorm
  change 4 ≤ b.natAbs
  by_contra! hm
  obtain ⟨m, hm'⟩ := hb
  have hb' : b = 0 ∨ b = 2 ∨ b = -2 := by omega
  have hb2 : b ^ 2 ≤ 4 := by rcases hb' with rfl | rfl | rfl <;> decide
  have ha' : a.natAbs < 3 := (Int.natAbs_lt_iff_sq_lt (a := a) (b := 3)).mpr (by nlinarith)
  rw [Int.odd_iff] at ha
  have ha_pm : a = 1 ∨ a = -1 := by omega
  have h1 : 1 < ((⟨1, 1⟩ : R) * (⟨1, 2⟩ : R) ^ p).im := by
    obtain ⟨n, hn⟩ := ho
    rw [show p = 2 * (n - 1) + 3 by omega]
    exact (small_positive _).2
  have h2 : 1 < ((⟨1, 1⟩ : R) * (⟨1, -2⟩ : R) ^ p).im := by
    obtain ⟨n, hn⟩ := ho
    rw [show p = 2 * (n - 1) + 3 by omega]
    exact (small_negative _).2
  have hz' := congrArg Zsqrtd.im hz
  change 1 = ((⟨1, 1⟩ : R) * (⟨a, b⟩ : R) ^ p).im at hz'
  rcases hb' with rfl | rfl | rfl
  · nlinarith [sq_nonneg a]
  · rcases ha_pm with rfl | rfl
    · omega
    · rw [show (⟨-1, 2⟩ : R) = -(⟨1, -2⟩ : R) by rfl, ho.neg_pow, mul_neg, im_neg] at hz'
      omega
  · rcases ha_pm with rfl | rfl
    · omega
    · rw [show (⟨-1, -2⟩ : R) = -(⟨1, 2⟩ : R) by rfl, ho.neg_pow, mul_neg, im_neg] at hz'
      omega



private abbrev splitValid (p : ℕ) (row : ℕ × ℕ × ℕ × ℕ) : Prop :=
  let (q, s, k, g) := row
  q.Prime ∧ q = k * p + 1 ∧ 0 < k ∧ s ≤ q ∧ (s : ZMod q) ^ 2 = 2 ∧
    (g : ZMod q) ^ k = 1 ∧ ∀ j : Fin k, 0 < j.val → (g : ZMod q) ^ j.val ≠ 1

private abbrev checkRow (p : ℕ) (row : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let (q, s, k, g) := row
  decide (q = k * p + 1 ∧ 0 < k ∧ s ≤ q ∧ s ^ 2 % q = 2 % q ∧ g ^ k % q = 1 % q) &&
  (List.range k).all (fun j => decide (0 < j → g ^ j % q ≠ 1 % q))

private theorem checkRow_spec (p : ℕ) (row : ℕ × ℕ × ℕ × ℕ) (hq : row.1.Prime)
    (h : checkRow p row = true) :
    splitValid p row := by
  obtain ⟨q, s, k, g⟩ := row
  change (decide (q = k * p + 1 ∧ 0 < k ∧ s ≤ q ∧
    s ^ 2 % q = 2 % q ∧ g ^ k % q = 1 % q) && _) = true at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hrel, hk, hsq, hs, hg⟩ := of_decide_eq_true h.1
  refine ⟨hq, hrel, hk, hsq, ?_, ?_, ?_⟩
  · have hh := congrArg (fun n : ℕ => (n : ZMod q)) hs
    simpa only [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_ofNat] using hh
  · have hh := congrArg (fun n : ℕ => (n : ZMod q)) hg
    simpa only [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one] using hh
  · intro j hj hz
    have hne := of_decide_eq_true (List.all_eq_true.mp h.2 j.val (List.mem_range.mpr j.isLt)) hj
    apply hne
    have hh := congrArg ZMod.val hz
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.val_natCast, ZMod.val_natCast] at hh
    exact hh

private abbrev rejectRow (r : ℕ) (row : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let (q, s, k, g) := row
  let a := (1 + s) ^ r % q
  let b := (1 + (q - s)) ^ r % q
  let target := b ^ k % q
  (List.range (k + 1)).all fun j =>
    let u := if j = k then 0 else g ^ j % q
    let v := (a * u + 2 * (q - s)) % q
    v != 0 && v ^ k % q != target

private theorem rejectRow_spec (r q s k g : ℕ) (hsq : s ≤ q)
    (h : rejectRow r (q, s, k, g) = true) (j : Fin (k + 1)) :
    let u : ZMod q := if j.val = k then 0 else (g : ZMod q) ^ j.val
    let v : ZMod q := (1 + (s : ZMod q)) ^ r * u - 2 * s
    v ≠ 0 ∧ v ^ k ≠ ((1 - (s : ZMod q)) ^ r) ^ k := by
  let a := (1 + s) ^ r % q
  let b := (1 + (q - s)) ^ r % q
  let u := if j.val = k then 0 else g ^ j.val % q
  let v := a * u + 2 * (q - s)
  have hj := List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt)
  change (v % q != 0 && (v % q) ^ k % q != b ^ k % q) = true at hj
  simp only [Bool.and_eq_true, bne_iff_ne] at hj
  have hu : (u : ZMod q) = (if j.val = k then 0 else (g : ZMod q) ^ j.val) := by
    by_cases h' : j.val = k <;> simp [u, h', ZMod.natCast_mod]
  have hqs : ((q - s : ℕ) : ZMod q) = -(s : ZMod q) := by
    rw [Nat.cast_sub hsq, ZMod.natCast_self, zero_sub]
  have hv : (v : ZMod q) = (1 + (s : ZMod q)) ^ r * (u : ZMod q) - 2 * s := by
    dsimp [v, a]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
      ZMod.natCast_mod, hqs, mul_neg, sub_eq_add_neg]
  have hb : (b : ZMod q) = (1 - (s : ZMod q)) ^ r := by
    simp [b, ZMod.natCast_mod, hqs, sub_eq_add_neg]
  dsimp
  rw [← hu, ← hv, ← hb, ← Nat.cast_pow, ← Nat.cast_pow]
  constructor
  · intro hz
    apply hj.1
    have he := congrArg ZMod.val hz
    rwa [ZMod.val_natCast, ZMod.val_zero] at he
  · intro hz
    apply hj.2
    have he : (((v % q) ^ k : ℕ) : ZMod q) = ((b ^ k : ℕ) : ZMod q) := by
      rw [Nat.cast_pow, ZMod.natCast_mod, ← Nat.cast_pow]
      exact hz
    simpa only [ZMod.val_natCast] using congrArg ZMod.val he

private theorem split_impossible {p r : ℕ} {x : ℤ} {z : Zsqrtd 2}
    (hp : 0 < p)
    (h : (⟨x, 1⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ p)
    (row : ℕ × ℕ × ℕ × ℕ) (hv : splitValid p row) (hr : rejectRow r row = true) :
    False := by
  obtain ⟨q, s, k, g⟩ := row
  rcases hv with ⟨hq, hqk, hk, hsq, hs, hg, hprim⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero k := ⟨hk.ne'⟩
  have hroot : IsPrimitiveRoot (g : ZMod q) k := by
    refine IsPrimitiveRoot.mk_of_lt _ hk hg (fun j hj hjk => ?_)
    exact hprim ⟨j, hjk⟩ hj
  have hs' : (s : ZMod q) * s = (2 : ℤ) := by simpa [pow_two] using hs
  let f₁ : Zsqrtd 2 →+* ZMod q := Zsqrtd.lift ⟨s, hs'⟩
  let f₂ : Zsqrtd 2 →+* ZMod q := Zsqrtd.lift ⟨-(s : ZMod q), by simpa using hs'⟩
  have h₁ := congrArg f₁ h
  have h₂ := congrArg f₂ h
  simp only [map_mul, map_pow] at h₁ h₂
  have H : (1 + (s : ZMod q)) ^ r * f₁ z ^ p - 2 * s =
      (1 - (s : ZMod q)) ^ r * f₂ z ^ p := by
    change (x : ZMod q) + (1 : ℤ) * (s : ZMod q) =
      ((1 : ℤ) + (1 : ℤ) * (s : ZMod q)) ^ r * f₁ z ^ p at h₁
    change (x : ZMod q) + (1 : ℤ) * -(s : ZMod q) =
      ((1 : ℤ) + (1 : ℤ) * -(s : ZMod q)) ^ r * f₂ z ^ p at h₂
    push_cast at h₁ h₂
    simp only [one_mul] at h₁ h₂
    calc
      _ = (x : ZMod q) - s := by rw [← h₁]; ring
      _ = _ := by simpa only [sub_eq_add_neg] using h₂
  have pth_to_k (v : ZMod q) (hne : v ≠ 0) : (v ^ p) ^ k = 1 := by
    rw [← pow_mul, mul_comm p, ← show q - 1 = k * p by omega]
    exact ZMod.pow_card_sub_one_eq_one hne
  obtain ⟨j, hj⟩ : ∃ j : Fin (k + 1), f₁ z ^ p =
      (if j.val = k then 0 else (g : ZMod q) ^ j.val) := by
    by_cases hz : f₁ z = 0
    · exact ⟨⟨k, by omega⟩, by simp [hz, hp.ne']⟩
    · obtain ⟨j, hj, hjg⟩ := hroot.eq_pow_of_pow_eq_one (pth_to_k _ hz)
      exact ⟨⟨j, by omega⟩, by simp [Nat.ne_of_lt hj, hjg]⟩
  have hrj := rejectRow_spec r q s k g hsq hr j
  change _ ≠ 0 ∧ _ ≠ _ at hrj
  rw [← hj, H] at hrj
  have hz : f₂ z ≠ 0 := by
    intro hz
    simp [hz, hp.ne'] at hrj
  exact hrj.2 (by rw [mul_pow, pth_to_k _ hz, mul_one])

private theorem cover {p r : ℕ} {x : ℤ} {z : Zsqrtd 2}
    (hp : 0 < p) (hr : r ≤ p / 2)
    (h : (⟨x, 1⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ p)
    (rows : List (ℕ × ℕ × ℕ × ℕ)) (exceptions : List ℕ)
    (hprime : ∀ row ∈ rows, row.1.Prime)
    (hvalid : rows.all (checkRow p) = true)
    (hcover : (List.range (p / 2 + 1)).all (fun j =>
      decide (j < 2) || exceptions.contains j || rows.any (rejectRow j)) = true)
    (hr₂ : 2 ≤ r) :
    r ∈ exceptions := by
  have hcheck := List.all_eq_true.mp hcover r (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem, not_lt.mpr hr₂, false_or,
    List.any_eq_true] at hcheck
  rcases hcheck with hmem | ⟨row, hrow, hre⟩
  · exact hmem
  · have hv := checkRow_spec p row (hprime row hrow) (List.all_eq_true.mp hvalid row hrow)
    exact (split_impossible hp h row hv hre).elim


private abbrev sievedPrimes : List ℕ := [17, 19, 23, 37, 41, 43, 47]

-- Each table row records q, a square root of 2 modulo q, k, and a
-- primitive kth root of unity modulo q.

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem certified_sieve {p r : ℕ} {x : ℤ} {z : Zsqrtd 2}
    (hp : p ∈ sievedPrimes) (hr : r ≤ p / 2) (hr₂ : 2 ≤ r)
    (h : (⟨x, 1⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ p) :
    (p = 19 ∧ r ∈ ([3, 4, 8, 9] : List ℕ)) ∨
      (p = 41 ∧ r ∈ ([11, 13] : List ℕ)) ∨ (p = 47 ∧ r = 14) := by
  simp only [sievedPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hh := cover (by decide : 0 < 17) hr h
      [(103, 38, 6, 57), (137, 31, 8, 127), (409, 97, 24, 371)] [] (by
        intro row hrow
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
        rcases hrow with rfl | rfl | rfl <;> norm_num) (by rfl) (by rfl) hr₂
    simp at hh
  · have hh := cover (by decide : 0 < 19) hr h
      [(191, 134, 10, 82), (457, 80, 24, 240), (647, 36, 34, 74)] [3, 4, 8, 9] (by
        intro row hrow
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
        rcases hrow with rfl | rfl | rfl <;> norm_num) (by rfl) (by rfl) hr₂
    exact Or.inl ⟨rfl, hh⟩
  · have hh := cover (by decide : 0 < 23) hr h
      [(47, 7, 2, 46), (967, 44, 42, 731)] [] (by
        intro row hrow
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
        rcases hrow with rfl | rfl <;> norm_num) (by rfl) (by rfl) hr₂
    simp at hh
  · have hh := cover (by decide : 0 < 37) hr h
      [(223, 15, 6, 184), (1481, 144, 40, 813)] [] (by
        intro row hrow
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
        rcases hrow with rfl | rfl <;> norm_num) (by rfl) (by rfl) hr₂
    simp at hh
  · have hh := cover (by decide : 0 < 41) hr h
      [(1231, 900, 30, 1176), (1559, 1058, 38, 236), (2543, 353, 62, 1206), (2953, 483, 72, 2468)] [11, 13] (by
        intro row hrow
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
        rcases hrow with rfl | rfl | rfl | rfl <;> norm_num) (by rfl) (by rfl) hr₂
    exact Or.inr (Or.inl ⟨rfl, hh⟩)
  · have hh := cover (by decide : 0 < 43) hr h
      [(431, 243, 10, 315), (1033, 404, 24, 135), (1721, 640, 40, 1470), (2753, 1129, 64, 1037)] [] (by
        intro row hrow
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
        rcases hrow with rfl | rfl | rfl | rfl <;> norm_num) (by rfl) (by rfl) hr₂
    simp at hh
  · have hh := cover (by decide : 0 < 47) hr h
      [(1129, 406, 24, 738), (1223, 1188, 26, 57), (4231, 92, 90, 1477), (4513, 2118, 96, 1778)] [14] (by
        intro row hrow
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
        rcases hrow with rfl | rfl | rfl | rfl <;> norm_num) (by rfl) (by rfl) hr₂
    exact Or.inr (Or.inr ⟨rfl, by simpa using hh⟩)


private theorem square_zero_pow {A : Type*} [CommRing A]
    (u d : A) (hd : d ^ 2 = 0) (n : ℕ) :
    (u + d) ^ (n + 1) = u ^ (n + 1) + ((n + 1 : ℕ) : A) * u ^ n * d := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ (u + d), ih, pow_succ u (n + 1), pow_succ u n]
      push_cast
      linear_combination (n + 1 : A) * u ^ n * hd

private theorem exponent_41_mod {r : ℕ} {x : ℤ} {z : Zsqrtd 2}
    (h : (⟨x, 1⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ 41) :
    (((⟨1, 1⟩ : Zsqrtd 2) ^ r *
      (⟨z.re % 41, z.im % 41⟩ : Zsqrtd 2) ^ 41).im) % 1681 = 1 := by
  let I := Ideal.span ({(1681 : Zsqrtd 2)} : Set (Zsqrtd 2))
  let f := Ideal.Quotient.mk I
  let v : Zsqrtd 2 := ⟨z.re % 41, z.im % 41⟩
  let w : Zsqrtd 2 := ⟨z.re / 41, z.im / 41⟩
  have hz : z = v + 41 * w := by
    apply Zsqrtd.ext
    · rw [re_add, re_mul]
      change z.re = z.re % 41 + (41 * (z.re / 41) + 2 * 0 * (z.im / 41))
      rw [mul_zero, zero_mul, add_zero, Int.emod_add_mul_ediv]
    · rw [im_add, im_mul]
      change z.im = z.im % 41 + (41 * (z.im / 41) + 0 * (z.re / 41))
      rw [zero_mul, add_zero, Int.emod_add_mul_ediv]
  have h1681 : f (1681 : Zsqrtd 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  have cutoff : ((41 : Zsqrtd 2) ^ 2) = 1681 := by decide
  have hd : (f (41 * w)) ^ 2 = 0 := by
    rw [← map_pow, mul_pow, cutoff, map_mul, h1681, zero_mul]
  have hmul : (41 : Zsqrtd 2) * (41 * w) = 1681 * w := by
    rw [← mul_assoc, ← pow_two, cutoff]
  have hd' : (41 : (Zsqrtd 2) ⧸ I) * f (41 * w) = 0 := by
    rw [← map_ofNat f, ← map_mul, hmul, map_mul, h1681, zero_mul]
  have hf : f z ^ 41 = f v ^ 41 := by
    calc
      _ = (f v + f (41 * w)) ^ 41 := by rw [hz, map_add]
      _ = f v ^ 41 + 41 * f v ^ 40 * f (41 * w) := by
        exact square_zero_pow (f v) (f (41 * w)) hd 40
      _ = _ := by rw [mul_right_comm, hd', zero_mul, add_zero]
  let u : Zsqrtd 2 := (⟨1, 1⟩ : Zsqrtd 2) ^ r * v ^ 41
  have hfu : f u = f (⟨x, 1⟩ : Zsqrtd 2) := by
    rw [h]
    simp only [u, map_mul, map_pow, hf]
  have hdiv : (1681 : Zsqrtd 2) ∣ u - (⟨x, 1⟩ : Zsqrtd 2) :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hfu)
  obtain ⟨t, ht⟩ := hdiv
  have hti := congrArg Zsqrtd.im ht
  rw [im_sub, im_mul] at hti
  change u.im - 1 = 1681 * t.im + 0 * t.re at hti
  change u.im % 1681 = 1
  omega

private abbrev squareAndMultiply (z : Zsqrtd 2) : Zsqrtd 2 :=
  let a := z * z
  let b := a * a
  let c := b * b
  let d := c * c
  let e := d * d
  e * c * z

private theorem pow41_eq (z : Zsqrtd 2) : z ^ 41 = squareAndMultiply z := by
  dsimp [squareAndMultiply]
  ring

private theorem imag_frobenius_41 (u z : Zsqrtd 2) :
    (((u * z ^ 41).im : ℤ) : ZMod 41) = ((u * z).im : ZMod 41) := by
  let : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  let f : Zsqrtd 2 →+* ZMod 41 := Zsqrtd.lift ⟨17, by decide⟩
  let g : Zsqrtd 2 →+* ZMod 41 := Zsqrtd.lift ⟨-17, by decide⟩
  have h (φ : Zsqrtd 2 →+* ZMod 41) : φ (u * z ^ 41) = φ (u * z) := by
    rw [map_mul, map_pow, ZMod.pow_card, map_mul]
  have hf := h f
  have hg := h g
  change (↑(u * z ^ 41).re : ZMod 41) + (↑(u * z ^ 41).im : ZMod 41) * 17 =
    (↑(u * z).re : ZMod 41) + (↑(u * z).im : ZMod 41) * 17 at hf
  change (↑(u * z ^ 41).re : ZMod 41) + (↑(u * z ^ 41).im : ZMod 41) * (-17) =
    (↑(u * z).re : ZMod 41) + (↑(u * z).im : ZMod 41) * (-17) at hg
  have hc : (34 : ZMod 41) * (((u * z ^ 41).im : ZMod 41) - ((u * z).im : ZMod 41)) = 0 := by
    linear_combination hf - hg
  have h34 : (34 : ZMod 41) ≠ 0 := by decide
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left h34)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private theorem forty_one {r : ℕ} {x : ℤ} {z : Zsqrtd 2}
    (hr : r ∈ ([11, 13] : List ℕ))
    (h : (⟨x, 1⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ 41) : False := by
  let linear := fun (r a b : ℕ) => if r = 11 then (a + b) % 41 else (5 * a + 7 * b) % 41
  let check := fun (r a b : ℕ) =>
    decide (linear r a b = 1 → ((⟨1, 1⟩ : Zsqrtd 2) ^ r *
      squareAndMultiply (⟨a, b⟩ : Zsqrtd 2)).im % 1681 ≠ 1)
  have hcheck : ([11, 13] : List ℕ).all (fun r => (List.range 41).all (fun a =>
      (List.range 41).all (check r a))) = true := by rfl
  have har : 0 ≤ z.re % 41 := Int.emod_nonneg _ (by decide)
  have hbr : 0 ≤ z.im % 41 := Int.emod_nonneg _ (by decide)
  have ha : (z.re % 41).toNat ∈ List.range 41 := by
    have ht := Int.emod_lt_of_pos z.re (by decide : 0 < (41 : ℤ))
    exact List.mem_range.mpr (by omega)
  have hb : (z.im % 41).toNat ∈ List.range 41 := by
    have ht := Int.emod_lt_of_pos z.im (by decide : 0 < (41 : ℤ))
    exact List.mem_range.mpr (by omega)
  have he := of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hcheck r hr) _ ha) _ hb)
  have hli : linear r (z.re % 41).toNat (z.im % 41).toNat = 1 := by
    have hpow : (((((⟨1, 1⟩ : Zsqrtd 2) ^ r) * z).im : ℤ) : ZMod 41) = 1 := by
      rw [← imag_frobenius_41, ← h]
      change ((1 : ℤ) : ZMod 41) = 1
      simp
    have hpow' := hpow
    rw [im_mul] at hpow'
    push_cast at hpow'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hr11 : ((((⟨1, 1⟩ : Zsqrtd 2) ^ 11).re : ℤ) : ZMod 41) = 1 := by decide
      have hi11 : ((((⟨1, 1⟩ : Zsqrtd 2) ^ 11).im : ℤ) : ZMod 41) = 1 := by decide
      rw [hr11, hi11, one_mul, one_mul, add_comm] at hpow'
      have hval := congrArg ZMod.val hpow'
      have hn : ((z.re % 41).toNat : ZMod 41) = (z.re : ZMod 41) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg har, ZMod.intCast_eq_intCast_iff']
        exact Int.emod_emod _ _
      have hm : ((z.im % 41).toNat : ZMod 41) = (z.im : ZMod 41) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hbr, ZMod.intCast_eq_intCast_iff']
        exact Int.emod_emod _ _
      change ((z.re % 41).toNat + (z.im % 41).toNat) % 41 = 1
      rw [← ZMod.val_natCast, Nat.cast_add, hn, hm]
      exact hval
    · have hr13 : ((((⟨1, 1⟩ : Zsqrtd 2) ^ 13).re : ℤ) : ZMod 41) = 7 := by decide
      have hi13 : ((((⟨1, 1⟩ : Zsqrtd 2) ^ 13).im : ℤ) : ZMod 41) = 5 := by decide
      rw [hr13, hi13, add_comm] at hpow'
      have hval := congrArg ZMod.val hpow'
      have hn : ((z.re % 41).toNat : ZMod 41) = (z.re : ZMod 41) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg har, ZMod.intCast_eq_intCast_iff']
        exact Int.emod_emod _ _
      have hm : ((z.im % 41).toNat : ZMod 41) = (z.im : ZMod 41) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hbr, ZMod.intCast_eq_intCast_iff']
        exact Int.emod_emod _ _
      change (5 * (z.re % 41).toNat + 7 * (z.im % 41).toNat) % 41 = 1
      rw [← ZMod.val_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hn, hm]
      exact hval
  apply he hli
  simpa only [Int.toNat_of_nonneg har, Int.toNat_of_nonneg hbr, ← pow41_eq] using
    exponent_41_mod h


private theorem factor_norm {p r : ℕ} (ho : Odd p) {x y : ℤ} {z : Zsqrtd 2}
    (h : x ^ 2 - 2 = y ^ p)
    (hz : (⟨x, 1⟩ : Zsqrtd 2) = (⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ p) :
    (-1 : ℤ) ^ r * z.norm = y := by
  have hh := congrArg Zsqrtd.norm hz
  change x * x - 2 * 1 * 1 = _ at hh
  rw [Zsqrtd.norm_mul,
    show ((⟨1, 1⟩ : Zsqrtd 2) ^ r).norm = (-1 : ℤ) ^ r from
      map_pow (Zsqrtd.normMonoidHom : Zsqrtd 2 →* ℤ) ⟨1, 1⟩ r,
    show (z ^ p).norm = z.norm ^ p from map_pow (Zsqrtd.normMonoidHom : Zsqrtd 2 →* ℤ) z p] at hh
  apply ho.pow_inj.mp
  rw [mul_pow, ← pow_mul, mul_comm r p, pow_mul, ho.neg_one_pow, ← hh, ← h]
  ring

/-- Exponent exclusions outside the range of the finite sieve. -/
def H1 : Prop :=
  ∀ (p : ℕ) (x y : ℤ), p.Prime → Odd p →
    (p < 17 ∨ 911 < p ∨ p % 24 ∉ ([13, 17, 19, 23] : List ℕ)) →
    1 < y → x ^ 2 - 2 ≠ y ^ p

/-- The remaining normalized Thue equations with unit exponent one. -/
def H2 : Prop :=
  ∀ (p : ℕ) (z : Zsqrtd 2), p.Prime → 17 ≤ p → p ≤ 911 →
    p % 24 ∈ ([13, 17, 19, 23] : List ℕ) →
    Odd z.re → Even z.im → 4 ≤ z.im.natAbs → 1 < -z.norm →
    ((⟨1, 1⟩ : Zsqrtd 2) * z ^ p).im ≠ 1

/-- The non-normalized cases surviving the congruence certificates. -/
def H3 : Prop :=
  ∀ (p r : ℕ) (z : Zsqrtd 2),
    p.Prime → 17 ≤ p → p ≤ 911 → p % 24 ∈ ([13, 17, 19, 23] : List ℕ) →
    2 ≤ r → r ≤ p / 2 →
    (p ∉ sievedPrimes ∨ (p = 19 ∧ r ∈ ([3, 4, 8, 9] : List ℕ)) ∨ (p = 47 ∧ r = 14)) →
    1 < (-1 : ℤ) ^ r * z.norm →
    ((⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ p).im ≠ 1

theorem main : H1 → H2 → H3 → type_of% @LebesgueNagell.lebesgue_nagell := by
  intro h₁ h₂ h₃ p hp ho x y
  constructor
  · intro h
    by_cases hy : y = -1
    · refine ⟨?_, hy⟩
      rw [hy, ho.neg_one_pow] at h
      have hz : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with h' | h' <;> omega
    · exfalso
      have hp₂ := hp.two_le
      have hp₃ : 3 ≤ p := by
        obtain ⟨k, hk⟩ := ho
        omega
      have hy' := positive_base hp₂ ho h hy
      have hlo : 17 ≤ p := by
        by_contra! hc
        exact h₁ p x y hp ho (Or.inl hc) hy' h
      have hhi : p ≤ 911 := by
        by_contra! hc
        exact h₁ p x y hp ho (Or.inr (Or.inl hc)) hy' h
      have hm : p % 24 ∈ ([13, 17, 19, 23] : List ℕ) := by
        by_contra hc
        exact h₁ p x y hp ho (Or.inr (Or.inr hc)) hy' h
      obtain ⟨r, z, x', hr, hx', hz⟩ := bounded_factor hp₂ ho h
      have him : ((⟨1, 1⟩ : Zsqrtd 2) ^ r * z ^ p).im = 1 := (congrArg Zsqrtd.im hz).symm
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at him
        exact nonzero_exponent hp₃ ho z him
      by_cases hr1 : r = 1
      · subst r
        rw [pow_one] at hz him
        obtain ⟨ha, hb⟩ := normalized_even hp₂ ho hx' hz
        have hn := normalized_norm ho hx' hz
        have hlarge := normalized_large hp₃ ho hx' hy' hz
        exact h₂ p z hp hlo hhi hm ha hb hlarge (by omega) him
      · have hr₂ : 2 ≤ r := by omega
        have hfin : p ∉ sievedPrimes ∨ (p = 19 ∧ r ∈ ([3, 4, 8, 9] : List ℕ)) ∨
            (p = 47 ∧ r = 14) := by
          by_cases hc : p ∈ sievedPrimes
          · rcases certified_sieve hc hr hr₂ hz with h19 | ⟨rfl, h41⟩ | h47
            · exact Or.inr (Or.inl h19)
            · exact (forty_one h41 hz).elim
            · exact Or.inr (Or.inr h47)
          · exact Or.inl hc
        exact h₃ p r z hp hlo hhi hm hr₂ hr hfin ((factor_norm ho hx' hz).symm ▸ hy') him
  · rintro ⟨rfl | rfl, rfl⟩
    · exact LebesgueNagell.lebesgue_nagell_solution_pos_one p ho
    · exact LebesgueNagell.lebesgue_nagell_solution_neg_one p ho

end OMA.R_LebesgueNagell_lebesgue_nagell_R2
