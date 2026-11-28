import FormalConjectures.ErdosProblems.«672»
import Mathlib

section

-- Reduction Erdos672.erdos_672.variants.oblath.R1 of Erdős Problem 672 — oblath
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction of four independent arithmetic statements, one per
-- (length, exponent) pair, so each conjunct is its own attackable step.

namespace OMA.R_Erdos672_erdos_672_variants_oblath_R1

/-- The `k = 5`, `l = 2` case: the product of a 5-term arithmetic progression with coprime
first term and difference is never a square. -/
def H1 : Prop := Erdos672.Erdos672With 5 2

/-- The `k = 3`, `l = 3` case: the product of a 3-term arithmetic progression with coprime
first term and difference is never a cube. -/
def H2 : Prop := Erdos672.Erdos672With 3 3

/-- The `k = 3`, `l = 4` case: the product of a 3-term arithmetic progression with coprime
first term and difference is never a fourth power. -/
def H3 : Prop := Erdos672.Erdos672With 3 4

/-- The `k = 3`, `l = 5` case: the product of a 3-term arithmetic progression with coprime
first term and difference is never a fifth power. -/
def H4 : Prop := Erdos672.Erdos672With 3 5

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos672.erdos_672.variants.oblath := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_Erdos672_erdos_672_variants_oblath_R1
end

section

-- Step Erdos672.erdos_672.variants.oblath.R1.H1: hypothesis H1 of reduction Erdos672.erdos_672.variants.oblath.R1
-- Credit: @aqron7

/-! Euler: `x ^ 4 - x ^ 2 y ^ 2 + y ^ 4 = z ^ 2` forces `x y = 0` or `x ^ 2 = y ^ 2`. -/

namespace OMA672Q

/-- Nontrivial solution of the quartic. -/
def G (x y z : ℤ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 ≠ y ^ 2 ∧ x ^ 4 - x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2

lemma G.z_ne_zero {x y z : ℤ} (h : G x y z) : z ≠ 0 := by
  rintro rfl
  have h1 := h.2.2.2
  have : 0 < x ^ 2 := by positivity [h.1]
  have : 0 < y ^ 2 := by positivity [h.2.1]
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]

lemma G.symm {x y z : ℤ} (h : G x y z) : G y x z :=
  ⟨h.2.1, h.1, fun e => h.2.2.1 e.symm, by linear_combination h.2.2.2⟩

/-- From `c ^ 2 = a ^ 2 + d ^ 2` and `b ^ 2 = a ^ 2 + 4 d ^ 2` we get a solution. -/
lemma G_of_T {a b c d : ℤ} (ha : a ≠ 0) (hd : d ≠ 0) (hc : c ^ 2 = a ^ 2 + d ^ 2)
    (hb : b ^ 2 = a ^ 2 + 4 * d ^ 2) : G a (|c| + |d|) ((|c| + |d|) * |b|) := by
  have hc2 : |c| ^ 2 = a ^ 2 + d ^ 2 := by rw [sq_abs]; exact hc
  have hd2 : |d| ^ 2 = d ^ 2 := sq_abs d
  have hb2 : |b| ^ 2 = a ^ 2 + 4 * d ^ 2 := by rw [sq_abs]; exact hb
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hcnn : 0 ≤ |c| := abs_nonneg c
  refine ⟨ha, by positivity, ?_, ?_⟩
  · intro e
    have : a ^ 2 = |c| ^ 2 + 2 * |c| * |d| + |d| ^ 2 := by rw [e]; ring
    nlinarith
  · have ha2 : a ^ 2 = |c| ^ 2 - |d| ^ 2 := by rw [hc2, hd2]; ring
    have hb3 : |b| ^ 2 = |c| ^ 2 + 3 * |d| ^ 2 := by rw [hb2, hc2, hd2]; ring
    rw [mul_pow]
    linear_combination (a ^ 2 + |c| ^ 2 - |d| ^ 2 - (|c| + |d|) ^ 2) * ha2
      - (|c| + |d|) ^ 2 * hb3


lemma three_dvd_of_sq_add {a d : ℤ} (h : (3 : ℤ) ∣ a ^ 2 + d ^ 2) : (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ d := by
  have h' : ((a : ZMod 3)) ^ 2 + ((d : ZMod 3)) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + d ^ 2) 3).mpr h
    push_cast at this; exact this
  have key : ∀ A D : ZMod 3, A ^ 2 + D ^ 2 = 0 → A = 0 ∧ D = 0 := by decide
  obtain ⟨h1, h2⟩ := key _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp h1, (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp h2⟩

lemma size_bound (A D : ℤ) (hA : 1 ≤ A) (hD : 1 ≤ D) :
    2 * (A + 2 * D) * (A + 4 * D) < (A ^ 2 + 2 * A * D + 4 * D ^ 2) ^ 2 := by
  have h1 : A ≤ A ^ 2 := by nlinarith
  have h2 : 1 ≤ A * D := by nlinarith
  have h3 : D ≤ D ^ 2 := by nlinarith
  set Z := A ^ 2 + 2 * A * D + 4 * D ^ 2 with hZdef
  have hZ : 7 ≤ Z := by rw [hZdef]; nlinarith
  have h4 : 7 * Z ≤ Z ^ 2 := by nlinarith
  have e : 2 * (A + 2 * D) * (A + 4 * D) = 2 * A ^ 2 + 12 * (A * D) + 16 * D ^ 2 := by ring
  have e2 : 7 * Z = 7 * A ^ 2 + 14 * (A * D) + 28 * D ^ 2 := by rw [hZdef]; ring
  nlinarith

/-- One of `x, y` even: descent through `c ^ 2 = a ^ 2 + d ^ 2`, `b ^ 2 = a ^ 2 + 4 d ^ 2`. -/
lemma step_one_even {x y z : ℤ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz : 0 < z)
    (hcopI : IsCoprime x y) (hx2 : x % 2 = 1) (hy2 : y % 2 = 0)
    (hpt : (x ^ 2 - y ^ 2) ^ 2 + (x * y) ^ 2 = z ^ 2)
    (hcop2 : IsCoprime (x ^ 2 - y ^ 2) (x * y)) :
    ∃ a b c : ℤ, G a b c ∧ c.natAbs < z.natAbs := by
  have ht : PythagoreanTriple (x ^ 2 - y ^ 2) (x * y) z := by
    delta PythagoreanTriple; linear_combination hpt
  have hg : Int.gcd (x ^ 2 - y ^ 2) (x * y) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop2
  have hpar : (x ^ 2 - y ^ 2) % 2 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, y = 2 * j := ⟨y / 2, by omega⟩
    have : x ^ 2 - y ^ 2 = 1 + 2 * (2 * k ^ 2 + 2 * k - 2 * j ^ 2) := by rw [hk, hj]; ring
    rw [this, Int.add_mul_emod_self_left]; norm_num
  obtain ⟨m, n, e1, e2, e3, e4, -, e6⟩ := ht.coprime_classification' hg hpar hz
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hm0 : m ≠ 0 := by rintro rfl; apply hxy0; rw [e2]; ring
  have hn0 : n ≠ 0 := by rintro rfl; apply hxy0; rw [e2]; ring
  -- decompose x = b * a, m = c * a
  obtain ⟨a, b, c, ha, hbc, hxba, hmca⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left m hx0)
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbyn : b * y = 2 * c * n := by
    apply mul_left_cancel₀ ha0
    have e2' := e2
    rw [hxba, hmca] at e2'
    linear_combination e2'
  have hbodd : b % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one b with h | h
    · exfalso
      have : (2 : ℤ) ∣ x := by rw [hxba]; exact Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero h) _
      omega
    · exact h
  have hbc' : IsCoprime b c := Int.isCoprime_iff_gcd_eq_one.mpr hbc
  have hb2 : IsCoprime b 2 := by
    obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
    exact ⟨1, -k, by rw [hk]; ring⟩
  have hbn : b ∣ n := by
    have : b ∣ (2 * c) * n := ⟨y, by rw [← hbyn]⟩
    exact (hb2.mul_right hbc').dvd_of_dvd_mul_left this
  obtain ⟨d, rfl⟩ := hbn
  have hb0 : b ≠ 0 := by rintro rfl; simp at hxba; exact hx0 hxba
  have hy : y = 2 * c * d := by
    apply mul_left_cancel₀ hb0; linear_combination hbyn
  subst hy
  have hc0 : c ≠ 0 := by rintro rfl; simp at hmca; exact hm0 hmca
  have hd0 : d ≠ 0 := by rintro rfl; simp at hn0
  have hmn : IsCoprime m (b * d) := Int.isCoprime_iff_gcd_eq_one.mpr e4
  have had : IsCoprime (a : ℤ) d := by
    rw [hmca] at hmn
    exact hmn.of_mul_left_right.of_mul_right_right
  have hkey : (a : ℤ) ^ 2 * (b ^ 2 - c ^ 2) = d ^ 2 * (4 * c ^ 2 - b ^ 2) := by
    rw [hxba, hmca] at e1; linear_combination e1
  obtain ⟨k, hk⟩ : (a : ℤ) ^ 2 ∣ 4 * c ^ 2 - b ^ 2 := by
    have : (a : ℤ) ^ 2 ∣ d ^ 2 * (4 * c ^ 2 - b ^ 2) := ⟨b ^ 2 - c ^ 2, hkey.symm⟩
    exact (had.pow).dvd_of_dvd_mul_left this
  have ha2 : (a : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ ha0
  have hk2 : b ^ 2 - c ^ 2 = d ^ 2 * k := by
    apply mul_left_cancel₀ ha2; rw [hkey, hk]; ring
  have h3c : 3 * c ^ 2 = k * ((a : ℤ) ^ 2 + d ^ 2) := by linear_combination hk + hk2
  have h3b : 3 * b ^ 2 = k * ((a : ℤ) ^ 2 + 4 * d ^ 2) := by linear_combination hk + 4 * hk2
  have hk3 : k ∣ 3 := by
    obtain ⟨u, v, huv⟩ := (hbc'.symm.pow (m := 2) (n := 2))
    exact ⟨u * ((a : ℤ) ^ 2 + d ^ 2) + v * ((a : ℤ) ^ 2 + 4 * d ^ 2), by
      linear_combination (-3) * huv + u * h3c + v * h3b⟩
  have hkpos : 0 < k := by
    have : 0 < 3 * c ^ 2 := by positivity
    have : 0 < (a : ℤ) ^ 2 + d ^ 2 := by positivity
    nlinarith
  have hkle : k ≤ 3 := Int.le_of_dvd (by norm_num) hk3
  interval_cases k
  · -- k = 1: 3 ∣ a^2 + d^2
    exfalso
    obtain ⟨h1, h2⟩ := three_dvd_of_sq_add (a := a) (d := d) ⟨c ^ 2, by linarith⟩
    exact Int.prime_three.not_isUnit (had.isUnit_of_dvd' h1 h2)
  · exfalso; omega
  · -- k = 3
    have hcT : c ^ 2 = (a : ℤ) ^ 2 + d ^ 2 := by linarith
    have hbT : b ^ 2 = (a : ℤ) ^ 2 + 4 * d ^ 2 := by linarith
    refine ⟨a, |c| + |d|, (|c| + |d|) * |b|, G_of_T ha0 hd0 hcT hbT, ?_⟩
    have hZ0 : 0 ≤ (|c| + |d|) * |b| := by positivity
    have hzv : z = c ^ 2 * (a : ℤ) ^ 2 + b ^ 2 * d ^ 2 := by rw [e3, hmca]; ring
    have hlt : (|c| + |d|) * |b| < z := by
      have hA : 1 ≤ (a : ℤ) ^ 2 := by have := sq_pos_of_ne_zero ha0; omega
      have hD : 1 ≤ d ^ 2 := by have := sq_pos_of_ne_zero hd0; omega
      have e : ((|c| + |d|) * |b|) ^ 2 ≤ 2 * (c ^ 2 + d ^ 2) * b ^ 2 := by
        rw [mul_pow, sq_abs b]
        have : (|c| + |d|) ^ 2 ≤ 2 * (c ^ 2 + d ^ 2) := by
          nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d]
        nlinarith [sq_nonneg b]
      have hR : 2 * (c ^ 2 + d ^ 2) * b ^ 2
          = 2 * ((a : ℤ) ^ 2 + 2 * d ^ 2) * ((a : ℤ) ^ 2 + 4 * d ^ 2) := by rw [hcT, hbT]; ring
      have hz' : z = ((a : ℤ) ^ 2) ^ 2 + 2 * (a : ℤ) ^ 2 * d ^ 2 + 4 * (d ^ 2) ^ 2 := by
        rw [hzv, hcT, hbT]; ring
      have hsq : ((|c| + |d|) * |b|) ^ 2 < z ^ 2 := by
        have := size_bound ((a : ℤ) ^ 2) (d ^ 2) hA hD
        rw [hz']; linarith
      exact lt_of_pow_lt_pow_left₀ 2 hz.le hsq
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hZ0 hlt

/-- Both `x, y` odd: `(m, n, (x ^ 2 + y ^ 2) / 2)` is a smaller solution. -/
lemma step_odd_odd {x y z : ℤ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ^ 2 ≠ y ^ 2) (hz : 0 < z)
    (hx2 : x % 2 = 1) (hy2 : y % 2 = 1)
    (hpt : (x ^ 2 - y ^ 2) ^ 2 + (x * y) ^ 2 = z ^ 2)
    (hcop2 : IsCoprime (x ^ 2 - y ^ 2) (x * y)) :
    ∃ a b c : ℤ, G a b c ∧ c.natAbs < z.natAbs := by
  have ht : PythagoreanTriple (x * y) (x ^ 2 - y ^ 2) z := by
    delta PythagoreanTriple; linear_combination hpt
  have hg : Int.gcd (x * y) (x ^ 2 - y ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop2.symm
  have hpar : (x * y) % 2 = 1 := by rw [Int.mul_emod, hx2, hy2]; norm_num
  obtain ⟨m, n, e1, e2, e3, -, -, e6⟩ := ht.coprime_classification' hg hpar hz
  obtain ⟨w, hw⟩ : ∃ w, x ^ 2 + y ^ 2 = 2 * w := by
    obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, y = 2 * j + 1 := ⟨y / 2, by omega⟩
    exact ⟨2 * k ^ 2 + 2 * k + 2 * j ^ 2 + 2 * j + 1, by rw [hk, hj]; ring⟩
  have hd : x ^ 2 - y ^ 2 ≠ 0 := fun e => hxy (by linarith)
  have hm0 : m ≠ 0 := by rintro rfl; apply hd; rw [e2]; ring
  have hn0 : n ≠ 0 := by rintro rfl; apply hd; rw [e2]; ring
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  refine ⟨m, n, w, ⟨hm0, hn0, fun e => hxy0 (by rw [e1, e]; ring), ?_⟩, ?_⟩
  · have : 4 * (m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) = 4 * w ^ 2 := by
      linear_combination (-4 * (m ^ 2 - n ^ 2 + x * y)) * e1
        + (-(x ^ 2 - y ^ 2 + 2 * m * n)) * e2 + (x ^ 2 + y ^ 2 + 2 * w) * hw
    linarith
  · have hw0 : 0 < w := by
      have : 0 < x ^ 2 + y ^ 2 := by positivity
      omega
    have hsq : w ^ 2 < z ^ 2 := by
      have : 0 < (x ^ 2 - y ^ 2) ^ 2 := by positivity
      have h4 : 4 * w ^ 2 = (x ^ 2 + y ^ 2) ^ 2 := by rw [hw]; ring
      nlinarith [hpt]
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hw0.le (lt_of_pow_lt_pow_left₀ 2 hz.le hsq)

theorem G_aux (N : ℕ) : ∀ x y z : ℤ, z.natAbs = N → G x y z → False := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x y z hN h
  have ih' : ∀ a b c : ℤ, G a b c → c.natAbs < z.natAbs → False :=
    fun a b c hg hlt => ih _ (hN ▸ hlt) a b c rfl hg
  clear ih hN
  have hz0 := h.z_ne_zero
  -- WLOG z > 0
  wlog hz : 0 < z generalizing z
  · exact this (-z) ⟨h.1, h.2.1, h.2.2.1, by rw [h.2.2.2]; ring⟩
      (fun a b c hg hlt => ih' a b c hg (by simpa using hlt)) (by omega) (by omega)
  obtain ⟨hx0, hy0, hxy, heq⟩ := h
  -- coprime reduction
  have hcop : Int.gcd x y = 1 := by
    by_contra hg
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpz : (p : ℤ) ^ 2 ∣ z := by
      rw [← Int.pow_dvd_pow_iff two_ne_zero]
      exact ⟨x1 ^ 4 - x1 ^ 2 * y1 ^ 2 + y1 ^ 4, by rw [← heq]; ring⟩
    obtain ⟨z1, rfl⟩ := hpz
    apply ih' x1 y1 z1
    · refine ⟨fun e => hx0 (by rw [e, mul_zero]), fun e => hy0 (by rw [e, mul_zero]), ?_, ?_⟩
      · intro e; apply hxy; rw [mul_pow, mul_pow, e]
      · have hp4 : (p : ℤ) ^ 4 ≠ 0 := pow_ne_zero _ hp0
        apply mul_left_cancel₀ hp4; linear_combination heq
    · have hz1 : z1.natAbs ≠ 0 := by
        intro e; apply hz0; simp [Int.natAbs_eq_zero.mp e]
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      exact lt_mul_left (Nat.pos_of_ne_zero hz1) (Nat.one_lt_pow two_ne_zero hp.one_lt)
  have hcopI : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  -- the Pythagorean triple
  have hpt : (x ^ 2 - y ^ 2) ^ 2 + (x * y) ^ 2 = z ^ 2 := by linear_combination heq
  have hcop2 : IsCoprime (x ^ 2 - y ^ 2) (x * y) := by
    apply IsCoprime.mul_right
    · have : x ^ 2 - y ^ 2 = -(y ^ 2) + x * x := by ring
      rw [this]; exact (hcopI.symm.pow_left.neg_left).add_mul_left_left x
    · have : x ^ 2 - y ^ 2 = x ^ 2 + (-y) * y := by ring
      rw [this]; exact hcopI.pow_left.add_mul_right_left (-y)
  rcases Int.emod_two_eq_zero_or_one x with hx2 | hx2 <;>
    rcases Int.emod_two_eq_zero_or_one y with hy2 | hy2
  · -- both even: impossible
    exfalso
    have : (2 : ℤ) ∣ (Int.gcd x y : ℤ) :=
      Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hx2) (Int.dvd_of_emod_eq_zero hy2)
    rw [hcop] at this; norm_num at this
  · obtain ⟨a, b, c, hg, hlt⟩ := step_one_even hy0 hx0 hz hcopI.symm hy2 hx2
      (by linear_combination hpt) (by
        have := hcop2
        have e1 : y ^ 2 - x ^ 2 = -(x ^ 2 - y ^ 2) := by ring
        have e2 : y * x = x * y := by ring
        rw [e1, e2]; exact this.neg_left)
    exact ih' a b c hg hlt
  · obtain ⟨a, b, c, hg, hlt⟩ := step_one_even hx0 hy0 hz hcopI hx2 hy2 hpt hcop2
    exact ih' a b c hg hlt
  · obtain ⟨a, b, c, hg, hlt⟩ := step_odd_odd hx0 hy0 hxy hz hx2 hy2 hpt hcop2
    exact ih' a b c hg hlt

/-- Euler: `x ^ 4 - x ^ 2 y ^ 2 + y ^ 4 = z ^ 2` forces `x y = 0` or `x ^ 2 = y ^ 2`. -/
theorem quartic_trivial (x y z : ℤ) (h : x ^ 4 - x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2) :
    x * y = 0 ∨ x ^ 2 = y ^ 2 := by
  by_contra hc
  push_neg at hc
  exact G_aux _ x y z rfl ⟨left_ne_zero_of_mul hc.1, right_ne_zero_of_mul hc.1, hc.2, h⟩

end OMA672Q

namespace OMA672H1

open OMA672Q

def cv : Fin 4 → ℕ := ![1, 2, 3, 6]

def ok (M c a : ℕ) : Bool := (List.range M).any (fun s => a % M == c * s * s % M)

def L16 : List (List ℕ) := [[1, 1, 1, 1, 1], [1, 1, 2, 3, 1], [1, 3, 2, 1, 1], [1, 3, 2, 1, 2], [1, 3, 2, 1, 3], [1, 3, 2, 1, 6], [1, 3, 6, 1, 3], [2, 1, 2, 3, 1], [2, 3, 6, 1, 3], [3, 1, 2, 3, 1], [3, 1, 6, 3, 1], [3, 1, 6, 3, 2], [3, 1, 6, 3, 3], [3, 1, 6, 3, 6], [3, 3, 3, 3, 3], [3, 3, 6, 1, 3], [6, 1, 2, 3, 1], [6, 3, 6, 1, 3]]

def L9 : List (List ℕ) := [[1, 1, 1, 1, 1], [1, 1, 2, 1, 6], [1, 1, 2, 3, 1], [1, 2, 1, 1, 2], [1, 2, 1, 6, 2], [1, 2, 2, 1, 2], [1, 2, 2, 1, 6], [1, 2, 3, 1, 2], [1, 2, 6, 1, 2], [1, 3, 2, 1, 1], [1, 3, 2, 1, 2], [1, 3, 2, 1, 3], [1, 3, 2, 1, 6], [1, 6, 2, 1, 3], [1, 6, 2, 1, 6], [2, 1, 1, 2, 1], [2, 1, 1, 2, 3], [2, 1, 2, 2, 1], [2, 1, 2, 3, 1], [2, 1, 3, 2, 1], [2, 1, 6, 2, 1], [2, 2, 1, 2, 3], [2, 2, 1, 6, 2], [2, 2, 2, 2, 2], [2, 3, 1, 2, 3], [2, 3, 1, 2, 6], [2, 6, 1, 2, 1], [2, 6, 1, 2, 2], [2, 6, 1, 2, 3], [2, 6, 1, 2, 6], [3, 1, 2, 3, 1], [3, 1, 2, 6, 1], [3, 2, 1, 1, 2], [3, 2, 1, 2, 2], [3, 2, 1, 3, 2], [3, 2, 1, 6, 2], [6, 1, 2, 1, 1], [6, 1, 2, 2, 1], [6, 1, 2, 3, 1], [6, 1, 2, 6, 1], [6, 2, 1, 3, 2], [6, 2, 1, 6, 2]]

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem loc16 : ∀ N D : Fin 16, (N.val % 2 = 1 ∨ D.val % 2 = 1) → ∀ k0 : Fin 4, ok 16 (cv k0) N = true →
    ∀ k1 : Fin 4, ok 16 (cv k1) (N + D) = true → ∀ k2 : Fin 4, ok 16 (cv k2) (N + 2 * D) = true →
    ∀ k3 : Fin 4, ok 16 (cv k3) (N + 3 * D) = true → ∀ k4 : Fin 4, ok 16 (cv k4) (N + 4 * D) = true →
    [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L16 := by decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem loc9 : ∀ N D : Fin 9, (N.val % 3 ≠ 0 ∨ D.val % 3 ≠ 0) → ∀ k0 : Fin 4, ok 9 (cv k0) N = true →
    ∀ k1 : Fin 4, ok 9 (cv k1) (N + D) = true → ∀ k2 : Fin 4, ok 9 (cv k2) (N + 2 * D) = true →
    ∀ k3 : Fin 4, ok 9 (cv k3) (N + 3 * D) = true → ∀ k4 : Fin 4, ok 9 (cv k4) (N + 4 * D) = true →
    [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L9 := by decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem combine : ∀ k0 k1 k2 k3 k4 : Fin 4, [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L16 →
    [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L9 →
    (∃ r : Fin 100, r.val * r.val = cv k0 * cv k1 * cv k2 * cv k3 * cv k4) →
    [cv k0, cv k1, cv k2, cv k3, cv k4] = [1, 1, 1, 1, 1] ∨
    [cv k0, cv k1, cv k2, cv k3, cv k4] = [1, 3, 2, 1, 6] ∨
    [cv k0, cv k1, cv k2, cv k3, cv k4] = [6, 1, 2, 3, 1] := by decide

lemma ok_intro {M : ℕ} (hM : 0 < M) {x c b : ℕ} (h : x % M = (b ^ 2 * c) % M) : ok M c x = true := by
  simp only [ok, List.any_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨b % M, Nat.mod_lt _ hM, ?_⟩
  have hm : c * (b % M) * (b % M) ≡ c * b * b [MOD M] :=
    ((Nat.ModEq.refl c).mul (Nat.mod_modEq b M)).mul (Nat.mod_modEq b M)
  rw [h, show b ^ 2 * c = c * b * b by ring]
  exact hm.symm

/-- Four squares in a nonconstant AP: impossible. -/
lemma caseA {n d y0 y1 y2 y3 : ℕ} (hd : 0 < d) (h0 : n = y0 ^ 2) (h1 : n + d = y1 ^ 2)
    (h2 : n + 2 * d = y2 ^ 2) (h3 : n + 3 * d = y3 ^ 2) : False := by
  have hr1 : (y2 : ℤ) ^ 2 = 2 * (y1 : ℤ) ^ 2 - (y0 : ℤ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℤ) h0; have := congrArg (Nat.cast : ℕ → ℤ) h1
    have := congrArg (Nat.cast : ℕ → ℤ) h2; push_cast at *; linarith
  have hr2 : (y3 : ℤ) ^ 2 = 3 * (y1 : ℤ) ^ 2 - 2 * (y0 : ℤ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℤ) h0; have := congrArg (Nat.cast : ℕ → ℤ) h1
    have := congrArg (Nat.cast : ℕ → ℤ) h3; push_cast at *; linarith
  set a : ℤ := (y0 : ℤ); set b : ℤ := (y1 : ℤ); set c : ℤ := (y2 : ℤ); set e : ℤ := (y3 : ℤ)
  have hq := quartic_trivial (a + c) (b + e) (a * b - a * e + 3 * b * c + c * e) (by
    linear_combination (5 * a ^ 2 + 4 * a * c - 8 * b ^ 2 - 8 * b * e + c ^ 2 - 2 * e ^ 2) * hr1
      + (-2 * a ^ 2 + 5 * b ^ 2 + 4 * b * e + e ^ 2) * hr2)
  have hlt01 : y0 < y1 := by
    have : y0 ^ 2 < y1 ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hlt23 : y2 < y3 := by
    have : y2 ^ 2 < y3 ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hy1 : 0 < y1 := by omega
  have hy3 : 0 < y3 := by omega
  rcases hq with h | h
  · rcases mul_eq_zero.mp h with h | h
    · have hy2 : 0 < y2 := Nat.pos_of_ne_zero (by rintro rfl; simp at h2; omega)
      have : (0 : ℤ) < c := by show (0 : ℤ) < (y2 : ℤ); exact_mod_cast hy2
      have : (0 : ℤ) ≤ a := by positivity
      linarith
    · have : (0 : ℤ) < b := by show (0 : ℤ) < (y1 : ℤ); exact_mod_cast hy1
      have : (0 : ℤ) ≤ e := by positivity
      linarith
  · have hab : a + c = b + e := by
      have h0' : (0 : ℤ) ≤ a + c := by positivity
      have h1' : (0 : ℤ) ≤ b + e := by positivity
      nlinarith [sq_nonneg (a + c - (b + e)), sq_nonneg (a + c + (b + e))]
    have : (y0 : ℤ) + y2 < y1 + y3 := by exact_mod_cast (by omega : y0 + y2 < y1 + y3)
    linarith

/-- `3u², 2v², w², 6s²` in AP (either direction): impossible. -/
lemma caseB {u v w s : ℤ} (hu : u ≠ 0) (hs : 0 < s) (hv : 0 ≤ v)
    (hw : w ^ 2 = 4 * v ^ 2 - 3 * u ^ 2) (hs2 : s ^ 2 = v ^ 2 - u ^ 2) : False := by
  have hq := quartic_trivial u (v + s) ((v + s) * w) (by
    linear_combination (-s ^ 2 - 2 * s * v - v ^ 2) * hw + (s ^ 2 + 4 * s * v + u ^ 2 + 3 * v ^ 2) * hs2)
  rcases hq with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hu h
    · linarith
  · nlinarith [mul_nonneg hv hs.le]

lemma no_large_prime_two {n d p i j : ℕ} (hnd : n.gcd d = 1) (hp : p.Prime) (hp6 : ¬ p ∣ 6)
    (hi : i < 5) (hj : j < 5) (hij : i ≠ j) (hpi : p ∣ n + i * d) (hpj : p ∣ n + j * d) : False := by
  have hp5 : 5 ≤ p := by
    by_contra hlt; push_neg at hlt
    interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hp6; done) | norm_num at hp hp6
  wlog hlt : i < j generalizing i j
  · exact this hj hi (Ne.symm hij) hpj hpi (by omega)
  have hdiff : p ∣ (j - i) * d := by
    have : n + j * d = (n + i * d) + (j - i) * d := by
      rw [Nat.sub_mul]; have : i * d ≤ j * d := Nat.mul_le_mul_right _ hlt.le; omega
    rw [this] at hpj
    exact (Nat.dvd_add_right hpi).mp hpj
  rcases (Nat.Prime.dvd_mul hp).mp hdiff with h | h
  · have : p ≤ j - i := Nat.le_of_dvd (by omega) h
    omega
  · have hpn : p ∣ n := (Nat.dvd_add_left (Dvd.dvd.mul_left h i)).mp hpi
    have : p ∣ Nat.gcd n d := Nat.dvd_gcd hpn h
    rw [hnd] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem ap5_ne_sq {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1)
    (h : n * ((n + d) * ((n + 2 * d) * ((n + 3 * d) * (n + 4 * d)))) = q ^ 2) : False := by
  have hpos : ∀ i : ℕ, 0 < n + i * d := fun i => by positivity
  have hsplit : ∀ i : ℕ, ∃ c b : ℕ, 0 < c ∧ 0 < b ∧ b ^ 2 * c = n + i * d ∧ Squarefree c :=
    fun i => Nat.sq_mul_squarefree_of_pos (hpos i)
  choose c b hc hb hbc hsf using hsplit
  have hprodA : ∏ i ∈ Finset.range 5, (n + i * d) = q ^ 2 := by
    rw [← h]; simp [Finset.prod_range_succ]; ring
  have hprod : (∏ i ∈ Finset.range 5, b i) ^ 2 * ∏ i ∈ Finset.range 5, c i = q ^ 2 := by
    rw [← hprodA, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hbc i)
  set B := ∏ i ∈ Finset.range 5, b i with hB
  set C := ∏ i ∈ Finset.range 5, c i with hC
  have hB0 : B ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hb i).ne')
  have hBq : B ∣ q := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨C, hprod.symm⟩
  obtain ⟨r, hr⟩ := hBq
  have hCr : C = r ^ 2 := by
    have : B ^ 2 * C = B ^ 2 * r ^ 2 := by rw [hprod, hr]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  -- each squarefree part divides 6
  have hc6 : ∀ i, i < 5 → c i ∣ 6 := by
    intro i hi
    have hpf : ∀ p, p.Prime → p ∣ c i → p ∣ 6 := by
      intro p hp hpc
      by_contra hp6
      have hpC : p ∣ C := dvd_trans hpc (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi))
      rw [hCr] at hpC
      have hpr : p ∣ r := hp.dvd_of_dvd_pow hpC
      have hp2C : p ^ 2 ∣ C := by rw [hCr]; exact pow_dvd_pow_of_dvd hpr 2
      rw [hC, ← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi)] at hp2C
      have hrest : ¬ p ∣ ∏ j ∈ (Finset.range 5).erase i, c j := by
        intro hpe
        obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpe
        obtain ⟨hji, hj5⟩ := Finset.mem_erase.mp hj
        exact no_large_prime_two hnd hp hp6 hi (Finset.mem_range.mp hj5) (Ne.symm hji)
          (dvd_trans hpc ⟨b i ^ 2, by rw [← hbc i]; ring⟩)
          (dvd_trans hpj ⟨b j ^ 2, by rw [← hbc j]; ring⟩)
      have hcop : Nat.Coprime (p ^ 2) (∏ j ∈ (Finset.range 5).erase i, c j) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hrest)
      have : p * p ∣ c i := by rw [← sq]; exact hcop.dvd_of_dvd_mul_right hp2C
      exact (Nat.squarefree_iff_prime_squarefree.mp (hsf i)) p hp this
    rw [← Nat.prod_primeFactors_of_squarefree (hsf i)]
    have h6 : ∏ p ∈ (6 : ℕ).primeFactors, p = 6 :=
      Nat.prod_primeFactors_of_squarefree (by decide +kernel)
    rw [← h6]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hpf p hp.1 hp.2.1, by norm_num⟩
  have hk : ∀ i, i < 5 → ∃ k : Fin 4, c i = cv k := by
    intro i hi
    have h1 := hc6 i hi
    have h2 : c i ≤ 6 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hc i
    interval_cases hci : c i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · norm_num at h1
    · norm_num at h1
    · exact ⟨3, rfl⟩
  obtain ⟨k0, hk0⟩ := hk 0 (by norm_num)
  obtain ⟨k1, hk1⟩ := hk 1 (by norm_num)
  obtain ⟨k2, hk2⟩ := hk 2 (by norm_num)
  obtain ⟨k3, hk3⟩ := hk 3 (by norm_num)
  obtain ⟨k4, hk4⟩ := hk 4 (by norm_num)
  have e0 : n = b 0 ^ 2 * cv k0 := by rw [← hk0, hbc 0]; ring
  have e1 : n + d = b 1 ^ 2 * cv k1 := by rw [← hk1, hbc 1]; ring
  have e2 : n + 2 * d = b 2 ^ 2 * cv k2 := by rw [← hk2, hbc 2]
  have e3 : n + 3 * d = b 3 ^ 2 * cv k3 := by rw [← hk3, hbc 3]
  have e4 : n + 4 * d = b 4 ^ 2 * cv k4 := by rw [← hk4, hbc 4]
  -- local conditions
  have hnotboth : ∀ p, p.Prime → ¬ (p ∣ n ∧ p ∣ d) := by
    rintro p hp ⟨h1, h2⟩
    have : p ∣ Nat.gcd n d := Nat.dvd_gcd h1 h2
    rw [hnd] at this; exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have h16 := loc16 ⟨n % 16, Nat.mod_lt _ (by norm_num)⟩ ⟨d % 16, Nat.mod_lt _ (by norm_num)⟩
    (by have := hnotboth 2 Nat.prime_two; simp only; omega) k0
    (ok_intro (by norm_num) (by simp only; rw [← e0]; omega)) k1
    (ok_intro (by norm_num) (by simp only; rw [← e1]; omega)) k2
    (ok_intro (by norm_num) (by simp only; rw [← e2]; omega)) k3
    (ok_intro (by norm_num) (by simp only; rw [← e3]; omega)) k4
    (ok_intro (by norm_num) (by simp only; rw [← e4]; omega))
  have h9 := loc9 ⟨n % 9, Nat.mod_lt _ (by norm_num)⟩ ⟨d % 9, Nat.mod_lt _ (by norm_num)⟩
    (by have := hnotboth 3 Nat.prime_three; simp only; omega) k0
    (ok_intro (by norm_num) (by simp only; rw [← e0]; omega)) k1
    (ok_intro (by norm_num) (by simp only; rw [← e1]; omega)) k2
    (ok_intro (by norm_num) (by simp only; rw [← e2]; omega)) k3
    (ok_intro (by norm_num) (by simp only; rw [← e3]; omega)) k4
    (ok_intro (by norm_num) (by simp only; rw [← e4]; omega))
  have hCv : C = cv k0 * cv k1 * cv k2 * cv k3 * cv k4 := by
    rw [hC]; simp [Finset.prod_range_succ, hk0, hk1, hk2, hk3, hk4]
  have hcvle : ∀ k : Fin 4, cv k ≤ 6 := by decide
  have hr100 : r < 100 := by
    have : r ^ 2 ≤ 6 * 6 * 6 * 6 * 6 := by
      rw [← hCr, hCv]
      have := hcvle k0; have := hcvle k1; have := hcvle k2; have := hcvle k3; have := hcvle k4
      gcongr <;> assumption
    nlinarith
  have hres := combine k0 k1 k2 k3 k4 h16 h9 ⟨⟨r, hr100⟩, by simp only; rw [← hCv, hCr]; ring⟩
  simp only [List.cons.injEq, and_true] at hres
  rcases hres with ⟨c0, c1, c2, c3, c4⟩ | ⟨c0, c1, c2, c3, c4⟩ | ⟨c0, c1, c2, c3, c4⟩
  · rw [c0] at e0; rw [c1] at e1; rw [c2] at e2; rw [c3] at e3
    exact caseA (n := n) (d := d) (y0 := b 0) (y1 := b 1) (y2 := b 2) (y3 := b 3) hd (by rw [e0]; ring) (by rw [e1]; ring) (by rw [e2]; ring) (by rw [e3]; ring)
  · rw [c1] at e1; rw [c2] at e2; rw [c3] at e3; rw [c4] at e4
    have z1 := congrArg (Nat.cast : ℕ → ℤ) e1; have z2 := congrArg (Nat.cast : ℕ → ℤ) e2
    have z3 := congrArg (Nat.cast : ℕ → ℤ) e3; have z4 := congrArg (Nat.cast : ℕ → ℤ) e4
    push_cast at z1 z2 z3 z4
    exact caseB (u := b 1) (v := b 2) (w := b 3) (s := b 4) (by exact_mod_cast (hb 1).ne')
      (by exact_mod_cast hb 4) (by positivity) (by linarith) (by linarith)
  · rw [c0] at e0; rw [c1] at e1; rw [c2] at e2; rw [c3] at e3
    have z0 := congrArg (Nat.cast : ℕ → ℤ) e0; have z1 := congrArg (Nat.cast : ℕ → ℤ) e1
    have z2 := congrArg (Nat.cast : ℕ → ℤ) e2; have z3 := congrArg (Nat.cast : ℕ → ℤ) e3
    push_cast at z0 z1 z2 z3
    exact caseB (u := b 3) (v := b 2) (w := b 1) (s := b 0) (by exact_mod_cast (hb 3).ne')
      (by exact_mod_cast hb 0) (by positivity) (by linarith) (by linarith)

end OMA672H1

private theorem oma_h1 : OMA.R_Erdos672_erdos_672_variants_oblath_R1.H1 := by
  show Erdos672.Erdos672With 5 2
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d, n + 3 * d, n + 4 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 5 := by exact_mod_cast hk
      interval_cases k <;> simp <;> omega
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
      · exact ⟨3, by norm_num, by ring⟩
      · exact ⟨4, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d, n + 3 * d, n + 4 * d} : Finset ℕ) := by simp; omega
  have h2 : n + d ∉ ({n + 2 * d, n + 3 * d, n + 4 * d} : Finset ℕ) := by simp; omega
  have h3 : n + 2 * d ∉ ({n + 3 * d, n + 4 * d} : Finset ℕ) := by simp; omega
  have h4 : n + 3 * d ∉ ({n + 4 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_insert h3, Finset.prod_insert h4,
    Finset.prod_singleton] at hq
  exact OMA672H1.ap5_ne_sq hn hd hnd hq
end

section

-- Step Erdos672.erdos_672.variants.oblath.R1.H2: hypothesis H2 of reduction Erdos672.erdos_672.variants.oblath.R1
-- Credit: @aqron7

/-! Lemma L (Euler): if `gcd(s, 3t) = 1`, `s + t` is odd and `s ^ 2 + 3 t ^ 2` is a cube, then
`s + t √-3 = (u + v √-3) ^ 3` for integers `u, v`. Proved in the Eisenstein integers. -/

open NumberField IsCyclotomicExtension.Rat.Three

namespace OMA672

/-- The third cyclotomic field. -/
abbrev K3 := CyclotomicField 3 ℚ

instance oma_ne3 : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance oma_cyc3 : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

instance oma_pid : IsPrincipalIdealRing (𝓞 K3) := IsCyclotomicExtension.Rat.three_pid K3

lemma hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K3) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K3

/-- The Eisenstein unit `ω`. -/
noncomputable abbrev ω : 𝓞 K3 := hζ3.toInteger

lemma ω_sq : ω ^ 2 = -ω - 1 := eta_sq hζ3

lemma ω_cube : ω ^ 3 = 1 := hζ3.toInteger_cube_eq_one

/-- Integer coordinates in the basis `1, ω` are unique. -/
lemma coord_zero {a b : ℤ} (h : (a : 𝓞 K3) + b * ω = 0) : a = 0 ∧ b = 0 := by
  have hn : ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K3) = 0 := by
    have : ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K3) = ((a : 𝓞 K3) + b * ω) * (a + b * ω ^ 2) := by
      push_cast
      linear_combination (-(b : 𝓞 K3) ^ 2 * ω - (a : 𝓞 K3) * b + (b : 𝓞 K3) ^ 2) * ω_sq
    rw [this, h, zero_mul]
  have hz : a ^ 2 - a * b + b ^ 2 = 0 := by exact_mod_cast hn
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

lemma coord_eq {a b c d : ℤ} (h : (a : 𝓞 K3) + b * ω = c + d * ω) : a = c ∧ b = d := by
  have := coord_zero (a := a - c) (b := b - d) (by push_cast; linear_combination h)
  omega

/-- Every element of `𝓞 K3` has integer coordinates. -/
lemma exists_coord (x : 𝓞 K3) : ∃ a b : ℤ, x = a + b * ω := by
  obtain ⟨f, rfl⟩ := hζ3.integralPowerBasis.exists_eq_aeval' x
  rw [IsPrimitiveRoot.integralPowerBasis_gen]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, b, ha⟩ := hp
    obtain ⟨c, d, hc⟩ := hq
    exact ⟨a + c, b + d, by rw [map_add, ha, hc]; push_cast; ring⟩
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    induction n with
    | zero => exact ⟨c, 0, by simp⟩
    | succ n ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨-b, a - b, ?_⟩
      rw [pow_succ, ← mul_assoc, hab]
      push_cast
      linear_combination (b : 𝓞 K3) * ω_sq

/-- `√-3 = 1 + 2 ω`. -/
noncomputable abbrev r3 : 𝓞 K3 := 1 + 2 * ω

lemma r3_sq : r3 ^ 2 = -3 := by
  linear_combination 4 * ω_sq

theorem lemma_L {s t b : ℤ} (hc : IsCoprime s (3 * t)) (hpar : Odd (s + t))
    (hb : s ^ 2 + 3 * t ^ 2 = b ^ 3) :
    ∃ u v : ℤ, s = u ^ 3 - 9 * u * v ^ 2 ∧ t = 3 * u ^ 2 * v - 3 * v ^ 3 := by
  set ρ : 𝓞 K3 := s + t * r3 with hρ
  set ρ' : 𝓞 K3 := s - t * r3 with hρ'
  have hprod : ρ * ρ' = (b : 𝓞 K3) ^ 3 := by
    have : ((s ^ 2 + 3 * t ^ 2 : ℤ) : 𝓞 K3) = ((b ^ 3 : ℤ) : 𝓞 K3) := by rw [hb]
    push_cast at this
    rw [← this, hρ, hρ']
    linear_combination (-(t : 𝓞 K3) ^ 2) * r3_sq
  -- coprimality of ρ and ρ'
  have hcop : IsCoprime ρ ρ' := by
    have h3 : IsCoprime s 3 := hc.of_mul_right_left
    have ht : IsCoprime s t := hc.of_mul_right_right
    have hA : IsCoprime (s ^ 2 + 3 * t ^ 2) s := by
      have : IsCoprime (3 * t ^ 2) s := (h3.mul_right ht.pow_right).symm
      have e : s ^ 2 + 3 * t ^ 2 = 3 * t ^ 2 + s * s := by ring
      rw [e]; exact this.add_mul_left_left s
    have hB : IsCoprime (s ^ 2 + 3 * t ^ 2) 2 := by
      obtain ⟨k, hk⟩ := hpar
      refine ⟨1, -(2 * k ^ 2 + 2 * k - 2 * k * t - t + 2 * t ^ 2), ?_⟩
      have : s = 2 * k + 1 - t := by omega
      rw [this]; ring
    obtain ⟨A, B, hAB⟩ := hA.mul_right hB
    refine ⟨A * ρ' + B, B, ?_⟩
    have : ((A * (s ^ 2 + 3 * t ^ 2) + B * (s * 2) : ℤ) : 𝓞 K3) = 1 := by rw [hAB]; simp
    push_cast at this
    rw [← this, hρ, hρ']
    linear_combination (-(A : 𝓞 K3) * (t : 𝓞 K3) ^ 2) * r3_sq
  obtain ⟨γ0, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  -- ρ = ± ω ^ k * γ0 ^ 3
  have hunit : ∃ k ∈ ({0, 1, 2} : Finset ℕ), ∃ γ1 : 𝓞 K3, ρ = ω ^ k * γ1 ^ 3 := by
    have hm := Units.mem hζ3 u0
    have e : ((IsPrimitiveRoot.isUnit (hζ3.toInteger_isPrimitiveRoot) (by decide)).unit :
      𝓞 K3) = ω := rfl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> subst h
    · exact ⟨0, by simp, γ0, by rw [← hu0]; simp⟩
    · exact ⟨0, by simp, -γ0, by rw [← hu0]; simp; ring⟩
    · exact ⟨1, by simp, γ0, by rw [← hu0]; simp [e]; ring⟩
    · exact ⟨1, by simp, -γ0, by rw [← hu0]; simp [e]; ring⟩
    · exact ⟨2, by simp, γ0, by rw [← hu0]; simp [e]; ring⟩
    · exact ⟨2, by simp, -γ0, by rw [← hu0]; simp [e]; ring⟩
  obtain ⟨k, hk, γ1, hγ1⟩ := hunit
  -- normalise γ1 to have even ω-coordinate
  obtain ⟨c, d, hcd⟩ := exists_coord γ1
  have hnorm : ∃ u v : ℤ, γ1 ^ 3 = (u + v * r3) ^ 3 := by
    rcases Int.even_or_odd d with ⟨v, hv⟩ | hd
    · exact ⟨c - v, v, by rw [hcd, hv]; push_cast; ring⟩
    · rcases Int.even_or_odd c with ⟨w, hw⟩ | hco
      · -- ω^2 γ1 = (d - c) + (-c) ω, and -c is even
        refine ⟨d - c + w, -w, ?_⟩
        have : γ1 ^ 3 = (ω ^ 2 * γ1) ^ 3 := by
          rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ω_cube]; ring
        rw [this, hcd, hw]
        push_cast
        have e2 : ω ^ 2 * ((c : 𝓞 K3) + d * ω) = (d - c) + (-c) * ω := by
          linear_combination (c : 𝓞 K3) * ω_sq + (d : 𝓞 K3) * ω_cube
        rw [hw] at e2; push_cast at e2
        rw [e2]; ring
      · -- ω γ1 = -d + (c - d) ω, and c - d is even
        obtain ⟨w, hw⟩ : Even (c - d) := by
          rcases hco with ⟨i, hi⟩; rcases hd with ⟨j, hj⟩; exact ⟨i - j, by omega⟩
        refine ⟨-d - w, w, ?_⟩
        have : γ1 ^ 3 = (ω * γ1) ^ 3 := by rw [mul_pow, ω_cube, one_mul]
        rw [this, hcd]
        have e1 : ω * ((c : 𝓞 K3) + d * ω) = -d + ((c - d : ℤ) : 𝓞 K3) * ω := by
          push_cast; linear_combination (d : 𝓞 K3) * ω_sq
        rw [e1, hw]; push_cast; ring
  obtain ⟨u, v, huv⟩ := hnorm
  rw [huv] at hγ1
  set P := u ^ 3 - 9 * u * v ^ 2 with hP
  set Q := 3 * u ^ 2 * v - 3 * v ^ 3 with hQ
  have hcube : ((u : 𝓞 K3) + v * r3) ^ 3 = P + Q * r3 := by
    rw [hP, hQ]; push_cast
    linear_combination (3 * (u : 𝓞 K3) * v ^ 2 + (v : 𝓞 K3) ^ 3 * r3) * r3_sq
  rw [hcube] at hγ1
  -- compare coordinates in each case
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · refine ⟨u, v, ?_⟩
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((P + Q : ℤ) : 𝓞 K3) + ((2 * Q : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1
    have := coord_eq h0
    constructor <;> omega
  · exfalso
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((-2 * Q : ℤ) : 𝓞 K3) + ((P - Q : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1 + 2 * (Q : 𝓞 K3) * ω_sq
    have := coord_eq h0
    obtain ⟨k, hk⟩ := hpar
    omega
  · exfalso
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((Q - P : ℤ) : 𝓞 K3) + ((-(P + Q) : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1 + ((P : 𝓞 K3) + Q) * ω_sq + 2 * (Q : 𝓞 K3) * ω_cube
    have := coord_eq h0
    obtain ⟨k, hk⟩ := hpar
    omega

/-- If `u ^ 3 - 9 u v ^ 2 + 3 u ^ 2 v - 3 v ^ 3` is odd then `u + v` is odd. -/
lemma odd_add_of_odd_PQ {u v : ℤ}
    (h : Odd (u ^ 3 - 9 * u * v ^ 2 + (3 * u ^ 2 * v - 3 * v ^ 3))) : Odd (u + v) := by
  rcases Int.even_or_odd (u + v) with ⟨m, hm⟩ | ho
  · exfalso
    have hu : u = 2 * m - v := by omega
    rw [← Int.not_even_iff_odd] at h
    apply h
    exact ⟨4 * m ^ 3 - 12 * m * v ^ 2 + 4 * v ^ 3, by rw [hu]; ring⟩
  · exact ho

lemma isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime n 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨1, -k, by ring⟩

lemma cube_left {a b c : ℤ} (h : IsCoprime a b) (habc : a * b = c ^ 3) : ∃ d, a = d ^ 3 :=
  Int.eq_pow_of_mul_eq_pow_odd_left h (by decide) habc

lemma natAbs_le_of_mul {a b : ℤ} (hb : b ≠ 0) : a.natAbs ≤ (a * b).natAbs := by
  rw [Int.natAbs_mul]
  exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hb)

theorem euler_aux (n : ℕ) : ∀ x y z : ℤ, z.natAbs = n → x ^ 3 + y ^ 3 = 2 * z ^ 3 → x ≠ y →
    z ≠ 0 → False := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn h hxy hz
  have ih' : ∀ a b c : ℤ, a ^ 3 + b ^ 3 = 2 * c ^ 3 → a ≠ b → c ≠ 0 →
      c.natAbs < z.natAbs → False :=
    fun a b c h1 h2 h3 h4 => ih _ (hn ▸ h4) a b c rfl h1 h2 h3
  clear ih hn
  -- Step A: x and y coprime
  have hcop : IsCoprime x y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpz : (p : ℤ) ∣ z := by
      have h3 : (p : ℤ) ^ 3 ∣ 2 * z ^ 3 := ⟨x1 ^ 3 + y1 ^ 3, by rw [← h]; ring⟩
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpp.dvd_or_dvd (dvd_trans (dvd_pow_self _ (by norm_num)) h3) with h2 | h2
      · -- p ∣ 2, so p = 2
        have hp2 : p = 2 := by
          have : p ∣ 2 := by exact_mod_cast h2
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
        subst hp2
        obtain ⟨k, hk⟩ := h3
        push_cast at hk ⊢
        have : (2 : ℤ) ∣ z ^ 3 := ⟨2 * k, by linarith⟩
        exact Int.prime_two.dvd_of_dvd_pow this
      · exact hpp.dvd_of_dvd_pow h2
    obtain ⟨z1, rfl⟩ := hpz
    have h1 : x1 ^ 3 + y1 ^ 3 = 2 * z1 ^ 3 := by
      have hp3 : (p : ℤ) ^ 3 ≠ 0 := pow_ne_zero _ hp0
      apply mul_left_cancel₀ hp3
      linear_combination h
    apply ih' x1 y1 z1 h1 (fun e => hxy (by rw [e])) (fun e => hz (by rw [e, mul_zero]))
    have hz1 : z1.natAbs ≠ 0 := by
      intro h0; apply hz; simp [Int.natAbs_eq_zero.mp h0]
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_left (Nat.pos_of_ne_zero hz1) hp.one_lt
  -- Step B: x, y odd; write x = s + t, y = s - t
  have hxy_even : Even (x + y) := by
    have h2 : Even (x ^ 3 + y ^ 3) := ⟨z ^ 3, by rw [h]; ring⟩
    rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at h2
    rw [Int.even_add]; exact h2
  obtain ⟨s, hs⟩ := hxy_even
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := by
        obtain ⟨r, hr⟩ := hx
        exact ⟨s - r, by omega⟩
      have h2 := Int.isCoprime_iff_gcd_eq_one.mp hcop
      have : (2 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hx.two_dvd hy.two_dvd
      rw [h2] at this; norm_num at this
    · exact hx
  set t := x - s with ht
  have hx' : x = s + t := by omega
  have hy' : y = s - t := by omega
  have hpar : Odd (s + t) := by rw [← hx']; exact hxodd
  have ht0 : t ≠ 0 := by intro h0; apply hxy; omega
  have heq : s * (s ^ 2 + 3 * t ^ 2) = z ^ 3 := by
    have : (s + t) ^ 3 + (s - t) ^ 3 = 2 * z ^ 3 := by rw [← hx', ← hy']; exact h
    linarith [this]
  have hs0 : s ≠ 0 := by
    intro h0; apply hz; rw [h0, zero_mul] at heq; exact pow_eq_zero_iff (by norm_num) |>.mp heq.symm
  have hst : IsCoprime s t := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx', hy']; ring⟩
  have hM3 : 3 ≤ (s ^ 2 + 3 * t ^ 2).natAbs := by
    have : 0 < t ^ 2 := by positivity
    have : 3 ≤ s ^ 2 + 3 * t ^ 2 := by nlinarith [sq_nonneg s]
    omega
  by_cases h3s : (3 : ℤ) ∣ s
  · -- Case 2: 3 ∣ s
    obtain ⟨s', rfl⟩ := h3s
    have h3t : IsCoprime t 3 := by
      rw [isCoprime_comm, Prime.coprime_iff_not_dvd Int.prime_three]
      intro h3; exact Int.prime_three.not_isUnit (hst.isUnit_of_dvd' (dvd_mul_right 3 s') h3)
    have hs't : IsCoprime s' t := hst.of_mul_left_right
    have h3z : (3 : ℤ) ∣ z := by
      apply Int.prime_three.dvd_of_dvd_pow (n := 3)
      exact ⟨s' * (9 * s' ^ 2 + 3 * t ^ 2), by rw [← heq]; ring⟩
    obtain ⟨w, rfl⟩ := h3z
    set M := t ^ 2 + 3 * s' ^ 2 with hM
    have hw : s' * M = 3 * w ^ 3 := by
      have : 27 * (s' * M) = 27 * (3 * w ^ 3) := by rw [hM]; linear_combination 3 * heq
      linarith
    have hM3' : ¬ (3 : ℤ) ∣ M := by
      intro h3
      have : (3 : ℤ) ∣ t ^ 2 := by
        have := dvd_sub h3 (dvd_mul_right 3 (s' ^ 2)); rwa [hM, add_sub_cancel_right] at this
      have := Int.prime_three.dvd_of_dvd_pow this
      exact Int.prime_three.not_isUnit (h3t.isUnit_of_dvd' this (dvd_refl 3))
    have h3s' : (3 : ℤ) ∣ s' := by
      rcases Int.prime_three.dvd_or_dvd (⟨w ^ 3, hw⟩ : (3 : ℤ) ∣ s' * M) with h | h
      · exact h
      · exact absurd h hM3'
    obtain ⟨s'', rfl⟩ := h3s'
    have hw' : s'' * M = w ^ 3 := by linarith [hw]
    have hs''M : IsCoprime s'' M := by
      have : IsCoprime s'' t := hs't.of_mul_left_right
      have h1 : IsCoprime s'' (t ^ 2) := this.pow_right
      have e : M = t ^ 2 + s'' * (27 * s'') := by rw [hM]; ring
      rw [e]; exact h1.add_mul_left_right _
    obtain ⟨c, hc⟩ := cube_left hs''M hw'
    obtain ⟨b, hb⟩ := cube_left hs''M.symm (by rw [mul_comm]; exact hw')
    have hL1 : IsCoprime t (3 * (3 * s'')) := h3t.mul_right hs't.symm
    have hL2 : Odd (t + 3 * s'') := by
      have : t + 3 * s'' = 3 * (3 * s'') + t - 2 * (3 * s'') := by ring
      rw [this]
      obtain ⟨k, hk⟩ := hpar
      exact ⟨k - 3 * s'', by omega⟩
    obtain ⟨u, v, hu, hv⟩ := lemma_L hL1 hL2 (by have := hb; rw [hM] at this; exact this)
    have hvc : v * ((u - v) * (u + v)) = c ^ 3 := by
      rw [← hc]
      have : 3 * (v * ((u - v) * (u + v))) = 3 * s'' := by linear_combination -hv
      omega
    have huv : IsCoprime u v := by
      have h1 : IsCoprime t (3 * s'') := hs't.symm
      rw [hu, hv] at h1
      have e1 : u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) := by ring
      have e2 : 3 * u ^ 2 * v - 3 * v ^ 3 = v * (3 * u ^ 2 - 3 * v ^ 2) := by ring
      rw [e1, e2] at h1
      exact h1.of_mul_left_left.of_mul_right_left
    have hodd : Odd (u + v) := by
      have h1 := hL2
      rw [hu, hv] at h1
      exact odd_add_of_odd_PQ h1
    have hvm : IsCoprime v (u - v) := by
      have e : u - v = u + v * (-1) := by ring
      rw [e]; exact huv.symm.add_mul_left_right _
    have hvp : IsCoprime v (u + v) := by
      have e : u + v = u + v * 1 := by ring
      rw [e]; exact huv.symm.add_mul_left_right _
    have hmp : IsCoprime (u - v) (u + v) := by
      have h2 : IsCoprime (u - v) 2 := isCoprime_two_of_odd (by
        obtain ⟨k, hk⟩ := hodd; exact ⟨k - v, by omega⟩)
      have h2v : IsCoprime (u - v) (2 * v) := h2.mul_right hvm.symm
      have e : u + v = 2 * v + (u - v) * 1 := by ring
      rw [e]; exact h2v.add_mul_left_right _
    obtain ⟨γ, hγ⟩ := cube_left (hvm.mul_right hvp) hvc
    obtain ⟨α, hα⟩ := cube_left (hmp.mul_right hvm.symm) (by rw [← hvc]; ring)
    obtain ⟨β, hβ⟩ := cube_left (hmp.symm.mul_right hvp.symm) (by rw [← hvc]; ring)
    have hv0 : v ≠ 0 := by
      intro h0; apply hs0; rw [h0] at hv; linarith [hv]
    have hu0 : u ≠ 0 := by
      intro h0; apply ht0; rw [hu, h0]; ring
    have hγ0 : γ ≠ 0 := by rintro rfl; apply hv0; rw [hγ]; ring
    apply ih' β (-α) γ (by linear_combination -hβ + hα + 2 * hγ) ?_ hγ0 ?_
    · intro e
      apply hu0
      have : β ^ 3 = -(α ^ 3) := by rw [e]; ring
      linarith [hα, hβ, this]
    · -- |γ| ≤ |c| ≤ |w| < 3 |w| = |z|
      have hc0 : c ≠ 0 := by
        rintro rfl; apply hs0; rw [hc]; ring
      have hγc : γ.natAbs ^ 3 ≤ c.natAbs ^ 3 := by
        rw [← Int.natAbs_pow, ← Int.natAbs_pow, ← hγ, ← hvc]
        have hm : (u - v) * (u + v) ≠ 0 := by
          intro h0; apply hc0; have := hvc; rw [h0, mul_zero] at this
          exact pow_eq_zero_iff (by norm_num) |>.mp this.symm
        exact natAbs_le_of_mul hm
      have hγc' : γ.natAbs ≤ c.natAbs :=
        (Nat.pow_le_pow_iff_left (by norm_num)).mp hγc
      have hb0 : b ≠ 0 := by
        rintro rfl; have : M = 0 := by rw [hb]; ring
        rw [hM] at this; nlinarith [sq_pos_of_ne_zero ht0, sq_nonneg s'']
      have hwcb : w ^ 3 = (c * b) ^ 3 := by rw [mul_pow, ← hc, ← hb, hw']
      have hw : w.natAbs = c.natAbs * b.natAbs := by
        rw [← Int.natAbs_mul]
        have := congrArg Int.natAbs hwcb
        rw [Int.natAbs_pow, Int.natAbs_pow] at this
        exact Nat.pow_left_injective (by norm_num) this
      have hb1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb0
      rw [Int.natAbs_mul]
      norm_num
      nlinarith [Int.natAbs_pos.mpr hc0]
  · -- Case 1: 3 ∤ s
    have h3 : IsCoprime s 3 := by
      rw [isCoprime_comm, Prime.coprime_iff_not_dvd Int.prime_three]; exact h3s
    have hL1 : IsCoprime s (3 * t) := h3.mul_right hst
    have hsM : IsCoprime s (s ^ 2 + 3 * t ^ 2) := by
      have : IsCoprime s (3 * t ^ 2) := h3.mul_right hst.pow_right
      have e : s ^ 2 + 3 * t ^ 2 = 3 * t ^ 2 + s * s := by ring
      rw [e]; exact this.add_mul_left_right _
    obtain ⟨a, ha⟩ := cube_left hsM heq
    obtain ⟨b, hb⟩ := cube_left hsM.symm (by rw [mul_comm]; exact heq)
    obtain ⟨u, v, hu, hv⟩ := lemma_L hL1 hpar hb
    have huv : IsCoprime u v := by
      have h1 := hst
      rw [hu, hv] at h1
      have e1 : u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) := by ring
      have e2 : 3 * u ^ 2 * v - 3 * v ^ 3 = v * (3 * u ^ 2 - 3 * v ^ 2) := by ring
      rw [e1, e2] at h1
      exact h1.of_mul_left_left.of_mul_right_left
    have hu3 : IsCoprime u 3 := by
      have h1 := h3
      rw [hu, show u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) by ring] at h1
      exact h1.of_mul_left_left
    have hodd : Odd (u + v) := by
      apply odd_add_of_odd_PQ; rw [← hu, ← hv]; exact hpar
    have hsfac : s = u * ((u - 3 * v) * (u + 3 * v)) := by rw [hu]; ring
    have hu3v : IsCoprime u (3 * v) := hu3.mul_right huv
    have hum : IsCoprime u (u - 3 * v) := by
      have e : u - 3 * v = -(3 * v) + u * 1 := by ring
      rw [e]; exact hu3v.neg_right.add_mul_left_right _
    have hup : IsCoprime u (u + 3 * v) := by
      have e : u + 3 * v = 3 * v + u * 1 := by ring
      rw [e]; exact hu3v.add_mul_left_right _
    have hmp : IsCoprime (u - 3 * v) (u + 3 * v) := by
      have h2 : IsCoprime (u - 3 * v) 2 := isCoprime_two_of_odd (by
        obtain ⟨k, hk⟩ := hodd; exact ⟨k - 2 * v, by omega⟩)
      have h3' : IsCoprime (u - 3 * v) 3 := by
        have e : u - 3 * v = u + 3 * (-v) := by ring
        rw [e]; exact (hu3.symm.add_mul_left_right _).symm
      have hv' : IsCoprime (u - 3 * v) v := by
        have e : u - 3 * v = u + v * (-3) := by ring
        rw [e]; exact (huv.symm.add_mul_left_right _).symm
      have h6 : IsCoprime (u - 3 * v) (6 * v) := by
        have := (h2.mul_right h3').mul_right hv'
        convert this using 2; ring
      have e : u + 3 * v = 6 * v + (u - 3 * v) * 1 := by ring
      rw [e]; exact h6.add_mul_left_right _
    rw [hsfac] at ha
    obtain ⟨α, hα⟩ := cube_left (hum.mul_right hup) ha
    obtain ⟨β, hβ⟩ := cube_left (hmp.mul_right hum.symm) (by rw [← ha]; ring)
    obtain ⟨γ, hγ⟩ := cube_left (hmp.symm.mul_right hup.symm) (by rw [← ha]; ring)
    have hu0 : u ≠ 0 := by intro h0; apply hs0; rw [hsfac, h0, zero_mul]
    have hv0 : v ≠ 0 := by intro h0; apply ht0; rw [hv, h0]; ring
    have hα0 : α ≠ 0 := by rintro rfl; apply hu0; rw [hα]; ring
    apply ih' β γ α (by linear_combination -hβ - hγ + 2 * hα) ?_ hα0 ?_
    · intro e; apply hv0
      have : β ^ 3 = γ ^ 3 := by rw [e]
      linarith [hβ, hγ, this]
    · -- |α|^3 = |u| ≤ |s| < |z|^3
      have hm : (u - 3 * v) * (u + 3 * v) ≠ 0 := by
        intro h0; apply hs0; rw [hsfac, h0, mul_zero]
      have h1 : α.natAbs ^ 3 ≤ s.natAbs := by
        rw [← Int.natAbs_pow, ← hα, hsfac]; exact natAbs_le_of_mul hm
      have h2 : z.natAbs ^ 3 = s.natAbs * (s ^ 2 + 3 * t ^ 2).natAbs := by
        rw [← Int.natAbs_pow, ← heq, Int.natAbs_mul]
      have hs1 : 1 ≤ s.natAbs := Int.natAbs_pos.mpr hs0
      have h3' : α.natAbs ^ 3 < z.natAbs ^ 3 := by rw [h2]; nlinarith
      exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h3'

/-- Euler: `x ^ 3 + y ^ 3 = 2 z ^ 3` forces `x = y` or `z = 0`. -/
theorem euler_cubes (x y z : ℤ) (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : x = y ∨ z = 0 := by
  by_contra hc
  push_neg at hc
  exact euler_aux _ x y z rfl h hc.1 hc.2

end OMA672

namespace OMA672

/-- Euler: the only integer solutions of `x ^ 3 + y ^ 3 = 2 z ^ 3` have `x = y` or `z = 0`. -/
def EulerCubes : Prop := ∀ x y z : ℤ, x ^ 3 + y ^ 3 = 2 * z ^ 3 → x = y ∨ z = 0

lemma cube_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (habc : a * b = c ^ 3) : ∃ u, a = u ^ 3 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) habc

/-- If `E * O = 2 * m ^ 3` with `E` even and `E, O` coprime then `E = 2 u ^ 3`, `O = w ^ 3`. -/
lemma split_even {E O m : ℕ} (hc : Nat.Coprime E O) (hE : Even E) (h : E * O = 2 * m ^ 3) :
    ∃ u w, E = 2 * u ^ 3 ∧ O = w ^ 3 := by
  obtain ⟨E', rfl⟩ := hE
  have h' : E' * O = m ^ 3 := by nlinarith [h]
  have hc' : Nat.Coprime E' O := Nat.Coprime.coprime_mul_left (by rwa [← two_mul] at hc)
  obtain ⟨u, hu⟩ := cube_of_coprime hc' h'
  obtain ⟨w, hw⟩ := cube_of_coprime hc'.symm (by rw [mul_comm]; exact h')
  exact ⟨u, w, by rw [hu]; ring, hw⟩

theorem ap3_ne_cube (core : EulerCubes) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) : n * ((n + d) * (n + 2 * d)) ≠ q ^ 3 := by
  intro hq
  have c1 : Nat.Coprime (n + d) n := by
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.Coprime.symm hnd
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := by
    have : n + 2 * d = (n + d) + d := by ring
    rw [this, Nat.coprime_self_add_right, Nat.coprime_add_self_left]; exact hnd
  have hmid : (n + d) * (n * (n + 2 * d)) = q ^ 3 := by rw [← hq]; ring
  obtain ⟨b, hb⟩ := cube_of_coprime (Nat.Coprime.mul_right c1 c2) hmid
  have hb0 : (b : ℤ) ≠ 0 := by
    intro h0; have : b = 0 := by exact_mod_cast h0
    subst this; simp at hb; omega
  rcases Nat.even_or_odd n with hev | hodd
  · -- n even: n = 2A, d odd, A and A + d coprime
    obtain ⟨A, hA⟩ := hev
    have hA' : n = 2 * A := by omega
    subst hA'
    have hdodd : Odd d := by
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | h
      · exfalso
        have : 2 ∣ Nat.gcd (2 * A) d := Nat.dvd_gcd ⟨A, rfl⟩ ⟨k, by omega⟩
        rw [hnd] at this; omega
      · exact h
    have hcAC : Nat.Coprime A (A + d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.coprime_mul_left hnd
    have hrest : 2 * A * (2 * A + 2 * d) = 4 * (A * (A + d)) := by ring
    have hBA : (2 * A * (2 * A + 2 * d)) * (2 * A + d) = q ^ 3 := by rw [← hmid]; ring
    obtain ⟨m, hm⟩ := cube_of_coprime (Nat.Coprime.mul_right c1 c2).symm hBA
    rw [hrest] at hm
    have hm2 : 2 ∣ m := by
      have : 2 ∣ m ^ 3 := ⟨2 * (A * (A + d)), by rw [← hm]; ring⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    obtain ⟨m', rfl⟩ := hm2
    have hAC : A * (A + d) = 2 * m' ^ 3 := by nlinarith [hm]
    have hsum : 2 * A + d = A + (A + d) := by ring
    have hApos : 0 < A := by omega
    rcases Nat.even_or_odd A with hAe | hAo
    · obtain ⟨u, w, hu, hw⟩ := split_even hcAC hAe hAC
      have key : (b : ℤ) ^ 3 + (-(w : ℤ)) ^ 3 = 2 * (u : ℤ) ^ 3 := by
        have : b ^ 3 = 2 * u ^ 3 + w ^ 3 := by rw [← hb, hsum, hw, hu]
        have : ((b ^ 3 : ℕ) : ℤ) = ((2 * u ^ 3 + w ^ 3 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      rcases core _ _ _ key with h | h
      · have hw0 : (0 : ℤ) < w := by
          have : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h0 | h0
            · subst h0; simp at hw; omega
            · exact h0
          exact_mod_cast this
        have : (0 : ℤ) ≤ b := by positivity
        omega
      · have : u = 0 := by exact_mod_cast h
        subst this; simp at hu; omega
    · have hCe : Even (A + d) := by
        rcases hAo with ⟨k, hk⟩; rcases hdodd with ⟨j, hj⟩; exact ⟨k + j + 1, by omega⟩
      obtain ⟨u, w, hu, hw⟩ := split_even hcAC.symm hCe (by rw [mul_comm]; exact hAC)
      have key : (b : ℤ) ^ 3 + (-(w : ℤ)) ^ 3 = 2 * (u : ℤ) ^ 3 := by
        have : b ^ 3 = 2 * u ^ 3 + w ^ 3 := by rw [← hb, hsum, hu, hw]; ring
        have : ((b ^ 3 : ℕ) : ℤ) = ((2 * u ^ 3 + w ^ 3 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      rcases core _ _ _ key with h | h
      · have hw0 : (0 : ℤ) < w := by
          have : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h0 | h0
            · subst h0; simp at hw; omega
            · exact h0
          exact_mod_cast this
        have : (0 : ℤ) ≤ b := by positivity
        omega
      · have : u = 0 := by exact_mod_cast h
        subst this; simp at hu; omega
  · -- n odd: the three terms are pairwise coprime cubes
    have c3 : Nat.Coprime n (n + 2 * d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.mul_right (hodd.coprime_two_right) hnd
    have hfirst : n * ((n + d) * (n + 2 * d)) = q ^ 3 := hq
    obtain ⟨a, ha⟩ := cube_of_coprime (Nat.Coprime.mul_right c1.symm c3) hfirst
    have hlast : (n + 2 * d) * (n * (n + d)) = q ^ 3 := by rw [← hq]; ring
    obtain ⟨c, hc⟩ := cube_of_coprime (Nat.Coprime.mul_right c3.symm c2.symm) hlast
    have key : (a : ℤ) ^ 3 + (c : ℤ) ^ 3 = 2 * (b : ℤ) ^ 3 := by
      have : a ^ 3 + c ^ 3 = 2 * b ^ 3 := by rw [← ha, ← hb, ← hc]; ring
      exact_mod_cast this
    rcases core _ _ _ key with h | h
    · have : a = c := by exact_mod_cast h
      subst this; omega
    · exact hb0 h


end OMA672

private theorem oma_h2 : OMA.R_Erdos672_erdos_672_variants_oblath_R1.H2 := by
  show Erdos672.Erdos672With 3 3
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k <;> simp <;> omega
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by simp; omega
  have h2 : n + d ∉ ({n + 2 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton] at hq
  exact OMA672.ap3_ne_cube OMA672.euler_cubes hn hd hnd hq
end

section

-- Step Erdos672.erdos_672.variants.oblath.R1.H3: hypothesis H3 of reduction Erdos672.erdos_672.variants.oblath.R1
-- Credit: @aqron7

/-! Fermat's right triangle theorem: `y ^ 4 + z ^ 2 = x ^ 4` has no solutions with `y z ≠ 0`. -/

namespace OMA672

/-- A nontrivial solution of `y ^ 4 + z ^ 2 = x ^ 4`. -/
def F (x y z : ℤ) : Prop := y ≠ 0 ∧ z ≠ 0 ∧ y ^ 4 + z ^ 2 = x ^ 4

lemma F.x_ne_zero {x y z : ℤ} (h : F x y z) : x ≠ 0 := by
  rintro rfl
  have : 0 < y ^ 4 := by positivity [h.1]
  nlinarith [h.2.2, sq_nonneg z]

lemma F.neg {x y z : ℤ} (h : F x y z) : F (-x) y z :=
  ⟨h.1, h.2.1, by rw [h.2.2]; ring⟩

/-- `r ^ 2 - s ^ 2` is coprime to `r * s` when `r` and `s` are coprime. -/
lemma isCoprime_sq_sub {r s : ℤ} (h : IsCoprime r s) : IsCoprime (r ^ 2 - s ^ 2) (r * s) := by
  apply IsCoprime.mul_right
  · have : IsCoprime (s ^ 2) r := (isCoprime_comm.mp h).pow_left
    have h2 : IsCoprime (-(s ^ 2)) r := this.neg_left
    have : r ^ 2 - s ^ 2 = -(s ^ 2) + r * r := by ring
    rw [this]
    exact h2.add_mul_left_left r
  · have : IsCoprime (r ^ 2) s := h.pow_left
    have : r ^ 2 - s ^ 2 = r ^ 2 + (-s) * s := by ring
    rw [this]
    exact (h.pow_left).add_mul_right_left (-s)

/-- If `a * b = c ^ 2` with `a, b` coprime and `a > 0` then `a` is a square. -/
lemma sq_of_coprime_pos {a b c : ℤ} (hab : Int.gcd a b = 1) (h : a * b = c ^ 2) (ha : 0 < a) :
    ∃ i, a = i ^ 2 := by
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hab h
  rcases hi with hi | hi
  · exact ⟨i, hi⟩
  · exfalso; nlinarith [sq_nonneg i]

/-- The descent step, shared by both parity cases: `o` odd, `o ^ 2 + e ^ 2 = x ^ 2`,
coprime, `x > 0`, `o > 0`, `e ≠ 0`, and `w ^ 2 = o * e * 2` for some `w`. Produces a solution
with smaller first coordinate. -/
lemma step_even {o e x w : ℤ} (hco : Int.gcd o e = 1) (ho : o % 2 = 1) (hx : 0 < x)
    (hpy : o ^ 2 + e ^ 2 = x ^ 2) (hopos : 0 < o) (he : e ≠ 0) (hw : w ^ 2 = 2 * o * e) :
    ∃ a b c, F a b c ∧ a.natAbs < x.natAbs := by
  have ht : PythagoreanTriple o e x := by
    delta PythagoreanTriple; linear_combination hpy
  obtain ⟨r, s, h1, h2, h3, h4, -, h6⟩ := ht.coprime_classification' hco ho hx
  -- w is even
  have hw2 : Even w := by
    have : Even (w ^ 2) := ⟨o * e, by rw [hw]; ring⟩
    exact (Int.even_pow' two_ne_zero).mp this
  obtain ⟨w', hw'⟩ := hw2
  have hw'' : w = 2 * w' := by rw [hw']; ring
  rw [hw''] at hw
  have hs : w' ^ 2 = o * (r * s) := by
    have : (2 * w') ^ 2 = 2 * o * (2 * r * s) := by rw [hw, h2]
    nlinarith [this]
  have hcp : Int.gcd o (r * s) = 1 := by
    rw [h1]
    exact Int.isCoprime_iff_gcd_eq_one.mp (isCoprime_sq_sub (Int.isCoprime_iff_gcd_eq_one.mpr h4))
  have hrs0 : r * s ≠ 0 := by
    intro h0; apply he; rw [h2]; linear_combination 2 * h0
  have hrspos : 0 < r * s := by
    have : 0 ≤ o * (r * s) := by rw [← hs]; positivity
    exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_left hopos).mp this) (Ne.symm hrs0)
  obtain ⟨i, hi⟩ := sq_of_coprime_pos hcp hs.symm hopos
  have hcp' : Int.gcd (r * s) o = 1 := by rw [Int.gcd_comm]; exact hcp
  have hs' : r * s * o = w' ^ 2 := by rw [hs]; ring
  obtain ⟨d, hd⟩ := sq_of_coprime_pos hcp' hs' hrspos
  -- r and s have the same sign; r = ±j^2, s = ±k^2 with r ^ 2 = j ^ 4, s ^ 2 = k ^ 4
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one h4 hd
  have h4' : Int.gcd s r = 1 := by rw [Int.gcd_comm]; exact h4
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one h4' (by rw [mul_comm]; exact hd)
  have hr0 : r ≠ 0 := left_ne_zero_of_mul hrs0
  have hs0 : s ≠ 0 := right_ne_zero_of_mul hrs0
  have hj2 : r ^ 2 = j ^ 4 := by rcases hj with hj | hj <;> rw [hj] <;> ring
  have hk2 : s ^ 2 = k ^ 4 := by rcases hk with hk | hk <;> rw [hk] <;> ring
  have hk0 : k ≠ 0 := by rintro rfl; apply hs0; simpa using hk2
  have hi0 : i ≠ 0 := by rintro rfl; rw [hi] at hopos; norm_num at hopos
  refine ⟨j, k, i, ⟨hk0, hi0, ?_⟩, ?_⟩
  · rw [← hk2, ← hj2]; linarith [hi, h1]
  · have hjx : |j| < x := by
      have h1' : |j| ≤ j ^ 2 := by
        have := Int.natAbs_le_self_sq j; rwa [Int.natCast_natAbs] at this
      have h2' : j ^ 2 ≤ j ^ 4 := by
        have := Int.le_self_sq (j ^ 2); nlinarith [this]
      have : 0 < s ^ 2 := by positivity
      nlinarith
    have := Int.natAbs_lt_natAbs_of_nonneg_of_lt (abs_nonneg j) hjx
    rwa [Int.natAbs_abs] at this

theorem no_F_aux (n : ℕ) : ∀ x y z : ℤ, x.natAbs = n → F x y z → False := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn h
  have ih' : ∀ a b c, F a b c → a.natAbs < x.natAbs → False :=
    fun a b c hf hlt => ih _ (hn ▸ hlt) a b c rfl hf
  clear ih hn
  wlog hx : 0 < x generalizing x
  · have hx0 := h.x_ne_zero
    exact this (-x) h.neg (fun a b c hf hlt => ih' a b c hf (by simpa using hlt)) (by omega)
  have hx0 := h.x_ne_zero
  -- x and y are coprime, else divide out a common prime
  have hcop : Int.gcd x y = 1 := by
    by_contra hg
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hpz : (p : ℤ) ^ 2 ∣ z := by
      rw [← Int.pow_dvd_pow_iff two_ne_zero]
      exact ⟨x1 ^ 4 - y1 ^ 4, by linear_combination h.2.2⟩
    obtain ⟨z1, rfl⟩ := hpz
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hf : F x1 y1 z1 := by
      refine ⟨fun h0 => h.1 (by simp [h0]), fun h0 => h.2.1 (by simp [h0]), ?_⟩
      have hp4 : (p : ℤ) ^ 4 ≠ 0 := pow_ne_zero _ hp0
      apply mul_left_cancel₀ hp4
      linear_combination h.2.2
    apply ih' x1 y1 z1 hf
    have hx1 : x1.natAbs ≠ 0 := by
      intro h0; apply hx0; simp [Int.natAbs_eq_zero.mp h0]
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_left (Nat.pos_of_ne_zero hx1) hp.one_lt
  -- y and z are coprime
  have hyz : Int.gcd y z = 1 := by
    by_contra hg
    obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    have hpy' := Int.natCast_dvd.mpr hpy
    have hpz' := Int.natCast_dvd.mpr hpz
    have h4 : (p : ℤ) ∣ x ^ 4 := by
      rw [← h.2.2]; exact dvd_add (dvd_pow hpy' (by norm_num)) (dvd_pow hpz' (by norm_num))
    have hpx : (p : ℤ) ∣ x := Int.Prime.dvd_pow' hp h4
    have hd : (p : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hpx hpy'
    rw [hcop] at hd
    have : p ∣ 1 := by exact_mod_cast hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hyz2 : IsCoprime (y ^ 2) z := (Int.isCoprime_iff_gcd_eq_one.mpr hyz).pow_left
  rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · -- y even: z odd, and (z, y^2, x^2) is a primitive triple
    have hz : z % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one z with hz | hz
      · exfalso
        have h2 : (2 : ℤ) ∣ (Int.gcd y z : ℤ) :=
          Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hy) (Int.dvd_of_emod_eq_zero hz)
        rw [hyz] at h2; norm_num at h2
      · exact hz
    have ht : PythagoreanTriple z (y ^ 2) (x ^ 2) := by
      delta PythagoreanTriple; linear_combination h.2.2
    have hg : Int.gcd z (y ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hyz2.symm
    obtain ⟨m, k, e1, e2, e3, e4, e5, e6⟩ := ht.coprime_classification' hg hz (by positivity)
    have hmk : 0 < m * k := by
      have : 0 < y ^ 2 := by positivity [h.1]
      nlinarith
    have hm : 0 < m := lt_of_le_of_ne e6 (by rintro rfl; simp at hmk)
    have hk : 0 < k := pos_of_mul_pos_right hmk hm.le
    rcases e5 with ⟨hm2, hk2⟩ | ⟨hm2, hk2⟩
    · obtain ⟨a, b, c, hf, hlt⟩ := step_even (o := k) (e := m) (x := x) (w := y)
        (by rw [Int.gcd_comm]; exact e4) hk2 hx (by linear_combination -e3) hk hm.ne'
        (by rw [e2]; ring)
      exact ih' a b c hf hlt
    · obtain ⟨a, b, c, hf, hlt⟩ := step_even (o := m) (e := k) (x := x) (w := y)
        e4 hm2 hx (by linear_combination -e3) hm hk.ne' (by rw [e2])
      exact ih' a b c hf hlt
  · -- y odd: (y^2, z, x^2) is a primitive triple
    have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
      delta PythagoreanTriple; linear_combination h.2.2
    have hg : Int.gcd (y ^ 2) z = 1 := Int.isCoprime_iff_gcd_eq_one.mp hyz2
    have hy2 : y ^ 2 % 2 = 1 := by rw [sq, Int.mul_emod, hy]; decide
    obtain ⟨m, k, e1, e2, e3, e4, e5, e6⟩ := ht.coprime_classification' hg hy2 (by positivity)
    have hk0 : k ≠ 0 := by rintro rfl; apply h.2.1; simp [e2]
    have hxy : x * y ≠ 0 := mul_ne_zero hx0 h.1
    have hf : F m k (x * y) := by
      refine ⟨hk0, hxy, ?_⟩
      have : (x * y) ^ 2 = (m ^ 2 + k ^ 2) * (m ^ 2 - k ^ 2) := by rw [mul_pow, e3, e1]
      linear_combination this
    apply ih' m k (x * y) hf
    have hk2 : 0 < k ^ 2 := by positivity
    have hmx : m < x := by nlinarith
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt e6 hmx

/-- Fermat: `y ^ 4 + z ^ 2 = x ^ 4` has no solution with `y z ≠ 0`. -/
theorem not_F {x y z : ℤ} (hy : y ≠ 0) (hz : z ≠ 0) : y ^ 4 + z ^ 2 ≠ x ^ 4 :=
  fun h => no_F_aux _ x y z rfl ⟨hy, hz, h⟩

end OMA672

namespace OMA672

/-- The product of `n, n + d, n + 2d` with `n, d` positive and coprime is never a fourth power. -/
theorem ap3_ne_pow_four {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1) :
    n * ((n + d) * (n + 2 * d)) ≠ q ^ 4 := by
  intro hq
  have c1 : Nat.Coprime (n + d) n := by
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.Coprime.symm hnd
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := by
    have : n + 2 * d = (n + d) + d := by ring
    rw [this, Nat.coprime_self_add_right, Nat.coprime_add_self_left]; exact hnd
  have hcop : Nat.Coprime (n + d) (n * (n + 2 * d)) := Nat.Coprime.mul_right c1 c2
  have hAB : (n + d) * (n * (n + 2 * d)) = q ^ 4 := by rw [← hq]; ring
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hAB
  have hBA : (n * (n + 2 * d)) * (n + d) = q ^ 4 := by rw [← hAB]; ring
  obtain ⟨m, hm⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm) hBA
  have key : (n + d) ^ 2 = n * (n + 2 * d) + d ^ 2 := by ring
  rw [hv, hm] at key
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < n * (n + 2 * d) := by positivity
    simp [hm] at this
  apply not_F (x := (v : ℤ) ^ 2) (y := (m : ℤ)) (z := (d : ℤ))
    (by exact_mod_cast hm0) (by exact_mod_cast hd.ne')
  have key' : ((v : ℤ) ^ 4) ^ 2 = (m : ℤ) ^ 4 + (d : ℤ) ^ 2 := by exact_mod_cast key
  linear_combination -key'

end OMA672

private theorem oma_h3 : OMA.R_Erdos672_erdos_672_variants_oblath_R1.H3 := by
  show Erdos672.Erdos672With 3 4
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k <;> simp <;> omega
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by simp; omega
  have h2 : n + d ∉ ({n + 2 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton] at hq
  exact OMA672.ap3_ne_pow_four hn hd hnd hq
end

section

-- Reduction Erdos672.erdos_672.variants.oblath.R1.H4.R1 of step Erdos672.erdos_672.variants.oblath.R1.H4
--
-- H4 is `Erdos672.Erdos672With 3 5`: for positive `n`, `d` with `gcd n d = 1` the product
-- `n * (n + d) * (n + 2 * d)` is never a perfect fifth power. Writing `n * (n + d) * (n + 2 * d)
-- = q ^ 5`, the two gcds `gcd n (n + d)` and `gcd (n + d) (n + 2 * d)` are `1` and the outer
-- gcd divides `2`, so the parity of `n` decides the shape of the problem:
--
--   H1: `x ^ 5 + y ^ 5 = 2 * z ^ 5` has no solution with `x ≠ y` and `z ≠ 0`, that is, there
--       are no three distinct fifth powers in arithmetic progression. This is the odd branch,
--       where `n`, `n + d`, `n + 2 * d` are pairwise coprime and hence all fifth powers.
--   H2: `g ^ 5 + 8 * b ^ 5 = s ^ 5` has no solution with `b` and `g` positive. This is the even
--       branch, where `n = 2 * A`, `C = A + d` and the pairwise coprime numbers `4 * A`, `C`,
--       `A + C` multiply to `q ^ 5`.
--
-- Both hypotheses are classical fifth power statements; `main` proves `H1 → H2 → H4`.

/-!
# H4 of Erdős 672 (Obláth), `k = 3`, `l = 5`, split into two fifth power statements

The product of a three term arithmetic progression with coprime first term and difference is
never a perfect fifth power, assuming there are no three distinct fifth powers in arithmetic
progression and no solution of the primitive equation `g ^ 5 + 8 * b ^ 5 = s ^ 5`.

Suppose `n * (n + d) * (n + 2 * d) = q ^ 5` with `n`, `d` positive and `gcd n d = 1`.

* `n` odd: the three terms are odd, hence pairwise coprime, hence each is a fifth power: say
  `n = a ^ 5`, `n + d = b ^ 5`, `n + 2 * d = c ^ 5`. Then `a ^ 5 + c ^ 5 = 2 * b ^ 5` with
  `a ≠ c` and `b ≠ 0`, contradicting `H1`.
* `n` even: then `d` is odd and `gcd n (n + 2 * d) = 2`. Write `n = 2 * A` and `C = A + d`, so
  `n + d = A + C` and `n + 2 * d = 2 * C`. Exactly one of `A`, `C` is even, so the three
  pairwise coprime numbers `4 * A`, `C`, `A + C` multiply to `q ^ 5` (the factor `4` sits on the
  even one and `A + C` is odd). Each is a fifth power; `4 * A = y ^ 5` forces `A = 8 * b ^ 5`,
  and `C = g ^ 5`, `A + C = s ^ 5` give `g ^ 5 + 8 * b ^ 5 = s ^ 5` with `b`, `g` positive,
  contradicting `H2`.
-/

namespace OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1

/-- No three distinct fifth powers are in arithmetic progression, in the integral form
`x ^ 5 + y ^ 5 = 2 * z ^ 5`. -/
def H1 : Prop := ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 2 * z ^ 5 → x = y ∨ z = 0

/-- The shifted equation `g ^ 5 + 8 * b ^ 5 = s ^ 5` has no solution with `b`, `g` positive. -/
def H2 : Prop := ∀ b g s : ℕ, 0 < b → 0 < g → g ^ 5 + 8 * b ^ 5 ≠ s ^ 5

/- ## Splitting coprime products of fifth powers -/

/-- A factor of a fifth power coprime to the rest is itself a fifth power. -/
lemma pow5_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (habc : a * b = c ^ 5) :
    ∃ u, a = u ^ 5 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) habc

/-- If `4 * X` is a fifth power then `X` is eight times a fifth power. -/
lemma eq_eight_mul_pow5 {X : ℕ} {y : ℕ} (h : 4 * X = y ^ 5) : ∃ u, X = 8 * u ^ 5 := by
  have h2 : 2 ∣ y := by
    refine Nat.prime_two.dvd_of_dvd_pow (n := 5) ?_
    rw [← h]
    exact ⟨2 * X, by ring⟩
  obtain ⟨u, rfl⟩ := h2
  refine ⟨u, ?_⟩
  have hy : 4 * X = 32 * u ^ 5 := by rw [h]; ring
  omega

/- ## The gcd structure of a three term progression -/

/-- The first and second term of the progression are coprime. -/
lemma coprime_n_naddd {n d : ℕ} (hnd : n.gcd d = 1) : Nat.Coprime n (n + d) := by
  rw [Nat.coprime_self_add_right]
  exact hnd

/-- The second and third term of the progression are coprime. -/
lemma coprime_naddd_n2d {n d : ℕ} (hnd : n.gcd d = 1) : Nat.Coprime (n + d) (n + 2 * d) := by
  have h : n + 2 * d = (n + d) + d := by ring
  rw [h, Nat.coprime_self_add_right, Nat.coprime_add_self_left]
  exact hnd

/-- The outer terms of the progression have gcd dividing `2`. -/
lemma gcd_n_n2d_dvd_two {n d : ℕ} (hnd : n.gcd d = 1) : Nat.gcd n (n + 2 * d) ∣ 2 := by
  have h1 : Nat.gcd n (n + 2 * d) = Nat.gcd n (2 * d) := by
    rw [Nat.gcd_self_add_right]
  rw [h1]
  have hcop : Nat.Coprime (Nat.gcd n (2 * d)) d := by
    rw [Nat.Coprime, Nat.gcd_assoc]
    rw [show Nat.gcd (2 * d) d = d from
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd (Nat.dvd_mul_left d 2) dvd_rfl)]
    exact hnd
  exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_right n (2 * d))

/-- With `n` odd the outer terms of the progression are coprime. -/
lemma coprime_n_n2d_of_odd {n d : ℕ} (hnd : n.gcd d = 1) (hodd : Odd n) :
    Nat.Coprime n (n + 2 * d) := by
  rw [Nat.coprime_self_add_right]
  exact hodd.coprime_two_right.mul_right hnd

/- ## The odd branch -/

/-- If `n` is odd and `n * (n + d) * (n + 2 * d)` is a fifth power, then the three terms are
fifth powers `a ^ 5`, `b ^ 5`, `c ^ 5` in arithmetic progression, with `a ≠ c` and `b ≠ 0`. -/
theorem odd_branch {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1)
    (hodd : Odd n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) :
    ∃ a b c : ℕ, n = a ^ 5 ∧ n + d = b ^ 5 ∧ n + 2 * d = c ^ 5 ∧
      a ^ 5 + c ^ 5 = 2 * b ^ 5 ∧ a ≠ c ∧ b ≠ 0 := by
  have c1 : Nat.Coprime (n + d) n := (coprime_n_naddd hnd).symm
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := coprime_naddd_n2d hnd
  have c3 : Nat.Coprime n (n + 2 * d) := coprime_n_n2d_of_odd hnd hodd
  obtain ⟨b, hb⟩ := pow5_of_coprime (c1.mul_right c2) (by rw [← hq]; ring)
  obtain ⟨a, ha⟩ := pow5_of_coprime (c1.symm.mul_right c3) hq
  obtain ⟨c, hc⟩ := pow5_of_coprime (c3.symm.mul_right c2.symm) (by rw [← hq]; ring)
  have hsum : a ^ 5 + c ^ 5 = 2 * b ^ 5 := by
    rw [← ha, ← hb, ← hc]
    ring
  refine ⟨a, b, c, ha, hb, hc, hsum, ?_, ?_⟩
  · intro h
    subst h
    omega
  · intro h
    subst h
    simp at hb
    omega

/-- On the odd branch, `H1` gives a contradiction. -/
theorem false_of_odd (h1 : H1) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) (hodd : Odd n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) : False := by
  obtain ⟨a, b, c, ha, hb, hc, hsum, hac, hb0⟩ := odd_branch hn hd hnd hodd hq
  have hkey : ((a : ℤ)) ^ 5 + ((c : ℤ)) ^ 5 = 2 * ((b : ℤ)) ^ 5 := by
    exact_mod_cast hsum
  rcases h1 a c b hkey with h | h
  · exact hac (by exact_mod_cast h)
  · exact hb0 (by exact_mod_cast h)

/- ## The even branch -/

/-- From `4 * A * C * (A + C)` a fifth power, with `A`, `C` positive and coprime and `A + C`
odd, one gets positive `b`, `g`, `s` with `g ^ 5 + 8 * b ^ 5 = s ^ 5`. -/
theorem exists_eight_of_even {A C q : ℕ} (hA : 0 < A) (hC : 0 < C) (hcop : Nat.Coprime A C)
    (hodd : Odd (A + C)) (hq : 4 * (A * C * (A + C)) = q ^ 5) :
    ∃ b g s : ℕ, 0 < b ∧ 0 < g ∧ g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
  have h2 : Nat.Coprime 2 (A + C) := hodd.coprime_two_left
  have hAAC : Nat.Coprime A (A + C) := by
    rw [Nat.coprime_self_add_right]
    exact hcop
  have hCAC : Nat.Coprime C (A + C) := by
    have h : Nat.Coprime C (C + A) := by
      rw [Nat.coprime_self_add_right]
      exact hcop.symm
    rwa [add_comm C A] at h
  rcases Nat.even_or_odd A with hAe | hAo
  · -- `A` even and `C` odd: the coprime triple is `4 * A`, `C`, `A + C`
    have hCodd : Odd C := by
      obtain ⟨j, hj⟩ := hodd
      obtain ⟨k, hk⟩ := hAe
      exact ⟨j - k, by omega⟩
    have h4C : Nat.Coprime (2 * 2) C := hCodd.coprime_two_left.mul_left hCodd.coprime_two_left
    have h4AC : Nat.Coprime (4 * A) C := by
      have h := h4C.mul_left hcop
      rwa [show 2 * 2 = 4 from rfl] at h
    have h4AAC : Nat.Coprime (4 * A) (A + C) := by
      have h2A : Nat.Coprime (2 * A) (A + C) := h2.mul_left hAAC
      have h := h2.mul_left h2A
      rwa [show 2 * (2 * A) = 4 * A from by ring] at h
    have hp1 : (4 * A) * (C * (A + C)) = q ^ 5 := by rw [← hq]; ring
    have hp2 : C * ((A + C) * (4 * A)) = q ^ 5 := by rw [← hq]; ring
    have hp3 : (A + C) * (C * (4 * A)) = q ^ 5 := by rw [← hq]; ring
    obtain ⟨y, hy⟩ := pow5_of_coprime (h4AC.mul_right h4AAC) hp1
    obtain ⟨g, hg⟩ := pow5_of_coprime (hCAC.mul_right h4AC.symm) hp2
    obtain ⟨s, hs⟩ := pow5_of_coprime (hCAC.symm.mul_right h4AAC.symm) hp3
    obtain ⟨b, hb⟩ := eq_eight_mul_pow5 hy
    refine ⟨b, g, s, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0] at hb
        simp at hb
        omega
      · exact h0
    · rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0] at hg
        simp at hg
        omega
      · exact h0
    · have h : g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
        rw [← hg, ← hb]
        omega
      exact h
  · -- `A` odd and `C` even: the coprime triple is `A`, `4 * C`, `A + C`
    have hCe : Even C := by
      obtain ⟨j, hj⟩ := hodd
      obtain ⟨k, hk⟩ := hAo
      exact ⟨j - k, by omega⟩
    have hAodd : Odd A := hAo
    have h4A : Nat.Coprime (2 * 2) A := hAodd.coprime_two_left.mul_left hAodd.coprime_two_left
    have h4CA : Nat.Coprime (4 * C) A := by
      have h := h4A.mul_left hcop.symm
      rwa [show 2 * 2 = 4 from rfl] at h
    have hA4C : Nat.Coprime A (4 * C) := h4CA.symm
    have h4CAC : Nat.Coprime (4 * C) (A + C) := by
      have h2C : Nat.Coprime (2 * C) (A + C) := h2.mul_left hCAC
      have h := h2.mul_left h2C
      rwa [show 2 * (2 * C) = 4 * C from by ring] at h
    have hp1 : A * ((A + C) * (4 * C)) = q ^ 5 := by rw [← hq]; ring
    have hp2 : (4 * C) * (A * (A + C)) = q ^ 5 := by rw [← hq]; ring
    have hp3 : (A + C) * (A * (4 * C)) = q ^ 5 := by rw [← hq]; ring
    obtain ⟨g, hg⟩ := pow5_of_coprime (hAAC.mul_right hA4C) hp1
    obtain ⟨y, hy⟩ := pow5_of_coprime (h4CA.mul_right h4CAC) hp2
    obtain ⟨s, hs⟩ := pow5_of_coprime (hAAC.symm.mul_right h4CAC.symm) hp3
    obtain ⟨b, hb⟩ := eq_eight_mul_pow5 hy
    refine ⟨b, g, s, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0] at hb
        simp at hb
        omega
      · exact h0
    · rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0] at hg
        simp at hg
        omega
      · exact h0
    · have h : g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
        rw [← hg, ← hb]
        omega
      exact h

/-- If `n` is even and `n * (n + d) * (n + 2 * d)` is a fifth power, then one gets a solution
of `g ^ 5 + 8 * b ^ 5 = s ^ 5` with `b`, `g` positive. -/
theorem even_branch {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1)
    (hev : Even n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) :
    ∃ b g s : ℕ, 0 < b ∧ 0 < g ∧ g ^ 5 + 8 * b ^ 5 = s ^ 5 := by
  obtain ⟨A, hA⟩ := hev
  have hA' : n = 2 * A := by omega
  subst hA'
  have hdodd : Odd d := by
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | h
    · exfalso
      have h2 : 2 ∣ Nat.gcd (2 * A) d := Nat.dvd_gcd ⟨A, by ring⟩ ⟨k, by omega⟩
      rw [hnd] at h2
      omega
    · exact h
  have hApos : 0 < A := by omega
  have hAC : Nat.Coprime A (A + d) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.Coprime.coprime_mul_left hnd
  have hoddAC : Odd (A + (A + d)) := by
    have he : A + (A + d) = 2 * A + d := by ring
    rw [he]
    obtain ⟨k, hk⟩ := hdodd
    exact ⟨A + k, by omega⟩
  have hq' : 4 * (A * (A + d) * (A + (A + d))) = q ^ 5 := by
    have h1 : 2 * A + d = A + (A + d) := by ring
    have h2 : 2 * A + 2 * d = 2 * (A + d) := by ring
    rw [h1, h2] at hq
    have he : 4 * (A * (A + d) * (A + (A + d))) = 2 * A * ((A + (A + d)) * (2 * (A + d))) := by
      ring
    rw [he]
    exact hq
  exact exists_eight_of_even hApos (by omega) hAC hoddAC hq'

/-- On the even branch, `H2` gives a contradiction. -/
theorem false_of_even (h2 : H2) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) (hev : Even n) (hq : n * ((n + d) * (n + 2 * d)) = q ^ 5) : False := by
  obtain ⟨b, g, s, hb0, hg0, heq⟩ := even_branch hn hd hnd hev hq
  exact h2 b g s hb0 hg0 heq

/- ## The arithmetic progression -/

/-- The product of a three term arithmetic progression with coprime first term and difference is
never a perfect fifth power. -/
theorem ap3_ne_pow5 (h1 : H1) (h2 : H2) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) : n * ((n + d) * (n + 2 * d)) ≠ q ^ 5 := by
  intro hq
  rcases Nat.even_or_odd n with hev | hodd
  · exact false_of_even h2 hn hd hnd hev hq
  · exact false_of_odd h1 hn hd hnd hodd hq

theorem main : H1 → H2 → OMA.R_Erdos672_erdos_672_variants_oblath_R1.H4 := by
  intro h1 h2 s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1' : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have h2' : n + d ∉ ({n + 2 * d} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.prod_insert h1', Finset.prod_insert h2', Finset.prod_singleton] at hq
  exact ap3_ne_pow5 h1 h2 hn hd hnd hq

end OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1
end

section

/-!
# Integer fifth powers in arithmetic progression: exact Obláth H1

New quartic descent formalization and integration: Hanan Beer (@hananzlt).
Mathematical proof: Dirichlet and V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵,
https://www.numdam.org/item/JMPA_1843_1_8__49_0.pdf (especially Propositions III–IV).

The golden-integer Euclidean ring, unit classification, fifth-power norm extraction, and
Dirichlet second-case descent below are reused from Pedro Bessa (@nijv):
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5575
Immutable source commit: 572ffd235e0a734035a1737d90d28c37c24417ee.
The exact reduction H1 is authored by @mudkjp, PR3625.
All original source attribution is retained in the component comments below.
This proves an auxiliary step expressing a classical known theorem, not a new mathematical discovery.
-/

/- Component: Dirichlet.lean -/

/-
Golden-integer fifth-power descent, reused from Pedro Bessa (@nijv), PR #5575:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5575
Immutable source head: 572ffd235e0a734035a1737d90d28c37c24417ee.
The source theorem formalizes Dirichlet's classical descent; the mathematical source is also
V.-A. Lebesgue (1843), Théorèmes nouveaux sur l'équation indéterminée x⁵ + y⁵ = az⁵.
Adaptation and integration for exact H1 by Hanan Beer (@hananzlt).
This is supporting material and is not an exact target proof.
-/


open NumberField QuadraticAlgebra

namespace OMA672H2_H1

/- ## Section 1: Euclidean Structure and Units of `ℤ[(1 + √5)/2]` -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
abbrev R := QuadraticAlgebra ℤ 1 1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma five_dvd_of_sq_dvd {x : ℤ} (h : (5 : ℤ) ∣ x ^ 2) : (5 : ℤ) ∣ x :=
  Int.Prime.dvd_pow' Nat.prime_five h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma not_isUnit_five : ¬ IsUnit (5 : ℤ) := by
  rw [Int.isUnit_iff]
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma isCoprime_five_of_not_dvd {n : ℤ} (h : ¬ (5 : ℤ) ∣ n) : IsCoprime n 5 := by
  have hdiv : 5 * (n / 5) + n % 5 = n := Int.mul_ediv_add_emod n 5
  have hr0 : 0 ≤ n % 5 := Int.emod_nonneg n (by omega)
  have hr5 : n % 5 < 5 := Int.emod_lt_of_pos n (by omega)
  have hr_ne : n % 5 ≠ 0 := fun h0 => h (Int.dvd_of_emod_eq_zero h0)
  set q := n / 5
  set r := n % 5
  interval_cases r
  · exact absurd rfl hr_ne
  · exact ⟨1, -q, by omega⟩
  · exact ⟨3, -3 * q - 1, by omega⟩
  · exact ⟨2, -2 * q - 1, by omega⟩
  · exact ⟨-1, q + 1, by omega⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_iff_zmod2 (n : ℤ) : Even n ↔ (n : ZMod 2) = 0 := by
  have h2 : Even n ↔ ((2 : ℕ) : ℤ) ∣ n :=
    ⟨fun ⟨k, hk⟩ => ⟨k, by omega⟩, fun ⟨k, hk⟩ => ⟨k, by omega⟩⟩
  rw [h2, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_iff_zmod2 (n : ℤ) : Odd n ↔ (n : ZMod 2) = 1 := by
  rw [← Int.not_even_iff_odd, even_iff_zmod2]
  generalize (n : ZMod 2) = x
  revert x; decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma norm_eq_zero_aux : ∀ n : ℕ, ∀ x y : ℤ, y.natAbs = n →
    (2 * x + y) ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn h
    have h5a : (5 : ℤ) ∣ (2 * x + y) := five_dvd_of_sq_dvd (h ▸ dvd_mul_right 5 _)
    obtain ⟨k, hk⟩ := h5a
    have hy2 : y ^ 2 = 5 * k ^ 2 := by
      have h25 : 25 * k ^ 2 = 5 * y ^ 2 := by
        calc 25 * k ^ 2 = (5 * k) ^ 2 := by ring
          _ = 5 * y ^ 2 := by rw [← hk, h]
      linarith
    have h5y : (5 : ℤ) ∣ y := five_dvd_of_sq_dvd (hy2 ▸ dvd_mul_right 5 _)
    obtain ⟨y1, rfl⟩ := h5y
    have h5x : (5 : ℤ) ∣ x := by
      have h2x : (5 : ℤ) ∣ 2 * x := ⟨k - y1, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h2x with h2 | hx
      · norm_num at h2
      · exact hx
    obtain ⟨x1, rfl⟩ := h5x
    by_cases hy0 : y1 = 0
    · subst hy0
      simp at h
      exact ⟨by omega, rfl⟩
    · have h1 : (2 * x1 + y1) ^ 2 = 5 * y1 ^ 2 := by
        have : 25 * (2 * x1 + y1) ^ 2 = 25 * (5 * y1 ^ 2) := by linear_combination h
        linarith
      have hlt : y1.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have hypos : 0 < y1.natAbs := Int.natAbs_pos.mpr hy0
        have h5 : (5 : ℤ).natAbs = 5 := rfl
        rw [h5]
        omega
      obtain ⟨hx1, hy1⟩ := ih _ hlt x1 y1 rfl h1
      exact ⟨by simp [hx1], by simp [hy1]⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma R_norm_eq_zero {z : R} (hz : z.norm = 0) : z = 0 := by
  have h4 : (2 * z.re + z.im) ^ 2 = 5 * z.im ^ 2 := by
    have : z.re * z.re + 1 * z.re * z.im - 1 * z.im * z.im = 0 := hz
    linear_combination 4 * this
  obtain ⟨hre, him⟩ := norm_eq_zero_aux _ z.re z.im rfl h4
  ext <;> simp [hre, him]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
instance : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have hn : a.norm * b.norm = 0 := by
      rw [← map_mul, hab, QuadraticAlgebra.norm_zero]
    rcases mul_eq_zero.mp hn with ha | hb
    · exact Or.inl (R_norm_eq_zero ha)
    · exact Or.inr (R_norm_eq_zero hb)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
instance : IsDomain R := NoZeroDivisors.to_isDomain R

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def nearestDiv (N d : ℤ) : ℤ :=
  let Ns := if 0 ≤ d then N else -N
  (2 * Ns + |d|) / (2 * |d|)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma nearestDiv_spec (N : ℤ) {d : ℤ} (hd : d ≠ 0) :
    4 * (N - nearestDiv N d * d) ^ 2 ≤ d ^ 2 := by
  dsimp [nearestDiv]
  set Ns := if 0 ≤ d then N else -N
  have hd_pos : 0 < |d| := abs_pos.mpr hd
  have h2d : 0 < 2 * |d| := by omega
  set q := (2 * Ns + |d|) / (2 * |d|)
  set r := (2 * Ns + |d|) % (2 * |d|)
  have hdiv : 2 * |d| * q + r = 2 * Ns + |d| := Int.mul_ediv_add_emod (2 * Ns + |d|) (2 * |d|)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hr1 : r < 2 * |d| := Int.emod_lt_of_pos _ h2d
  have hdiff : (N - q * d) ^ 2 = (Ns - q * |d|) ^ 2 := by
    by_cases h : 0 ≤ d
    · simp [Ns, h, abs_of_nonneg h]
    · have h' : d < 0 := lt_of_not_ge h
      simp [Ns, h, abs_of_neg h']
      ring
  rw [hdiff]
  have heq : 2 * (Ns - q * |d|) = r - |d| := by linear_combination -hdiv
  have hlin1 : -|d| ≤ 2 * (Ns - q * |d|) := by omega
  have hlin2 : 2 * (Ns - q * |d|) ≤ |d| := by omega
  have hsq : (2 * (Ns - q * |d|)) ^ 2 ≤ |d| ^ 2 := by nlinarith
  have habs : |d| ^ 2 = d ^ 2 := sq_abs d
  nlinarith

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def R_div (a b : R) : R :=
  if b = 0 then 0 else
    let d := b.norm
    let num := a * star b
    ⟨nearestDiv num.re d, nearestDiv num.im d⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
instance : EuclideanDomain R where
  quotient := R_div
  quotient_zero a := by simp [R_div]
  remainder a b := a - R_div a b * b
  quotient_mul_add_remainder_eq a b := by ring
  r a b := a.norm.natAbs < b.norm.natAbs
  r_wellFounded := InvImage.wf (fun z : R => z.norm.natAbs) wellFounded_lt
  remainder_lt a {b} hb := by
    have hd : b.norm ≠ 0 := fun h => hb (R_norm_eq_zero h)
    have hq : R_div a b = ⟨nearestDiv (a * star b).re b.norm, nearestDiv (a * star b).im b.norm⟩ := by
      simp [R_div, hb]
    set q := R_div a b
    set rem := a - q * b
    set d := b.norm
    set X := (a * star b).re - q.re * d
    set Y := (a * star b).im - q.im * d
    have hX : 4 * X ^ 2 ≤ d ^ 2 := by
      dsimp only [X]
      rw [hq]
      exact nearestDiv_spec _ hd
    have hY : 4 * Y ^ 2 ≤ d ^ 2 := by
      dsimp only [Y]
      rw [hq]
      exact nearestDiv_spec _ hd
    have hrem_mul : rem * star b = ⟨X, Y⟩ := by
      have hbb : b * star b = algebraMap ℤ R d := (algebraMap_norm_eq_mul_star b).symm
      calc rem * star b = a * star b - q * (b * star b) := by ring
        _ = a * star b - q * algebraMap ℤ R d := by rw [hbb]
        _ = ⟨X, Y⟩ := by ext <;> simp [X, Y]
    have hnorm_prod : rem.norm * d = X * X + 1 * X * Y - 1 * Y * Y := by
      have := congr_arg QuadraticAlgebra.norm hrem_mul
      rw [map_mul, QuadraticAlgebra.norm_star] at this
      exact this
    have hd2_pos : 1 ≤ d ^ 2 := by
      have : 0 < d ^ 2 := sq_pos_of_ne_zero hd
      omega
    have hup : rem.norm * d < d ^ 2 := by
      have : 16 * (rem.norm * d) = 20 * X ^ 2 - 4 * (X - 2 * Y) ^ 2 := by
        rw [hnorm_prod]; ring
      nlinarith [sq_nonneg (X - 2 * Y)]
    have hlo : -(d ^ 2) < rem.norm * d := by
      have : 16 * (rem.norm * d) = 4 * (2 * X + Y) ^ 2 - 20 * Y ^ 2 := by
        rw [hnorm_prod]; ring
      nlinarith [sq_nonneg (2 * X + Y)]
    have habs_lt : (rem.norm * d).natAbs < (d ^ 2).natAbs := by
      rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
        abs_of_pos (show 0 < d ^ 2 by omega), abs_lt]
      exact ⟨hlo, hup⟩
    rw [Int.natAbs_mul, sq, Int.natAbs_mul] at habs_lt
    exact Nat.lt_of_mul_lt_mul_right habs_lt
  mul_left_not_lt a {b} hb := by
    rw [map_mul, Int.natAbs_mul]
    have hbn : b.norm ≠ 0 := fun h => hb (R_norm_eq_zero h)
    have hb1 : 1 ≤ b.norm.natAbs := Int.natAbs_pos.mpr hbn
    exact not_lt.mpr (Nat.le_mul_of_pos_right _ hb1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def ω₀ : R := ⟨0, 1⟩
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def ω_inv : R := ⟨-1, 1⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma ω₀_mul_inv : ω₀ * ω_inv = 1 := by
  ext <;> simp [ω₀, ω_inv]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma isUnit_ω₀ : IsUnit ω₀ :=
  ⟨⟨ω₀, ω_inv, ω₀_mul_inv, by rw [mul_comm]; exact ω₀_mul_inv⟩, rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma isUnit_ω_inv : IsUnit ω_inv :=
  ⟨⟨ω_inv, ω₀, by rw [mul_comm]; exact ω₀_mul_inv, ω₀_mul_inv⟩, rfl⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma unit_form_neg {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ -v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  exact ⟨r, hr, -η, hη.neg, by ring⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma unit_form_mul_ω₀ {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ ω₀ * v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  rw [Finset.mem_range] at hr
  interval_cases r
  · exact ⟨1, by simp, η, hη, by ring⟩
  · exact ⟨2, by simp, η, hη, by ring⟩
  · exact ⟨3, by simp, η, hη, by ring⟩
  · exact ⟨4, by simp, η, hη, by ring⟩
  · exact ⟨0, by simp, ω₀ * η, isUnit_ω₀.mul hη, by ring⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma unit_form_mul_inv {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ ω_inv * v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  rw [Finset.mem_range] at hr
  interval_cases r
  · refine ⟨4, by simp, ω_inv * η, isUnit_ω_inv.mul hη, ?_⟩
    have h4 : ω₀ ^ 4 * ω_inv ^ 5 = ω_inv := by
      calc ω₀ ^ 4 * ω_inv ^ 5 = (ω₀ * ω_inv) ^ 4 * ω_inv := by ring
        _ = ω_inv := by rw [ω₀_mul_inv]; ring
    calc ω_inv * (ω₀ ^ 0 * η ^ 5) = ω_inv * η ^ 5 := by ring
      _ = (ω₀ ^ 4 * ω_inv ^ 5) * η ^ 5 := by rw [h4]
      _ = ω₀ ^ 4 * (ω_inv * η) ^ 5 := by ring
  · refine ⟨0, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 1 * η ^ 5) = (ω₀ * ω_inv) * η ^ 5 := by ring
      _ = ω₀ ^ 0 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨1, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 2 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 1 * η ^ 5) := by ring
      _ = ω₀ ^ 1 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨2, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 3 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 2 * η ^ 5) := by ring
      _ = ω₀ ^ 2 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨3, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 4 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 3 * η ^ 5) := by ring
      _ = ω₀ ^ 3 * η ^ 5 := by rw [ω₀_mul_inv]; ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma unit_form_aux : ∀ n : ℕ, ∀ u : R, u.re.natAbs + u.im.natAbs = n →
    (u.norm = 1 ∨ u.norm = -1) →
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ u = ω₀ ^ r * η ^ 5 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hn hnorm
    set x := u.re
    set y := u.im
    have hu : u = ⟨x, y⟩ := (QuadraticAlgebra.mk_eta u).symm
    have hxy : x * x + 1 * x * y - 1 * y * y = 1 ∨ x * x + 1 * x * y - 1 * y * y = -1 := hnorm
    by_cases hy0 : y = 0
    · rcases hxy with h1 | h1
      · rw [hy0] at h1
        have hx1 : x = 1 ∨ x = -1 := sq_eq_one_iff.mp (by linarith)
        rcases hx1 with hx1 | hx1
        · exact ⟨0, by simp, 1, isUnit_one, by rw [hu, hx1, hy0]; ext <;> simp⟩
        · refine ⟨0, by simp, -1, isUnit_one.neg, ?_⟩
          rw [show (-1 : R) ^ 5 = -1 by ring, hu, hx1, hy0]
          ext <;> simp
      · exfalso
        rw [hy0] at h1
        nlinarith [sq_nonneg x]
    · by_cases hx0 : x = 0
      · rcases hxy with h1 | h1
        · exfalso
          rw [hx0] at h1
          nlinarith [sq_nonneg y]
        · rw [hx0] at h1
          have hy1 : y = 1 ∨ y = -1 := sq_eq_one_iff.mp (by linarith)
          rcases hy1 with hy1 | hy1
          · exact ⟨1, by simp, 1, isUnit_one, by rw [hu, hx0, hy1]; ext <;> simp [ω₀]⟩
          · refine ⟨1, by simp, -1, isUnit_one.neg, ?_⟩
            rw [show (-1 : R) ^ 5 = -1 by ring, hu, hx0, hy1]
            ext <;> simp [ω₀]
      · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos <;>
        rcases lt_or_gt_of_ne hy0 with hyneg | hypos
        · set u' := ω_inv * (-u)
          have hu'_eq : u' = ⟨x - y, -x⟩ := by
            dsimp [u']; rw [hu]; ext
            · simp [ω_inv]; ring
            · simp [ω_inv]
          have hxley : y ≤ x := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hinv_n : ω_inv.norm = -1 := by decide
            rw [map_mul, QuadraticAlgebra.norm_neg, hinv_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_neg (unit_form_mul_ω₀ (ih _ hlt u' rfl hu'_norm))
          have heq : -(ω₀ * u') = u := by
            dsimp [u']
            calc -(ω₀ * (ω_inv * -u)) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω₀ * (-u)
          have hu'_eq : u' = ⟨-y, -x - y⟩ := by
            dsimp [u']; rw [hu]; ext
            · simp [ω₀]
            · simp [ω₀]; ring
          have hy_le : y ≤ -x := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hω_n : ω₀.norm = -1 := by decide
            rw [map_mul, QuadraticAlgebra.norm_neg, hω_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_neg (unit_form_mul_inv (ih _ hlt u' rfl hu'_norm))
          have heq : -(ω_inv * u') = u := by
            dsimp [u']
            calc -(ω_inv * (ω₀ * -u)) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω₀ * u
          have hu'_eq : u' = ⟨y, x + y⟩ := by
            dsimp [u']; rw [hu]; ext <;> simp [ω₀]
          have hxy_ge : 0 ≤ x + y := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hω_n : ω₀.norm = -1 := by decide
            rw [map_mul, hω_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_mul_inv (ih _ hlt u' rfl hu'_norm)
          have heq : ω_inv * u' = u := by
            dsimp [u']
            calc ω_inv * (ω₀ * u) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω_inv * u
          have hu'_eq : u' = ⟨-x + y, x⟩ := by
            dsimp [u']; rw [hu]; ext <;> simp [ω_inv]
          have hxley : x ≤ y := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hinv_n : ω_inv.norm = -1 := by decide
            rw [map_mul, hinv_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_mul_ω₀ (ih _ hlt u' rfl hu'_norm)
          have heq : ω₀ * u' = u := by
            dsimp [u']
            calc ω₀ * (ω_inv * u) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma unit_form (u : R) (hu : IsUnit u) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ u = ω₀ ^ r * η ^ 5 := by
  have hn : IsUnit u.norm := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
  exact unit_form_aux _ u rfl (Int.isUnit_iff.mp hn)

/- ## Section 2: Dirichlet's 1825 Lemma and Second-Case Infinite Descent -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma mk_pow5 (c d : ℤ) :
    (⟨c, d⟩ : R) ^ 5 =
      ⟨c ^ 5 + 10 * c ^ 3 * d ^ 2 + 10 * c ^ 2 * d ^ 3 + 10 * c * d ^ 4 + 3 * d ^ 5,
       5 * d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4)⟩ := by
  ext <;> simp [pow_succ, pow_zero] <;> ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime n 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨1, -k, by ring⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma zmod2_im_zero : ∀ c d : ZMod 2,
    d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4) = 0 → d = 0 := by
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem dirichlet_lemma {P Q w : ℤ} (hcop : IsCoprime P Q) (h5P : ¬ (5 : ℤ) ∣ P)
    (h5Q : (5 : ℤ) ∣ Q) (hpar : Odd (P + Q)) (hw : P ^ 2 - 5 * Q ^ 2 = w ^ 5) :
    ∃ a b : ℤ, P = a * (a ^ 4 + 50 * a ^ 2 * b ^ 2 + 125 * b ^ 4) ∧
      Q = 5 * b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) := by
  set ρ : R := ⟨P - Q, 2 * Q⟩
  set ρ' : R := star ρ
  have hprod : ρ * ρ' = (w : R) ^ 5 := by
    have hnorm : ρ.norm = P ^ 2 - 5 * Q ^ 2 := by
      simp only [QuadraticAlgebra.norm_def, ρ]
      ring
    calc ρ * ρ' = algebraMap ℤ R ρ.norm := (algebraMap_norm_eq_mul_star ρ).symm
      _ = algebraMap ℤ R (w ^ 5) := by rw [hnorm, hw]
      _ = (w : R) ^ 5 := by simp
  have hcop_ρ : IsCoprime ρ ρ' := by
    have hP5 : IsCoprime P 5 := isCoprime_five_of_not_dvd h5P
    have hA : IsCoprime (P ^ 2 - 5 * Q ^ 2) P := by
      have h1 : IsCoprime (5 * Q ^ 2) P := (hP5.symm.mul_left hcop.symm.pow_left)
      have h2 : IsCoprime (-(5 * Q ^ 2)) P := h1.neg_left
      have he : P ^ 2 - 5 * Q ^ 2 = -(5 * Q ^ 2) + P * P := by ring
      rw [he]
      exact h2.add_mul_left_left P
    have hB : IsCoprime (P ^ 2 - 5 * Q ^ 2) 2 := by
      apply isCoprime_two_of_odd
      obtain ⟨k, hk⟩ := hpar
      refine ⟨2 * k ^ 2 + 2 * k - 2 * k * Q - Q - 2 * Q ^ 2, ?_⟩
      have hP : P = 2 * k + 1 - Q := by omega
      rw [hP]; ring
    obtain ⟨A, B, hAB⟩ := hA.mul_right hB
    refine ⟨(A : R) * ρ' + B, B, ?_⟩
    have h1 : ((A * (P ^ 2 - 5 * Q ^ 2) + B * (P * 2) : ℤ) : R) = 1 := by
      rw [hAB]; simp
    have hsum : ρ + ρ' = ((P * 2 : ℤ) : R) := by
      ext
      · simp [ρ, ρ']; ring
      · simp [ρ, ρ']
    have hmul : ρ * ρ' = ((P ^ 2 - 5 * Q ^ 2 : ℤ) : R) := by
      rw [hprod, hw]; push_cast; rfl
    calc ((A : R) * ρ' + B) * ρ + (B : R) * ρ'
        = (A : R) * (ρ * ρ') + (B : R) * (ρ + ρ') := by ring
      _ = ((A * (P ^ 2 - 5 * Q ^ 2) + B * (P * 2) : ℤ) : R) := by
          rw [hmul, hsum]; push_cast; ring
      _ = 1 := h1
  obtain ⟨γ0, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop_ρ hprod
  obtain ⟨r, hr, η, -, hη⟩ := unit_form (u0 : R) u0.isUnit
  set γ : R := γ0 * η
  have hρ : ρ = ω₀ ^ r * γ ^ 5 := by
    calc ρ = γ0 ^ 5 * (u0 : R) := hu0.symm
      _ = γ0 ^ 5 * (ω₀ ^ r * η ^ 5) := by rw [hη]
      _ = ω₀ ^ r * γ ^ 5 := by dsimp [γ]; ring
  set c := γ.re
  set d := γ.im
  have hγ_mk : γ = ⟨c, d⟩ := (QuadraticAlgebra.mk_eta γ).symm
  set X5 := c ^ 5 + 10 * c ^ 3 * d ^ 2 + 10 * c ^ 2 * d ^ 3 + 10 * c * d ^ 4 + 3 * d ^ 5
  set Y5 := d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4)
  have hγ5 : γ ^ 5 = ⟨X5, 5 * Y5⟩ := by
    rw [hγ_mk, mk_pow5]
    dsimp [X5, Y5]
    ext
    · simp
    · simp; ring
  rw [hγ5] at hρ
  obtain ⟨Q', rfl⟩ := h5Q
  have h5_not_re : ¬ (5 : ℤ) ∣ (P - 5 * Q') := by
    intro hd
    exact h5P (by obtain ⟨m, hm⟩ := hd; exact ⟨m + Q', by omega⟩)
  rw [Finset.mem_range] at hr
  have hr0 : r = 0 := by
    interval_cases r
    · rfl
    · exfalso
      have hre : P - 5 * Q' = 5 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀] at this; linarith
      exact h5_not_re ⟨Y5, hre⟩
    · exfalso
      have hre : P - 5 * Q' = X5 + 5 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_two] at this; linarith
      have him : 10 * Q' = X5 + 10 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_two] at this; linarith
      exact h5_not_re ⟨2 * Q' - Y5, by omega⟩
    · exfalso
      have hre : P - 5 * Q' = X5 + 10 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have him : 10 * Q' = 2 * X5 + 15 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have h5X : (5 : ℤ) ∣ 2 * X5 := ⟨2 * Q' - 3 * Y5, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h5X with h2 | hX
      · norm_num at h2
      · obtain ⟨k, hk⟩ := hX
        exact h5_not_re ⟨k + 2 * Y5, by omega⟩
    · exfalso
      have hre : P - 5 * Q' = 2 * X5 + 15 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have him : 10 * Q' = 3 * X5 + 25 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have h5X : (5 : ℤ) ∣ 3 * X5 := ⟨2 * Q' - 5 * Y5, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h5X with h3 | hX
      · norm_num at h3
      · obtain ⟨k, hk⟩ := hX
        exact h5_not_re ⟨2 * k + 3 * Y5, by omega⟩
  subst hr0
  simp only [pow_zero, one_mul] at hρ
  have hre : P - 5 * Q' = X5 := congr_arg QuadraticAlgebra.re hρ
  have him : 2 * Q' = Y5 := by
    have := congr_arg QuadraticAlgebra.im hρ
    simp only [ρ] at this
    omega
  have hd_dvd : (2 : ℤ) ∣ d := by
    change ((2 : ℕ) : ℤ) ∣ d
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply zmod2_im_zero (c : ZMod 2) (d : ZMod 2)
    have hY2 : (Y5 : ZMod 2) = 0 := by
      rw [← him]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
    dsimp [Y5] at hY2
    push_cast at hY2
    exact hY2
  obtain ⟨b, hb⟩ := hd_dvd
  refine ⟨c + b, b, ?_, ?_⟩
  · have hX_eq : 2 * X5 + 5 * Y5 =
        2 * ((c + b) * ((c + b) ^ 4 + 50 * (c + b) ^ 2 * b ^ 2 + 125 * b ^ 4)) := by
      dsimp [X5, Y5]; rw [hb]; ring
    linarith [hre, him, hX_eq]
  · have hY_eq : Y5 = 2 * b * ((c + b) ^ 4 + 10 * (c + b) ^ 2 * b ^ 2 + 5 * b ^ 4) := by
      dsimp [Y5]; rw [hb]; ring
    linarith [him, hY_eq]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma pow5_of_coprime_int {a b c : ℤ} (h : IsCoprime a b) (habc : a * b = c ^ 5) :
    ∃ d : ℤ, a = d ^ 5 :=
  Int.eq_pow_of_mul_eq_pow_odd_left h (by decide) habc

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_add_of_odd_PQ5 {a b : ℤ}
    (h : Odd (a * (a ^ 4 + 50 * a ^ 2 * b ^ 2 + 125 * b ^ 4) +
      5 * b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4))) : Odd (a + b) := by
  rw [odd_iff_zmod2] at h ⊢
  push_cast at h ⊢
  revert h
  generalize (a : ZMod 2) = x, (b : ZMod 2) = y
  revert x y; decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def Eq2 (a b Z : ℤ) (M N : ℕ) : Prop :=
  1 ≤ M ∧ 1 ≤ N ∧ IsCoprime a b ∧ Odd (a + b) ∧ ¬ (5 : ℤ) ∣ a ∧ b ≠ 0 ∧ IsCoprime Z 10 ∧
    b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) = 2 ^ M * 5 ^ N * Z ^ 5

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem no_eq2_aux : ∀ n : ℕ, ∀ a b Z : ℤ, ∀ M N : ℕ, b.natAbs = n → Eq2 a b Z M N → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b Z M N hn ⟨hM, hN, hcop, hodd, h5a, hb0, hZ10, heq⟩
    set Q := a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4
    have hQ_odd : Odd Q := by
      rw [odd_iff_zmod2] at hodd ⊢
      dsimp [Q]
      push_cast at hodd ⊢
      revert hodd
      generalize (a : ZMod 2) = x, (b : ZMod 2) = y
      revert x y; decide
    have h5Q : ¬ (5 : ℤ) ∣ Q := by
      intro hd
      have h5a4 : (5 : ℤ) ∣ a ^ 4 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨k - 2 * a ^ 2 * b ^ 2 - b ^ 4, by dsimp [Q] at hk; linarith⟩
      exact h5a (Int.Prime.dvd_pow' Nat.prime_five h5a4)
    have hQ2 : IsCoprime Q 2 := isCoprime_two_of_odd hQ_odd
    have hQ5 : IsCoprime Q 5 := isCoprime_five_of_not_dvd h5Q
    have hQ_25 : IsCoprime Q (2 ^ M * 5 ^ N) := hQ2.pow_right.mul_right hQ5.pow_right
    have hdvd_b : (2 ^ M * 5 ^ N : ℤ) ∣ b := by
      refine hQ_25.symm.dvd_of_dvd_mul_right ?_
      exact ⟨Z ^ 5, heq⟩
    obtain ⟨b', hb'⟩ := hdvd_b
    have h25_ne : (2 ^ M * 5 ^ N : ℤ) ≠ 0 := by positivity
    have heq' : b' * Q = Z ^ 5 := by
      apply mul_left_cancel₀ h25_ne
      calc 2 ^ M * 5 ^ N * (b' * Q) = (2 ^ M * 5 ^ N * b') * Q := by ring
        _ = b * Q := by rw [← hb']
        _ = 2 ^ M * 5 ^ N * Z ^ 5 := heq
    have hbQ : IsCoprime b Q := by
      have hba4 : IsCoprime b (a ^ 4) := hcop.symm.pow_right
      have he : Q = a ^ 4 + b * (10 * a ^ 2 * b + 5 * b ^ 3) := by dsimp [Q]; ring
      rw [he]
      exact hba4.add_mul_left_right _
    have hb'Q : IsCoprime b' Q := by
      rw [hb'] at hbQ
      exact hbQ.of_mul_left_right
    obtain ⟨c, hc⟩ := pow5_of_coprime_int hb'Q heq'
    obtain ⟨d, hd⟩ := pow5_of_coprime_int hb'Q.symm (by rw [mul_comm]; exact heq')
    have hb_eq : b = 2 ^ M * 5 ^ N * c ^ 5 := by rw [hb', hc]
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hb0; rw [hb_eq]; ring
    have hc10 : IsCoprime (c ^ 2) 10 := by
      have hZ5_10 : IsCoprime (Z ^ 5) 10 := hZ10.pow_left
      rw [← heq', hc] at hZ5_10
      obtain ⟨u1, u2, hu12⟩ := hZ5_10.of_mul_left_left
      have hc_10 : IsCoprime c 10 := ⟨u1 * c ^ 4, u2, by linear_combination hu12⟩
      exact hc_10.pow_left
    have h5b : (5 : ℤ) ∣ b := by
      refine ⟨2 ^ M * 5 ^ (N - 1) * c ^ 5, ?_⟩
      rw [hb_eq]
      have hN' : 5 ^ N = (5 : ℤ) * 5 ^ (N - 1) := by
        conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ']
      rw [hN']; ring
    have h2b : Even b := by
      refine ⟨2 ^ (M - 1) * 5 ^ N * c ^ 5, ?_⟩
      rw [hb_eq]
      have hM' : 2 ^ M = (2 : ℤ) * 2 ^ (M - 1) := by
        conv_lhs => rw [show M = (M - 1) + 1 by omega, pow_succ']
      rw [hM']; ring
    set P1 := a ^ 2 + 5 * b ^ 2
    set R1 := 2 * b ^ 2
    have hPR_odd : Odd (P1 + R1) := by
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨m, hm⟩ := h2b
      refine ⟨2 * (k - m) ^ 2 + 2 * (k - m) + 14 * m ^ 2, ?_⟩
      have ha : a = 2 * (k - m) + 1 := by omega
      dsimp [P1, R1]; rw [ha, hm]; ring
    have h5P1 : ¬ (5 : ℤ) ∣ P1 := by
      intro hd
      have h5a2 : (5 : ℤ) ∣ a ^ 2 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨k - b ^ 2, by dsimp [P1] at hk; linarith⟩
      exact h5a (five_dvd_of_sq_dvd h5a2)
    have h5R1 : (5 : ℤ) ∣ R1 := by
      obtain ⟨k, hk⟩ := h5b
      exact ⟨10 * k ^ 2, by dsimp [R1]; rw [hk]; ring⟩
    have hcop_PR : IsCoprime P1 R1 := by
      have hP1_b : IsCoprime P1 b := by
        have he : P1 = a ^ 2 + b * (5 * b) := by dsimp [P1]; ring
        rw [he]
        exact hcop.pow_left.add_mul_left_left _
      have hP1_2 : IsCoprime P1 2 := by
        apply isCoprime_two_of_odd
        obtain ⟨k, hk⟩ := hPR_odd
        exact ⟨k - b ^ 2, by dsimp [R1] at hk; omega⟩
      exact hP1_2.mul_right hP1_b.pow_right
    have hd5 : P1 ^ 2 - 5 * R1 ^ 2 = d ^ 5 := by
      have he : P1 ^ 2 - 5 * R1 ^ 2 = Q := by dsimp [P1, R1, Q]; ring
      rw [he, hd]
    obtain ⟨a1, b1, ha1, hb1⟩ := dirichlet_lemma hcop_PR h5P1 h5R1 hPR_odd hd5
    have hcop1 : IsCoprime a1 b1 := by
      have h := hcop_PR
      rw [ha1, hb1] at h
      exact h.of_mul_left_left.of_mul_right_left.of_mul_right_right
    have hodd1 : Odd (a1 + b1) := by
      apply odd_add_of_odd_PQ5
      rw [← ha1, ← hb1]
      exact hPR_odd
    have h5a1 : ¬ (5 : ℤ) ∣ a1 := by
      intro hd
      exact h5P1 (ha1 ▸ dvd_mul_of_dvd_left hd _)
    have ha1_ne : a1 ≠ 0 := fun h0 => h5a1 (by simp [h0])
    set Q1 := a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4
    have hQ1_pos : 1 ≤ Q1 := by
      have : 0 < a1 ^ 2 := sq_pos_of_ne_zero ha1_ne
      have : 1 ≤ a1 ^ 4 := by nlinarith
      dsimp [Q1]
      nlinarith [sq_nonneg (a1 * b1), sq_nonneg (b1 ^ 2)]
    have hb1_pos : 0 < b1 := by
      have hR1_pos : 0 < R1 := by dsimp [R1]; positivity
      rw [hb1] at hR1_pos
      nlinarith
    have hb1_lt : b1.natAbs < n := by
      have hb1_2 : b1 ^ 2 ≤ b1 ^ 4 := by nlinarith [sq_nonneg (b1 - 1)]
      have h5b1_sq : 5 * b1 ^ 2 ≤ 2 * b ^ 2 := by
        have h1 : b1 ≤ Q1 := by dsimp [Q1]; nlinarith
        have h2 : 5 * b1 ^ 2 ≤ 5 * b1 * Q1 := by nlinarith
        linarith [hb1]
      have hbsq : b1 ^ 2 < b ^ 2 := by nlinarith
      have hlt_abs : |b1| < |b| := by
        rw [← sq_lt_sq]
        exact hbsq
      rw [← hn, ← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs]
      exact hlt_abs
    have heq1 : b1 * Q1 = 2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5 := by
      have h5pow : (5 : ℤ) ^ (2 * N) = 5 * 5 ^ (2 * N - 1) := by
        conv_lhs => rw [show 2 * N = (2 * N - 1) + 1 by omega, pow_succ']
      have hR : 5 * (b1 * Q1) = 5 * (2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5) := by
        calc 5 * (b1 * Q1) = R1 := by dsimp [Q1]; linarith [hb1]
          _ = 2 * (2 ^ M * 5 ^ N * c ^ 5) ^ 2 := by dsimp [R1]; rw [hb_eq]
          _ = 2 * 2 ^ (2 * M) * 5 ^ (2 * N) * (c ^ 2) ^ 5 := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
              ring_nf
          _ = 5 * (2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5) := by
              rw [h5pow, pow_succ]; ring
      linarith
    exact ih _ hb1_lt a1 b1 (c ^ 2) (2 * M + 1) (2 * N - 1) rfl
      ⟨by omega, by omega, hcop1, hodd1, h5a1, hb1_pos.ne', hc10, heq1⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem no_sol_case2 {x y Z : ℤ} {m n : ℕ} (hm : 1 ≤ m) (hn : 3 ≤ n)
    (hcop : IsCoprime x y) (hZ10 : IsCoprime Z 10) (hZ0 : Z ≠ 0) :
    x ^ 5 + y ^ 5 ≠ 2 ^ m * 5 ^ n * Z ^ 5 := by
  intro h
  have hxy_even : Even (x + y) := by
    have hm' : 2 ^ m = (2 : ℤ) * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    have h2 : Even (x ^ 5 + y ^ 5) := ⟨2 ^ (m - 1) * 5 ^ n * Z ^ 5, by rw [h, hm']; ring⟩
    rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at h2
    rwa [Int.even_add]
  obtain ⟨u, hu⟩ := hxy_even
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := by obtain ⟨r, hr⟩ := hx; exact ⟨u - r, by omega⟩
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
      have hd : (2 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hx.two_dvd hy.two_dvd
      rw [hg] at hd; norm_num at hd
    · exact hx
  set v := x - u
  have hx' : x = u + v := by omega
  have hy' : y = u - v := by omega
  have hpar : Odd (u + v) := hx' ▸ hxodd
  have huv : IsCoprime u v := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx', hy']; ring⟩
  have h5_xy : (5 : ℤ) ∣ (x + y) := by
    have hn' : 5 ^ n = (5 : ℤ) * 5 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
    have h5_pow : (5 : ℤ) ∣ (x + y) ^ 5 := by
      refine ⟨2 ^ m * 5 ^ (n - 1) * Z ^ 5 + x * y * (x + y) * (x ^ 2 + x * y + y ^ 2), ?_⟩
      calc (x + y) ^ 5 = (x ^ 5 + y ^ 5) + 5 * (x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by ring
        _ = 2 ^ m * 5 ^ n * Z ^ 5 + 5 * (x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by rw [h]
        _ = 5 * (2 ^ m * 5 ^ (n - 1) * Z ^ 5 + x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by
            rw [hn']; ring
    exact Int.Prime.dvd_pow' Nat.prime_five h5_pow
  have h5u : (5 : ℤ) ∣ u := by
    have h2u : (5 : ℤ) ∣ 2 * u := by rwa [show 2 * u = x + y by omega]
    rcases Int.Prime.dvd_mul' Nat.prime_five h2u with h2 | h5
    · norm_num at h2
    · exact h5
  obtain ⟨U, rfl⟩ := h5u
  have h5v : ¬ (5 : ℤ) ∣ v := by
    intro hd
    exact not_isUnit_five (huv.isUnit_of_dvd' (dvd_mul_right 5 U) hd)
  have hUv : IsCoprime U v := huv.of_mul_left_right
  have hU_odd : Odd (U + v) := by
    obtain ⟨k, hk⟩ := hpar
    exact ⟨k - 2 * U, by omega⟩
  set Q' := v ^ 4 + 50 * U ^ 2 * v ^ 2 + 125 * U ^ 4
  have heqU : U * Q' = 2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5 := by
    have hm' : 2 ^ m = (2 : ℤ) * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    have hn' : (5 : ℤ) ^ n = 25 * 5 ^ (n - 2) := by
      calc (5 : ℤ) ^ n = 5 ^ ((n - 2) + 2) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 25 * 5 ^ (n - 2) := by rw [pow_add]; ring
    have h50 : 50 * (U * Q') = 50 * (2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5) := by
      calc 50 * (U * Q') = (5 * U + v) ^ 5 + (5 * U - v) ^ 5 := by dsimp [Q']; ring
        _ = x ^ 5 + y ^ 5 := by rw [← hx', ← hy']
        _ = 2 ^ m * 5 ^ n * Z ^ 5 := h
        _ = 50 * (2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5) := by rw [hm', hn']; ring
    linarith
  have hQ'_odd : Odd Q' := by
    rw [odd_iff_zmod2] at hU_odd ⊢
    dsimp [Q']
    push_cast at hU_odd ⊢
    revert hU_odd
    generalize (U : ZMod 2) = x1, (v : ZMod 2) = y1
    revert x1 y1; decide
  have h5Q' : ¬ (5 : ℤ) ∣ Q' := by
    intro hd
    have h5v4 : (5 : ℤ) ∣ v ^ 4 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 10 * U ^ 2 * v ^ 2 - 25 * U ^ 4, by dsimp [Q'] at hk; linarith⟩
    exact h5v (Int.Prime.dvd_pow' Nat.prime_five h5v4)
  have hQ'2 : IsCoprime Q' 2 := isCoprime_two_of_odd hQ'_odd
  have hQ'5 : IsCoprime Q' 5 := isCoprime_five_of_not_dvd h5Q'
  have hQ'_25 : IsCoprime Q' (2 ^ (m - 1) * 5 ^ (n - 2)) := hQ'2.pow_right.mul_right hQ'5.pow_right
  have hdvd_U : (2 ^ (m - 1) * 5 ^ (n - 2) : ℤ) ∣ U := by
    refine hQ'_25.symm.dvd_of_dvd_mul_right ?_
    exact ⟨Z ^ 5, heqU⟩
  obtain ⟨U', hU'⟩ := hdvd_U
  have h25_ne : (2 ^ (m - 1) * 5 ^ (n - 2) : ℤ) ≠ 0 := by positivity
  have heqU' : U' * Q' = Z ^ 5 := by
    apply mul_left_cancel₀ h25_ne
    calc 2 ^ (m - 1) * 5 ^ (n - 2) * (U' * Q') = U * Q' := by rw [hU']; ring
      _ = 2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5 := heqU
  have hUQ' : IsCoprime U Q' := by
    have he : Q' = v ^ 4 + U * (50 * U * v ^ 2 + 125 * U ^ 3) := by dsimp [Q']; ring
    rw [he]
    exact hUv.pow_right.add_mul_left_right _
  have hU'Q' : IsCoprime U' Q' := by
    rw [hU'] at hUQ'
    exact hUQ'.of_mul_left_right
  obtain ⟨t, ht⟩ := pow5_of_coprime_int hU'Q' heqU'
  obtain ⟨w, hw⟩ := pow5_of_coprime_int hU'Q'.symm (by rw [mul_comm]; exact heqU')
  have hU_eq : U = 2 ^ (m - 1) * 5 ^ (n - 2) * t ^ 5 := by rw [hU', ht]
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hZ0
    rw [ht, zero_pow (by norm_num), zero_mul] at heqU'
    exact pow_eq_zero_iff (by norm_num) |>.mp heqU'.symm
  have ht10 : IsCoprime (t ^ 2) 10 := by
    have hZ5_10 : IsCoprime (Z ^ 5) 10 := hZ10.pow_left
    rw [← heqU', ht] at hZ5_10
    obtain ⟨u1, u2, hu12⟩ := hZ5_10.of_mul_left_left
    have ht_10 : IsCoprime t 10 := ⟨u1 * t ^ 4, u2, by linear_combination hu12⟩
    exact ht_10.pow_left
  set P2 := v ^ 2 + 25 * U ^ 2
  set R2 := 10 * U ^ 2
  have hPR2_odd : Odd (P2 + R2) := by
    obtain ⟨k, hk⟩ := hU_odd
    rcases Int.even_or_odd U with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hv' : v = 2 * (k - j) + 1 := by omega
      exact ⟨2 * (k - j) ^ 2 + 2 * (k - j) + 70 * j ^ 2, by dsimp [P2, R2]; rw [hj, hv']; ring⟩
    · have hv' : v = 2 * (k - j) := by omega
      exact ⟨2 * (k - j) ^ 2 + 70 * j ^ 2 + 70 * j + 17, by dsimp [P2, R2]; rw [hj, hv']; ring⟩
  have h5P2 : ¬ (5 : ℤ) ∣ P2 := by
    intro hd
    have h5v2 : (5 : ℤ) ∣ v ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 5 * U ^ 2, by dsimp [P2] at hk; linarith⟩
    exact h5v (five_dvd_of_sq_dvd h5v2)
  have h5R2 : (5 : ℤ) ∣ R2 := ⟨2 * U ^ 2, by dsimp [R2]; ring⟩
  have hcop_PR2 : IsCoprime P2 R2 := by
    have hP2_U : IsCoprime P2 U := by
      have he : P2 = v ^ 2 + U * (25 * U) := by dsimp [P2]; ring
      rw [he]
      exact hUv.symm.pow_left.add_mul_left_left _
    have hP2_2 : IsCoprime P2 2 := by
      apply isCoprime_two_of_odd
      obtain ⟨k, hk⟩ := hPR2_odd
      exact ⟨k - 5 * U ^ 2, by dsimp [R2] at hk; omega⟩
    have hP2_5 : IsCoprime P2 5 := isCoprime_five_of_not_dvd h5P2
    have h10 : R2 = (2 * 5) * U ^ 2 := by ring
    rw [h10]
    exact (hP2_2.mul_right hP2_5).mul_right hP2_U.pow_right
  have hw5 : P2 ^ 2 - 5 * R2 ^ 2 = w ^ 5 := by
    have he : P2 ^ 2 - 5 * R2 ^ 2 = Q' := by dsimp [P2, R2, Q']; ring
    rw [he, hw]
  obtain ⟨a1, b1, ha1, hb1⟩ := dirichlet_lemma hcop_PR2 h5P2 h5R2 hPR2_odd hw5
  have hcop1 : IsCoprime a1 b1 := by
    have hc := hcop_PR2
    rw [ha1, hb1] at hc
    exact hc.of_mul_left_left.of_mul_right_left.of_mul_right_right
  have hodd1 : Odd (a1 + b1) := by
    apply odd_add_of_odd_PQ5
    rw [← ha1, ← hb1]
    exact hPR2_odd
  have h5a1 : ¬ (5 : ℤ) ∣ a1 := fun hd => h5P2 (ha1 ▸ dvd_mul_of_dvd_left hd _)
  have hU0 : U ≠ 0 := by
    rw [hU_eq]
    exact mul_ne_zero (by positivity) (pow_ne_zero 5 ht0)
  have hb1_ne : b1 ≠ 0 := by
    rintro rfl
    have hR0 : R2 = 0 := by rw [hb1]; ring
    dsimp [R2] at hR0
    exact hU0 (by nlinarith)
  have heq1 : b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4) =
      2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5 := by
    have h2pow : 2 * (2 : ℤ) ^ (2 * (m - 1)) = 2 ^ (2 * m - 1) := by
      conv_rhs => rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, pow_succ']
    have h5R : 5 * (b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4)) =
        5 * (2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by
      calc 5 * (b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4)) = R2 := by linarith [hb1]
        _ = 10 * (2 ^ (m - 1) * 5 ^ (n - 2) * t ^ 5) ^ 2 := by dsimp [R2]; rw [hU_eq]
        _ = 5 * ((2 * 2 ^ (2 * (m - 1))) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by
            rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
            ring_nf
        _ = 5 * (2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by rw [h2pow]
    linarith
  exact no_eq2_aux _ a1 b1 (t ^ 2) (2 * m - 1) (2 * (n - 2)) rfl
    ⟨by omega, by omega, hcop1, hodd1, h5a1, hb1_ne, ht10, heq1⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma strip_two_five : ∀ n : ℕ, ∀ B : ℤ, B.natAbs = n → B ≠ 0 →
    ∃ a c : ℕ, ∃ B0 : ℤ, B0 ≠ 0 ∧ IsCoprime B0 10 ∧ B = 2 ^ a * 5 ^ c * B0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hn hB0
    by_cases h2 : (2 : ℤ) ∣ B
    · obtain ⟨B', rfl⟩ := h2
      have hB'0 : B' ≠ 0 := fun h0 => hB0 (by simp [h0])
      have hlt : B'.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have : 0 < B'.natAbs := Int.natAbs_pos.mpr hB'0
        have h2a : (2 : ℤ).natAbs = 2 := rfl
        rw [h2a]
        omega
      obtain ⟨a, c, B0, h0, hcop, hB'⟩ := ih _ hlt B' rfl hB'0
      exact ⟨a + 1, c, B0, h0, hcop, by rw [hB', pow_succ]; ring⟩
    · by_cases h5 : (5 : ℤ) ∣ B
      · obtain ⟨B', rfl⟩ := h5
        have hB'0 : B' ≠ 0 := fun h0 => hB0 (by simp [h0])
        have hlt : B'.natAbs < n := by
          rw [← hn, Int.natAbs_mul]
          have : 0 < B'.natAbs := Int.natAbs_pos.mpr hB'0
          have h5a : (5 : ℤ).natAbs = 5 := rfl
          rw [h5a]
          omega
        obtain ⟨a, c, B0, h0, hcop, hB'⟩ := ih _ hlt B' rfl hB'0
        exact ⟨a, c + 1, B0, h0, hcop, by rw [hB', pow_succ]; ring⟩
      · refine ⟨0, 0, B, hB0, ?_, by simp⟩
        have hc2 : IsCoprime B 2 := (Prime.coprime_iff_not_dvd Int.prime_two).mpr h2 |>.symm
        have hc5 : IsCoprime B 5 := isCoprime_five_of_not_dvd h5
        simpa using hc2.mul_right hc5


end OMA672H2_H1


/- Component: Necessary.lean -/

/-
Elementary residue constraints for the fifth-power arithmetic-progression equation.
Work by Hanan Beer (@hananzlt). This is partial supporting work, not a proof of the target.
The modulo-25 split follows the classical approach of V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵ + y⁵ = az⁵.
-/


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem pow5_residue (a : Fin 25) :
    a.val ^ 5 % 25 = (a.val % 5) ^ 5 % 25 := by
  fin_cases a <;> norm_num

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem mod25_fifth_fin (a b c : Fin 5)
    (h : (a.val ^ 5 + b.val ^ 5) % 25 = (2 * c.val ^ 5) % 25) :
    (a.val = b.val ∧ a.val = c.val) ∨
    ((a.val + b.val) % 5 = 0 ∧ c.val = 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num at *

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem mod25_fifth (a b c : Fin 25)
    (h : (a.val ^ 5 + b.val ^ 5) % 25 = (2 * c.val ^ 5) % 25) :
    (a.val % 5 = b.val % 5 ∧ a.val % 5 = c.val % 5) ∨
    ((a.val + b.val) % 5 = 0 ∧ c.val % 5 = 0) := by
  rw [Nat.add_mod, Nat.mul_mod, pow5_residue a, pow5_residue b, pow5_residue c,
    ← Nat.add_mod, ← Nat.mul_mod] at h
  let a' : Fin 5 := ⟨a.val % 5, Nat.mod_lt _ (by decide)⟩
  let b' : Fin 5 := ⟨b.val % 5, Nat.mod_lt _ (by decide)⟩
  let c' : Fin 5 := ⟨c.val % 5, Nat.mod_lt _ (by decide)⟩
  simpa [a', b', c', Nat.add_mod] using mod25_fifth_fin a' b' c' h


/- A necessary congruence for the target equation; this is not sufficient for the target. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem fifth_ap_mod_five (x y z : ℤ) (h : x ^ 5 + y ^ 5 = 2 * z ^ 5) :
    (x % 5 = y % 5 ∧ x % 5 = z % 5) ∨ ((x + y) % 5 = 0 ∧ z % 5 = 0) := by
  let f (t : ℤ) : Fin 25 := ⟨(t % 25).toNat, by omega⟩
  have hf (t : ℤ) : ((f t).val : ℤ) = t % 25 := by
    dsimp [f]
    omega
  have hmod : ((x % 25) ^ 5 + (y % 25) ^ 5) % 25 = (2 * (z % 25) ^ 5) % 25 := by
    have hr (t : ℤ) : Int.ModEq 25 (t % 25) t := by
      show (t % 25) % 25 = t % 25
      exact Int.emod_emod t 25
    have hl := ((hr x).pow 5).add ((hr y).pow 5)
    have hz := ((hr z).pow 5).mul_left 2
    exact hl.eq.trans ((congrArg (fun t => t % 25) h).trans hz.eq.symm)
  have hnat : ((f x).val ^ 5 + (f y).val ^ 5) % 25 = (2 * (f z).val ^ 5) % 25 := by
    zify
    simpa only [hf] using hmod
  have hlift (t : ℤ) : (((f t).val % 5 : ℕ) : ℤ) = t % 5 := by
    push_cast
    rw [hf]
    omega
  rcases mod25_fifth (f x) (f y) (f z) hnat with ⟨hxy, hxz⟩ | ⟨hxy, hz⟩
  · left
    constructor
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hxy
      simpa only [hlift] using hh
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hxz
      simpa only [hlift] using hh
  · right
    constructor
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hxy
      push_cast at hh
      rw [hf, hf] at hh
      omega
    · have hh := congrArg (fun n : ℕ => (n : ℤ)) hz
      simpa only [hlift, Int.natCast_zero] using hh


/- Component: Primitive5.lean -/

/-
Primitive branch reductions for the exact fifth-power arithmetic-progression target.
New work by Hanan Beer (@hananzlt). The imported Dirichlet descent is by
Pedro Bessa (@nijv), PR5575 at head572ffd235e0a734035a1737d90d28c37c24417ee;
see Dirichlet.lean for source and mathematical attribution.
This file is supporting material, not a completed exact target proof.
-/

namespace OblathH1
open OMA672H2_H1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_five_not_dvd {x y z : ℤ} (hcop : IsCoprime x y)
    (hz : z ≠ 0) (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : ¬ (5 : ℤ) ∣ z := by
  intro h5z
  obtain ⟨a, c, Z, hZ0, hZ10, hz_eq⟩ := strip_two_five _ z rfl hz
  have hc : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · exfalso
      simp only [pow_zero, mul_one] at hz_eq
      rw [hz_eq] at h5z
      have h25 : IsCoprime (2 : ℤ) 5 := ⟨-2, 1, by ring⟩
      have h5Z : (5 : ℤ) ∣ Z := h25.pow_left.symm.dvd_of_dvd_mul_left h5z
      have hZ5 : IsCoprime Z 5 := by
        rw [show (10 : ℤ) = 2 * 5 by norm_num] at hZ10
        exact hZ10.of_mul_right_right
      exact not_isUnit_five (hZ5.isUnit_of_dvd' h5Z dvd_rfl)
    · exact hc
  apply no_sol_case2 (x := x) (y := y) (Z := Z) (m := 5 * a + 1) (n := 5 * c)
    (by omega) (by omega) hcop hZ10 hZ0
  calc x ^ 5 + y ^ 5 = 2 * z ^ 5 := heq
    _ = 2 * (2 ^ a * 5 ^ c * Z) ^ 5 := by rw [hz_eq]
    _ = 2 ^ (5 * a + 1) * 5 ^ (5 * c) * Z ^ 5 := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a 5,
        Nat.mul_comm c 5, pow_succ]
      ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_five_dvd_sub {x y z : ℤ} (hcop : IsCoprime x y)
    (hz : z ≠ 0) (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : (5 : ℤ) ∣ x - y := by
  have hz5 := primitive_five_not_dvd hcop hz heq
  rcases fifth_ap_mod_five x y z heq with ⟨hxy, -⟩ | ⟨-, hzmod⟩
  · exact Int.dvd_of_emod_eq_zero (by omega)
  · exact False.elim (hz5 (Int.dvd_of_emod_eq_zero hzmod))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_odd_xy {x y z : ℤ} (hcop : IsCoprime x y)
    (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : Odd x ∧ Odd y := by
  have hev : Even (x ^ 5 + y ^ 5) := ⟨z ^ 5, by linarith⟩
  rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at hev
  rcases Int.even_or_odd x with hx | hx
  · have hy : Even y := hev.mp hx
    have h2unit := hcop.isUnit_of_dvd' hx.two_dvd hy.two_dvd
    norm_num [Int.isUnit_iff] at h2unit
  · refine ⟨hx, ?_⟩
    rcases Int.even_or_odd y with hy | hy
    · have hxev : Even x := hev.mpr hy
      exact False.elim (Int.not_even_iff_odd.mpr hx hxev)
    · exact hy

end OblathH1


/- Component: Factor.lean -/

/-
Coprime power-factor extraction for Lebesgue's quartic descent.
New formalization by Hanan Beer (@hananzlt), following V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
This file is supporting work for exact Oblath H1, not a complete solution.
-/

namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_pow_signed {A B C : ℤ} {k : ℕ} (hk : Even k) (hk0 : k ≠ 0)
    (hc : C ≠ 0) (hab : IsCoprime A B) (heq : A * B = C ^ k) :
    ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
      A = ε * u ^ k ∧ B = ε * v ^ k ∧ |C| = |u * v| := by
  obtain ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hab heq
  obtain ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hab.symm
    (show B * A = C ^ k by rw [mul_comm]; exact heq)
  replace hu := hu.symm
  replace hv := hv.symm
  rw [Int.associated_iff_natAbs, Int.natAbs_eq_natAbs_iff] at hu hv
  have hcpos : 0 < C ^ k := lt_of_le_of_ne (hk.pow_nonneg _) (Ne.symm (pow_ne_zero _ hc))
  have hu0 : 0 ≤ u ^ k := hk.pow_nonneg _
  have hv0 : 0 ≤ v ^ k := hk.pow_nonneg _
  have finish (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (ha : A = ε * u ^ k)
      (hb : B = ε * v ^ k) :
      ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
        A = ε * u ^ k ∧ B = ε * v ^ k ∧ |C| = |u * v| := by
    refine ⟨u, v, ε, hε, ?_, ha, hb, ?_⟩
    · have hcuv : IsCoprime (u ^ k) (v ^ k) := by
        rcases hε with rfl | rfl
        · simpa [ha, hb] using hab
        · simpa [ha, hb] using hab.neg_left.neg_right
      exact (IsCoprime.pow_left_iff (Nat.pos_of_ne_zero hk0)).mp
        ((IsCoprime.pow_right_iff (Nat.pos_of_ne_zero hk0)).mp hcuv)
    · have he : C ^ k = (u * v) ^ k := by
        rw [← heq, ha, hb, mul_pow]
        rcases hε with rfl | rfl <;> ring
      apply (pow_left_inj₀ (abs_nonneg C) (abs_nonneg (u * v)) hk0).mp
      rw [hk.pow_abs, hk.pow_abs]
      exact he
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact finish 1 (Or.inl rfl) (by simpa using hu) (by simpa using hv)
  · have hm : A * B ≤ 0 := by rw [hu, hv]; nlinarith
    omega
  · have hm : A * B ≤ 0 := by rw [hu, hv]; nlinarith
    omega
  · exact finish (-1) (Or.inr rfl) (by simpa using hu) (by simpa using hv)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma five_pow_split_left {A B C : ℤ} {r k : ℕ} (hk : Even k) (hk0 : k ≠ 0)
    (hc : C ≠ 0) (hab : IsCoprime A B) (hA5 : ¬ (5 : ℤ) ∣ A)
    (heq : A * B = 5 ^ r * C ^ k) :
    ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
      A = ε * u ^ k ∧ B = ε * 5 ^ r * v ^ k ∧ |C| = |u * v| ∧
      ¬ (5 : ℤ) ∣ u := by
  have h5A : IsCoprime (5 : ℤ) A :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Nat.prime_five)).mpr hA5
  have hdiv : (5 : ℤ) ^ r ∣ B := h5A.pow_left.dvd_of_dvd_mul_left ⟨C ^ k, heq⟩
  obtain ⟨B0, hB⟩ := hdiv
  have hAB0 : A * B0 = C ^ k := by
    apply mul_left_cancel₀ (show (5 : ℤ) ^ r ≠ 0 by positivity)
    calc 5 ^ r * (A * B0) = A * B := by rw [hB]; ring
      _ = 5 ^ r * C ^ k := heq
  have hcop0 : IsCoprime A B0 := by
    rw [hB] at hab
    exact hab.of_mul_right_right
  obtain ⟨u, v, ε, hε, huv, hu, hv, hcuv⟩ := even_pow_signed hk hk0 hc hcop0 hAB0
  refine ⟨u, v, ε, hε, huv, hu, ?_, hcuv, ?_⟩
  · rw [hB, hv]; ring
  · intro h5u
    apply hA5
    rw [hu]
    exact dvd_mul_of_dvd_right (dvd_pow h5u hk0) _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma five_pow_split {A B C : ℤ} {r k : ℕ} (hk : Even k) (hk0 : k ≠ 0)
    (hc : C ≠ 0) (hab : IsCoprime A B) (heq : A * B = 5 ^ r * C ^ k) :
    ∃ u v ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsCoprime u v ∧
      A + B = ε * (u ^ k + 5 ^ r * v ^ k) ∧ |C| = |u * v| ∧
      ¬ (5 : ℤ) ∣ u := by
  by_cases hA5 : (5 : ℤ) ∣ A
  · have hB5 : ¬ (5 : ℤ) ∣ B := by
      intro hB5
      have hu := hab.isUnit_of_dvd' hA5 hB5
      norm_num [Int.isUnit_iff] at hu
    obtain ⟨u, v, ε, hε, huv, hB, hA, hcuv, hu5⟩ :=
      five_pow_split_left hk hk0 hc hab.symm hB5 (by rw [mul_comm]; exact heq)
    exact ⟨u, v, ε, hε, huv, by rw [hA, hB]; ring, hcuv, hu5⟩
  · obtain ⟨u, v, ε, hε, huv, hA, hB, hcuv, hu5⟩ :=
      five_pow_split_left hk hk0 hc hab hA5 heq
    exact ⟨u, v, ε, hε, huv, by rw [hA, hB]; ring, hcuv, hu5⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_factors_of_sum {A B M D : ℤ} (hsum : A + B = M)
    (hprod : A * B = D) (hcop : IsCoprime M D) : IsCoprime A B := by
  rw [← hsum, ← hprod] at hcop
  have h := hcop.of_mul_right_right
  obtain ⟨r, s, hrs⟩ := h
  exact ⟨r, r + s, by linear_combination hrs⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_factors_five_pow {A B M C : ℤ} {r k : ℕ} (hsum : A + B = M)
    (hprod : A * B = 5 ^ r * C ^ k) (hcop : IsCoprime M C)
    (h5 : ¬ (5 : ℤ) ∣ M) : IsCoprime A B := by
  have hM5 : IsCoprime M 5 :=
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Nat.prime_five)).mpr h5).symm
  exact coprime_factors_of_sum hsum hprod (hM5.pow_right.mul_right hcop.pow_right)

end OblathH1


/- Component: Quartic.lean -/

/-
Lebesgue's quartic obstruction, supporting the exact Oblath H1 target.
New formalization by Hanan Beer (@hananzlt), following V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
This is incomplete supporting work; no exact target theorem is claimed here.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_pow_of_abs_eq {a b : ℤ} (h : |a| = |b|) {k : ℕ} (hk : Even k) :
    a ^ k = b ^ k := by
  rw [← hk.pow_abs a, ← hk.pow_abs b, h]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_four_mod16 {a : ℤ} (ha : Odd a) : a ^ 4 % 16 = 1 := by
  have hz : ((a ^ 4 : ℤ) : ZMod 16) = (1 : ℤ) := by
    obtain ⟨t, rfl⟩ := ha
    push_cast
    have h (t : ZMod 16) : (t + t + 1) ^ 4 = 1 := by fin_cases t <;> decide
    simpa [two_mul] using h (t : ZMod 16)
  exact (ZMod.intCast_eq_intCast_iff' _ _ 16).mp hz

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_eight_mod16 {a : ℤ} (ha : Odd a) : a ^ 8 % 16 = 1 := by
  have h : Int.ModEq 16 (a ^ 4) 1 := odd_four_mod16 ha
  have hh := h.pow 2
  simpa [← pow_mul] using hh.eq

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma not_five_dvd_four {a : ℤ} (ha : ¬ (5 : ℤ) ∣ a) : ¬ (5 : ℤ) ∣ a ^ 4 :=
  fun h => ha (Int.Prime.dvd_pow' Nat.prime_five h)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_product_of_abs_eq {a b c : ℤ} (ha : Odd a) (h : |a| = |b * c|) :
    Odd b ∧ Odd c := by
  have hbc : Odd |b * c| := h ▸ (odd_abs.mpr ha)
  exact Int.odd_mul.mp (odd_abs.mp hbc)

/- The first factorization of the odd branch. -/
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_first {a d h : ℤ} (hah : IsCoprime a h) (ha5 : ¬ (5 : ℤ) ∣ a)
    (ha : Odd a) (hh : Odd h) (hh0 : h ≠ 0)
    (heq : d ^ 2 = a ^ 4 + 250 * a ^ 2 * h ^ 4 + 3125 * h ^ 8) :
    ∃ u v : ℤ, IsCoprime u v ∧ Odd u ∧ Odd v ∧ ¬ (5 : ℤ) ∣ u ∧
      |h| = |u * v| ∧ a ^ 2 = u ^ 8 - 125 * u ^ 4 * v ^ 4 + 3125 * v ^ 8 := by
  let M := a ^ 2 + 125 * h ^ 4
  have hMeven : Even M := by
    apply Int.even_iff.mpr
    have ha2 : Odd (a ^ 2) := ha.pow
    have hh4 : Odd (h ^ 4) := hh.pow
    rw [Int.odd_iff] at ha2 hh4
    dsimp [M]
    omega
  have hdeven : Even d := by
    apply (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    rw [heq]
    apply Int.even_iff.mpr
    have ha4 : Odd (a ^ 4) := ha.pow
    have hh8 : Odd (h ^ 8) := hh.pow
    rw [Int.odd_iff] at ha4 hh8
    rw [show a ^ 4 + 250 * a ^ 2 * h ^ 4 + 3125 * h ^ 8 =
      a ^ 4 + 250 * (a ^ 2 * h ^ 4) + 3125 * h ^ 8 by ring]
    omega
  obtain ⟨m, hm⟩ := hMeven
  obtain ⟨e, he⟩ := hdeven
  let A := m + e
  let B := m - e
  have hsum : A + B = M := by dsimp [A, B]; omega
  have hprod : A * B = 5 ^ 5 * h ^ 8 := by
    have hid : M ^ 2 - d ^ 2 = 4 * 5 ^ 5 * h ^ 8 := by
      dsimp [M]; linear_combination -heq
    dsimp [A, B]
    rw [hm, he] at hid
    nlinarith only [hid]
  have hMh : IsCoprime M h := by
    have hrep : M = a ^ 2 + h * (125 * h ^ 3) := by dsimp [M]; ring
    rw [hrep]
    exact hah.pow_left.add_mul_left_left _
  have hM5 : ¬ (5 : ℤ) ∣ M := by
    intro hd
    apply not_five_dvd_four ha5
    have ha2 : (5 : ℤ) ∣ a ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 25 * h ^ 4, by dsimp [M] at hk; linarith⟩
    exact dvd_trans ha2 (by use a ^ 2; ring)
  have hAB := coprime_factors_five_pow hsum hprod hMh hM5
  obtain ⟨u, v, ε, hε, huv, huv_sum, huv_abs, hu5⟩ :=
    five_pow_split (by decide : Even 8) (by decide) hh0 hAB hprod
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · have hMpos : 0 < M := by dsimp [M]; positivity
      have hu8 : 0 ≤ u ^ 8 := by positivity
      have hv8 : 0 ≤ v ^ 8 := by positivity
      rw [hsum, hε] at huv_sum
      nlinarith
  obtain ⟨huodd, hvodd⟩ := odd_product_of_abs_eq hh huv_abs
  have hh4 : h ^ 4 = (u * v) ^ 4 := even_pow_of_abs_eq huv_abs (by decide)
  refine ⟨u, v, huv, huodd, hvodd, hu5, huv_abs, ?_⟩
  rw [hsum, hε1] at huv_sum
  dsimp [M] at huv_sum
  rw [hh4] at huv_sum
  linear_combination huv_sum

end OblathH1

/- Component: QuarticOdd.lean -/

/-
The odd branch of Lebesgue's quartic obstruction.
Formalization: Hanan Beer (@hananzlt); mathematical proof: V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Proposition III.
Supporting work for exact Oblath H1. Not a complete exact solution.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_four_zmod16 {a : ℤ} (ha : Odd a) : (a : ZMod 16) ^ 4 = 1 := by
  have h := (ZMod.intCast_eq_intCast_iff' (a ^ 4) 1 16).mpr (odd_four_mod16 ha)
  simpa using h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_eight_zmod16 {a : ℤ} (ha : Odd a) : (a : ZMod 16) ^ 8 = 1 := by
  have h := (ZMod.intCast_eq_intCast_iff' (a ^ 8) 1 16).mpr (odd_eight_mod16 ha)
  simpa using h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma nonzero_of_odd {a : ℤ} (ha : Odd a) : a ≠ 0 := by
  rw [Int.odd_iff] at ha
  omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_of_abs_product {a b c d : ℤ} (hab : IsCoprime a b) (h : |b| = |c * d|) :
    IsCoprime a c ∧ IsCoprime a d := by
  rcases abs_eq_abs.mp h with hb | hb
  · rw [hb] at hab
    exact ⟨hab.of_mul_right_left, hab.of_mul_right_right⟩
  · have h' : IsCoprime a (c * d) := by
      simpa [hb] using hab.neg_right
    exact ⟨h'.of_mul_right_left, h'.of_mul_right_right⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_second {a u v : ℤ} (huv : IsCoprime u v)
    (huodd : Odd u) (hvodd : Odd v) (hu5 : ¬ (5 : ℤ) ∣ u)
    (heq : a ^ 2 = u ^ 8 - 125 * u ^ 4 * v ^ 4 + 3125 * v ^ 8) :
    ∃ p q L : ℤ, IsCoprime p q ∧ IsCoprime p u ∧ Odd p ∧ Odd q ∧ Odd L ∧
      ¬ (5 : ℤ) ∣ p ∧ p ^ 8 - u ^ 4 = 80 * L ^ 2 ∧
      p ^ 4 - 25 * q ^ 4 = 8 * L := by
  let D := 2 * u ^ 4 - 125 * v ^ 4
  let A := D + 2 * a
  let B := D - 2 * a
  have hsum : A + B = 2 * D := by dsimp [A, B]; ring
  have hprod : A * B = 5 ^ 5 * v ^ 8 := by
    dsimp [A, B, D]
    linear_combination -4 * heq
  have h2v : IsCoprime (2 : ℤ) v := Int.isCoprime_two_left.mpr hvodd
  have hDv : IsCoprime D v := by
    have hr : D = 2 * u ^ 4 + v * (-(125 * v ^ 3)) := by dsimp [D]; ring
    rw [hr]
    exact (h2v.mul_left huv.pow_left).add_mul_left_left _
  have h2D5 : ¬ (5 : ℤ) ∣ 2 * D := by
    intro hd
    have h4u : (5 : ℤ) ∣ 4 * u ^ 4 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k + 50 * v ^ 4, by dsimp [D] at hk; linarith⟩
    rcases Int.Prime.dvd_mul' Nat.prime_five h4u with h4 | hu
    · norm_num at h4
    · exact hu5 (Int.Prime.dvd_pow' Nat.prime_five hu)
  have hAB := coprime_factors_five_pow hsum hprod (h2v.mul_left hDv) h2D5
  obtain ⟨p, q, ε, hε, hpq, hsum2, hvabs, hp5⟩ :=
    five_pow_split (by decide : Even 8) (by decide) (nonzero_of_odd hvodd) hAB hprod
  obtain ⟨hpodd, hqodd⟩ := odd_product_of_abs_eq hvodd hvabs
  have hv4 := even_pow_of_abs_eq hvabs (by decide : Even 4)
  have hbase : 4 * u ^ 4 = ε * (p ^ 8 + 3125 * q ^ 8) + 250 * p ^ 4 * q ^ 4 := by
    rw [hsum] at hsum2
    dsimp [D] at hsum2
    rw [hv4] at hsum2
    linear_combination hsum2
  have hεneg : ε = -1 := by
    rcases hε with hε | hε
    · exfalso
      rw [hε] at hbase
      have hmod := congrArg (fun x : ℤ => (x : ZMod 16)) hbase
      push_cast at hmod
      rw [odd_four_zmod16 huodd, odd_eight_zmod16 hpodd, odd_eight_zmod16 hqodd,
        odd_four_zmod16 hpodd, odd_four_zmod16 hqodd] at hmod
      norm_num at hmod
      exact (by decide : (4 : ZMod 16) ≠ 3376) hmod
    · exact hε
  let L := (p ^ 4 - 25 * q ^ 4) / 8
  have hp4 := odd_four_mod16 hpodd
  have hq4 := odd_four_mod16 hqodd
  have hL : p ^ 4 - 25 * q ^ 4 = 8 * L := by dsimp [L]; omega
  have hLodd : Odd L := by rw [Int.odd_iff]; dsimp [L]; omega
  have hpu : IsCoprime p u := ((coprime_of_abs_product huv hvabs).1).symm
  refine ⟨p, q, L, hpq, hpu, hpodd, hqodd, hLodd, hp5, ?_, hL⟩
  have hid : 4 * (p ^ 8 - u ^ 4) = 5 * (p ^ 4 - 25 * q ^ 4) ^ 2 := by
    rw [hεneg] at hbase
    linear_combination -hbase
  rw [hL] at hid
  nlinarith only [hid]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_sq_zmod8 {a : ℤ} (ha : Odd a) : (a : ZMod 8) ^ 2 = 1 := by
  obtain ⟨t, rfl⟩ := ha
  push_cast
  have h (t : ZMod 8) : (t + t + 1) ^ 2 = 1 := by fin_cases t <;> decide
  simpa [two_mul] using h (t : ZMod 8)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_four_zmod8 {a : ℤ} (ha : Odd a) : (a : ZMod 8) ^ 4 = 1 := by
  calc (a : ZMod 8) ^ 4 = ((a : ZMod 8) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [odd_sq_zmod8 ha]; norm_num

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_final {p q u L : ℤ} (hpq : IsCoprime p q)
    (hpodd : Odd p) (huodd : Odd u) (hLodd : Odd L)
    (hp5 : ¬ (5 : ℤ) ∣ p) (heq : p ^ 8 - u ^ 4 = 80 * L ^ 2)
    (hL : p ^ 4 - 25 * q ^ 4 = 8 * L) : False := by
  have hpL : IsCoprime p L := by
    have hp5cop : IsCoprime p 5 :=
      ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Nat.prime_five)).mpr hp5).symm
    have hp25 : IsCoprime p 25 := by simpa using (hp5cop.pow_right (n := 2))
    have hc := (hp25.mul_right (hpq.pow_right (n := 4))).neg_right.add_mul_left_right (p ^ 3)
    have he : -(25 * q ^ 4) + p * p ^ 3 = 8 * L := by linear_combination hL
    rw [he] at hc
    exact hc.of_mul_right_right
  have hp2 : IsCoprime p 2 := Int.isCoprime_two_right.mpr hpodd
  have hp2L : IsCoprime p (2 * L) := hp2.mul_right hpL
  have hp4odd : Odd (p ^ 4) := hpodd.pow
  have hu2odd : Odd (u ^ 2) := huodd.pow
  obtain ⟨A, hA⟩ : Even (p ^ 4 + u ^ 2) := hp4odd.add_odd hu2odd
  obtain ⟨B, hB⟩ : Even (p ^ 4 - u ^ 2) := hp4odd.sub_odd hu2odd
  have hsum : A + B = p ^ 4 := by omega
  have hprod : A * B = 5 ^ 1 * (2 * L) ^ 2 := by
    have hid : (p ^ 4 + u ^ 2) * (p ^ 4 - u ^ 2) = 4 * (5 ^ 1 * (2 * L) ^ 2) := by
      linear_combination heq
    rw [hA, hB] at hid
    nlinarith only [hid]
  have hAB := coprime_factors_five_pow hsum hprod hp2L.pow_left (not_five_dvd_four hp5)
  have h2L0 : 2 * L ≠ 0 := mul_ne_zero (by norm_num) (nonzero_of_odd hLodd)
  obtain ⟨r, s, ε, hε, hrs, hrs_sum, hrs_abs, -⟩ :=
    five_pow_split (by decide : Even 2) (by decide) h2L0 hAB hprod
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · have hp4pos : 0 < p ^ 4 := by
        exact pow_pos (abs_pos.mpr (nonzero_of_odd hpodd)) 4 |>.trans_eq (by rw [Even.pow_abs (by decide : Even 4)])
      rw [hsum, hε] at hrs_sum
      nlinarith [sq_nonneg r, sq_nonneg s]
  have hrs_eq : r ^ 2 + 5 * s ^ 2 = p ^ 4 := by
    rw [hsum, hε1] at hrs_sum
    simpa using hrs_sum.symm
  have hrs_prod : (r * s) ^ 2 = (2 * L) ^ 2 :=
    (even_pow_of_abs_eq hrs_abs (by decide : Even 2)).symm
  have hsumz : (r : ZMod 8) ^ 2 + 5 * (s : ZMod 8) ^ 2 = 1 := by
    have hh := congrArg (fun x : ℤ => (x : ZMod 8)) hrs_eq
    push_cast at hh
    rwa [odd_four_zmod8 hpodd] at hh
  have hprodz : ((r : ZMod 8) * (s : ZMod 8)) ^ 2 = 4 := by
    have hh := congrArg (fun x : ℤ => (x : ZMod 8)) hrs_prod
    push_cast at hh
    rw [mul_pow, mul_pow, odd_sq_zmod8 hLodd] at hh
    norm_num at hh ⊢
    simpa only [mul_pow] using hh
  have hres : (r : ZMod 8) ^ 2 = 4 ∧ (s : ZMod 8) ^ 2 = 1 := by
    have hh : ∀ r s : ZMod 8, r ^ 2 + 5 * s ^ 2 = 1 → (r * s) ^ 2 = 4 →
        r ^ 2 = 4 ∧ s ^ 2 = 1 := by
      intro r s; fin_cases r <;> fin_cases s <;> decide
    exact hh (r : ZMod 8) (s : ZMod 8) hsumz hprodz
  have hrmod : r ^ 2 % 8 = 4 := (ZMod.intCast_eq_intCast_iff' (r ^ 2) 4 8).mp (by
    push_cast; exact hres.1)
  have hsmod : s ^ 2 % 8 = 1 := (ZMod.intCast_eq_intCast_iff' (s ^ 2) 1 8).mp (by
    push_cast; exact hres.2)
  have hreven : Even r := (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    (Int.even_iff.mpr (by omega))
  have hsodd : Odd s := (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    (Int.odd_iff.mpr (by omega))
  obtain ⟨R, hR⟩ := hreven
  have hps := (coprime_of_abs_product hp2L hrs_abs).2
  let C := p ^ 2 + 2 * R
  let D := p ^ 2 - 2 * R
  have hsum2 : C + D = 2 * p ^ 2 := by dsimp [C, D]; ring
  have hprod2 : C * D = 5 ^ 1 * s ^ 2 := by
    dsimp [C, D]
    rw [hR] at hrs_eq
    linear_combination -hrs_eq
  have h2s : IsCoprime (2 : ℤ) s := Int.isCoprime_two_left.mpr hsodd
  have h2p5 : ¬ (5 : ℤ) ∣ 2 * p ^ 2 := by
    intro hd
    rcases Int.Prime.dvd_mul' Nat.prime_five hd with h2 | hp
    · norm_num at h2
    · exact hp5 (Int.Prime.dvd_pow' Nat.prime_five hp)
  have hCD := coprime_factors_five_pow hsum2 hprod2 (h2s.mul_left hps.pow_left) h2p5
  obtain ⟨t, w, η, hη, -, htw, -, -⟩ :=
    five_pow_split (by decide : Even 2) (by decide) (nonzero_of_odd hsodd) hCD hprod2
  have hη1 : η = 1 := by
    rcases hη with hη | hη
    · exact hη
    · have hp2pos := sq_pos_of_ne_zero (nonzero_of_odd hpodd)
      rw [hsum2, hη] at htw
      nlinarith [sq_nonneg t, sq_nonneg w]
  rw [hsum2, hη1] at htw
  have hmod := congrArg (fun x : ℤ => (x : ZMod 5)) htw
  push_cast at hmod
  rw [show (5 : ZMod 5) = 0 by decide, zero_mul, add_zero] at hmod
  norm_num at hmod
  have hres5 : ∀ p t : ZMod 5, 2 * p ^ 2 = t ^ 2 → p = 0 := by
    decide
  have hpzero : (p : ZMod 5) = 0 := hres5 (p : ZMod 5) (t : ZMod 5) hmod
  exact hp5 ((ZMod.intCast_zmod_eq_zero_iff_dvd p 5).mp hpzero)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_no_solution {a h d : ℤ} (hah : IsCoprime a h)
    (ha5 : ¬ (5 : ℤ) ∣ a) (ha : Odd a) (hh : Odd h) (hh0 : h ≠ 0)
    (heq : d ^ 2 = a ^ 4 + 250 * a ^ 2 * h ^ 4 + 3125 * h ^ 8) : False := by
  obtain ⟨u, v, huv, huodd, hvodd, hu5, -, hfirst⟩ :=
    odd_quartic_first hah ha5 ha hh hh0 heq
  obtain ⟨p, q, L, hpq, -, hpodd, -, hLodd, hp5, hsecond, hL⟩ :=
    odd_quartic_second huv huodd hvodd hu5 hfirst
  exact odd_quartic_final hpq hpodd huodd hLodd hp5 hsecond hL

end OblathH1


/- Component: Squareclass.lean -/

/-
Preservation of the 5/10 square classes in Lebesgue's quartic descent.
Formalization by Hanan Beer (@hananzlt); mathematical source V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Proposition III.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma positive_five_square_extract {A B H : ℤ} (hA : 0 < A) (hB : 0 < B)
    (hcop : IsCoprime A B) (hA5 : ¬ (5 : ℤ) ∣ A) (heq : A * B = 5 * H ^ 2) :
    ∃ v : ℤ, B = 5 * v ^ 2 := by
  have hH0 : H ≠ 0 := by intro h; rw [h] at heq; nlinarith
  obtain ⟨u, v, ε, hε, -, -, hBv, -, -⟩ := five_pow_split_left
    (by decide : Even 2) (by decide) hH0 hcop hA5
    (show A * B = 5 ^ 1 * H ^ 2 by simpa using heq)
  rcases hε with rfl | rfl
  · exact ⟨v, by simpa using hBv⟩
  · nlinarith [sq_nonneg v]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma squareclass_descend {A B H : ℤ} (hA : 0 < A) (hB : 0 < B)
    (hcop : IsCoprime A B) (hA5 : ¬ (5 : ℤ) ∣ A)
    (heq : 2 * A * B = 5 * H ^ 2 ∨ 2 * A * B = 10 * H ^ 2) :
    ∃ v : ℤ, B = 5 * v ^ 2 ∨ B = 10 * v ^ 2 := by
  rcases heq with heq | heq
  · have hHeven : Even H := by
      apply (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
      apply Int.even_iff.mpr
      have hlin : 2 * (A * B) = 5 * H ^ 2 := by linear_combination heq
      omega
    obtain ⟨K, hK⟩ := hHeven
    have heq' : A * B = 10 * K ^ 2 := by rw [hK] at heq; nlinarith only [heq]
    rcases Int.even_or_odd B with hBeven | hBodd
    · have hAodd : Odd A := by
        rcases Int.even_or_odd A with hAe | hAo
        · have hu := hcop.isUnit_of_dvd' hAe.two_dvd hBeven.two_dvd
          norm_num [Int.isUnit_iff] at hu
        · exact hAo
      have hA2 : IsCoprime A 2 := Int.isCoprime_two_right.mpr hAodd
      obtain ⟨v, hv⟩ := positive_five_square_extract hA (by omega : 0 < 2 * B)
        (hA2.mul_right hcop) hA5 (show A * (2 * B) = 5 * (2 * K) ^ 2 by
          linear_combination 2 * heq')
      have hveven : Even v := by
        apply (Int.even_pow' (by decide : (2 : ℕ) ≠ 0)).mp
        apply Int.even_iff.mpr
        omega
      obtain ⟨w, hw⟩ := hveven
      exact ⟨w, Or.inr (by rw [hw] at hv; nlinarith only [hv])⟩
    · have h2B : IsCoprime (2 : ℤ) B := Int.isCoprime_two_left.mpr hBodd
      have h2A5 : ¬ (5 : ℤ) ∣ 2 * A := by
        intro hd
        rcases Int.Prime.dvd_mul' Nat.prime_five hd with h2 | hA
        · norm_num at h2
        · exact hA5 hA
      obtain ⟨v, hv⟩ := positive_five_square_extract (by omega : 0 < 2 * A) hB
        (h2B.mul_left hcop) h2A5 (show (2 * A) * B = 5 * (2 * K) ^ 2 by
          linear_combination 2 * heq')
      exact ⟨v, Or.inl hv⟩
  · obtain ⟨v, hv⟩ := positive_five_square_extract hA hB hcop hA5
      (show A * B = 5 * H ^ 2 by nlinarith only [heq])
    exact ⟨v, Or.inl hv⟩

end OblathH1

/- Component: QuarticEven.lean -/

/-
The even branch of Lebesgue's quartic descent.
Formalization by Hanan Beer (@hananzlt), following V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
Supporting work for exact Oblath H1, not a complete solution.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_first {a c d : ℤ} (hac : IsCoprime a c)
    (haodd : Odd a) (hceven : Even c) (hc0 : c ≠ 0) (ha5 : ¬ (5 : ℤ) ∣ a)
    (heq : d ^ 2 = a ^ 4 + 10 * a ^ 2 * c ^ 2 + 5 * c ^ 4) :
    ∃ g f : ℤ, IsCoprime g f ∧ ¬ (5 : ℤ) ∣ g ∧ |c| = |g * f| ∧
      a ^ 2 = g ^ 4 - 5 * g ^ 2 * f ^ 2 + 5 * f ^ 4 := by
  let M := a ^ 2 + 5 * c ^ 2
  have hModd : Odd M := by
    have ha2 : Odd (a ^ 2) := haodd.pow
    have hc2 : Even (c ^ 2) := hceven.pow_of_ne_zero (by decide)
    rw [Int.odd_iff] at ha2 ⊢
    rw [Int.even_iff] at hc2
    dsimp [M]; omega
  have hdodd : Odd d := by
    apply (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp
    rw [heq, Int.odd_iff]
    have ha4 : Odd (a ^ 4) := haodd.pow
    have hc4 : Even (c ^ 4) := hceven.pow_of_ne_zero (by decide)
    rw [Int.odd_iff] at ha4
    rw [Int.even_iff] at hc4
    rw [show a ^ 4 + 10 * a ^ 2 * c ^ 2 + 5 * c ^ 4 =
      a ^ 4 + 10 * (a ^ 2 * c ^ 2) + 5 * c ^ 4 by ring]
    omega
  obtain ⟨A, hA⟩ := hModd.add_odd hdodd
  obtain ⟨B, hB⟩ := hModd.sub_odd hdodd
  have hsum : A + B = M := by omega
  have hprod : A * B = 5 ^ 1 * c ^ 4 := by
    have hid : (M + d) * (M - d) = 4 * (5 ^ 1 * c ^ 4) := by
      dsimp [M]; linear_combination -heq
    rw [hA, hB] at hid
    nlinarith only [hid]
  have hMc : IsCoprime M c := by
    have hrep : M = a ^ 2 + c * (5 * c) := by dsimp [M]; ring
    rw [hrep]
    exact hac.pow_left.add_mul_left_left _
  have hM5 : ¬ (5 : ℤ) ∣ M := by
    intro hd
    have ha2 : (5 : ℤ) ∣ a ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - c ^ 2, by dsimp [M] at hk; linarith⟩
    exact ha5 (Int.Prime.dvd_pow' Nat.prime_five ha2)
  have hAB := coprime_factors_five_pow hsum hprod hMc hM5
  obtain ⟨g, f, ε, hε, hgf, hgf_sum, hgf_abs, hg5⟩ :=
    five_pow_split (by decide : Even 4) (by decide) hc0 hAB hprod
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · have hMpos : 0 < M := by
        dsimp [M]; nlinarith [sq_pos_of_ne_zero (nonzero_of_odd haodd), sq_nonneg c]
      rw [hsum, hε] at hgf_sum
      nlinarith [sq_nonneg (g ^ 2), sq_nonneg (f ^ 2)]
  have hc2 := even_pow_of_abs_eq hgf_abs (by decide : Even 2)
  refine ⟨g, f, hgf, hg5, hgf_abs, ?_⟩
  rw [hsum, hε1] at hgf_sum
  dsimp [M] at hgf_sum
  rw [hc2] at hgf_sum
  linear_combination hgf_sum

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_step_even {a g h : ℤ} (hgh : IsCoprime g h)
    (haodd : Odd a) (hgodd : Odd g) (hg5 : ¬ (5 : ℤ) ∣ g) (hh0 : h ≠ 0)
    (heq : a ^ 2 = g ^ 4 - 20 * g ^ 2 * h ^ 2 + 80 * h ^ 4) :
    ∃ u v : ℤ, IsCoprime u v ∧ Odd u ∧ ¬ (5 : ℤ) ∣ u ∧ |h| = |u * v| ∧
      g ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 := by
  let D := g ^ 2 - 10 * h ^ 2
  have hDodd : Odd D := by
    have hg2 : Odd (g ^ 2) := hgodd.pow
    rw [Int.odd_iff] at hg2 ⊢
    dsimp [D]; omega
  obtain ⟨A, hA⟩ := hDodd.add_odd haodd
  obtain ⟨B, hB⟩ := hDodd.sub_odd haodd
  have hsum : A + B = D := by omega
  have hprod : A * B = 5 ^ 1 * h ^ 4 := by
    have hid : (D + a) * (D - a) = 4 * (5 ^ 1 * h ^ 4) := by
      dsimp [D]; linear_combination -heq
    rw [hA, hB] at hid
    nlinarith only [hid]
  have hDh : IsCoprime D h := by
    have hr : D = g ^ 2 + h * (-10 * h) := by dsimp [D]; ring
    rw [hr]
    exact hgh.pow_left.add_mul_left_left _
  have hD5 : ¬ (5 : ℤ) ∣ D := by
    intro hd
    have hg2 : (5 : ℤ) ∣ g ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k + 2 * h ^ 2, by dsimp [D] at hk; linarith⟩
    exact hg5 (Int.Prime.dvd_pow' Nat.prime_five hg2)
  have hAB := coprime_factors_five_pow hsum hprod hDh hD5
  obtain ⟨u, v, ε, hε, huv, huv_sum, huv_abs, hu5⟩ :=
    five_pow_split (by decide : Even 4) (by decide) hh0 hAB hprod
  have hh2 := even_pow_of_abs_eq huv_abs (by decide : Even 2)
  have hbase : g ^ 2 = ε * (u ^ 4 + 5 * v ^ 4) + 10 * u ^ 2 * v ^ 2 := by
    rw [hsum] at huv_sum
    dsimp [D] at huv_sum
    rw [hh2] at huv_sum
    linear_combination huv_sum
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · exfalso
      rw [hε] at hbase
      have hmod := congrArg (fun x : ℤ => (x : ZMod 8)) hbase
      push_cast at hmod
      rw [odd_sq_zmod8 hgodd] at hmod
      have impossible : ∀ u v : ZMod 8,
          1 ≠ -1 * (u ^ 4 + 5 * v ^ 4) + 10 * u ^ 2 * v ^ 2 := by
        intro u v; fin_cases u <;> fin_cases v <;> decide
      exact impossible (u : ZMod 8) (v : ZMod 8) hmod
  have hnew : g ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 := by
    rw [hε1] at hbase
    linear_combination hbase
  have huodd : Odd u := by
    have hmod := congrArg (fun x : ℤ => (x : ZMod 8)) hnew
    push_cast at hmod
    rw [odd_sq_zmod8 hgodd] at hmod
    have hc : ∀ u v : ZMod 8,
        1 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 → u ^ 2 = 1 := by
      intro u v; fin_cases u <;> fin_cases v <;> decide
    have hu2z := hc (u : ZMod 8) (v : ZMod 8) hmod
    have hu2mod : u ^ 2 % 8 = 1 := (ZMod.intCast_eq_intCast_iff' (u ^ 2) 1 8).mp (by
      push_cast; exact hu2z)
    exact (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp (Int.odd_iff.mpr (by omega))
  exact ⟨u, v, huv, huodd, hu5, huv_abs, hnew⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_step_odd {a f h : ℤ} (hhf : IsCoprime h f)
    (hfodd : Odd f) (hh5 : ¬ (5 : ℤ) ∣ h)
    (heq : a ^ 2 = 16 * h ^ 4 - 20 * h ^ 2 * f ^ 2 + 5 * f ^ 4) :
    ∃ u v : ℤ, IsCoprime u v ∧ Odd u ∧ Odd v ∧ ¬ (5 : ℤ) ∣ u ∧ |f| = |u * v| ∧
      (4 * h) ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 := by
  let D := 8 * h ^ 2 - 5 * f ^ 2
  let A := D + 2 * a
  let B := D - 2 * a
  have hsum : A + B = 2 * D := by dsimp [A, B]; ring
  have hprod : A * B = 5 ^ 1 * f ^ 4 := by
    dsimp [A, B, D]
    linear_combination -4 * heq
  have h2f : IsCoprime (2 : ℤ) f := Int.isCoprime_two_left.mpr hfodd
  have h8f : IsCoprime (8 : ℤ) f := by simpa using (h2f.pow_left (m := 3))
  have hDf : IsCoprime D f := by
    have hr : D = 8 * h ^ 2 + f * (-5 * f) := by dsimp [D]; ring
    rw [hr]
    exact (h8f.mul_left hhf.pow_left).add_mul_left_left _
  have h2D5 : ¬ (5 : ℤ) ∣ 2 * D := by
    intro hd
    have h16h : (5 : ℤ) ∣ 16 * h ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k + 2 * f ^ 2, by dsimp [D] at hk; linarith⟩
    rcases Int.Prime.dvd_mul' Nat.prime_five h16h with h16 | hh
    · norm_num at h16
    · exact hh5 (Int.Prime.dvd_pow' Nat.prime_five hh)
  have hAB := coprime_factors_five_pow hsum hprod (h2f.mul_left hDf) h2D5
  obtain ⟨u, v, ε, hε, huv, huv_sum, huv_abs, hu5⟩ :=
    five_pow_split (by decide : Even 4) (by decide) (nonzero_of_odd hfodd) hAB hprod
  obtain ⟨huodd, hvodd⟩ := odd_product_of_abs_eq hfodd huv_abs
  have hf2 := even_pow_of_abs_eq huv_abs (by decide : Even 2)
  have hbase : 16 * h ^ 2 = ε * (u ^ 4 + 5 * v ^ 4) + 10 * u ^ 2 * v ^ 2 := by
    rw [hsum] at huv_sum
    dsimp [D] at huv_sum
    rw [hf2] at huv_sum
    linear_combination huv_sum
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · exfalso
      rw [hε] at hbase
      have hmod := congrArg (fun x : ℤ => (x : ZMod 16)) hbase
      push_cast at hmod
      rw [odd_four_zmod16 huodd, odd_four_zmod16 hvodd] at hmod
      have hu2 := odd_sq_zmod8 huodd
      have hv2 := odd_sq_zmod8 hvodd
      have hmod8 := congrArg (fun x : ℤ => (x : ZMod 8)) hbase
      push_cast at hmod8
      rw [odd_four_zmod8 huodd, odd_four_zmod8 hvodd, hu2, hv2] at hmod8
      rw [show (16 : ZMod 8) = 0 by decide, zero_mul] at hmod8
      norm_num at hmod8
      exact (by decide : (0 : ZMod 8) ≠ 4) hmod8
  refine ⟨u, v, huv, huodd, hvodd, hu5, huv_abs, ?_⟩
  rw [hε1] at hbase
  linear_combination hbase

end OblathH1

/- Component: Descent.lean -/

/-
Assembly of Lebesgue's quartic descent, supporting exact Oblath H1.
Formalization by Hanan Beer (@hananzlt); proof source V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵, Propositions II–III.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def FiveSquareclass (c : ℤ) : Prop := ∃ H : ℤ, c = 5 * H ^ 2 ∨ c = 10 * H ^ 2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def QuarticCandidate (c : ℤ) : Prop :=
  0 < c ∧ ∃ a d : ℤ, IsCoprime a c ∧ Odd a ∧ ¬ (5 : ℤ) ∣ a ∧
    FiveSquareclass c ∧ d ^ 2 = a ^ 4 + 10 * a ^ 2 * c ^ 2 + 5 * c ^ 4

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma nonzero_of_not_five_dvd {a : ℤ} (ha : ¬ (5 : ℤ) ∣ a) : a ≠ 0 := by
  intro h; apply ha; simp [h]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma coprime_abs_right_int {a b : ℤ} (h : IsCoprime a b) : IsCoprime a |b| := by
  rcases le_total 0 b with hb | hb
  · simpa [abs_of_nonneg hb] using h
  · simpa [abs_of_nonpos hb] using h.neg_right

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma odd_quartic_candidate {c : ℤ} (hc : QuarticCandidate c) (hcodd : Odd c) : False := by
  obtain ⟨hcpos, a, d, hac, haodd, ha5, ⟨H, hH⟩, heq⟩ := hc
  rcases hH with hH | hH
  · have hHodd : Odd H := by
      have hprod : Odd (5 * H ^ 2) := hH ▸ hcodd
      have hsq := (Int.odd_mul.mp hprod).2
      exact (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp hsq
    have haH : IsCoprime a H := hac.of_isCoprime_of_dvd_right
      ⟨5 * H, by rw [hH]; ring⟩
    have heq' : d ^ 2 = a ^ 4 + 250 * a ^ 2 * H ^ 4 + 3125 * H ^ 8 := by
      rw [hH] at heq
      linear_combination heq
    exact odd_quartic_no_solution haH ha5 haodd hHodd (nonzero_of_odd hHodd) heq'
  · have hceven : Even c := ⟨5 * H ^ 2, by linarith⟩
    exact Int.not_even_iff_odd.mpr hcodd hceven

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma package_descent {c k u v d : ℤ} (_hc : 0 < c)
    (hclass : FiveSquareclass c) (hcid : c = 2 * |k * u| * |v|)
    (hkv : IsCoprime k v) (huv : IsCoprime u v)
    (hk5 : ¬ (5 : ℤ) ∣ k) (hu5 : ¬ (5 : ℤ) ∣ u) (huodd : Odd u) (hv0 : v ≠ 0)
    (heq : d ^ 2 = u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4) :
    ∃ c' : ℤ, c' < c ∧ QuarticCandidate c' := by
  have hA : 0 < |k * u| := abs_pos.mpr
    (mul_ne_zero (nonzero_of_not_five_dvd hk5) (nonzero_of_not_five_dvd hu5))
  have hB : 0 < |v| := abs_pos.mpr hv0
  have hcop : IsCoprime |k * u| |v| :=
    (coprime_abs_right_int (coprime_abs_right_int (hkv.mul_left huv)).symm).symm
  have hA5 : ¬ (5 : ℤ) ∣ |k * u| := by
    intro hd
    rcases Int.Prime.dvd_mul' Nat.prime_five ((dvd_abs _ _).mp hd) with hk | hu
    · exact hk5 hk
    · exact hu5 hu
  obtain ⟨H, hH⟩ := hclass
  obtain ⟨V, hV⟩ := squareclass_descend hA hB hcop hA5 (by rwa [← hcid])
  refine ⟨|v|, ?_, hB, u, d, coprime_abs_right_int huv, huodd, hu5, ⟨V, hV⟩, ?_⟩
  · have hA1 : 1 ≤ |k * u| := by omega
    nlinarith
  · rw [Even.pow_abs (by decide : Even 2), Even.pow_abs (by decide : Even 4)]
    exact heq

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma even_quartic_candidate {c : ℤ} (hc : QuarticCandidate c) (hceven : Even c) :
    ∃ c' : ℤ, c' < c ∧ QuarticCandidate c' := by
  obtain ⟨hcpos, a, d, hac, haodd, ha5, hclass, heq⟩ := hc
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  obtain ⟨g, f, hgf, hg5, hgf_abs, hfirst⟩ :=
    even_quartic_first hac haodd hceven hc0 ha5 heq
  have hcabs : c = |g * f| := by rw [← hgf_abs, abs_of_pos hcpos]
  rcases Int.even_or_odd f with hfeven | hfodd
  · obtain ⟨h, hf⟩ := hfeven
    have hf' : f = 2 * h := by omega
    have hgh : IsCoprime g h := by rw [hf'] at hgf; exact hgf.of_mul_right_right
    have hgodd : Odd g := by
      rcases Int.even_or_odd g with hgeven | hgodd
      · have hu := hgf.isUnit_of_dvd' hgeven.two_dvd (by rw [hf']; exact dvd_mul_right 2 h)
        norm_num [Int.isUnit_iff] at hu
      · exact hgodd
    have hh0 : h ≠ 0 := by
      intro h0
      rw [hf', h0] at hcabs
      simp at hcabs
      exact hc0 hcabs
    have hstep : a ^ 2 = g ^ 4 - 20 * g ^ 2 * h ^ 2 + 80 * h ^ 4 := by
      rw [hf'] at hfirst
      linear_combination hfirst
    obtain ⟨u, v, huv, huodd, hu5, hhabs, hnew⟩ :=
      even_quartic_step_even hgh haodd hgodd hg5 hh0 hstep
    have hgv := (coprime_of_abs_product hgh hhabs).2
    have hv0 : v ≠ 0 := by
      intro hv
      apply hh0
      have : |h| = 0 := by simpa [hv] using hhabs
      exact abs_eq_zero.mp this
    have hcid : c = 2 * |g * u| * |v| := by
      calc c = |g * f| := hcabs
        _ = 2 * |g| * |h| := by rw [hf']; simp only [abs_mul]; norm_num; ring
        _ = 2 * |g * u| * |v| := by rw [hhabs]; simp only [abs_mul]; ring
    exact package_descent hcpos hclass hcid hgv huv hg5 hu5 huodd hv0 hnew
  · have hgeven : Even g := by
      have hev : Even (g * f) := even_abs.mp (hgf_abs ▸ even_abs.mpr hceven)
      rcases Int.even_mul.mp hev with hg | hf
      · exact hg
      · exact False.elim (Int.not_even_iff_odd.mpr hfodd hf)
    obtain ⟨h, hg⟩ := hgeven
    have hg' : g = 2 * h := by omega
    have hhf : IsCoprime h f := by rw [hg'] at hgf; exact hgf.of_mul_left_right
    have hh5 : ¬ (5 : ℤ) ∣ h := by
      intro hd; apply hg5; rw [hg']; exact dvd_mul_of_dvd_right hd 2
    have hstep : a ^ 2 = 16 * h ^ 4 - 20 * h ^ 2 * f ^ 2 + 5 * f ^ 4 := by
      rw [hg'] at hfirst
      linear_combination hfirst
    obtain ⟨u, v, huv, huodd, -, hu5, hfabs, hnew⟩ :=
      even_quartic_step_odd hhf hfodd hh5 hstep
    have hhv := (coprime_of_abs_product hhf hfabs).2
    have hv0 : v ≠ 0 := by
      intro hv
      apply nonzero_of_odd hfodd
      have : |f| = 0 := by simpa [hv] using hfabs
      exact abs_eq_zero.mp this
    have hcid : c = 2 * |h * u| * |v| := by
      calc c = |g * f| := hcabs
        _ = 2 * |h| * |f| := by rw [hg']; simp only [abs_mul]; norm_num
        _ = 2 * |h * u| * |v| := by rw [hfabs]; simp only [abs_mul]; ring
    exact package_descent hcpos hclass hcid hhv huv hh5 hu5 huodd hv0 hnew

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma no_quartic_candidate_aux : ∀ n : ℕ, ∀ c : ℤ, c.natAbs = n → ¬ QuarticCandidate c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hcn hc
    rcases Int.even_or_odd c with hceven | hcodd
    · obtain ⟨c', hc'lt, hc'⟩ := even_quartic_candidate hc hceven
      have hn : c'.natAbs < n := by
        rw [← hcn, ← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_pos hc'.1, abs_of_pos hc.1]
        exact hc'lt
      exact ih _ hn c' rfl hc'
    · exact odd_quartic_candidate hc hcodd

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma no_quartic_candidate (c : ℤ) : ¬ QuarticCandidate c :=
  no_quartic_candidate_aux _ c rfl

end OblathH1

/- Component: PrimitiveFirst.lean -/

/-
First-case bridge from primitive fifth-power arithmetic progressions to Lebesgue's quartic descent.
New formalization by Hanan Beer (@hananzlt). The imported Dirichlet extraction and its
parity/coprimality patterns are reused from Pedro Bessa (@nijv), PR5575, immutable head
572ffd235e0a734035a1737d90d28c37c24417ee; full provenance is in Dirichlet.lean.
Mathematical source: V.-A. Lebesgue (1843), Théorèmes nouveaux sur l'équation indéterminée
x⁵+y⁵=az⁵, Propositions III–IV. Existing exact reduction authored by @mudkjp.
-/
namespace OblathH1
open OMA672H2_H1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma square_of_pos_mul {A B C : ℤ} (hA : 0 < A) (hcop : IsCoprime A B)
    (heq : A * B = C ^ 2) : ∃ r : ℤ, A = r ^ 2 := by
  obtain ⟨r, hr | hr⟩ := Int.sq_of_isCoprime hcop heq
  · exact ⟨r, hr⟩
  · nlinarith [sq_nonneg r]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma quartic_fifth_impossible {u v w : ℤ} (huv : IsCoprime u v)
    (hpar : Odd (u + v)) (hu5 : ¬ (5 : ℤ) ∣ u) (hv5 : (5 : ℤ) ∣ v) (hv0 : v ≠ 0)
    (heq : u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4 = w ^ 5) : False := by
  let P := u ^ 2 + 5 * v ^ 2
  let R := 2 * v ^ 2
  have hPodd : Odd P := by
    rw [odd_iff_zmod2] at hpar ⊢
    dsimp [P]
    push_cast at hpar ⊢
    revert hpar
    generalize (u : ZMod 2) = x, (v : ZMod 2) = y
    revert x y; decide
  have hPRodd : Odd (P + R) := hPodd.add_even ⟨v ^ 2, by dsimp [R]; ring⟩
  have hPv : IsCoprime P v := by
    have hr : P = u ^ 2 + v * (5 * v) := by dsimp [P]; ring
    rw [hr]
    exact huv.pow_left.add_mul_left_left _
  have hPR : IsCoprime P R :=
    (isCoprime_two_of_odd hPodd).mul_right hPv.pow_right
  have hP5 : ¬ (5 : ℤ) ∣ P := by
    intro hd
    have hu2 : (5 : ℤ) ∣ u ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - v ^ 2, by dsimp [P] at hk; linarith⟩
    exact hu5 (Int.Prime.dvd_pow' Nat.prime_five hu2)
  have hR5 : (5 : ℤ) ∣ R := by
    obtain ⟨k, hk⟩ := hv5
    exact ⟨10 * k ^ 2, by dsimp [R]; rw [hk]; ring⟩
  have hnorm : P ^ 2 - 5 * R ^ 2 = w ^ 5 := by
    dsimp [P, R]
    linear_combination heq
  obtain ⟨a, b, ha, hb⟩ := dirichlet_lemma hPR hP5 hR5 hPRodd hnorm
  have hab : IsCoprime a b := by
    have hc := hPR
    rw [ha, hb] at hc
    exact hc.of_mul_left_left.of_mul_right_left.of_mul_right_right
  have habodd : Odd (a + b) := by
    apply odd_add_of_odd_PQ5
    rw [← ha, ← hb]
    exact hPRodd
  have ha5 : ¬ (5 : ℤ) ∣ a := fun hd => hP5 (ha ▸ dvd_mul_of_dvd_left hd _)
  let T := a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4
  have hTpos : 0 < T := by
    have ha0 := nonzero_of_not_five_dvd ha5
    have ha4 : 1 ≤ a ^ 4 := by nlinarith [sq_pos_of_ne_zero ha0]
    dsimp [T]
    nlinarith [sq_nonneg (a * b), sq_nonneg (b ^ 2)]
  have hTodd : Odd T := by
    rw [odd_iff_zmod2] at habodd ⊢
    dsimp [T]
    push_cast at habodd ⊢
    revert habodd
    generalize (a : ZMod 2) = x, (b : ZMod 2) = y
    revert x y; decide
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hbpos : 0 < b := by
    have hr : R = 5 * b * T := hb
    nlinarith
  have hbEven : Even b := by
    have he : Even (5 * b * T) := ⟨v ^ 2, by dsimp [R] at hb; linarith⟩
    rw [Int.even_mul, Int.even_mul] at he
    rcases he with (h5 | hb) | hT
    · norm_num at h5
    · exact hb
    · exact False.elim (Int.not_even_iff_odd.mpr hTodd hT)
  obtain ⟨B, hB⟩ := hbEven
  have hB' : b = 2 * B := by omega
  have hBpos : 0 < B := by omega
  have hbT : IsCoprime b T := by
    have hr : T = a ^ 4 + b * (10 * a ^ 2 * b + 5 * b ^ 3) := by dsimp [T]; ring
    rw [hr]
    exact hab.symm.pow_right.add_mul_left_right _
  have hBT : IsCoprime B T := by rw [hB'] at hbT; exact hbT.of_mul_left_right
  have hT5 : ¬ (5 : ℤ) ∣ T := by
    intro hd
    have ha4 : (5 : ℤ) ∣ a ^ 4 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 2 * a ^ 2 * b ^ 2 - b ^ 4, by dsimp [T] at hk; linarith⟩
    exact ha5 (Int.Prime.dvd_pow' Nat.prime_five ha4)
  have h5BT : IsCoprime (5 * B) T := (isCoprime_five_of_not_dvd hT5).symm.mul_left hBT
  have heBT : (5 * B) * T = v ^ 2 := by
    change R = 5 * b * T at hb
    dsimp [R] at hb
    rw [hB'] at hb
    nlinarith only [hb]
  obtain ⟨r, hr⟩ := square_of_pos_mul (by positivity : 0 < 5 * B) h5BT heBT
  obtain ⟨l, hl⟩ := square_of_pos_mul hTpos h5BT.symm
    (show T * (5 * B) = v ^ 2 by rw [mul_comm]; exact heBT)
  have hr5 : (5 : ℤ) ∣ r := Int.Prime.dvd_pow' Nat.prime_five
    (show (5 : ℤ) ∣ r ^ 2 by rw [← hr]; exact dvd_mul_right 5 B)
  obtain ⟨H, hH⟩ := hr5
  have hbclass : b = 10 * H ^ 2 := by rw [hH] at hr; nlinarith only [hr, hB']
  have haodd : Odd a := by
    obtain ⟨k, hk⟩ := habodd
    exact ⟨k - B, by omega⟩
  apply no_quartic_candidate b
  exact ⟨hbpos, a, l, hab, haodd, ha5, ⟨H, Or.inr hbclass⟩, hl.symm⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma primitive_eq {x y z : ℤ} (hcop : IsCoprime x y) (hz : z ≠ 0)
    (heq : x ^ 5 + y ^ 5 = 2 * z ^ 5) : x = y := by
  by_contra hxy
  obtain ⟨hxodd, hyodd⟩ := primitive_odd_xy hcop heq
  obtain ⟨u, hu⟩ := hxodd.add_odd hyodd
  let v := x - u
  have hx : x = u + v := by dsimp [v]; omega
  have hy : y = u - v := by dsimp [v]; omega
  have huv : IsCoprime u v := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx, hy]; ring⟩
  have hpar : Odd (u + v) := hx ▸ hxodd
  have hv5 : (5 : ℤ) ∣ v := by
    have hsub := primitive_five_dvd_sub hcop hz heq
    have h2v : (5 : ℤ) ∣ 2 * v := by
      convert hsub using 1
      rw [hx, hy]; ring
    rcases Int.Prime.dvd_mul' Nat.prime_five h2v with h2 | hv
    · norm_num at h2
    · exact hv
  have hu5 : ¬ (5 : ℤ) ∣ u := by
    intro hd
    exact not_isUnit_five (huv.isUnit_of_dvd' hd hv5)
  have hv0 : v ≠ 0 := by intro hv; apply hxy; omega
  let Q := u ^ 4 + 10 * u ^ 2 * v ^ 2 + 5 * v ^ 4
  have hprod : u * Q = z ^ 5 := by
    have h2 : 2 * (u * Q) = 2 * z ^ 5 := by
      rw [hx, hy] at heq
      dsimp [Q]
      linear_combination heq
    omega
  have huQ : IsCoprime u Q := by
    have hu5cop := isCoprime_five_of_not_dvd hu5
    have hc : IsCoprime u (5 * v ^ 4) := hu5cop.mul_right huv.pow_right
    have hr : Q = 5 * v ^ 4 + u * (u ^ 3 + 10 * u * v ^ 2) := by dsimp [Q]; ring
    rw [hr]
    exact hc.add_mul_left_right _
  obtain ⟨w, hw⟩ := pow5_of_coprime_int huQ.symm
    (show Q * u = z ^ 5 by rw [mul_comm]; exact hprod)
  exact quartic_fifth_impossible huv hpar hu5 hv5 hv0 hw

end OblathH1

/- Component: Main.lean -/

/-
Exact H1 of the Oblath reduction for Erdős672: integer fifth powers in arithmetic progression.
New formalization and integration by Hanan Beer (@hananzlt), following the classical
Dirichlet–Lebesgue proof. Mathematical source: V.-A. Lebesgue (1843),
Théorèmes nouveaux sur l'équation indéterminée x⁵+y⁵=az⁵.
The golden-integer and Dirichlet helper proof is reused from Pedro Bessa (@nijv), PR5575,
immutable head572ffd235e0a734035a1737d90d28c37c24417ee. Full attribution is in Dirichlet.lean.
The exact H1 reduction is due to @mudkjp, PR3625.
-/
namespace OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma all_int_aux : ∀ n : ℕ, ∀ x y z : ℤ, z.natAbs = n →
    x ^ 5 + y ^ 5 = 2 * z ^ 5 → x = y ∨ z = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y z hzn heq
    by_cases hz : z = 0
    · exact Or.inr hz
    by_cases hcop : IsCoprime x y
    · exact Or.inl (primitive_eq hcop hz heq)
    have hnc : ¬ Nat.Coprime x.natAbs y.natAbs :=
      fun h => hcop (Int.isCoprime_iff_nat_coprime.mpr h)
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    obtain ⟨X, hX⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨Y, hY⟩ := Int.natCast_dvd.mpr hpy
    have heq' : (p : ℤ) ^ 5 * (X ^ 5 + Y ^ 5) = 2 * z ^ 5 := by
      rw [hX, hY] at heq
      linear_combination heq
    have hpz : (p : ℤ) ∣ z := by
      by_cases hp2 : p = 2
      · subst p
        have hz5 : (2 : ℤ) ∣ z ^ 5 := by
          refine ⟨8 * (X ^ 5 + Y ^ 5), ?_⟩
          norm_num at heq'
          nlinarith only [heq']
        exact Int.Prime.dvd_pow' Nat.prime_two hz5
      · have hpProd : (p : ℤ) ∣ 2 * z ^ 5 := by
          rw [← heq']
          exact dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by decide : 5 ≠ 0)) _
        rcases Int.Prime.dvd_mul' hp hpProd with hp2dvd | hpz5
        · have hp2Nat : p ∣ 2 := by exact_mod_cast hp2dvd
          have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hp2Nat
          have hpge := hp.two_le
          exact False.elim (hp2 (by omega))
        · exact Int.Prime.dvd_pow' hp hpz5
    obtain ⟨Z, hZ⟩ := hpz
    have hZ0 : Z ≠ 0 := by intro h0; apply hz; simp [hZ, h0]
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have heq_small : X ^ 5 + Y ^ 5 = 2 * Z ^ 5 := by
      apply mul_left_cancel₀ (pow_ne_zero 5 hp0)
      rw [heq', hZ]
      ring
    have hlt : Z.natAbs < n := by
      rw [← hzn, hZ, Int.natAbs_mul, Int.natAbs_natCast]
      have hZpos := Int.natAbs_pos.mpr hZ0
      nlinarith [hp.two_le]
    rcases ih _ hlt X Y Z rfl heq_small with hXY | hZzero
    · exact Or.inl (by rw [hX, hY, hXY])
    · exact False.elim (hZ0 hZzero)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma all_int (x y z : ℤ) (h : x ^ 5 + y ^ 5 = 2 * z ^ 5) : x = y ∨ z = 0 :=
  all_int_aux _ x y z rfl h

end OblathH1

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
private theorem oma_h4_h1 : OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1.H1 := by
  intro x y z h
  exact OblathH1.all_int x y z h

end

section

/-!
# Step H2 of Erdős 672 (Obláth): No Positive Solutions to `g ^ 5 + 8 * b ^ 5 = s ^ 5`

We prove `OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1.H2`, namely that for positive natural
numbers `b` and `g`, `g ^ 5 + 8 * b ^ 5 ≠ s ^ 5`.

After dividing out any common prime factor of `g` and `s`, the equation splits into two branches
according to whether `5` divides `b`:
* When `5 ∤ b`, unique factorization in the PID `𝓞 (CyclotomicField 5 ℚ)` together with Kronecker's
  unit-conjugation identity forces a congruence modulo `5` incompatible with `g ^ 5 + 8 * b ^ 5 = s ^ 5`
  modulo `25`.
* When `5 ∣ b`, Dirichlet's 1825 fifth-power infinite descent in the Euclidean golden-ratio ring
  `QuadraticAlgebra ℤ 1 1` (`ℤ[(1 + √5)/2]`) yields an infinite descent on `b.natAbs`.
-/

open NumberField QuadraticAlgebra

namespace OMA672H2

/- ## Section 1: Euclidean Structure and Units of `ℤ[(1 + √5)/2]` -/

abbrev R := QuadraticAlgebra ℤ 1 1

lemma five_dvd_of_sq_dvd {x : ℤ} (h : (5 : ℤ) ∣ x ^ 2) : (5 : ℤ) ∣ x :=
  Int.Prime.dvd_pow' Nat.prime_five h

lemma not_isUnit_five : ¬ IsUnit (5 : ℤ) := by
  rw [Int.isUnit_iff]
  omega

lemma isCoprime_five_of_not_dvd {n : ℤ} (h : ¬ (5 : ℤ) ∣ n) : IsCoprime n 5 := by
  have hdiv : 5 * (n / 5) + n % 5 = n := Int.mul_ediv_add_emod n 5
  have hr0 : 0 ≤ n % 5 := Int.emod_nonneg n (by omega)
  have hr5 : n % 5 < 5 := Int.emod_lt_of_pos n (by omega)
  have hr_ne : n % 5 ≠ 0 := fun h0 => h (Int.dvd_of_emod_eq_zero h0)
  set q := n / 5
  set r := n % 5
  interval_cases r
  · exact absurd rfl hr_ne
  · exact ⟨1, -q, by omega⟩
  · exact ⟨3, -3 * q - 1, by omega⟩
  · exact ⟨2, -2 * q - 1, by omega⟩
  · exact ⟨-1, q + 1, by omega⟩

lemma even_iff_zmod2 (n : ℤ) : Even n ↔ (n : ZMod 2) = 0 := by
  have h2 : Even n ↔ ((2 : ℕ) : ℤ) ∣ n :=
    ⟨fun ⟨k, hk⟩ => ⟨k, by omega⟩, fun ⟨k, hk⟩ => ⟨k, by omega⟩⟩
  rw [h2, ← ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma odd_iff_zmod2 (n : ℤ) : Odd n ↔ (n : ZMod 2) = 1 := by
  rw [← Int.not_even_iff_odd, even_iff_zmod2]
  generalize (n : ZMod 2) = x
  revert x; decide

lemma norm_eq_zero_aux : ∀ n : ℕ, ∀ x y : ℤ, y.natAbs = n →
    (2 * x + y) ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn h
    have h5a : (5 : ℤ) ∣ (2 * x + y) := five_dvd_of_sq_dvd (h ▸ dvd_mul_right 5 _)
    obtain ⟨k, hk⟩ := h5a
    have hy2 : y ^ 2 = 5 * k ^ 2 := by
      have h25 : 25 * k ^ 2 = 5 * y ^ 2 := by
        calc 25 * k ^ 2 = (5 * k) ^ 2 := by ring
          _ = 5 * y ^ 2 := by rw [← hk, h]
      linarith
    have h5y : (5 : ℤ) ∣ y := five_dvd_of_sq_dvd (hy2 ▸ dvd_mul_right 5 _)
    obtain ⟨y1, rfl⟩ := h5y
    have h5x : (5 : ℤ) ∣ x := by
      have h2x : (5 : ℤ) ∣ 2 * x := ⟨k - y1, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h2x with h2 | hx
      · norm_num at h2
      · exact hx
    obtain ⟨x1, rfl⟩ := h5x
    by_cases hy0 : y1 = 0
    · subst hy0
      simp at h
      exact ⟨by omega, rfl⟩
    · have h1 : (2 * x1 + y1) ^ 2 = 5 * y1 ^ 2 := by
        have : 25 * (2 * x1 + y1) ^ 2 = 25 * (5 * y1 ^ 2) := by linear_combination h
        linarith
      have hlt : y1.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have hypos : 0 < y1.natAbs := Int.natAbs_pos.mpr hy0
        have h5 : (5 : ℤ).natAbs = 5 := rfl
        rw [h5]
        omega
      obtain ⟨hx1, hy1⟩ := ih _ hlt x1 y1 rfl h1
      exact ⟨by simp [hx1], by simp [hy1]⟩

lemma R_norm_eq_zero {z : R} (hz : z.norm = 0) : z = 0 := by
  have h4 : (2 * z.re + z.im) ^ 2 = 5 * z.im ^ 2 := by
    have : z.re * z.re + 1 * z.re * z.im - 1 * z.im * z.im = 0 := hz
    linear_combination 4 * this
  obtain ⟨hre, him⟩ := norm_eq_zero_aux _ z.re z.im rfl h4
  ext <;> simp [hre, him]

instance : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    have hn : a.norm * b.norm = 0 := by
      rw [← map_mul, hab, QuadraticAlgebra.norm_zero]
    rcases mul_eq_zero.mp hn with ha | hb
    · exact Or.inl (R_norm_eq_zero ha)
    · exact Or.inr (R_norm_eq_zero hb)

instance : IsDomain R := NoZeroDivisors.to_isDomain R

def nearestDiv (N d : ℤ) : ℤ :=
  let Ns := if 0 ≤ d then N else -N
  (2 * Ns + |d|) / (2 * |d|)

lemma nearestDiv_spec (N : ℤ) {d : ℤ} (hd : d ≠ 0) :
    4 * (N - nearestDiv N d * d) ^ 2 ≤ d ^ 2 := by
  dsimp [nearestDiv]
  set Ns := if 0 ≤ d then N else -N
  have hd_pos : 0 < |d| := abs_pos.mpr hd
  have h2d : 0 < 2 * |d| := by omega
  set q := (2 * Ns + |d|) / (2 * |d|)
  set r := (2 * Ns + |d|) % (2 * |d|)
  have hdiv : 2 * |d| * q + r = 2 * Ns + |d| := Int.mul_ediv_add_emod (2 * Ns + |d|) (2 * |d|)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hr1 : r < 2 * |d| := Int.emod_lt_of_pos _ h2d
  have hdiff : (N - q * d) ^ 2 = (Ns - q * |d|) ^ 2 := by
    by_cases h : 0 ≤ d
    · simp [Ns, h, abs_of_nonneg h]
    · have h' : d < 0 := lt_of_not_ge h
      simp [Ns, h, abs_of_neg h']
      ring
  rw [hdiff]
  have heq : 2 * (Ns - q * |d|) = r - |d| := by linear_combination -hdiv
  have hlin1 : -|d| ≤ 2 * (Ns - q * |d|) := by omega
  have hlin2 : 2 * (Ns - q * |d|) ≤ |d| := by omega
  have hsq : (2 * (Ns - q * |d|)) ^ 2 ≤ |d| ^ 2 := by nlinarith
  have habs : |d| ^ 2 = d ^ 2 := sq_abs d
  nlinarith

def R_div (a b : R) : R :=
  if b = 0 then 0 else
    let d := b.norm
    let num := a * star b
    ⟨nearestDiv num.re d, nearestDiv num.im d⟩

instance : EuclideanDomain R where
  quotient := R_div
  quotient_zero a := by simp [R_div]
  remainder a b := a - R_div a b * b
  quotient_mul_add_remainder_eq a b := by ring
  r a b := a.norm.natAbs < b.norm.natAbs
  r_wellFounded := InvImage.wf (fun z : R => z.norm.natAbs) wellFounded_lt
  remainder_lt a {b} hb := by
    have hd : b.norm ≠ 0 := fun h => hb (R_norm_eq_zero h)
    have hq : R_div a b = ⟨nearestDiv (a * star b).re b.norm, nearestDiv (a * star b).im b.norm⟩ := by
      simp [R_div, hb]
    set q := R_div a b
    set rem := a - q * b
    set d := b.norm
    set X := (a * star b).re - q.re * d
    set Y := (a * star b).im - q.im * d
    have hX : 4 * X ^ 2 ≤ d ^ 2 := by
      dsimp only [X]
      rw [hq]
      exact nearestDiv_spec _ hd
    have hY : 4 * Y ^ 2 ≤ d ^ 2 := by
      dsimp only [Y]
      rw [hq]
      exact nearestDiv_spec _ hd
    have hrem_mul : rem * star b = ⟨X, Y⟩ := by
      have hbb : b * star b = algebraMap ℤ R d := (algebraMap_norm_eq_mul_star b).symm
      calc rem * star b = a * star b - q * (b * star b) := by ring
        _ = a * star b - q * algebraMap ℤ R d := by rw [hbb]
        _ = ⟨X, Y⟩ := by ext <;> simp [X, Y]
    have hnorm_prod : rem.norm * d = X * X + 1 * X * Y - 1 * Y * Y := by
      have := congr_arg QuadraticAlgebra.norm hrem_mul
      rw [map_mul, QuadraticAlgebra.norm_star] at this
      exact this
    have hd2_pos : 1 ≤ d ^ 2 := by
      have : 0 < d ^ 2 := sq_pos_of_ne_zero hd
      omega
    have hup : rem.norm * d < d ^ 2 := by
      have : 16 * (rem.norm * d) = 20 * X ^ 2 - 4 * (X - 2 * Y) ^ 2 := by
        rw [hnorm_prod]; ring
      nlinarith [sq_nonneg (X - 2 * Y)]
    have hlo : -(d ^ 2) < rem.norm * d := by
      have : 16 * (rem.norm * d) = 4 * (2 * X + Y) ^ 2 - 20 * Y ^ 2 := by
        rw [hnorm_prod]; ring
      nlinarith [sq_nonneg (2 * X + Y)]
    have habs_lt : (rem.norm * d).natAbs < (d ^ 2).natAbs := by
      rw [← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs,
        abs_of_pos (show 0 < d ^ 2 by omega), abs_lt]
      exact ⟨hlo, hup⟩
    rw [Int.natAbs_mul, sq, Int.natAbs_mul] at habs_lt
    exact Nat.lt_of_mul_lt_mul_right habs_lt
  mul_left_not_lt a {b} hb := by
    rw [map_mul, Int.natAbs_mul]
    have hbn : b.norm ≠ 0 := fun h => hb (R_norm_eq_zero h)
    have hb1 : 1 ≤ b.norm.natAbs := Int.natAbs_pos.mpr hbn
    exact not_lt.mpr (Nat.le_mul_of_pos_right _ hb1)

def ω₀ : R := ⟨0, 1⟩
def ω_inv : R := ⟨-1, 1⟩

lemma ω₀_mul_inv : ω₀ * ω_inv = 1 := by
  ext <;> simp [ω₀, ω_inv]

lemma isUnit_ω₀ : IsUnit ω₀ :=
  ⟨⟨ω₀, ω_inv, ω₀_mul_inv, by rw [mul_comm]; exact ω₀_mul_inv⟩, rfl⟩

lemma isUnit_ω_inv : IsUnit ω_inv :=
  ⟨⟨ω_inv, ω₀, by rw [mul_comm]; exact ω₀_mul_inv, ω₀_mul_inv⟩, rfl⟩

lemma unit_form_neg {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ -v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  exact ⟨r, hr, -η, hη.neg, by ring⟩

lemma unit_form_mul_ω₀ {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ ω₀ * v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  rw [Finset.mem_range] at hr
  interval_cases r
  · exact ⟨1, by simp, η, hη, by ring⟩
  · exact ⟨2, by simp, η, hη, by ring⟩
  · exact ⟨3, by simp, η, hη, by ring⟩
  · exact ⟨4, by simp, η, hη, by ring⟩
  · exact ⟨0, by simp, ω₀ * η, isUnit_ω₀.mul hη, by ring⟩

lemma unit_form_mul_inv {v : R}
    (hv : ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ v = ω₀ ^ r * η ^ 5) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ ω_inv * v = ω₀ ^ r * η ^ 5 := by
  obtain ⟨r, hr, η, hη, rfl⟩ := hv
  rw [Finset.mem_range] at hr
  interval_cases r
  · refine ⟨4, by simp, ω_inv * η, isUnit_ω_inv.mul hη, ?_⟩
    have h4 : ω₀ ^ 4 * ω_inv ^ 5 = ω_inv := by
      calc ω₀ ^ 4 * ω_inv ^ 5 = (ω₀ * ω_inv) ^ 4 * ω_inv := by ring
        _ = ω_inv := by rw [ω₀_mul_inv]; ring
    calc ω_inv * (ω₀ ^ 0 * η ^ 5) = ω_inv * η ^ 5 := by ring
      _ = (ω₀ ^ 4 * ω_inv ^ 5) * η ^ 5 := by rw [h4]
      _ = ω₀ ^ 4 * (ω_inv * η) ^ 5 := by ring
  · refine ⟨0, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 1 * η ^ 5) = (ω₀ * ω_inv) * η ^ 5 := by ring
      _ = ω₀ ^ 0 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨1, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 2 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 1 * η ^ 5) := by ring
      _ = ω₀ ^ 1 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨2, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 3 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 2 * η ^ 5) := by ring
      _ = ω₀ ^ 2 * η ^ 5 := by rw [ω₀_mul_inv]; ring
  · refine ⟨3, by simp, η, hη, ?_⟩
    calc ω_inv * (ω₀ ^ 4 * η ^ 5) = (ω₀ * ω_inv) * (ω₀ ^ 3 * η ^ 5) := by ring
      _ = ω₀ ^ 3 * η ^ 5 := by rw [ω₀_mul_inv]; ring

lemma unit_form_aux : ∀ n : ℕ, ∀ u : R, u.re.natAbs + u.im.natAbs = n →
    (u.norm = 1 ∨ u.norm = -1) →
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ u = ω₀ ^ r * η ^ 5 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hn hnorm
    set x := u.re
    set y := u.im
    have hu : u = ⟨x, y⟩ := (QuadraticAlgebra.mk_eta u).symm
    have hxy : x * x + 1 * x * y - 1 * y * y = 1 ∨ x * x + 1 * x * y - 1 * y * y = -1 := hnorm
    by_cases hy0 : y = 0
    · rcases hxy with h1 | h1
      · rw [hy0] at h1
        have hx1 : x = 1 ∨ x = -1 := sq_eq_one_iff.mp (by linarith)
        rcases hx1 with hx1 | hx1
        · exact ⟨0, by simp, 1, isUnit_one, by rw [hu, hx1, hy0]; ext <;> simp⟩
        · refine ⟨0, by simp, -1, isUnit_one.neg, ?_⟩
          rw [show (-1 : R) ^ 5 = -1 by ring, hu, hx1, hy0]
          ext <;> simp
      · exfalso
        rw [hy0] at h1
        nlinarith [sq_nonneg x]
    · by_cases hx0 : x = 0
      · rcases hxy with h1 | h1
        · exfalso
          rw [hx0] at h1
          nlinarith [sq_nonneg y]
        · rw [hx0] at h1
          have hy1 : y = 1 ∨ y = -1 := sq_eq_one_iff.mp (by linarith)
          rcases hy1 with hy1 | hy1
          · exact ⟨1, by simp, 1, isUnit_one, by rw [hu, hx0, hy1]; ext <;> simp [ω₀]⟩
          · refine ⟨1, by simp, -1, isUnit_one.neg, ?_⟩
            rw [show (-1 : R) ^ 5 = -1 by ring, hu, hx0, hy1]
            ext <;> simp [ω₀]
      · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos <;>
        rcases lt_or_gt_of_ne hy0 with hyneg | hypos
        · set u' := ω_inv * (-u)
          have hu'_eq : u' = ⟨x - y, -x⟩ := by
            dsimp [u']; rw [hu]; ext
            · simp [ω_inv]; ring
            · simp [ω_inv]
          have hxley : y ≤ x := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hinv_n : ω_inv.norm = -1 := by decide
            rw [map_mul, QuadraticAlgebra.norm_neg, hinv_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_neg (unit_form_mul_ω₀ (ih _ hlt u' rfl hu'_norm))
          have heq : -(ω₀ * u') = u := by
            dsimp [u']
            calc -(ω₀ * (ω_inv * -u)) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω₀ * (-u)
          have hu'_eq : u' = ⟨-y, -x - y⟩ := by
            dsimp [u']; rw [hu]; ext
            · simp [ω₀]
            · simp [ω₀]; ring
          have hy_le : y ≤ -x := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hω_n : ω₀.norm = -1 := by decide
            rw [map_mul, QuadraticAlgebra.norm_neg, hω_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_neg (unit_form_mul_inv (ih _ hlt u' rfl hu'_norm))
          have heq : -(ω_inv * u') = u := by
            dsimp [u']
            calc -(ω_inv * (ω₀ * -u)) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω₀ * u
          have hu'_eq : u' = ⟨y, x + y⟩ := by
            dsimp [u']; rw [hu]; ext <;> simp [ω₀]
          have hxy_ge : 0 ≤ x + y := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hω_n : ω₀.norm = -1 := by decide
            rw [map_mul, hω_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_mul_inv (ih _ hlt u' rfl hu'_norm)
          have heq : ω_inv * u' = u := by
            dsimp [u']
            calc ω_inv * (ω₀ * u) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1
        · set u' := ω_inv * u
          have hu'_eq : u' = ⟨-x + y, x⟩ := by
            dsimp [u']; rw [hu]; ext <;> simp [ω_inv]
          have hxley : x ≤ y := by
            by_contra hlt
            have := not_le.mp hlt
            rcases hxy with h1 | h1 <;> nlinarith
          have hlt : u'.re.natAbs + u'.im.natAbs < n := by
            rw [← hn, hu'_eq]; dsimp only; omega
          have hu'_norm : u'.norm = 1 ∨ u'.norm = -1 := by
            have hinv_n : ω_inv.norm = -1 := by decide
            rw [map_mul, hinv_n]
            rcases hnorm with h | h <;> rw [h] <;> simp
          have h1 := unit_form_mul_ω₀ (ih _ hlt u' rfl hu'_norm)
          have heq : ω₀ * u' = u := by
            dsimp [u']
            calc ω₀ * (ω_inv * u) = (ω₀ * ω_inv) * u := by ring
              _ = u := by rw [ω₀_mul_inv, one_mul]
          rwa [heq] at h1

lemma unit_form (u : R) (hu : IsUnit u) :
    ∃ r ∈ Finset.range 5, ∃ η : R, IsUnit η ∧ u = ω₀ ^ r * η ^ 5 := by
  have hn : IsUnit u.norm := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
  exact unit_form_aux _ u rfl (Int.isUnit_iff.mp hn)

/- ## Section 2: Dirichlet's 1825 Lemma and Second-Case Infinite Descent -/

lemma mk_pow5 (c d : ℤ) :
    (⟨c, d⟩ : R) ^ 5 =
      ⟨c ^ 5 + 10 * c ^ 3 * d ^ 2 + 10 * c ^ 2 * d ^ 3 + 10 * c * d ^ 4 + 3 * d ^ 5,
       5 * d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4)⟩ := by
  ext <;> simp [pow_succ, pow_zero] <;> ring

lemma isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime n 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨1, -k, by ring⟩

lemma zmod2_im_zero : ∀ c d : ZMod 2,
    d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4) = 0 → d = 0 := by
  decide

theorem dirichlet_lemma {P Q w : ℤ} (hcop : IsCoprime P Q) (h5P : ¬ (5 : ℤ) ∣ P)
    (h5Q : (5 : ℤ) ∣ Q) (hpar : Odd (P + Q)) (hw : P ^ 2 - 5 * Q ^ 2 = w ^ 5) :
    ∃ a b : ℤ, P = a * (a ^ 4 + 50 * a ^ 2 * b ^ 2 + 125 * b ^ 4) ∧
      Q = 5 * b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) := by
  set ρ : R := ⟨P - Q, 2 * Q⟩
  set ρ' : R := star ρ
  have hprod : ρ * ρ' = (w : R) ^ 5 := by
    have hnorm : ρ.norm = P ^ 2 - 5 * Q ^ 2 := by
      simp only [QuadraticAlgebra.norm_def, ρ]
      ring
    calc ρ * ρ' = algebraMap ℤ R ρ.norm := (algebraMap_norm_eq_mul_star ρ).symm
      _ = algebraMap ℤ R (w ^ 5) := by rw [hnorm, hw]
      _ = (w : R) ^ 5 := by simp
  have hcop_ρ : IsCoprime ρ ρ' := by
    have hP5 : IsCoprime P 5 := isCoprime_five_of_not_dvd h5P
    have hA : IsCoprime (P ^ 2 - 5 * Q ^ 2) P := by
      have h1 : IsCoprime (5 * Q ^ 2) P := (hP5.symm.mul_left hcop.symm.pow_left)
      have h2 : IsCoprime (-(5 * Q ^ 2)) P := h1.neg_left
      have he : P ^ 2 - 5 * Q ^ 2 = -(5 * Q ^ 2) + P * P := by ring
      rw [he]
      exact h2.add_mul_left_left P
    have hB : IsCoprime (P ^ 2 - 5 * Q ^ 2) 2 := by
      apply isCoprime_two_of_odd
      obtain ⟨k, hk⟩ := hpar
      refine ⟨2 * k ^ 2 + 2 * k - 2 * k * Q - Q - 2 * Q ^ 2, ?_⟩
      have hP : P = 2 * k + 1 - Q := by omega
      rw [hP]; ring
    obtain ⟨A, B, hAB⟩ := hA.mul_right hB
    refine ⟨(A : R) * ρ' + B, B, ?_⟩
    have h1 : ((A * (P ^ 2 - 5 * Q ^ 2) + B * (P * 2) : ℤ) : R) = 1 := by
      rw [hAB]; simp
    have hsum : ρ + ρ' = ((P * 2 : ℤ) : R) := by
      ext
      · simp [ρ, ρ']; ring
      · simp [ρ, ρ']
    have hmul : ρ * ρ' = ((P ^ 2 - 5 * Q ^ 2 : ℤ) : R) := by
      rw [hprod, hw]; push_cast; rfl
    calc ((A : R) * ρ' + B) * ρ + (B : R) * ρ'
        = (A : R) * (ρ * ρ') + (B : R) * (ρ + ρ') := by ring
      _ = ((A * (P ^ 2 - 5 * Q ^ 2) + B * (P * 2) : ℤ) : R) := by
          rw [hmul, hsum]; push_cast; ring
      _ = 1 := h1
  obtain ⟨γ0, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop_ρ hprod
  obtain ⟨r, hr, η, -, hη⟩ := unit_form (u0 : R) u0.isUnit
  set γ : R := γ0 * η
  have hρ : ρ = ω₀ ^ r * γ ^ 5 := by
    calc ρ = γ0 ^ 5 * (u0 : R) := hu0.symm
      _ = γ0 ^ 5 * (ω₀ ^ r * η ^ 5) := by rw [hη]
      _ = ω₀ ^ r * γ ^ 5 := by dsimp [γ]; ring
  set c := γ.re
  set d := γ.im
  have hγ_mk : γ = ⟨c, d⟩ := (QuadraticAlgebra.mk_eta γ).symm
  set X5 := c ^ 5 + 10 * c ^ 3 * d ^ 2 + 10 * c ^ 2 * d ^ 3 + 10 * c * d ^ 4 + 3 * d ^ 5
  set Y5 := d * (c ^ 4 + 2 * c ^ 3 * d + 4 * c ^ 2 * d ^ 2 + 3 * c * d ^ 3 + d ^ 4)
  have hγ5 : γ ^ 5 = ⟨X5, 5 * Y5⟩ := by
    rw [hγ_mk, mk_pow5]
    dsimp [X5, Y5]
    ext
    · simp
    · simp; ring
  rw [hγ5] at hρ
  obtain ⟨Q', rfl⟩ := h5Q
  have h5_not_re : ¬ (5 : ℤ) ∣ (P - 5 * Q') := by
    intro hd
    exact h5P (by obtain ⟨m, hm⟩ := hd; exact ⟨m + Q', by omega⟩)
  rw [Finset.mem_range] at hr
  have hr0 : r = 0 := by
    interval_cases r
    · rfl
    · exfalso
      have hre : P - 5 * Q' = 5 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀] at this; linarith
      exact h5_not_re ⟨Y5, hre⟩
    · exfalso
      have hre : P - 5 * Q' = X5 + 5 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_two] at this; linarith
      have him : 10 * Q' = X5 + 10 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_two] at this; linarith
      exact h5_not_re ⟨2 * Q' - Y5, by omega⟩
    · exfalso
      have hre : P - 5 * Q' = X5 + 10 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have him : 10 * Q' = 2 * X5 + 15 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have h5X : (5 : ℤ) ∣ 2 * X5 := ⟨2 * Q' - 3 * Y5, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h5X with h2 | hX
      · norm_num at h2
      · obtain ⟨k, hk⟩ := hX
        exact h5_not_re ⟨k + 2 * Y5, by omega⟩
    · exfalso
      have hre : P - 5 * Q' = 2 * X5 + 15 * Y5 := by
        have := congr_arg QuadraticAlgebra.re hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have him : 10 * Q' = 3 * X5 + 25 * Y5 := by
        have := congr_arg QuadraticAlgebra.im hρ
        simp [ρ, ω₀, pow_succ, pow_zero] at this; linarith
      have h5X : (5 : ℤ) ∣ 3 * X5 := ⟨2 * Q' - 5 * Y5, by omega⟩
      rcases Int.Prime.dvd_mul' Nat.prime_five h5X with h3 | hX
      · norm_num at h3
      · obtain ⟨k, hk⟩ := hX
        exact h5_not_re ⟨2 * k + 3 * Y5, by omega⟩
  subst hr0
  simp only [pow_zero, one_mul] at hρ
  have hre : P - 5 * Q' = X5 := congr_arg QuadraticAlgebra.re hρ
  have him : 2 * Q' = Y5 := by
    have := congr_arg QuadraticAlgebra.im hρ
    simp only [ρ] at this
    omega
  have hd_dvd : (2 : ℤ) ∣ d := by
    change ((2 : ℕ) : ℤ) ∣ d
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply zmod2_im_zero (c : ZMod 2) (d : ZMod 2)
    have hY2 : (Y5 : ZMod 2) = 0 := by
      rw [← him]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
    dsimp [Y5] at hY2
    push_cast at hY2
    exact hY2
  obtain ⟨b, hb⟩ := hd_dvd
  refine ⟨c + b, b, ?_, ?_⟩
  · have hX_eq : 2 * X5 + 5 * Y5 =
        2 * ((c + b) * ((c + b) ^ 4 + 50 * (c + b) ^ 2 * b ^ 2 + 125 * b ^ 4)) := by
      dsimp [X5, Y5]; rw [hb]; ring
    linarith [hre, him, hX_eq]
  · have hY_eq : Y5 = 2 * b * ((c + b) ^ 4 + 10 * (c + b) ^ 2 * b ^ 2 + 5 * b ^ 4) := by
      dsimp [Y5]; rw [hb]; ring
    linarith [him, hY_eq]

lemma pow5_of_coprime_int {a b c : ℤ} (h : IsCoprime a b) (habc : a * b = c ^ 5) :
    ∃ d : ℤ, a = d ^ 5 :=
  Int.eq_pow_of_mul_eq_pow_odd_left h (by decide) habc

lemma odd_add_of_odd_PQ5 {a b : ℤ}
    (h : Odd (a * (a ^ 4 + 50 * a ^ 2 * b ^ 2 + 125 * b ^ 4) +
      5 * b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4))) : Odd (a + b) := by
  rw [odd_iff_zmod2] at h ⊢
  push_cast at h ⊢
  revert h
  generalize (a : ZMod 2) = x, (b : ZMod 2) = y
  revert x y; decide

def Eq2 (a b Z : ℤ) (M N : ℕ) : Prop :=
  1 ≤ M ∧ 1 ≤ N ∧ IsCoprime a b ∧ Odd (a + b) ∧ ¬ (5 : ℤ) ∣ a ∧ b ≠ 0 ∧ IsCoprime Z 10 ∧
    b * (a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4) = 2 ^ M * 5 ^ N * Z ^ 5

theorem no_eq2_aux : ∀ n : ℕ, ∀ a b Z : ℤ, ∀ M N : ℕ, b.natAbs = n → Eq2 a b Z M N → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b Z M N hn ⟨hM, hN, hcop, hodd, h5a, hb0, hZ10, heq⟩
    set Q := a ^ 4 + 10 * a ^ 2 * b ^ 2 + 5 * b ^ 4
    have hQ_odd : Odd Q := by
      rw [odd_iff_zmod2] at hodd ⊢
      dsimp [Q]
      push_cast at hodd ⊢
      revert hodd
      generalize (a : ZMod 2) = x, (b : ZMod 2) = y
      revert x y; decide
    have h5Q : ¬ (5 : ℤ) ∣ Q := by
      intro hd
      have h5a4 : (5 : ℤ) ∣ a ^ 4 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨k - 2 * a ^ 2 * b ^ 2 - b ^ 4, by dsimp [Q] at hk; linarith⟩
      exact h5a (Int.Prime.dvd_pow' Nat.prime_five h5a4)
    have hQ2 : IsCoprime Q 2 := isCoprime_two_of_odd hQ_odd
    have hQ5 : IsCoprime Q 5 := isCoprime_five_of_not_dvd h5Q
    have hQ_25 : IsCoprime Q (2 ^ M * 5 ^ N) := hQ2.pow_right.mul_right hQ5.pow_right
    have hdvd_b : (2 ^ M * 5 ^ N : ℤ) ∣ b := by
      refine hQ_25.symm.dvd_of_dvd_mul_right ?_
      exact ⟨Z ^ 5, heq⟩
    obtain ⟨b', hb'⟩ := hdvd_b
    have h25_ne : (2 ^ M * 5 ^ N : ℤ) ≠ 0 := by positivity
    have heq' : b' * Q = Z ^ 5 := by
      apply mul_left_cancel₀ h25_ne
      calc 2 ^ M * 5 ^ N * (b' * Q) = (2 ^ M * 5 ^ N * b') * Q := by ring
        _ = b * Q := by rw [← hb']
        _ = 2 ^ M * 5 ^ N * Z ^ 5 := heq
    have hbQ : IsCoprime b Q := by
      have hba4 : IsCoprime b (a ^ 4) := hcop.symm.pow_right
      have he : Q = a ^ 4 + b * (10 * a ^ 2 * b + 5 * b ^ 3) := by dsimp [Q]; ring
      rw [he]
      exact hba4.add_mul_left_right _
    have hb'Q : IsCoprime b' Q := by
      rw [hb'] at hbQ
      exact hbQ.of_mul_left_right
    obtain ⟨c, hc⟩ := pow5_of_coprime_int hb'Q heq'
    obtain ⟨d, hd⟩ := pow5_of_coprime_int hb'Q.symm (by rw [mul_comm]; exact heq')
    have hb_eq : b = 2 ^ M * 5 ^ N * c ^ 5 := by rw [hb', hc]
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hb0; rw [hb_eq]; ring
    have hc10 : IsCoprime (c ^ 2) 10 := by
      have hZ5_10 : IsCoprime (Z ^ 5) 10 := hZ10.pow_left
      rw [← heq', hc] at hZ5_10
      obtain ⟨u1, u2, hu12⟩ := hZ5_10.of_mul_left_left
      have hc_10 : IsCoprime c 10 := ⟨u1 * c ^ 4, u2, by linear_combination hu12⟩
      exact hc_10.pow_left
    have h5b : (5 : ℤ) ∣ b := by
      refine ⟨2 ^ M * 5 ^ (N - 1) * c ^ 5, ?_⟩
      rw [hb_eq]
      have hN' : 5 ^ N = (5 : ℤ) * 5 ^ (N - 1) := by
        conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ']
      rw [hN']; ring
    have h2b : Even b := by
      refine ⟨2 ^ (M - 1) * 5 ^ N * c ^ 5, ?_⟩
      rw [hb_eq]
      have hM' : 2 ^ M = (2 : ℤ) * 2 ^ (M - 1) := by
        conv_lhs => rw [show M = (M - 1) + 1 by omega, pow_succ']
      rw [hM']; ring
    set P1 := a ^ 2 + 5 * b ^ 2
    set R1 := 2 * b ^ 2
    have hPR_odd : Odd (P1 + R1) := by
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨m, hm⟩ := h2b
      refine ⟨2 * (k - m) ^ 2 + 2 * (k - m) + 14 * m ^ 2, ?_⟩
      have ha : a = 2 * (k - m) + 1 := by omega
      dsimp [P1, R1]; rw [ha, hm]; ring
    have h5P1 : ¬ (5 : ℤ) ∣ P1 := by
      intro hd
      have h5a2 : (5 : ℤ) ∣ a ^ 2 := by
        obtain ⟨k, hk⟩ := hd
        exact ⟨k - b ^ 2, by dsimp [P1] at hk; linarith⟩
      exact h5a (five_dvd_of_sq_dvd h5a2)
    have h5R1 : (5 : ℤ) ∣ R1 := by
      obtain ⟨k, hk⟩ := h5b
      exact ⟨10 * k ^ 2, by dsimp [R1]; rw [hk]; ring⟩
    have hcop_PR : IsCoprime P1 R1 := by
      have hP1_b : IsCoprime P1 b := by
        have he : P1 = a ^ 2 + b * (5 * b) := by dsimp [P1]; ring
        rw [he]
        exact hcop.pow_left.add_mul_left_left _
      have hP1_2 : IsCoprime P1 2 := by
        apply isCoprime_two_of_odd
        obtain ⟨k, hk⟩ := hPR_odd
        exact ⟨k - b ^ 2, by dsimp [R1] at hk; omega⟩
      exact hP1_2.mul_right hP1_b.pow_right
    have hd5 : P1 ^ 2 - 5 * R1 ^ 2 = d ^ 5 := by
      have he : P1 ^ 2 - 5 * R1 ^ 2 = Q := by dsimp [P1, R1, Q]; ring
      rw [he, hd]
    obtain ⟨a1, b1, ha1, hb1⟩ := dirichlet_lemma hcop_PR h5P1 h5R1 hPR_odd hd5
    have hcop1 : IsCoprime a1 b1 := by
      have h := hcop_PR
      rw [ha1, hb1] at h
      exact h.of_mul_left_left.of_mul_right_left.of_mul_right_right
    have hodd1 : Odd (a1 + b1) := by
      apply odd_add_of_odd_PQ5
      rw [← ha1, ← hb1]
      exact hPR_odd
    have h5a1 : ¬ (5 : ℤ) ∣ a1 := by
      intro hd
      exact h5P1 (ha1 ▸ dvd_mul_of_dvd_left hd _)
    have ha1_ne : a1 ≠ 0 := fun h0 => h5a1 (by simp [h0])
    set Q1 := a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4
    have hQ1_pos : 1 ≤ Q1 := by
      have : 0 < a1 ^ 2 := sq_pos_of_ne_zero ha1_ne
      have : 1 ≤ a1 ^ 4 := by nlinarith
      dsimp [Q1]
      nlinarith [sq_nonneg (a1 * b1), sq_nonneg (b1 ^ 2)]
    have hb1_pos : 0 < b1 := by
      have hR1_pos : 0 < R1 := by dsimp [R1]; positivity
      rw [hb1] at hR1_pos
      nlinarith
    have hb1_lt : b1.natAbs < n := by
      have hb1_2 : b1 ^ 2 ≤ b1 ^ 4 := by nlinarith [sq_nonneg (b1 - 1)]
      have h5b1_sq : 5 * b1 ^ 2 ≤ 2 * b ^ 2 := by
        have h1 : b1 ≤ Q1 := by dsimp [Q1]; nlinarith
        have h2 : 5 * b1 ^ 2 ≤ 5 * b1 * Q1 := by nlinarith
        linarith [hb1]
      have hbsq : b1 ^ 2 < b ^ 2 := by nlinarith
      have hlt_abs : |b1| < |b| := by
        rw [← sq_lt_sq]
        exact hbsq
      rw [← hn, ← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs]
      exact hlt_abs
    have heq1 : b1 * Q1 = 2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5 := by
      have h5pow : (5 : ℤ) ^ (2 * N) = 5 * 5 ^ (2 * N - 1) := by
        conv_lhs => rw [show 2 * N = (2 * N - 1) + 1 by omega, pow_succ']
      have hR : 5 * (b1 * Q1) = 5 * (2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5) := by
        calc 5 * (b1 * Q1) = R1 := by dsimp [Q1]; linarith [hb1]
          _ = 2 * (2 ^ M * 5 ^ N * c ^ 5) ^ 2 := by dsimp [R1]; rw [hb_eq]
          _ = 2 * 2 ^ (2 * M) * 5 ^ (2 * N) * (c ^ 2) ^ 5 := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
              ring_nf
          _ = 5 * (2 ^ (2 * M + 1) * 5 ^ (2 * N - 1) * (c ^ 2) ^ 5) := by
              rw [h5pow, pow_succ]; ring
      linarith
    exact ih _ hb1_lt a1 b1 (c ^ 2) (2 * M + 1) (2 * N - 1) rfl
      ⟨by omega, by omega, hcop1, hodd1, h5a1, hb1_pos.ne', hc10, heq1⟩

theorem no_sol_case2 {x y Z : ℤ} {m n : ℕ} (hm : 1 ≤ m) (hn : 3 ≤ n)
    (hcop : IsCoprime x y) (hZ10 : IsCoprime Z 10) (hZ0 : Z ≠ 0) :
    x ^ 5 + y ^ 5 ≠ 2 ^ m * 5 ^ n * Z ^ 5 := by
  intro h
  have hxy_even : Even (x + y) := by
    have hm' : 2 ^ m = (2 : ℤ) * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    have h2 : Even (x ^ 5 + y ^ 5) := ⟨2 ^ (m - 1) * 5 ^ n * Z ^ 5, by rw [h, hm']; ring⟩
    rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at h2
    rwa [Int.even_add]
  obtain ⟨u, hu⟩ := hxy_even
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := by obtain ⟨r, hr⟩ := hx; exact ⟨u - r, by omega⟩
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
      have hd : (2 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hx.two_dvd hy.two_dvd
      rw [hg] at hd; norm_num at hd
    · exact hx
  set v := x - u
  have hx' : x = u + v := by omega
  have hy' : y = u - v := by omega
  have hpar : Odd (u + v) := hx' ▸ hxodd
  have huv : IsCoprime u v := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx', hy']; ring⟩
  have h5_xy : (5 : ℤ) ∣ (x + y) := by
    have hn' : 5 ^ n = (5 : ℤ) * 5 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
    have h5_pow : (5 : ℤ) ∣ (x + y) ^ 5 := by
      refine ⟨2 ^ m * 5 ^ (n - 1) * Z ^ 5 + x * y * (x + y) * (x ^ 2 + x * y + y ^ 2), ?_⟩
      calc (x + y) ^ 5 = (x ^ 5 + y ^ 5) + 5 * (x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by ring
        _ = 2 ^ m * 5 ^ n * Z ^ 5 + 5 * (x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by rw [h]
        _ = 5 * (2 ^ m * 5 ^ (n - 1) * Z ^ 5 + x * y * (x + y) * (x ^ 2 + x * y + y ^ 2)) := by
            rw [hn']; ring
    exact Int.Prime.dvd_pow' Nat.prime_five h5_pow
  have h5u : (5 : ℤ) ∣ u := by
    have h2u : (5 : ℤ) ∣ 2 * u := by rwa [show 2 * u = x + y by omega]
    rcases Int.Prime.dvd_mul' Nat.prime_five h2u with h2 | h5
    · norm_num at h2
    · exact h5
  obtain ⟨U, rfl⟩ := h5u
  have h5v : ¬ (5 : ℤ) ∣ v := by
    intro hd
    exact not_isUnit_five (huv.isUnit_of_dvd' (dvd_mul_right 5 U) hd)
  have hUv : IsCoprime U v := huv.of_mul_left_right
  have hU_odd : Odd (U + v) := by
    obtain ⟨k, hk⟩ := hpar
    exact ⟨k - 2 * U, by omega⟩
  set Q' := v ^ 4 + 50 * U ^ 2 * v ^ 2 + 125 * U ^ 4
  have heqU : U * Q' = 2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5 := by
    have hm' : 2 ^ m = (2 : ℤ) * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    have hn' : (5 : ℤ) ^ n = 25 * 5 ^ (n - 2) := by
      calc (5 : ℤ) ^ n = 5 ^ ((n - 2) + 2) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 25 * 5 ^ (n - 2) := by rw [pow_add]; ring
    have h50 : 50 * (U * Q') = 50 * (2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5) := by
      calc 50 * (U * Q') = (5 * U + v) ^ 5 + (5 * U - v) ^ 5 := by dsimp [Q']; ring
        _ = x ^ 5 + y ^ 5 := by rw [← hx', ← hy']
        _ = 2 ^ m * 5 ^ n * Z ^ 5 := h
        _ = 50 * (2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5) := by rw [hm', hn']; ring
    linarith
  have hQ'_odd : Odd Q' := by
    rw [odd_iff_zmod2] at hU_odd ⊢
    dsimp [Q']
    push_cast at hU_odd ⊢
    revert hU_odd
    generalize (U : ZMod 2) = x1, (v : ZMod 2) = y1
    revert x1 y1; decide
  have h5Q' : ¬ (5 : ℤ) ∣ Q' := by
    intro hd
    have h5v4 : (5 : ℤ) ∣ v ^ 4 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 10 * U ^ 2 * v ^ 2 - 25 * U ^ 4, by dsimp [Q'] at hk; linarith⟩
    exact h5v (Int.Prime.dvd_pow' Nat.prime_five h5v4)
  have hQ'2 : IsCoprime Q' 2 := isCoprime_two_of_odd hQ'_odd
  have hQ'5 : IsCoprime Q' 5 := isCoprime_five_of_not_dvd h5Q'
  have hQ'_25 : IsCoprime Q' (2 ^ (m - 1) * 5 ^ (n - 2)) := hQ'2.pow_right.mul_right hQ'5.pow_right
  have hdvd_U : (2 ^ (m - 1) * 5 ^ (n - 2) : ℤ) ∣ U := by
    refine hQ'_25.symm.dvd_of_dvd_mul_right ?_
    exact ⟨Z ^ 5, heqU⟩
  obtain ⟨U', hU'⟩ := hdvd_U
  have h25_ne : (2 ^ (m - 1) * 5 ^ (n - 2) : ℤ) ≠ 0 := by positivity
  have heqU' : U' * Q' = Z ^ 5 := by
    apply mul_left_cancel₀ h25_ne
    calc 2 ^ (m - 1) * 5 ^ (n - 2) * (U' * Q') = U * Q' := by rw [hU']; ring
      _ = 2 ^ (m - 1) * 5 ^ (n - 2) * Z ^ 5 := heqU
  have hUQ' : IsCoprime U Q' := by
    have he : Q' = v ^ 4 + U * (50 * U * v ^ 2 + 125 * U ^ 3) := by dsimp [Q']; ring
    rw [he]
    exact hUv.pow_right.add_mul_left_right _
  have hU'Q' : IsCoprime U' Q' := by
    rw [hU'] at hUQ'
    exact hUQ'.of_mul_left_right
  obtain ⟨t, ht⟩ := pow5_of_coprime_int hU'Q' heqU'
  obtain ⟨w, hw⟩ := pow5_of_coprime_int hU'Q'.symm (by rw [mul_comm]; exact heqU')
  have hU_eq : U = 2 ^ (m - 1) * 5 ^ (n - 2) * t ^ 5 := by rw [hU', ht]
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hZ0
    rw [ht, zero_pow (by norm_num), zero_mul] at heqU'
    exact pow_eq_zero_iff (by norm_num) |>.mp heqU'.symm
  have ht10 : IsCoprime (t ^ 2) 10 := by
    have hZ5_10 : IsCoprime (Z ^ 5) 10 := hZ10.pow_left
    rw [← heqU', ht] at hZ5_10
    obtain ⟨u1, u2, hu12⟩ := hZ5_10.of_mul_left_left
    have ht_10 : IsCoprime t 10 := ⟨u1 * t ^ 4, u2, by linear_combination hu12⟩
    exact ht_10.pow_left
  set P2 := v ^ 2 + 25 * U ^ 2
  set R2 := 10 * U ^ 2
  have hPR2_odd : Odd (P2 + R2) := by
    obtain ⟨k, hk⟩ := hU_odd
    rcases Int.even_or_odd U with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hv' : v = 2 * (k - j) + 1 := by omega
      exact ⟨2 * (k - j) ^ 2 + 2 * (k - j) + 70 * j ^ 2, by dsimp [P2, R2]; rw [hj, hv']; ring⟩
    · have hv' : v = 2 * (k - j) := by omega
      exact ⟨2 * (k - j) ^ 2 + 70 * j ^ 2 + 70 * j + 17, by dsimp [P2, R2]; rw [hj, hv']; ring⟩
  have h5P2 : ¬ (5 : ℤ) ∣ P2 := by
    intro hd
    have h5v2 : (5 : ℤ) ∣ v ^ 2 := by
      obtain ⟨k, hk⟩ := hd
      exact ⟨k - 5 * U ^ 2, by dsimp [P2] at hk; linarith⟩
    exact h5v (five_dvd_of_sq_dvd h5v2)
  have h5R2 : (5 : ℤ) ∣ R2 := ⟨2 * U ^ 2, by dsimp [R2]; ring⟩
  have hcop_PR2 : IsCoprime P2 R2 := by
    have hP2_U : IsCoprime P2 U := by
      have he : P2 = v ^ 2 + U * (25 * U) := by dsimp [P2]; ring
      rw [he]
      exact hUv.symm.pow_left.add_mul_left_left _
    have hP2_2 : IsCoprime P2 2 := by
      apply isCoprime_two_of_odd
      obtain ⟨k, hk⟩ := hPR2_odd
      exact ⟨k - 5 * U ^ 2, by dsimp [R2] at hk; omega⟩
    have hP2_5 : IsCoprime P2 5 := isCoprime_five_of_not_dvd h5P2
    have h10 : R2 = (2 * 5) * U ^ 2 := by ring
    rw [h10]
    exact (hP2_2.mul_right hP2_5).mul_right hP2_U.pow_right
  have hw5 : P2 ^ 2 - 5 * R2 ^ 2 = w ^ 5 := by
    have he : P2 ^ 2 - 5 * R2 ^ 2 = Q' := by dsimp [P2, R2, Q']; ring
    rw [he, hw]
  obtain ⟨a1, b1, ha1, hb1⟩ := dirichlet_lemma hcop_PR2 h5P2 h5R2 hPR2_odd hw5
  have hcop1 : IsCoprime a1 b1 := by
    have hc := hcop_PR2
    rw [ha1, hb1] at hc
    exact hc.of_mul_left_left.of_mul_right_left.of_mul_right_right
  have hodd1 : Odd (a1 + b1) := by
    apply odd_add_of_odd_PQ5
    rw [← ha1, ← hb1]
    exact hPR2_odd
  have h5a1 : ¬ (5 : ℤ) ∣ a1 := fun hd => h5P2 (ha1 ▸ dvd_mul_of_dvd_left hd _)
  have hU0 : U ≠ 0 := by
    rw [hU_eq]
    exact mul_ne_zero (by positivity) (pow_ne_zero 5 ht0)
  have hb1_ne : b1 ≠ 0 := by
    rintro rfl
    have hR0 : R2 = 0 := by rw [hb1]; ring
    dsimp [R2] at hR0
    exact hU0 (by nlinarith)
  have heq1 : b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4) =
      2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5 := by
    have h2pow : 2 * (2 : ℤ) ^ (2 * (m - 1)) = 2 ^ (2 * m - 1) := by
      conv_rhs => rw [show 2 * m - 1 = 2 * (m - 1) + 1 by omega, pow_succ']
    have h5R : 5 * (b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4)) =
        5 * (2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by
      calc 5 * (b1 * (a1 ^ 4 + 10 * a1 ^ 2 * b1 ^ 2 + 5 * b1 ^ 4)) = R2 := by linarith [hb1]
        _ = 10 * (2 ^ (m - 1) * 5 ^ (n - 2) * t ^ 5) ^ 2 := by dsimp [R2]; rw [hU_eq]
        _ = 5 * ((2 * 2 ^ (2 * (m - 1))) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by
            rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
            ring_nf
        _ = 5 * (2 ^ (2 * m - 1) * 5 ^ (2 * (n - 2)) * (t ^ 2) ^ 5) := by rw [h2pow]
    linarith
  exact no_eq2_aux _ a1 b1 (t ^ 2) (2 * m - 1) (2 * (n - 2)) rfl
    ⟨by omega, by omega, hcop1, hodd1, h5a1, hb1_ne, ht10, heq1⟩

/- ## Section 3: First-Case Elimination (`5 ∤ b`) in `𝓞 (CyclotomicField 5 ℚ)` -/

abbrev K5 := CyclotomicField 5 ℚ

instance : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
instance : IsCyclotomicExtension {5} ℚ K5 := CyclotomicField.isCyclotomicExtension 5 ℚ
instance : IsPrincipalIdealRing (𝓞 K5) := IsCyclotomicExtension.Rat.five_pid K5

lemma hζ5 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 5 ℚ K5) 5 :=
  IsCyclotomicExtension.zeta_spec 5 ℚ K5

noncomputable abbrev ζ : 𝓞 K5 := hζ5.toInteger

lemma ζ_pow5 : ζ ^ 5 = 1 := hζ5.toInteger_isPrimitiveRoot.pow_eq_one

lemma ζ_ne_one : ζ ≠ 1 := hζ5.toInteger_isPrimitiveRoot.ne_one (by decide)

lemma ζ_cyc : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
  apply mul_left_cancel₀ (sub_ne_zero.mpr ζ_ne_one)
  calc (ζ - 1) * (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) = ζ ^ 5 - 1 := by ring
    _ = 0 := by rw [ζ_pow5, sub_self]
    _ = (ζ - 1) * 0 := by rw [mul_zero]

lemma ζ4 : ζ ^ 4 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by linear_combination ζ_cyc
lemma ζ5 : ζ ^ 5 = 1 := ζ_pow5
lemma ζ6 : ζ ^ 6 = ζ := by
  calc ζ ^ 6 = ζ ^ 5 * ζ := by ring
    _ = ζ := by rw [ζ_pow5, one_mul]
lemma ζ7 : ζ ^ 7 = ζ ^ 2 := by
  calc ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
    _ = ζ ^ 2 := by rw [ζ_pow5, one_mul]
lemma ζ8 : ζ ^ 8 = ζ ^ 3 := by
  calc ζ ^ 8 = ζ ^ 5 * ζ ^ 3 := by ring
    _ = ζ ^ 3 := by rw [ζ_pow5, one_mul]
lemma ζ9 : ζ ^ 9 = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by
  calc ζ ^ 9 = ζ ^ 5 * ζ ^ 4 := by ring
    _ = -1 - ζ - ζ ^ 2 - ζ ^ 3 := by rw [ζ_pow5, one_mul, ζ4]
lemma ζ10 : ζ ^ 10 = 1 := by
  calc ζ ^ 10 = (ζ ^ 5) ^ 2 := by ring
    _ = 1 := by rw [ζ_pow5]; ring

lemma exists_coord5 (x : 𝓞 K5) :
    ∃ b0 b1 b2 b3 : ℤ, x = b0 + b1 * ζ + b2 * ζ ^ 2 + b3 * ζ ^ 3 := by
  obtain ⟨f, rfl⟩ := hζ5.integralPowerBasis.exists_eq_aeval' x
  rw [IsPrimitiveRoot.integralPowerBasis_gen]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a0, a1, a2, a3, ha⟩ := hp
    obtain ⟨c0, c1, c2, c3, hc⟩ := hq
    refine ⟨a0 + c0, a1 + c1, a2 + c2, a3 + c3, ?_⟩
    rw [map_add, ha, hc]; push_cast; ring
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    induction n with
    | zero => exact ⟨c, 0, 0, 0, by simp⟩
    | succ n ih =>
      obtain ⟨b0, b1, b2, b3, hb⟩ := ih
      refine ⟨-b3, b0 - b3, b1 - b3, b2 - b3, ?_⟩
      rw [pow_succ, ← mul_assoc, hb]
      push_cast
      linear_combination (b3 : 𝓞 K5) * ζ_cyc

lemma coord5_zero {b0 b1 b2 b3 : ℤ}
    (h : (b0 : 𝓞 K5) + b1 * ζ + b2 * ζ ^ 2 + b3 * ζ ^ 3 = 0) :
    b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 := by
  have hdim : hζ5.integralPowerBasis.dim = 4 := by
    rw [IsPrimitiveRoot.integralPowerBasis_dim]
    rfl
  let c : Fin 4 → ℤ := ![b0, b1, b2, b3]
  have hsum : ∑ i : Fin hζ5.integralPowerBasis.dim,
      c (finCongr hdim i) • hζ5.integralPowerBasis.basis i = 0 := by
    rw [← (finCongr hdim).symm.sum_comp]
    simp only [Equiv.apply_symm_apply, Fin.sum_univ_four, PowerBasis.basis_eq_pow,
      IsPrimitiveRoot.integralPowerBasis_gen]
    simpa [c, zsmul_eq_mul, pow_two] using h
  have hli := Fintype.linearIndependent_iff.mp hζ5.integralPowerBasis.basis.linearIndependent
    (fun i => c (finCongr hdim i)) hsum
  have hc : ∀ j : Fin 4, c j = 0 := fun j => by
    simpa using hli ((finCongr hdim).symm j)
  exact ⟨hc 0, hc 1, hc 2, hc 3⟩

lemma coord5_eq {a0 a1 a2 a3 b0 b1 b2 b3 : ℤ}
    (h : (a0 : 𝓞 K5) + a1 * ζ + a2 * ζ ^ 2 + a3 * ζ ^ 3 =
         (b0 : 𝓞 K5) + b1 * ζ + b2 * ζ ^ 2 + b3 * ζ ^ 3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have hz := coord5_zero (b0 := a0 - b0) (b1 := a1 - b1) (b2 := a2 - b2) (b3 := a3 - b3)
    (by push_cast; linear_combination h)
  omega

noncomputable def conj5 : 𝓞 K5 ≃+* 𝓞 K5 :=
  RingOfIntegers.mapRingEquiv
    (IsCyclotomicExtension.fromZetaAut (hζ5.pow_of_coprime 4 (by decide))
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))).toRingEquiv

lemma conj5_ζ : conj5 ζ = ζ ^ 4 := by
  apply Subtype.ext
  change (IsCyclotomicExtension.fromZetaAut (hζ5.pow_of_coprime 4 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by norm_num)))
      (IsCyclotomicExtension.zeta 5 ℚ K5) = _
  rw [IsCyclotomicExtension.fromZetaAut_spec]
  rfl

lemma conj5_involution (x : 𝓞 K5) : conj5 (conj5 x) = x := by
  obtain ⟨b0, b1, b2, b3, rfl⟩ := exists_coord5 x
  have hζ4 : conj5 (ζ ^ 4) = ζ := by
    rw [map_pow, conj5_ζ, ← pow_mul]
    calc ζ ^ 16 = (ζ ^ 5) ^ 3 * ζ := by ring
      _ = ζ := by rw [ζ_pow5]; ring
  simp only [map_add, map_mul, map_pow, map_intCast, conj5_ζ, hζ4]

lemma sos4_bound {x y z w : ℤ}
    (h : (x - y) ^ 2 + (y - z) ^ 2 + (z - w) ^ 2 + (x - z) ^ 2 +
         (y - w) ^ 2 + (x - w) ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 4) :
    -1 ≤ x ∧ x ≤ 1 := by
  have hx2 : 5 * x ^ 2 ≤ 8 := by
    have hid : 5 * x ^ 2 + (x - 2 * y) ^ 2 + (x - 2 * z) ^ 2 + (x - 2 * w) ^ 2 +
        2 * (y - z) ^ 2 + 2 * (z - w) ^ 2 + 2 * (y - w) ^ 2 = 8 := by
      linear_combination 2 * h
    linarith [sq_nonneg (x - 2 * y), sq_nonneg (x - 2 * z), sq_nonneg (x - 2 * w),
      sq_nonneg (y - z), sq_nonneg (z - w), sq_nonneg (y - w)]
  have hx1 : x ^ 2 ≤ 1 := by omega
  exact ⟨by by_contra! hc; nlinarith, by by_contra! hc; nlinarith⟩

lemma kronecker_unit5 {η : 𝓞 K5} (h : η * conj5 η = 1) :
    ∃ s : 𝓞 K5, (s = 1 ∨ s = -1) ∧ ∃ k ∈ Finset.range 5, η = s * ζ ^ k := by
  obtain ⟨b0, b1, b2, b3, hη_b⟩ := exists_coord5 η
  have ⟨a1, a2, a3, a4, hη⟩ : ∃ a1 a2 a3 a4 : ℤ,
      η = (a1 : 𝓞 K5) * ζ + a2 * ζ ^ 2 + a3 * ζ ^ 3 + a4 * ζ ^ 4 :=
    ⟨b1 - b0, b2 - b0, b3 - b0, -b0, by
      rw [hη_b]; push_cast; linear_combination (b0 : 𝓞 K5) * ζ_cyc⟩
  clear hη_b b0 b1 b2 b3
  have hconj : conj5 η = (a1 : 𝓞 K5) * ζ ^ 4 + a2 * ζ ^ 3 + a3 * ζ ^ 2 + a4 * ζ := by
    rw [hη]
    simp only [map_add, map_mul, map_pow, map_intCast, conj5_ζ]
    have h8 : (ζ ^ 4) ^ 2 = ζ ^ 3 := by
      calc (ζ ^ 4) ^ 2 = ζ ^ 5 * ζ ^ 3 := by ring
        _ = ζ ^ 3 := by rw [ζ_pow5, one_mul]
    have h12 : (ζ ^ 4) ^ 3 = ζ ^ 2 := by
      calc (ζ ^ 4) ^ 3 = (ζ ^ 5) ^ 2 * ζ ^ 2 := by ring
        _ = ζ ^ 2 := by rw [ζ_pow5]; ring
    have h16 : (ζ ^ 4) ^ 4 = ζ := by
      calc (ζ ^ 4) ^ 4 = (ζ ^ 5) ^ 3 * ζ := by ring
        _ = ζ := by rw [ζ_pow5]; ring
    rw [h8, h12, h16]
  set C0 := a1 ^ 2 - a1 * a2 + a2 ^ 2 - a2 * a3 + a3 ^ 2 - a3 * a4 + a4 ^ 2
  set C2 := -a1 * a2 + a1 * a3 + a1 * a4 - a2 * a3 + a2 * a4 - a3 * a4
  have hprod : η * conj5 η = (C0 : 𝓞 K5) + 0 * ζ + C2 * ζ ^ 2 + C2 * ζ ^ 3 := by
    rw [hconj, hη]
    dsimp [C0, C2]
    push_cast
    ring_nf
    simp only [ζ8, ζ7, ζ6, ζ5, ζ4]
    ring
  have heq : (C0 : 𝓞 K5) + (0 : ℤ) * ζ + C2 * ζ ^ 2 + C2 * ζ ^ 3 =
      (1 : ℤ) + (0 : ℤ) * ζ + (0 : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 := by
    simpa [hprod] using h
  obtain ⟨hC0, -, hC2, -⟩ := coord5_eq heq
  have hsos : (a1 - a2) ^ 2 + (a2 - a3) ^ 2 + (a3 - a4) ^ 2 + (a1 - a3) ^ 2 +
      (a2 - a4) ^ 2 + (a1 - a4) ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 = 4 := by
    dsimp [C0, C2] at hC0 hC2
    linarith
  obtain ⟨ha1_lo, ha1_hi⟩ := sos4_bound hsos
  obtain ⟨ha2_lo, ha2_hi⟩ := sos4_bound (x := a2) (y := a1) (z := a3) (w := a4) (by linarith)
  obtain ⟨ha3_lo, ha3_hi⟩ := sos4_bound (x := a3) (y := a1) (z := a2) (w := a4) (by linarith)
  obtain ⟨ha4_lo, ha4_hi⟩ := sos4_bound (x := a4) (y := a1) (z := a2) (w := a3) (by linarith)
  clear C0 C2 hC0 hC2 hprod heq hconj h
  interval_cases a1 <;> interval_cases a2 <;> interval_cases a3 <;> interval_cases a4
  all_goals try { exfalso; norm_num at hsos }
  · exact ⟨1, Or.inl rfl, 0, by simp, by rw [hη]; push_cast; linear_combination -ζ_cyc⟩
  · exact ⟨-1, Or.inr rfl, 1, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 2, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 3, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 4, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 4, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 3, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 2, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨1, Or.inl rfl, 1, by simp, by rw [hη]; push_cast; ring⟩
  · exact ⟨-1, Or.inr rfl, 0, by simp, by rw [hη]; push_cast; linear_combination ζ_cyc⟩

lemma five_eq_prod_zeta :
    (1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4) = (5 : 𝓞 K5) := by
  ring_nf
  simp only [ζ10, ζ9, ζ8, ζ5]
  ring

lemma pow5_sub_pow5_fac (x y : 𝓞 K5) :
    x ^ 5 - y ^ 5 =
      (x - y) * (x - ζ * y) * (x - ζ ^ 2 * y) * (x - ζ ^ 3 * y) * (x - ζ ^ 4 * y) := by
  ring_nf
  simp only [ζ10, ζ9, ζ8, ζ7, ζ6, ζ5, ζ4]
  ring

lemma pow5_cong_int (α : 𝓞 K5) : ∃ C : ℤ, ∃ q : 𝓞 K5, α ^ 5 = C + 5 * q := by
  obtain ⟨b0, b1, b2, b3, rfl⟩ := exists_coord5 α
  have hadd : ∀ A B : 𝓞 K5, ∃ r : 𝓞 K5, (A + B) ^ 5 = A ^ 5 + B ^ 5 + 5 * r := fun A B =>
    ⟨A * B * (A + B) * (A ^ 2 + A * B + B ^ 2), by ring⟩
  obtain ⟨r1, hr1⟩ := hadd ((b0 : 𝓞 K5) + b1 * ζ + b2 * ζ ^ 2) (b3 * ζ ^ 3)
  obtain ⟨r2, hr2⟩ := hadd ((b0 : 𝓞 K5) + b1 * ζ) (b2 * ζ ^ 2)
  obtain ⟨r3, hr3⟩ := hadd (b0 : 𝓞 K5) (b1 * ζ)
  refine ⟨b0 ^ 5 + b1 ^ 5 + b2 ^ 5 + b3 ^ 5, r1 + r2 + r3, ?_⟩
  rw [hr1, hr2, hr3, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    show 2 * 5 = 5 * 2 by rfl, show 3 * 5 = 5 * 3 by rfl, pow_mul, pow_mul, ζ_pow5]
  push_cast
  ring

lemma zmod25_no_sol_H2 : ∀ g b s : ZMod 25,
    (ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) b) ≠ 0 →
    (ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) g = 0 ∨
     ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) s = 0 ∨
     ZMod.castHom (show 5 ∣ 25 by norm_num) (ZMod 5) (s + g) = 0) →
    g ^ 5 + 8 * b ^ 5 ≠ s ^ 5 := by
  decide

lemma isCoprime_factor_five {S G : ℤ} (hSG : IsCoprime S G)
    (h5 : IsCoprime ((S : 𝓞 K5) - ζ * G) (5 : 𝓞 K5))
    {u : 𝓞 K5} (hu : (1 - u) ∣ (5 : 𝓞 K5)) :
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ * u * G) := by
  obtain ⟨a, c, hac⟩ := hSG
  obtain ⟨d, hd⟩ := hu
  obtain ⟨x, y, hxy⟩ := h5
  refine ⟨x - y * d * ζ ^ 4 * (c + a * ζ * u), y * d * ζ ^ 4 * (c + a * ζ), ?_⟩
  have hlin : (c + a * ζ) * ((S : 𝓞 K5) - ζ * u * G) - (c + a * ζ * u) * ((S : 𝓞 K5) - ζ * G) =
      ζ * (1 - u) * ((a * S + c * G : ℤ) : 𝓞 K5) := by push_cast; ring
  rw [hac] at hlin
  have h5_eq : ((5 : 𝓞 K5)) = ζ ^ 4 * d * (ζ * (1 - u)) := by
    calc (5 : 𝓞 K5) = (1 - u) * d := hd
      _ = ζ ^ 5 * (1 - u) * d := by rw [ζ_pow5, one_mul]
      _ = ζ ^ 4 * d * (ζ * (1 - u)) := by ring
  calc (x - y * d * ζ ^ 4 * (c + a * ζ * u)) * ((S : 𝓞 K5) - ζ * G) +
        (y * d * ζ ^ 4 * (c + a * ζ)) * ((S : 𝓞 K5) - ζ * u * G)
      = x * ((S : 𝓞 K5) - ζ * G) +
        y * (ζ ^ 4 * d * ((c + a * ζ) * ((S : 𝓞 K5) - ζ * u * G) -
          (c + a * ζ * u) * ((S : 𝓞 K5) - ζ * G))) := by ring
    _ = x * ((S : 𝓞 K5) - ζ * G) + y * (5 : 𝓞 K5) := by
        rw [hlin]; simp [← h5_eq]
    _ = 1 := hxy

lemma isCoprime_conj_factors {S G : ℤ} (hSG : IsCoprime S G)
    (h5_cop : IsCoprime ((S : 𝓞 K5) - ζ * G) (5 : 𝓞 K5)) :
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - G) ∧
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ ^ 2 * G) ∧
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ ^ 3 * G) ∧
    IsCoprime ((S : 𝓞 K5) - ζ * G) ((S : 𝓞 K5) - ζ ^ 4 * G) := by
  have hd4 : (1 - ζ ^ 4) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3), by rw [← five_eq_prod_zeta]; ring⟩
  have hd1 : (1 - ζ) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4), by rw [← five_eq_prod_zeta]; ring⟩
  have hd2 : (1 - ζ ^ 2) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ) * (1 - ζ ^ 3) * (1 - ζ ^ 4), by rw [← five_eq_prod_zeta]; ring⟩
  have hd3 : (1 - ζ ^ 3) ∣ (5 : 𝓞 K5) :=
    ⟨(1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 4), by rw [← five_eq_prod_zeta]; ring⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := isCoprime_factor_five hSG h5_cop hd4
    have he : (S : 𝓞 K5) - ζ * ζ ^ 4 * G = (S : 𝓞 K5) - G := by
      calc (S : 𝓞 K5) - ζ * ζ ^ 4 * G = (S : 𝓞 K5) - ζ ^ 5 * G := by ring
        _ = (S : 𝓞 K5) - G := by rw [ζ_pow5, one_mul]
    rwa [he] at h
  · have h := isCoprime_factor_five hSG h5_cop hd1
    have he : (S : 𝓞 K5) - ζ * ζ * G = (S : 𝓞 K5) - ζ ^ 2 * G := by ring
    rwa [he] at h
  · have h := isCoprime_factor_five hSG h5_cop hd2
    have he : (S : 𝓞 K5) - ζ * ζ ^ 2 * G = (S : 𝓞 K5) - ζ ^ 3 * G := by ring
    rwa [he] at h
  · have h := isCoprime_factor_five hSG h5_cop hd3
    have he : (S : 𝓞 K5) - ζ * ζ ^ 3 * G = (S : 𝓞 K5) - ζ ^ 4 * G := by ring
    rwa [he] at h

lemma unit_conj_cases {S G : ℤ} {s : 𝓞 K5} (hs : s = 1 ∨ s = -1)
    {k : ℕ} (hk : k ∈ Finset.range 5) {w : 𝓞 K5}
    (hdiff5 : ((S : 𝓞 K5) - ζ * G) - s * ζ ^ k * ((S : 𝓞 K5) - ζ ^ 4 * G) = 5 * w) :
    (5 : ℤ) ∣ G ∨ (5 : ℤ) ∣ S ∨ (5 : ℤ) ∣ (S + G) ∨ (5 : ℤ) ∣ (S - G) := by
  obtain ⟨r0, r1, r2, r3, hr⟩ := exists_coord5 w
  rw [hr] at hdiff5
  have hd' : ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 =
      ((S : 𝓞 K5) - ζ * G) - s * ζ ^ k * ((S : 𝓞 K5) - ζ ^ 4 * G) := by
    rw [hdiff5]; push_cast; ring
  clear hdiff5 hr w
  rw [Finset.mem_range] at hk
  rcases hs with rfl | rfl <;> interval_cases k
  · have hc : ((-G : ℤ) : 𝓞 K5) + (-2 * G : ℤ) * ζ + (-G : ℤ) * ζ ^ 2 + (-G : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ4]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inl ⟨-r0, by omega⟩
  · have hc : ((S + G : ℤ) : 𝓞 K5) + (-(S + G) : ℤ) * ζ + (0 : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ5]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inr (Or.inl ⟨r0, h0⟩))
  · have hc : (S : 𝓞 K5) + (0 : ℤ) * ζ + (-S : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ6]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : (S : 𝓞 K5) + (-G : ℤ) * ζ + (G : ℤ) * ζ ^ 2 + (-S : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ7]
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : ((2 * S : ℤ) : 𝓞 K5) + ((S - G : ℤ)) * ζ + (S : ℤ) * ζ ^ 2 + ((S + G : ℤ)) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ8, ζ4]; ring
    obtain ⟨-, -, h2, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r2, h2⟩)
  · have hc : ((2 * S + G : ℤ) : 𝓞 K5) + (0 : ℤ) * ζ + (G : ℤ) * ζ ^ 2 + (G : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ4]; ring
    obtain ⟨-, -, h2, -⟩ := coord5_eq hc
    exact Or.inl ⟨r2, h2⟩
  · have hc : ((S - G : ℤ) : 𝓞 K5) + ((S - G : ℤ)) * ζ + (0 : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ5]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inr (Or.inr ⟨r0, h0⟩))
  · have hc : (S : 𝓞 K5) + ((-2 * G : ℤ)) * ζ + (S : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ6]; ring
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : (S : 𝓞 K5) + (-G : ℤ) * ζ + (-G : ℤ) * ζ ^ 2 + (S : ℤ) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ7]
    obtain ⟨h0, -, -, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨r0, h0⟩)
  · have hc : ((0 : ℤ) : 𝓞 K5) + ((-S - G : ℤ)) * ζ + (-S : ℤ) * ζ ^ 2 + ((-S - G : ℤ)) * ζ ^ 3 =
        ((5 * r0 : ℤ) : 𝓞 K5) + (5 * r1 : ℤ) * ζ + (5 * r2 : ℤ) * ζ ^ 2 + (5 * r3 : ℤ) * ζ ^ 3 := by
      rw [hd']; push_cast; ring_nf; rw [ζ8, ζ4]; ring
    obtain ⟨-, -, h2, -⟩ := coord5_eq hc
    exact Or.inr (Or.inl ⟨-r2, by omega⟩)

theorem no_sol_case1_H2 {G B S : ℤ} (hSG : IsCoprime S G) (h5B : ¬ (5 : ℤ) ∣ B)
    (heq : G ^ 5 + 8 * B ^ 5 = S ^ 5) : False := by
  have hS_odd : Odd S := by
    rcases Int.even_or_odd S with hSe | hSo
    · exfalso
      have hGe : Even G := by
        have hG5 : Even (G ^ 5) := by
          obtain ⟨k, hk⟩ := hSe
          exact ⟨16 * k ^ 5 - 4 * B ^ 5, by rw [show G ^ 5 = S ^ 5 - 8 * B ^ 5 by linarith, hk]; ring⟩
        exact (Int.even_pow' (by norm_num)).mp hG5
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hSG
      have hd : (2 : ℤ) ∣ (Int.gcd S G : ℤ) := Int.dvd_coe_gcd hSe.two_dvd hGe.two_dvd
      rw [hg] at hd; norm_num at hd
    · exact hSo
  have hG_odd : Odd G := by
    rcases Int.even_or_odd G with hGe | hGo
    · exfalso
      have hSe : Even S := by
        have hS5 : Even (S ^ 5) := by
          obtain ⟨k, hk⟩ := hGe
          exact ⟨16 * k ^ 5 + 4 * B ^ 5, by rw [← heq, hk]; ring⟩
        exact (Int.even_pow' (by norm_num)).mp hS5
      have hg := Int.isCoprime_iff_gcd_eq_one.mp hSG
      have hd : (2 : ℤ) ∣ (Int.gcd S G : ℤ) := Int.dvd_coe_gcd hSe.two_dvd hGe.two_dvd
      rw [hg] at hd; norm_num at hd
    · exact hGo
  set Q4 := S ^ 4 + S ^ 3 * G + S ^ 2 * G ^ 2 + S * G ^ 3 + G ^ 4
  have hQ4_odd : Odd Q4 := by
    have h1 : Even (S ^ 4 + S ^ 3 * G) := hS_odd.pow.add_odd (hS_odd.pow.mul hG_odd)
    have h2 : Even (S ^ 2 * G ^ 2 + S * G ^ 3) :=
      (hS_odd.pow.mul hG_odd.pow).add_odd (hS_odd.mul hG_odd.pow)
    have he : Q4 = (S ^ 4 + S ^ 3 * G) + (S ^ 2 * G ^ 2 + S * G ^ 3) + G ^ 4 := by
      dsimp [Q4]; ring
    rw [he]
    exact (h1.add h2).add_odd hG_odd.pow
  have h8_dvd : (8 : ℤ) ∣ (S - G) := by
    have hQ4_8 : IsCoprime Q4 8 := by
      have h2 := isCoprime_two_of_odd hQ4_odd
      simpa using h2.pow_right (n := 3)
    refine hQ4_8.symm.dvd_of_dvd_mul_right ?_
    exact ⟨B ^ 5, by dsimp [Q4]; linear_combination -heq⟩
  obtain ⟨M, hM⟩ := h8_dvd
  have hfac : ((S : 𝓞 K5) - ζ * G) *
      ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)) =
      (B : 𝓞 K5) ^ 5 := by
    apply mul_left_cancel₀ (show (8 : 𝓞 K5) ≠ 0 by norm_num)
    have hSG8 : (S : 𝓞 K5) - G = 8 * M := by exact_mod_cast hM
    have hB8 : (S : 𝓞 K5) ^ 5 - (G : 𝓞 K5) ^ 5 = 8 * (B : 𝓞 K5) ^ 5 := by
      have : S ^ 5 - G ^ 5 = 8 * B ^ 5 := by linarith
      exact_mod_cast this
    calc (8 : 𝓞 K5) * (((S : 𝓞 K5) - ζ * G) *
          ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)))
        = ((8 * M : 𝓞 K5)) * (S - ζ * G) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G) := by
          ring
      _ = ((S : 𝓞 K5) - G) * (S - ζ * G) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G) := by
          rw [← hSG8]
      _ = (S : 𝓞 K5) ^ 5 - (G : 𝓞 K5) ^ 5 := (pow5_sub_pow5_fac _ _).symm
      _ = 8 * (B : 𝓞 K5) ^ 5 := hB8
  have h5_cop : IsCoprime ((S : 𝓞 K5) - ζ * G) (5 : 𝓞 K5) := by
    have hB5 : IsCoprime (B ^ 5) 5 := (isCoprime_five_of_not_dvd h5B).pow_left
    obtain ⟨x, y, hxy⟩ := hB5
    refine ⟨(x : 𝓞 K5) * ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)), y, ?_⟩
    calc (x : 𝓞 K5) * ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)) *
          ((S : 𝓞 K5) - ζ * G) + (y : 𝓞 K5) * 5
        = (x : 𝓞 K5) * (((S : 𝓞 K5) - ζ * G) *
          ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G))) + (y : 𝓞 K5) * 5 := by
          ring
      _ = (x : 𝓞 K5) * (B : 𝓞 K5) ^ 5 + (y : 𝓞 K5) * 5 := by rw [hfac]
      _ = ((x * B ^ 5 + y * 5 : ℤ) : 𝓞 K5) := by push_cast; ring
      _ = 1 := by rw [hxy]; simp
  obtain ⟨hcSG, hc2, hc3, hc4⟩ := isCoprime_conj_factors hSG h5_cop
  have hcM : IsCoprime ((S : 𝓞 K5) - ζ * G) (M : 𝓞 K5) := by
    have hSG8 : (S : 𝓞 K5) - G = 8 * M := by exact_mod_cast hM
    rw [hSG8] at hcSG
    exact hcSG.of_mul_right_right
  have hcop_fac : IsCoprime ((S : 𝓞 K5) - ζ * G)
      ((M : 𝓞 K5) * (S - ζ ^ 2 * G) * (S - ζ ^ 3 * G) * (S - ζ ^ 4 * G)) :=
    ((hcM.mul_right hc2).mul_right hc3).mul_right hc4
  obtain ⟨α, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop_fac hfac
  set u0_bar : (𝓞 K5)ˣ := Units.map conj5.toMonoidHom u0
  set η_u : (𝓞 K5)ˣ := u0 * u0_bar⁻¹
  have hη_norm : (η_u : 𝓞 K5) * conj5 (η_u : 𝓞 K5) = 1 := by
    have hub : (u0_bar : 𝓞 K5) = conj5 (u0 : 𝓞 K5) := rfl
    have hinv1 : (u0_bar : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = 1 := Units.mul_inv u0_bar
    have hinv2 : (u0 : 𝓞 K5) * conj5 ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = 1 := by
      have := congr_arg conj5 hinv1
      rw [map_mul, map_one, hub, conj5_involution] at this
      exact this
    have hη_val : (η_u : 𝓞 K5) = (u0 : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) := rfl
    rw [hη_val, map_mul]
    calc (u0 : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) *
          (conj5 (u0 : 𝓞 K5) * conj5 ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5))
        = ((u0 : 𝓞 K5) * conj5 ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) *
          ((u0_bar : 𝓞 K5) * ((u0_bar⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) := by rw [hub]; ring
      _ = 1 := by rw [hinv2, hinv1, mul_one]
  obtain ⟨s, hs, k, hk, hη_eq⟩ := kronecker_unit5 hη_norm
  have hu0_rel : (u0 : 𝓞 K5) = s * ζ ^ k * conj5 (u0 : 𝓞 K5) := by
    have hub : (u0_bar : 𝓞 K5) = conj5 (u0 : 𝓞 K5) := rfl
    have hu_eq : η_u * u0_bar = u0 := by simp [η_u]
    calc (u0 : 𝓞 K5) = ((η_u * u0_bar : (𝓞 K5)ˣ) : 𝓞 K5) := (congr_arg Units.val hu_eq).symm
      _ = (η_u : 𝓞 K5) * (u0_bar : 𝓞 K5) := Units.val_mul η_u u0_bar
      _ = s * ζ ^ k * conj5 (u0 : 𝓞 K5) := by rw [hη_eq, hub]
  have hu0_conj : (conj5 α) ^ 5 * conj5 (u0 : 𝓞 K5) = (S : 𝓞 K5) - ζ ^ 4 * G := by
    have := congr_arg conj5 hu0
    simpa [conj5_ζ] using this
  obtain ⟨C, q, hα5⟩ := pow5_cong_int α
  have hα5_conj : (conj5 α) ^ 5 = (C : 𝓞 K5) + 5 * conj5 q := by
    rw [← map_pow, hα5, map_add, map_intCast, map_mul, map_ofNat]
  have hdiff5 : ((S : 𝓞 K5) - ζ * G) - s * ζ ^ k * ((S : 𝓞 K5) - ζ ^ 4 * G) =
      5 * (q * (u0 : 𝓞 K5) - s * ζ ^ k * conj5 q * conj5 (u0 : 𝓞 K5)) := by
    have hu0_sub : (u0 : 𝓞 K5) - s * ζ ^ k * conj5 (u0 : 𝓞 K5) = 0 := sub_eq_zero.mpr hu0_rel
    rw [← hu0, ← hu0_conj, hα5, hα5_conj]
    calc ((C : 𝓞 K5) + 5 * q) * (u0 : 𝓞 K5) -
          s * ζ ^ k * (((C : 𝓞 K5) + 5 * conj5 q) * conj5 (u0 : 𝓞 K5))
        = (C : 𝓞 K5) * ((u0 : 𝓞 K5) - s * ζ ^ k * conj5 (u0 : 𝓞 K5)) +
          5 * (q * (u0 : 𝓞 K5) - s * ζ ^ k * conj5 q * conj5 (u0 : 𝓞 K5)) := by ring
      _ = 5 * (q * (u0 : 𝓞 K5) - s * ζ ^ k * conj5 q * conj5 (u0 : 𝓞 K5)) := by
          rw [hu0_sub]; ring
  have heq25 : (G : ZMod 25) ^ 5 + 8 * (B : ZMod 25) ^ 5 = (S : ZMod 25) ^ 5 := by
    have := congr_arg (Int.cast : ℤ → ZMod 25) heq
    push_cast at this
    exact this
  rcases unit_conj_cases hs hk hdiff5 with h5G | h5S | h5SG | h5SmG
  · apply zmod25_no_sol_H2 (G : ZMod 25) (B : ZMod 25) (S : ZMod 25)
    · simp only [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5B
    · left
      simp only [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5G
    · exact heq25
  · apply zmod25_no_sol_H2 (G : ZMod 25) (B : ZMod 25) (S : ZMod 25)
    · simp only [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5B
    · right; left
      simp only [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5S
    · exact heq25
  · apply zmod25_no_sol_H2 (G : ZMod 25) (B : ZMod 25) (S : ZMod 25)
    · simp only [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5B
    · right; right
      rw [← Int.cast_add]
      simp only [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h5SG
    · exact heq25
  · obtain ⟨t, ht⟩ := h5SmG
    have h5_8B5 : (5 : ℤ) ∣ 8 * B ^ 5 := by
      refine ⟨t * Q4, ?_⟩
      calc 8 * B ^ 5 = S ^ 5 - G ^ 5 := by linarith
        _ = (S - G) * Q4 := by dsimp [Q4]; ring
        _ = 5 * (t * Q4) := by rw [ht]; ring
    rcases Int.Prime.dvd_mul' Nat.prime_five h5_8B5 with h8 | hB5
    · norm_num at h8
    · exact h5B (Int.Prime.dvd_pow' Nat.prime_five hB5)

/- ## Section 4: Assembling the Full Proof of `H2` -/

lemma strip_two_five : ∀ n : ℕ, ∀ B : ℤ, B.natAbs = n → B ≠ 0 →
    ∃ a c : ℕ, ∃ B0 : ℤ, B0 ≠ 0 ∧ IsCoprime B0 10 ∧ B = 2 ^ a * 5 ^ c * B0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hn hB0
    by_cases h2 : (2 : ℤ) ∣ B
    · obtain ⟨B', rfl⟩ := h2
      have hB'0 : B' ≠ 0 := fun h0 => hB0 (by simp [h0])
      have hlt : B'.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have : 0 < B'.natAbs := Int.natAbs_pos.mpr hB'0
        have h2a : (2 : ℤ).natAbs = 2 := rfl
        rw [h2a]
        omega
      obtain ⟨a, c, B0, h0, hcop, hB'⟩ := ih _ hlt B' rfl hB'0
      exact ⟨a + 1, c, B0, h0, hcop, by rw [hB', pow_succ]; ring⟩
    · by_cases h5 : (5 : ℤ) ∣ B
      · obtain ⟨B', rfl⟩ := h5
        have hB'0 : B' ≠ 0 := fun h0 => hB0 (by simp [h0])
        have hlt : B'.natAbs < n := by
          rw [← hn, Int.natAbs_mul]
          have : 0 < B'.natAbs := Int.natAbs_pos.mpr hB'0
          have h5a : (5 : ℤ).natAbs = 5 := rfl
          rw [h5a]
          omega
        obtain ⟨a, c, B0, h0, hcop, hB'⟩ := ih _ hlt B' rfl hB'0
        exact ⟨a, c + 1, B0, h0, hcop, by rw [hB', pow_succ]; ring⟩
      · refine ⟨0, 0, B, hB0, ?_, by simp⟩
        have hc2 : IsCoprime B 2 := (Prime.coprime_iff_not_dvd Int.prime_two).mpr h2 |>.symm
        have hc5 : IsCoprime B 5 := isCoprime_five_of_not_dvd h5
        simpa using hc2.mul_right hc5

theorem h2_aux : ∀ s : ℕ, ∀ b g : ℕ, 0 < b → 0 < g → g ^ 5 + 8 * b ^ 5 ≠ s ^ 5 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro b g hb hg heq
    have hs_pos : 0 < s := by
      by_contra hs0
      have hs0' : s = 0 := by omega
      subst hs0'
      have : 0 < g ^ 5 + 8 * b ^ 5 := by positivity
      omega
    by_cases hcop_gs : Nat.Coprime g s
    · let G : ℤ := (g : ℤ)
      let B : ℤ := (b : ℤ)
      let S : ℤ := (s : ℤ)
      have heqZ : G ^ 5 + 8 * B ^ 5 = S ^ 5 := by dsimp only [G, B, S]; exact_mod_cast heq
      have hSG : IsCoprime S G :=
        Int.isCoprime_iff_gcd_eq_one.mpr (by change s.gcd g = 1; exact hcop_gs.symm)
      by_cases h5B : (5 : ℤ) ∣ B
      · have hB0 : B ≠ 0 := by omega
        obtain ⟨a, c, B0, hB0_ne, hB0_10, hB_eq⟩ := strip_two_five _ B rfl hB0
        have hc_pos : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | hpos
          · exfalso
            rw [pow_zero, mul_one] at hB_eq
            rw [hB_eq] at h5B
            have h2a_5 : IsCoprime (2 ^ a : ℤ) 5 := by
              have h25 : IsCoprime (2 : ℤ) 5 := ⟨-2, 1, by ring⟩
              exact h25.pow_left
            have h5B0 : (5 : ℤ) ∣ B0 := h2a_5.symm.dvd_of_dvd_mul_left h5B
            have hB0_5 : IsCoprime B0 5 := by
              have : (10 : ℤ) = 2 * 5 := by norm_num
              rw [this] at hB0_10
              exact hB0_10.of_mul_right_right
            exact not_isUnit_five (hB0_5.isUnit_of_dvd' h5B0 dvd_rfl)
          · exact hpos
        apply no_sol_case2 (x := S) (y := -G) (Z := B0) (m := 5 * a + 3) (n := 5 * c)
          (by omega) (by omega) hSG.neg_right hB0_10 hB0_ne
        calc S ^ 5 + (-G) ^ 5 = S ^ 5 - G ^ 5 := by ring
          _ = 8 * B ^ 5 := by linarith [heqZ]
          _ = 8 * (2 ^ a * 5 ^ c * B0) ^ 5 := by rw [hB_eq]
          _ = 2 ^ (5 * a + 3) * 5 ^ (5 * c) * B0 ^ 5 := by
              rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm a 5, Nat.mul_comm c 5, pow_add]
              ring
      · exact no_sol_case1_H2 hSG h5B heqZ
    · obtain ⟨p, hp, hpg, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop_gs
      obtain ⟨g1, rfl⟩ := hpg
      obtain ⟨s1, rfl⟩ := hps
      have hpb : p ∣ b := by
        have hp5_dvd : p ^ 5 ∣ 8 * b ^ 5 := by
          have hp5_eq : p ^ 5 * g1 ^ 5 + 8 * b ^ 5 = p ^ 5 * s1 ^ 5 := by
            calc p ^ 5 * g1 ^ 5 + 8 * b ^ 5 = (p * g1) ^ 5 + 8 * b ^ 5 := by ring
              _ = (p * s1) ^ 5 := heq
              _ = p ^ 5 * s1 ^ 5 := by ring
          refine ⟨s1 ^ 5 - g1 ^ 5, ?_⟩
          rw [Nat.mul_sub_left_distrib]
          omega
        by_cases hp2 : p = 2
        · subst hp2
          obtain ⟨k, hk⟩ := hp5_dvd
          have hb5_even : 2 ∣ b ^ 5 := ⟨2 * k, by omega⟩
          exact Nat.prime_two.dvd_of_dvd_pow hb5_even
        · have hcop_p8 : Nat.Coprime (p ^ 5) 8 := by
            have hp_odd : Odd p := hp.odd_of_ne_two hp2
            exact hp_odd.coprime_two_right.pow 5 3
          have hp_b5 : p ∣ b ^ 5 := dvd_trans (dvd_pow_self p (by norm_num))
            (hcop_p8.dvd_of_dvd_mul_left hp5_dvd)
          exact hp.dvd_of_dvd_pow hp_b5
      obtain ⟨b1, rfl⟩ := hpb
      have hb1_pos : 0 < b1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hb)
      have hg1_pos : 0 < g1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hg)
      have hs1_pos : 0 < s1 := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hs_pos)
      have hs1_lt : s1 < p * s1 := by nlinarith [hp.one_lt]
      have heq1 : g1 ^ 5 + 8 * b1 ^ 5 = s1 ^ 5 := by
        have hp5_pos : 0 < p ^ 5 := pow_pos hp.pos 5
        apply Nat.eq_of_mul_eq_mul_left hp5_pos
        calc p ^ 5 * (g1 ^ 5 + 8 * b1 ^ 5) = (p * g1) ^ 5 + 8 * (p * b1) ^ 5 := by ring
          _ = (p * s1) ^ 5 := heq
          _ = p ^ 5 * s1 ^ 5 := by ring
      exact ih s1 hs1_lt b1 g1 hb1_pos hg1_pos heq1

end OMA672H2

private theorem oma_h4_h2 : OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1.H2 := by
  intro b g s hb hg
  exact OMA672H2.h2_aux s b g hb hg


end

theorem OMA.solution : type_of% @Erdos672.erdos_672.variants.oblath :=
  OMA.R_Erdos672_erdos_672_variants_oblath_R1.main
    oma_h1 oma_h2 oma_h3
    (OMA.R_Erdos672_erdos_672_variants_oblath_R1_H4_R1.main oma_h4_h1 oma_h4_h2)
