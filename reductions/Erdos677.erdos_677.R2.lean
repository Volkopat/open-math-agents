import FormalConjectures.ErdosProblems.«677»

-- Reduction Erdos677.erdos_677.R2 of Erdős Problem 677
-- Credit: @phase-shift-lab
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Erdős 677, split by the window length k, with the cases k ≤ 2 and k = 4 proved here.

* k ≤ 2: `M(n,1) = n+1` and `M(n,2) = (n+1)(n+2)` are strictly increasing.
* k = 4 (proved below, theorem `k4`): an equality of the lcms of two length-4 windows with gap at
  least 4 forces `P(b) = 3 P(a)` with `3 ∣ b`, `¬ 3 ∣ a` (`a = n+1`, `b = m+1`,
  `P(x) = x(x+1)(x+2)(x+3)`). Then `u = b²+3b+1`, `v = a²+3a+1` solve `u² + 2 = 3 v²`, so `(u, v)`
  is the `j`-th point of the orbit `(1+√3)(2+√3)^j` with `j ≡ 2 (mod 6)`, while `4u+5` and `4v+5`
  are squares. A Cohn-type argument (the moduli 13 and 7, and a Jacobi symbol) excludes every
  `j ≠ 2`, and `j = 2` is the window pair (2..5, 3..6), whose gap is 1.
* H1 (k = 3) and H2 (k ≥ 5) are the hypotheses this reduction leaves.
-/

namespace OMA.R_Erdos677_erdos_677_R2

/-- Intervals of length 3. -/
def H1 : Prop :=
  ∀ m n : ℕ, m ≥ n + 3 → Finset.lcmInterval m 3 ≠ Finset.lcmInterval n 3

/-- Intervals of length at least 5. -/
def H2 : Prop :=
  ∀ m n k : ℕ, 5 ≤ k → m ≥ n + k → Finset.lcmInterval m k ≠ Finset.lcmInterval n k

/- ### Lengths 1 and 2 -/

lemma lcmInterval_one (n : ℕ) : Finset.lcmInterval n 1 = n + 1 := by
  have hs : Finset.Ioc n (n + 1) = {n + 1} := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
  simp only [Finset.lcmInterval, hs, Finset.lcm_singleton, id, normalize_eq]

lemma lcmInterval_two (n : ℕ) : Finset.lcmInterval n 2 = (n + 1) * (n + 2) := by
  have hs : Finset.Ioc n (n + 2) = {n + 1, n + 2} := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]; omega
  simp only [Finset.lcmInterval, hs, Finset.lcm_insert, Finset.lcm_singleton, id, normalize_eq]
  exact Nat.Coprime.lcm_eq_mul (by
    rw [show n + 2 = (n + 1) + 1 by ring]
    exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _))

lemma small_k (m n k : ℕ) (hk : 0 < k) (hk2 : k ≤ 2) (hm : m ≥ n + k) :
    Finset.lcmInterval m k ≠ Finset.lcmInterval n k := by
  interval_cases k
  · rw [lcmInterval_one, lcmInterval_one]; omega
  · rw [lcmInterval_two, lcmInterval_two]
    intro h
    have : (n + 1) * (n + 2) < (m + 1) * (m + 2) := Nat.mul_lt_mul'' (by omega) (by omega)
    omega

/- ### Powers of `2 + √3` in `ℤ√3` -/

lemma norm_α_pow (r : ℕ) : ((⟨2, 1⟩ : ℤ√3) ^ r).norm = 1 := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, Zsqrtd.norm_mul, ih]; simp [Zsqrtd.norm_def]

lemma α_pow_mul_star (r : ℕ) : (⟨2, 1⟩ : ℤ√3) ^ r * star ((⟨2, 1⟩ : ℤ√3) ^ r) = 1 := by
  rw [← Zsqrtd.norm_eq_mul_conj, norm_α_pow]; simp

lemma α_pow_add_star (r : ℕ) :
    (⟨2, 1⟩ : ℤ√3) ^ r + star ((⟨2, 1⟩ : ℤ√3) ^ r) =
      ((2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re : ℤ) : ℤ√3) := by
  ext
  · simp only [Zsqrtd.re_add, Zsqrtd.re_star, Zsqrtd.re_intCast]; ring
  · simp only [Zsqrtd.im_add, Zsqrtd.im_star, Zsqrtd.im_intCast]; ring

/-- `w(j+2r) + w(j) = 2 H(r) w(j+r)` for `w(j) = (1+√3)(2+√3)^j` and `H(r) = re (2+√3)^r`. -/
lemma w_identity (j r : ℕ) :
    (⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ (j + 2 * r) + (⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ j =
      ((2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re : ℤ) : ℤ√3) * ((⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ (j + r)) := by
  rw [← α_pow_add_star]
  have h := α_pow_mul_star r
  calc (⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ (j + 2 * r) + (⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ j
      = (⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ j * ((⟨2, 1⟩ : ℤ√3) ^ r * (⟨2, 1⟩ : ℤ√3) ^ r +
          (⟨2, 1⟩ : ℤ√3) ^ r * star ((⟨2, 1⟩ : ℤ√3) ^ r)) := by
        rw [h]; simp only [pow_add, two_mul]; ring
    _ = ((⟨2, 1⟩ : ℤ√3) ^ r + star ((⟨2, 1⟩ : ℤ√3) ^ r)) *
          ((⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ (j + r)) := by
        simp only [pow_add]; ring

lemma H_double (r : ℕ) :
    ((⟨2, 1⟩ : ℤ√3) ^ (2 * r)).re = 2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re ^ 2 - 1 := by
  have hn := norm_α_pow r
  rw [Zsqrtd.norm_def] at hn
  rw [two_mul, pow_add, Zsqrtd.re_mul]
  nlinarith [hn]

lemma H_two : ((⟨2, 1⟩ : ℤ√3) ^ 2).re = 7 := by decide
lemma H_three : ((⟨2, 1⟩ : ℤ√3) ^ 3).re = 26 := by decide
lemma H_four : ((⟨2, 1⟩ : ℤ√3) ^ 4).re = 97 := by decide

lemma α_pow_bounds (r : ℕ) : 1 ≤ ((⟨2, 1⟩ : ℤ√3) ^ r).re ∧ 0 ≤ ((⟨2, 1⟩ : ℤ√3) ^ r).im := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
    have ar : (⟨2, 1⟩ : ℤ√3).re = 2 := rfl
    have ai : (⟨2, 1⟩ : ℤ√3).im = 1 := rfl
    rw [ar, ai]
    constructor <;> nlinarith [ih.1, ih.2]

lemma H_pos (r : ℕ) : 0 < ((⟨2, 1⟩ : ℤ√3) ^ r).re := by
  have := (α_pow_bounds r).1; omega

lemma H_pow_two_mod (k : ℕ) (hk : 2 ≤ k) :
    ((⟨2, 1⟩ : ℤ√3) ^ (2 ^ k)).re % 4 = 1 ∧ ((⟨2, 1⟩ : ℤ√3) ^ (2 ^ k)).re % 3 = 1 ∧
      ((⟨2, 1⟩ : ℤ√3) ^ (2 ^ k)).re % 13 = 6 := by
  induction k, hk using Nat.le_induction with
  | base => rw [show (2:ℕ) ^ 2 = 4 by norm_num, H_four]; decide
  | succ k _ ih =>
    rw [pow_succ, mul_comm, H_double]
    obtain ⟨h4, h3, h13⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · have : ((⟨2, 1⟩ : ℤ√3) ^ (2 ^ k)).re ≡ 1 [ZMOD 4] := h4
      exact ((this.pow 2).mul_left 2).sub_right 1
    · have : ((⟨2, 1⟩ : ℤ√3) ^ (2 ^ k)).re ≡ 1 [ZMOD 3] := h3
      exact ((this.pow 2).mul_left 2).sub_right 1
    · have : ((⟨2, 1⟩ : ℤ√3) ^ (2 ^ k)).re ≡ 6 [ZMOD 13] := h13
      exact ((this.pow 2).mul_left 2).sub_right 1

/- ### Residues -/

lemma jacobi_neg39 (h : ℕ) (h4 : h % 4 = 1) (h3 : h % 3 = 1) (h13 : h % 13 = 6) :
    jacobiSym (-39) h = -1 := by
  have hodd : Odd h := Nat.odd_iff.2 (by omega)
  rw [show (-39 : ℤ) = (-1) * 3 * 13 by norm_num, jacobiSym.mul_left, jacobiSym.mul_left,
    jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four h4]
  have q3 := jacobiSym.quadratic_reciprocity_one_mod_four' (a := 3) (b := h) (by decide) h4
  have q13 := jacobiSym.quadratic_reciprocity_one_mod_four' (a := 13) (b := h) (by decide) h4
  push_cast at q3 q13
  rw [q3, q13, jacobiSym.mod_left, jacobiSym.mod_left (h : ℤ) 13]
  have e3 : (h : ℤ) % ((3 : ℕ) : ℤ) = 1 := by push_cast; omega
  have e13 : (h : ℤ) % ((13 : ℕ) : ℤ) = 6 := by push_cast; omega
  rw [e3, e13, jacobiSym.one_left]
  norm_num

lemma no_square_mod (n : ℕ) (c : ℤ) (z : ℕ) (hz : ((z : ℤ) ^ 2) ≡ c [ZMOD n])
    (hc : ¬ IsSquare (c : ZMod n)) : False := by
  apply hc
  refine ⟨(z : ZMod n), ?_⟩
  have := (ZMod.intCast_eq_intCast_iff _ _ n).2 hz
  push_cast at this
  rw [← this]; ring

/- ### The orbit of `u² + 2 = 3 v²`

Statements are made for any `o : ℕ → ℕ × ℕ` with `o 0 = (1, 1)` and
`o (j+1) = (2u + 3v, u + 2v)`; the theorem `k4` uses an explicit iterate. -/

section Orbit

variable {o : ℕ → ℕ × ℕ}
  (ho : o 0 = (1, 1) ∧ ∀ j, o (j + 1) = (2 * (o j).1 + 3 * (o j).2, (o j).1 + 2 * (o j).2))
include ho

lemma orb_complete : ∀ v u : ℕ, u ^ 2 + 2 = 3 * v ^ 2 → ∃ j, o j = (u, v) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro u h
    rcases Nat.lt_or_ge v 2 with hv | hv
    · interval_cases v
      · omega
      · have : u = 1 := by nlinarith
        refine ⟨0, ?_⟩
        rw [ho.1, this]
    · have hu1 : v < u := by nlinarith
      have hu2 : u < 2 * v := by nlinarith
      have hu3 : 3 * v < 2 * u := by nlinarith
      obtain ⟨j, hj⟩ := ih (2 * v - u) (by omega) (2 * u - 3 * v) (by
        have e1 : ((2 * u - 3 * v : ℕ) : ℤ) = 2 * u - 3 * v := by omega
        have e2 : ((2 * v - u : ℕ) : ℤ) = 2 * v - u := by omega
        have h' : ((u : ℤ)) ^ 2 + 2 = 3 * (v : ℤ) ^ 2 := by exact_mod_cast h
        have : (((2 * u - 3 * v : ℕ) : ℤ)) ^ 2 + 2 = 3 * (((2 * v - u : ℕ) : ℤ)) ^ 2 := by
          rw [e1, e2]; nlinarith [h']
        exact_mod_cast this)
      refine ⟨j + 1, ?_⟩
      rw [ho.2, hj]
      simp only [Prod.mk.injEq]
      constructor <;> omega

lemma orb_mod3 (j : ℕ) :
    (j % 6 = 0 → (o j).1 % 3 = 1 ∧ (o j).2 % 3 = 1) ∧
    (j % 6 = 1 → (o j).1 % 3 = 2 ∧ (o j).2 % 3 = 0) ∧
    (j % 6 = 2 → (o j).1 % 3 = 1 ∧ (o j).2 % 3 = 2) ∧
    (j % 6 = 3 → (o j).1 % 3 = 2 ∧ (o j).2 % 3 = 2) ∧
    (j % 6 = 4 → (o j).1 % 3 = 1 ∧ (o j).2 % 3 = 0) ∧
    (j % 6 = 5 → (o j).1 % 3 = 2 ∧ (o j).2 % 3 = 1) := by
  induction j with
  | zero => rw [ho.1]; omega
  | succ j ih => rw [ho.2]; dsimp only; omega

lemma orb_mod_three (j : ℕ) (h1 : (o j).1 % 3 = 1) (h2 : (o j).2 % 3 = 2) : j % 6 = 2 := by
  have := orb_mod3 ho j
  omega

lemma orb_two : o 2 = (19, 11) := by
  have e1 : o 1 = (5, 3) := by
    have h := ho.2 0
    rw [ho.1] at h
    simpa using h
  have h := ho.2 1
  rw [e1] at h
  simpa using h

lemma w_eq (j : ℕ) :
    (⟨1, 1⟩ : ℤ√3) * ⟨2, 1⟩ ^ j = ⟨((o j).1 : ℤ), ((o j).2 : ℤ)⟩ := by
  induction j with
  | zero => rw [ho.1]; ext <;> simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ih, ho.2]
    ext
    · simp only [Zsqrtd.re_mul]; push_cast; ring
    · simp only [Zsqrtd.im_mul]; push_cast; ring

lemma identity_re (j r : ℕ) :
    ((o (j + 2 * r)).1 : ℤ) + (o j).1 = 2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re * (o (j + r)).1 := by
  have h := w_identity j r
  rw [w_eq ho, w_eq ho, w_eq ho] at h
  have := congrArg Zsqrtd.re h
  simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] at this
  linarith

lemma identity_im (j r : ℕ) :
    ((o (j + 2 * r)).2 : ℤ) + (o j).2 = 2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re * (o (j + r)).2 := by
  have h := w_identity j r
  rw [w_eq ho, w_eq ho, w_eq ho] at h
  have := congrArg Zsqrtd.im h
  simp only [Zsqrtd.im_add, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] at this
  linarith

lemma step_re (j r : ℕ) :
    ((o (j + 2 * r)).1 : ℤ) ≡ -((o j).1 : ℤ) [ZMOD 2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re] :=
  (Int.modEq_iff_dvd).2 ⟨-((o (j + r)).1 : ℤ), by linarith [identity_re ho j r]⟩

lemma step_im (j r : ℕ) :
    ((o (j + 2 * r)).2 : ℤ) ≡ -((o j).2 : ℤ) [ZMOD 2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re] :=
  (Int.modEq_iff_dvd).2 ⟨-((o (j + r)).2 : ℤ), by linarith [identity_im ho j r]⟩

/-- After an odd number `2t+1` of steps of length `2r`, the sign flips modulo `2 H(r)`. -/
lemma flip_re (j0 r t : ℕ) :
    ((o (j0 + 2 * r * (2 * t + 1))).1 : ℤ) ≡ -((o j0).1 : ℤ)
      [ZMOD 2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re] := by
  induction t with
  | zero => simpa using step_re ho j0 r
  | succ t ih =>
    have e : j0 + 2 * r * (2 * (t + 1) + 1) = (j0 + 2 * r * (2 * t + 1)) + 2 * r + 2 * r := by
      ring
    rw [e]
    have h2 := (step_re ho (j0 + 2 * r * (2 * t + 1)) r).neg
    rw [neg_neg] at h2
    exact ((step_re ho _ r).trans h2).trans ih

lemma flip_im (j0 r t : ℕ) :
    ((o (j0 + 2 * r * (2 * t + 1))).2 : ℤ) ≡ -((o j0).2 : ℤ)
      [ZMOD 2 * ((⟨2, 1⟩ : ℤ√3) ^ r).re] := by
  induction t with
  | zero => simpa using step_im ho j0 r
  | succ t ih =>
    have e : j0 + 2 * r * (2 * (t + 1) + 1) = (j0 + 2 * r * (2 * t + 1)) + 2 * r + 2 * r := by
      ring
    rw [e]
    have h2 := (step_im ho (j0 + 2 * r * (2 * t + 1)) r).neg
    rw [neg_neg] at h2
    exact ((step_im ho _ r).trans h2).trans ih

/-- No `j ≠ 2` with `j ≡ 2 (mod 6)` makes both `4u+5` and `4v+5` squares. -/
lemma orb_no_squares (j : ℕ) (hj : j % 6 = 2) (hj2 : j ≠ 2) (x y : ℕ)
    (hx : 4 * (o j).1 + 5 = x ^ 2) (hy : 4 * (o j).2 + 5 = y ^ 2) : False := by
  have hne : j - 2 ≠ 0 := by omega
  obtain ⟨e, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd hne
  obtain ⟨t, rfl⟩ := hm
  have hj' : j = 2 + (j - 2) := by omega
  rcases e with _ | _ | _ | k
  · simp at hjm; omega
  · -- j - 2 = 2 m with 3 ∣ m: use r = 3 and the modulus 13
    have h3 : (2 * t + 1) % 3 = 0 := by simp at hjm; omega
    obtain ⟨s, hs⟩ : ∃ s, 2 * t + 1 = 3 * (2 * s + 1) := ⟨(2 * t + 1) / 6, by omega⟩
    have hjj : j = 2 + 2 * 3 * (2 * s + 1) := by simp at hjm; omega
    have key := flip_re ho 2 3 s
    rw [← hjj, H_three, orb_two ho] at key
    have k13 := Int.ModEq.of_dvd (by norm_num : (13 : ℤ) ∣ 2 * 26) key
    have hx' : ((x : ℤ)) ^ 2 = 4 * ((o j).1 : ℤ) + 5 := by exact_mod_cast hx.symm
    have : ((x : ℤ)) ^ 2 ≡ 7 [ZMOD 13] := by
      rw [hx']; exact ((k13.mul_left 4).add_right 5).trans (by decide)
    exact no_square_mod 13 7 x this (by decide)
  · -- j - 2 = 4 m: use r = 2 and the modulus 7
    have hjj : j = 2 + 2 * 2 * (2 * t + 1) := by simp at hjm; omega
    have key := flip_im ho 2 2 t
    rw [← hjj, H_two, orb_two ho] at key
    have k7 := Int.ModEq.of_dvd (by norm_num : (7 : ℤ) ∣ 2 * 7) key
    have hy' : ((y : ℤ)) ^ 2 = 4 * ((o j).2 : ℤ) + 5 := by exact_mod_cast hy.symm
    have : ((y : ℤ)) ^ 2 ≡ 3 [ZMOD 7] := by
      rw [hy']; exact ((k7.mul_left 4).add_right 5).trans (by decide)
    exact no_square_mod 7 3 y this (by decide)
  · -- j - 2 = 2^(k+3) m: use r = 2^(k+2) and a Jacobi symbol
    set r := 2 ^ (k + 2) with hr
    have hjj : j = 2 + 2 * r * (2 * t + 1) := by rw [hr]; rw [hjm] at hj'; rw [hj']; ring
    have key := flip_im ho 2 r t
    rw [← hjj, orb_two ho] at key
    have kH := Int.ModEq.of_dvd (dvd_mul_left (((⟨2, 1⟩ : ℤ√3) ^ r).re) 2) key
    obtain ⟨m4, m3, m13⟩ := H_pow_two_mod (k + 2) (by omega)
    have hpos := H_pos r
    set h := (((⟨2, 1⟩ : ℤ√3) ^ r).re).toNat with hh
    have hcast : (h : ℤ) = ((⟨2, 1⟩ : ℤ√3) ^ r).re := Int.toNat_of_nonneg hpos.le
    have hy' : ((y : ℤ)) ^ 2 = 4 * ((o j).2 : ℤ) + 5 := by exact_mod_cast hy.symm
    have hsq : ((y : ℤ)) ^ 2 ≡ -39 [ZMOD (h : ℤ)] := by
      rw [hy', hcast]; exact ((kH.mul_left 4).add_right 5).trans (by norm_num)
    have hJ : jacobiSym (-39) h = -1 :=
      jacobi_neg39 h (by rw [← hr] at m4; omega) (by rw [← hr] at m3; omega)
        (by rw [← hr] at m13; omega)
    exact no_square_mod h (-39) y hsq (ZMod.nonsquare_of_jacobiSym_eq_neg_one hJ)

end Orbit

/- ### Length 4 -/

lemma lcmInterval_four (n : ℕ) :
    Finset.lcmInterval n 4 = Nat.lcm (n + 1) (Nat.lcm (n + 2) (Nat.lcm (n + 3) (n + 4))) := by
  have hs : Finset.Ioc n (n + 4) = {n + 1, n + 2, n + 3, n + 4} := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]; omega
  simp only [Finset.lcmInterval, hs, Finset.lcm_insert, Finset.lcm_singleton, id, normalize_eq]
  rfl

/-- The window formula: `2 · gcd(n+1, 3) · L = (n+1)(n+2)(n+3)(n+4)`. -/
lemma window_formula (n : ℕ) :
    2 * Nat.gcd (n + 1) 3 * Nat.lcm (n + 1) (Nat.lcm (n + 2) (Nat.lcm (n + 3) (n + 4))) =
      (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
  set X := Nat.lcm (n + 1) (n + 4)
  set Y := (n + 2) * (n + 3)
  have hY : Nat.lcm (n + 2) (n + 3) = Y := by
    apply Nat.Coprime.lcm_eq_mul
    rw [show n + 3 = (n + 2) + 1 by ring]
    exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
  have hL : Nat.lcm (n + 1) (Nat.lcm (n + 2) (Nat.lcm (n + 3) (n + 4))) = Nat.lcm X Y := by
    rw [← hY]
    apply Nat.dvd_antisymm
    · refine Nat.lcm_dvd ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_left _ _))
        (Nat.lcm_dvd ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _))
          (Nat.lcm_dvd ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))
            ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_left _ _))))
    · refine Nat.lcm_dvd (Nat.lcm_dvd (Nat.dvd_lcm_left _ _) ?_) (Nat.lcm_dvd ?_ ?_)
      · exact (Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))
      · exact (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
      · exact (Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))
  have hXd : X ∣ (n + 1) * (n + 4) := Nat.lcm_dvd_mul _ _
  have hYe : Y = (n + 1) * (n + 4) + 2 := by simp only [Y]; ring
  have hg2 : Nat.gcd X Y ∣ 2 := by
    have h1 : Nat.gcd X Y ∣ Nat.gcd ((n + 1) * (n + 4)) Y := Nat.gcd_dvd_gcd_of_dvd_left _ hXd
    rw [hYe, Nat.gcd_self_add_right] at h1
    rw [hYe]
    exact h1.trans (Nat.gcd_dvd_right _ _)
  have h2X : 2 ∣ X := by
    rcases Nat.even_or_odd n with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact (show 2 ∣ n + 4 by omega).trans (Nat.dvd_lcm_right _ _)
    · exact (show 2 ∣ n + 1 by omega).trans (Nat.dvd_lcm_left _ _)
  have h2Y : 2 ∣ Y := by
    simp only [Y]; exact (Nat.even_mul_succ_self (n + 2)).two_dvd
  have hg : Nat.gcd X Y = 2 := Nat.dvd_antisymm hg2 (Nat.dvd_gcd h2X h2Y)
  have hXY := Nat.gcd_mul_lcm X Y
  have ha := Nat.gcd_mul_lcm (n + 1) (n + 4)
  have h3 : Nat.gcd (n + 1) (n + 4) = Nat.gcd (n + 1) 3 := by
    rw [show n + 4 = (n + 1) + 3 by ring, Nat.gcd_self_add_right]
  rw [h3] at ha
  rw [hL, hg] at *
  calc 2 * Nat.gcd (n + 1) 3 * Nat.lcm X Y = Nat.gcd (n + 1) 3 * (2 * Nat.lcm X Y) := by ring
    _ = Nat.gcd (n + 1) 3 * (X * Y) := by rw [hXY]
    _ = (Nat.gcd (n + 1) 3 * X) * Y := by ring
    _ = (n + 1) * (n + 4) * Y := by rw [ha]
    _ = (n + 1) * (n + 2) * (n + 3) * (n + 4) := by simp only [Y]; ring

lemma gcd_three (x : ℕ) : Nat.gcd x 3 = 1 ∨ Nat.gcd x 3 = 3 :=
  (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_right _ _)

lemma mod3_u (B : ℕ) (hB : B % 3 = 0) : (B ^ 2 + 3 * B + 1) % 3 = 1 := by
  simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hB]

lemma mod3_v (A : ℕ) (hA : A % 3 ≠ 0) : (A ^ 2 + 3 * A + 1) % 3 = 2 := by
  have : A % 3 = 1 ∨ A % 3 = 2 := by omega
  rcases this with h | h <;> simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h]

/-- Erdős 677 for windows of length 4. -/
lemma k4 : ∀ m n : ℕ, m ≥ n + 4 → Finset.lcmInterval m 4 ≠ Finset.lcmInterval n 4 := by
  intro m n hmn heq
  obtain ⟨o, hO⟩ : ∃ o : ℕ → ℕ × ℕ, o 0 = (1, 1) ∧
      ∀ j, o (j + 1) = (2 * (o j).1 + 3 * (o j).2, (o j).1 + 2 * (o j).2) :=
    ⟨fun j => (fun p : ℕ × ℕ => (2 * p.1 + 3 * p.2, p.1 + 2 * p.2))^[j] (1, 1), rfl,
      fun j => Function.iterate_succ_apply' _ j _⟩
  rw [lcmInterval_four, lcmInterval_four] at heq
  have wb := window_formula m
  have wa := window_formula n
  rw [heq] at wb
  have hPlt : (n + 1) * (n + 2) * (n + 3) * (n + 4) < (m + 1) * (m + 2) * (m + 3) * (m + 4) :=
    Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (Nat.mul_lt_mul'' (by omega) (by omega)) (by omega))
      (by omega)
  have eu : ((m + 1) ^ 2 + 3 * (m + 1) + 1) ^ 2 = (m + 1) * (m + 2) * (m + 3) * (m + 4) + 1 := by
    ring
  have ev : ((n + 1) ^ 2 + 3 * (n + 1) + 1) ^ 2 = (n + 1) * (n + 2) * (n + 3) * (n + 4) + 1 := by
    ring
  have d3b : Nat.gcd (m + 1) 3 ∣ m + 1 := Nat.gcd_dvd_left _ _
  generalize hPm : (m + 1) * (m + 2) * (m + 3) * (m + 4) = Pm at wb hPlt eu
  generalize hPn : (n + 1) * (n + 2) * (n + 3) * (n + 4) = Pn at wa hPlt ev
  rcases gcd_three (m + 1) with gb | gb <;> rcases gcd_three (n + 1) with ga | ga
  · -- gcd(m+1,3) = gcd(n+1,3) = 1 would give P(m+1) = P(n+1)
    rw [gb] at wb; rw [ga] at wa; omega
  · -- gcd(m+1,3) = 1, gcd(n+1,3) = 3 would give P(m+1) < P(n+1)
    rw [gb] at wb; rw [ga] at wa; omega
  · -- the only possible case: gcd(m+1,3) = 3 and gcd(n+1,3) = 1, so P(m+1) = 3 P(n+1)
    rw [gb] at wb d3b; rw [ga] at wa
    have h3P : Pm = 3 * Pn := by omega
    have hna : ¬ 3 ∣ n + 1 := fun h => by rw [Nat.gcd_eq_right h] at ga; omega
    set u := (m + 1) ^ 2 + 3 * (m + 1) + 1 with hu
    set v := (n + 1) ^ 2 + 3 * (n + 1) + 1 with hv
    have huv : u ^ 2 + 2 = 3 * v ^ 2 := by rw [eu, ev, h3P]; ring
    obtain ⟨j, hj⟩ := orb_complete hO v u huv
    have hu3 : (o j).1 % 3 = 1 := by rw [hj]; exact mod3_u (m + 1) (by omega)
    have hv3 : (o j).2 % 3 = 2 := by rw [hj]; exact mod3_v (n + 1) (by omega)
    have hj6 := orb_mod_three hO j hu3 hv3
    have hj2 : j ≠ 2 := by
      rintro rfl
      rw [orb_two hO] at hj
      have h19 : u = 19 := (Prod.mk.inj hj).1.symm
      rw [hu] at h19
      nlinarith
    exact orb_no_squares hO j hj6 hj2 (2 * (m + 1) + 3) (2 * (n + 1) + 3)
      (by rw [hj]; simp only [hu]; ring) (by rw [hj]; simp only [hv]; ring)
  · -- gcd(m+1,3) = gcd(n+1,3) = 3 would give P(m+1) = P(n+1)
    rw [gb] at wb; rw [ga] at wa; omega

theorem main : H1 → H2 → type_of% @Erdos677.erdos_677 := by
  intro h1 h2 m n k hk hm
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k by omega) with rfl | rfl | rfl | rfl | h5
  · exact small_k m n 1 hk (by norm_num) hm
  · exact small_k m n 2 hk (by norm_num) hm
  · exact h1 m n hm
  · exact k4 m n hm
  · exact h2 m n k h5 hm

end OMA.R_Erdos677_erdos_677_R2
