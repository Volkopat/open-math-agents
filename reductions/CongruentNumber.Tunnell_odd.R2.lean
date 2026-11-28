import FormalConjectures.Wikipedia.CongruentNumber

/-!
Reduction of `CongruentNumber.Tunnell_odd` (Tunnell, *Invent. Math.* 72 (1983), 323-334:
if `n` is an odd squarefree congruent number, then `2 * |A_n| = |B_n|`) to the two
analytic pillars of Tunnell's proof for odd squarefree `n` with `n % 8 ∈ {1, 3}`:
- `H1`: Coates-Wiles theorem (1977) for the CM elliptic curve `E_n : y^2 = x^3 - n^2 * x`
  (existence of a rational point of infinite order implies the analytic continuation of
  `E_n.LSeries` vanishes at `s = 1`), and
- `H2`: Tunnell-Waldspurger special-value formula (1981/1983) expressing the analytic
  continuation of `E_n.LSeries` at `s = 1` as a nonzero multiple of `(2 * |A_n| - |B_n|)^2`.

Everything else in Tunnell's theorem is proved completely in Lean:
1. Finiteness of `A n` and `B n`, the even-`z` bijection identifying `A n` inside `B n`, and
   an unconditional proof (zero hypotheses) of `Tunnell_odd` for all `n % 8 = 5` and
   `n % 8 = 7` via `ZMod 8` obstruction (half of all odd squarefree numbers).
2. Congruent-number to non-2-torsion rational point construction on `E_n : y^2 = x^3 - n^2 * x`
   via the classical parametrization `(x, y) = (c^2 / 4, c * (a^2 - b^2) / 8)` (together with
   the converse reconstruction of a rational right triangle from any affine point with `y ≠ 0`).
3. Complete proof that `E_n(Q)_tors = E_n[2]` (so every affine point with `y ≠ 0` has infinite
   order in `E_n.toAffine.Point`):
   - Exact duplication identity `(x^2 + n^2)^2 - 4*n*(x^3 - n^2*x) = (x^2 - 2*n*x - n^2)^2`
     combined with `irrational_sqrt_two` ruling out 4-torsion.
   - Complete `p`-adic formal-group filtration in local coordinates `(t, s) = (-x/y, -1/y)`
     showing that the kernel of reduction modulo any prime `p > max (2*n) q` contains no
     points of order `q`, hence every point in `<Q>` has `p`-integral coordinates.
   - Explicit reduction-mod-`p` homomorphism `<Q> -> E_n(ZMod p)` with trivial kernel.
   - Supersingular point count `|E_n(ZMod p)| = p + 1` for every prime `p ≡ 3 (mod 4)` with
     `p ∤ n`, combined with Dirichlet's theorem (`p ≡ 2*q + 1 (mod 4*q)`) ruling out every
     odd prime order `q`.
4. Complex-analytic uniqueness at `s = 1` via the Identity Theorem
   (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) on the convex open half-plane
   `{s : ℂ | 1/2 < s.re}` joining `H1` and `H2`.
-/

namespace OMA.R_CongruentNumber_Tunnell_odd_R2

/- === Section 1: Analytic Hypotheses (Coates-Wiles and Tunnell-Waldspurger) === -/

/- Coates-Wiles theorem (1977) for the CM congruent-number elliptic curve
`E_n : y^2 = x^3 - n^2 * x`: for odd squarefree `n` with `n % 8 ∈ {1, 3}`, if `E_n(Q)`
contains a point of infinite order, then `E_n.LSeries` admits an analytic continuation to the
half-plane `{s : ℂ | 1/2 < s.re}` vanishing at `s = 1`. -/
def H1 : Prop :=
  ∀ n : ℕ, Squarefree n → Odd n → (n % 8 = 1 ∨ n % 8 = 3) →
    let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
    (∃ P : W.toAffine.Point, ∀ m : ℕ, 0 < m → m • P ≠ 0) →
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L {s : ℂ | (1 / 2 : ℝ) < s.re} ∧
      (∀ s : ℂ, 2 < s.re → L s = W.LSeries s) ∧ L 1 = 0

/- Tunnell (1983) / Waldspurger (1981) special-value formula for odd squarefree `n` with
`n % 8 ∈ {1, 3}`: `E_n.LSeries` admits an analytic continuation to `{s : ℂ | 1/2 < s.re}`
whose central value `L 1` equals `Ω * (2 * |A_n| - |B_n|)^2` for a nonzero complex period
factor `Ω ≠ 0`. -/
def H2 : Prop :=
  ∀ n : ℕ, Squarefree n → Odd n → (n % 8 = 1 ∨ n % 8 = 3) →
    let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L {s : ℂ | (1 / 2 : ℝ) < s.re} ∧
      (∀ s : ℂ, 2 < s.re → L s = W.LSeries s) ∧
      ∃ Ω : ℂ, Ω ≠ 0 ∧
        L 1 = Ω * ((2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard) ^ 2

/- === Section 2: Quadratic Form Finiteness, Even-z Embedding, and Mod-8 Exclusion === -/

/- Coordinate bound for elements of `CongruentNumber.B n`. -/
lemma mem_B_bounds {n : ℕ} {t : ℤ × ℤ × ℤ} (ht : t ∈ CongruentNumber.B n) :
    -(n : ℤ) ≤ t.1 ∧ t.1 ≤ (n : ℤ) ∧
    -(n : ℤ) ≤ t.2.1 ∧ t.2.1 ≤ (n : ℤ) ∧
    -(n : ℤ) ≤ t.2.2 ∧ t.2.2 ≤ (n : ℤ) := by
  rcases t with ⟨x, y, z⟩
  have h : (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 := ht
  have hx : x ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg y, sq_nonneg z]
  have hy : y ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg x, sq_nonneg z]
  have hz : z ^ 2 ≤ (n : ℤ) := by nlinarith [sq_nonneg x, sq_nonneg y]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/- `CongruentNumber.B n` is finite for every `n : ℕ`. -/
lemma B_finite (n : ℕ) : (CongruentNumber.B n).Finite := by
  let box : Finset (ℤ × ℤ × ℤ) :=
    Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ
      (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ))
  refine box.finite_toSet.subset fun t ht => ?_
  have hb := mem_B_bounds ht
  simp only [box, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hb.1, hb.2.1⟩, ⟨hb.2.2.1, hb.2.2.2.1⟩, ⟨hb.2.2.2.2.1, hb.2.2.2.2.2⟩⟩

/- Embedding `(x, y, z) ↦ (x, y, 2 * z)` identifies `A n` with the even-`z` subset of `B n`. -/
lemma A_image_eq_B_even_z (n : ℕ) :
    (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1, 2 * t.2.2)) '' CongruentNumber.A n =
      {t ∈ CongruentNumber.B n | Even t.2.2} := by
  ext ⟨x, y, w⟩
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x', y', z'⟩, hA, hEq⟩
    simp only [Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl, rfl⟩
    have hA' : (n : ℤ) = 2 * x' ^ 2 + y' ^ 2 + 32 * z' ^ 2 := hA
    refine ⟨?_, ⟨z', by ring⟩⟩
    change (n : ℤ) = 2 * x' ^ 2 + y' ^ 2 + 8 * (2 * z') ^ 2
    linarith
  · rintro ⟨hB, ⟨z, rfl⟩⟩
    refine ⟨(x, y, z), ?_, by simp [two_mul]⟩
    have hB' : (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * (z + z) ^ 2 := hB
    change (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2
    linarith

/- `CongruentNumber.A n` is finite for every `n : ℕ`. -/
lemma A_finite (n : ℕ) : (CongruentNumber.A n).Finite := by
  have hinj : Function.Injective (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1, 2 * t.2.2)) := by
    rintro ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, h3⟩
    have hz : z₁ = z₂ := by omega
    rw [hz]
  have hsub : (fun t : ℤ × ℤ × ℤ => (t.1, t.2.1, 2 * t.2.2)) '' CongruentNumber.A n ⊆
      CongruentNumber.B n := by
    rw [A_image_eq_B_even_z]
    exact fun _ h => h.1
  exact ((B_finite n).subset hsub).of_finite_image hinj.injOn

/- Every square mod 8 lies in `{0, 1, 4}`, so `2*x^2 + y^2 + 8*z^2` is never `5` or `7` mod 8. -/
lemma quadratic_mod_eight_ne (x y z : ℤ) :
    (2 * x ^ 2 + y ^ 2 + 8 * z ^ 2) % 8 ≠ 5 ∧ (2 * x ^ 2 + y ^ 2 + 8 * z ^ 2) % 8 ≠ 7 := by
  have hsq : ∀ u : ℤ, (u ^ 2) % 8 = 0 ∨ (u ^ 2) % 8 = 1 ∨ (u ^ 2) % 8 = 4 := by
    intro u
    have hmod : u % 8 = 0 ∨ u % 8 = 1 ∨ u % 8 = 2 ∨ u % 8 = 3 ∨
        u % 8 = 4 ∨ u % 8 = 5 ∨ u % 8 = 6 ∨ u % 8 = 7 := by omega
    have hsq_mod : (u ^ 2) % 8 = ((u % 8) ^ 2) % 8 := by
      rw [sq, sq, Int.mul_emod]
    rw [hsq_mod]
    rcases hmod with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hrew : (2 * x ^ 2 + y ^ 2 + 8 * z ^ 2) % 8 =
      (2 * ((x ^ 2) % 8) + (y ^ 2) % 8) % 8 := by
    omega
  rw [hrew]
  rcases hsq x with hx | hx | hx <;> rcases hsq y with hy | hy | hy <;>
    rw [hx, hy] <;> decide

/- Unconditional proof of `CongruentNumber.Tunnell_odd` for all `n % 8 = 5` and `n % 8 = 7`
(zero hypotheses): both `A n` and `B n` are empty. -/
lemma Tunnell_odd_of_mod_eight_five_or_seven {n : ℕ} (hmod : n % 8 = 5 ∨ n % 8 = 7) :
    2 * (CongruentNumber.A n).ncard = (CongruentNumber.B n).ncard := by
  have hB : CongruentNumber.B n = ∅ := by
    ext ⟨x, y, z⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hmem
    have heq : (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * z ^ 2 := hmem
    have hne := quadratic_mod_eight_ne x y z
    rw [← heq] at hne
    rcases hmod with h5 | h7 <;> omega
  have hA : CongruentNumber.A n = ∅ := by
    ext ⟨x, y, z⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hmem
    have heq : (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 32 * z ^ 2 := hmem
    have hmemB : (x, y, 2 * z) ∈ CongruentNumber.B n := by
      change (n : ℤ) = 2 * x ^ 2 + y ^ 2 + 8 * (2 * z) ^ 2
      linarith
    rw [hB] at hmemB
    exact hmemB
  rw [hA, hB, Set.ncard_empty]

/- === Section 3: Congruent Number <-> Non-2-Torsion Point on E_n : y^2 = x^3 - n^2 * x === -/

/- Equation and nonsingularity characterizations for `E_n : y^2 = x^3 - n^2 * x` over any field
of characteristic not equal to `2`. -/
lemma congCurve_equation_iff {F : Type*} [Field F] (n : F) (x y : F) :
    (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 - n ^ 2 * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [WeierstrassCurve.toAffine]
  ring_nf

lemma congCurve_nonsingular_of_Y_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (n x y : F)
    (heq : y ^ 2 = x ^ 3 - n ^ 2 * x) (hy : y ≠ 0) :
    (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨(congCurve_equation_iff n x y).mpr heq, Or.inr ?_⟩
  dsimp [WeierstrassCurve.toAffine]
  intro hneg
  have : (2 : F) * y = 0 := by linear_combination hneg
  exact (mul_ne_zero h2 hy) this

/- Rational squares cannot equal `2` (direct corollary of `irrational_sqrt_two`). -/
lemma rat_sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro hq
  have hreal : ((q : ℝ)) ^ 2 = (Real.sqrt 2) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact_mod_cast hq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hreal with h | h
  · exact irrational_sqrt_two ⟨q, h⟩
  · exact irrational_sqrt_two ⟨-q, by push_cast; linarith⟩

/- From `congruentNumber n` (`n ≠ 0`), construct an explicit rational point `(x, y)` on
`E_n : y^2 = x^3 - n^2 * x` with `y ≠ 0` via the classical parametrization
`x = (c / 2)^2`, `y = c * (a^2 - b^2) / 8`. -/
lemma curve_point_of_congruentNumber {n : ℕ} (hn : n ≠ 0) (hcong : CongruentNumber.congruentNumber n) :
    let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
    ∃ x y : ℚ, y ≠ 0 ∧ ∃ h : W.toAffine.Nonsingular x y,
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 := by
  intro W
  obtain ⟨a, b, c, hpyth, harea⟩ := hcong
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hab : a * b = 2 * (n : ℚ) := by linarith
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hab
    exact hnq (by linarith)
  have hc : c ≠ 0 := by
    intro h0
    rw [h0] at hpyth
    have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg b]
  have hab_diff : a ^ 2 - b ^ 2 ≠ 0 := by
    intro hdiff
    have hb2 : b ^ 2 = a ^ 2 := by linarith
    have hc2 : (c / a) ^ 2 = 2 := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 ha)]
      linarith
    exact rat_sq_ne_two (c / a) hc2
  let x : ℚ := c ^ 2 / 4
  let y : ℚ := c * (a ^ 2 - b ^ 2) / 8
  have hy : y ≠ 0 := div_ne_zero (mul_ne_zero hc hab_diff) (by norm_num)
  have heq : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by
    dsimp only [x, y]
    have h4n2 : 4 * (n : ℚ) ^ 2 = a ^ 2 * b ^ 2 := by
      linear_combination (a * b + 2 * (n : ℚ)) * hab.symm
    linear_combination (c ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) / 64) * hpyth +
      (c ^ 2 / 16) * h4n2
  have hns : W.toAffine.Nonsingular x y :=
    congCurve_nonsingular_of_Y_ne_zero (by norm_num) (n : ℚ) x y heq hy
  exact ⟨x, y, hy, hns, WeierstrassCurve.Affine.Point.some_ne_zero hns⟩

/- === Section 4: No 4-Torsion on E_n(Q) === -/

/- Negation formula on `E_n : y^2 = x^3 - n^2 * x`: `negY x y = -y`. -/
lemma congCurve_negY {F : Type*} [Field F] (n x y : F) :
    (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.negY x y = -y := by
  unfold WeierstrassCurve.Affine.negY
  simp

/- Slope, `addX`, and `addY` simplified for `E_n : y^2 = x^3 - n^2 * x`. -/
lemma congCurve_addX {F : Type*} [Field F] (n x₁ x₂ ℓ : F) :
    (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - x₁ - x₂ := by
  unfold WeierstrassCurve.Affine.addX
  simp

lemma congCurve_addY {F : Type*} [Field F] (n x₁ x₂ y₁ ℓ : F) :
    (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.addY x₁ x₂ y₁ ℓ =
      -(ℓ * ((ℓ ^ 2 - x₁ - x₂) - x₁) + y₁) := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
  rw [congCurve_negY, congCurve_addX]

lemma congCurve_slope_self {F : Type*} [Field F] [DecidableEq F] (n x y : F) (hy : y ≠ -y) :
    (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.slope x x y y =
      (3 * x ^ 2 - n ^ 2) / (2 * y) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (by rwa [congCurve_negY]), congCurve_negY]
  dsimp [WeierstrassCurve.toAffine]
  ring_nf

lemma congCurve_slope_ne {F : Type*} [Field F] [DecidableEq F] (n x₁ x₂ y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.slope x₁ x₂ y₁ y₂ =
      (y₁ - y₂) / (x₁ - x₂) := by
  exact WeierstrassCurve.Affine.slope_of_X_ne hx

/- An affine point `(x, y)` on `E_n` has `2 • P = 0` iff `y = 0` (when `char F ≠ 2`). -/
lemma congCurve_two_nsmul_eq_zero_iff {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    (n x y : F) (h : (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.Nonsingular x y) :
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ y = 0 := by
  rw [two_nsmul]
  constructor
  · intro hadd
    by_contra hy
    have hny : y ≠ (WeierstrassCurve.mk (0 : F) 0 0 (-n ^ 2) 0).toAffine.negY x y := by
      rw [congCurve_negY]
      intro hneg
      have : (2 : F) * y = 0 := by linear_combination hneg
      exact (mul_ne_zero h2 hy) this
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hny] at hadd
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hadd
  · intro hy
    subst hy
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by rw [congCurve_negY, neg_zero])

/- Complete algebraic proof that `E_n(Q)` has no points of exact order `4`: for any `n ≠ 0` and
any affine point `P = (x, y)` on `E_n(Q)` with `y ≠ 0`, `4 • P ≠ 0`. -/
lemma congCurve_four_nsmul_ne_zero {n : ℕ} (hn : n ≠ 0) (x y : ℚ)
    (h : (WeierstrassCurve.mk (0 : ℚ) 0 0 (-(n : ℚ) ^ 2) 0).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    (4 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h) ≠ 0 := by
  let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hnpos : (0 : ℚ) < (n : ℚ) := by positivity
  have heq : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := (congCurve_equation_iff (n : ℚ) x y).mp h.1
  have hny : y ≠ W.toAffine.negY x y := by
    rw [congCurve_negY]; intro h0; exact hy (by linarith)
  have h2P := (two_nsmul (WeierstrassCurve.Affine.Point.some x y h)).trans
    (WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h) hny)
  intro h4
  have h4' : (2 : ℕ) • ((2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h)) = 0 := by
    rw [← mul_nsmul]; exact h4
  rw [h2P, congCurve_two_nsmul_eq_zero_iff (by norm_num)] at h4'
  let x₂ : ℚ := W.toAffine.addX x x (W.toAffine.slope x x y y)
  let y₂ : ℚ := W.toAffine.addY x x y (W.toAffine.slope x x y y)
  have hns₂ : W.toAffine.Nonsingular x₂ y₂ :=
    W.toAffine.nonsingular_add h h (by rw [congCurve_negY]; intro h0; exact hny (by rw [congCurve_negY]; exact h0.2))
  have heq₂ : y₂ ^ 2 = x₂ ^ 3 - (n : ℚ) ^ 2 * x₂ :=
    (congCurve_equation_iff (n : ℚ) x₂ y₂).mp hns₂.1
  change y₂ = 0 at h4'
  rw [h4'] at heq₂
  have hx₂_formula : x₂ = (x ^ 2 + (n : ℚ) ^ 2) ^ 2 / (4 * y ^ 2) := by
    dsimp only [x₂]
    rw [congCurve_addX, congCurve_slope_self (n : ℚ) x y (by intro h0; exact hy (by linarith)),
      div_pow, show (2 * y) ^ 2 = 4 * y ^ 2 by ring]
    field_simp [hy]
    linear_combination (-8 * x) * heq
  have hx₂_pos : 0 < x₂ := by
    rw [hx₂_formula]
    have hnum : 0 < (x ^ 2 + (n : ℚ) ^ 2) ^ 2 := sq_pos_of_pos (by positivity)
    have hden : 0 < 4 * y ^ 2 := by positivity
    exact div_pos hnum hden
  have hx₂_roots : x₂ * (x₂ - (n : ℚ)) * (x₂ + (n : ℚ)) = 0 := by
    linear_combination -heq₂
  have hx₂_eq_n : x₂ = (n : ℚ) := by
    rcases mul_eq_zero.mp hx₂_roots with h1 | h3
    · rcases mul_eq_zero.mp h1 with h0 | h2
      · linarith
      · linarith
    · linarith
  have hquad : (x ^ 2 - 2 * (n : ℚ) * x - (n : ℚ) ^ 2) ^ 2 = 0 := by
    have hcross : (x ^ 2 + (n : ℚ) ^ 2) ^ 2 = 4 * (n : ℚ) * y ^ 2 := by
      rw [hx₂_formula] at hx₂_eq_n
      have hden : (4 * y ^ 2 : ℚ) ≠ 0 := by positivity
      have := (div_eq_iff hden).mp hx₂_eq_n
      linarith
    linear_combination hcross + 4 * (n : ℚ) * heq
  have hquad0 : x ^ 2 - 2 * (n : ℚ) * x - (n : ℚ) ^ 2 = 0 := sq_eq_zero_iff.mp hquad
  have hsqrt2 : ((x - (n : ℚ)) / (n : ℚ)) ^ 2 = 2 := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hnq)]
    linear_combination hquad0
  exact rat_sq_ne_two ((x - (n : ℚ)) / (n : ℚ)) hsqrt2

/- === Section 5: p-Adic Formal-Group Filtration (Kernel of Reduction Is Torsion-Free) === -/

/- Elementary `p`-adic valuation helper: `0 <= padicValRat p q <-> ¬ (p ∣ q.den)`. -/
lemma padicValRat_nonneg_iff_not_dvd_den {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ) :
    0 ≤ padicValRat p q ↔ ¬ (p ∣ q.den) := by
  by_cases hq : q = 0
  · subst hq
    simp [hp.out.not_dvd_one]
  · have hnum : (q.num : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr hq
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hval : padicValRat p q = (padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) := by
      conv_lhs => rw [← Rat.num_div_den q]
      rw [padicValRat.div hnum hden, padicValRat.of_int, padicValRat.of_nat]
    rw [hval]
    constructor
    · intro hge hdvd
      have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
      have hndvd_num : ¬ (p ∣ q.num.natAbs) := by
        intro h1
        exact hp.out.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 hdvd)
      have hnum0 : padicValInt p q.num = 0 := by
        unfold padicValInt
        exact padicValNat.eq_zero_of_not_dvd hndvd_num
      have hden1 : 1 ≤ padicValNat p q.den :=
        one_le_padicValNat_of_dvd q.den_nz hdvd
      omega
    · intro hndvd
      have hden0 : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hndvd
      omega

/- `p`-adic valuation lower bound for sums and differences (including zero outcomes). -/
lemma padicValRat_add_ge {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ} {k : ℤ}
    (ha : a = 0 ∨ k ≤ padicValRat p a) (hb : b = 0 ∨ k ≤ padicValRat p b) :
    a + b = 0 ∨ k ≤ padicValRat p (a + b) := by
  by_cases hab : a + b = 0
  · exact Or.inl hab
  · right
    rcases ha with rfl | ha
    · simpa using hb.resolve_left (by simpa using hab)
    · rcases hb with rfl | hb
      · simpa using ha
      · exact le_trans (le_min ha hb) (padicValRat.min_le_padicValRat_add hab)

lemma padicValRat_sub_ge {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ} {k : ℤ}
    (ha : a = 0 ∨ k ≤ padicValRat p a) (hb : b = 0 ∨ k ≤ padicValRat p b) :
    a - b = 0 ∨ k ≤ padicValRat p (a - b) := by
  rw [sub_eq_add_neg]
  refine padicValRat_add_ge ha ?_
  rcases hb with rfl | hb
  · left; simp
  · right; rwa [padicValRat.neg]

lemma padicValRat_mul_ge {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ} {k₁ k₂ : ℤ}
    (ha : a = 0 ∨ k₁ ≤ padicValRat p a) (hb : b = 0 ∨ k₂ ≤ padicValRat p b) :
    a * b = 0 ∨ k₁ + k₂ ≤ padicValRat p (a * b) := by
  by_cases hab : a * b = 0
  · exact Or.inl hab
  · right
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
    rw [padicValRat.mul ha0 hb0]
    exact add_le_add (ha.resolve_left ha0) (hb.resolve_left hb0)

lemma padicValRat_one_add_eq_zero {p : ℕ} [hp : Fact (Nat.Prime p)] {u : ℚ}
    (hu : u = 0 ∨ 1 ≤ padicValRat p u) :
    1 + u ≠ 0 ∧ padicValRat p (1 + u) = 0 := by
  rcases hu with rfl | hu
  · simp
  · have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, padicValRat.zero] at hu
      omega
    have h1u : 1 + u ≠ 0 := by
      intro h0
      have hneg : u = -1 := by linarith
      rw [hneg, padicValRat.neg, padicValRat.one] at hu
      omega
    refine ⟨h1u, ?_⟩
    have hne : padicValRat p (1 : ℚ) ≠ padicValRat p u := by
      rw [padicValRat.one]; omega
    rw [padicValRat.add_eq_min h1u one_ne_zero hu0 hne, padicValRat.one]
    omega

/- On `y^2 = x^3 - n^2 * x` with `p ∤ n`, any point with `padicValRat p x < 0` has
`padicValRat p x = -(2 * r)` and `padicValRat p y = -(3 * r)` for some `1 <= r : ℕ`. -/
lemma padicValRat_pole_structure {p n : ℕ} [hp : Fact (Nat.Prime p)] (hpn : ¬ (p ∣ n))
    {x y : ℚ} (heq : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x) (hx_neg : padicValRat p x < 0) :
    ∃ r : ℕ, 1 ≤ r ∧ x ≠ 0 ∧ y ≠ 0 ∧
      padicValRat p x = -(2 * (r : ℤ)) ∧ padicValRat p y = -(3 * (r : ℤ)) := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, padicValRat.zero] at hx_neg; omega
  have hnq : (n : ℚ) ≠ 0 := by
    intro h0
    have hn0 : n = 0 := by exact_mod_cast h0
    exact hpn (hn0 ▸ dvd_zero p)
  have hvn : padicValRat p (n : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpn]
    rfl
  have hv_x3 : padicValRat p (x ^ 3) = 3 * padicValRat p x := by
    rw [padicValRat.pow]; norm_num
  have hv_n2x : padicValRat p (-((n : ℚ) ^ 2 * x)) = padicValRat p x := by
    rw [padicValRat.neg, padicValRat.mul (pow_ne_zero 2 hnq) hx0, padicValRat.pow, hvn]
    ring
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at heq
    have hxeq : x ^ 3 = (n : ℚ) ^ 2 * x := by linarith
    have hv1 := congrArg (padicValRat p) hxeq
    rw [hv_x3, padicValRat.mul (pow_ne_zero 2 hnq) hx0, padicValRat.pow, hvn] at hv1
    omega
  have hrhs_ne : x ^ 3 + -((n : ℚ) ^ 2 * x) ≠ 0 := by
    rw [← sub_eq_add_neg, ← heq]; exact pow_ne_zero 2 hy0
  have hv_rhs : padicValRat p (x ^ 3 - (n : ℚ) ^ 2 * x) = 3 * padicValRat p x := by
    rw [sub_eq_add_neg, padicValRat.add_eq_min hrhs_ne (pow_ne_zero 3 hx0)
      (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hnq) hx0)) (by omega)]
    omega
  have hv_eq : 2 * padicValRat p y = 3 * padicValRat p x := by
    have := congrArg (padicValRat p) heq
    rw [padicValRat.pow, hv_rhs] at this
    push_cast at this
    linarith
  let r : ℕ := (-padicValRat p x / 2).toNat
  have hr1 : 1 ≤ r := by
    dsimp only [r]; omega
  refine ⟨r, hr1, hx0, hy0, ?_, ?_⟩ <;> dsimp only [r] <;> omega

/- Converse pole detection: if `padicValRat p y < 0`, then `padicValRat p x < 0` as well. -/
lemma padicValRat_X_neg_of_Y_neg {p n : ℕ} [hp : Fact (Nat.Prime p)]
    {x y : ℚ} (heq : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x) (hy_neg : padicValRat p y < 0) :
    padicValRat p x < 0 := by
  by_contra hx_nn
  push Not at hx_nn
  have hx_p : x = 0 ∨ 0 ≤ padicValRat p x := Or.inr hx_nn
  have h1 : x ^ 3 = 0 ∨ 0 ≤ padicValRat p (x ^ 3) := by
    rw [padicValRat.pow]; push_cast; right; linarith
  have h2 : (n : ℚ) ^ 2 * x = 0 ∨ 0 ≤ padicValRat p ((n : ℚ) ^ 2 * x) := by
    have hmul := padicValRat_mul_ge (p := p) (k₁ := 0) (k₂ := 0)
      (Or.inr (by rw [padicValRat.pow, padicValRat.of_nat]; positivity : 0 ≤ padicValRat p ((n : ℚ) ^ 2))) hx_p
    rw [zero_add] at hmul
    exact hmul
  have hsub := padicValRat_sub_ge h1 h2
  rw [← heq] at hsub
  rcases hsub with hy2_0 | hy2_nn
  · have hy0 : y = 0 := sq_eq_zero_iff.mp hy2_0
    rw [hy0, padicValRat.zero] at hy_neg
    omega
  · rw [padicValRat.pow] at hy2_nn
    omega

/- Pure polynomial identity for the formal-group addition law in opaque variables `(t₁, t₂, lam, nu)`,
eliminating `let`-unfolding overhead inside `formal_group_add`. -/
lemma formal_group_poly_identity (n t₁ t₂ lam nu x₃ : ℚ)
    (hnu : nu ≠ 0) (hd1 : lam * t₁ + nu ≠ 0) (hd2 : lam * t₂ + nu ≠ 0)
    (hlamx : lam * x₃ - 1 ≠ 0) (h1nl2 : 1 - n ^ 2 * lam ^ 2 ≠ 0)
    (hx₃ : x₃ = (lam / nu) ^ 2 - t₁ / (lam * t₁ + nu) - t₂ / (lam * t₂ + nu))
    (hP1 : (1 - n ^ 2 * lam ^ 2) * t₁ ^ 3 - 2 * n ^ 2 * lam * nu * t₁ ^ 2 -
      (lam + n ^ 2 * nu ^ 2) * t₁ - nu = 0)
    (hQsec : -lam ^ 2 * n ^ 2 * t₁ ^ 2 - lam ^ 2 * n ^ 2 * t₁ * t₂ -
      lam ^ 2 * n ^ 2 * t₂ ^ 2 - 2 * lam * n ^ 2 * nu * t₁ -
      2 * lam * n ^ 2 * nu * t₂ - lam - n ^ 2 * nu ^ 2 +
      t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 = 0) :
    nu * x₃ / (lam * x₃ - 1) = t₁ + t₂ - (2 * n ^ 2 * lam * nu) / (1 - n ^ 2 * lam ^ 2) := by
  have hD : nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hnu) hd1) hd2
  have hx₃_num : x₃ * (nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu)) =
      lam ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu) -
      t₁ * nu ^ 2 * (lam * t₂ + nu) -
      t₂ * nu ^ 2 * (lam * t₁ + nu) := by
    rw [hx₃]
    field_simp [hnu, hd1, hd2]
  have hbig_ne : (lam * x₃ - 1) * (nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu)) ≠ 0 :=
    mul_ne_zero hlamx hD
  have hmul_div : nu * x₃ / (lam * x₃ - 1) * (lam * x₃ - 1) = nu * x₃ :=
    div_mul_cancel₀ _ hlamx
  have hstep1 :
      ((nu * x₃ / (lam * x₃ - 1) - (t₁ + t₂)) * (1 - n ^ 2 * lam ^ 2) +
        2 * n ^ 2 * lam * nu) * (lam * x₃ - 1) =
      (nu * x₃ - (t₁ + t₂) * (lam * x₃ - 1)) * (1 - n ^ 2 * lam ^ 2) +
        2 * n ^ 2 * lam * nu * (lam * x₃ - 1) := by
    linear_combination (1 - n ^ 2 * lam ^ 2) * hmul_div
  have hbig_zero :
      ((nu * x₃ / (lam * x₃ - 1) - (t₁ + t₂)) * (1 - n ^ 2 * lam ^ 2) +
        2 * n ^ 2 * lam * nu) *
        ((lam * x₃ - 1) * (nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu))) = 0 := by
    rw [← mul_assoc, hstep1]
    have hstep2 :
        ((nu * x₃ - (t₁ + t₂) * (lam * x₃ - 1)) * (1 - n ^ 2 * lam ^ 2) +
          2 * n ^ 2 * lam * nu * (lam * x₃ - 1)) *
          (nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu)) =
        (nu * (x₃ * (nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu))) -
          (t₁ + t₂) * (lam * (x₃ * (nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu))) -
            nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu))) *
          (1 - n ^ 2 * lam ^ 2) +
        2 * n ^ 2 * lam * nu *
          (lam * (x₃ * (nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu))) -
            nu ^ 2 * (lam * t₁ + nu) * (lam * t₂ + nu)) := by ring
    rw [hstep2, hx₃_num]
    linear_combination
      (lam ^ 2 * (lam ^ 3 - 3 * nu ^ 2)) * hP1 +
      (-lam * (lam ^ 4 * t₁ + lam ^ 3 * nu - 3 * lam * nu ^ 2 * t₁ - 2 * nu ^ 3)) * hQsec
  have hcleared := (mul_eq_zero.mp hbig_zero).resolve_right hbig_ne
  have hsub_eq : nu * x₃ / (lam * x₃ - 1) - (t₁ + t₂) =
      -(2 * n ^ 2 * lam * nu) / (1 - n ^ 2 * lam ^ 2) := by
    rw [eq_div_iff h1nl2]
    linear_combination hcleared
  rw [neg_div] at hsub_eq
  linarith

/- Formal-group addition law on `E_n(Q)` in local coordinates `t = -x/y`, `s = -1/y`:
for any prime `p ∤ n` and any `r >= 1`, the filtration set
`K_r = {0} ∪ {(x, y) | padicValRat p x <= -2*r}` is closed under addition, and the local
parameter `t` is additive modulo `p^(5*r)`. -/
lemma formal_group_add {p n r : ℕ} [hp : Fact (Nat.Prime p)] (hpn : ¬ (p ∣ n)) (hr : 1 ≤ r) :
    let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
    let inKr : W.toAffine.Point → Prop := fun P =>
      match P with
      | .zero => True
      | .some x _ _ => padicValRat p x ≤ -(2 * (r : ℤ))
    let tOf : W.toAffine.Point → ℚ := fun P =>
      match P with
      | .zero => 0
      | .some x y _ => if y = 0 then 0 else -x / y
    ∀ P₁ P₂ : W.toAffine.Point, inKr P₁ → inKr P₂ →
      inKr (P₁ + P₂) ∧
      (tOf (P₁ + P₂) - (tOf P₁ + tOf P₂) = 0 ∨
        5 * (r : ℤ) ≤ padicValRat p (tOf (P₁ + P₂) - (tOf P₁ + tOf P₂))) := by
  intro W inKr tOf P₁ P₂ hK₁ hK₂
  have hnq : (n : ℚ) ≠ 0 := by
    intro h0
    have hn0 : n = 0 := by exact_mod_cast h0
    exact hpn (hn0 ▸ dvd_zero p)
  have hvn : padicValRat p (n : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpn]
    rfl
  cases P₁ with
  | zero =>
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
    refine ⟨hK₂, Or.inl ?_⟩
    dsimp only [tOf]; ring
  | some x₁ y₁ h₁ =>
    cases P₂ with
    | zero =>
      rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero]
      refine ⟨hK₁, Or.inl ?_⟩
      dsimp only [tOf]; ring
    | some x₂ y₂ h₂ =>
      have heq₁ : y₁ ^ 2 = x₁ ^ 3 - (n : ℚ) ^ 2 * x₁ := (congCurve_equation_iff (n : ℚ) x₁ y₁).mp h₁.1
      have heq₂ : y₂ ^ 2 = x₂ ^ 3 - (n : ℚ) ^ 2 * x₂ := (congCurve_equation_iff (n : ℚ) x₂ y₂).mp h₂.1
      have hx₁_neg : padicValRat p x₁ < 0 := by dsimp only [inKr] at hK₁; omega
      have hx₂_neg : padicValRat p x₂ < 0 := by dsimp only [inKr] at hK₂; omega
      obtain ⟨r₁, hr₁, hx₁0, hy₁0, hvx₁, hvy₁⟩ := padicValRat_pole_structure hpn heq₁ hx₁_neg
      obtain ⟨r₂, hr₂, hx₂0, hy₂0, hvx₂, hvy₂⟩ := padicValRat_pole_structure hpn heq₂ hx₂_neg
      have hr₁_ge : (r : ℤ) ≤ (r₁ : ℤ) := by dsimp only [inKr] at hK₁; omega
      have hr₂_ge : (r : ℤ) ≤ (r₂ : ℤ) := by dsimp only [inKr] at hK₂; omega
      by_cases hopp : x₁ = x₂ ∧ y₁ = -y₂
      · rcases hopp with ⟨rfl, hy_opp⟩
        have hadd0 : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) +
            WeierstrassCurve.Affine.Point.some x₁ y₂ h₂ = 0 :=
          WeierstrassCurve.Affine.Point.add_of_Y_eq rfl (by rw [congCurve_negY]; exact hy_opp)
        rw [hadd0]
        refine ⟨trivial, Or.inl ?_⟩
        dsimp only [tOf]
        simp only [hy₁0, hy₂0, ↓reduceIte]
        rw [hy_opp]
        field_simp [hy₂0]
        ring
      · have hnot_opp : ¬ (x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
          rwa [congCurve_negY]
        have hadd_some := WeierstrassCurve.Affine.Point.add_some (h₁ := h₁) (h₂ := h₂) hnot_opp
        let m : ℚ := W.toAffine.slope x₁ x₂ y₁ y₂
        let x₃ : ℚ := W.toAffine.addX x₁ x₂ m
        let y₃ : ℚ := W.toAffine.addY x₁ x₂ y₁ m
        let t₁ : ℚ := -x₁ / y₁
        let s₁ : ℚ := -1 / y₁
        let t₂ : ℚ := -x₂ / y₂
        let s₂ : ℚ := -1 / y₂
        have ht₁0 : t₁ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₁0) hy₁0
        have hs₁0 : s₁ ≠ 0 := div_ne_zero (by norm_num) hy₁0
        have ht₂0 : t₂ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₂0) hy₂0
        have hs₂0 : s₂ ≠ 0 := div_ne_zero (by norm_num) hy₂0
        have hvt₁ : padicValRat p t₁ = (r₁ : ℤ) := by
          dsimp only [t₁]
          rw [padicValRat.div (neg_ne_zero.mpr hx₁0) hy₁0, padicValRat.neg, hvx₁, hvy₁]
          omega
        have hvs₁ : padicValRat p s₁ = 3 * (r₁ : ℤ) := by
          dsimp only [s₁]
          rw [padicValRat.div (by norm_num) hy₁0, padicValRat.neg, padicValRat.one, hvy₁]
          omega
        have hvt₂ : padicValRat p t₂ = (r₂ : ℤ) := by
          dsimp only [t₂]
          rw [padicValRat.div (neg_ne_zero.mpr hx₂0) hy₂0, padicValRat.neg, hvx₂, hvy₂]
          omega
        have hvs₂ : padicValRat p s₂ = 3 * (r₂ : ℤ) := by
          dsimp only [s₂]
          rw [padicValRat.div (by norm_num) hy₂0, padicValRat.neg, padicValRat.one, hvy₂]
          omega
        have hts₁ : s₁ = t₁ ^ 3 - (n : ℚ) ^ 2 * t₁ * s₁ ^ 2 := by
          dsimp only [t₁, s₁]
          field_simp [hy₁0]
          linear_combination -heq₁
        have hts₂ : s₂ = t₂ ^ 3 - (n : ℚ) ^ 2 * t₂ * s₂ ^ 2 := by
          dsimp only [t₂, s₂]
          field_simp [hy₂0]
          linear_combination -heq₂
        let denom_lam : ℚ := 1 + (n : ℚ) ^ 2 * t₁ * (s₁ + s₂)
        have hv_dlam_term : (n : ℚ) ^ 2 * t₁ * (s₁ + s₂) = 0 ∨
            4 * (r : ℤ) ≤ padicValRat p ((n : ℚ) ^ 2 * t₁ * (s₁ + s₂)) := by
          have h1 : (n : ℚ) ^ 2 * t₁ = 0 ∨ (r : ℤ) ≤ padicValRat p ((n : ℚ) ^ 2 * t₁) := by
            right
            rw [padicValRat.mul (pow_ne_zero 2 hnq) ht₁0, padicValRat.pow, hvn, hvt₁]
            omega
          have h2 : s₁ + s₂ = 0 ∨ 3 * (r : ℤ) ≤ padicValRat p (s₁ + s₂) :=
            padicValRat_add_ge (Or.inr (by omega)) (Or.inr (by omega))
          have hmul := padicValRat_mul_ge h1 h2
          simpa [show (r : ℤ) + 3 * (r : ℤ) = 4 * (r : ℤ) by ring] using hmul
        have ⟨hdlam0, hv_dlam⟩ : denom_lam ≠ 0 ∧ padicValRat p denom_lam = 0 :=
          padicValRat_one_add_eq_zero (hv_dlam_term.imp id (by omega))
        let num_lam : ℚ := t₂ ^ 2 + t₁ * t₂ + t₁ ^ 2 - (n : ℚ) ^ 2 * s₂ ^ 2
        let lam : ℚ := num_lam / denom_lam
        let nu : ℚ := s₁ - lam * t₁
        have hv_lam : lam = 0 ∨ 2 * (r : ℤ) ≤ padicValRat p lam := by
          have hv_nlam : num_lam = 0 ∨ 2 * (r : ℤ) ≤ padicValRat p num_lam := by
            have ha : t₂ ^ 2 = 0 ∨ 2 * (r : ℤ) ≤ padicValRat p (t₂ ^ 2) := by
              right; rw [padicValRat.pow, hvt₂]; omega
            have hb : t₁ * t₂ = 0 ∨ 2 * (r : ℤ) ≤ padicValRat p (t₁ * t₂) := by
              right; rw [padicValRat.mul ht₁0 ht₂0, hvt₁, hvt₂]; omega
            have hc : t₁ ^ 2 = 0 ∨ 2 * (r : ℤ) ≤ padicValRat p (t₁ ^ 2) := by
              right; rw [padicValRat.pow, hvt₁]; omega
            have hd : (n : ℚ) ^ 2 * s₂ ^ 2 = 0 ∨ 2 * (r : ℤ) ≤ padicValRat p ((n : ℚ) ^ 2 * s₂ ^ 2) := by
              right
              rw [padicValRat.mul (pow_ne_zero 2 hnq) (pow_ne_zero 2 hs₂0),
                padicValRat.pow, padicValRat.pow, hvn, hvs₂]
              omega
            exact padicValRat_sub_ge (padicValRat_add_ge (padicValRat_add_ge ha hb) hc) hd
          by_cases hlam0 : lam = 0
          · exact Or.inl hlam0
          · right
            have hnlam0 : num_lam ≠ 0 := by
              intro h0; exact hlam0 (by dsimp only [lam]; rw [h0, zero_div])
            dsimp only [lam]
            rw [padicValRat.div hnlam0 hdlam0, hv_dlam, sub_zero]
            exact hv_nlam.resolve_left hnlam0
        have hv_nu : nu = 0 ∨ 3 * (r : ℤ) ≤ padicValRat p nu := by
          have hlt : lam * t₁ = 0 ∨ 3 * (r : ℤ) ≤ padicValRat p (lam * t₁) := by
            have := padicValRat_mul_ge hv_lam (Or.inr (by omega : (r : ℤ) ≤ padicValRat p t₁))
            simpa [show 2 * (r : ℤ) + (r : ℤ) = 3 * (r : ℤ) by ring] using this
          exact padicValRat_sub_ge (Or.inr (by omega : 3 * (r : ℤ) ≤ padicValRat p s₁)) hlt
        have hs₂_line : s₂ = lam * t₂ + nu := by
          have hdiff : (s₂ - s₁) * denom_lam = (t₂ - t₁) * num_lam := by
            dsimp only [denom_lam, num_lam]
            linear_combination hts₂ - hts₁
          have hlam_eq : (s₂ - s₁) = lam * (t₂ - t₁) := by
            dsimp only [lam]
            rw [div_mul_eq_mul_div, eq_div_iff hdlam0]
            linarith
          dsimp only [nu]
          linarith
        have hnu0 : nu ≠ 0 := by
          intro hnu_zero
          have hs₁_eq : s₁ = lam * t₁ := by dsimp only [nu] at hnu_zero; linarith
          have hs₂_eq : s₂ = lam * t₂ := by rw [hnu_zero, add_zero] at hs₂_line; exact hs₂_line
          have hlam_x₁ : lam = 1 / x₁ := by
            dsimp only [t₁, s₁] at hs₁_eq
            field_simp [hx₁0, hy₁0] at hs₁_eq ⊢
            linarith
          have hx_eq : x₁ = x₂ := by
            have hlam_x₂ : lam = 1 / x₂ := by
              dsimp only [t₂, s₂] at hs₂_eq
              field_simp [hx₂0, hy₂0] at hs₂_eq ⊢
              linarith
            rw [hlam_x₁] at hlam_x₂
            field_simp [hx₁0, hx₂0] at hlam_x₂
            linarith
          have hy_eq : y₁ = y₂ := by
            have hy2 : y₁ ^ 2 = y₂ ^ 2 := by rw [heq₁, heq₂, hx_eq]
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2 with h | h
            · exact h
            · exact False.elim (hopp ⟨hx_eq, h⟩)
          subst hx_eq; subst hy_eq
          have hlam_def : lam * denom_lam = num_lam := div_mul_cancel₀ num_lam hdlam0
          have h2s₁ : 2 * s₁ = 0 := by
            have h1 : lam * t₁ = s₁ := hs₁_eq.symm
            dsimp only [denom_lam, num_lam] at hlam_def
            linear_combination -t₁ * hlam_def + (1 + 2 * (n : ℚ) ^ 2 * t₁ * s₁) * h1 + 3 * hts₁
          exact hs₁0 (by linarith)
        have hm_eq : m = lam / nu := by
          by_cases hx_eq : x₁ = x₂
          · have hy_eq : y₁ = y₂ := by
              have hy2 : y₁ ^ 2 = y₂ ^ 2 := by rw [heq₁, heq₂, hx_eq]
              rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2 with h | h
              · exact h
              · exact False.elim (hopp ⟨hx_eq, h⟩)
            subst hx_eq; subst hy_eq
            dsimp only [m]
            rw [congCurve_slope_self (n : ℚ) x₁ y₁ (by intro h0; exact hy₁0 (by linarith))]
            rw [div_eq_div_iff (mul_ne_zero (by norm_num) hy₁0) hnu0]
            have hlam_def : lam * denom_lam = num_lam := div_mul_cancel₀ num_lam hdlam0
            have hlam_clear : lam * (y₁ ^ 2 + 2 * (n : ℚ) ^ 2 * x₁) = 3 * x₁ ^ 2 - (n : ℚ) ^ 2 := by
              dsimp only [denom_lam, num_lam, t₁, s₁, t₂, s₂] at hlam_def
              field_simp [hy₁0] at hlam_def
              linear_combination hlam_def
            have hnu_clear : nu * y₁ = -1 + lam * x₁ := by
              have hnu_def : nu = s₁ - lam * t₁ := rfl
              dsimp only [t₁, s₁] at hnu_def
              field_simp [hy₁0] at hnu_def
              linarith
            have hmul_y : ((3 * x₁ ^ 2 - (n : ℚ) ^ 2) * nu - 2 * y₁ * lam) * y₁ = 0 := by
              linear_combination (3 * x₁ ^ 2 - (n : ℚ) ^ 2) * hnu_clear + hlam_clear - 3 * lam * heq₁
            have hzero := (mul_eq_zero.mp hmul_y).resolve_right hy₁0
            linarith
          · dsimp only [m]
            rw [congCurve_slope_ne (n : ℚ) x₁ x₂ y₁ y₂ hx_eq]
            rw [div_eq_div_iff (sub_ne_zero.mpr hx_eq) hnu0]
            have hnu1 : nu * y₁ = -1 + lam * x₁ := by
              have hs_rel : nu = s₁ - lam * t₁ := rfl
              dsimp only [t₁, s₁] at hs_rel
              field_simp [hy₁0] at hs_rel
              linarith
            have hnu2 : nu * y₂ = -1 + lam * x₂ := by
              have hs₂_rel : s₂ - lam * t₂ = nu := by linarith
              dsimp only [t₂, s₂] at hs₂_rel
              field_simp [hy₂0] at hs₂_rel
              linarith
            linarith
        have hdenom_1nl2 : 1 - (n : ℚ) ^ 2 * lam ^ 2 ≠ 0 ∧
            padicValRat p (1 - (n : ℚ) ^ 2 * lam ^ 2) = 0 := by
          rw [sub_eq_add_neg]
          refine padicValRat_one_add_eq_zero ?_
          have h1 : (n : ℚ) ^ 2 * lam ^ 2 = 0 ∨ 4 * (r : ℤ) ≤ padicValRat p ((n : ℚ) ^ 2 * lam ^ 2) := by
            rcases hv_lam with h0 | hv
            · left; rw [h0]; ring
            · right
              have hlam0 : lam ≠ 0 := by
                intro h0; rw [h0, padicValRat.zero] at hv; omega
              rw [padicValRat.mul (pow_ne_zero 2 hnq) (pow_ne_zero 2 hlam0),
                padicValRat.pow, padicValRat.pow, hvn]
              omega
          rcases h1 with h0 | hv
          · left; rw [h0, neg_zero]
          · right; rw [padicValRat.neg]; omega
        have hnu_x1y1 : lam * x₁ - nu * y₁ = 1 := by
          have hnu_def : nu = s₁ - lam * t₁ := rfl
          dsimp only [t₁, s₁] at hnu_def
          field_simp [hy₁0] at hnu_def
          linarith
        have hy₃_def : y₃ = -(m * (x₃ - x₁) + y₁) := by
          dsimp only [x₃, y₃]
          rw [congCurve_addY, congCurve_addX]
        have hy₃_lin : nu * y₃ = -(lam * x₃ - 1) := by
          have h1 := hy₃_def
          rw [hm_eq] at h1
          have h2 : nu * y₃ = -(lam * (x₃ - x₁) + nu * y₁) := by
            field_simp [hnu0] at h1
            linarith
          linarith
        have hy₃0 : y₃ ≠ 0 := by
          intro hy₃_zero
          have hns₃ := W.toAffine.nonsingular_add h₁ h₂ hnot_opp
          have heq₃ : y₃ ^ 2 = x₃ ^ 3 - (n : ℚ) ^ 2 * x₃ :=
            (congCurve_equation_iff (n : ℚ) x₃ y₃).mp hns₃.1
          rw [hy₃_zero] at heq₃
          have hlin : lam * x₃ - 1 = 0 := by
            rw [hy₃_zero, mul_zero] at hy₃_lin
            linarith
          have hlam0 : lam ≠ 0 := by
            intro h0; rw [h0, zero_mul] at hlin; norm_num at hlin
          have hx₃_eq : x₃ = 1 / lam := by
            rw [eq_div_iff hlam0]; linarith
          have hx₃_roots : x₃ * (x₃ - (n : ℚ)) * (x₃ + (n : ℚ)) = 0 := by
            linear_combination -heq₃
          rcases mul_eq_zero.mp hx₃_roots with h1' | h3'
          · rcases mul_eq_zero.mp h1' with hx0 | hxn
            · rw [hx0, mul_zero] at hlin; norm_num at hlin
            · have hlam_n : lam = 1 / (n : ℚ) := by
                have : x₃ = (n : ℚ) := by linarith
                rw [this] at hx₃_eq
                field_simp [hnq, hlam0] at hx₃_eq ⊢; linarith
              have hv := hv_lam.resolve_left hlam0
              rw [hlam_n, padicValRat.div one_ne_zero hnq, padicValRat.one, hvn] at hv
              omega
          · have hlam_n : lam = -1 / (n : ℚ) := by
              have : x₃ = -(n : ℚ) := by linarith
              rw [this] at hx₃_eq
              field_simp [hnq, hlam0] at hx₃_eq ⊢; linarith
            have hv := hv_lam.resolve_left hlam0
            rw [hlam_n, padicValRat.div (by norm_num) hnq, padicValRat.neg, padicValRat.one, hvn] at hv
            omega
        have hlamx₃_ne : lam * x₃ - 1 ≠ 0 := by
          intro h0
          rw [h0, neg_zero] at hy₃_lin
          exact mul_ne_zero hnu0 hy₃0 hy₃_lin
        have ht₃_formula : -x₃ / y₃ =
            t₁ + t₂ - (2 * (n : ℚ) ^ 2 * lam * nu) / (1 - (n : ℚ) ^ 2 * lam ^ 2) := by
          have hs₁_line : s₁ = lam * t₁ + nu := by dsimp only [nu]; ring
          have hP1 : (1 - (n : ℚ) ^ 2 * lam ^ 2) * t₁ ^ 3 - 2 * (n : ℚ) ^ 2 * lam * nu * t₁ ^ 2 -
              (lam + (n : ℚ) ^ 2 * nu ^ 2) * t₁ - nu = 0 := by
            have h1 := hts₁
            rw [hs₁_line] at h1
            linear_combination -h1
          have hQsec : -lam ^ 2 * (n : ℚ) ^ 2 * t₁ ^ 2 - lam ^ 2 * (n : ℚ) ^ 2 * t₁ * t₂ -
              lam ^ 2 * (n : ℚ) ^ 2 * t₂ ^ 2 - 2 * lam * (n : ℚ) ^ 2 * nu * t₁ -
              2 * lam * (n : ℚ) ^ 2 * nu * t₂ - lam - (n : ℚ) ^ 2 * nu ^ 2 +
              t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 = 0 := by
            have hlam_def : lam * denom_lam = num_lam := div_mul_cancel₀ num_lam hdlam0
            dsimp only [denom_lam, num_lam] at hlam_def
            rw [hs₁_line, hs₂_line] at hlam_def
            linear_combination -hlam_def
          have hx₁_ts : x₁ = t₁ / s₁ := by dsimp only [t₁, s₁]; field_simp [hy₁0]
          have hx₂_ts : x₂ = t₂ / s₂ := by dsimp only [t₂, s₂]; field_simp [hy₂0]
          have hx₃_def : x₃ = m ^ 2 - x₁ - x₂ := congCurve_addX (n : ℚ) x₁ x₂ m
          have hx₃_ts : x₃ = (lam / nu) ^ 2 - t₁ / (lam * t₁ + nu) - t₂ / (lam * t₂ + nu) := by
            rw [hx₃_def, hm_eq, hx₁_ts, hx₂_ts, hs₁_line, hs₂_line]
          have hs₁_lne : lam * t₁ + nu ≠ 0 := by rw [← hs₁_line]; exact hs₁0
          have hs₂_lne : lam * t₂ + nu ≠ 0 := by rw [← hs₂_line]; exact hs₂0
          have ht₃_eq : -x₃ / y₃ = nu * x₃ / (lam * x₃ - 1) := by
            rw [div_eq_div_iff hy₃0 hlamx₃_ne]
            linear_combination -x₃ * hy₃_lin
          rw [ht₃_eq]
          exact formal_group_poly_identity (n : ℚ) t₁ t₂ lam nu x₃
            hnu0 hs₁_lne hs₂_lne hlamx₃_ne hdenom_1nl2.1 hx₃_ts hP1 hQsec
        have hv_err :
            -((2 * (n : ℚ) ^ 2 * lam * nu) / (1 - (n : ℚ) ^ 2 * lam ^ 2)) = 0 ∨
            5 * (r : ℤ) ≤ padicValRat p
              (-((2 * (n : ℚ) ^ 2 * lam * nu) / (1 - (n : ℚ) ^ 2 * lam ^ 2))) := by
          have hnum_ge : 2 * (n : ℚ) ^ 2 * lam * nu = 0 ∨
              5 * (r : ℤ) ≤ padicValRat p (2 * (n : ℚ) ^ 2 * lam * nu) := by
            have h2n2 : (2 * (n : ℚ) ^ 2 : ℚ) = 0 ∨ 0 ≤ padicValRat p (2 * (n : ℚ) ^ 2) := by
              right
              rw [padicValRat.mul (by norm_num) (pow_ne_zero 2 hnq),
                padicValRat.pow, hvn, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
                padicValRat.of_nat]
              positivity
            have hlam_nu := padicValRat_mul_ge hv_lam hv_nu
            have hmul := padicValRat_mul_ge h2n2 hlam_nu
            simpa [mul_assoc, show (0 : ℤ) + (2 * (r : ℤ) + 3 * (r : ℤ)) = 5 * (r : ℤ) by ring] using hmul
          by_cases h0 : (2 * (n : ℚ) ^ 2 * lam * nu) / (1 - (n : ℚ) ^ 2 * lam ^ 2) = 0
          · left; rw [h0, neg_zero]
          · right
            have hnum0 : 2 * (n : ℚ) ^ 2 * lam * nu ≠ 0 := by
              intro hz; exact h0 (by rw [hz, zero_div])
            rw [padicValRat.neg, padicValRat.div hnum0 hdenom_1nl2.1, hdenom_1nl2.2, sub_zero]
            exact hnum_ge.resolve_left hnum0
        have hv_t₃ : -x₃ / y₃ = 0 ∨ (r : ℤ) ≤ padicValRat p (-x₃ / y₃) := by
          have h12 : t₁ + t₂ = 0 ∨ (r : ℤ) ≤ padicValRat p (t₁ + t₂) :=
            padicValRat_add_ge (Or.inr (by omega)) (Or.inr (by omega))
          have herr_r : -((2 * (n : ℚ) ^ 2 * lam * nu) / (1 - (n : ℚ) ^ 2 * lam ^ 2)) = 0 ∨
              (r : ℤ) ≤ padicValRat p
                (-((2 * (n : ℚ) ^ 2 * lam * nu) / (1 - (n : ℚ) ^ 2 * lam ^ 2))) :=
            hv_err.imp id (by omega)
          rw [ht₃_formula, sub_eq_add_neg]
          exact padicValRat_add_ge h12 herr_r
        have hs₃_eq : -1 / y₃ = lam * (-x₃ / y₃) - nu := by
          field_simp [hy₃0]
          have h1 : lam * x₃ - 1 = -(nu * y₃) := by linarith
          linear_combination h1
        have hv_s₃ : 3 * (r : ℤ) ≤ padicValRat p (-1 / y₃) := by
          have hs₃_ne : -1 / y₃ ≠ 0 := div_ne_zero (by norm_num) hy₃0
          have hlt₃ := padicValRat_mul_ge hv_lam hv_t₃
          have hlt₃' : lam * (-x₃ / y₃) = 0 ∨ 3 * (r : ℤ) ≤ padicValRat p (lam * (-x₃ / y₃)) := by
            rw [show 3 * (r : ℤ) = 2 * (r : ℤ) + (r : ℤ) by ring]
            exact hlt₃
          have hsub := padicValRat_sub_ge hlt₃' hv_nu
          rw [← hs₃_eq] at hsub
          exact hsub.resolve_left hs₃_ne
        have hvy₃_le : padicValRat p y₃ ≤ -(3 * (r : ℤ)) := by
          rw [padicValRat.div (by norm_num) hy₃0, padicValRat.neg, padicValRat.one] at hv_s₃
          omega
        have hns₃ := W.toAffine.nonsingular_add h₁ h₂ hnot_opp
        have heq₃ : y₃ ^ 2 = x₃ ^ 3 - (n : ℚ) ^ 2 * x₃ :=
          (congCurve_equation_iff (n : ℚ) x₃ y₃).mp hns₃.1
        have hx₃_neg : padicValRat p x₃ < 0 :=
          padicValRat_X_neg_of_Y_neg heq₃ (by omega)
        obtain ⟨r₃, _, _, _, hvx₃, hvy₃⟩ := padicValRat_pole_structure hpn heq₃ hx₃_neg
        rw [hadd_some]
        refine ⟨?_, ?_⟩
        · change padicValRat p x₃ ≤ -(2 * (r : ℤ))
          omega
        · change (if y₃ = 0 then 0 else -x₃ / y₃) -
            ((if y₁ = 0 then 0 else -x₁ / y₁) + (if y₂ = 0 then 0 else -x₂ / y₂)) = 0 ∨
            5 * (r : ℤ) ≤ padicValRat p ((if y₃ = 0 then 0 else -x₃ / y₃) -
              ((if y₁ = 0 then 0 else -x₁ / y₁) + (if y₂ = 0 then 0 else -x₂ / y₂)))
          simp only [hy₁0, hy₂0, hy₃0, ↓reduceIte]
          have hdiff_eq : -x₃ / y₃ - (-x₁ / y₁ + -x₂ / y₂) =
              -((2 * (n : ℚ) ^ 2 * lam * nu) / (1 - (n : ℚ) ^ 2 * lam ^ 2)) := by
            dsimp only [t₁, t₂] at ht₃_formula
            linarith
          rw [hdiff_eq]
          exact hv_err

/- Consequence of the formal-group filtration: for any odd prime `q`, any prime `p > max (2*n) q`,
and any point `R` on `E_n(Q)` with `q • R = 0`, `R` cannot lie in the kernel of reduction mod `p`
(i.e. `R = 0` or `0 <= padicValRat p x` and `0 <= padicValRat p y`). -/
lemma torsion_p_integral {n q p : ℕ} [hp : Fact (Nat.Prime p)] (hpq : q < p) (hpn : ¬ (p ∣ n))
    (hq : 0 < q) :
    let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
    ∀ R : W.toAffine.Point, q • R = 0 →
      match R with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat p x ∧ 0 ≤ padicValRat p y := by
  intro W R hqR
  cases R with
  | zero => trivial
  | some x y h =>
    have heq : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := (congCurve_equation_iff (n : ℚ) x y).mp h.1
    have hx_nn : 0 ≤ padicValRat p x := by
      by_contra hx_neg
      push Not at hx_neg
      obtain ⟨r, hr1, hx0, hy0, hvx, hvy⟩ := padicValRat_pole_structure hpn heq hx_neg
      let inKr : W.toAffine.Point → Prop := fun P =>
        match P with
        | .zero => True
        | .some x' _ _ => padicValRat p x' ≤ -(2 * (r : ℤ))
      let tOf : W.toAffine.Point → ℚ := fun P =>
        match P with
        | .zero => 0
        | .some x' y' _ => if y' = 0 then 0 else -x' / y'
      let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h
      have hP_in : inKr P := by dsimp only [inKr, P]; omega
      have hind : ∀ k : ℕ, inKr (k • P) ∧
          (tOf (k • P) - (k : ℚ) * tOf P = 0 ∨
            5 * (r : ℤ) ≤ padicValRat p (tOf (k • P) - (k : ℚ) * tOf P)) := by
        intro k
        induction k with
        | zero =>
          refine ⟨trivial, Or.inl ?_⟩
          simp [tOf]
        | succ k ih =>
          rw [succ_nsmul]
          have hstep := formal_group_add (p := p) (n := n) (r := r) hpn hr1 (k • P) P ih.1 hP_in
          refine ⟨hstep.1, ?_⟩
          have hsplit : tOf (k • P + P) - ((k + 1 : ℕ) : ℚ) * tOf P =
              (tOf (k • P + P) - (tOf (k • P) + tOf P)) + (tOf (k • P) - (k : ℚ) * tOf P) := by
            push_cast; ring
          rw [hsplit]
          exact padicValRat_add_ge hstep.2 ih.2
      have hq_step := (hind q).2
      have hqP : q • P = 0 := hqR
      rw [hqP] at hq_step
      have ht0 : tOf 0 = 0 := rfl
      rw [ht0, zero_sub] at hq_step
      have htP_ne : tOf P ≠ 0 := by
        dsimp only [tOf, P]
        simp only [hy0, ↓reduceIte]
        exact div_ne_zero (neg_ne_zero.mpr hx0) hy0
      have hv_tP : padicValRat p (tOf P) = (r : ℤ) := by
        dsimp only [tOf, P]
        simp only [hy0, ↓reduceIte]
        rw [padicValRat.div (neg_ne_zero.mpr hx0) hy0, padicValRat.neg, hvx, hvy]
        omega
      have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hv_q : padicValRat p (q : ℚ) = 0 := by
        rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hq hpq)]
        rfl
      rcases hq_step with h0 | hv_ge
      · exact mul_ne_zero hq_ne htP_ne (neg_eq_zero.mp h0)
      · rw [padicValRat.neg, padicValRat.mul hq_ne htP_ne, hv_q, hv_tP] at hv_ge
        omega
    have hy_nn : 0 ≤ padicValRat p y := by
      by_contra hy_neg
      push Not at hy_neg
      have := padicValRat_X_neg_of_Y_neg heq hy_neg
      omega
    exact ⟨hx_nn, hy_nn⟩

/- === Section 6: Reduction Mod p Homomorphism, Supersingular Count, and Infinite Order === -/

/- Modular reduction of `p`-integral rationals into `ZMod p` preserves `0, 1, -, +, *`,
and detects positive `p`-adic valuation. -/
lemma ratModP_zero {p : ℕ} : (((0 : ℚ).num : ZMod p) * (((0 : ℚ).den : ZMod p))⁻¹) = 0 := by
  simp

lemma ratModP_int {p : ℕ} (z : ℤ) :
    (((z : ℚ).num : ZMod p) * (((z : ℚ).den : ZMod p))⁻¹) = (z : ZMod p) := by
  simp

lemma ratModP_nat {p : ℕ} (k : ℕ) :
    (((k : ℚ).num : ZMod p) * (((k : ℚ).den : ZMod p))⁻¹) = (k : ZMod p) := by
  simp

lemma ratModP_neg {p : ℕ} (a : ℚ) :
    ((((-a).num : ZMod p) * (((-a).den : ZMod p))⁻¹)) =
      -(((a.num : ZMod p) * ((a.den : ZMod p))⁻¹)) := by
  simp [Rat.neg_num, Rat.neg_den, neg_mul]

lemma ratModP_add {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    (((a + b).num : ZMod p) * (((a + b).den : ZMod p))⁻¹) =
      ((a.num : ZMod p) * ((a.den : ZMod p))⁻¹) +
      ((b.num : ZMod p) * ((b.den : ZMod p))⁻¹) := by
  have ha' : ¬ (p ∣ a.den) := (padicValRat_nonneg_iff_not_dvd_den a).mp ha
  have hb' : ¬ (p ∣ b.den) := (padicValRat_nonneg_iff_not_dvd_den b).mp hb
  have hab' : ¬ (p ∣ (a + b).den) := fun hd =>
    (hp.out.dvd_mul.mp (dvd_trans hd (Rat.add_den_dvd a b))).elim ha' hb'
  have hda : (a.den : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hdb : (b.den : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hdab : ((a + b).den : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hint : (a + b).num * ((a.den : ℤ) * (b.den : ℤ)) =
      (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)) * ((a + b).den : ℤ) := by
    have hq : ((a + b).num : ℚ) / ((a + b).den : ℚ) =
        (a.num : ℚ) / (a.den : ℚ) + (b.num : ℚ) / (b.den : ℚ) := by
      rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
    have hq' : ((a + b).num : ℚ) * ((a.den : ℚ) * (b.den : ℚ)) =
        ((a.num : ℚ) * (b.den : ℚ) + (b.num : ℚ) * (a.den : ℚ)) * ((a + b).den : ℚ) := by
      have ha0 : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
      have hb0 : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
      have hab0 : ((a + b).den : ℚ) ≠ 0 := by exact_mod_cast (a + b).den_nz
      field_simp [ha0, hb0, hab0] at hq
      linarith
    exact_mod_cast hq'
  have hmod : (((a + b).num : ZMod p) * ((a.den : ZMod p) * (b.den : ZMod p))) =
      ((a.num : ZMod p) * (b.den : ZMod p) + (b.num : ZMod p) * (a.den : ZMod p)) *
        ((a + b).den : ZMod p) := by
    have := congrArg (Int.cast (R := ZMod p)) hint
    simpa using this
  field_simp [hda, hdb, hdab]
  linear_combination hmod

lemma ratModP_sub {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    (((a - b).num : ZMod p) * (((a - b).den : ZMod p))⁻¹) =
      ((a.num : ZMod p) * ((a.den : ZMod p))⁻¹) -
      ((b.num : ZMod p) * ((b.den : ZMod p))⁻¹) := by
  rw [sub_eq_add_neg, ratModP_add ha (by rwa [padicValRat.neg]), ratModP_neg, sub_eq_add_neg]

lemma ratModP_mul {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) :
    (((a * b).num : ZMod p) * (((a * b).den : ZMod p))⁻¹) =
      ((a.num : ZMod p) * ((a.den : ZMod p))⁻¹) *
      ((b.num : ZMod p) * ((b.den : ZMod p))⁻¹) := by
  have ha' : ¬ (p ∣ a.den) := (padicValRat_nonneg_iff_not_dvd_den a).mp ha
  have hb' : ¬ (p ∣ b.den) := (padicValRat_nonneg_iff_not_dvd_den b).mp hb
  have hab' : ¬ (p ∣ (a * b).den) := fun hd =>
    (hp.out.dvd_mul.mp (dvd_trans hd (Rat.mul_den_dvd a b))).elim ha' hb'
  have hda : (a.den : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hdb : (b.den : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hdab : ((a * b).den : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hint : (a * b).num * ((a.den : ℤ) * (b.den : ℤ)) =
      (a.num * b.num) * ((a * b).den : ℤ) := by
    have hq : ((a * b).num : ℚ) / ((a * b).den : ℚ) =
        ((a.num : ℚ) / (a.den : ℚ)) * ((b.num : ℚ) / (b.den : ℚ)) := by
      rw [Rat.num_div_den, Rat.num_div_den, Rat.num_div_den]
    have hq' : ((a * b).num : ℚ) * ((a.den : ℚ) * (b.den : ℚ)) =
        ((a.num : ℚ) * (b.num : ℚ)) * ((a * b).den : ℚ) := by
      have ha0 : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
      have hb0 : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
      have hab0 : ((a * b).den : ℚ) ≠ 0 := by exact_mod_cast (a * b).den_nz
      field_simp [ha0, hb0, hab0] at hq
      linarith
    exact_mod_cast hq'
  have hmod : (((a * b).num : ZMod p) * ((a.den : ZMod p) * (b.den : ZMod p))) =
      ((a.num : ZMod p) * (b.num : ZMod p)) * ((a * b).den : ZMod p) := by
    have := congrArg (Int.cast (R := ZMod p)) hint
    simpa using this
  field_simp [hda, hdb, hdab]
  linear_combination hmod

lemma padicValRat_nonneg_of_add {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) : 0 ≤ padicValRat p (a + b) := by
  rcases padicValRat_add_ge (Or.inr ha) (Or.inr hb) with h0 | hv
  · rw [h0, padicValRat.zero]
  · exact hv

lemma padicValRat_nonneg_of_sub {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) : 0 ≤ padicValRat p (a - b) := by
  rw [sub_eq_add_neg]; exact padicValRat_nonneg_of_add ha (by rwa [padicValRat.neg])

lemma padicValRat_nonneg_of_mul {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b) : 0 ≤ padicValRat p (a * b) := by
  rcases padicValRat_mul_ge (Or.inr ha) (Or.inr hb) with h0 | hv
  · rw [h0, padicValRat.zero]
  · exact hv

lemma ratModP_pow {p : ℕ} [hp : Fact (Nat.Prime p)] {a : ℚ} (ha : 0 ≤ padicValRat p a) (k : ℕ) :
    ((((a ^ k).num : ZMod p) * (((a ^ k).den : ZMod p))⁻¹)) =
      (((a.num : ZMod p) * ((a.den : ZMod p))⁻¹)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ratModP_mul _ ha, ih]
    rw [padicValRat.pow]; positivity

lemma ratModP_div_of_ne_zero {p : ℕ} [hp : Fact (Nat.Prime p)] {a b : ℚ}
    (ha : 0 ≤ padicValRat p a) (hb : 0 ≤ padicValRat p b)
    (hb_mod : ((b.num : ZMod p) * ((b.den : ZMod p))⁻¹) ≠ 0) :
    0 ≤ padicValRat p (a / b) ∧
    (((a / b).num : ZMod p) * (((a / b).den : ZMod p))⁻¹) =
      ((a.num : ZMod p) * ((a.den : ZMod p))⁻¹) /
      ((b.num : ZMod p) * ((b.den : ZMod p))⁻¹) := by
  have hb0 : b ≠ 0 := by
    intro h0; subst h0; exact hb_mod (by simp)
  have hb_num_mod : (b.num : ZMod p) ≠ 0 := left_ne_zero_of_mul hb_mod
  have hndvd_num : ¬ (p ∣ b.num.natAbs) := by
    intro hd
    apply hb_num_mod
    have : (p : ℤ) ∣ b.num := Int.natCast_dvd.mpr hd
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd b.num p).mpr this
  have hvb0 : padicValRat p b = 0 := by
    have hdn : ¬ (p ∣ b.den) := (padicValRat_nonneg_iff_not_dvd_den b).mp hb
    have hnum_q : (b.num : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr hb0
    have hden_q : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
    conv_lhs => rw [← Rat.num_div_den b]
    rw [padicValRat.div hnum_q hden_q, padicValRat.of_int, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hdn]
    unfold padicValInt
    rw [padicValNat.eq_zero_of_not_dvd hndvd_num]
    simp
  have hdiv_nn : 0 ≤ padicValRat p (a / b) := by
    by_cases ha0 : a = 0
    · rw [ha0, zero_div, padicValRat.zero]
    · rw [padicValRat.div ha0 hb0, hvb0, sub_zero]; exact ha
  refine ⟨hdiv_nn, ?_⟩
  rw [eq_div_iff hb_mod, ← ratModP_mul hdiv_nn hb, div_mul_cancel₀ a hb0]

/- Every point on `E_n(ZMod p)` (`p` odd prime, `p ∤ n`) is nonsingular. -/
lemma congCurve_ZMod_nonsingular {p n : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (hpn : ¬ (p ∣ n)) (x y : ZMod p)
    (heq : y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x) :
    (WeierstrassCurve.mk (0 : ZMod p) 0 0 (-(n : ZMod p) ^ 2) 0).toAffine.Nonsingular x y := by
  have h2z : (2 : ZMod p) ≠ 0 := by
    rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
  have hnz : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  by_cases hy : y = 0
  · rw [WeierstrassCurve.Affine.nonsingular_iff]
    refine ⟨(congCurve_equation_iff (n : ZMod p) x y).mpr heq, Or.inl ?_⟩
    dsimp [WeierstrassCurve.toAffine]
    intro hderiv
    rw [hy, zero_pow (by norm_num)] at heq
    have hroots : x * (x - (n : ZMod p)) * (x + (n : ZMod p)) = 0 := by
      linear_combination -heq
    rcases mul_eq_zero.mp hroots with h1 | h3
    · rcases mul_eq_zero.mp h1 with hx0 | hxn
      · rw [hx0] at hderiv
        have : (n : ZMod p) ^ 2 = 0 := by linear_combination hderiv
        exact pow_ne_zero 2 hnz this
      · have hx : x = (n : ZMod p) := sub_eq_zero.mp hxn
        rw [hx] at hderiv
        have : (2 : ZMod p) * (n : ZMod p) ^ 2 = 0 := by linear_combination -hderiv
        exact mul_ne_zero h2z (pow_ne_zero 2 hnz) this
    · have hx : x = -(n : ZMod p) := eq_neg_of_add_eq_zero_left h3
      rw [hx] at hderiv
      have : (2 : ZMod p) * (n : ZMod p) ^ 2 = 0 := by linear_combination -hderiv
      exact mul_ne_zero h2z (pow_ne_zero 2 hnz) this
  · exact congCurve_nonsingular_of_Y_ne_zero h2z (n : ZMod p) x y heq hy

/- Supersingular point count: for every prime `p ≡ 3 (mod 4)` with `p ∤ n`,
`Fintype.card (E_n (ZMod p)).toAffine.Point = p + 1`. -/
lemma congCurve_ZMod_card {p n : ℕ} [hp : Fact (Nat.Prime p)] (hp4 : p % 4 = 3)
    (hpn : ¬ (p ∣ n)) :
    let Wp : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, -(n : ZMod p) ^ 2, 0⟩
    Nat.card Wp.toAffine.Point = p + 1 := by
  intro Wp
  have hp2 : p ≠ 2 := by omega
  have h2z : (2 : ZMod p) ≠ 0 := by
    rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
  have hneg1_nsq : ¬ IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]; exact not_not.mpr hp4
  let f : ZMod p → ZMod p := fun x => x ^ 3 - (n : ZMod p) ^ 2 * x
  let c : ZMod p → ℕ := fun x => (Finset.univ.filter fun y : ZMod p => y ^ 2 = f x).card
  have hcard_sq : ∀ a : ZMod p, a ≠ 0 →
      (IsSquare a → (Finset.univ.filter fun y : ZMod p => y ^ 2 = a).card = 2) ∧
      (¬ IsSquare a → (Finset.univ.filter fun y : ZMod p => y ^ 2 = a).card = 0) := by
    intro a ha
    constructor
    · rintro ⟨r, rfl⟩
      have hr : r ≠ 0 := fun h0 => ha (by rw [h0, mul_zero])
      have hr_ne : r ≠ -r := by
        intro h; have : (2 : ZMod p) * r = 0 := by linear_combination h
        exact mul_ne_zero h2z hr this
      have hset : (Finset.univ.filter fun y : ZMod p => y ^ 2 = r * r) = {r, -r} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, ← sq]
        exact sq_eq_sq_iff_eq_or_eq_neg
      rw [hset, Finset.card_pair hr_ne]
    · intro hnsq
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y _ hy
      exact hnsq ⟨y, by rw [← sq, hy]⟩
  have hxor : ∀ a : ZMod p, a ≠ 0 → (IsSquare a ∧ ¬ IsSquare (-a)) ∨ (¬ IsSquare a ∧ IsSquare (-a)) := by
    intro a ha
    have hnot_both : ¬ (IsSquare a ∧ IsSquare (-a)) := by
      rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      have hr0 : r ≠ 0 := fun h0 => ha (by rw [hr, h0, mul_zero])
      apply hneg1_nsq
      refine ⟨s / r, ?_⟩
      field_simp [hr0]
      linear_combination hs + hr
    have heither : IsSquare a ∨ IsSquare (-a) := by
      let k : ℕ := p / 4
      have hp_eq : p = 4 * k + 3 := by dsimp only [k]; omega
      have hflt : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
      have hpow2 : (a ^ (2 * k + 1)) ^ 2 = 1 := by
        rw [← pow_mul, show (2 * k + 1) * 2 = p - 1 by omega]
        exact hflt
      have hsq_u : (a ^ (k + 1)) ^ 2 = a * a ^ (2 * k + 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1; omega
      rcases sq_eq_one_iff.mp hpow2 with h1 | hm1
      · left; refine ⟨a ^ (k + 1), ?_⟩; rw [← sq, hsq_u, h1, mul_one]
      · right; refine ⟨a ^ (k + 1), ?_⟩; rw [← sq, hsq_u, hm1, mul_neg_one]
    rcases heither with h | h
    · exact Or.inl ⟨h, fun h' => hnot_both ⟨h, h'⟩⟩
    · exact Or.inr ⟨fun h' => hnot_both ⟨h', h⟩, h⟩
  have hpair : ∀ x : ZMod p, c x + c (-x) = 2 := by
    intro x
    have hfneg : f (-x) = -f x := by dsimp only [f]; ring
    by_cases hfx : f x = 0
    · have hc1 : (Finset.univ.filter fun y : ZMod p => y ^ 2 = 0).card = 1 := by
        have hset : (Finset.univ.filter fun y : ZMod p => y ^ 2 = 0) = {0} := by
          ext y; simp
        rw [hset, Finset.card_singleton]
      dsimp only [c]
      rw [hfneg, hfx, neg_zero, hc1]
    · dsimp only [c]
      rw [hfneg]
      rcases hxor (f x) hfx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [(hcard_sq (f x) hfx).1 h1, (hcard_sq (-f x) (neg_ne_zero.mpr hfx)).2 h2]
      · rw [(hcard_sq (f x) hfx).2 h1, (hcard_sq (-f x) (neg_ne_zero.mpr hfx)).1 h2]
  have hsum_c : ∑ x : ZMod p, c x = p := by
    have hsym : ∑ x : ZMod p, c (-x) = ∑ x : ZMod p, c x :=
      Equiv.sum_comp (Equiv.neg (ZMod p)) c
    have h2sum : 2 * ∑ x : ZMod p, c x = 2 * p := by
      calc
        2 * ∑ x : ZMod p, c x = (∑ x : ZMod p, c x) + ∑ x : ZMod p, c (-x) := by
          rw [hsym, two_mul]
        _ = ∑ x : ZMod p, (c x + c (-x)) := (Finset.sum_add_distrib).symm
        _ = ∑ _x : ZMod p, 2 := Finset.sum_congr rfl fun x _ => hpair x
        _ = 2 * p := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
    omega
  have hcard_ns :
      Nat.card { xy : ZMod p × ZMod p // Wp.toAffine.Nonsingular xy.1 xy.2 } = p := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfilt : (Finset.univ.filter fun xy : ZMod p × ZMod p => Wp.toAffine.Nonsingular xy.1 xy.2) =
        (Finset.univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = f xy.1) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => (congCurve_equation_iff (n : ZMod p) x y).mp h.1,
        fun h => congCurve_ZMod_nonsingular hp2 hpn x y h⟩
    rw [hfilt]
    have hfib : (Finset.univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = f xy.1) =
        Finset.univ.biUnion fun x : ZMod p =>
          (Finset.univ.filter fun y : ZMod p => y ^ 2 = f x).map
            ⟨fun y => (x, y), fun _ _ h => (Prod.mk.inj h).2⟩ := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_map]
      constructor
      · intro h; exact ⟨x, y, h, rfl⟩
      · rintro ⟨x', y', hy', hEq⟩
        rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact hy'
    rw [hfib, Finset.card_biUnion]
    · simp_rw [Finset.card_map]
      exact hsum_c
    · intro x₁ _ x₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_map] at h1 h2
      obtain ⟨_, _, hEq1⟩ := h1
      obtain ⟨_, _, hEq2⟩ := h2
      exact hne ((Prod.mk.inj hEq1).1.trans (Prod.mk.inj hEq2).1.symm)
  have hcard_opt :
      Nat.card (WithZero { xy : ZMod p × ZMod p // Wp.toAffine.Nonsingular xy.1 xy.2 }) =
        Nat.card { xy : ZMod p × ZMod p // Wp.toAffine.Nonsingular xy.1 xy.2 } + 1 := by
    classical
    change Nat.card (Option { xy : ZMod p × ZMod p // Wp.toAffine.Nonsingular xy.1 xy.2 }) = _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_option
  calc
    Nat.card Wp.toAffine.Point
        = Nat.card (WithZero { xy : ZMod p × ZMod p // Wp.toAffine.Nonsingular xy.1 xy.2 }) :=
          Nat.card_congr Wp.toAffine.nonsingularPointEquiv
    _ = Nat.card { xy : ZMod p × ZMod p // Wp.toAffine.Nonsingular xy.1 xy.2 } + 1 := hcard_opt
    _ = p + 1 := by rw [hcard_ns]

/- Reduction mod `p` exists on `p`-integral points of `E_n(Q)`, maps `0 ↦ 0`, sends every
`p`-integral affine point to a nonzero point of `E_n(ZMod p)`, and preserves addition whenever
the sum is also `p`-integral (good reduction of `E_n` at any odd prime `p ∤ n`). -/
lemma congCurve_red_add {p n : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hpn : ¬ (p ∣ n)) :
    let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
    let Wp : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, -(n : ZMod p) ^ 2, 0⟩
    let isInt : W.toAffine.Point → Prop := fun P =>
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat p x ∧ 0 ≤ padicValRat p y
    ∃ red : ∀ P : W.toAffine.Point, isInt P → Wp.toAffine.Point,
      (∀ h0, red 0 h0 = 0) ∧
      (∀ x y h hi, red (WeierstrassCurve.Affine.Point.some x y h) hi ≠ 0) ∧
      (∀ (P₁ P₂ : W.toAffine.Point) (h₁ : isInt P₁) (h₂ : isInt P₂) (h₁₂ : isInt (P₁ + P₂)),
        red (P₁ + P₂) h₁₂ = red P₁ h₁ + red P₂ h₂) := by
  intro W Wp isInt
  let modP : ℚ → ZMod p := fun q => (q.num : ZMod p) * ((q.den : ZMod p))⁻¹
  let red : ∀ P : W.toAffine.Point, isInt P → Wp.toAffine.Point := fun P hP =>
    match P, hP with
    | .zero, _ => 0
    | .some x y h, ⟨hx, hy⟩ =>
      WeierstrassCurve.Affine.Point.some (modP x) (modP y) (by
        apply congCurve_ZMod_nonsingular hp2 hpn
        have heq : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := (congCurve_equation_iff (n : ℚ) x y).mp h.1
        have hmod := congrArg modP heq
        dsimp only [modP] at hmod ⊢
        rw [ratModP_pow hy 2,
          ratModP_sub (by rw [padicValRat.pow]; positivity)
            (padicValRat_nonneg_of_mul (by rw [padicValRat.pow, padicValRat.of_nat]; positivity) hx),
          ratModP_pow hx 3,
          ratModP_mul (by rw [padicValRat.pow, padicValRat.of_nat]; positivity) hx,
          ratModP_pow (by rw [padicValRat.of_nat]; positivity) 2, ratModP_nat] at hmod
        exact hmod)
  refine ⟨red, fun _ => rfl, fun x y h ⟨hx, hy⟩ => WeierstrassCurve.Affine.Point.some_ne_zero _, ?_⟩
  intro P₁ P₂ h₁ h₂ h₁₂
  have h2z : (2 : ZMod p) ≠ 0 := by
    rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
  have hnz : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h2_nn : 0 ≤ padicValRat p (2 : ℚ) := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]; positivity
  have h3_nn : 0 ≤ padicValRat p (3 : ℚ) := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]; positivity
  have hn_nn : 0 ≤ padicValRat p (n : ℚ) := by rw [padicValRat.of_nat]; positivity
  have hn2_nn : 0 ≤ padicValRat p ((n : ℚ) ^ 2) := by rw [padicValRat.pow]; positivity
  have hred_eq : ∀ {A B : W.toAffine.Point} (hA : isInt A) (hB : isInt B),
      A = B → red A hA = red B hB := by
    rintro _ _ _ _ rfl
    rfl
  cases P₁ with
  | zero =>
    have h0 : (WeierstrassCurve.Affine.Point.zero : W.toAffine.Point) + P₂ = P₂ := by
      rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
    rw [hred_eq h₁₂ h₂ h0]
    dsimp only [red]
    rw [zero_add]
  | some x₁ y₁ hns₁ =>
    cases P₂ with
    | zero =>
      have h0 : (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ : W.toAffine.Point) +
          WeierstrassCurve.Affine.Point.zero =
          WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ := by
        rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero]
      rw [hred_eq h₁₂ h₁ h0]
      dsimp only [red]
      rw [add_zero]
    | some x₂ y₂ hns₂ =>
      rcases h₁ with ⟨hx₁, hy₁⟩
      rcases h₂ with ⟨hx₂, hy₂⟩
      have heq₁ : y₁ ^ 2 = x₁ ^ 3 - (n : ℚ) ^ 2 * x₁ :=
        (congCurve_equation_iff (n : ℚ) x₁ y₁).mp hns₁.1
      have heq₂ : y₂ ^ 2 = x₂ ^ 3 - (n : ℚ) ^ 2 * x₂ :=
        (congCurve_equation_iff (n : ℚ) x₂ y₂).mp hns₂.1
      by_cases hopp : x₁ = x₂ ∧ y₁ = -y₂
      · rcases hopp with ⟨rfl, hy_opp⟩
        have hadd0 : (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ : W.toAffine.Point) +
            WeierstrassCurve.Affine.Point.some x₁ y₂ hns₂ = 0 :=
          WeierstrassCurve.Affine.Point.add_of_Y_eq rfl (by rw [congCurve_negY]; exact hy_opp)
        have hlhs : red (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ +
            WeierstrassCurve.Affine.Point.some x₁ y₂ hns₂) h₁₂ = 0 :=
          hred_eq h₁₂ (by trivial : isInt 0) hadd0
        rw [hlhs]
        symm
        dsimp only [red]
        exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl (by
          rw [congCurve_negY, hy_opp]; exact ratModP_neg y₂)
      · have hnot_opp : ¬ (x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by rwa [congCurve_negY]
        have hadd_some := WeierstrassCurve.Affine.Point.add_some (h₁ := hns₁) (h₂ := hns₂) hnot_opp
        let m : ℚ := W.toAffine.slope x₁ x₂ y₁ y₂
        let x₃ : ℚ := W.toAffine.addX x₁ x₂ m
        let y₃ : ℚ := W.toAffine.addY x₁ x₂ y₁ m
        have h₁₂' : 0 ≤ padicValRat p x₃ ∧ 0 ≤ padicValRat p y₃ := by
          have := h₁₂
          rw [hadd_some] at this
          exact this
        have hx₃_def : x₃ = m ^ 2 - x₁ - x₂ := congCurve_addX (n : ℚ) x₁ x₂ m
        have hy₃_def : y₃ = -(m * (x₃ - x₁) + y₁) := by
          dsimp only [x₃, y₃]
          rw [congCurve_addY, congCurve_addX]
        have hm_nn : 0 ≤ padicValRat p m := by
          have hm2 : m ^ 2 = x₃ + x₁ + x₂ := by linarith
          have hm2_nn : 0 ≤ padicValRat p (m ^ 2) := by
            rw [hm2]; exact padicValRat_nonneg_of_add (padicValRat_nonneg_of_add h₁₂'.1 hx₁) hx₂
          rw [padicValRat.pow] at hm2_nn
          omega
        have hnot_opp_mod : ¬ (modP x₁ = modP x₂ ∧ modP y₁ = Wp.toAffine.negY (modP x₂) (modP y₂)) := by
          rw [congCurve_negY]
          rintro ⟨hx_mod, hy_mod⟩
          have hbar_y_eq : modP y₁ = modP y₂ := by
            by_cases hx_eq : x₁ = x₂
            · have hy2 : y₁ ^ 2 = y₂ ^ 2 := by rw [heq₁, heq₂, hx_eq]
              rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2 with h | h
              · rw [h]
              · exact False.elim (hopp ⟨hx_eq, h⟩)
            · have hdiff_y : y₁ - y₂ = m * (x₁ - x₂) := by
                have hm_val : m = (y₁ - y₂) / (x₁ - x₂) := congCurve_slope_ne (n : ℚ) x₁ x₂ y₁ y₂ hx_eq
                have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx_eq
                exact ((eq_div_iff hne).mp hm_val).symm
              have hmod_y := congrArg modP hdiff_y
              dsimp only [modP] at hmod_y hx_mod ⊢
              rw [ratModP_sub hy₁ hy₂, ratModP_mul hm_nn (padicValRat_nonneg_of_sub hx₁ hx₂),
                ratModP_sub hx₁ hx₂, hx_mod, sub_self, mul_zero] at hmod_y
              exact sub_eq_zero.mp hmod_y
          have hy₁_zero : modP y₁ = 0 := by
            have : (2 : ZMod p) * modP y₁ = 0 := by linear_combination hy_mod + hbar_y_eq
            exact (mul_eq_zero.mp this).resolve_left h2z
          have hy₂_zero : modP y₂ = 0 := by rw [← hbar_y_eq, hy₁_zero]
          have hderiv_zero : 3 * (modP x₁) ^ 2 - (n : ZMod p) ^ 2 = 0 := by
            by_cases hx_eq : x₁ = x₂
            · have hy_eq : y₁ = y₂ := by
                have hy2 : y₁ ^ 2 = y₂ ^ 2 := by rw [heq₁, heq₂, hx_eq]
                rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy2 with h | h
                · exact h
                · exact False.elim (hopp ⟨hx_eq, h⟩)
              have hm_val : m = (3 * x₁ ^ 2 - (n : ℚ) ^ 2) / (2 * y₁) := by
                dsimp only [m]
                rw [hx_eq, hy_eq]
                exact congCurve_slope_self (n : ℚ) x₂ y₂ (by
                  intro h0; exact hopp ⟨hx_eq, by rw [hy_eq]; exact h0⟩)
              have hy₁0 : y₁ ≠ 0 := by
                intro h0; exact hopp ⟨hx_eq, by rw [← hy_eq, h0, neg_zero]⟩
              have hcross : m * (2 * y₁) = 3 * x₁ ^ 2 - (n : ℚ) ^ 2 := by
                rw [hm_val, div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hy₁0)]
              have hmod_c := congrArg modP hcross
              dsimp only [modP] at hmod_c hy₁_zero ⊢
              rw [ratModP_mul hm_nn (padicValRat_nonneg_of_mul h2_nn hy₁),
                ratModP_mul h2_nn hy₁, hy₁_zero, mul_zero, mul_zero,
                ratModP_sub (padicValRat_nonneg_of_mul h3_nn (by rw [padicValRat.pow]; positivity)) hn2_nn,
                ratModP_mul h3_nn (by rw [padicValRat.pow]; positivity),
                ratModP_pow hx₁ 2, ratModP_pow hn_nn 2,
                show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, ratModP_nat, ratModP_nat] at hmod_c
              simpa using hmod_c.symm
            · have hpoly : m * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (n : ℚ) ^ 2 := by
                have hdiff_y : y₁ - y₂ = m * (x₁ - x₂) := by
                  have hm_val : m = (y₁ - y₂) / (x₁ - x₂) := congCurve_slope_ne (n : ℚ) x₁ x₂ y₁ y₂ hx_eq
                  exact ((eq_div_iff (sub_ne_zero.mpr hx_eq)).mp hm_val).symm
                have hfac : (x₁ - x₂) * (m * (y₁ + y₂) - (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (n : ℚ) ^ 2)) = 0 := by
                  linear_combination (y₁ + y₂) * hdiff_y.symm + heq₁ - heq₂
                exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hx_eq))
              have hmod_p := congrArg modP hpoly
              have hsq1_nn : 0 ≤ padicValRat p (x₁ ^ 2) := by rw [padicValRat.pow]; positivity
              have hsq2_nn : 0 ≤ padicValRat p (x₂ ^ 2) := by rw [padicValRat.pow]; positivity
              have h12_nn : 0 ≤ padicValRat p (x₁ * x₂) := padicValRat_nonneg_of_mul hx₁ hx₂
              dsimp only [modP] at hmod_p hx_mod hy₁_zero hy₂_zero ⊢
              rw [ratModP_mul hm_nn (padicValRat_nonneg_of_add hy₁ hy₂),
                ratModP_add hy₁ hy₂, hy₁_zero, hy₂_zero, add_zero, mul_zero,
                ratModP_sub (padicValRat_nonneg_of_add (padicValRat_nonneg_of_add hsq1_nn h12_nn) hsq2_nn) hn2_nn,
                ratModP_add (padicValRat_nonneg_of_add hsq1_nn h12_nn) hsq2_nn,
                ratModP_add hsq1_nn h12_nn,
                ratModP_pow hx₁ 2, ratModP_mul hx₁ hx₂, ratModP_pow hx₂ 2,
                ratModP_pow hn_nn 2, ratModP_nat, ← hx_mod] at hmod_p
              linear_combination -hmod_p
          have hbar_eq : (modP y₁) ^ 2 = (modP x₁) ^ 3 - (n : ZMod p) ^ 2 * modP x₁ := by
            have hmod_e := congrArg modP heq₁
            dsimp only [modP] at hmod_e ⊢
            rw [ratModP_pow hy₁ 2,
              ratModP_sub (by rw [padicValRat.pow]; positivity) (padicValRat_nonneg_of_mul hn2_nn hx₁),
              ratModP_pow hx₁ 3, ratModP_mul hn2_nn hx₁, ratModP_pow hn_nn 2, ratModP_nat] at hmod_e
            exact hmod_e
          rw [hy₁_zero, zero_pow (by norm_num)] at hbar_eq
          have hroots : modP x₁ * (modP x₁ - (n : ZMod p)) * (modP x₁ + (n : ZMod p)) = 0 := by
            linear_combination -hbar_eq
          rcases mul_eq_zero.mp hroots with h1' | h3'
          · rcases mul_eq_zero.mp h1' with hx0 | hxn
            · rw [hx0] at hderiv_zero
              have : (n : ZMod p) ^ 2 = 0 := by linear_combination -hderiv_zero
              exact pow_ne_zero 2 hnz this
            · have hx : modP x₁ = (n : ZMod p) := sub_eq_zero.mp hxn
              rw [hx] at hderiv_zero
              have : (2 : ZMod p) * (n : ZMod p) ^ 2 = 0 := by linear_combination hderiv_zero
              exact mul_ne_zero h2z (pow_ne_zero 2 hnz) this
          · have hx : modP x₁ = -(n : ZMod p) := eq_neg_of_add_eq_zero_left h3'
            rw [hx] at hderiv_zero
            have : (2 : ZMod p) * (n : ZMod p) ^ 2 = 0 := by linear_combination hderiv_zero
            exact mul_ne_zero h2z (pow_ne_zero 2 hnz) this
        have hbar_m : modP m = Wp.toAffine.slope (modP x₁) (modP x₂) (modP y₁) (modP y₂) := by
          by_cases hx_mod : modP x₁ = modP x₂
          · have hy_mod_ne : modP y₁ ≠ -modP y₂ := by
              intro h; exact hnot_opp_mod ⟨hx_mod, by rw [congCurve_negY]; exact h⟩
            have hy_sum_ne : modP y₁ + modP y₂ ≠ 0 := by
              intro h; exact hy_mod_ne (eq_neg_of_add_eq_zero_left h)
            have hbar_y_eq : modP y₁ = modP y₂ := by
              have he1 : (modP y₁) ^ 2 = (modP x₁) ^ 3 - (n : ZMod p) ^ 2 * modP x₁ := by
                have hmod_e := congrArg modP heq₁
                dsimp only [modP] at hmod_e ⊢
                rw [ratModP_pow hy₁ 2,
                  ratModP_sub (by rw [padicValRat.pow]; positivity) (padicValRat_nonneg_of_mul hn2_nn hx₁),
                  ratModP_pow hx₁ 3, ratModP_mul hn2_nn hx₁, ratModP_pow hn_nn 2, ratModP_nat] at hmod_e
                exact hmod_e
              have he2 : (modP y₂) ^ 2 = (modP x₂) ^ 3 - (n : ZMod p) ^ 2 * modP x₂ := by
                have hmod_e := congrArg modP heq₂
                dsimp only [modP] at hmod_e ⊢
                rw [ratModP_pow hy₂ 2,
                  ratModP_sub (by rw [padicValRat.pow]; positivity) (padicValRat_nonneg_of_mul hn2_nn hx₂),
                  ratModP_pow hx₂ 3, ratModP_mul hn2_nn hx₂, ratModP_pow hn_nn 2, ratModP_nat] at hmod_e
                exact hmod_e
              have hsq : (modP y₁) ^ 2 = (modP y₂) ^ 2 := by rw [he1, he2, hx_mod]
              exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_right hy_mod_ne
            rw [hx_mod, hbar_y_eq, congCurve_slope_self (n : ZMod p) (modP x₂) (modP y₂) (by
              intro h; exact hy_mod_ne (by rw [hbar_y_eq]; exact h))]
            have h2y₂_ne : (2 : ZMod p) * modP y₂ ≠ 0 := by
              have : (2 : ZMod p) * modP y₂ = modP y₁ + modP y₂ := by rw [hbar_y_eq]; ring
              rw [this]; exact hy_sum_ne
            rw [eq_div_iff h2y₂_ne]
            by_cases hx_eq : x₁ = x₂
            · have hy_eq : y₁ = y₂ := by
                have hy2 : y₁ ^ 2 = y₂ ^ 2 := by rw [heq₁, heq₂, hx_eq]
                exact (sq_eq_sq_iff_eq_or_eq_neg.mp hy2).resolve_right (fun h => hopp ⟨hx_eq, h⟩)
              have hy₁0 : y₁ ≠ 0 := by
                intro h0; exact h2y₂_ne (by rw [← hbar_y_eq, h0]; simp [modP])
              have hcross : m * (2 * y₁) = 3 * x₁ ^ 2 - (n : ℚ) ^ 2 := by
                have hm_val : m = (3 * x₁ ^ 2 - (n : ℚ) ^ 2) / (2 * y₁) := by
                  dsimp only [m]; rw [hx_eq, hy_eq]
                  exact congCurve_slope_self (n : ℚ) x₂ y₂ (by
                    intro h0; exact hopp ⟨hx_eq, by rw [hy_eq]; exact h0⟩)
                rw [hm_val, div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hy₁0)]
              have hmod_c := congrArg modP hcross
              dsimp only [modP] at hmod_c hx_mod hbar_y_eq ⊢
              rw [ratModP_mul hm_nn (padicValRat_nonneg_of_mul h2_nn hy₁),
                ratModP_mul h2_nn hy₁,
                show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, ratModP_nat,
                ratModP_sub (padicValRat_nonneg_of_mul h3_nn (by rw [padicValRat.pow]; positivity)) hn2_nn,
                ratModP_mul h3_nn (by rw [padicValRat.pow]; positivity),
                ratModP_pow hx₁ 2, ratModP_pow hn_nn 2,
                show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, ratModP_nat, ratModP_nat,
                hx_mod, hbar_y_eq] at hmod_c
              simpa using hmod_c
            · have hpoly : m * (y₁ + y₂) = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (n : ℚ) ^ 2 := by
                have hdiff_y : y₁ - y₂ = m * (x₁ - x₂) := by
                  have hm_val : m = (y₁ - y₂) / (x₁ - x₂) := congCurve_slope_ne (n : ℚ) x₁ x₂ y₁ y₂ hx_eq
                  exact ((eq_div_iff (sub_ne_zero.mpr hx_eq)).mp hm_val).symm
                have hfac : (x₁ - x₂) * (m * (y₁ + y₂) - (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (n : ℚ) ^ 2)) = 0 := by
                  linear_combination (y₁ + y₂) * hdiff_y.symm + heq₁ - heq₂
                exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hx_eq))
              have hmod_p := congrArg modP hpoly
              have hsq1_nn : 0 ≤ padicValRat p (x₁ ^ 2) := by rw [padicValRat.pow]; positivity
              have hsq2_nn : 0 ≤ padicValRat p (x₂ ^ 2) := by rw [padicValRat.pow]; positivity
              have h12_nn : 0 ≤ padicValRat p (x₁ * x₂) := padicValRat_nonneg_of_mul hx₁ hx₂
              dsimp only [modP] at hmod_p hx_mod hbar_y_eq ⊢
              rw [ratModP_mul hm_nn (padicValRat_nonneg_of_add hy₁ hy₂),
                ratModP_add hy₁ hy₂,
                ratModP_sub (padicValRat_nonneg_of_add (padicValRat_nonneg_of_add hsq1_nn h12_nn) hsq2_nn) hn2_nn,
                ratModP_add (padicValRat_nonneg_of_add hsq1_nn h12_nn) hsq2_nn,
                ratModP_add hsq1_nn h12_nn,
                ratModP_pow hx₁ 2, ratModP_mul hx₁ hx₂, ratModP_pow hx₂ 2,
                ratModP_pow hn_nn 2, ratModP_nat, hx_mod, hbar_y_eq] at hmod_p
              linear_combination hmod_p
          · have hx_ne : x₁ ≠ x₂ := fun h => hx_mod (by rw [h])
            rw [congCurve_slope_ne (n : ZMod p) (modP x₁) (modP x₂) (modP y₁) (modP y₂) hx_mod]
            have hm_val : m = (y₁ - y₂) / (x₁ - x₂) := congCurve_slope_ne (n : ℚ) x₁ x₂ y₁ y₂ hx_ne
            have hdx_mod : modP (x₁ - x₂) ≠ 0 := by
              dsimp only [modP]; rw [ratModP_sub hx₁ hx₂]; exact sub_ne_zero.mpr hx_mod
            rw [hm_val]
            have hdiv := (ratModP_div_of_ne_zero (padicValRat_nonneg_of_sub hy₁ hy₂)
              (padicValRat_nonneg_of_sub hx₁ hx₂) hdx_mod).2
            dsimp only [modP] at hdiv ⊢
            rw [hdiv, ratModP_sub hy₁ hy₂, ratModP_sub hx₁ hx₂]
        have hbar_x₃ : modP x₃ = Wp.toAffine.addX (modP x₁) (modP x₂) (modP m) := by
          rw [congCurve_addX]
          have hmod_x := congrArg modP hx₃_def
          dsimp only [modP] at hmod_x ⊢
          rw [ratModP_sub (padicValRat_nonneg_of_sub (by rw [padicValRat.pow]; positivity) hx₁) hx₂,
            ratModP_sub (by rw [padicValRat.pow]; positivity) hx₁, ratModP_pow hm_nn 2] at hmod_x
          exact hmod_x
        have hbar_y₃ : modP y₃ = Wp.toAffine.addY (modP x₁) (modP x₂) (modP y₁) (modP m) := by
          rw [congCurve_addY]
          have hmod_y := congrArg modP hy₃_def
          dsimp only [modP] at hmod_y hbar_x₃ ⊢
          rw [ratModP_neg,
            ratModP_add (padicValRat_nonneg_of_mul hm_nn (padicValRat_nonneg_of_sub h₁₂'.1 hx₁)) hy₁,
            ratModP_mul hm_nn (padicValRat_nonneg_of_sub h₁₂'.1 hx₁),
            ratModP_sub h₁₂'.1 hx₁, hbar_x₃, congCurve_addX] at hmod_y
          exact hmod_y
        rcases h₁₂' with ⟨hx₃_nn, hy₃_nn⟩
        have hlhs : red (WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁ +
            WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂) h₁₂ =
            WeierstrassCurve.Affine.Point.some (modP x₃) (modP y₃) (by
              apply congCurve_ZMod_nonsingular hp2 hpn
              have hns₃ := W.toAffine.nonsingular_add hns₁ hns₂ hnot_opp
              have heq₃ : y₃ ^ 2 = x₃ ^ 3 - (n : ℚ) ^ 2 * x₃ :=
                (congCurve_equation_iff (n : ℚ) x₃ y₃).mp hns₃.1
              have hmod_e := congrArg modP heq₃
              dsimp only [modP] at hmod_e ⊢
              have hx3_pow : 0 ≤ padicValRat p (x₃ ^ 3) := by
                rw [padicValRat.pow]; push_cast; linarith [hx₃_nn]
              rw [ratModP_pow hy₃_nn 2,
                ratModP_sub hx3_pow (padicValRat_nonneg_of_mul hn2_nn hx₃_nn),
                ratModP_pow hx₃_nn 3, ratModP_mul hn2_nn hx₃_nn, ratModP_pow hn_nn 2, ratModP_nat] at hmod_e
              exact hmod_e) := by
          exact hred_eq
            (B := WeierstrassCurve.Affine.Point.some x₃ y₃ (W.toAffine.nonsingular_add hns₁ hns₂ hnot_opp))
            h₁₂ ⟨hx₃_nn, hy₃_nn⟩ hadd_some
        rw [hlhs]
        symm
        dsimp only [red]
        rw [WeierstrassCurve.Affine.Point.add_some hnot_opp_mod]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨by rw [← hbar_m, ← hbar_x₃], by rw [← hbar_m, ← hbar_y₃]⟩

/- No point of odd prime order `q` exists on `E_n(Q)` (`n ≠ 0`): pick a prime `p > max (2*n) q`
with `p ≡ 2*q + 1 (mod 4*q)` by Dirichlet's theorem, reduce `<Q>` injectively into `E_n(ZMod p)`,
and derive `q ∣ p + 1`, contradicting `p + 1 ≡ 2 (mod q)`. -/
lemma congCurve_no_odd_prime_torsion {n q : ℕ} (hn : n ≠ 0) (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
    ∀ Q : W.toAffine.Point, Q ≠ 0 → q • Q ≠ 0 := by
  intro W Q hQ0 hqQ
  have hcop : Nat.Coprime (2 * q + 1) (4 * q) := by
    have hq_odd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with rfl | hodd
      · exact False.elim (hq2 rfl)
      · exact hodd
    have hc4 : Nat.Coprime (2 * q + 1) 4 := by
      have : Nat.Coprime (2 * q + 1) 2 := by
        rw [Nat.coprime_two_right]; exact ⟨q, by ring⟩
      simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using this.pow_right 2
    have hcq : Nat.Coprime (2 * q + 1) q := by
      rw [Nat.coprime_iff_gcd_eq_one]
      refine Nat.dvd_one.mp ?_
      have h1 : Nat.gcd (2 * q + 1) q ∣ 2 * q + 1 := Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd (2 * q + 1) q ∣ 2 * q := dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 2
      exact (Nat.dvd_add_right h2).mp h1
    exact hc4.mul_right hcq
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (2 * n) q)
      (by have := hq.pos; positivity : 4 * q ≠ 0) hcop
  have : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hp_gt_2n : 2 * n < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_gt_q : q < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hpn : ¬ (p ∣ n) := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) (by omega)
  have hp2 : p ≠ 2 := by omega
  have hp4 : p % 4 = 3 := by
    have hmod4 : p ≡ 2 * q + 1 [MOD 4] :=
      Nat.ModEq.of_dvd (dvd_mul_right 4 q) hp_mod
    have hq_odd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with rfl | hodd
      · exact False.elim (hq2 rfl)
      · exact hodd
    change p % 4 = (2 * q + 1) % 4 at hmod4
    omega
  have hndvd_p1 : ¬ (q ∣ p + 1) := by
    have hmodq : p ≡ 2 * q + 1 [MOD q] :=
      Nat.ModEq.of_dvd (dvd_mul_left q 4) hp_mod
    change p % q = (2 * q + 1) % q at hmodq
    have h2q1 : (2 * q + 1) % q = 1 := by
      rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hq.one_lt]
    rw [h2q1] at hmodq
    intro hd
    have h0 : (p + 1) % q = 0 := Nat.mod_eq_zero_of_dvd hd
    have hq3 : 2 < q := by
      have := hq.two_le; omega
    have h2 : (p + 1) % q = 2 := by
      rw [Nat.add_mod, hmodq, Nat.mod_eq_of_lt hq.one_lt, Nat.mod_eq_of_lt hq3]
    omega
  let Wp : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, -(n : ZMod p) ^ 2, 0⟩
  let isInt : W.toAffine.Point → Prop := fun P =>
    match P with
    | .zero => True
    | .some x y _ => 0 ≤ padicValRat p x ∧ 0 ≤ padicValRat p y
  obtain ⟨red, hred0, hred_some, hred_add⟩ := congCurve_red_add (p := p) (n := n) hp2 hpn
  have hred_eq : ∀ {A B : W.toAffine.Point} (hA : isInt A) (hB : isInt B),
      A = B → red A hA = red B hB := by
    rintro _ _ _ _ rfl
    rfl
  have hall_int : ∀ k : ℕ, isInt (k • Q) := by
    intro k
    have hqk : q • (k • Q) = 0 := by
      rw [← mul_nsmul, mul_comm, mul_nsmul, hqQ, nsmul_zero]
    exact torsion_p_integral hp_gt_q hpn hq.pos (k • Q) hqk
  have hQ_int : isInt Q := by simpa using hall_int 1
  have hred_nsmul : ∀ k : ℕ, red (k • Q) (hall_int k) = k • red Q hQ_int := by
    intro k
    induction k with
    | zero =>
      exact (hred_eq (hall_int 0) (by trivial : isInt 0) (zero_nsmul Q)).trans (hred0 _)
    | succ k ih =>
      have hk1 : isInt (k • Q + Q) := by simpa [succ_nsmul] using hall_int (k + 1)
      have hstep := hred_add (k • Q) Q (hall_int k) hQ_int hk1
      calc
        red ((k + 1) • Q) (hall_int (k + 1))
            = red (k • Q + Q) hk1 := hred_eq _ _ (succ_nsmul Q k)
        _ = red (k • Q) (hall_int k) + red Q hQ_int := hstep
        _ = k • red Q hQ_int + red Q hQ_int := by rw [ih]
        _ = (k + 1) • red Q hQ_int := (succ_nsmul _ k).symm
  have hred_ne_of_ne : ∀ (P : W.toAffine.Point) (hP : isInt P), P ≠ 0 → red P hP ≠ 0 := by
    intro P hP hP0
    cases P with
    | zero => exact False.elim (hP0 rfl)
    | some x y h => exact hred_some x y h hP
  have hred_ne : red Q hQ_int ≠ 0 := hred_ne_of_ne Q hQ_int hQ0
  have hq_red : q • red Q hQ_int = 0 := by
    rw [← hred_nsmul q]
    exact (hred_eq (hall_int q) (by trivial : isInt 0) hqQ).trans (hred0 _)
  have hord_dvd : addOrderOf (red Q hQ_int) ∣ q := addOrderOf_dvd_of_nsmul_eq_zero hq_red
  have hord_ne1 : addOrderOf (red Q hQ_int) ≠ 1 := by
    intro h1
    have h0 := addOrderOf_nsmul_eq_zero (red Q hQ_int)
    rw [h1, one_nsmul] at h0
    exact hred_ne h0
  have hord_eq : addOrderOf (red Q hQ_int) = q :=
    (hq.eq_one_or_self_of_dvd _ hord_dvd).resolve_left hord_ne1
  classical
  let _inst : Fintype Wp.toAffine.Point :=
    Fintype.ofEquiv (Option { xy : ZMod p × ZMod p // Wp.toAffine.Nonsingular xy.1 xy.2 })
      Wp.toAffine.nonsingularPointEquiv.symm
  have hcard_dvd : q ∣ Nat.card Wp.toAffine.Point := by
    rw [Nat.card_eq_fintype_card, ← hord_eq]
    exact addOrderOf_dvd_card
  rw [congCurve_ZMod_card hp4 hpn] at hcard_dvd
  exact hndvd_p1 hcard_dvd

/- Complete Torsion Theorem for `E_n(Q)`: for every `n ≠ 0` and every affine rational point
`P = (x, y)` on `E_n(Q)` with `y ≠ 0`, `P` has infinite order (`∀ m > 0, m • P ≠ 0`). -/
lemma congCurve_point_infinite_order {n : ℕ} (hn : n ≠ 0) (x y : ℚ)
    (h : (WeierstrassCurve.mk (0 : ℚ) 0 0 (-(n : ℚ) ^ 2) 0).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    ∀ m : ℕ, 0 < m → m • (WeierstrassCurve.Affine.Point.some x y h) ≠ 0 := by
  let W : WeierstrassCurve ℚ := ⟨0, 0, 0, -(n : ℚ) ^ 2, 0⟩
  let P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h
  intro m hm hmP
  have h2P_ne : (2 : ℕ) • P ≠ 0 := by
    intro h2
    exact hy ((congCurve_two_nsmul_eq_zero_iff (by norm_num) (n : ℚ) x y h).mp h2)
  let d : ℕ := addOrderOf P
  have hd_dvd : d ∣ m := addOrderOf_dvd_of_nsmul_eq_zero hmP
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hm
  have hd_ne1 : d ≠ 1 := by
    intro h1
    have h0 : d • P = 0 := addOrderOf_nsmul_eq_zero P
    rw [h1, one_nsmul] at h0
    exact WeierstrassCurve.Affine.Point.some_ne_zero h h0
  have hd_ne2 : d ≠ 2 := by
    intro h2
    have hdP : d • P = 0 := addOrderOf_nsmul_eq_zero P
    rw [h2] at hdP
    exact h2P_ne hdP
  have hd_ge3 : 3 ≤ d := by omega
  by_cases hodd_fac : ∃ q : ℕ, Nat.Prime q ∧ q ≠ 2 ∧ q ∣ d
  · obtain ⟨q, hq_prime, hq2, hqd⟩ := hodd_fac
    obtain ⟨k, hk⟩ := hqd
    let Q : W.toAffine.Point := k • P
    have hk_lt : k < d := by
      have hq2' : 2 ≤ q := hq_prime.two_le
      nlinarith
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      omega
    have hQ_ne : Q ≠ 0 := by
      intro hQ0
      have hd_dvd_k : d ∣ k := addOrderOf_dvd_of_nsmul_eq_zero hQ0
      exact absurd (Nat.le_of_dvd hk_pos hd_dvd_k) (not_le_of_gt hk_lt)
    have hqQ : q • Q = 0 := by
      dsimp only [Q]
      rw [← mul_nsmul, mul_comm, ← hk]
      exact addOrderOf_nsmul_eq_zero P
    exact congCurve_no_odd_prime_torsion hn hq_prime hq2 Q hQ_ne hqQ
  · have h4_dvd : 4 ∣ d := by
      have h2_dvd : 2 ∣ d := by
        obtain ⟨q, hq_prime, hqd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        by_cases hq2 : q = 2
        · rwa [hq2] at hqd
        · exact False.elim (hodd_fac ⟨q, hq_prime, hq2, hqd⟩)
      obtain ⟨r, hr⟩ := h2_dvd
      have hr_ne1 : r ≠ 1 := by omega
      obtain ⟨q, hq_prime, hqr⟩ := Nat.exists_prime_and_dvd hr_ne1
      have hqd : q ∣ d := dvd_trans hqr (by rw [hr]; exact dvd_mul_left r 2)
      have hq2 : q = 2 := by
        by_contra hne
        exact hodd_fac ⟨q, hq_prime, hne, hqd⟩
      rw [hq2] at hqr
      obtain ⟨s, hs⟩ := hqr
      exact ⟨s, by omega⟩
    obtain ⟨k, hk⟩ := h4_dvd
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      omega
    let Q : W.toAffine.Point := k • P
    have h2Q_ne : (2 : ℕ) • Q ≠ 0 := by
      intro h2Q
      dsimp only [Q] at h2Q
      rw [← mul_nsmul, mul_comm] at h2Q
      have hd_dvd_2k : d ∣ 2 * k := addOrderOf_dvd_of_nsmul_eq_zero h2Q
      have hle : d ≤ 2 * k := Nat.le_of_dvd (by omega) hd_dvd_2k
      omega
    have h4Q : (4 : ℕ) • Q = 0 := by
      dsimp only [Q]
      rw [← mul_nsmul, mul_comm, ← hk]
      exact addOrderOf_nsmul_eq_zero P
    cases hQ_cases : Q with
    | zero =>
      rw [hQ_cases, ← WeierstrassCurve.Affine.Point.zero_def, nsmul_zero] at h2Q_ne
      exact h2Q_ne rfl
    | some x' y' h' =>
      have hy' : y' ≠ 0 := by
        intro hy'0
        apply h2Q_ne
        rw [hQ_cases]
        exact (congCurve_two_nsmul_eq_zero_iff (by norm_num) (n : ℚ) x' y' h').mpr hy'0
      rw [hQ_cases] at h4Q
      exact congCurve_four_nsmul_ne_zero hn x' y' h' hy' h4Q

/- === Section 7: Identity Theorem on the Half-Plane and Main Reduction === -/

/- Uniqueness of analytic continuation at `s = 1`: any two functions analytic on the convex
open half-plane `{s : ℂ | 1/2 < s.re}` that agree on `{s : ℂ | 2 < s.re}` take the same value
at `s = 1`. -/
lemma analytic_continuation_eq_at_one {L₁ L₂ : ℂ → ℂ}
    (hL₁ : AnalyticOnNhd ℂ L₁ {s : ℂ | (1 / 2 : ℝ) < s.re})
    (hL₂ : AnalyticOnNhd ℂ L₂ {s : ℂ | (1 / 2 : ℝ) < s.re})
    (heq : ∀ s : ℂ, 2 < s.re → L₁ s = L₂ s) :
    L₁ 1 = L₂ 1 := by
  let U : Set ℂ := {s : ℂ | (1 / 2 : ℝ) < s.re}
  have hU_convex : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change (1 / 2 : ℝ) < (a • x + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have hx' : (1 / 2 : ℝ) < x.re := hx
    have hy' : (1 / 2 : ℝ) < y.re := hy
    by_cases ha0 : a = 0
    · subst ha0; nlinarith
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith
  have hU_conn : IsPreconnected U := hU_convex.isPreconnected
  have h3_mem : (3 : ℂ) ∈ U := by
    change (1 / 2 : ℝ) < (3 : ℂ).re
    norm_num
  have h1_mem : (1 : ℂ) ∈ U := by
    change (1 / 2 : ℝ) < (1 : ℂ).re
    norm_num
  have hev : L₁ =ᶠ[nhds (3 : ℂ)] L₂ := by
    have hopen : IsOpen {s : ℂ | (2 : ℝ) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h3_in : (3 : ℂ) ∈ {s : ℂ | (2 : ℝ) < s.re} := by
      change (2 : ℝ) < (3 : ℂ).re
      norm_num
    exact Filter.eventuallyEq_of_mem (hopen.mem_nhds h3_in) heq
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hL₁ hL₂ hU_conn h3_mem hev h1_mem

/- Main reduction: Coates-Wiles (`H1`) and Tunnell-Waldspurger (`H2`) imply Tunnell's necessary
condition `CongruentNumber.Tunnell_odd` for all odd squarefree congruent numbers. -/
theorem main : H1 → H2 → type_of% @CongruentNumber.Tunnell_odd := by
  intro hH1 hH2 n hsqf hodd hcong
  have hmod8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    rcases hodd with ⟨k, rfl⟩
    omega
  rcases hmod8 with h1 | h3 | h5 | h7
  · have h13 : n % 8 = 1 ∨ n % 8 = 3 := Or.inl h1
    have hn0 : n ≠ 0 := by omega
    obtain ⟨x, y, hy, hns, _⟩ := curve_point_of_congruentNumber hn0 hcong
    have hinf : ∃ P : (WeierstrassCurve.mk (0 : ℚ) 0 0 (-(n : ℚ) ^ 2) 0).toAffine.Point,
        ∀ m : ℕ, 0 < m → m • P ≠ 0 :=
      ⟨WeierstrassCurve.Affine.Point.some x y hns, congCurve_point_infinite_order hn0 x y hns hy⟩
    obtain ⟨L₁, hL₁_an, hL₁_eq, hL₁_zero⟩ := hH1 n hsqf hodd h13 hinf
    obtain ⟨L₂, hL₂_an, hL₂_eq, Ω, hΩ_ne, hL₂_val⟩ := hH2 n hsqf hodd h13
    have hL_eq : L₁ 1 = L₂ 1 := analytic_continuation_eq_at_one hL₁_an hL₂_an fun s hs => by
      rw [hL₁_eq s hs, hL₂_eq s hs]
    have hprod_zero :
        Ω * ((2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard) ^ 2 = 0 := by
      rw [← hL₂_val, ← hL_eq, hL₁_zero]
    have hsq_zero :
        ((2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard) ^ 2 = 0 :=
      (mul_eq_zero.mp hprod_zero).resolve_left hΩ_ne
    have hdiff_zero :
        (2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard = 0 :=
      sq_eq_zero_iff.mp hsq_zero
    have heq_complex :
        ((2 * (CongruentNumber.A n).ncard : ℕ) : ℂ) = ((CongruentNumber.B n).ncard : ℂ) := by
      push_cast
      exact sub_eq_zero.mp hdiff_zero
    exact_mod_cast heq_complex
  · have h13 : n % 8 = 1 ∨ n % 8 = 3 := Or.inr h3
    have hn0 : n ≠ 0 := by omega
    obtain ⟨x, y, hy, hns, _⟩ := curve_point_of_congruentNumber hn0 hcong
    have hinf : ∃ P : (WeierstrassCurve.mk (0 : ℚ) 0 0 (-(n : ℚ) ^ 2) 0).toAffine.Point,
        ∀ m : ℕ, 0 < m → m • P ≠ 0 :=
      ⟨WeierstrassCurve.Affine.Point.some x y hns, congCurve_point_infinite_order hn0 x y hns hy⟩
    obtain ⟨L₁, hL₁_an, hL₁_eq, hL₁_zero⟩ := hH1 n hsqf hodd h13 hinf
    obtain ⟨L₂, hL₂_an, hL₂_eq, Ω, hΩ_ne, hL₂_val⟩ := hH2 n hsqf hodd h13
    have hL_eq : L₁ 1 = L₂ 1 := analytic_continuation_eq_at_one hL₁_an hL₂_an fun s hs => by
      rw [hL₁_eq s hs, hL₂_eq s hs]
    have hprod_zero :
        Ω * ((2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard) ^ 2 = 0 := by
      rw [← hL₂_val, ← hL_eq, hL₁_zero]
    have hsq_zero :
        ((2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard) ^ 2 = 0 :=
      (mul_eq_zero.mp hprod_zero).resolve_left hΩ_ne
    have hdiff_zero :
        (2 * (CongruentNumber.A n).ncard : ℂ) - (CongruentNumber.B n).ncard = 0 :=
      sq_eq_zero_iff.mp hsq_zero
    have heq_complex :
        ((2 * (CongruentNumber.A n).ncard : ℕ) : ℂ) = ((CongruentNumber.B n).ncard : ℂ) := by
      push_cast
      exact sub_eq_zero.mp hdiff_zero
    exact_mod_cast heq_complex
  · exact Tunnell_odd_of_mod_eight_five_or_seven (Or.inl h5)
  · exact Tunnell_odd_of_mod_eight_five_or_seven (Or.inr h7)

end OMA.R_CongruentNumber_Tunnell_odd_R2
