import OMAStatements.S_opg_something_like_picard_for_1_forms

-- Problem: Something like Picard for 1-forms (Open Problem Garden, B. Elsner).
-- Target: OMA.S_opg_something_like_picard_for_1_forms.main. This file REFUTES the formal statement.
-- Why it is false as stated: the open sets U_j are not required to be connected. Take
-- F(z) = exp(1/z). In the w = 1/z plane, cover everything by four families of pairwise disjoint
-- open squares of side 3/2 centred at the lattice points (2k + a) + (2l + b) i, a, b in {0, 1}.
-- U_j is the set of z in the punctured unit disk with 1/z in a square of family j, and
-- f_j = exp(1/z) + c, where the constant c depends on the square. exp is injective on each square
-- (height 3/2 < 2 pi) and bounded there by exp(x + 1), so the constants
-- c = 4 exp(x + 1) + 3 y exp(x + 1) i (x + y i the centre) make the images of different squares
-- disjoint: f_j is injective and holomorphic on U_j. All f_j have derivative -exp(1/z)/z^2, which
-- has an essential singularity at 0, hence is not meromorphic there.
-- With connected U_j (the reading the source intends) the question stays open; this file says
-- nothing about it.

open Filter Topology

namespace OMA.P30

/-- Offsets of the four families of squares: `(a, b)` with `a, b` in `{0, 1}`. -/
def off (j : Fin 4) : ℤ × ℤ := (((j.val % 2 : ℕ) : ℤ), ((j.val / 2 : ℕ) : ℤ))

/-- An open square of side `3/2` centred at the lattice point `x + y i` (in the `1/z` plane). -/
def Q (x y : ℤ) : Set ℂ := {w | |w.re - x| < 3 / 4 ∧ |w.im - y| < 3 / 4}

/-- A piece: the points `z` of the punctured unit disk with `1/z` in the square around
`(2k + a) + (2l + b) i`. -/
def piece (j : Fin 4) (k l : ℤ) : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ ({0}ᶜ ∩ (fun z : ℂ => z⁻¹) ⁻¹' Q (2 * k + (off j).1) (2 * l + (off j).2))

/-- The `j`-th open set: a disjoint union of pieces. -/
def U (j : Fin 4) : Set ℂ := ⋃ k : ℤ, ⋃ l : ℤ, piece j k l

/-- A bound for `exp` on the squares with real centre `x`. -/
noncomputable def D (x : ℤ) : ℝ := Real.exp (x + 1)

/-- The additive constant used on the piece with centre `x + y i`. -/
noncomputable def Cst (x y : ℤ) : ℂ := ⟨4 * D x, 3 * y * D x⟩

noncomputable def kk (j : Fin 4) (z : ℂ) : ℤ := ⌊((z⁻¹).re - (off j).1) / 2 + 1 / 2⌋

noncomputable def ll (j : Fin 4) (z : ℂ) : ℤ := ⌊((z⁻¹).im - (off j).2) / 2 + 1 / 2⌋

/-- `exp (1/z)` plus a constant that depends only on the piece containing `z`. -/
noncomputable def F (j : Fin 4) (z : ℂ) : ℂ :=
  Complex.exp z⁻¹ + Cst (2 * kk j z + (off j).1) (2 * ll j z + (off j).2)

lemma isOpen_Q (x y : ℤ) : IsOpen (Q x y) := by
  have h1 : IsOpen {w : ℂ | |w.re - x| < 3 / 4} :=
    isOpen_lt ((Complex.continuous_re.sub continuous_const).abs) continuous_const
  have h2 : IsOpen {w : ℂ | |w.im - y| < 3 / 4} :=
    isOpen_lt ((Complex.continuous_im.sub continuous_const).abs) continuous_const
  exact h1.inter h2

lemma isOpen_piece (j : Fin 4) (k l : ℤ) : IsOpen (piece j k l) :=
  Metric.isOpen_ball.inter
    (continuousOn_inv₀.isOpen_inter_preimage isOpen_compl_singleton (isOpen_Q _ _))

lemma isOpen_U (j : Fin 4) : IsOpen (U j) :=
  isOpen_iUnion fun k => isOpen_iUnion fun l => isOpen_piece j k l

lemma mem_piece {j : Fin 4} {k l : ℤ} {z : ℂ} :
    z ∈ piece j k l ↔ ‖z‖ < 1 ∧ z ≠ 0 ∧
      |(z⁻¹).re - (2 * (k : ℝ) + ((off j).1 : ℝ))| < 3 / 4 ∧
      |(z⁻¹).im - (2 * (l : ℝ) + ((off j).2 : ℝ))| < 3 / 4 := by
  simp [piece, Q]

lemma kk_eq {j : Fin 4} {k l : ℤ} {z : ℂ} (h : z ∈ piece j k l) : kk j z = k ∧ ll j z = l := by
  obtain ⟨-, -, h1, h2⟩ := mem_piece.1 h
  rw [abs_lt] at h1 h2
  constructor
  · unfold kk
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  · unfold ll
    rw [Int.floor_eq_iff]
    constructor <;> linarith

lemma F_eq {j : Fin 4} {k l : ℤ} {z : ℂ} (h : z ∈ piece j k l) :
    F j z = Complex.exp z⁻¹ + Cst (2 * k + (off j).1) (2 * l + (off j).2) := by
  unfold F
  rw [(kk_eq h).1, (kk_eq h).2]

lemma hasDerivAt_F {j : Fin 4} {z : ℂ} (h : z ∈ U j) :
    HasDerivAt (F j) (Complex.exp z⁻¹ * (-(z ^ 2)⁻¹)) z := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
  obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hk
  have hz : z ≠ 0 := (mem_piece.1 hl).2.1
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp z⁻¹ + Cst (2 * k + (off j).1) (2 * l + (off j).2))
      (Complex.exp z⁻¹ * (-(z ^ 2)⁻¹)) z := ((hasDerivAt_inv hz).cexp).add_const _
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_piece j k l).mem_nhds hl] with w hw
  exact F_eq hw

lemma D_pos (x : ℤ) : 0 < D x := Real.exp_pos _

lemma D_two {x x' : ℤ} (h : x < x') : 2 * D x ≤ D x' := by
  have h1 : (x : ℝ) + 1 ≤ x' := by exact_mod_cast h
  have h2 : Real.exp ((x : ℝ) + 1 + 1) ≤ Real.exp ((x' : ℝ) + 1) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [Real.exp_add] at h2
  unfold D
  nlinarith [Real.exp_pos ((x : ℝ) + 1)]

lemma norm_exp_lt {j : Fin 4} {k l : ℤ} {z : ℂ} (h : z ∈ piece j k l) :
    ‖Complex.exp z⁻¹‖ < D (2 * k + (off j).1) := by
  obtain ⟨-, -, h1, -⟩ := mem_piece.1 h
  rw [abs_lt] at h1
  rw [Complex.norm_exp]
  unfold D
  apply Real.exp_lt_exp.mpr
  push_cast
  linarith

lemma injOn_F (j : Fin 4) : Set.InjOn (F j) (U j) := by
  intro z₁ h₁ z₂ h₂ heq
  obtain ⟨k₁, hk₁⟩ := Set.mem_iUnion.1 h₁
  obtain ⟨l₁, hl₁⟩ := Set.mem_iUnion.1 hk₁
  obtain ⟨k₂, hk₂⟩ := Set.mem_iUnion.1 h₂
  obtain ⟨l₂, hl₂⟩ := Set.mem_iUnion.1 hk₂
  rw [F_eq hl₁, F_eq hl₂] at heq
  have hn₁ := norm_exp_lt hl₁
  have hn₂ := norm_exp_lt hl₂
  have hre₁ := Complex.abs_re_le_norm (Complex.exp z₁⁻¹)
  have hre₂ := Complex.abs_re_le_norm (Complex.exp z₂⁻¹)
  have him₁ := Complex.abs_im_le_norm (Complex.exp z₁⁻¹)
  have him₂ := Complex.abs_im_le_norm (Complex.exp z₂⁻¹)
  rw [abs_le] at hre₁ hre₂ him₁ him₂
  have hRe := congrArg Complex.re heq
  have hIm := congrArg Complex.im heq
  simp only [Complex.add_re, Complex.add_im, Cst] at hRe hIm
  have hp₁ := D_pos (2 * k₁ + (off j).1)
  have hp₂ := D_pos (2 * k₂ + (off j).1)
  -- the real centres agree
  have hk : k₁ = k₂ := by
    rcases lt_trichotomy k₁ k₂ with hlt | heq' | hgt
    · exfalso
      have := D_two (show 2 * k₁ + (off j).1 < 2 * k₂ + (off j).1 by omega)
      linarith
    · exact heq'
    · exfalso
      have := D_two (show 2 * k₂ + (off j).1 < 2 * k₁ + (off j).1 by omega)
      linarith
  subst hk
  -- the imaginary centres agree
  have hl : l₁ = l₂ := by
    rcases lt_trichotomy l₁ l₂ with hlt | heq' | hgt
    · exfalso
      have h1 : (l₁ : ℝ) + 1 ≤ l₂ := by exact_mod_cast hlt
      push_cast at hIm
      nlinarith
    · exact heq'
    · exfalso
      have h1 : (l₂ : ℝ) + 1 ≤ l₁ := by exact_mod_cast hgt
      push_cast at hIm
      nlinarith
  subst hl
  have hexp : Complex.exp z₁⁻¹ = Complex.exp z₂⁻¹ := add_right_cancel heq
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  obtain ⟨-, -, -, hi₁⟩ := mem_piece.1 hl₁
  obtain ⟨-, -, -, hi₂⟩ := mem_piece.1 hl₂
  rw [abs_lt] at hi₁ hi₂
  obtain ⟨hi₁a, hi₁b⟩ := hi₁
  obtain ⟨hi₂a, hi₂b⟩ := hi₂
  have hIm' : (z₁⁻¹).im = (z₂⁻¹).im + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa [-Complex.inv_im] using this
  have hpi := Real.pi_gt_three
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hlt | heq' | hgt
    · exfalso
      have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith
    · exact heq'
    · exfalso
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hgt
      nlinarith
  subst hn0
  simp at hn
  exact hn

lemma parity (X : ℤ) : ∃ a : ℕ, a < 2 ∧ ∃ k : ℤ, X = 2 * k + a := by
  rcases Int.emod_two_eq_zero_or_one X with h | h
  · exact ⟨0, by norm_num, X / 2, by push_cast; omega⟩
  · exact ⟨1, by norm_num, X / 2, by push_cast; omega⟩

lemma cover {z : ℂ} (hz1 : ‖z‖ < 1) (hz0 : z ≠ 0) : ∃ j, z ∈ U j := by
  obtain ⟨a, ha, k, hk⟩ := parity ⌊(z⁻¹).re + 1 / 2⌋
  obtain ⟨b, hb, l, hl⟩ := parity ⌊(z⁻¹).im + 1 / 2⌋
  have hx1 := Int.floor_le ((z⁻¹).re + 1 / 2)
  have hx2 := Int.lt_floor_add_one ((z⁻¹).re + 1 / 2)
  have hy1 := Int.floor_le ((z⁻¹).im + 1 / 2)
  have hy2 := Int.lt_floor_add_one ((z⁻¹).im + 1 / 2)
  rw [hk] at hx1 hx2
  rw [hl] at hy1 hy2
  push_cast at hx1 hx2 hy1 hy2
  refine ⟨⟨a + 2 * b, by omega⟩, Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨l, ?_⟩⟩⟩
  have ha' : (a + 2 * b) % 2 = a := by omega
  have hb' : (a + 2 * b) / 2 = b := by omega
  rw [mem_piece]
  refine ⟨hz1, hz0, ?_, ?_⟩
  · simp only [off, ha']
    rw [abs_lt]
    constructor <;> push_cast <;> linarith
  · simp only [off, hb']
    rw [abs_lt]
    constructor <;> push_cast <;> linarith

lemma union_eq : (⋃ j, U j) = Metric.ball (0 : ℂ) 1 \ {0} := by
  ext z
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hj
    obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hk
    obtain ⟨h1, h0, -, -⟩ := mem_piece.1 hl
    exact ⟨by simpa using h1, by simpa using h0⟩
  · rintro ⟨h1, h0⟩
    obtain ⟨j, hj⟩ := cover (by simpa using h1) (by simpa using h0)
    exact Set.mem_iUnion.2 ⟨j, hj⟩

/-- The glued derivative `-exp (1/z) / z^2` has an essential singularity at `0`. -/
lemma not_meromorphic (g : ℂ → ℂ)
    (hg : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → g z = Complex.exp z⁻¹ * (-(z ^ 2)⁻¹)) :
    ¬ MeromorphicAt g 0 := by
  rintro ⟨n, hn⟩
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 hn.continuousAt 1 one_pos
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    (((Real.tendsto_exp_div_pow_atTop n).eventually_gt_atTop
      (‖(fun z : ℂ => (z - 0) ^ n • g z) 0‖ + 1)).and
      ((eventually_gt_atTop (1 : ℝ)).and (eventually_gt_atTop δ⁻¹))).exists
  have hs0 : 0 < s := by linarith
  have hsinv : s⁻¹ < δ := (inv_lt_comm₀ hδ hs0).1 hs3
  have hsinv1 : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs2
  have hnorm : ‖((s⁻¹ : ℝ) : ℂ)‖ = s⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs0.le)]
  have hz0 : ((s⁻¹ : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (inv_pos.2 hs0).ne hnorm
  have hval : (((s⁻¹ : ℝ) : ℂ) - 0) ^ n • g ((s⁻¹ : ℝ) : ℂ) =
      (((s⁻¹) ^ n * (Real.exp s * (-((s⁻¹) ^ 2)⁻¹)) : ℝ) : ℂ) := by
    rw [hg _ (by rw [hnorm]; exact hsinv1) hz0]
    push_cast
    simp
  have hd := hb (show dist ((s⁻¹ : ℝ) : ℂ) 0 < δ by rw [dist_zero_right, hnorm]; exact hsinv)
  rw [dist_eq_norm] at hd
  have hd' := norm_sub_norm_le ((fun z : ℂ => (z - 0) ^ n • g z) ((s⁻¹ : ℝ) : ℂ))
    ((fun z : ℂ => (z - 0) ^ n • g z) 0)
  have hlt : ‖(((s⁻¹ : ℝ) : ℂ) - 0) ^ n • g ((s⁻¹ : ℝ) : ℂ)‖ <
      ‖(fun z : ℂ => (z - 0) ^ n • g z) 0‖ + 1 := by
    have : ‖(fun z : ℂ => (z - 0) ^ n • g z) ((s⁻¹ : ℝ) : ℂ)‖ <
        ‖(fun z : ℂ => (z - 0) ^ n • g z) 0‖ + 1 := by linarith
    exact this
  rw [hval, Complex.norm_real, Real.norm_eq_abs] at hlt
  have he : Real.exp s / s ^ n ≤ |(s⁻¹) ^ n * (Real.exp s * (-((s⁻¹) ^ 2)⁻¹))| := by
    have h2 : ((s⁻¹) ^ 2)⁻¹ = s ^ 2 := by rw [inv_pow, inv_inv]
    have h3 : (s⁻¹) ^ n * (Real.exp s * (-((s⁻¹) ^ 2)⁻¹)) = -((s⁻¹) ^ n * Real.exp s * s ^ 2) := by
      rw [h2]; ring
    rw [h3, abs_neg, abs_of_pos (by positivity), div_eq_mul_inv, ← inv_pow]
    have h4 : (1 : ℝ) ≤ s ^ 2 := by nlinarith
    have h5 : 0 < (s⁻¹) ^ n * Real.exp s := by positivity
    nlinarith
  linarith

end OMA.P30

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_something_like_picard_for_1_forms.main) := by
  intro H
  obtain ⟨g, hg, hmer⟩ := H 4 OMA.P30.U OMA.P30.F OMA.P30.isOpen_U OMA.P30.union_eq
    (fun j z hz => (OMA.P30.hasDerivAt_F hz).differentiableAt.differentiableWithinAt)
    OMA.P30.injOn_F
    (fun j k z hz => by
      rw [(OMA.P30.hasDerivAt_F hz.1).deriv, (OMA.P30.hasDerivAt_F hz.2).deriv])
  refine OMA.P30.not_meromorphic g ?_ hmer
  intro z hz1 hz0
  obtain ⟨j, hj⟩ := OMA.P30.cover hz1 hz0
  rw [hg j z hj, (OMA.P30.hasDerivAt_F hj).deriv]
