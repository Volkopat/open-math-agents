import OMAReductions.R_Green28_green_28_R1
import Mathlib

/-! Reduction Green28.green_28.R1.H1.R1 of step Green28.green_28.R1.H1: the case where one of
the two factors has support of size at most two is proved here. If `X + Y` is uniform on its
support and `Y` is supported on two points `t < u`, comparing the sum at the two ends of the
support of `X` forces equal weights on `Y`, and then `X n + X (n - (u - t))` takes only the values
`0` and one fixed `K`, which by induction from the bottom of the support forces `X` to take only
the values `0` and `K`. If `X` has two support points the same end-point comparison with the
roles swapped gives equal weights, and one-point supports are translates. The step reduces to
the case where both supports have at least three points, split by which factor is larger. -/

namespace OMA.G28Lib

open Green28

/-- Convolution formula for `indepSum`. -/
theorem indepSum_apply (X Y : PMF ℤ) (n : ℤ) :
    indepSum X Y n = ∑' x, X x * Y (n - x) := by
  change (X.bind fun x => Y.bind fun y => PMF.pure (x + y)) n = _
  rw [PMF.bind_apply]
  refine tsum_congr fun x => ?_
  congr 1
  rw [PMF.bind_apply, tsum_eq_single (n - x)]
  · simp [PMF.pure_apply]
  · intro y hy
    have : n ≠ x + y := by omega
    simp [PMF.pure_apply, this]

theorem indepSum_comm (X Y : PMF ℤ) : indepSum X Y = indepSum Y X := by
  change (X.bind fun x => Y.bind fun y => PMF.pure (x + y)) =
    (Y.bind fun y => X.bind fun x => PMF.pure (y + x))
  rw [PMF.bind_comm]
  simp_rw [add_comm]

theorem indepSum_apply' (X Y : PMF ℤ) (n : ℤ) :
    indepSum X Y n = ∑' y, Y y * X (n - y) := by
  rw [indepSum_comm, indepSum_apply]

theorem toReal_eq_zero_iff (X : PMF ℤ) (n : ℤ) : (X n).toReal = 0 ↔ X n = 0 := by
  rw [ENNReal.toReal_eq_zero_iff]
  simp [PMF.apply_ne_top]

theorem toReal_pos_iff (X : PMF ℤ) (n : ℤ) : 0 < (X n).toReal ↔ n ∈ X.support := by
  rw [PMF.mem_support_iff, ← not_iff_not, not_lt, not_not, ← toReal_eq_zero_iff]
  constructor
  · intro h; exact le_antisymm h ENNReal.toReal_nonneg
  · intro h; exact h.le

theorem toReal_nonneg' (X : PMF ℤ) (n : ℤ) : 0 ≤ (X n).toReal := ENNReal.toReal_nonneg

theorem toReal_le_one (X : PMF ℤ) (n : ℤ) : (X n).toReal ≤ 1 := by
  have h := PMF.coe_le_one X n
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this

/-- Real-valued convolution formula, as a finite sum over any finset containing `supp Y`. -/
theorem indepSum_toReal (X Y : PMF ℤ) (S : Finset ℤ) (hS : ∀ y, y ∉ S → Y y = 0) (n : ℤ) :
    (indepSum X Y n).toReal = ∑ y ∈ S, (Y y).toReal * (X (n - y)).toReal := by
  rw [indepSum_apply', tsum_eq_sum (s := S) (fun y hy => by simp [hS y hy])]
  rw [ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro y _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

/-- Same, with the sum over the first factor. -/
theorem indepSum_toReal_left (X Y : PMF ℤ) (S : Finset ℤ) (hS : ∀ x, x ∉ S → X x = 0) (n : ℤ) :
    (indepSum X Y n).toReal = ∑ x ∈ S, (X x).toReal * (Y (n - x)).toReal := by
  rw [indepSum_comm]; exact indepSum_toReal Y X S hS n

/-- Total mass in reals over a finset containing the support. -/
theorem sum_toReal_eq_one (X : PMF ℤ) (S : Finset ℤ) (hS : ∀ x, x ∉ S → X x = 0) :
    ∑ x ∈ S, (X x).toReal = 1 := by
  have h1 : ∑' x, X x = ∑ x ∈ S, X x := tsum_eq_sum (fun x hx => hS x hx)
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top X a), ← h1, PMF.tsum_coe]
  simp

theorem notMem_finite_toFinset (X : PMF ℤ) (hX : X.support.Finite) :
    ∀ x, x ∉ hX.toFinset → X x = 0 := by
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  exact (PMF.apply_eq_zero_iff X x).2 hx

/-- Uniform on support from equal (ENNReal) values on the support. -/
theorem isUniform_of_const (X : PMF ℤ) (hX : X.support.Finite)
    (h : ∀ a b, a ∈ X.support → b ∈ X.support → X a = X b) : IsUniformOnSupport X := by
  set s := hX.toFinset with hsdef
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := X.support_nonempty
    exact ⟨a, by simpa [hsdef] using ha⟩
  refine ⟨s, hs, ?_⟩
  obtain ⟨a0, ha0⟩ := id hs
  have ha0' : a0 ∈ X.support := by simpa [hsdef] using ha0
  have hsum : ∑' x, X x = ∑ x ∈ s, X x := tsum_eq_sum (fun x hx => notMem_finite_toFinset X hX x hx)
  have hconst : ∑ x ∈ s, X x = s.card * X a0 := by
    rw [Finset.sum_congr rfl (g := fun _ => X a0)]
    · simp
    · intro x hx
      exact h x a0 (by simpa [hsdef] using hx) ha0'
  have hc : (s.card : ENNReal) * X a0 = 1 := by rw [← hconst, ← hsum, PMF.tsum_coe]
  have hcard0 : (s.card : ENNReal) ≠ 0 := by
    have : 0 < s.card := Finset.card_pos.2 ⟨a0, ha0⟩
    exact_mod_cast this.ne'
  have hval : X a0 = (s.card : ENNReal)⁻¹ := by
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hc)
  ext n
  by_cases hn : n ∈ s
  · rw [PMF.uniformOfFinset_apply, if_pos hn, ← hval]
    exact h n a0 (by simpa [hsdef] using hn) ha0'
  · rw [PMF.uniformOfFinset_apply, if_neg hn]
    exact notMem_finite_toFinset X hX n hn

/-- Uniform on support from equal real values on the support. -/
theorem isUniform_of_const_real (X : PMF ℤ) (hX : X.support.Finite)
    (h : ∀ a b, a ∈ X.support → b ∈ X.support → (X a).toReal = (X b).toReal) :
    IsUniformOnSupport X := by
  refine isUniform_of_const X hX fun a b ha hb => ?_
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 (h a b ha hb)

/-- Uniform on support with a single real value `c` on the support. -/
theorem isUniform_of_value (X : PMF ℤ) (hX : X.support.Finite) (c : ℝ)
    (h : ∀ a, a ∈ X.support → (X a).toReal = c) : IsUniformOnSupport X :=
  isUniform_of_const_real X hX fun a b ha hb => by rw [h a ha, h b hb]

/-- Values of a uniform-on-support PMF: zero or a fixed positive constant. -/
theorem uniform_values (Z : PMF ℤ) (hZ : IsUniformOnSupport Z) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, (Z n).toReal = 0 ∨ (Z n).toReal = c := by
  obtain ⟨s, hs, rfl⟩ := hZ
  refine ⟨((s.card : ENNReal)⁻¹).toReal, ?_, ?_⟩
  · have hc : 0 < s.card := Finset.card_pos.2 hs
    rw [ENNReal.toReal_inv]
    simp only [ENNReal.toReal_natCast]
    exact inv_pos.2 (by exact_mod_cast hc)
  · intro n
    by_cases hn : n ∈ s
    · right; rw [PMF.uniformOfFinset_apply, if_pos hn]
    · left; rw [PMF.uniformOfFinset_apply, if_neg hn]; simp

/-- A uniform-on-support PMF is uniform: real version with the support. -/
theorem uniform_pos_eq (Z : PMF ℤ) (hZ : IsUniformOnSupport Z) :
    ∃ c : ℝ, 0 < c ∧ (∀ n, (Z n).toReal = 0 ∨ (Z n).toReal = c) ∧
      ∀ n, 0 < (Z n).toReal → (Z n).toReal = c := by
  obtain ⟨c, hc, h⟩ := uniform_values Z hZ
  refine ⟨c, hc, h, fun n hn => ?_⟩
  rcases h n with h1 | h1
  · linarith
  · exact h1

theorem isUniform_pure (t : ℤ) : IsUniformOnSupport (PMF.pure t) := by
  refine ⟨{t}, Finset.singleton_nonempty t, ?_⟩
  ext n
  by_cases h : n = t
  · subst h; simp [PMF.uniformOfFinset_apply]
  · rw [PMF.pure_apply_of_ne _ _ h, PMF.uniformOfFinset_apply, if_neg (by simpa using h)]

theorem eq_pure_of_support (Y : PMF ℤ) (t : ℤ) (h : Y.support = {t}) : Y = PMF.pure t := by
  have h1 : Y t = 1 := (PMF.apply_eq_one_iff Y t).2 h
  ext n
  by_cases hn : n = t
  · subst hn; simp [h1]
  · rw [PMF.pure_apply_of_ne _ _ hn, PMF.apply_eq_zero_iff, h]
    simpa using hn

theorem indepSum_pure_right (X : PMF ℤ) (t n : ℤ) : indepSum X (PMF.pure t) n = X (n - t) := by
  rw [indepSum_apply', tsum_eq_single t]
  · simp
  · intro y hy; simp [PMF.pure_apply_of_ne _ _ hy]

theorem indepSum_pure_left (Y : PMF ℤ) (t n : ℤ) : indepSum (PMF.pure t) Y n = Y (n - t) := by
  rw [indepSum_comm]; exact indepSum_pure_right Y t n

/-- Case `supp Y` a singleton: `X` is uniform if the sum is. -/
theorem uniform_of_pure_right (X : PMF ℤ) (hX : X.support.Finite) (t : ℤ)
    (h : IsUniformOnSupport (indepSum X (PMF.pure t))) : IsUniformOnSupport X := by
  obtain ⟨c, _, _, hpos⟩ := uniform_pos_eq _ h
  refine isUniform_of_value X hX c fun a ha => ?_
  have := hpos (a + t)
  rw [indepSum_pure_right, add_sub_cancel_right] at this
  exact this ((toReal_pos_iff X a).2 ha)

theorem support_ncard_pos (X : PMF ℤ) (hX : X.support.Finite) : 1 ≤ X.support.ncard := by
  have := (Set.ncard_pos hX).2 X.support_nonempty
  omega

/-- Two-point support data in reals. -/
theorem two_point (Y : PMF ℤ) (t u : ℤ) (htu : t ≠ u) (h : Y.support = {t, u}) :
    0 < (Y t).toReal ∧ 0 < (Y u).toReal ∧ (Y t).toReal + (Y u).toReal = 1 ∧
      ∀ X : PMF ℤ, ∀ n, (indepSum X Y n).toReal =
        (Y t).toReal * (X (n - t)).toReal + (Y u).toReal * (X (n - u)).toReal := by
  have hS : ∀ y, y ∉ ({t, u} : Finset ℤ) → Y y = 0 := by
    intro y hy
    rw [PMF.apply_eq_zero_iff, h]
    simpa using hy
  refine ⟨(toReal_pos_iff Y t).2 (by rw [h]; simp), (toReal_pos_iff Y u).2 (by rw [h]; simp), ?_, ?_⟩
  · have := sum_toReal_eq_one Y {t, u} hS
    rwa [Finset.sum_pair htu] at this
  · intro X n
    rw [indepSum_toReal X Y {t, u} hS, Finset.sum_pair htu]

/-- Existence of min and max of a finite nonempty set of integers. -/
theorem exists_min_max (s : Set ℤ) (hs : s.Finite) (hne : s.Nonempty) :
    ∃ m M, m ∈ s ∧ M ∈ s ∧ ∀ a ∈ s, m ≤ a ∧ a ≤ M := by
  refine ⟨hs.toFinset.min' (by simpa using hne), hs.toFinset.max' (by simpa using hne), ?_, ?_, ?_⟩
  · simpa using hs.toFinset.min'_mem (by simpa using hne)
  · simpa using hs.toFinset.max'_mem (by simpa using hne)
  · intro a ha
    have ha' : a ∈ hs.toFinset := by simpa using ha
    exact ⟨hs.toFinset.min'_le a ha', hs.toFinset.le_max' a ha'⟩

/-- Support of the sum is finite. -/
theorem indepSum_support_finite (X Y : PMF ℤ) (hX : X.support.Finite) (hY : Y.support.Finite) :
    (indepSum X Y).support.Finite := by
  refine (Set.Finite.image2 (· + ·) hX hY).subset ?_
  intro n hn
  rw [PMF.mem_support_iff, indepSum_apply] at hn
  obtain ⟨x, hx⟩ : ∃ x, X x * Y (n - x) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn (ENNReal.tsum_eq_zero.2 hcon)
  -- hx : X x * Y (n - x) ≠ 0
  have hx1 : X x ≠ 0 := left_ne_zero_of_mul hx
  have hx2 : Y (n - x) ≠ 0 := right_ne_zero_of_mul hx
  exact ⟨x, hx1, n - x, hx2, by ring⟩

end OMA.G28Lib


namespace OMA.G28Core

/-- Step (b): the min and max of the support force equal weights. -/
theorem weights_eq (y : ℤ → ℝ) (hy0 : ∀ n, 0 ≤ y n) (m M : ℤ) (hm : 0 < y m) (hM : 0 < y M)
    (hlo : ∀ n, n < m → y n = 0) (hhi : ∀ n, M < n → y n = 0)
    (α β c : ℝ) (d : ℤ) (hd : 0 < d) (hα : 0 < α) (hβ : 0 < β)
    (hg : ∀ n, α * y n + β * y (n - d) = 0 ∨ α * y n + β * y (n - d) = c) : α = β := by
  have h1 := hg m
  have h2 := hg (m + d)
  have h3 := hg (M + d)
  have h4 := hg M
  rw [hlo (m - d) (by omega)] at h1
  rw [show m + d - d = m by ring] at h2
  rw [hhi (M + d) (by omega), show M + d - d = M by ring] at h3
  have e1 : 0 < α * y m := mul_pos hα hm
  have e2 : 0 < β * y m := mul_pos hβ hm
  have e3 : 0 < β * y M := mul_pos hβ hM
  have e4 : 0 < α * y M := mul_pos hα hM
  have p2 : 0 ≤ α * y (m + d) := mul_nonneg hα.le (hy0 _)
  have p4 : 0 ≤ β * y (M - d) := mul_nonneg hβ.le (hy0 _)
  have hba : β ≤ α := by
    rcases h1 with h1 | h1
    · linarith
    rcases h2 with h2 | h2
    · linarith
    have : β * y m ≤ α * y m := by linarith
    exact le_of_mul_le_mul_right this hm
  have hab : α ≤ β := by
    rcases h3 with h3 | h3
    · linarith
    rcases h4 with h4 | h4
    · linarith
    have : α * y M ≤ β * y M := by linarith
    exact le_of_mul_le_mul_right this hM
  linarith

/-- Step (c): if `x n + x (n - d)` takes values in `{0, C}`, `x ≥ 0` and `x` vanishes below `m`,
then `x` takes values in `{0, C}`. -/
theorem values_two (x : ℤ → ℝ) (hx0 : ∀ n, 0 ≤ x n) (m : ℤ) (hlo : ∀ n, n < m → x n = 0)
    (C : ℝ) (hC : 0 < C) (d : ℤ) (hd : 0 < d)
    (hg : ∀ n, x n + x (n - d) = 0 ∨ x n + x (n - d) = C) : ∀ n, x n = 0 ∨ x n = C := by
  have key : ∀ k : ℕ, ∀ n, n < m + k → x n = 0 ∨ x n = C := by
    intro k
    induction k with
    | zero => intro n hn; left; exact hlo n (by simpa using hn)
    | succ k ih =>
      intro n hn
      by_cases hlt : n < m + k
      · exact ih n hlt
      · have hprev := ih (n - d) (by push_cast at hn ⊢; omega)
        have hn0 := hx0 n
        rcases hprev with hp | hp <;> rcases hg n with hq | hq <;> rw [hp] at hq
        · left; linarith
        · right; linarith
        · left; linarith
        · left; linarith
  intro n
  exact key ((n - m).toNat + 1) n (by push_cast; omega)

/-- Combined: two-point second factor with weights `α, β` at offset `d > 0`. -/
theorem two_point_core (x : ℤ → ℝ) (hx0 : ∀ n, 0 ≤ x n) (m M : ℤ) (hm : 0 < x m) (hM : 0 < x M)
    (hlo : ∀ n, n < m → x n = 0) (hhi : ∀ n, M < n → x n = 0)
    (α β c : ℝ) (hc : 0 < c) (d : ℤ) (hd : 0 < d) (hα : 0 < α) (hβ : 0 < β)
    (hg : ∀ n, α * x n + β * x (n - d) = 0 ∨ α * x n + β * x (n - d) = c) :
    ∀ n, x n = 0 ∨ x n = c / α := by
  have hab := weights_eq x hx0 m M hm hM hlo hhi α β c d hd hα hβ hg
  subst hab
  refine values_two x hx0 m hlo (c / α) (div_pos hc hα) d hd fun n => ?_
  rcases hg n with h | h
  · left
    have : α * (x n + x (n - d)) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact h'
  · right
    field_simp
    linarith

end OMA.G28Core


namespace OMA.R_Green28_green_28_R1_H1_R1

open Green28 OMA.G28Lib OMA.G28Core

/-- Both supports have at least three points, and `X` has no more support points than `Y`. -/
def H1 : Prop :=
  ∀ X Y : PMF ℤ, X.support.Finite → Y.support.Finite →
    3 ≤ X.support.ncard → 3 ≤ Y.support.ncard → X.support.ncard ≤ Y.support.ncard →
    IsUniformOnSupport (indepSum X Y) → IsUniformOnSupport X

/-- Both supports have at least three points, and `X` has more support points than `Y`. -/
def H2 : Prop :=
  ∀ X Y : PMF ℤ, X.support.Finite → Y.support.Finite →
    3 ≤ X.support.ncard → 3 ≤ Y.support.ncard → Y.support.ncard < X.support.ncard →
    IsUniformOnSupport (indepSum X Y) → IsUniformOnSupport X

theorem ordered_pair (s : Set ℤ) (h : s.ncard = 2) : ∃ t u, t < u ∧ s = {t, u} := by
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 h
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, rfl⟩
  · exact ⟨b, a, h, Set.pair_comm a b⟩

theorem lo_hi (X : PMF ℤ) (m M : ℤ) (hmM : ∀ a ∈ X.support, m ≤ a ∧ a ≤ M) :
    (∀ n, n < m → (X n).toReal = 0) ∧ (∀ n, M < n → (X n).toReal = 0) := by
  constructor
  · intro n hn
    by_contra hne
    have h1 : n ∈ X.support :=
      (toReal_pos_iff X n).1 (lt_of_le_of_ne (toReal_nonneg' X n) (Ne.symm hne))
    have := (hmM n h1).1
    omega
  · intro n hn
    by_contra hne
    have h1 : n ∈ X.support :=
      (toReal_pos_iff X n).1 (lt_of_le_of_ne (toReal_nonneg' X n) (Ne.symm hne))
    have := (hmM n h1).2
    omega

/-- Second factor supported on two points. -/
theorem case_Y_two (X Y : PMF ℤ) (hX : X.support.Finite) (t u : ℤ) (htu : t < u)
    (hY : Y.support = {t, u}) (hS : IsUniformOnSupport (indepSum X Y)) : IsUniformOnSupport X := by
  obtain ⟨ha, hb, _, hconv⟩ := two_point Y t u htu.ne hY
  obtain ⟨c, hc, hval, _⟩ := uniform_pos_eq _ hS
  obtain ⟨m, M, hmS, hMS, hmM⟩ := exists_min_max X.support hX X.support_nonempty
  obtain ⟨hlo, hhi⟩ := lo_hi X m M hmM
  have hg : ∀ n, (Y t).toReal * (X n).toReal + (Y u).toReal * (X (n - (u - t))).toReal = 0 ∨
      (Y t).toReal * (X n).toReal + (Y u).toReal * (X (n - (u - t))).toReal = c := by
    intro n
    have h := hval (n + t)
    rw [hconv X (n + t), show n + t - t = n by ring, show n + t - u = n - (u - t) by ring] at h
    exact h
  have hv := two_point_core (fun n => (X n).toReal) (fun n => toReal_nonneg' X n) m M
    ((toReal_pos_iff X m).2 hmS) ((toReal_pos_iff X M).2 hMS) hlo hhi _ _ c hc (u - t)
    (by omega) ha hb hg
  refine isUniform_of_value X hX (c / (Y t).toReal) fun n hn => ?_
  rcases hv n with h | h
  · have := (toReal_pos_iff X n).2 hn
    linarith
  · exact h

/-- First factor supported on two points. -/
theorem case_X_two (X Y : PMF ℤ) (hY : Y.support.Finite) (t u : ℤ) (htu : t < u)
    (hXs : X.support = {t, u}) (hS : IsUniformOnSupport (indepSum X Y)) : IsUniformOnSupport X := by
  have hX : X.support.Finite := by rw [hXs]; exact Set.toFinite _
  obtain ⟨ha, hb, _, hconv⟩ := two_point X t u htu.ne hXs
  obtain ⟨c, hc, hval, _⟩ := uniform_pos_eq _ hS
  obtain ⟨m, M, hmS, hMS, hmM⟩ := exists_min_max Y.support hY Y.support_nonempty
  obtain ⟨hlo, hhi⟩ := lo_hi Y m M hmM
  have hg : ∀ n, (X t).toReal * (Y n).toReal + (X u).toReal * (Y (n - (u - t))).toReal = 0 ∨
      (X t).toReal * (Y n).toReal + (X u).toReal * (Y (n - (u - t))).toReal = c := by
    intro n
    have h := hval (n + t)
    rw [indepSum_comm, hconv Y (n + t), show n + t - t = n by ring,
      show n + t - u = n - (u - t) by ring] at h
    exact h
  have heq := weights_eq (fun n => (Y n).toReal) (fun n => toReal_nonneg' Y n) m M
    ((toReal_pos_iff Y m).2 hmS) ((toReal_pos_iff Y M).2 hMS) hlo hhi _ _ c (u - t)
    (by omega) ha hb hg
  refine isUniform_of_value X hX (X t).toReal fun n hn => ?_
  rw [hXs] at hn
  rcases hn with rfl | hn
  · rfl
  · rw [Set.mem_singleton_iff] at hn
    rw [hn, heq]

/-- The small case: if one factor has support of size at most two, `X` is uniform. -/
theorem small_case (X Y : PMF ℤ) (hX : X.support.Finite) (hY : Y.support.Finite)
    (hS : IsUniformOnSupport (indepSum X Y))
    (h : X.support.ncard ≤ 2 ∨ Y.support.ncard ≤ 2) : IsUniformOnSupport X := by
  have hX1 := support_ncard_pos X hX
  have hY1 := support_ncard_pos Y hY
  rcases h with h | h
  · rcases (show X.support.ncard = 1 ∨ X.support.ncard = 2 by omega) with h1 | h2
    · obtain ⟨t, ht⟩ := Set.ncard_eq_one.1 h1
      rw [eq_pure_of_support X t ht]
      exact isUniform_pure t
    · obtain ⟨t, u, htu, hs⟩ := ordered_pair _ h2
      exact case_X_two X Y hY t u htu hs hS
  · rcases (show Y.support.ncard = 1 ∨ Y.support.ncard = 2 by omega) with h1 | h2
    · obtain ⟨t, ht⟩ := Set.ncard_eq_one.1 h1
      rw [eq_pure_of_support Y t ht] at hS
      exact uniform_of_pure_right X hX t hS
    · obtain ⟨t, u, htu, hs⟩ := ordered_pair _ h2
      exact case_Y_two X Y hX t u htu hs hS

theorem main : H1 → H2 → OMA.R_Green28_green_28_R1.H1 := by
  intro hH1 hH2 X Y hX hY hS
  by_cases h : X.support.ncard ≤ 2 ∨ Y.support.ncard ≤ 2
  · exact small_case X Y hX hY hS h
  · push Not at h
    rcases le_or_gt X.support.ncard Y.support.ncard with hle | hlt
    · exact hH1 X Y hX hY (by omega) (by omega) hle hS
    · exact hH2 X Y hX hY (by omega) (by omega) hlt hS

end OMA.R_Green28_green_28_R1_H1_R1
