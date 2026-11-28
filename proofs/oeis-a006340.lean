import OMAStatements.S_oeis_a006340

-- Problem: A006340: An "eta-sequence": [ (n+1)*tau + 1/2 ] - [ n*tau + 1/2 ], tau = (1 + sqrt(5))/2.
-- Upstream: formal-conjectures statements/oeis-a006340.lean:0 (declaration OMA.S_oeis_a006340.main)
-- Credit: @weizj99 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace A006340Infra
open OMA.S_oeis_a006340
open scoped symmDiff

noncomputable def L (j : ℕ) : ℕ := ⌊(j : ℝ) * Real.goldenRatio⌋₊
noncomputable def U (j : ℕ) : ℕ := ⌊(j : ℝ) * Real.goldenRatio ^ 2⌋₊

noncomputable def r (j : ℕ) : ℕ :=
  ⌊((j : ℝ) + 1) * Real.goldenRatio⌋₊ - ⌊(j : ℝ) * Real.goldenRatio⌋₊

noncomputable def v : ℕ → ℝ
  | 0 => 2
  | j + 1 => r (j + 1) + 1 / v j

theorem L_step (j : ℕ) : L (j + 1) = L j + 1 ∨ L (j + 1) = L j + 2 := by
  have lo (k : ℕ) : (L k : ℝ) ≤ (k : ℝ) * Real.goldenRatio :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg k) Real.goldenRatio_pos.le)
  have hi (k : ℕ) : (k : ℝ) * Real.goldenRatio < (L k : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have lo' := lo (j+1)
  have hi' := hi (j+1)
  push_cast at lo' hi'
  have p : (L j : ℝ) < (L (j+1) : ℝ) := by
    linarith [lo j, Real.one_lt_goldenRatio]
  have q : (L (j+1) : ℝ) < (L j : ℝ) + 3 := by
    linarith [hi j, Real.goldenRatio_lt_two]
  have pp : L j < L (j+1) := by exact_mod_cast p
  have qq : L (j+1) < L j + 3 := by exact_mod_cast q
  omega

theorem r_eq_L_sub (j : ℕ) : r j = L (j+1) - L j := by simp [L, r]

theorem r_one_or_two (j : ℕ) : r j = 1 ∨ r j = 2 := by
  rw [r_eq_L_sub]
  rcases L_step j with h | h <;> omega

theorem U_eq_L_add (j : ℕ) : U j = L j + j := by
  simp only [U, L, Real.goldenRatio_sq, mul_add, mul_one]
  exact Nat.floor_add_natCast (mul_nonneg (Nat.cast_nonneg j) Real.goldenRatio_pos.le) j

theorem U_step (j : ℕ) : U (j+1) = U j + r j + 1 := by
  rw [U_eq_L_add, U_eq_L_add, r_eq_L_sub]
  rcases L_step j with h | h <;> omega

theorem U_strictMono : StrictMono U := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [U_step]
  omega

theorem U_zero : U 0 = 0 := by simp [U]

theorem L_one : L 1 = 1 := by
  simp only [L, Nat.cast_one, one_mul]
  exact Nat.floor_eq_on_Ico 1 _ ⟨by simpa using Real.one_lt_goldenRatio.le,
    by norm_num; exact Real.goldenRatio_lt_two⟩

theorem U_one : U 1 = 2 := by rw [U_eq_L_add, L_one]

theorem beatty_mem_nat_iff (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ((n : ℤ) ∈ {beattySeq x k | k > 0}) ↔
      ∃ k : ℕ, 1 ≤ k ∧ n = ⌊(k : ℝ) * x⌋₊ := by
  constructor
  · rintro ⟨k, hk, h⟩
    lift k to ℕ using hk.le
    refine ⟨k, by exact_mod_cast hk, ?_⟩
    have hf := Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg k) hx)
    simp only [beattySeq, Int.cast_natCast] at h
    exact_mod_cast (h.symm.trans hf.symm)
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ℤ), by exact_mod_cast (show 0 < k by omega), ?_⟩
    simp only [beattySeq, Int.cast_natCast]
    exact (Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg k) hx)).symm

theorem lower_iff_not_upper {n : ℕ} (hn : 1 ≤ n) :
    IsLowerWythoff n ↔ ¬ ∃ k : ℕ, 1 ≤ k ∧ n = U k := by
  have hc : Real.goldenRatio.HolderConjugate (Real.goldenRatio ^ 2) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨Real.one_lt_goldenRatio, ?_⟩
    have aux (p : ℝ) (hp : p ≠ 0) (hs : p ^ 2 = p + 1) : p⁻¹ + (p ^ 2)⁻¹ = 1 := by
      field_simp
      nlinarith
    exact aux _ Real.goldenRatio_ne_zero Real.goldenRatio_sq
  have h := Irrational.beattySeq_symmDiff_beattySeq_pos hc Real.goldenRatio_irrational
  have hm : (n : ℤ) ∈ ({beattySeq Real.goldenRatio k | k > 0} ∆
      {beattySeq (Real.goldenRatio ^ 2) k | k > 0}) := by
    rw [h]
    change 0 < (n : ℤ)
    exact_mod_cast (show 0 < n by omega)
  rw [Set.mem_symmDiff, beatty_mem_nat_iff _ Real.goldenRatio_pos.le,
    beatty_mem_nat_iff _ (sq_nonneg _)] at hm
  change (∃ k : ℕ, 1 ≤ k ∧ n = L k) ↔ ¬ ∃ k : ℕ, 1 ≤ k ∧ n = U k
  change ((∃ k : ℕ, 1 ≤ k ∧ n = L k) ∧ ¬ ∃ k : ℕ, 1 ≤ k ∧ n = U k) ∨
    ((∃ k : ℕ, 1 ≤ k ∧ n = U k) ∧ ¬ ∃ k : ℕ, 1 ≤ k ∧ n = L k) at hm
  rcases hm with h|h
  · exact ⟨fun _ => h.2, fun _ => h.1⟩
  · exact ⟨fun hl => (h.2 hl).elim, fun hu => (hu h.1).elim⟩

theorem lower_of_between {n j : ℕ} (h₀ : U j < n) (h₁ : n < U (j+1)) :
    IsLowerWythoff n := by
  apply (lower_iff_not_upper (by omega)).mpr
  rintro ⟨k, _, rfl⟩
  have hk := U_strictMono.lt_iff_lt.mp h₀
  have hk' := U_strictMono.lt_iff_lt.mp h₁
  omega

theorem upper_not_lower {k : ℕ} (hk : 1 ≤ k) : ¬ IsLowerWythoff (U k) := by
  have hn := U_strictMono.monotone hk
  rw [U_one] at hn
  exact fun h => ((lower_iff_not_upper (by omega)).mp h) ⟨k, hk, rfl⟩

theorem lower_run_card (j : ℕ) :
    (Finset.Ioo (U j) (U (j+1))).card = r j ∧
      ∀ n ∈ Finset.Ioo (U j) (U (j+1)), IsLowerWythoff n := by
  constructor
  · rw [Nat.card_Ioo, U_step]
    omega
  · intro n hn
    exact lower_of_between (Finset.mem_Ioo.mp hn).1 (Finset.mem_Ioo.mp hn).2


theorem v_one_le (j : ℕ) : 1 ≤ v j := by
  induction j with
  | zero => norm_num [v]
  | succ j ih =>
    change 1 ≤ (r (j+1) : ℝ) + 1 / v j
    have hr : 1 ≤ r (j+1) := by rcases r_one_or_two (j+1) with h|h <;> omega
    have hR : (1 : ℝ) ≤ (r (j+1) : ℝ) := by exact_mod_cast hr
    linarith [one_div_nonneg.mpr (zero_le_one.trans ih)]

theorem v_positive (j : ℕ) : 0 < v j := lt_of_lt_of_le zero_lt_one (v_one_le j)

theorem inv_v_le_one (j : ℕ) : 1 / v j ≤ 1 := by
  rw [div_le_iff₀ (v_positive j)]
  simpa using v_one_le j

theorem v_le_three (j : ℕ) : v j ≤ 3 := by
  cases j with
  | zero => norm_num [v]
  | succ j =>
    change (r (j+1) : ℝ) + 1 / v j ≤ 3
    have h := inv_v_le_one j
    rcases r_one_or_two (j+1) with hr | hr <;> rw [hr] <;> push_cast <;> linarith

theorem s_next_lower {n : ℕ} (hn : 1 ≤ n) (hl : IsLowerWythoff n) :
    s (n+1) = s n + 1 := by
  cases n with
  | zero => omega
  | succ n => simp only [s, if_pos hl]

theorem s_next_upper {n : ℕ} (hn : 1 ≤ n) (hu : ¬ IsLowerWythoff n) :
    s (n+1) = 1 / s n := by
  cases n with
  | zero => omega
  | succ n => simp only [s, if_neg hu]

theorem U_pos {j : ℕ} (hj : 1 ≤ j) : 1 ≤ U j := by
  have h := U_strictMono.monotone hj
  rw [U_one] at h
  omega

theorem s_after_upper {j : ℕ} (hj : 1 ≤ j) :
    s (U j + 1) = 1 / s (U j) :=
  s_next_upper (U_pos hj) (upper_not_lower hj)

theorem s_upper (j : ℕ) : s (U (j+1)) = v j := by
  induction j with
  | zero =>
    have h : IsLowerWythoff 1 := ⟨1, by decide, L_one.symm⟩
    change s (U 1) = 2
    rw [U_one, show (2:ℕ) = 1+1 from rfl, s_next_lower (by decide) h]
    norm_num [s]
  | succ j ih =>
    let b := U (j+1)
    have h₁ := s_after_upper (j := j+1) (by omega)
    change s (b+1) = 1 / s b at h₁
    change s b = v j at ih
    have hgap : U (j+1+1) = b + r (j+1) + 1 := U_step (j+1)
    have h₂ : IsLowerWythoff (b+1) := by
      apply lower_of_between (j := j+1) (by dsimp [b]; omega)
      rcases r_one_or_two (j+1) with h|h <;> omega
    have e₂ := s_next_lower (by omega : 1 ≤ b+1) h₂
    change s (U (j+1+1)) = (r (j+1) : ℝ) + 1 / v j
    rcases r_one_or_two (j+1) with hr|hr
    · rw [hgap, hr, Nat.cast_one]
      change s (b+1+1) = 1 + 1 / v j
      rw [e₂, h₁, ih, add_comm]
    · have h₃ : IsLowerWythoff (b+1+1) := by
        apply lower_of_between (j := j+1) (by dsimp [b]; omega)
        omega
      have e₃ := s_next_lower (by omega : 1 ≤ b+1+1) h₃
      rw [hgap, hr]
      change s (b+1+1+1) = 2 + 1 / v j
      rw [e₃, e₂, h₁, ih]
      ring

theorem exists_run (n : ℕ) : ∃ j, U j ≤ n ∧ n < U (j+1) := by
  induction n with
  | zero => exact ⟨0, U_zero.le, by rw [U_one]; omega⟩
  | succ n ih =>
    obtain ⟨j, h₀, h₁⟩ := ih
    by_cases h : n+1 < U (j+1)
    · exact ⟨j, by omega, h⟩
    · have eq : n+1 = U (j+1) := by omega
      exact ⟨j+1, eq.ge, eq ▸ U_strictMono (Nat.lt_succ_self _)⟩

theorem s_nonpeak_le_two {n : ℕ}
    (hne : ∀ j : ℕ, n ≠ U (j+1)) : s n ≤ 2 := by
  by_cases hz : n = 0
  · norm_num [hz, s]
  have hn : 1 ≤ n := by omega
  obtain ⟨j, hj₀, hj₁⟩ := exists_run n
  cases j with
  | zero =>
    rw [U_one] at hj₁
    have eq : n = 1 := by omega
    norm_num [eq, s]
  | succ j =>
    let b := U (j+1)
    have hgap : U (j+1+1) = b + r (j+1) + 1 := U_step _
    have hnb : b < n := lt_of_le_of_ne hj₀ (hne j).symm
    have h₁ : s (b+1) = 1 / v j := by
      rw [show b = U (j+1) from rfl, s_after_upper (by omega), s_upper]
    have hr : r (j+1) ≤ 2 := by rcases r_one_or_two (j+1) with h|h <;> omega
    have hn' : n = b+1 ∨ n = b+1+1 := by omega
    rcases hn' with heq|heq
    · rw [heq, h₁]
      linarith [inv_v_le_one j]
    · have hl : IsLowerWythoff (b+1) := by
        apply lower_of_between (j := j+1) (by dsimp [b]; omega)
        omega
      rw [heq, s_next_lower (by omega) hl, h₁]
      linarith [inv_v_le_one j]

theorem s_bddAbove : BddAbove (Set.range fun n : ℕ => s (n+1)) := by
  refine ⟨3, ?_⟩
  rintro _ ⟨n, rfl⟩
  change s (n+1) ≤ 3
  by_cases h : ∃ j, n+1 = U (j+1)
  · obtain ⟨j,h⟩ := h
    rw [h, s_upper]
    exact v_le_three j
  · have h' := s_nonpeak_le_two (n := n+1) (fun j eq => h ⟨j,eq⟩)
    linarith

theorem v_bddAbove : BddAbove (Set.range v) := by
  refine ⟨3, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact v_le_three j

theorem c_eq_iSup_v : c = ⨆ j, v j := by
  unfold c
  apply le_antisymm
  · apply ciSup_le
    intro n
    by_cases h : ∃ j, n+1 = U (j+1)
    · obtain ⟨j,h⟩ := h
      rw [h, s_upper]
      exact le_ciSup v_bddAbove j
    · have h' := s_nonpeak_le_two (n := n+1) (fun j eq => h ⟨j,eq⟩)
      exact h'.trans (le_ciSup v_bddAbove 0)
  · apply ciSup_le
    intro j
    have h := U_pos (j := j+1) (by omega)
    have eq : U (j+1) - 1 + 1 = U (j+1) := by omega
    have le := le_ciSup s_bddAbove (U (j+1)-1)
    simpa only [eq, s_upper] using le

noncomputable def aN (i : ℕ) : ℕ := (a i).toNat

theorem a_one_or_two (i : ℕ) : a i = 1 ∨ a i = 2 := by
  let x : ℝ := (i : ℝ) * Real.goldenRatio + 1 / 2
  have h : a i = ⌊x + Real.goldenRatio⌋ - ⌊x⌋ := by
    unfold a x
    ring_nf
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  have h₁ := Int.floor_le (x + Real.goldenRatio)
  have h₂ := Int.lt_floor_add_one (x + Real.goldenRatio)
  have hl : (⌊x⌋ : ℝ) < (⌊x + Real.goldenRatio⌋ : ℝ) := by
    linarith [Real.one_lt_goldenRatio]
  have hu : (⌊x + Real.goldenRatio⌋ : ℝ) < (⌊x⌋ : ℝ) + 3 := by
    linarith [Real.goldenRatio_lt_two]
  have hl' : ⌊x⌋ < ⌊x + Real.goldenRatio⌋ := by exact_mod_cast hl
  have hu' : ⌊x + Real.goldenRatio⌋ < ⌊x⌋ + 3 := by exact_mod_cast hu
  omega

theorem aN_cast (i : ℕ) : (a i : ℝ) = (aN i : ℝ) := by
  rcases a_one_or_two i with h | h <;> norm_num [aN, h, Int.toNat]

theorem aN_one_or_two (i : ℕ) : aN i = 1 ∨ aN i = 2 := by
  rcases a_one_or_two i with h | h <;> simp [aN, h]

theorem aN_pos (i : ℕ) : 1 ≤ aN i := by
  rcases aN_one_or_two i with h | h <;> omega

open Filter
open scoped Topology

noncomputable def cfPrefix : (ℕ → ℕ) → ℕ → ℝ → ℝ
  | _, 0, x => x
  | w, n + 1, x => (w 0 : ℝ) + 1 / cfPrefix (fun i => w (i + 1)) n x

theorem cfPrefix_ge_one {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) (n : ℕ)
    {x : ℝ} (hx : 1 ≤ x) : 1 ≤ cfPrefix w n x := by
  induction n generalizing w with
  | zero => exact hx
  | succ n ih =>
    rw [cfPrefix]
    have hd := ih (w := fun i => w (i + 1)) (fun i => hw (i + 1))
    have hh : (1 : ℝ) ≤ w 0 := by exact_mod_cast hw 0
    exact hh.trans (le_add_of_nonneg_right (div_nonneg (by norm_num) (by linarith)))

theorem cfPrefix_append (w : ℕ → ℕ) (m n : ℕ) (x : ℝ) :
    cfPrefix w (m + n) x = cfPrefix w m (cfPrefix (fun i => w (i + m)) n x) := by
  induction m generalizing w with
  | zero => simp [cfPrefix]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [cfPrefix]
    rw [ih]
    simp only [Nat.add_assoc]

theorem cfPrefix_congr {u w : ℕ → ℕ} (n : ℕ) (x : ℝ)
    (h : ∀ i, i < n → u i = w i) : cfPrefix u n x = cfPrefix w n x := by
  induction n generalizing u w with
  | zero => rfl
  | succ n ih =>
    rw [cfPrefix, cfPrefix, h 0 (by omega)]
    rw [ih (u := fun i => u (i+1)) (w := fun i => w (i+1)) (fun i hi => h (i+1) (by omega))]

theorem cf_two_step {a b x y : ℝ} (hb : 1 ≤ b) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |(a + 1 / (b + 1 / x)) - (a + 1 / (b + 1 / y))| ≤ (1/4 : ℝ) * |x-y| := by
  have hx' : 0 < x := by linarith
  have hy' : 0 < y := by linarith
  have hb' : 0 < b := by linarith
  have hbx : 0 < b*x+1 := by positivity
  have hby : 0 < b*y+1 := by positivity
  have hx'' : 0 < b + 1/x := by positivity
  have hy'' : 0 < b + 1/y := by positivity
  have h1 : 1 / (b + 1/x) = x / (b*x+1) := by
    field_simp
  have h2 : 1 / (b + 1/y) = y / (b*y+1) := by
    field_simp
  have h3 : (a + x/(b*x+1)) - (a + y/(b*y+1)) =
      (x-y) / ((b*x+1)*(b*y+1)) := by
    field_simp
    ring
  rw [h1, h2, h3, abs_div, abs_of_pos (mul_pos hbx hby), div_le_iff₀ (mul_pos hbx hby)]
  have hx2 : 2 ≤ b*x+1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) hx'.le]
  have hy2 : 2 ≤ b*y+1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) hy'.le]
  have hprod : 4 ≤ (b*x+1)*(b*y+1) := by
    calc 4 = (2 : ℝ)*2 := by norm_num
         _ ≤ _ := mul_le_mul hx2 hy2 (by norm_num) hbx.le
  nlinarith [mul_nonneg (abs_nonneg (x-y)) (sub_nonneg.mpr hprod)]

theorem cfPrefix_close {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) (k : ℕ)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |cfPrefix w (2*k+1) x - cfPrefix w (2*k+1) y| ≤ (1/4 : ℝ)^k := by
  induction k generalizing w with
  | zero =>
    simp only [cfPrefix, pow_zero]
    have ix : 0 ≤ 1/x := div_nonneg (by norm_num) (by linarith)
    have iy : 0 ≤ 1/y := div_nonneg (by norm_num) (by linarith)
    have bx : 1/x ≤ 1 := (div_le_one₀ (by linarith)).2 hx
    have by' : 1/y ≤ 1 := (div_le_one₀ (by linarith)).2 hy
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega]
    simp only [cfPrefix]
    let t := fun i => w ((i+1)+1)
    have ht : ∀ i, 1 ≤ t i := fun i => hw _
    have h := cf_two_step (a := (w 0 : ℝ)) (b := (w 1 : ℝ)) (by exact_mod_cast hw 1)
      (cfPrefix_ge_one ht (2*k+1) hx) (cfPrefix_ge_one ht (2*k+1) hy)
    calc
      _ ≤ (1/4 : ℝ) * |cfPrefix t (2*k+1) x - cfPrefix t (2*k+1) y| := h
      _ ≤ (1/4 : ℝ) * (1/4 : ℝ)^k := mul_le_mul_of_nonneg_left (ih ht) (by norm_num)
      _ = _ := by ring

theorem cfPrefix_cauchy {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) :
    CauchySeq (fun n => cfPrefix w n 1) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1/4 : ℝ)^k < ε := exists_pow_lt_of_lt_one hε (by norm_num)
  let d := 2*k+1
  refine ⟨d, ?_⟩
  intro m hm n hn
  obtain ⟨p,rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Real.dist_eq, cfPrefix_append w d p, cfPrefix_append w d q]
  exact lt_of_le_of_lt (cfPrefix_close hw k (cfPrefix_ge_one (fun i => hw (i+d)) p le_rfl)
    (cfPrefix_ge_one (fun i => hw (i+d)) q le_rfl)) hk

noncomputable def cfVal (w : ℕ → ℕ) : ℝ := by
  classical
  exact if h : ∃ x : ℝ, Tendsto (fun n => cfPrefix w n 1) atTop (𝓝 x) then h.choose else 0

theorem cfPrefix_tendsto {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) :
    Tendsto (fun n => cfPrefix w n 1) atTop (𝓝 (cfVal w)) := by
  classical
  have h := cauchySeq_tendsto_of_complete (cfPrefix_cauchy hw)
  rw [cfVal, dif_pos h]
  exact h.choose_spec

theorem cfVal_ge_one {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) : 1 ≤ cfVal w :=
  ge_of_tendsto' (cfPrefix_tendsto hw) (fun n => cfPrefix_ge_one hw n le_rfl)

theorem cfVal_unfold {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) :
    cfVal w = (w 0 : ℝ) + 1 / cfVal (fun i => w (i+1)) := by
  let t := fun i => w (i+1)
  have ht : ∀ i, 1 ≤ t i := fun i => hw _
  have hpos : 0 < cfVal t := lt_of_lt_of_le zero_lt_one (cfVal_ge_one ht)
  have hL : Tendsto (fun n => cfPrefix w (n+1) 1) atTop (𝓝 (cfVal w)) :=
    (cfPrefix_tendsto hw).comp (tendsto_add_atTop_nat 1)
  have hR : Tendsto (fun n => (w 0 : ℝ) + 1 / cfPrefix t n 1) atTop
      (𝓝 ((w 0 : ℝ) + 1 / cfVal t)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div (cfPrefix_tendsto ht) hpos.ne')
  exact tendsto_nhds_unique hL hR

theorem cfVal_gt_head {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) : (w 0 : ℝ) < cfVal w := by
  rw [cfVal_unfold hw]
  have ht := cfVal_ge_one (w := fun i => w (i+1)) (fun i => hw _)
  exact lt_add_of_pos_right _ (div_pos zero_lt_one (by linarith))

theorem cfVal_bounds {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) :
    (w 0 : ℝ) < cfVal w ∧ cfVal w < (w 0 : ℝ) + 1 := by
  refine ⟨cfVal_gt_head hw, ?_⟩
  rw [cfVal_unfold hw]
  apply add_lt_add_right
  have h := cfVal_gt_head (w := fun i => w (i+1)) (fun i => hw _)
  have hw1 : (1 : ℝ) ≤ w 1 := by exact_mod_cast hw 1
  change (w 1 : ℝ) < cfVal (fun i => w (i+1)) at h
  exact (div_lt_one₀ (lt_trans zero_lt_one (hw1.trans_lt h))).2 (hw1.trans_lt h)

theorem cfVal_prefix {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) (n : ℕ) :
    cfVal w = cfPrefix w n (cfVal (fun i => w (i+n))) := by
  induction n generalizing w with
  | zero => simp [cfPrefix]
  | succ n ih =>
    rw [cfVal_unfold hw, cfPrefix]
    have h := ih (w := fun i => w (i+1)) (fun i => hw (i+1))
    simpa only [Nat.add_assoc] using congrArg (fun x : ℝ => (w 0 : ℝ) + 1/x) h

theorem v_as_prefix (n j : ℕ) (w : ℕ → ℕ) (hn : n ≤ j)
    (heq : ∀ i : ℕ, i < n → r (j-i) = w i) :
    v j = cfPrefix w n (v (j-n)) := by
  induction n generalizing j w with
  | zero => simp [cfPrefix]
  | succ n ih =>
    cases j with
    | zero => omega
    | succ j =>
      have h0 : r (j+1) = w 0 := by simpa using heq 0 (by omega)
      have he (i : ℕ) (hi : i < n) : r (j-i) = w (i+1) := by
        simpa using heq (i+1) (by omega)
      change (r (j+1) : ℝ) + 1 / v j =
        (w 0 : ℝ) + 1 / cfPrefix (fun i => w (i+1)) n (v ((j+1)-(n+1)))
      rw [h0, Nat.succ_sub_succ_eq_sub, ← ih j (fun i => w (i+1)) (by omega) he]

theorem v_eq_reversed_cf (j : ℕ) :
    v j = cfPrefix (fun i => r (j-i)) j 2 := by
  simpa [Nat.sub_self, v] using
    v_as_prefix j j (fun i => r (j-i)) le_rfl (fun _ _ => rfl)

noncomputable def rotationPoint (i : ℕ) : ℝ := (i : ℝ) * Real.goldenRatio + 1 / 2

theorem rotation_margin (N : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ≤ N, rotationPoint i + ε < (⌊rotationPoint i⌋ : ℝ) + 1 := by
  induction N with
  | zero =>
    let d : ℝ := ((⌊rotationPoint 0⌋ : ℝ) + 1 - rotationPoint 0) / 2
    have h := Int.lt_floor_add_one (rotationPoint 0)
    refine ⟨d, by dsimp [d]; linarith, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    dsimp [d]
    linarith
  | succ N ih =>
    obtain ⟨ε, hε, H⟩ := ih
    let d : ℝ := ((⌊rotationPoint (N+1)⌋ : ℝ) + 1 - rotationPoint (N+1)) / 2
    have h := Int.lt_floor_add_one (rotationPoint (N+1))
    have hd : 0 < d := by dsimp [d]; linarith
    refine ⟨min ε d, lt_min hε hd, fun i hi => ?_⟩
    by_cases hlast : i = N + 1
    · subst i
      have hm := min_le_right ε d
      dsimp [d] at hm
      linarith
    · exact lt_of_le_of_lt (add_le_add_right (min_le_left ε d) _) (H i (by omega))

theorem rotation_contraction :
    0 < 13 - 8 * Real.goldenRatio ∧ 13 - 8 * Real.goldenRatio < 1 / 2 := by
  have hu : Real.goldenRatio < 13 / 8 := by
    by_contra! h
    nlinarith only [Real.goldenRatio_sq, mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ Real.goldenRatio + 5 / 8 by linarith [Real.goldenRatio_pos])]
  have hl : 25 / 16 < Real.goldenRatio := by
    by_contra! h
    nlinarith only [Real.goldenRatio_sq, mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ Real.goldenRatio + 9 / 16 by linarith [Real.goldenRatio_pos])]
  constructor <;> linarith

noncomputable def halfGap (k h : ℕ) : ℝ := (h : ℝ) + 1 / 2 - (k : ℝ) * Real.goldenRatio

theorem halfGap_contract (k h : ℕ) :
    halfGap (5*k + 8*h + 4) (8*k + 13*h + 6) =
      halfGap k h * (13 - 8 * Real.goldenRatio) := by
  unfold halfGap
  push_cast
  linear_combination -(8 * (k : ℝ)) * Real.goldenRatio_sq

theorem halfGap_sequence (n : ℕ) : ∃ k h : ℕ, n < k ∧ 0 < halfGap k h ∧
    ((n : ℝ) + 1) * halfGap k h ≤ 1 := by
  obtain ⟨hc, hsmall⟩ := rotation_contraction
  induction n with
  | zero =>
    refine ⟨4, 6, by decide, ?_, ?_⟩ <;> norm_num [halfGap] <;> linarith
  | succ n ih =>
    obtain ⟨k, h, hk, hd, hbound⟩ := ih
    refine ⟨5*k + 8*h + 4, 8*k + 13*h + 6, by omega, ?_, ?_⟩
    · rw [halfGap_contract]
      exact mul_pos hd hc
    · rw [halfGap_contract, Nat.cast_succ]
      have hs : halfGap k h * (13 - 8 * Real.goldenRatio) ≤ halfGap k h / 2 := by
        linarith [mul_le_mul_of_nonneg_left hsmall.le hd.le]
      calc
        _ ≤ ((n : ℝ) + 1 + 1) * (halfGap k h / 2) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ ≤ ((n : ℝ) + 1) * halfGap k h := by
          nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hd.le]
        _ ≤ 1 := hbound

theorem halfGap_small (N : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ k h : ℕ, N < k ∧ 0 < halfGap k h ∧ halfGap k h < ε := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  obtain ⟨k, h, hk, hd, hb⟩ := halfGap_sequence (N + m)
  refine ⟨k, h, by omega, hd, ?_⟩
  have hm' := (div_lt_iff₀ he).mp hm
  by_contra! H
  have hle := mul_le_mul_of_nonneg_left H (show 0 ≤ ((N + m : ℕ) : ℝ) + 1 by positivity)
  push_cast at hb hle
  nlinarith only [hb, hle, hm', he, mul_nonneg (Nat.cast_nonneg (α := ℝ) N) he.le]

theorem rotation_reflect_floor {k h i : ℕ} {ε : ℝ} (hi : i ≤ k)
    (hd : 0 < halfGap k h) (he : halfGap k h < ε)
    (hm : rotationPoint i + ε < (⌊rotationPoint i⌋ : ℝ) + 1) :
    (⌊((k-i : ℕ) : ℝ) * Real.goldenRatio⌋₊ : ℤ) = (h : ℤ) - ⌊rotationPoint i⌋ := by
  rw [Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg _) Real.goldenRatio_pos.le)]
  apply Int.floor_eq_iff.mpr
  rw [Int.cast_sub, Int.cast_natCast, Nat.cast_sub hi, sub_mul]
  have hlo := Int.floor_le (rotationPoint i)
  unfold halfGap at hd he
  have hs : rotationPoint i = (i : ℝ) * Real.goldenRatio + 1 / 2 := rfl
  constructor <;> linarith

theorem reversed_prefix_exists (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧ ∀ i : ℕ, i < N → r (j-i) = aN i := by
  obtain ⟨ε, hε, hm⟩ := rotation_margin N
  obtain ⟨k, h, hk, hd, he⟩ := halfGap_small N hε
  refine ⟨k-1, by omega, fun i hi => ?_⟩
  have h₀ := rotation_reflect_floor (i := i) (by omega : i ≤ k) hd he (hm i (by omega))
  have h₁ := rotation_reflect_floor (i := i+1) (by omega : i+1 ≤ k) hd he (hm (i+1) hi)
  rw [show k-i = k-1-i+1 by omega, Nat.cast_add, Nat.cast_one] at h₀
  rw [show k-(i+1) = k-1-i by omega] at h₁
  have ha : a i = ⌊rotationPoint (i+1)⌋ - ⌊rotationPoint i⌋ := by simp [a, rotationPoint]
  unfold r aN
  rw [ha]
  omega

/-- A common prefix of odd length bounds the distance to the infinite fraction. -/
theorem v_approaches_cfVal {ε : ℝ} (hε : 0 < ε) :
    ∃ j : ℕ, cfVal aN - ε < v j := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (show (1/4 : ℝ) < 1 by norm_num)
  let N := 2*k+1
  obtain ⟨j, hj, he⟩ := reversed_prefix_exists N
  refine ⟨j, ?_⟩
  have hclose := cfPrefix_close aN_pos k (v_one_le (j-N))
    (cfVal_ge_one (w := fun i => aN (i+N)) (fun i => aN_pos _))
  change |cfPrefix aN N (v (j-N)) - cfPrefix aN N _| ≤ _ at hclose
  rw [← v_as_prefix N j aN hj he, ← cfVal_prefix aN_pos N] at hclose
  linarith [(abs_le.mp hclose).1]

/-- The integer and fractional parts at position n come from the nth complete quotient. -/
theorem cfVal_digits {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) :
    (GenContFract.of (cfVal w)).h = (w 0 : ℝ) ∧
    ∀ n : ℕ, (GenContFract.of (cfVal w)).s.get? n = some ⟨1, (w (n+1) : ℝ)⟩ := by
  let q (n : ℕ) := cfVal (fun i => w (i + n))
  have hq (n : ℕ) : (w n : ℝ) < q n ∧ q n < (w n : ℝ) + 1 := by
    simpa [q] using (cfVal_bounds (w := fun i => w (i + n)) (fun i => hw (i + n)))
  have hf (n : ℕ) : ⌊q n⌋ = (w n : ℤ) := by
    apply Int.floor_eq_iff.mpr
    simpa using And.intro (hq n).1.le (hq n).2
  have hrec (n : ℕ) : q n = (w n : ℝ) + 1 / q (n + 1) := by
    simpa [q, Nat.add_assoc, Nat.add_comm 1] using
      (cfVal_unfold (w := fun i => w (i + n)) (fun i => hw (i + n)))
  have hfr (n : ℕ) : Int.fract (q n) = (q (n+1))⁻¹ := by
    rw [Int.fract, hf, Int.cast_natCast]
    linarith [show q n = (w n : ℝ) + (q (n+1))⁻¹ by simpa only [one_div] using hrec n]
  have hs (n : ℕ) : GenContFract.IntFractPair.stream (cfVal w) n =
      some (GenContFract.IntFractPair.of (q n)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hp : 0 < q (n+1) := lt_of_le_of_lt (Nat.cast_nonneg _) (hq _).1
      have hn : (GenContFract.IntFractPair.of (q n)).fr ≠ 0 := by
        change Int.fract (q n) ≠ 0
        rw [hfr]
        exact inv_ne_zero hp.ne'
      have hnext := GenContFract.IntFractPair.stream_succ_of_some ih hn
      simpa only [GenContFract.IntFractPair.of, hfr, inv_inv] using hnext
  constructor
  · rw [GenContFract.of_h_eq_floor]
    change ((⌊q 0⌋ : ℤ) : ℝ) = _
    simp [hf]
  · intro n
    have h := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream (hs (n+1))
    simpa only [GenContFract.IntFractPair.of, hf, Int.cast_natCast] using h

def H_upper : Prop := ∀ j : ℕ, v j ≤ cfVal aN

theorem c_eq_cfVal (h : H_upper) : c = cfVal aN := by
  apply le_antisymm
  · rw [c_eq_iSup_v]
    exact ciSup_le h
  · by_contra! hlt
    obtain ⟨j, hj⟩ := v_approaches_cfVal (sub_pos.mpr hlt)
    have hle : v j ≤ c := c_eq_iSup_v ▸ le_ciSup v_bddAbove j
    linarith

theorem main_of_upper (h : H_upper) : type_of% @OMA.S_oeis_a006340.main := by
  refine ⟨s_bddAbove, ?_⟩
  rw [c_eq_cfVal h]
  simpa only [aN_cast] using cfVal_digits aN_pos

end A006340Infra

open A006340Infra

namespace A006340Infra

open OMA.S_oeis_a006340

noncomputable def recordError (n : ℕ) (p : ℤ) : ℝ :=
  2 * (n : ℝ) * Real.goldenRatio - (p : ℝ)

theorem record_phi_bounds : (8/5 : ℝ) < Real.goldenRatio ∧ Real.goldenRatio < 13/8 := by
  constructor
  · by_contra! h
    nlinarith only [Real.goldenRatio_sq, mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ Real.goldenRatio + 3/5 by linarith [Real.goldenRatio_pos])]
  · by_contra! h
    nlinarith only [Real.goldenRatio_sq, mul_nonneg (sub_nonneg.mpr h)
      (show 0 ≤ Real.goldenRatio + 5/8 by linarith [Real.goldenRatio_pos])]

theorem record_transform {m n : ℕ} {q p : ℤ}
    (hn : (n : ℤ) = m + q) (hp : p = 4*(m : ℤ) + 3*q) :
    recordError n p = -(2*Real.goldenRatio-3) * recordError m q := by
  have hnr : (n : ℝ) = m + (q : ℝ) := by exact_mod_cast hn
  have hpr : (p : ℝ) = 4*(m : ℝ) + 3*(q : ℝ) := by exact_mod_cast hp
  unfold recordError
  rw [hnr, hpr]
  linear_combination (4*(m : ℝ)) * Real.goldenRatio_sq

theorem wrong_record_improved (n : ℕ) (p : ℤ) (hp : p % 2 = 1) (hn : 0 < n)
    (hlo : -1 ≤ recordError n p) (hhi : recordError n p ≤ 1)
    (hw : (n % 2 = 0 ∧ 0 < recordError n p) ∨ (n % 2 = 1 ∧ recordError n p < 0)) :
    ∃ (m : ℕ) (q : ℤ), 0 < m ∧ m < n ∧ q % 2 = 1 ∧
      ((0 < recordError m q ∧ recordError m q < recordError n p) ∨
       (recordError n p < recordError m q ∧ recordError m q < 0)) := by
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    let δ : ℝ := 2 * Real.goldenRatio - 3
    obtain ⟨hφ, Hφ⟩ := record_phi_bounds
    have hd : 0 < δ := by dsimp [δ]; linarith
    have hδ1 : δ < 1 := by dsimp [δ]; linarith
    have e1 : recordError 1 3 = δ := by norm_num [recordError, δ]
    have e4 : -δ < recordError 4 13 ∧ recordError 4 13 < 0 := by
      norm_num [recordError, δ]
      constructor <;> linarith
    by_cases Hpos : δ < recordError n p
    · have he : n % 2 = 0 := hw.resolve_right (fun h => by linarith [h.2]) |>.1
      exact ⟨1, 3, by decide, by omega, by decide, Or.inl ⟨e1 ▸ hd, e1 ▸ Hpos⟩⟩
    by_cases Hneg : recordError n p < -δ
    · have ho : n % 2 = 1 := hw.resolve_left (fun h => by linarith [h.2]) |>.1
      have hn4 : 4 < n := by
        by_contra! h
        have hcase : n = 1 ∨ n = 3 := by omega
        rcases hcase with rfl|rfl
        · norm_num [recordError] at hlo Hneg
          have pl : (3 : ℤ) < p := by
            exact_mod_cast (show (3:ℝ) < p by linarith)
          have pu : p < (5 : ℤ) := by
            exact_mod_cast (show (p:ℝ) < 5 by linarith)
          omega
        · norm_num [recordError] at hlo Hneg
          have pl : (9 : ℤ) < p := by
            exact_mod_cast (show (9:ℝ) < p by linarith)
          have pu : p < (11 : ℤ) := by
            exact_mod_cast (show (p:ℝ) < 11 by linarith)
          omega
      exact ⟨4, 13, by decide, hn4, by decide, Or.inr ⟨Hneg.trans e4.1, e4.2⟩⟩
    push Not at Hpos Hneg
    let N : ℕ := (p - 3*n).toNat
    let P : ℤ := 4*n-p
    have hlo' := hlo
    have hhi' := hhi
    unfold recordError at hlo' hhi'
    have hNnon : 0 ≤ p - 3*(n : ℤ) := by
      have hh : 3*(n : ℤ) - 1 < p := by
        exact_mod_cast (show 3*(n:ℝ)-1 < (p:ℝ) by
          nlinarith only [hhi', mul_pos (Nat.cast_pos.mpr hn : 0 < (n:ℝ)) hd,
            show δ = 2*Real.goldenRatio-3 from rfl])
      omega
    have HN : (N : ℤ) = p - 3*n := Int.toNat_of_nonneg hNnon
    have hNlt : N < n := by
      have hh : p < 4*(n : ℤ)+1 := by
        exact_mod_cast (show (p:ℝ) < 4*(n:ℝ)+1 by
          nlinarith only [hlo', mul_pos (Nat.cast_pos.mpr hn : 0 < (n:ℝ))
            (show 0 < 2-Real.goldenRatio by linarith)])
      omega
    have hNpos : 0 < N := by
      by_contra! h
      have hpn : p = 3*n := by omega
      have hpn' : (p:ℝ) = 3*(n:ℝ) := by exact_mod_cast hpn
      have herr : 0 < recordError n p := by
        unfold recordError
        rw [hpn']
        have hprod := mul_pos (Nat.cast_pos.mpr hn : 0 < (n:ℝ)) hd
        dsimp [δ] at hprod
        linarith
      rcases hw with hw|hw
      · omega
      · linarith [hw.2]
    have hnF : (n : ℤ) = N + P := by dsimp [P]; omega
    have hpF : p = 4*(N : ℤ) + 3*P := by dsimp [P]; omega
    have hF : recordError n p = -δ * recordError N P := record_transform hnF hpF
    have hNlo : -1 ≤ recordError N P := by
      by_contra! ht
      nlinarith only [mul_pos hd (sub_pos.mpr ht), Hpos, hF]
    have hNhi : recordError N P ≤ 1 := by
      by_contra! ht
      nlinarith only [mul_pos hd (sub_pos.mpr ht), Hneg, hF]
    have hW : (N % 2 = 0 ∧ 0 < recordError N P) ∨
        (N % 2 = 1 ∧ recordError N P < 0) := by
      rcases hw with hw|hw
      · right
        refine ⟨by omega, ?_⟩
        by_contra! ht
        nlinarith only [mul_nonneg hd.le ht, hF, hw.2]
      · left
        refine ⟨by omega, ?_⟩
        by_contra! ht
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos hd.le ht, hF, hw.2]
    obtain ⟨m,q,hm,hmN,hq,he⟩ := ih N hNlt P (by dsimp [P]; omega) hNpos hNlo hNhi hW
    have hml : -1 ≤ recordError m q := by rcases he with he|he <;> linarith [he.1,he.2]
    have hmu : recordError m q ≤ 1 := by rcases he with he|he <;> linarith [he.1,he.2]
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmNR : (m : ℝ)+1 ≤ (N : ℝ) := by exact_mod_cast hmN
    have hqpos : 0 < q := by
      unfold recordError at hmu
      exact_mod_cast (show 0 < (q : ℝ) by
        nlinarith only [hmu, hmR, mul_pos (Nat.cast_pos.mpr hm : 0 < (m:ℝ))
          (show 0 < Real.goldenRatio - 1 by linarith)])
    have hqP : q < P := by
      unfold recordError at hml hNhi
      exact_mod_cast (show (q : ℝ) < P by
        nlinarith only [hml, hNhi, hmNR, mul_pos (show 0 < (N:ℝ)-(m:ℝ) by linarith)
          (show 0 < Real.goldenRatio-1 by linarith)])
    let m' := ((m : ℤ) + q).toNat
    let q' : ℤ := 4*(m : ℤ) + 3*q
    have hm' : (m' : ℤ) = m + q := Int.toNat_of_nonneg (by omega)
    have hF' : recordError m' q' = -δ * recordError m q := record_transform hm' rfl
    refine ⟨m', q', by omega, by omega, by dsimp [q']; omega, ?_⟩
    rcases he with he|he
    · right
      rw [hF, hF']
      exact ⟨mul_lt_mul_of_neg_left he.2 (neg_lt_zero.mpr hd),
        mul_neg_of_neg_of_pos (neg_lt_zero.mpr hd) he.1⟩
    · left
      rw [hF, hF']
      exact ⟨mul_pos_of_neg_of_neg (neg_lt_zero.mpr hd) he.2,
        mul_lt_mul_of_neg_left he.1 (neg_lt_zero.mpr hd)⟩

theorem rotationPoint_irrational {n : ℕ} (hn : 0 < n) : Irrational (rotationPoint n) := by
  simpa [rotationPoint] using
    (Real.goldenRatio_irrational.natCast_mul hn.ne').add_ratCast (1/2)

theorem recordError_at_boundary (n : ℕ) (z : ℤ) :
    recordError n (2*z-1) = 2 * (rotationPoint n - (z : ℝ)) := by
  simp only [recordError, rotationPoint, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  ring

theorem floor_diff_at_int {x y : ℝ} {z : ℤ} (hx : x < (z : ℝ)) (hy : (z : ℝ) ≤ y) :
    ⌊x⌋ ≠ ⌊y⌋ := by
  exact ne_of_lt ((Int.floor_lt.mpr hx).trans_le (Int.le_floor.mpr hy))

theorem first_shift_floor_parity (d : ℝ) (n : ℕ) (hn : 0 < n)
    (hd₀ : -(1/2 : ℝ) ≤ d) (hd₁ : d ≤ 1/2)
    (hprev : ∀ m : ℕ, m < n → ⌊rotationPoint m + d⌋ = ⌊rotationPoint m⌋)
    (hdiff : ⌊rotationPoint n + d⌋ ≠ ⌊rotationPoint n⌋) :
    (0 < d ∧ n % 2 = 0 ∧ ⌊rotationPoint n + d⌋ = ⌊rotationPoint n⌋ + 1) ∨
    (d < 0 ∧ n % 2 = 1 ∧ ⌊rotationPoint n + d⌋ = ⌊rotationPoint n⌋ - 1) := by
  let f := ⌊rotationPoint n⌋
  let g := ⌊rotationPoint n + d⌋
  have f₀ : (f : ℝ) < rotationPoint n :=
    lt_of_le_of_ne (Int.floor_le _) ((rotationPoint_irrational hn).ne_int f).symm
  have f₁ : rotationPoint n < (f : ℝ) + 1 := Int.lt_floor_add_one _
  have g₀ : (g : ℝ) ≤ rotationPoint n + d := Int.floor_le _
  have g₁ : rotationPoint n + d < (g : ℝ) + 1 := Int.lt_floor_add_one _
  have hL : f - 2 < g := by exact_mod_cast (show (f : ℝ) - 2 < (g : ℝ) by linarith)
  have hU : g < f + 2 := by exact_mod_cast (show (g : ℝ) < (f : ℝ) + 2 by linarith)
  change g ≠ f at hdiff
  have halts : g = f+1 ∨ g = f-1 := by omega
  rcases halts with h | h
  · have hc : (g : ℝ) = (f : ℝ)+1 := by exact_mod_cast h
    have he := recordError_at_boundary n (f+1)
    push_cast at he
    have hneg : recordError n (2*(f+1)-1) < 0 := by linarith
    refine Or.inl ⟨by linarith, ?_, h⟩
    by_contra hbad
    obtain ⟨m,q,_,hm,hq,H⟩ := wrong_record_improved n (2*(f+1)-1) (by omega) hn
      (by linarith) (by linarith) (Or.inr ⟨by omega,hneg⟩)
    let z := (q+1)/2
    have hq' : q = 2*z-1 := by dsimp [z]; omega
    have hm' : recordError m q = 2*(rotationPoint m-(z:ℝ)) := by
      rw [hq']; exact recordError_at_boundary _ _
    rcases H with H|H
    · linarith [H.1,H.2]
    · exact floor_diff_at_int (z := z) (by linarith [H.2] : rotationPoint m < (z:ℝ))
        (by linarith [H.1] : (z:ℝ) ≤ rotationPoint m+d) (hprev m hm).symm
  · have hc : (g : ℝ) = (f : ℝ)-1 := by exact_mod_cast h
    have he := recordError_at_boundary n f
    have hpos : 0 < recordError n (2*f-1) := by linarith
    refine Or.inr ⟨by linarith, ?_, h⟩
    by_contra hbad
    obtain ⟨m,q,_,hm,hq,H⟩ := wrong_record_improved n (2*f-1) (by omega) hn
      (by linarith) (by linarith) (Or.inl ⟨by omega,hpos⟩)
    let z := (q+1)/2
    have hq' : q = 2*z-1 := by dsimp [z]; omega
    have hm' : recordError m q = 2*(rotationPoint m-(z:ℝ)) := by
      rw [hq']; exact recordError_at_boundary _ _
    rcases H with H|H
    · exact floor_diff_at_int (z := z) (by linarith [H.2] : rotationPoint m+d < (z:ℝ))
        (by linarith [H.1] : (z:ℝ) ≤ rotationPoint m) (hprev m hm)
    · linarith [H.1,H.2]

theorem at_boundary_negative_parity (d : ℝ) (n : ℕ) (hn : 0 < n)
    (hd₀ : -(1/2 : ℝ) ≤ d) (hd : d < 0)
    (hprev : ∀ m : ℕ, m < n → ⌊rotationPoint m+d⌋ = ⌊rotationPoint m⌋)
    (z : ℤ) (hz : rotationPoint n+d = (z : ℝ)) : n % 2 = 1 := by
  have he := recordError_at_boundary n z
  have hp : 0 < recordError n (2*z-1) := by linarith
  by_contra hbad
  obtain ⟨m,q,_,hm,hq,H⟩ := wrong_record_improved n (2*z-1) (by omega) hn
    (by linarith) (by linarith) (Or.inl ⟨by omega,hp⟩)
  let b := (q+1)/2
  have hq' : q = 2*b-1 := by dsimp [b]; omega
  have hem : recordError m q = 2*(rotationPoint m-(b:ℝ)) := by
    rw [hq']; exact recordError_at_boundary _ _
  rcases H with H|H
  · exact floor_diff_at_int (z := b) (by linarith [H.2] : rotationPoint m+d < (b:ℝ))
      (by linarith [H.1] : (b:ℝ) ≤ rotationPoint m) (hprev m hm)
  · linarith [H.1,H.2]

theorem cfPrefix_alt_lt {w : ℕ → ℕ} (hw : ∀ i, 1 ≤ w i) (k : ℕ)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : (k % 2 = 0 ∧ x < y) ∨ (k % 2 = 1 ∧ y < x)) :
    cfPrefix w k x < cfPrefix w k y := by
  induction k generalizing w x y with
  | zero => simpa [cfPrefix] using h
  | succ k ih =>
    let t := fun i => w (i+1)
    have ht : ∀ i, 1 ≤ t i := fun i => hw _
    have h' : (k % 2 = 0 ∧ y < x) ∨ (k % 2 = 1 ∧ x < y) := by
      rcases h with ⟨he, hxy⟩ | ⟨ho, hyx⟩
      · exact Or.inr ⟨by omega, hxy⟩
      · exact Or.inl ⟨by omega, hyx⟩
    have hlt : cfPrefix t k y < cfPrefix t k x := ih ht hy hx h'
    have hpos : 0 < cfPrefix t k y := zero_lt_one.trans_le (cfPrefix_ge_one ht k hy)
    change (w 0 : ℝ) + 1 / cfPrefix t k x < (w 0 : ℝ) + 1 / cfPrefix t k y
    exact add_lt_add_right (one_div_lt_one_div_of_lt hpos hlt) _

theorem v_gt_one (j : ℕ) : 1 < v j := by
  cases j with
  | zero => norm_num [v]
  | succ j =>
    have hp := one_div_pos.mpr (v_positive j)
    have hr : 1 ≤ r (j+1) := by rcases r_one_or_two (j+1) with h|h <;> omega
    have hh : (1 : ℝ) ≤ r (j+1) := by exact_mod_cast hr
    change 1 < (r (j+1) : ℝ) + 1 / v j
    linarith

theorem v_between_head {n : ℕ} (hn : 0 < n) :
    (r n : ℝ) < v n ∧ v n < (r n : ℝ) + 1 := by
  cases n with
  | zero => omega
  | succ n =>
    change (r (n+1) : ℝ) < (r (n+1) : ℝ) + 1/v n ∧
      (r (n+1) : ℝ) + 1/v n < (r (n+1) : ℝ) + 1
    exact ⟨lt_add_of_pos_right _ (one_div_pos.mpr (v_positive n)),
      add_lt_add_right ((div_lt_one₀ (v_positive n)).mpr (v_gt_one n)) _⟩

theorem v_lt_cfVal_of_mismatch (j k : ℕ) (hk : k < j)
    (hprefix : ∀ i, i < k → r (j-i) = aN i)
    (horder : (k % 2 = 0 ∧ r (j-k) < aN k) ∨ (k % 2 = 1 ∧ aN k < r (j-k))) :
    v j < cfVal aN := by
  let t := fun i => aN (i+k)
  have ht : ∀ i, 1 ≤ t i := fun i => aN_pos _
  have hV := v_between_head (n := j-k) (by omega)
  have hT : (aN k : ℝ) < cfVal t ∧ cfVal t < (aN k : ℝ) + 1 := by
    simpa [t] using cfVal_bounds ht
  rw [v_as_prefix k j aN hk.le hprefix, cfVal_prefix aN_pos k]
  apply cfPrefix_alt_lt aN_pos k (v_one_le _) (cfVal_ge_one ht)
  rcases horder with ⟨he,h⟩ | ⟨ho,h⟩
  · have hh : (r (j-k) : ℝ) + 1 ≤ aN k := by exact_mod_cast h
    exact Or.inl ⟨he, hV.2.trans (hh.trans_lt hT.1)⟩
  · have hh : (aN k : ℝ) + 1 ≤ r (j-k) := by exact_mod_cast h
    exact Or.inr ⟨ho, hT.2.trans (hh.trans_lt hV.1)⟩

theorem v_lt_cfVal_of_terminal (j : ℕ)
    (hprefix : ∀ i, i < j → r (j-i) = aN i)
    (horder : (j % 2 = 0 ∧ aN j = 2) ∨ (j % 2 = 1 ∧ aN j = 1)) :
    v j < cfVal aN := by
  let t := fun i => aN (i+j)
  have ht : ∀ i, 1 ≤ t i := fun i => aN_pos _
  have hT : (aN j : ℝ) < cfVal t ∧ cfVal t < (aN j : ℝ) + 1 := by
    simpa [t] using cfVal_bounds ht
  rw [v_as_prefix j j aN le_rfl hprefix, cfVal_prefix aN_pos j, Nat.sub_self]
  apply cfPrefix_alt_lt aN_pos j (v_one_le _) (cfVal_ge_one ht)
  change (j % 2 = 0 ∧ 2 < cfVal t) ∨ (j % 2 = 1 ∧ cfVal t < 2)
  rcases horder with ⟨he,h⟩ | ⟨ho,h⟩
  · exact Or.inl ⟨he, by simpa [h] using hT.1⟩
  · exact Or.inr ⟨ho, by norm_num [h] at hT; exact hT.2⟩

theorem center_digit (i : ℕ) :
    ⌊rotationPoint (i+1)⌋ - ⌊rotationPoint i⌋ = (aN i : ℤ) := by
  have h : ⌊rotationPoint (i+1)⌋ - ⌊rotationPoint i⌋ = a i := by
    simp [rotationPoint, a]
  rw [h]
  exact_mod_cast aN_cast i

theorem reverse_phase (j : ℕ) : ∃ d : ℝ,
    -(1/2 : ℝ) ≤ d ∧ d ≤ 1/2 ∧ d ≠ 0 ∧
    ⌊rotationPoint 0 + d⌋ = ⌊rotationPoint 0⌋ ∧
    (∀ i : ℕ, i < j → ⌊rotationPoint (i+1) + d⌋ - ⌊rotationPoint i + d⌋ = (r (j-i) : ℤ)) ∧
    ⌊rotationPoint (j+1) + d⌋ - ⌊rotationPoint j + d⌋ = 2 ∧
    ∃ z : ℤ, rotationPoint (j+1) + d = (z : ℝ) := by
  let k := j+1
  let d : ℝ := (L k : ℝ) + 1/2 - (k : ℝ) * Real.goldenRatio
  have lo (t : ℕ) (ht : t ≠ 0) : (L t : ℝ) < (t : ℝ) * Real.goldenRatio := by
    have h := Nat.floor_le (mul_nonneg (Nat.cast_nonneg t) Real.goldenRatio_pos.le)
    have hir := Real.goldenRatio_irrational.natCast_mul ht
    have hne := hir.ne_int (L t : ℤ)
    push_cast at hne
    exact lt_of_le_of_ne h hne.symm
  have hi (t : ℕ) : (t : ℝ)*Real.goldenRatio < (L t : ℝ)+1 := Nat.lt_floor_add_one _
  have hk : k ≠ 0 := Nat.succ_ne_zero j
  have hk2 : 2*k ≠ 0 := by omega
  have hzero : d ≠ 0 := by
    intro he
    have h := (Real.goldenRatio_irrational.natCast_mul hk2).ne_int ((2 : ℤ)*(L k : ℤ)+1)
    apply h
    push_cast
    dsimp [d] at he
    linarith
  have inner (i : ℕ) (hi' : i < k) :
      ⌊rotationPoint i + d⌋ = (L k : ℤ) - (L (k-i) : ℤ) := by
    apply Int.floor_eq_iff.mpr
    have low := lo (k-i) (by omega)
    have high := hi (k-i)
    rw [Nat.cast_sub hi'.le, sub_mul] at low high
    simp only [rotationPoint, d, Int.cast_sub, Int.cast_natCast]
    constructor <;> linarith
  have endval : rotationPoint k + d = ((L k : ℤ)+1 : ℤ) := by
    simp [rotationPoint, d]
    ring
  have kend : ⌊rotationPoint k + d⌋ = (L k : ℤ) + 1 := by rw [endval, Int.floor_intCast]
  refine ⟨d, ?_, ?_, hzero, ?_, ?_, ?_, (L k : ℤ)+1, endval⟩
  · dsimp [d]
    linarith [hi k]
  · dsimp [d]
    linarith [lo k hk]
  · rw [inner 0 (by omega)]
    norm_num [rotationPoint]
  · intro i hi'
    rw [inner (i+1) (by omega), inner i (by omega), r_eq_L_sub]
    have h₀ : k-i = (j-i)+1 := by omega
    have h₁ : k-(i+1) = j-i := by omega
    rw [h₀,h₁]
    rcases L_step (j-i) with h|h <;> omega
  · change ⌊rotationPoint k + d⌋ - ⌊rotationPoint j + d⌋ = 2
    rw [kend, inner j (by omega), show k-j=1 by omega, L_one]
    omega

theorem v_strict_upper (j : ℕ) : v j < cfVal aN := by
  classical
  obtain ⟨d, hd₀, hd₁, hd, h0, hrev, hend, z, hz⟩ := reverse_phase j
  let B := fun n : ℕ => ⌊rotationPoint n + d⌋
  let C := fun n : ℕ => ⌊rotationPoint n⌋
  change B 0 = C 0 at h0
  change ∀ i : ℕ, i < j → B (i+1) - B i = (r (j-i) : ℤ) at hrev
  change B (j+1) - B j = 2 at hend
  have common (n : ℕ) (hn : n ≤ j) (h : ∀ m : ℕ, m ≤ n → B m = C m)
      (i : ℕ) (hi : i<n) : r (j-i) = aN i := by
    have he := hrev i (by omega)
    rw [h i (by omega), h (i+1) (by omega)] at he
    exact_mod_cast he.symm.trans (center_digit i)
  by_cases ex : ∃ n : ℕ, n ≤ j ∧ B n ≠ C n
  · let n := Nat.find ex
    obtain ⟨hn, hn'⟩ : n ≤ j ∧ B n ≠ C n := Nat.find_spec ex
    have hall (m : ℕ) (hm : m<n) : B m = C m := by
      by_contra h
      exact (Nat.find_min ex hm) ⟨by omega, h⟩
    have hn0 : 0<n := Nat.pos_of_ne_zero (fun hzero => hn' (by rw [hzero]; exact h0))
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
    have hi' : i<j := by omega
    have he := hrev i hi'
    have ce : C (i+1) - C i = (aN i : ℤ) := center_digit i
    have same := hall i (by omega)
    apply v_lt_cfVal_of_mismatch j i hi' (common i (by omega) (fun _ hm => hall _ (by omega)))
    rcases first_shift_floor_parity d n hn0 hd₀ hd₁ hall hn' with h|h
    · obtain ⟨_,hp,heq⟩ := h
      change B n = C n + 1 at heq
      rw [hi] at hp heq
      have hh : (r (j-i) : ℤ) = (aN i : ℤ)+1 := by linarith only [heq, he, ce, same]
      exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨_,hp,heq⟩ := h
      change B n = C n - 1 at heq
      rw [hi] at hp heq
      have hh : (r (j-i) : ℤ) = (aN i : ℤ)-1 := by linarith only [heq, he, ce, same]
      exact Or.inl ⟨by omega, by omega⟩
  · have hall (m : ℕ) (hm : m ≤ j) : B m = C m := by
      by_contra h
      exact ex ⟨m, hm, h⟩
    apply v_lt_cfVal_of_terminal j (common j le_rfl hall)
    have ce : C (j+1) - C j = (aN j : ℤ) := center_digit j
    have hm := hall j le_rfl
    have ht : ∀ m : ℕ, m<j+1 → B m = C m := fun m hm => hall m (by omega)
    by_cases he : B (j+1) = C (j+1)
    · have hneg : d < 0 := by
        by_contra! h
        have hpos : 0 < d := lt_of_le_of_ne h hd.symm
        have hb : B (j+1) = z := by change ⌊rotationPoint (j+1) + d⌋ = z; rw [hz, Int.floor_intCast]
        have hh := Int.floor_le (rotationPoint (j+1))
        change (C (j+1) : ℝ) ≤ _ at hh
        rw [← he, hb] at hh
        linarith
      have hp := at_boundary_negative_parity d (j+1) (by omega) hd₀ hneg ht z hz
      left
      omega
    · rcases first_shift_floor_parity d (j+1) (by omega) hd₀ hd₁ ht he with h|h
      · obtain ⟨_,hp,hs⟩ := h
        change B (j+1) = C (j+1) + 1 at hs
        right
        omega
      · obtain ⟨_,_,hs⟩ := h
        change B (j+1) = C (j+1) - 1 at hs
        rcases aN_one_or_two j with ha|ha <;> omega

theorem upper_bound : H_upper := fun j => (v_strict_upper j).le

end A006340Infra

theorem OMA.solution : type_of% @OMA.S_oeis_a006340.main :=
  A006340Infra.main_of_upper A006340Infra.upper_bound
