import OMAStatements.S_oeis_a228213

namespace OMA.S_oeis_a228213

open Finset



/-- Values as integers. -/
def v {n : ℕ} (x : Fin (n + 2) → Fin 4) (i : ℕ) : ℤ := if h : i < n + 2 then ((x ⟨i, h⟩ : ℕ) : ℤ) else 0

lemma v_bounds {n : ℕ} (x : Fin (n + 2) → Fin 4) (i : ℕ) : 0 ≤ v x i ∧ v x i ≤ 3 := by
  unfold v
  split_ifs
  · have := (x ⟨i, by omega⟩).isLt
    constructor <;> omega
  · omega

/-- Equal second differences force a linear difference. -/
lemma linear_of_d2 {n : ℕ} (x y : Fin (n + 2) → Fin 4) (h : d2 n x = d2 n y) :
    ∀ i, i < n + 2 → v y i - v x i = (v y 0 - v x 0) + i * ((v y 1 - v x 1) - (v y 0 - v x 0)) := by
  have step : ∀ i, i < n → (v y (i + 2) - v x (i + 2)) - 2 * (v y (i + 1) - v x (i + 1)) +
      (v y i - v x i) = 0 := by
    intro i hi
    have := congrFun h ⟨i, hi⟩
    simp only [d2] at this
    unfold v
    rw [dif_pos (by omega), dif_pos (by omega), dif_pos (by omega), dif_pos (by omega),
      dif_pos (by omega), dif_pos (by omega)]
    linarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    match i, ih, hi with
    | 0, _, _ => ring
    | 1, _, _ => ring
    | j + 2, ih, hi =>
      have h1 := ih (j + 1) (by omega) (by omega)
      have h0 := ih j (by omega) (by omega)
      have hs := step j (by omega)
      push_cast at h1 h0 ⊢
      linear_combination hs + 2 * h1 - h0

lemma ext_of_v {n : ℕ} (x y : Fin (n + 2) → Fin 4) (h : ∀ i, i < n + 2 → v x i = v y i) : x = y := by
  funext i
  have := h i.1 i.2
  unfold v at this
  rw [dif_pos i.2, dif_pos i.2] at this
  exact Fin.ext (by exact_mod_cast this)

/-- For long arrays the slope vanishes. -/
lemma slope_zero {n : ℕ} (hn : 6 ≤ n) (x y : Fin (n + 2) → Fin 4) (h : d2 n x = d2 n y) :
    ∀ i, i < n + 2 → v y i - v x i = v y 0 - v x 0 := by
  have hl := linear_of_d2 x y h
  set b := (v y 1 - v x 1) - (v y 0 - v x 0) with hb
  have hlast := hl (n + 1) (by omega)
  have b1 := v_bounds x (n + 1)
  have b2 := v_bounds y (n + 1)
  have b3 := v_bounds x 0
  have b4 := v_bounds y 0
  have hb0 : b = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : ((n + 1 : ℕ) : ℤ) * b ≤ -7 := by
        have : (7 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by push_cast; omega
        nlinarith
      push_cast at hlast this
      linarith
    · have : ((n + 1 : ℕ) : ℤ) * b ≥ 7 := by
        have : (7 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by push_cast; omega
        nlinarith
      push_cast at hlast this
      linarith
  intro i hi
  rw [hl i hi, hb0, mul_zero, add_zero]

/-- Arrays with some entry 0. -/
def Z (n : ℕ) : Finset (Fin (n + 2) → Fin 4) := Finset.univ.filter (fun x => ∃ k, x k = 0)

/-- Shift an array down by its minimum. -/
def shift {n : ℕ} (x : Fin (n + 2) → Fin 4) : Fin (n + 2) → Fin 4 :=
  fun i => ⟨(x i : ℕ) - (Finset.univ.image (fun j => (x j : ℕ))).min' (by simp), by omega⟩

lemma shift_mem {n : ℕ} (x : Fin (n + 2) → Fin 4) : shift x ∈ Z n := by
  simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image (fun j => (x j : ℕ))) (by simp))
  refine ⟨k, Fin.ext ?_⟩
  simp only [shift, Fin.val_zero]
  omega

lemma d2_shift {n : ℕ} (x : Fin (n + 2) → Fin 4) : d2 n (shift x) = d2 n x := by
  funext i
  simp only [d2, shift]
  have hle : ∀ j, (Finset.univ.image (fun j => (x j : ℕ))).min' (by simp) ≤ (x j : ℕ) :=
    fun j => Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have h1 := hle ⟨i.1 + 2, by omega⟩
  have h2 := hle ⟨i.1 + 1, by omega⟩
  have h3 := hle ⟨i.1, by omega⟩
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  ring

lemma image_eq (n : ℕ) : Finset.univ.image (d2 n) = (Z n).image (d2 n) := by
  ext d
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨shift x, shift_mem x, d2_shift x⟩
  · rintro ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

lemma inj_on (n : ℕ) (hn : 6 ≤ n) : Set.InjOn (d2 n) (Z n : Set (Fin (n + 2) → Fin 4)) := by
  intro x hx y hy h
  simp only [Z, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
  have hc := slope_zero hn x y h
  -- the constant difference c = v y 0 - v x 0 vanishes since both minima are 0
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  have hvx : v x kx.1 = 0 := by unfold v; rw [dif_pos kx.2, hkx]; rfl
  have hvy : v y ky.1 = 0 := by unfold v; rw [dif_pos ky.2, hky]; rfl
  have c1 := hc kx.1 kx.2
  have c2 := hc ky.1 ky.2
  have b1 := v_bounds y kx.1
  have b2 := v_bounds x ky.1
  have hzero : v y 0 - v x 0 = 0 := by
    rw [hvx] at c1
    rw [hvy] at c2
    linarith
  apply ext_of_v
  intro i hi
  have := hc i hi
  rw [hzero] at this
  linarith

lemma card_Z (n : ℕ) : (Z n).card = 4 ^ (n + 2) - 3 ^ (n + 2) := by
  have hcompl : (Finset.univ.filter (fun x : Fin (n + 2) → Fin 4 => ¬ ∃ k, x k = 0)).card =
      3 ^ (n + 2) := by
    have : (Finset.univ.filter (fun x : Fin (n + 2) → Fin 4 => ¬ ∃ k, x k = 0)) =
        Fintype.piFinset (fun _ => (Finset.univ.filter (fun c : Fin 4 => c ≠ 0))) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, not_exists]
    rw [this, Fintype.card_piFinset]
    simp [Finset.prod_const]
    rfl
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 2) → Fin 4))) (fun x => ∃ k, x k = 0)
  rw [hcompl, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at htot
  unfold Z
  omega

/-- Barker's closed form. -/
theorem closed_form (n : ℕ) (hn : 5 < n) : a n = 4 ^ (2 + n) - 3 ^ (2 + n) := by
  unfold a
  rw [image_eq, Finset.card_image_of_injOn (inj_on n (by omega)), card_Z, Nat.add_comm 2 n]

/-! ### Small n: canonical representatives when slopes 0 and +-1 are possible (n >= 3) -/

/-- x has a slope-one partner with a zero entry: some a with x + a + i in 0..3 having a 0. -/
def partner (n : ℕ) (x : Fin (n + 2) → Fin 4) : Prop :=
  ∃ a : Fin 7, (∀ i : Fin (n + 2), 0 ≤ ((x i : ℕ) : ℤ) + ((a : ℕ) - 3 : ℤ) + (i : ℕ) ∧
    ((x i : ℕ) : ℤ) + ((a : ℕ) - 3 : ℤ) + (i : ℕ) ≤ 3) ∧
    ∃ k : Fin (n + 2), ((x k : ℕ) : ℤ) + ((a : ℕ) - 3 : ℤ) + (k : ℕ) = 0

instance (n : ℕ) : DecidablePred (partner n) := fun x => by unfold partner; infer_instance

/-- Canonical arrays: a zero entry and no slope-one partner. -/
def canon (n : ℕ) (x : Fin (n + 2) → Fin 4) : Prop := (∃ k, x k = 0) ∧ ¬ partner n x

instance (n : ℕ) : DecidablePred (canon n) := fun x => by unfold canon; infer_instance

lemma v_fin {n : ℕ} (x : Fin (n + 2) → Fin 4) (i : Fin (n + 2)) : v x i.1 = ((x i : ℕ) : ℤ) := by
  unfold v; rw [dif_pos i.2]

/-- Adding a linear function a + i. -/
def addLin {n : ℕ} (x : Fin (n + 2) → Fin 4) (a : ℤ)
    (h : ∀ i : Fin (n + 2), 0 ≤ ((x i : ℕ) : ℤ) + a + (i : ℕ) ∧ ((x i : ℕ) : ℤ) + a + (i : ℕ) ≤ 3) :
    Fin (n + 2) → Fin 4 :=
  fun i => ⟨(((x i : ℕ) : ℤ) + a + (i : ℕ)).toNat, by have := h i; omega⟩

lemma addLin_val {n : ℕ} (x : Fin (n + 2) → Fin 4) (a : ℤ) (h) (i : Fin (n + 2)) :
    (((addLin x a h i : Fin 4) : ℕ) : ℤ) = ((x i : ℕ) : ℤ) + a + (i : ℕ) := by
  simp only [addLin]
  have := h i
  omega

lemma d2_addLin {n : ℕ} (x : Fin (n + 2) → Fin 4) (a : ℤ) (h) : d2 n (addLin x a h) = d2 n x := by
  funext i
  simp only [d2]
  rw [addLin_val, addLin_val, addLin_val]
  push_cast
  ring

lemma slope_small {n : ℕ} (hn : 3 ≤ n) (x y : Fin (n + 2) → Fin 4) (h : d2 n x = d2 n y) :
    let b := (v y 1 - v x 1) - (v y 0 - v x 0); b = -1 ∨ b = 0 ∨ b = 1 := by
  intro b
  have hl := linear_of_d2 x y h
  have hlast := hl (n + 1) (by omega)
  have b1 := v_bounds x (n + 1)
  have b2 := v_bounds y (n + 1)
  have b3 := v_bounds x 0
  have b4 := v_bounds y 0
  have h4 : (4 : ℤ) ≤ (n : ℤ) + 1 := by omega
  push_cast at hlast
  have hp : ((n : ℤ) + 1) * b ≤ 6 ∧ -6 ≤ ((n : ℤ) + 1) * b := by
    constructor <;> nlinarith
  rcases (show b ≤ -2 ∨ b = -1 ∨ b = 0 ∨ b = 1 ∨ 2 ≤ b by omega) with h | h | h | h | h
  · nlinarith
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · nlinarith

lemma canon_inj (n : ℕ) (hn : 3 ≤ n) :
    Set.InjOn (d2 n) (Finset.univ.filter (canon n) : Set (Fin (n + 2) → Fin 4)) := by
  intro x hx y hy h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, canon] at hx hy
  obtain ⟨⟨kx, hkx⟩, hpx⟩ := hx
  obtain ⟨⟨ky, hky⟩, hpy⟩ := hy
  have hl := linear_of_d2 x y h
  have hs := slope_small hn x y h
  set c := v y 0 - v x 0 with hc
  set b := (v y 1 - v x 1) - (v y 0 - v x 0) with hb
  have cb : -3 ≤ c ∧ c ≤ 3 := by
    have := v_bounds x 0; have := v_bounds y 0; constructor <;> linarith
  have hvx : v x kx.1 = 0 := by rw [v_fin, hkx]; rfl
  have hvy : v y ky.1 = 0 := by rw [v_fin, hky]; rfl
  rcases hs with hb1 | hb0 | hb1
  · -- slope -1: y has a partner
    exfalso
    apply hpy
    have hcn : 0 ≤ 3 - c ∧ 3 - c < 7 := by constructor <;> linarith
    refine ⟨⟨(3 - c).toNat, by omega⟩, fun i => ?_, kx, ?_⟩
    · have e := hl i.1 i.2
      rw [v_fin, v_fin, hb1] at e
      have := (x i).isLt
      have := (y i).isLt
      simp only
      constructor <;> push_cast at e ⊢ <;> omega
    · have e := hl kx.1 kx.2
      rw [hb1, hvx] at e
      have := v_fin y kx
      simp only
      push_cast at e ⊢
      omega
  · -- slope 0: equal
    apply ext_of_v
    intro i hi
    have e := hl i hi
    rw [hb0, mul_zero, add_zero] at e
    have ex := hl kx.1 kx.2
    have ey := hl ky.1 ky.2
    rw [hb0, mul_zero, add_zero, hvx] at ex
    rw [hb0, mul_zero, add_zero, hvy] at ey
    have := v_bounds y kx.1
    have := v_bounds x ky.1
    have hc0 : c = 0 := by linarith
    linarith
  · -- slope 1: x has a partner
    exfalso
    apply hpx
    have hcn : 0 ≤ c + 3 ∧ c + 3 < 7 := by constructor <;> linarith
    refine ⟨⟨(c + 3).toNat, by omega⟩, fun i => ?_, ky, ?_⟩
    · have e := hl i.1 i.2
      rw [v_fin, v_fin, hb1] at e
      have := (y i).isLt
      have := (x i).isLt
      simp only
      constructor <;> push_cast at e ⊢ <;> omega
    · have e := hl ky.1 ky.2
      rw [hb1, hvy] at e
      have := v_fin x ky
      simp only
      push_cast at e ⊢
      omega

lemma canon_surj (n : ℕ) (hn : 3 ≤ n) :
    Finset.univ.image (d2 n) = (Finset.univ.filter (canon n)).image (d2 n) := by
  ext d
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨x, rfl⟩
    have hz := shift_mem x
    simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    by_cases hp : partner n (shift x)
    · obtain ⟨a, hrange, k, hk⟩ := hp
      refine ⟨addLin (shift x) (((a : ℕ) : ℤ) - 3) hrange, ⟨⟨k, Fin.ext ?_⟩, ?_⟩,
        by rw [d2_addLin, d2_shift]⟩
      · have := addLin_val (shift x) (((a : ℕ) : ℤ) - 3) hrange k
        rw [hk] at this
        simp only [Fin.val_zero]
        omega
      · rintro ⟨a', hrange', k', hk'⟩
        have e0 := hrange' ⟨0, by omega⟩
        have e1 := hrange' ⟨n + 1, by omega⟩
        rw [addLin_val] at e0 e1
        have := (shift x ⟨0, by omega⟩).isLt
        have := (shift x ⟨n + 1, by omega⟩).isLt
        have := a.isLt
        have := a'.isLt
        simp only at e0 e1
        push_cast at e0 e1
        omega
    · exact ⟨shift x, ⟨hz, hp⟩, d2_shift x⟩
  · rintro ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

lemma a_eq_canon (n : ℕ) (hn : 3 ≤ n) : a n = (Finset.univ.filter (canon n)).card := by
  unfold a
  rw [canon_surj n hn, Finset.card_image_of_injOn (canon_inj n hn)]

theorem a_one : a 1 = 13 := by decide +kernel

theorem a_two : a 2 = 103 := by decide +kernel

/-- Counting arrays through their base-4 codes, which the kernel enumerates cheaply. -/
lemma card_nat (L : ℕ) (P : (Fin L → Fin 4) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ((Finset.univ : Finset (Fin (4 ^ L))).filter (fun m => P (finFunctionFinEquiv.symm m))).card := by
  refine Finset.card_bij (fun x _ => finFunctionFinEquiv x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    simpa using hx
  · intro x _ y _ h
    exact finFunctionFinEquiv.injective h
  · intro m hm
    refine ⟨finFunctionFinEquiv.symm m, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact hm

/-- The base-4 digit i of m. -/
def dig (m i : ℕ) : ℕ := m / 4 ^ i % 4

/-- `canon` on base-4 codes, with natural-number arithmetic only (a is shifted by 3). -/
def okNat (L m : ℕ) : Bool :=
  (List.range L).any (fun k => dig m k == 0) &&
    !((List.range 7).any (fun a => (List.range L).all (fun i =>
        decide (3 ≤ dig m i + a + i) && decide (dig m i + a + i ≤ 6)) &&
      (List.range L).any (fun k => dig m k + a + k == 3)))

lemma canon_iff_okNat (n m : ℕ) (hm : m < 4 ^ (n + 2)) :
    canon n (finFunctionFinEquiv.symm ⟨m, hm⟩) ↔ okNat (n + 2) m = true := by
  have hx : ∀ i : Fin (n + 2), ((finFunctionFinEquiv.symm ⟨m, hm⟩ i : Fin 4) : ℕ) = dig m i := by
    intro i
    rw [finFunctionFinEquiv_symm_apply_val]
    rfl
  unfold canon partner okNat
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, List.all_eq_true,
    List.mem_range, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true, List.any_eq_false]
  constructor
  · rintro ⟨⟨k, hk⟩, hp⟩
    refine ⟨⟨k.1, k.2, ?_⟩, ?_⟩
    · rw [← hx k, hk]; rfl
    · intro a ha ⟨hall, k', hk', hk'eq⟩
      apply hp
      refine ⟨⟨a, ha⟩, fun i => ?_, ⟨k', hk'⟩, ?_⟩
      · have := hall i.1 i.2
        rw [hx i]
        simp only
        constructor <;> omega
      · rw [hx ⟨k', hk'⟩]
        simp only
        omega
  · rintro ⟨⟨k, hk, hk0⟩, hp⟩
    refine ⟨⟨⟨k, hk⟩, Fin.ext ?_⟩, ?_⟩
    · rw [hx ⟨k, hk⟩]; exact hk0
    · rintro ⟨a, hall, k', hk'⟩
      refine hp a.1 a.2 ⟨fun i hi => ?_, k'.1, k'.2, ?_⟩
      · have := hall ⟨i, hi⟩
        rw [hx ⟨i, hi⟩] at this
        simp only at this
        constructor <;> omega
      · rw [hx k'] at hk'
        omega

lemma card_canon_okNat (n : ℕ) :
    (Finset.univ.filter (canon n)).card =
      ((Finset.range (4 ^ (n + 2))).filter (fun m => okNat (n + 2) m = true)).card := by
  rw [card_nat]
  refine Finset.card_bij (fun m _ => m.1) ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hm ⊢
    exact ⟨m.2, (canon_iff_okNat n m.1 m.2).mp hm⟩
  · intro x _ y _ h
    exact Fin.ext h
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨⟨m, hm.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (canon_iff_okNat n m hm.1).mpr hm.2

/-- Splitting a count over an interval. -/
lemma card_split (p : ℕ → Prop) [DecidablePred p] (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    ((Finset.Ico a c).filter p).card =
      ((Finset.Ico a b).filter p).card + ((Finset.Ico b c).filter p).card := by
  rw [← Finset.Ico_union_Ico_eq_Ico hab hbc, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive a b c))]

/-- One more block of length 1024 (each block is a separate small kernel computation). -/
lemma step_sum (p : ℕ → Prop) [DecidablePred p] (j v c : ℕ)
    (hprev : ((Finset.Ico 0 (j * 1024)).filter p).card = v)
    (hchunk : ((Finset.Ico (j * 1024) (j * 1024 + 1024)).filter p).card = c) :
    ((Finset.Ico 0 (j * 1024 + 1024)).filter p).card = v + c := by
  rw [card_split p 0 (j * 1024) (j * 1024 + 1024) (Nat.zero_le _) (Nat.le_add_right _ _),
    hprev, hchunk]

lemma c3 : ((Finset.Ico (0 * 1024) (0 * 1024 + 1024)).filter (fun m => okNat (3 + 2) m = true)).card = 625 := by
  decide +kernel
lemma c4_0 : ((Finset.Ico (0 * 1024) (0 * 1024 + 1024)).filter (fun m => okNat (4 + 2) m = true)).card = 844 := by
  decide +kernel
lemma c4_1 : ((Finset.Ico (1 * 1024) (1 * 1024 + 1024)).filter (fun m => okNat (4 + 2) m = true)).card = 745 := by
  decide +kernel
lemma c4_2 : ((Finset.Ico (2 * 1024) (2 * 1024 + 1024)).filter (fun m => okNat (4 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c4_3 : ((Finset.Ico (3 * 1024) (3 * 1024 + 1024)).filter (fun m => okNat (4 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_0 : ((Finset.Ico (0 * 1024) (0 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 952 := by
  decide +kernel
lemma c5_1 : ((Finset.Ico (1 * 1024) (1 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 952 := by
  decide +kernel
lemma c5_2 : ((Finset.Ico (2 * 1024) (2 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 1024 := by
  decide +kernel
lemma c5_3 : ((Finset.Ico (3 * 1024) (3 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 1024 := by
  decide +kernel
lemma c5_4 : ((Finset.Ico (4 * 1024) (4 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 1024 := by
  decide +kernel
lemma c5_5 : ((Finset.Ico (5 * 1024) (5 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_6 : ((Finset.Ico (6 * 1024) (6 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_7 : ((Finset.Ico (7 * 1024) (7 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_8 : ((Finset.Ico (8 * 1024) (8 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 1024 := by
  decide +kernel
lemma c5_9 : ((Finset.Ico (9 * 1024) (9 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_10 : ((Finset.Ico (10 * 1024) (10 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_11 : ((Finset.Ico (11 * 1024) (11 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_12 : ((Finset.Ico (12 * 1024) (12 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 1024 := by
  decide +kernel
lemma c5_13 : ((Finset.Ico (13 * 1024) (13 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_14 : ((Finset.Ico (14 * 1024) (14 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel
lemma c5_15 : ((Finset.Ico (15 * 1024) (15 * 1024 + 1024)).filter (fun m => okNat (5 + 2) m = true)).card = 781 := by
  decide +kernel

lemma range_Ico (p : ℕ → Prop) [DecidablePred p] (N M : ℕ) (h : N = M) :
    ((Finset.range N).filter p).card = ((Finset.Ico 0 M).filter p).card := by
  rw [Finset.range_eq_Ico, h]

theorem a_three : a 3 = 625 := by
  have t := range_Ico (fun m => okNat (3 + 2) m = true) (4 ^ (3 + 2)) (0 * 1024 + 1024) (by norm_num)
  exact ((a_eq_canon 3 le_rfl).trans (card_canon_okNat 3)).trans (t.trans c3)

theorem a_four : a 4 = 3151 := by
  have t1 := step_sum _ 1 _ _ c4_0 c4_1
  have t2 := step_sum _ 2 _ _ t1 c4_2
  have t3 := step_sum _ 3 _ _ t2 c4_3
  have t := range_Ico (fun m => okNat (4 + 2) m = true) (4 ^ (4 + 2)) (3 * 1024 + 1024) (by norm_num)
  exact ((a_eq_canon 4 (by norm_num)).trans (card_canon_okNat 4)).trans (t.trans t3)

theorem a_five : a 5 = 14053 := by
  have t1 := step_sum _ 1 _ _ c5_0 c5_1
  have t2 := step_sum _ 2 _ _ t1 c5_2
  have t3 := step_sum _ 3 _ _ t2 c5_3
  have t4 := step_sum _ 4 _ _ t3 c5_4
  have t5 := step_sum _ 5 _ _ t4 c5_5
  have t6 := step_sum _ 6 _ _ t5 c5_6
  have t7 := step_sum _ 7 _ _ t6 c5_7
  have t8 := step_sum _ 8 _ _ t7 c5_8
  have t9 := step_sum _ 9 _ _ t8 c5_9
  have t10 := step_sum _ 10 _ _ t9 c5_10
  have t11 := step_sum _ 11 _ _ t10 c5_11
  have t12 := step_sum _ 12 _ _ t11 c5_12
  have t13 := step_sum _ 13 _ _ t12 c5_13
  have t14 := step_sum _ 14 _ _ t13 c5_14
  have t15 := step_sum _ 15 _ _ t14 c5_15
  have t := range_Ico (fun m => okNat (5 + 2) m = true) (4 ^ (5 + 2)) (15 * 1024 + 1024) (by norm_num)
  exact ((a_eq_canon 5 (by norm_num)).trans (card_canon_okNat 5)).trans (t.trans t15)

/-! ### The generating function -/

open PowerSeries




lemma den_eq : den = 1 - C (7 : ℚ) * X ^ 1 + C (12 : ℚ) * X ^ 2 := by
  unfold den
  rw [show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (12 : ℚ) : ℚ⟦X⟧) = 12 from map_ofNat C 12]
  ring

lemma num_eq : num = C (13 : ℚ) * X ^ 1 + C (12 : ℚ) * X ^ 2 + C (60 : ℚ) * X ^ 3 +
    C (12 : ℚ) * X ^ 4 - C (504 : ℚ) * X ^ 5 - C (1584 : ℚ) * X ^ 6 - C (1728 : ℚ) * X ^ 7 := by
  unfold num
  rw [show (C (13 : ℚ) : ℚ⟦X⟧) = 13 from map_ofNat C 13, show (C (12 : ℚ) : ℚ⟦X⟧) = 12 from map_ofNat C 12,
    show (C (60 : ℚ) : ℚ⟦X⟧) = 60 from map_ofNat C 60, show (C (504 : ℚ) : ℚ⟦X⟧) = 504 from map_ofNat C 504,
    show (C (1584 : ℚ) : ℚ⟦X⟧) = 1584 from map_ofNat C 1584,
    show (C (1728 : ℚ) : ℚ⟦X⟧) = 1728 from map_ofNat C 1728]
  ring

lemma a_cast (n : ℕ) (hn : 5 < n) : (a n : ℚ) = 4 ^ (n + 2) - 3 ^ (n + 2) := by
  rw [closed_form n hn, Nat.add_comm 2 n, Nat.cast_sub (Nat.pow_le_pow_left (by norm_num) _)]
  push_cast; ring

lemma coeffA (n : ℕ) : coeff n A = if n = 0 then 0 else (a n : ℚ) := by
  rw [A, coeff_mk]

lemma cA0 : coeff 0 A = 0 := by rw [coeffA, if_pos rfl]
lemma cA1 : coeff 1 A = 13 := by rw [coeffA, if_neg (by norm_num), a_one]; norm_num
lemma cA2 : coeff 2 A = 103 := by rw [coeffA, if_neg (by norm_num), a_two]; norm_num
lemma cA3 : coeff 3 A = 625 := by rw [coeffA, if_neg (by norm_num), a_three]; norm_num
lemma cA4 : coeff 4 A = 3151 := by rw [coeffA, if_neg (by norm_num), a_four]; norm_num
lemma cA5 : coeff 5 A = 14053 := by rw [coeffA, if_neg (by norm_num), a_five]; norm_num
lemma cA6 : coeff 6 A = 58975 := by
  rw [coeffA, if_neg (by norm_num), a_cast 6 (by norm_num)]; norm_num
lemma cA7 : coeff 7 A = 242461 := by
  rw [coeffA, if_neg (by norm_num), a_cast 7 (by norm_num)]; norm_num

lemma mul_den : A * den = num := by
  rw [den_eq, num_eq]
  ext n
  have e : A * (1 - C (7 : ℚ) * X ^ 1 + C (12 : ℚ) * X ^ 2) =
      A - C (7 : ℚ) * (A * X ^ 1) + C (12 : ℚ) * (A * X ^ 2) := by ring
  rw [e]
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow']
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n
    all_goals norm_num [cA0, cA1, cA2, cA3, cA4, cA5, cA6, cA7, coeff_C]
  · simp only [coeffA]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [coeff_C, show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega,
      show 3 ≤ m + 8 by omega, show 4 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega,
      show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega, if_true,
      show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
      show m + 8 - 7 = m + 1 by omega, show ¬ (m + 8 = 0) by omega, show ¬ (m + 7 = 0) by omega,
      show ¬ (m + 6 = 0) by omega, show ¬ (m + 5 = 0) by omega, show ¬ (m + 4 = 0) by omega,
      show ¬ (m + 3 = 0) by omega, show ¬ (m + 2 = 0) by omega, show ¬ (m + 1 = 0) by omega,
      if_false]
    rw [a_cast (m + 8) (by omega), a_cast (m + 7) (by omega), a_cast (m + 6) (by omega)]
    ring

/-- Barker's two conjectures. -/
theorem conjecture : A = num * den⁻¹ ∧ ∀ n : ℕ, 5 < n → a n = 4 ^ (2 + n) - 3 ^ (2 + n) := by
  refine ⟨?_, closed_form⟩
  have h : constantCoeff den ≠ 0 := by rw [den_eq]; simp
  rw [← mul_den, mul_assoc, PowerSeries.mul_inv_cancel _ h, mul_one]

end OMA.S_oeis_a228213

theorem OMA.solution : type_of% @OMA.S_oeis_a228213.main :=
  OMA.S_oeis_a228213.conjecture
