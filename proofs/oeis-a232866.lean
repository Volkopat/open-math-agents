import OMAStatements.S_oeis_a232866

namespace OMA.S_oeis_a232866

open Finset





/-! ### The distance function -/

/-- The number of moves needed to reach z from 0. -/
def d (z : GaussianInt) : ℤ :=
  (if z.re < 0 then -z.re else z.re) + (if z.im < 0 then -z.im else z.im) +
    (if z.im < 0 then 3 else if z.re < 0 then 2 else if 0 < z.im then 1 else 0)

lemma iu_mul_re (x : GaussianInt) : (iu * x).re = -x.im := by simp [iu]
lemma iu_mul_im (x : GaussianInt) : (iu * x).im = x.re := by simp [iu]

lemma d_nonneg (z : GaussianInt) : 0 ≤ d z := by
  unfold d; split_ifs <;> omega

lemma d_add_one (x : GaussianInt) : d (x + 1) ≤ d x + 1 := by
  have h1 : (x + 1).re = x.re + 1 := by simp
  have h2 : (x + 1).im = x.im := by simp
  unfold d
  rw [h1, h2]
  split_ifs <;> omega

lemma d_iu_mul (x : GaussianInt) : d (iu * x) ≤ d x + 1 := by
  unfold d
  rw [iu_mul_re, iu_mul_im]
  split_ifs <;> omega

lemma d_zero_iff (z : GaussianInt) : d z ≤ 0 ↔ z = 0 := by
  constructor
  · intro h
    unfold d at h
    have : z.re = 0 ∧ z.im = 0 := by split_ifs at h <;> omega
    exact Zsqrtd.ext this.1 this.2
  · rintro rfl
    simp [d]

/-- Every z with d(z) = t + 1 has a parent at distance t. -/
lemma d_parent (z : GaussianInt) (t : ℕ) (h : d z = t + 1) :
    d (z - 1) = t ∧ 1 ≤ z.re ∨ d ⟨z.im, -z.re⟩ = t ∧ iu * ⟨z.im, -z.re⟩ = z := by
  have hz : z - 1 = ⟨z.re - 1, z.im⟩ := by ext <;> simp
  rcases lt_or_ge 0 z.re with hre | hre
  · left
    refine ⟨?_, by omega⟩
    rw [hz]
    unfold d at h ⊢
    simp only at h ⊢
    split_ifs at h ⊢ <;> omega
  · right
    refine ⟨?_, ?_⟩
    · unfold d at h ⊢
      simp only at h ⊢
      split_ifs at h ⊢ <;> omega
    · ext <;> simp [iu]

/-! ### The lists -/

/-- The children of x, in order. -/
def ch (x : GaussianInt) : List GaussianInt := [x, x + 1, iu * x]

lemma step_eq (L : List GaussianInt) : step L = (L.flatMap ch).eraseDups := rfl

lemma mem_Lst_succ {t : ℕ} {z : GaussianInt} :
    z ∈ Lst (t + 1) ↔ ∃ x ∈ Lst t, z = x ∨ z = x + 1 ∨ z = iu * x := by
  rw [Lst, step_eq, List.mem_eraseDups, List.mem_flatMap]
  simp [ch, eq_comm]

/-- Membership in the list after t rounds is distance at most t. -/
lemma mem_Lst (t : ℕ) (z : GaussianInt) : z ∈ Lst t ↔ d z ≤ t := by
  induction t generalizing z with
  | zero =>
    simp only [Lst, List.mem_singleton, Nat.cast_zero]
    exact (d_zero_iff z).symm
  | succ t ih =>
    rw [mem_Lst_succ]
    constructor
    · rintro ⟨x, hx, h | h | h⟩
      · rw [h]; have := (ih x).1 hx; push_cast; omega
      · rw [h]; have := (ih x).1 hx; have := d_add_one x; push_cast; omega
      · rw [h]; have := (ih x).1 hx; have := d_iu_mul x; push_cast; omega
    · intro h
      rcases lt_or_ge (d z) (t + 1) with hlt | hge
      · exact ⟨z, (ih z).2 (by omega), Or.inl rfl⟩
      · have heq : d z = t + 1 := by push_cast at h; omega
        rcases d_parent z t heq with ⟨h1, _⟩ | ⟨h1, h2⟩
        · exact ⟨z - 1, (ih _).2 (by omega), Or.inr (Or.inl (by ring))⟩
        · exact ⟨_, (ih _).2 (by omega), Or.inr (Or.inr h2.symm)⟩

/-! ### Generations -/

/-- The t-th generation: the new elements of round t, in order. -/
def gen : ℕ → List GaussianInt
  | 0 => [0]
  | t + 1 => (((gen t).flatMap ch).removeAll (Lst t)).eraseDups

lemma removeAll_congr {xs ys zs : List GaussianInt} (h : ∀ x, x ∈ ys ↔ x ∈ zs) :
    xs.removeAll ys = xs.removeAll zs := by
  unfold List.removeAll
  congr 1
  funext x
  simp [List.elem_eq_mem, h]

/-- Each round appends the next generation. -/
lemma Lst_succ (t : ℕ) : Lst (t + 1) = Lst t ++ gen (t + 1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    have e1 : Lst (t + 1 + 1) = ((Lst (t + 1)).flatMap ch).eraseDups := rfl
    rw [e1, ih, List.flatMap_append, List.eraseDups_append, ← ih]
    have e2 : ((Lst t).flatMap ch).eraseDups = Lst (t + 1) := rfl
    rw [e2]
    congr 1
    show _ = (((gen (t + 1)).flatMap ch).removeAll (Lst (t + 1))).eraseDups
    congr 1
    apply removeAll_congr
    intro x
    rw [← e2, List.mem_eraseDups]

lemma d_nat (n : ℕ) : d (((n : ℤ) : GaussianInt)) = n := by
  unfold d
  simp only [Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  split_ifs <;> omega

lemma gen_sub (t : ℕ) : ∀ z ∈ gen t, z ∈ Lst t := by
  intro z hz
  cases t with
  | zero => exact hz
  | succ t => rw [Lst_succ]; exact List.mem_append_right _ hz

/-- The integer t is the first element of generation t. -/
lemma gen_head (t : ℕ) : ∃ r, gen t = (((t : ℤ) : GaussianInt)) :: r := by
  induction t with
  | zero => exact ⟨[], rfl⟩
  | succ t ih =>
    obtain ⟨r, hr⟩ := ih
    have hmem : ((t : ℤ) : GaussianInt) ∈ Lst t := (mem_Lst t _).2 (by rw [d_nat])
    have hnot : ((t : ℤ) : GaussianInt) + 1 ∉ Lst t := by
      rw [mem_Lst, show ((t : ℤ) : GaussianInt) + 1 = (((t + 1 : ℕ) : ℤ) : GaussianInt) by
        push_cast; ring, d_nat]
      push_cast; omega
    have e : gen (t + 1) = (((gen t).flatMap ch).removeAll (Lst t)).eraseDups := rfl
    rw [e, hr, List.flatMap_cons]
    simp only [ch, List.cons_append, List.removeAll, List.filter_cons, List.elem_eq_mem,
      decide_eq_true_eq, hmem, hnot, not_true_eq_false, not_false_eq_true, decide_true,
      decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true,
      if_true, if_false]
    rw [List.eraseDups_cons]
    exact ⟨_, by
      rw [show (((t + 1 : ℕ) : ℤ) : GaussianInt) = ((t : ℤ) : GaussianInt) + 1 by push_cast; ring]⟩

/-- The position of the integer k + 1 is right after the first k + 1 rounds' worth of list. -/
lemma a_succ_succ (k : ℕ) : a (k + 2) = (Lst k).length + 1 := by
  obtain ⟨r, hr⟩ := gen_head (k + 1)
  have hnot : (((k + 1 : ℕ) : ℤ) : GaussianInt) ∉ Lst k := by
    rw [mem_Lst, d_nat]; push_cast; omega
  unfold a
  rw [show k + 2 - 1 = k + 1 by omega, Lst_succ (k + 1), Lst_succ k, hr,
    List.idxOf_append_of_mem (by simp), List.idxOf_append_of_notMem hnot, List.idxOf_cons_self]

lemma a_one : a 1 = 1 := by decide

lemma eraseDups_nodup : ∀ l : List GaussianInt, l.eraseDups.Nodup
  | [] => by simp
  | x :: l => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨?_, eraseDups_nodup _⟩
    rw [List.mem_eraseDups]
    simp
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

lemma Lst_nodup (t : ℕ) : (Lst t).Nodup := by
  cases t with
  | zero => simp [Lst]
  | succ t => exact eraseDups_nodup _

/-! ### Counting -/

/-- The points at distance at most t, as pairs (re, im). -/
noncomputable def ball (t : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(t : ℤ)) t) ×ˢ (Icc (-(t : ℤ)) t)).filter (fun p => d ⟨p.1, p.2⟩ ≤ t)

/-- The points at distance exactly s. -/
noncomputable def sph (s : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(s : ℤ)) s) ×ˢ (Icc (-(s : ℤ)) s)).filter (fun p => d ⟨p.1, p.2⟩ = s)

lemma abs_le_d (z : GaussianInt) : (z.re ≤ d z ∧ -z.re ≤ d z) ∧ (z.im ≤ d z ∧ -z.im ≤ d z) := by
  unfold d; split_ifs <;> omega

lemma length_Lst (t : ℕ) : (Lst t).length = (ball t).card := by
  rw [← List.toFinset_card_of_nodup (Lst_nodup t)]
  have hinj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) := by
    intro z w h
    simp only [Prod.mk.injEq] at h
    exact Zsqrtd.ext h.1 h.2
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext ⟨x, y⟩
  simp only [Finset.mem_image, List.mem_toFinset, ball, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, rfl, rfl⟩
    rw [mem_Lst] at hz
    have := abs_le_d z
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, hz⟩
  · rintro ⟨_, h⟩
    exact ⟨⟨x, y⟩, (mem_Lst t _).2 h, rfl, rfl⟩

lemma ball_succ (t : ℕ) : ball (t + 1) = ball t ∪ sph (t + 1) := by
  ext ⟨x, y⟩
  simp only [ball, sph, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  have := abs_le_d ⟨x, y⟩
  simp only at this
  push_cast
  constructor
  · rintro ⟨_, h⟩
    rcases lt_or_ge (d ⟨x, y⟩) (t + 1) with h' | h'
    · left; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
    · right; exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩
    · exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, by omega⟩

lemma ball_sph_disjoint (t : ℕ) : Disjoint (ball t) (sph (t + 1)) := by
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [ball, sph, Finset.mem_filter] at h1 h2
  push_cast at h2
  omega

/-- The sphere of radius s >= 4 has 4s - 9 points. -/
lemma card_sph (s : ℕ) (hs : 4 ≤ s) : (sph s).card + 9 = 4 * s := by
  set S : ℤ := (s : ℤ) with hS
  have e : sph s = ({(S, 0)} : Finset (ℤ × ℤ)) ∪
      ((Icc (1 : ℤ) (S - 1)).image (fun b => (S - 1 - b, b)) ∪
      ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)) ∪
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))))) := by
    ext ⟨x, y⟩
    simp only [sph, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_image, Prod.mk.injEq]
    rw [← hS]
    unfold d
    simp only
    constructor
    · rintro ⟨_, h⟩
      rcases lt_or_ge y 0 with hy | hy
      · rcases lt_or_ge x 0 with hx | hx
        · right; right; right; right
          exact ⟨-y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
            by split_ifs at h <;> omega, by ring⟩
        · right; right; right; left
          exact ⟨-y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
            by split_ifs at h <;> omega, by ring⟩
      · rcases lt_or_ge x 0 with hx | hx
        · right; right; left
          exact ⟨y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
            by split_ifs at h <;> omega, rfl⟩
        · rcases lt_or_ge 0 y with hy' | hy'
          · right; left
            exact ⟨y, ⟨by split_ifs at h <;> omega, by split_ifs at h <;> omega⟩,
              by split_ifs at h <;> omega, rfl⟩
          · left
            exact ⟨by split_ifs at h <;> omega, by omega⟩
    · rintro (⟨rfl, rfl⟩ | ⟨b, ⟨h1, h2⟩, rfl, rfl⟩ | ⟨b, ⟨h1, h2⟩, rfl, rfl⟩ |
        ⟨c, ⟨h1, h2⟩, rfl, rfl⟩ | ⟨c, ⟨h1, h2⟩, rfl, rfl⟩) <;>
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩ <;> split_ifs <;> omega
  rw [e]
  have d1 : Disjoint ({(S, 0)} : Finset (ℤ × ℤ))
      ((Icc (1 : ℤ) (S - 1)).image (fun b => (S - 1 - b, b)) ∪
      ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)) ∪
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_singleton, Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rintro _ rfl
    simp only [Prod.mk.injEq]
    omega
  have d2 : Disjoint ((Icc (1 : ℤ) (S - 1)).image (fun b => (S - 1 - b, b)))
      ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)) ∪
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c)))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Prod.mk.injEq]
    omega
  have d3 : Disjoint ((Icc (0 : ℤ) (S - 3)).image (fun b => (b - (S - 2), b)))
      ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)) ∪
      (Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rintro _ ⟨b, hb, rfl⟩
    simp only [Prod.mk.injEq]
    omega
  have d4 : Disjoint ((Icc (1 : ℤ) (S - 3)).image (fun c => (S - 3 - c, -c)))
      ((Icc (1 : ℤ) (S - 4)).image (fun c => (c - (S - 3), -c))) := by
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_Icc]
    rintro _ ⟨c, hc, rfl⟩
    simp only [Prod.mk.injEq]
    omega
  rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2,
    Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d4]
  rw [Finset.card_image_of_injective _ (fun b b' h => by simpa using h),
    Finset.card_image_of_injective _ (fun b b' h => by simpa using h),
    Finset.card_image_of_injective _ (fun c c' h => by simpa using h),
    Finset.card_image_of_injective _ (fun c c' h => by simpa using h)]
  simp only [Int.card_Icc, Finset.card_singleton]
  omega

lemma card_ball (t : ℕ) (ht : 3 ≤ t) : (ball t).card + 7 * t = 2 * t ^ 2 + 11 := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge t 3 with h | h
    · have : t = 2 := by omega
      subst this
      decide
    · rw [ball_succ, Finset.card_union_of_disjoint (ball_sph_disjoint t)]
      have := ih h
      have := card_sph (t + 1) (by omega)
      nlinarith

/-! ### The conjectures -/

theorem closed_form (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = 2 * n ^ 2 + n + 6 := by
  rw [show n + 4 = (n + 2) + 2 by omega, a_succ_succ, length_Lst]
  have := card_ball (n + 2) (by omega)
  nlinarith

lemma a_two : a 2 = 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, a_succ_succ]
  decide

lemma a_three : a 3 = 3 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, a_succ_succ]
  decide

lemma a_four : a 4 = 5 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, a_succ_succ]
  decide

theorem recurrence (n : ℕ) (hn : 8 ≤ n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = (m + 3) + 4 by omega, show m + 8 - 2 = (m + 2) + 4 by omega,
    show m + 8 - 3 = (m + 1) + 4 by omega, show m + 8 = (m + 4) + 4 by omega,
    closed_form _ (by omega), closed_form _ (by omega), closed_form _ (by omega),
    closed_form _ (by omega)]
  push_cast
  ring

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (X - 1) ^ 3 =
    X * (-1 + X - X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have e1 : A * (X - 1) ^ 3 = A * X ^ 3 - A * X ^ 2 * C 3 + A * X ^ 1 * C 3 - A := by
    rw [show (C 3 : ℤ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  have e2 : (X : ℤ⟦X⟧) * (-1 + X - X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6) =
      X ^ 2 - X ^ 1 - X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7 := by ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  have v1 := a_one
  have v2 := a_two
  have v3 := a_three
  have v4 := a_four
  have v5 : a 5 = 9 := closed_form 1 le_rfl
  have v6 : a 6 = 16 := closed_form 2 (by norm_num)
  have v7 : a 7 = 27 := closed_form 3 (by norm_num)
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7]
  · have h := recurrence n hn
    have h1 : ¬ (n = 0) := by omega
    have h2 : ¬ (n - 1 = 0) := by omega
    have h3 : ¬ (n - 2 = 0) := by omega
    have h4 : ¬ (n - 3 = 0) := by omega
    simp only [h1, h2, h3, h4, if_false, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, if_true, show ¬ (n = 2) by omega, show ¬ (n = 1) by omega,
      show ¬ (n = 4) by omega, show ¬ (n = 5) by omega, show ¬ (n = 6) by omega,
      show ¬ (n = 7) by omega]
    rw [h]
    ring

/-- Kimberling's three conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → a (n + 4) = 2 * n ^ 2 + n + 6) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (PowerSeries.X - 1) ^ 3 =
      PowerSeries.X * (-1 + PowerSeries.X - PowerSeries.X ^ 3 - PowerSeries.X ^ 4 -
        PowerSeries.X ^ 5 - PowerSeries.X ^ 6) ∧
    ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨closed_form, gf, recurrence⟩

end OMA.S_oeis_a232866

theorem OMA.solution : type_of% @OMA.S_oeis_a232866.main :=
  OMA.S_oeis_a232866.conjecture
