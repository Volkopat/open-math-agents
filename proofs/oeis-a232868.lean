import OMAStatements.S_oeis_a232868

namespace OMA.S_oeis_a232868

open Finset






/-! ### The distance function -/

/-- The number of moves needed to reach z from 0. -/
def d (z : GaussianInt) : ℤ :=
  (if z.re < 0 then -z.re else z.re) + (if z.im < 0 then -z.im else z.im) +
    (if z.im < 0 then 3 else if z.re < 0 then 2 else if 0 < z.im then 1 else 0)

lemma iu_mul_re (x : GaussianInt) : (iu * x).re = -x.im := by simp [iu]
lemma iu_mul_im (x : GaussianInt) : (iu * x).im = x.re := by simp [iu]

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

lemma d_iu_nat (k : ℕ) (hk : 1 ≤ k) : d (iu * ((k : ℤ) : GaussianInt)) = k + 1 := by
  unfold d
  rw [iu_mul_re, iu_mul_im]
  simp only [Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  split_ifs <;> omega

lemma d_iu_nat_add_one (k : ℕ) (hk : 1 ≤ k) :
    d (iu * ((k : ℤ) : GaussianInt) + 1) = k + 2 := by
  have h1 : (iu * ((k : ℤ) : GaussianInt) + 1).re = 1 := by simp [iu]
  have h2 : (iu * ((k : ℤ) : GaussianInt) + 1).im = k := by simp [iu]
  unfold d
  rw [h1, h2]
  split_ifs <;> omega

lemma iu_iu (k : ℕ) : iu * (iu * ((k : ℤ) : GaussianInt)) = -((k : ℤ) : GaussianInt) := by
  ext <;> simp [iu]

lemma d_neg_nat (k : ℕ) (hk : 1 ≤ k) : d (-((k : ℤ) : GaussianInt)) = k + 2 := by
  unfold d
  simp only [Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  split_ifs <;> omega

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
      hmem, hnot, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      if_true, if_false]
    rw [List.eraseDups_cons]
    exact ⟨_, by
      rw [show (((t + 1 : ℕ) : ℤ) : GaussianInt) = ((t : ℤ) : GaussianInt) + 1 by push_cast; ring]⟩

/-- Generation k + 1 begins with k + 1 and i k (for k >= 1); then generation k + 2 begins with
k + 2, i (k + 1), i k + 1 and -k. -/
lemma gen_four (k : ℕ) (hk : 1 ≤ k) :
    (∃ r, gen (k + 1) = (((k + 1 : ℕ) : ℤ) : GaussianInt) :: (iu * ((k : ℤ) : GaussianInt)) :: r) ∧
    ∃ r, gen (k + 2) = (((k + 2 : ℕ) : ℤ) : GaussianInt) ::
      (iu * (((k + 1 : ℕ) : ℤ) : GaussianInt)) :: (iu * ((k : ℤ) : GaussianInt) + 1) ::
      (-((k : ℤ) : GaussianInt)) :: r := by
  induction k with
  | zero => omega
  | succ k ih =>
    have P : ∃ r, gen (k + 1 + 1) =
        (((k + 1 + 1 : ℕ) : ℤ) : GaussianInt) :: (iu * (((k + 1 : ℕ) : ℤ) : GaussianInt)) :: r := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨[], by decide⟩
      · obtain ⟨_, r, hr⟩ := ih hk0
        exact ⟨_, hr⟩
    refine ⟨P, ?_⟩
    obtain ⟨r, hr⟩ := P
    set m : ℕ := k + 1 with hm
    have hm1 : 1 ≤ m := by omega
    have e : gen (m + 2) = (((gen (m + 1)).flatMap ch).removeAll (Lst (m + 1))).eraseDups := rfl
    have x1 : (((m + 1 : ℕ) : ℤ) : GaussianInt) ∈ Lst (m + 1) := by
      rw [mem_Lst, d_nat]
    have x2 : (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 ∉ Lst (m + 1) := by
      rw [mem_Lst, show (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 = (((m + 2 : ℕ) : ℤ) : GaussianInt) by
        push_cast; ring, d_nat]
      push_cast; omega
    have x3 : iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) ∉ Lst (m + 1) := by
      rw [mem_Lst, d_iu_nat _ (by omega)]
      push_cast; omega
    have x4 : iu * ((m : ℤ) : GaussianInt) ∈ Lst (m + 1) := by
      rw [mem_Lst, d_iu_nat _ hm1]
      push_cast; omega
    have x5 : iu * ((m : ℤ) : GaussianInt) + 1 ∉ Lst (m + 1) := by
      rw [mem_Lst, d_iu_nat_add_one _ hm1]
      push_cast; omega
    have x6 : iu * (iu * ((m : ℤ) : GaussianInt)) ∉ Lst (m + 1) := by
      rw [mem_Lst, iu_iu, d_neg_nat _ hm1]
      push_cast; omega
    have n12 : iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) ≠ (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.im h; simp [iu] at this <;> omega
    have n13 : iu * ((m : ℤ) : GaussianInt) + 1 ≠ (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.im h; simp [iu] at this <;> omega
    have n14 : iu * (iu * ((m : ℤ) : GaussianInt)) ≠ (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.re h; simp [iu] at this <;> omega
    have n23 : iu * ((m : ℤ) : GaussianInt) + 1 ≠ iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) := by
      intro h; have := congrArg Zsqrtd.re h; simp [iu] at this <;> omega
    have n24 : iu * (iu * ((m : ℤ) : GaussianInt)) ≠ iu * (((m + 1 : ℕ) : ℤ) : GaussianInt) := by
      intro h; have := congrArg Zsqrtd.im h; simp [iu] at this <;> omega
    have n34 : iu * (iu * ((m : ℤ) : GaussianInt)) ≠ iu * ((m : ℤ) : GaussianInt) + 1 := by
      intro h; have := congrArg Zsqrtd.re h; simp [iu] at this <;> omega
    have b12 := beq_false_of_ne n12
    have b13 := beq_false_of_ne n13
    have b14 := beq_false_of_ne n14
    have b23 := beq_false_of_ne n23
    have b24 := beq_false_of_ne n24
    have b34 := beq_false_of_ne n34
    rw [e, hr, List.flatMap_cons, List.flatMap_cons]
    simp only [ch, List.cons_append, List.nil_append, List.removeAll, List.filter_cons,
      List.elem_eq_mem, x1, x2, x3, x4, x5, x6, decide_true, decide_false, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, if_true, if_false, ite_true, ite_false]
    rw [List.eraseDups_cons]
    simp only [List.filter_cons, b12, b13, b14, Bool.not_false, if_true, ite_true]
    rw [List.eraseDups_cons]
    simp only [List.filter_cons, b23, b24, Bool.not_false, if_true, ite_true]
    rw [List.eraseDups_cons]
    simp only [List.filter_cons, b34, Bool.not_false, if_true, ite_true]
    rw [List.eraseDups_cons, iu_iu]
    exact ⟨_, by
      rw [show (((m + 2 : ℕ) : ℤ) : GaussianInt) = (((m + 1 : ℕ) : ℤ) : GaussianInt) + 1 by
        push_cast; ring]⟩

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

/-! ### Positions of the integers -/

lemma Lst_prefix (t k : ℕ) : Lst t <+: Lst (t + k) := by
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih =>
    rw [← add_assoc, Lst_succ]
    exact ih.trans (List.prefix_append _ _)

lemma len_formula (t : ℕ) (ht : 3 ≤ t) : (Lst t).length + 7 * t = 2 * t ^ 2 + 11 := by
  rw [length_Lst]; exact card_ball t ht

lemma len0 : (Lst 0).length = 1 := by decide
lemma len1 : (Lst 1).length = 2 := by decide
lemma len2 : (Lst 2).length = 4 := by decide

lemma len_ge (t : ℕ) : t + 1 ≤ (Lst t).length := by
  rcases Nat.lt_or_ge t 3 with h | h
  · interval_cases t <;> simp [len0, len1, len2]
  · have := len_formula t h
    nlinarith

/-- The element at index i of the list after t rounds is the element at position i + 1 of S. -/
lemma elt_of {t i : ℕ} {z : GaussianInt} (hz : (Lst t)[i]? = some z) (hti : t ≤ i + 1) :
    elt (i + 1) = z := by
  obtain ⟨l, hl⟩ := Lst_prefix t (i + 1 - t)
  rw [show t + (i + 1 - t) = i + 1 by omega] at hl
  have hlt : i < (Lst t).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hz
    exact absurd hz (by simp)
  unfold elt
  rw [show i + 1 - 1 = i by omega, List.getD_eq_getElem?_getD, ← hl,
    List.getElem?_append_left hlt, hz]
  rfl

/-- Index of the integer k + 1: right after the first k + 1 rounds' worth of list. -/
lemma idx_nat (k : ℕ) :
    (Lst (k + 1)).idxOf (((k + 1 : ℕ) : ℤ) : GaussianInt) = (Lst k).length := by
  obtain ⟨r, hr⟩ := gen_head (k + 1)
  have hnot : (((k + 1 : ℕ) : ℤ) : GaussianInt) ∉ Lst k := by
    rw [mem_Lst, d_nat]; push_cast; omega
  rw [Lst_succ, hr, List.idxOf_append_of_notMem hnot, List.idxOf_cons_self]
  simp

/-- Index of -k, k >= 1: three past the first k + 2 rounds' worth of list. -/
lemma idx_neg (k : ℕ) (hk : 1 ≤ k) :
    (Lst (k + 2)).idxOf (-((k : ℤ) : GaussianInt)) = (Lst (k + 1)).length + 3 := by
  obtain ⟨r, hr⟩ := (gen_four k hk).2
  have hnot : -((k : ℤ) : GaussianInt) ∉ Lst (k + 1) := by
    rw [mem_Lst, d_neg_nat k hk]; push_cast; omega
  have h1 : -((k : ℤ) : GaussianInt) ≠ (((k + 2 : ℕ) : ℤ) : GaussianInt) := by
    intro h; have := congrArg Zsqrtd.re h; simp at this; omega
  have h2 : -((k : ℤ) : GaussianInt) ≠ iu * (((k + 1 : ℕ) : ℤ) : GaussianInt) := by
    intro h; have := congrArg Zsqrtd.im h; simp [iu] at this; omega
  have h3 : -((k : ℤ) : GaussianInt) ≠ iu * ((k : ℤ) : GaussianInt) + 1 := by
    intro h; have := congrArg Zsqrtd.re h; simp [iu] at this; omega
  rw [Lst_succ (k + 1), hr, List.idxOf_append_of_notMem hnot, List.idxOf_cons_ne _ h1.symm,
    List.idxOf_cons_ne _ h2.symm, List.idxOf_cons_ne _ h3.symm, List.idxOf_cons_self]

/-- The set of positions of the integers. -/
def IsP (p : ℕ) : Prop := 1 ≤ p ∧ (elt p).im = 0

lemma elt_nat (k : ℕ) : elt ((Lst k).length + 1) = (((k + 1 : ℕ) : ℤ) : GaussianInt) := by
  apply elt_of (t := k + 1)
  · rw [← idx_nat k]
    exact List.getElem?_idxOf ((mem_Lst _ _).2 (by rw [d_nat]))
  · have := len_ge k; omega

lemma elt_neg (k : ℕ) (hk : 1 ≤ k) :
    elt ((Lst (k + 1)).length + 4) = -((k : ℤ) : GaussianInt) := by
  rw [show (Lst (k + 1)).length + 4 = ((Lst (k + 1)).length + 3) + 1 by omega]
  apply elt_of (t := k + 2)
  · rw [← idx_neg k hk]
    exact List.getElem?_idxOf ((mem_Lst _ _).2 (by rw [d_neg_nat k hk]; push_cast; omega))
  · have := len_ge (k + 1); omega

lemma elt_one : elt 1 = 0 := by decide

/-- Every position of an integer is one of the explicit ones. -/
lemma IsP_cases {p : ℕ} (hp : IsP p) :
    p = 1 ∨ (∃ k : ℕ, p = (Lst k).length + 1) ∨ ∃ k : ℕ, 1 ≤ k ∧ p = (Lst (k + 1)).length + 4 := by
  obtain ⟨hp1, him⟩ := hp
  have hlen : p - 1 < (Lst p).length := by have := len_ge p; omega
  set z := elt p with hz
  have hzget : (Lst p)[p - 1]'hlen = z := by
    rw [hz]; unfold elt; rw [List.getD_eq_getElem _ _ hlen]
  have hzmem : z ∈ Lst p := by rw [← hzget]; exact List.getElem_mem hlen
  have hidx : (Lst p).idxOf z = p - 1 := by
    rw [← hzget]; exact (Lst_nodup p).idxOf_getElem (p - 1) hlen
  have hzr : z = ((z.re : ℤ) : GaussianInt) := by ext <;> simp [him]
  rcases lt_or_ge z.re 0 with hneg | hnn
  · -- z = -k with k >= 1
    obtain ⟨k, hk⟩ : ∃ k : ℕ, z.re = -(k : ℤ) := ⟨(-z.re).toNat, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hzk : z = -((k : ℤ) : GaussianInt) := by rw [hzr, hk]; push_cast; ring
    have hdk : (k + 2 : ℕ) ≤ p := by
      have := (mem_Lst p z).1 hzmem
      rw [hzk, d_neg_nat k hk1] at this
      exact_mod_cast this
    obtain ⟨l, hl⟩ := Lst_prefix (k + 2) (p - (k + 2))
    rw [show k + 2 + (p - (k + 2)) = p by omega] at hl
    have hmem2 : z ∈ Lst (k + 2) := (mem_Lst _ _).2 (by rw [hzk, d_neg_nat k hk1]; push_cast; omega)
    rw [← hl, List.idxOf_append_of_mem hmem2, hzk, idx_neg k hk1] at hidx
    right; right
    exact ⟨k, hk1, by omega⟩
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, z.re = (k : ℤ) := ⟨z.re.toNat, by omega⟩
    have hzk : z = ((k : ℤ) : GaussianInt) := by rw [hzr, hk]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · -- z = 0: index 0
      left
      have h0 : (Lst p).idxOf (0 : GaussianInt) = 0 := by
        cases p with
        | zero => omega
        | succ p =>
          obtain ⟨l, hl⟩ := Lst_prefix 0 (p + 1)
          rw [zero_add] at hl
          rw [← hl]
          simp [Lst]
      rw [hzk] at hidx
      simp only [Nat.cast_zero, Int.cast_zero] at hidx
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hdk : j + 1 ≤ p := by
        have := (mem_Lst p z).1 hzmem
        rw [hzk, d_nat] at this
        exact_mod_cast this
      obtain ⟨l, hl⟩ := Lst_prefix (j + 1) (p - (j + 1))
      rw [show j + 1 + (p - (j + 1)) = p by omega] at hl
      have hmem2 : z ∈ Lst (j + 1) := (mem_Lst _ _).2 (by rw [hzk, d_nat])
      rw [← hl, List.idxOf_append_of_mem hmem2, hzk, idx_nat j] at hidx
      right; left
      exact ⟨j, by omega⟩

/-! ### The enumeration -/

/-- The positions of the integers in increasing order (from index 0). -/
def e (i : ℕ) : ℕ :=
  if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 5
  else if i % 2 = 0 then (Lst ((i - 2) / 2 + 1)).length + 4 else (Lst ((i - 3) / 2 + 2)).length + 1

lemma e_even (j : ℕ) (hj : 1 ≤ j) : e (2 * j + 2) = (Lst (j + 1)).length + 4 := by
  unfold e
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show (2 * j + 2 - 2) / 2 + 1 = j + 1 by omega]

lemma e_odd (j : ℕ) (hj : 1 ≤ j) : e (2 * j + 3) = (Lst (j + 2)).length + 1 := by
  unfold e
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), show (2 * j + 3 - 3) / 2 + 2 = j + 2 by omega]

lemma len_step (t : ℕ) (ht : 2 ≤ t) : (Lst t).length + 4 ≤ (Lst (t + 1)).length := by
  rcases Nat.eq_or_lt_of_le ht with rfl | ht3
  · rw [len2, show 2 + 1 = 3 from rfl]
    have := len_formula 3 le_rfl
    omega
  · have h1 := len_formula t ht3
    have h2 := len_formula (t + 1) (by omega)
    nlinarith

lemma e_strictMono : StrictMono e := by
  apply strictMono_nat_of_lt_succ
  intro i
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · simp [e]
    · simp [e]
    · simp [e]
    · rw [show (3 + 1 : ℕ) = 2 * 1 + 2 from rfl, e_even 1 le_rfl, len2]
      simp [e]
  · rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [show i = 2 * m + 2 by omega, show 2 * m + 2 + 1 = 2 * m + 3 by omega,
        e_even m (by omega), e_odd m (by omega)]
      have := len_step (m + 1) (by omega)
      rw [show m + 1 + 1 = m + 2 from rfl] at this
      omega
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [show i = 2 * m + 3 by omega, show 2 * m + 3 + 1 = 2 * (m + 1) + 2 by omega,
        e_odd m (by omega), e_even (m + 1) (by omega)]
      rw [show m + 1 + 1 = m + 2 from rfl]
      omega

lemma e_maps (i : ℕ) : IsP (e i) := by
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · have he : e 0 = 1 := by simp [e]
      rw [he]; exact ⟨le_rfl, by rw [elt_one]; rfl⟩
    · have he : e 1 = 2 := by simp [e]
      have h := elt_nat 0
      rw [len0] at h
      rw [he]; exact ⟨by norm_num, by rw [show (2 : ℕ) = 1 + 1 from rfl, h]; simp⟩
    · have he : e 2 = 3 := by simp [e]
      have h := elt_nat 1
      rw [len1] at h
      rw [he]; exact ⟨by norm_num, by rw [show (3 : ℕ) = 2 + 1 from rfl, h]; simp⟩
    · have he : e 3 = 5 := by simp [e]
      have h := elt_nat 2
      rw [len2] at h
      rw [he]; exact ⟨by norm_num, by rw [show (5 : ℕ) = 4 + 1 from rfl, h]; simp⟩
  · rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [show i = 2 * m + 2 by omega, e_even m (by omega)]
      exact ⟨by omega, by rw [elt_neg m (by omega)]; simp⟩
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      rw [show i = 2 * m + 3 by omega, e_odd m (by omega)]
      exact ⟨by omega, by rw [elt_nat]; simp⟩

lemma e_surj {p : ℕ} (hp : IsP p) : ∃ i, e i = p := by
  rcases IsP_cases hp with rfl | ⟨k, rfl⟩ | ⟨k, hk, rfl⟩
  · exact ⟨0, by simp [e]⟩
  · rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · interval_cases k
      · exact ⟨1, by simp [e, len0]⟩
      · exact ⟨2, by simp [e, len1]⟩
      · exact ⟨3, by simp [e, len2]⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      exact ⟨2 * j + 3, e_odd j (by omega)⟩
  · exact ⟨2 * k + 2, e_even k hk⟩

lemma IsP_infinite : (Set.ofPred IsP).Infinite :=
  Set.infinite_of_injective_forall_mem e_strictMono.injective e_maps

lemma e_eq_nth (i : ℕ) : e i = Nat.nth IsP i := by
  have h := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := IsP) e
    (fun p hp => by
      obtain ⟨i, hi⟩ := e_surj hp
      exact ⟨i, fun hf => absurd hf IsP_infinite, hi⟩)
    (fun i _ => e_maps i)
    (e_strictMono.strictMonoOn _)
  exact h (fun hf => absurd hf IsP_infinite)

lemma a_eq (n : ℕ) : a n = e (n - 1) := by
  rw [e_eq_nth]
  rfl

/-! ### Closed forms and the conjectures -/

lemma e_even' (m : ℕ) (hm : 3 ≤ m) : (e (2 * m) : ℤ) = 2 * m ^ 2 - 7 * m + 15 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, e_even j (by omega)]
  have := len_formula (j + 1) (by omega)
  push_cast
  nlinarith

lemma e_odd' (m : ℕ) (hm : 2 ≤ m) : (e (2 * m + 1) : ℤ) = 2 * m ^ 2 - 3 * m + 7 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, e_odd j (by omega)]
  have := len_formula (j + 2) (by omega)
  push_cast
  nlinarith

theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
  simp only [a_eq, show k + 11 - 1 = k + 10 by omega, show k + 10 - 1 = k + 9 by omega,
    show k + 11 - 2 = k + 9 by omega, show k + 9 - 1 = k + 8 by omega,
    show k + 11 - 3 = k + 8 by omega, show k + 8 - 1 = k + 7 by omega,
    show k + 11 - 4 = k + 7 by omega, show k + 7 - 1 = k + 6 by omega,
    show k + 11 - 5 = k + 6 by omega, show k + 6 - 1 = k + 5 by omega]
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m + m + 10 = 2 * (m + 5) by ring, show m + m + 9 = 2 * (m + 4) + 1 by ring,
      show m + m + 8 = 2 * (m + 4) by ring, show m + m + 7 = 2 * (m + 3) + 1 by ring,
      show m + m + 6 = 2 * (m + 3) by ring, show m + m + 5 = 2 * (m + 2) + 1 by ring,
      e_even' (m + 5) (by omega), e_odd' (m + 4) (by omega), e_even' (m + 4) (by omega),
      e_odd' (m + 3) (by omega), e_even' (m + 3) (by omega), e_odd' (m + 2) (by omega)]
    push_cast
    ring
  · subst hm
    rw [show 2 * m + 1 + 10 = 2 * (m + 5) + 1 by ring, show 2 * m + 1 + 9 = 2 * (m + 5) by ring,
      show 2 * m + 1 + 8 = 2 * (m + 4) + 1 by ring, show 2 * m + 1 + 7 = 2 * (m + 4) by ring,
      show 2 * m + 1 + 6 = 2 * (m + 3) + 1 by ring, show 2 * m + 1 + 5 = 2 * (m + 3) by ring,
      e_odd' (m + 5) (by omega), e_even' (m + 5) (by omega), e_odd' (m + 4) (by omega),
      e_even' (m + 4) (by omega), e_odd' (m + 3) (by omega), e_even' (m + 3) (by omega)]
    push_cast
    ring

lemma a_values : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 5 ∧ a 5 = 8 ∧ a 6 = 9 ∧ a 7 = 12 ∧
    a 8 = 16 ∧ a 9 = 19 ∧ a 10 = 27 := by
  have l3 := len_formula 3 le_rfl
  have l4 := len_formula 4 (by norm_num)
  have l5 := len_formula 5 (by norm_num)
  simp only [a_eq]
  refine ⟨by simp [e], by simp [e], by simp [e], by simp [e], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (5 - 1 : ℕ) = 2 * 1 + 2 from rfl, e_even 1 le_rfl, len2]
  · rw [show (6 - 1 : ℕ) = 2 * 1 + 3 from rfl, e_odd 1 le_rfl]
    show (Lst 3).length + 1 = 9
    omega
  · rw [show (7 - 1 : ℕ) = 2 * 2 + 2 from rfl, e_even 2 (by norm_num)]
    show (Lst 3).length + 4 = 12
    omega
  · rw [show (8 - 1 : ℕ) = 2 * 2 + 3 from rfl, e_odd 2 (by norm_num)]
    show (Lst 4).length + 1 = 16
    omega
  · rw [show (9 - 1 : ℕ) = 2 * 3 + 2 from rfl, e_even 3 (by norm_num)]
    show (Lst 4).length + 4 = 19
    omega
  · rw [show (10 - 1 : ℕ) = 2 * 3 + 3 from rfl, e_odd 3 (by norm_num)]
    show (Lst 5).length + 1 = 27
    omega

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * ((X - 1) ^ 3 * (X + 1) ^ 2) =
    X * (-X ^ 9 - 4 * X ^ 7 + 2 * X ^ 6 + 2 * X ^ 5 - 2 * X ^ 4 + X ^ 2 - X - 1) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have e1 : A * ((X - 1) ^ 3 * (X + 1) ^ 2) =
      A * X ^ 5 - A * X ^ 4 - A * X ^ 3 * C 2 + A * X ^ 2 * C 2 + A * X ^ 1 - A := by
    rw [show (C 2 : ℤ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  have e2 : (X : ℤ⟦X⟧) * (-X ^ 9 - 4 * X ^ 7 + 2 * X ^ 6 + 2 * X ^ 5 - 2 * X ^ 4 + X ^ 2 - X - 1) =
      -X ^ 10 - X ^ 8 * C 4 + X ^ 7 * C 2 + X ^ 6 * C 2 - X ^ 5 * C 2 + X ^ 3 - X ^ 2 - X ^ 1 := by
    rw [show (C 2 : ℤ⟦X⟧) = 2 from map_ofNat C 2, show (C 4 : ℤ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := a_values
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · have h := recurrence n (by omega)
    simp only [show ¬ (n = 0) by omega, show ¬ (n - 1 = 0) by omega, show ¬ (n - 2 = 0) by omega,
      show ¬ (n - 3 = 0) by omega, show ¬ (n - 4 = 0) by omega, show ¬ (n - 5 = 0) by omega,
      if_false, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show ¬ (n = 10) by omega,
      show ¬ (n = 8) by omega, show ¬ (n = 7) by omega, show ¬ (n = 6) by omega,
      show ¬ (n = 5) by omega, show ¬ (n = 3) by omega, show ¬ (n = 2) by omega,
      show ¬ (n = 1) by omega]
    rw [h]
    ring

/-- Wu's two conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        ((PowerSeries.X - 1) ^ 3 * (PowerSeries.X + 1) ^ 2) =
      PowerSeries.X * (-PowerSeries.X ^ 9 - 4 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 6 +
        2 * PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 2 - PowerSeries.X - 1) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a232868

theorem OMA.solution : type_of% @OMA.S_oeis_a232868.main :=
  OMA.S_oeis_a232868.conjecture
