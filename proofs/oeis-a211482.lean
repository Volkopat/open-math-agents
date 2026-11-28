import OMAStatements.S_oeis_a211482
import Mathlib

open OMA.S_oeis_a211482

private theorem inv_le (u : ℤ) (h0 : u ≠ 0) (h1 : u ≠ 1) : (1 : ℚ) / u ≤ 1/2 := by
  by_cases hu : u < 0
  · have hu' : (u : ℚ) < 0 := by exact_mod_cast hu
    have hneg : (1 : ℚ) / u < 0 := div_neg_of_pos_of_neg (by norm_num) hu'
    linarith
  · have hu' : (2 : ℚ) ≤ u := by exact_mod_cast (show 2 ≤ u by omega)
    exact (div_le_div_iff_of_pos_left (by norm_num) (by linarith) (by norm_num)).mpr hu'

private theorem inv_bound (u v : ℤ) (hv : 0 < v) (h : v ≤ u) : (1 : ℚ) / u ≤ 1 / v := by
  have hv' : (0 : ℚ) < v := by exact_mod_cast hv
  have h' : (v : ℚ) ≤ u := by exact_mod_cast h
  exact (div_le_div_iff_of_pos_left (by norm_num) (by linarith) hv').mpr h'

private theorem small_first (w x y : ℤ)
    (h : (1 : ℚ)/w + 1/x + 1/y = 1)
    (_hw : 2 ≤ w) (hx : 2 ≤ x) (hy : 2 ≤ y) : w ≤ 6 := by
  by_contra! hw'
  have w7 := inv_bound w 7 (by decide) (by omega)
  have x2 := inv_bound x 2 (by decide) hx
  have y2 := inv_bound y 2 (by decide) hy
  simp only [one_div] at h
  norm_num at w7 x2 y2
  by_cases hxx : x = 2
  · by_cases hyy : y = 2
    · rw [hxx,hyy] at h
      norm_num at h
      have hwq : (0 : ℚ) < w := by exact_mod_cast (show 0 < w by omega)
      have hp : (0 : ℚ) < 1/w := div_pos (by norm_num) hwq
      simp only [one_div] at hp
      linarith
    · have y3 := inv_bound y 3 (by decide) (by omega)
      rw [hxx] at h
      norm_num at h y3
      linarith
  · have x3 := inv_bound x 3 (by decide) (by omega)
    norm_num at x3
    linarith

private theorem small (w x y : ℤ) (hs : Sol w x y)
    (hw : w ≠ 0 ∧ w ≠ 1) (hx : x ≠ 0 ∧ x ≠ 1) (hy : y ≠ 0 ∧ y ≠ 1) :
    (2 ≤ w ∧ w ≤ 6) ∧ (2 ≤ x ∧ x ≤ 6) ∧ (2 ≤ y ∧ y ≤ 6) := by
  have hnw : (w : ℚ) ≠ 0 := by exact_mod_cast hw.1
  have hnx : (x : ℚ) ≠ 0 := by exact_mod_cast hx.1
  have hny : (y : ℚ) ≠ 0 := by exact_mod_cast hy.1
  have hs' : (w : ℚ)*x + w*y + x*y = w*x*y := by exact_mod_cast hs
  have h : (1 : ℚ)/w + 1/x + 1/y = 1 := by
    field_simp
    linear_combination hs'
  have w2 := inv_le w hw.1 hw.2
  have x2 := inv_le x hx.1 hx.2
  have y2 := inv_le y hy.1 hy.2
  have wpos : 2 ≤ w := by
    by_contra! hh
    have hwq : (w : ℚ) < 0 := by exact_mod_cast (show w < 0 by omega)
    have hn : (1 : ℚ)/w < 0 := div_neg_of_pos_of_neg (by norm_num) hwq
    linarith
  have xpos : 2 ≤ x := by
    by_contra! hh
    have hxq : (x : ℚ) < 0 := by exact_mod_cast (show x < 0 by omega)
    have hn : (1 : ℚ)/x < 0 := div_neg_of_pos_of_neg (by norm_num) hxq
    linarith
  have ypos : 2 ≤ y := by
    by_contra! hh
    have hyq : (y : ℚ) < 0 := by exact_mod_cast (show y < 0 by omega)
    have hn : (1 : ℚ)/y < 0 := div_neg_of_pos_of_neg (by norm_num) hyq
    linarith
  exact ⟨⟨wpos, small_first w x y h wpos xpos ypos⟩,
    ⟨xpos, small_first x w y (by linarith) xpos wpos ypos⟩,
    ⟨ypos, small_first y w x (by linarith) ypos wpos xpos⟩⟩

private def shell (k : ℤ) : Finset Triple :=
  {(k,0,0), (-k,0,0), (0,k,0), (0,-k,0), (0,0,k), (0,0,-k),
    (1,k,-k), (1,-k,k), (k,1,-k), (-k,1,k), (k,-k,1), (-k,k,1)}

private theorem mem_solutions (n : ℕ) (w x y : ℤ) :
    (w,x,y) ∈ solutions n ↔
      ((-(n:ℤ) ≤ w ∧ w ≤ n) ∧ (-(n:ℤ) ≤ x ∧ x ≤ n) ∧ (-(n:ℤ) ≤ y ∧ y ≤ n)) ∧ Sol w x y := by
  simp [solutions, Finset.mem_product]

private theorem outer (n : ℕ) (hn : 6 ≤ n) (w x y : ℤ)
    (hnxt : (w,x,y) ∈ solutions (n+1)) (hprev : (w,x,y) ∉ solutions n) :
    (w,x,y) ∈ shell ((n:ℤ)+1) := by
  rw [mem_solutions, Nat.cast_add, Nat.cast_one] at hnxt
  rw [mem_solutions] at hprev
  obtain ⟨hb, hs⟩ := hnxt
  have hbad : ¬ ((-(n:ℤ) ≤ w ∧ w ≤ n) ∧ (-(n:ℤ) ≤ x ∧ x ≤ n) ∧ (-(n:ℤ) ≤ y ∧ y ≤ n)) :=
    fun h => hprev ⟨h,hs⟩
  by_cases hw : w = 0
  · have h : x*y=0 := by simpa [Sol,hw] using hs
    rcases mul_eq_zero.mp h with h | h
    · have he : y = (n:ℤ)+1 ∨ y = -((n:ℤ)+1) := by omega
      rcases he with he | he <;> simp [shell,hw,h,he]
    · have he : x = (n:ℤ)+1 ∨ x = -((n:ℤ)+1) := by omega
      rcases he with he | he <;> simp [shell,hw,h,he]
  by_cases hx : x = 0
  · have h : w*y=0 := by simpa [Sol,hx] using hs
    rcases mul_eq_zero.mp h with h | h
    · have he : y = (n:ℤ)+1 ∨ y = -((n:ℤ)+1) := by omega
      rcases he with he | he <;> simp [shell,hx,h,he]
    · have he : w = (n:ℤ)+1 ∨ w = -((n:ℤ)+1) := by omega
      rcases he with he | he <;> simp [shell,hx,h,he]
  by_cases hy : y = 0
  · have h : w*x=0 := by simpa [Sol,hy] using hs
    rcases mul_eq_zero.mp h with h | h
    · have he : x = (n:ℤ)+1 ∨ x = -((n:ℤ)+1) := by omega
      rcases he with he | he <;> simp [shell,hy,h,he]
    · have he : w = (n:ℤ)+1 ∨ w = -((n:ℤ)+1) := by omega
      rcases he with he | he <;> simp [shell,hy,h,he]
  by_cases hw1 : w = 1
  · have heq : x+y=0 := by
      unfold Sol at hs
      rw [hw1] at hs
      nlinarith
    have he : x = (n:ℤ)+1 ∨ x = -((n:ℤ)+1) := by omega
    have he' : y = -x := by omega
    rcases he with he | he <;> simp [shell,hw1,he',he]
  by_cases hx1 : x = 1
  · have heq : w+y=0 := by
      unfold Sol at hs
      rw [hx1] at hs
      nlinarith
    have he : w = (n:ℤ)+1 ∨ w = -((n:ℤ)+1) := by omega
    have he' : y = -w := by omega
    rcases he with he | he <;> simp [shell,hx1,he',he]
  by_cases hy1 : y = 1
  · have heq : w+x=0 := by
      unfold Sol at hs
      rw [hy1] at hs
      nlinarith
    have he : w = (n:ℤ)+1 ∨ w = -((n:ℤ)+1) := by omega
    have he' : x = -w := by omega
    rcases he with he | he <;> simp [shell,hy1,he',he]
  have e := small w x y hs ⟨hw,hw1⟩ ⟨hx,hx1⟩ ⟨hy,hy1⟩
  omega

private theorem inner_shell (n : ℕ) (hn : 6 ≤ n) {t : Triple}
    (h : t ∈ shell ((n:ℤ)+1)) : t ∈ solutions (n+1) ∧ t ∉ solutions n := by
  simp only [shell, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [mem_solutions, Nat.cast_add, Nat.cast_one] <;>
    constructor
  all_goals first
    | exact fun h => by omega
    | exact ⟨by omega, by unfold Sol; ring⟩

private theorem card_shell (n : ℕ) (hn : 6 ≤ n) : (shell ((n:ℤ)+1)).card = 12 := by
  unfold shell
  repeat' rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega)]
  simp

private def smallRange : Finset ℤ := (Finset.range 13).image (fun i : ℕ => (i : ℤ)-6)

private theorem smallRange_eq : smallRange = Finset.Icc (-6 : ℤ) 6 := by
  ext i
  simp only [smallRange, Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨j,hj,rfl⟩
    omega
  · intro h
    exact ⟨(i+6).toNat, by omega, by omega⟩

private def computableSolutions : Finset Triple :=
  (smallRange ×ˢ (smallRange ×ˢ smallRange)).filter
    (fun t => t.1*t.2.1+t.1*t.2.2+t.2.1*t.2.2=t.1*t.2.1*t.2.2)

private theorem card_six : (solutions 6).card = 80 := by
  have e : solutions 6 = computableSolutions := by
    ext t
    rcases t with ⟨w,x,y⟩
    rw [mem_solutions, computableSolutions, Finset.mem_filter]
    simp [smallRange_eq, Finset.mem_product, Sol]
  rw [e]
  decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a211482.main := by
  intro n hn
  have h6 : 6 ≤ n := by omega
  clear hn
  induction n, h6 using Nat.le_induction with
  | base => exact card_six
  | succ n hn ih =>
    have hd : Disjoint (solutions n) (shell ((n:ℤ)+1)) := by
      rw [Finset.disjoint_left]
      exact fun _ hs ht => (inner_shell n hn ht).2 hs
    have he : solutions (n+1) = solutions n ∪ shell ((n:ℤ)+1) := by
      ext t
      rcases t with ⟨w,x,y⟩
      rw [Finset.mem_union]
      constructor
      · intro h
        by_cases e : (w,x,y) ∈ solutions n
        · exact Or.inl e
        · exact Or.inr (outer n hn w x y h e)
      · rintro (h|h)
        · rw [mem_solutions] at h ⊢
          refine ⟨?_,h.2⟩
          push_cast
          omega
        · exact (inner_shell n hn h).1
    rw [he, Finset.card_union_of_disjoint hd, card_shell n hn, ih]
    omega