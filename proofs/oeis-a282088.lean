import OMAStatements.S_oeis_a282088


/-!
# Rule 553, an edge dilation of the Ulam–Warburton automaton

For Robert Price's A282088, https://oeis.org/A282088, Colin Barker
conjectured formulas for the decimal word along the left half-axis.
At odd stages the OFF cells are an edge dilation of the coarse
one-neighbor Ulam–Warburton growth process. The complementary local rule
is 430. Newly occupied coarse cells have alternating checkerboard parity,
so adjacent coarse cells cannot be born at the same step. This gives the
two-step update of the dilation. The growing coarse axis then determines
every digit in the word. The coarse light-cone and axis arguments also
appear in the Rule 129 calculation for A279030.
-/

namespace Rule553

def seed (x y : ℤ) : Bool := decide (x=0 ∧ y=0)

def grow (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  f x y || decide ((f (x+1) y).toNat + (f (x-1) y).toNat +
    (f x (y+1)).toNat + (f x (y-1)).toNat = 1)

def coarse : ℕ → ℤ → ℤ → Bool
  | 0 => seed
  | t+1 => grow (coarse t)

private theorem adjacent_abs (u v : ℤ) (hl : u-1≤v) (hr : v≤u+1) : |u| ≤ |v|+1 := by
  have hv := abs_le.mp (le_refl |v|)
  exact abs_le.mpr (by omega)

/-- Live sites stay within Manhattan distance t of the initial site. -/
theorem coarse_outside (t : ℕ) (x y : ℤ) (ho : (t:ℤ) < |x| + |y|) :
    coarse t x y = false := by
  induction t generalizing x y with
  | zero =>
    change decide (x=0 ∧ y=0) = false
    apply decide_eq_false
    rintro ⟨rfl,rfl⟩
    simp at ho
  | succ t ih =>
    have xp := adjacent_abs x (x+1) (by omega) (by omega)
    have xm := adjacent_abs x (x-1) (by omega) (by omega)
    have yp := adjacent_abs y (y+1) (by omega) (by omega)
    have ym := adjacent_abs y (y-1) (by omega) (by omega)
    simp [coarse,grow,ih x y (by omega),ih (x+1) y (by omega),ih (x-1) y (by omega),
      ih x (y+1) (by omega),ih x (y-1) (by omega)]

/-- At the new left endpoint the right neighbor is the only live neighbor
at the previous time. All earlier axis sites stay live. -/
theorem coarse_axis (t : ℕ) (x : ℤ) (hl : -(t:ℤ)≤x) (hr : x≤0) : coarse t x 0 = true := by
  induction t generalizing x with
  | zero =>
    have h : x=0 := by omega
    subst x
    decide
  | succ t ih =>
    by_cases hi : -(t:ℤ)≤x
    · simp [coarse,grow,ih x hi hr]
    · have endpt : x = -(t:ℤ)-1 := by omega
      have ox : |x| = -x := abs_of_nonpos hr
      have om : |x-1| = -(x-1) := abs_of_nonpos (by omega)
      have hc := coarse_outside t x 0 (by rw [ox,abs_zero]; omega)
      have hp := ih (x+1) (by omega) (by omega)
      have hm := coarse_outside t (x-1) 0 (by rw [om,abs_zero]; omega)
      have hu := coarse_outside t x 1 (by rw [ox,abs_one]; omega)
      have hd := coarse_outside t x (-1) (by rw [ox,abs_neg,abs_one]; omega)
      simp [coarse,grow,hc,hp,hm,hu,hd]

end Rule553

namespace Rule553

def dilate (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  if x%2=0 then
    if y%2=0 then f (x/2) (y/2) else f (x/2) (y/2) || f (x/2) (y/2+1)
  else if y%2=0 then f (x/2) (y/2) || f (x/2+1) (y/2) else false

def nbr (f : ℤ → ℤ → Bool) (x y : ℤ) : ℕ :=
  (f (x+1) y).toNat + (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat

def step430 (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (430 : ℕ).testBit ((f x y).toNat + 2*nbr f x y)

theorem dilateEE (f : ℤ → ℤ → Bool) (x y : ℤ) : dilate f (2*x) (2*y) = f x y := by
  simp (disch := omega) [dilate, show 2*x/2=x by omega,show 2*y/2=y by omega]

theorem dilateOE (f : ℤ → ℤ → Bool) (x y : ℤ) : dilate f (2*x+1) (2*y) = (f x y || f (x+1) y) := by
  simp (disch := omega) [dilate, show (2*x+1)/2=x by omega,show 2*y/2=y by omega]

theorem dilateEO (f : ℤ → ℤ → Bool) (x y : ℤ) : dilate f (2*x) (2*y+1) = (f x y || f x (y+1)) := by
  simp (disch := omega) [dilate, show 2*x/2=x by omega,show (2*y+1)/2=y by omega]

theorem dilateOO (f : ℤ → ℤ → Bool) (x y : ℤ) : dilate f (2*x+1) (2*y+1) = false := by
  simp (disch := omega) [dilate]

end Rule553

namespace Rule553

/-- A persistent coarse cell can change only on the checkerboard parity
of the new stage. At the other parity, its four neighbors have just
remained unchanged, so the same birth test is repeated. -/
theorem coarse_unchanged (h : ℕ) (x y : ℤ) (hp : (x+y)%2 ≠ ((h:ℤ)+1)%2) :
    coarse (h+1) x y = coarse h x y := by
  induction h generalizing x y with
  | zero =>
    change grow seed x y = seed x y
    have away (u v : ℤ) (hu : (u+v)%2 ≠ 0) : seed u v = false := by
      simp [seed]
      omega
    simp only [grow, away (x+1) y (by omega), away (x-1) y (by omega),
      away x (y+1) (by omega), away x (y-1) (by omega)]
    simp
  | succ h ih =>
    change grow (coarse (h+1)) x y = coarse (h+1) x y
    have prev : coarse (h+1) x y = grow (coarse h) x y := rfl
    rw [grow, ih (x+1) y (by omega), ih (x-1) y (by omega),
      ih x (y+1) (by omega), ih x (y-1) (by omega), prev, grow]
    simp

theorem coarse_birth_parity (h : ℕ) (x y : ℤ) (before : coarse h x y = false)
    (after : grow (coarse h) x y = true) : (x+y)%2 = ((h:ℤ)+1)%2 := by
  by_contra hp
  have same := coarse_unchanged h x y hp
  change grow (coarse h) x y = coarse h x y at same
  simp [before, after] at same

theorem coarse_no_adjX (h : ℕ) (x y : ℤ) :
    ¬ (coarse h x y = false ∧ grow (coarse h) x y = true ∧
       coarse h (x+1) y = false ∧ grow (coarse h) (x+1) y = true) := by
  rintro ⟨a,b,c,d⟩
  have left := coarse_birth_parity h x y a b
  have right := coarse_birth_parity h (x+1) y c d
  omega

theorem coarse_no_adjY (h : ℕ) (x y : ℤ) :
    ¬ (coarse h x y = false ∧ grow (coarse h) x y = true ∧
       coarse h x (y+1) = false ∧ grow (coarse h) x (y+1) = true) := by
  rintro ⟨a,b,c,d⟩
  have lower := coarse_birth_parity h x y a b
  have upper := coarse_birth_parity h x (y+1) c d
  omega

end Rule553

namespace Rule553
open OMA.S_oeis_a282088

private theorem complementary_rule (c e w n s : Bool) :
    Bool.not ((553:ℕ).testBit (c.toNat + 2*(e.toNat + w.toNat + n.toNat + s.toNat))) =
      (430:ℕ).testBit ((!c).toNat + 2*((!e).toNat + (!w).toNat + (!n).toNat + (!s).toNat)) := by
  decide +revert

theorem complement_step (t : ℕ) : (fun x y => !(cell 553 (t+1) x y)) =
    step430 (fun x y => !(cell 553 t x y)) := by
  funext x y
  exact complementary_rule _ _ _ _ _

/-- The first OFF cells are the five cells of the cross centered at the origin. -/
theorem complement_one : (fun x y => !(cell 553 1 x y)) = dilate (coarse 0) := by
  funext x y
  by_cases h : -1≤x ∧ x≤1 ∧ -1≤y ∧ y≤1
  · obtain ⟨h₁,h₂,h₃,h₄⟩ := h
    interval_cases x <;> interval_cases y <;> decide
  · have o (x' y' : ℤ) (hx₁ : -1≤x'-x) (hx₂ : x'-x≤1)
        (hy₁ : -1≤y'-y) (hy₂ : y'-y≤1) : ¬(x'=0 ∧ y'=0) := by omega
    have hx : Bool.not (cell 553 1 x y) = false := by
      simp only [cell,decide_eq_false (o x y (by omega) (by omega) (by omega) (by omega)),
        decide_eq_false (o (x+1) y (by omega) (by omega) (by omega) (by omega)),
        decide_eq_false (o (x-1) y (by omega) (by omega) (by omega) (by omega)),
        decide_eq_false (o x (y+1) (by omega) (by omega) (by omega) (by omega)),
        decide_eq_false (o x (y-1) (by omega) (by omega) (by omega) (by omega))]
      rfl
    rw [hx]
    simp only [dilate,coarse,seed]
    split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
      simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.false_eq_true, false_iff] <;> omega

end Rule553

namespace Rule553

private theorem prior (x : ℤ) : 2*x-1=2*(x-1)+1 := by omega
private theorem next (x : ℤ) : 2*x+1+1=2*(x+1) := by omega

private def oneFour (a : ℕ) : Bool := decide (a=1 ∨ a=4)

private def corner (a b c d : Bool) : Bool :=
  (430 : ℕ).testBit (0+2*((b || d).toNat + (a || c).toNat + (c || d).toNat + (a || b).toNat))

private theorem halfEECore (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step430 (dilate f) (2*x) (2*y) = (!f x y && oneFour (nbr f x y)) := by
  rw [step430]
  simp only [nbr, prior, sub_add_cancel, dilateEE, dilateEO, dilateOE]
  generalize f x y = v0
  generalize f (x+1) y = v1
  generalize f (x-1) y = v2
  generalize f x (y+1) = v3
  generalize f x (y-1) = v4
  revert v0 v1 v2 v3 v4
  decide +kernel

theorem halfOE (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step430 (dilate f) (2*x+1) (2*y) = (f x y || f (x+1) y) := by
  rw [step430]
  simp only [nbr, prior, next, add_sub_cancel_right, dilateEE, dilateOE, dilateOO]
  generalize f x y = v0
  generalize f (x+1) y = v1
  revert v0 v1
  decide +kernel

theorem halfEO (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step430 (dilate f) (2*x) (2*y+1) = (f x y || f x (y+1)) := by
  rw [step430]
  simp only [nbr, prior, next, add_sub_cancel_right, dilateEE, dilateEO, dilateOO]
  generalize f x y = v0
  generalize f x (y+1) = v1
  revert v0 v1
  decide +kernel

private theorem halfOO (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step430 (dilate f) (2*x+1) (2*y+1) = corner (f x y) (f (x+1) y) (f x (y+1)) (f (x+1) (y+1)) := by
  rw [step430]
  simp only [nbr, next, add_sub_cancel_right, dilateEO, dilateOE, dilateOO, corner]
  rfl

private theorem twoEE (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step430 (step430 (dilate f)) (2*x) (2*y) = dilate (grow f) (2*x) (2*y) := by
  rw [step430]
  simp only [← Bool.beq_eq_decide_eq, nbr, prior, sub_add_cancel, dilateEE, halfEECore, halfEO, halfOE, grow]
  generalize f x y = v0
  generalize f (x+1) y = v1
  generalize f (x-1) y = v2
  generalize f x (y+1) = v3
  generalize f x (y-1) = v4
  revert v0 v1 v2 v3 v4
  decide +kernel

private theorem twoOE (f : ℤ → ℤ → Bool) (x y : ℤ)
    (ha : ¬ (f x y=false ∧ grow f x y=true ∧ f (x+1) y=false ∧ grow f (x+1) y=true)) :
    step430 (step430 (dilate f)) (2*x+1) (2*y) = dilate (grow f) (2*x+1) (2*y) := by
  rw [step430]
  simp only [← Bool.beq_eq_decide_eq, nbr, prior, next, add_sub_cancel_right, sub_add_cancel, dilateOE, halfEECore, halfOE, halfOO, grow, corner] at ha ⊢
  generalize f x y = v0 at ha ⊢
  generalize f (x+1) y = v1 at ha ⊢
  generalize f (x-1) y = v2 at ha ⊢
  generalize f x (y+1) = v3 at ha ⊢
  generalize f x (y-1) = v4 at ha ⊢
  generalize f (x+1+1) y = v5 at ha ⊢
  generalize f (x+1) (y+1) = v6 at ha ⊢
  generalize f (x+1) (y-1) = v7 at ha ⊢
  revert v0 v1 v2 v3 v4 v5 v6 v7
  decide +kernel

private theorem twoEO (f : ℤ → ℤ → Bool) (x y : ℤ)
    (ha : ¬ (f x y=false ∧ grow f x y=true ∧ f x (y+1)=false ∧ grow f x (y+1)=true)) :
    step430 (step430 (dilate f)) (2*x) (2*y+1) = dilate (grow f) (2*x) (2*y+1) := by
  rw [step430]
  simp only [← Bool.beq_eq_decide_eq, nbr, prior, next, add_sub_cancel_right, sub_add_cancel, dilateEO, halfEECore, halfEO, halfOO, grow, corner] at ha ⊢
  generalize f x y = v0 at ha ⊢
  generalize f x (y+1) = v1 at ha ⊢
  generalize f x (y-1) = v2 at ha ⊢
  generalize f (x+1) y = v3 at ha ⊢
  generalize f (x-1) y = v4 at ha ⊢
  generalize f x (y+1+1) = v5 at ha ⊢
  generalize f (x+1) (y+1) = v6 at ha ⊢
  generalize f (x-1) (y+1) = v7 at ha ⊢
  revert v0 v1 v2 v3 v4 v5 v6 v7
  decide +kernel

private theorem twoOO (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step430 (step430 (dilate f)) (2*x+1) (2*y+1) = dilate (grow f) (2*x+1) (2*y+1) := by
  rw [step430]
  simp only [nbr, next, add_sub_cancel_right, dilateOO, halfEO, halfOE, halfOO, corner]
  generalize f x y = v0
  generalize f (x+1) y = v1
  generalize f x (y+1) = v2
  generalize f (x+1) (y+1) = v3
  revert v0 v1 v2 v3
  decide +kernel

theorem halfEE (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step430 (dilate f) (2*x) (2*y) = (!f x y && decide (nbr f x y=1 ∨ nbr f x y=4)) :=
  halfEECore f x y

/-- On dilated states, two updates implement one monotone coarse update whenever adjacent
coarse sites cannot be born together. -/
theorem double_step (f : ℤ → ℤ → Bool)
    (hx : ∀ x y, ¬ (f x y=false ∧ grow f x y=true ∧ f (x+1) y=false ∧ grow f (x+1) y=true))
    (hy : ∀ x y, ¬ (f x y=false ∧ grow f x y=true ∧ f x (y+1)=false ∧ grow f x (y+1)=true)) :
    step430 (step430 (dilate f)) = dilate (grow f) := by
  funext x y
  have parity (z : ℤ) : z=2*(z/2) ∨ z=2*(z/2)+1 := by omega
  rcases parity x with ax|ax <;> rcases parity y with ay|ay
  · exact ax.symm ▸ ay.symm ▸ twoEE f (x/2) (y/2)
  · exact ax.symm ▸ ay.symm ▸ twoEO f (x/2) (y/2) (hy _ _)
  · exact ax.symm ▸ ay.symm ▸ twoOE f (x/2) (y/2) (hx _ _)
  · exact ax.symm ▸ ay.symm ▸ twoOO f (x/2) (y/2)

end Rule553

namespace Rule553
open OMA.S_oeis_a282088

/-- At each odd stage the off cells form the dilation of the coarse process. -/
theorem odd_holes (h : ℕ) :
    (fun x y => !cell 553 (2*h+1) x y) = dilate (coarse h) := by
  induction h with
  | zero => exact complement_one
  | succ h ih =>
    rw [show 2*(h+1)+1=2*h+1+1+1 by omega, complement_step, complement_step, ih]
    exact double_step _ (coarse_no_adjX h) (coarse_no_adjY h)

/-- One application of the complementary update gives the intervening even stage. -/
theorem even_holes (h : ℕ) :
    (fun x y => !cell 553 (2*(h+1)) x y) = step430 (dilate (coarse h)) := by
  rw [show 2*(h+1)=2*h+1+1 by omega, complement_step, odd_holes]

theorem obit (h k : ℕ) (hk : k ≤ 2*h+1) :
    cell 553 (2*h+1) ((k:ℤ)-(2*h+1)) 0 = false := by
  let u : ℤ := ((k:ℤ)-(2*h+1))/2
  have he := congrFun (congrFun (odd_holes h) ((k:ℤ)-(2*h+1))) 0
  change (!cell 553 (2*h+1) ((k:ℤ)-(2*h+1)) 0) = _ at he
  by_cases par : ((k:ℤ)-(2*h+1))%2 = 0
  · have ex : (k:ℤ)-(2*h+1) = 2*u := by dsimp [u]; omega
    have c := coarse_axis h u (by dsimp [u]; omega) (by dsimp [u]; omega)
    rw [ex, ←show 2*(0:ℤ)=0 by decide, dilateEE, c] at he
    rw [ex]
    simpa using he
  · have ex : (k:ℤ)-(2*h+1) = 2*u+1 := by dsimp [u]; omega
    have c := coarse_axis h (u+1) (by dsimp [u]; omega) (by dsimp [u]; omega)
    rw [ex, ←show 2*(0:ℤ)=0 by decide, dilateOE, c, Bool.or_true] at he
    rw [ex]
    simpa using he

theorem ebit (h k : ℕ) (hh : 1 ≤ h) (hk : k ≤ 2*h) :
    cell 553 (2*h) ((k:ℤ)-2*h) 0 = decide (2 ≤ k ∧ k%2=0) := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
  simp only [Nat.cast_succ]
  let u : ℤ := ((k:ℤ)-2*(h+1))/2
  have he := congrFun (congrFun (even_holes h) ((k:ℤ)-2*(h+1))) 0
  change (!cell 553 (2*(h+1)) ((k:ℤ)-2*(h+1)) 0) = _ at he
  by_cases par : k%2=0
  · have ex : (k:ℤ)-2*(h+1) = 2*u := by dsimp [u]; omega
    rw [ex, ←show 2*(0:ℤ)=0 by decide, halfEE] at he
    rw [ex]
    by_cases hk0 : k=0
    · have hc := coarse_outside h u 0 (by
        rw [abs_of_nonpos (by dsimp [u]; omega : u ≤ 0),abs_zero]
        dsimp [u]; omega)
      have next := coarse_axis (h+1) u (by dsimp [u]; omega) (by dsimp [u]; omega)
      change (coarse h u 0 || decide (nbr (coarse h) u 0 = 1)) = true at next
      simp only [hc,Bool.false_or,decide_eq_true_eq] at next
      simpa [hk0,hc,next] using he
    · have hc := coarse_axis h u (by dsimp [u]; omega) (by dsimp [u]; omega)
      simpa [hc,par,show 2 ≤ k by omega] using he
  · have ex : (k:ℤ)-2*(h+1) = 2*u+1 := by dsimp [u]; omega
    have hc := coarse_axis h (u+1) (by dsimp [u]; omega) (by dsimp [u]; omega)
    rw [ex, ←show 2*(0:ℤ)=0 by decide, halfOE, hc, Bool.or_true] at he
    rw [ex]
    simpa [par] using he

end Rule553

namespace Rule553
open OMA.S_oeis_a282088 Finset

/-- The alternating decimal word with h ones is a geometric sum of powers of 100. -/
private theorem geometric (h : ℕ) :
    99 * (∑ k ∈ range (2*h), if k%2=0 then (10:ℤ)^k else 0) + 1 = 10^(2*h) := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [show 2*(h+1)=2*h+1+1 by omega,sum_range_succ,sum_range_succ,
      if_neg (show ¬(2*h+1)%2=0 by omega),if_pos (show (2*h)%2=0 by omega),
      show 2*h+1+1=2*h+2 by omega,pow_add (10:ℤ) (2*h) 2]
    linarith

theorem even_value (h : ℕ)
    (hp : ∀ k : ℕ, k ≤ 2*h → cell 553 (2*h) ((k:ℤ)-2*h) 0 = decide (2≤k ∧ k%2=0)) :
    (a (2*h) : ℚ) = ((10:ℚ)^(2*h)-1)/99 := by
  have hs : a (2*h) = ∑ k ∈ range (2*h), if k%2=0 then (10:ℤ)^k else 0 := by
    let d (k : ℕ) : ℤ := if k < 2*h ∧ k%2=0 then 10^k else 0
    have hr : ∑ k ∈ range (2*h+1), d k =
        ∑ k ∈ range (2*h), if k%2=0 then (10:ℤ)^k else 0 := by
      rw [sum_range_succ]
      simp only [d,lt_irrefl,false_and,if_false,add_zero]
      apply sum_congr rfl
      intro k hk
      simp [mem_range.mp hk]
    rw [←hr,←sum_range_reflect d (2*h+1),a]
    apply sum_congr rfl
    intro k hk
    have hb := mem_range.mp hk
    have e : 2*h+1-1=2*h := by omega
    have g : (2*h-k < 2*h ∧ (2*h-k)%2=0) ↔ (2≤k ∧ k%2=0) := by omega
    simp only [d,e,g,Nat.cast_mul,Nat.cast_ofNat,hp k (by omega),decide_eq_true_eq]
  have hv := geometric h
  rw [←hs] at hv
  have hq : 99*(a (2*h):ℚ)+1 = 10^(2*h) := by exact_mod_cast hv
  linarith

theorem odd_value (h : ℕ)
    (hp : ∀ k : ℕ, k ≤ 2*h+1 → cell 553 (2*h+1) ((k:ℤ)-(2*h+1)) 0 = false) :
    (a (2*h+1):ℚ) = 0 := by
  suffices a (2*h+1) = 0 by exact_mod_cast this
  rw [a]
  apply sum_eq_zero
  intro k hk
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,hp k (by have := mem_range.mp hk; omega)]
  rfl

end Rule553

namespace Rule553

open OMA.S_oeis_a282088 PowerSeries

theorem finish (hz : (a 0 : ℚ) = 1)
    (he : ∀ h : ℕ, 1 ≤ h → (a (2*h) : ℚ) = ((10:ℚ)^(2*h)-1)/99)
    (ho : ∀ h : ℕ, (a (2*h+1) : ℚ) = 0) : type_of% @OMA.S_oeis_a282088.main := by
  let v (n : ℕ) : ℚ := if n=0 then 1 else if n%2=0 then (10^n-1)/99 else 0
  have av (n : ℕ) : (a n : ℚ) = v n := by
    by_cases hn : n=0
    · subst n
      simpa [v] using hz
    · rcases Nat.even_or_odd n with ⟨h, e⟩ | ⟨h, e⟩
      · have f : n = 2*h := by omega
        rw [f]
        simpa [v, show h ≠ 0 by omega] using he h (by omega)
      · have f : n = 2*h+1 := by omega
        rw [f]
        simpa (disch := omega) [v] using ho h
  have relation (n : ℕ) (hn : 5≤n) : v n = 101 * v (n-2) - 100 * v (n-4) := by
    obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
    rw [show k+4-2=k+2 by omega,show k+4-4=k by omega]
    by_cases p : k%2=0
    · simp (disch := omega) only [v,if_neg,if_pos]
      rw [pow_add,pow_add]
      ring
    · simp (disch := omega) only [v,if_neg,mul_zero,sub_zero]
  refine ⟨fun n hn => ?_, ?_, ?_, ?_⟩
  · simpa only [av] using relation n hn
  · rintro n hn ⟨h,e⟩
    have f : n=2*h := by omega
    simpa only [f] using he h (by omega)
  · rintro n ⟨h,e⟩
    have f : n=2*h+1 := by omega
    simpa only [f] using ho h
  · let G : PowerSeries ℚ := mk v
    have den : G*((1-X)*(1+X)*(1-10*X)*(1+10*X)) =
        G - C 101*(G*X^2) + C 100*(G*X^4) := by simp only [map_ofNat]; ring
    have num : (1 - 100*X^2 + 100*X^4 : PowerSeries ℚ) =
        C 1 - C 100*X^2 + C 100*X^4 := by simp only [map_one,map_ofNat]
    simp only [av]
    change G*_ = _
    rw [den,num]
    ext n
    simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_C,G,coeff_mk]
    by_cases hn : n<5
    · interval_cases n <;> norm_num [v]
    · simp (disch := omega) only [if_pos,if_neg,sub_zero,add_zero]
      linarith only [relation n (by omega)]

end Rule553

open Rule553 OMA.S_oeis_a282088 in
theorem OMA.solution : type_of% @OMA.S_oeis_a282088.main := by
  apply finish
  · norm_num [a,cell]
  · exact fun h hh => even_value h (fun k hk => ebit h k hh hk)
  · exact fun h => odd_value h (fun k hk => obit h k hk)
