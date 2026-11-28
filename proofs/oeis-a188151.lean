import OMAStatements.S_oeis_a188151

-- Credit: @Aryan-Poonacha
-- Five oriented moves specify a shape. Each shift of its bounding box gives one walk.
namespace GridSix
open OMA.S_oeis_a188151

abbrev Word := Fin 5 → Fin 4
abbrev Point := ℤ × ℤ

def unitDir : Fin 4 → Point := ![(1,0),(-1,0),(0,1),(0,-1)]
def direction (p : Point) : Fin 4 :=
  if p.1 = 1 then 0 else if p.1 = -1 then 1 else if p.2 = 1 then 2 else 3

theorem dir_unit (i : Fin 4) : direction (unitDir i) = i := by fin_cases i <;> rfl

theorem unit_dir (p : Point) (h : |p.1| + |p.2| = 1) : unitDir (direction p) = p := by
  obtain ⟨x,y⟩ := p
  change |x| + |y| = 1 at h
  have hx := abs_le.mp (show |x| ≤ 1 by linarith [abs_nonneg y])
  have hy := abs_le.mp (show |y| ≤ 1 by linarith [abs_nonneg x])
  obtain ⟨hx1,hx2⟩ := hx
  obtain ⟨hy1,hy2⟩ := hy
  interval_cases x <;> interval_cases y <;> norm_num [direction, unitDir] at * <;> rfl

def steps (s : Word) : ℕ → Point
  | 0 => 0
  | i+1 => steps s i + unitDir (s ⟨i % 5, Nat.mod_lt _ (by decide)⟩)

def atPos (s : Word) (i : Fin 6) := steps s i

theorem at_zero (s : Word) : atPos s 0 = 0 := rfl

theorem at_succ (s : Word) (i : Fin 5) :
    atPos s i.succ = atPos s i.castSucc + unitDir (s i) := by
  rcases i with ⟨i,hi⟩
  simp [atPos, steps, Nat.mod_eq_of_lt hi]

abbrev Shape := { s : Word // Function.Injective (atPos s) }

def lo (f : Fin 6 → ℤ) := Finset.univ.inf' Finset.univ_nonempty f
def hi (f : Fin 6 → ℤ) := Finset.univ.sup' Finset.univ_nonempty f
def span (f : Fin 6 → ℤ) : ℕ := (hi f - lo f).toNat

theorem lo_le (f : Fin 6 → ℤ) (i : Fin 6) : lo f ≤ f i :=
  Finset.inf'_le f (Finset.mem_univ i)
theorem le_hi (f : Fin 6 → ℤ) (i : Fin 6) : f i ≤ hi f :=
  Finset.le_sup' f (Finset.mem_univ i)

theorem span_eq (f : Fin 6 → ℤ) : (span f : ℤ) = hi f - lo f := by
  have h := (lo_le f 0).trans (le_hi f 0)
  simp [span, h]

def xpos (s : Word) (i : Fin 6) := (atPos s i).1
def ypos (s : Word) (i : Fin 6) := (atPos s i).2

abbrev Walk (n : ℕ) := {w : Fin 6 → Fin n × Fin n //
  Function.Injective w ∧ ∀ i : Fin 5, Adjacent (w i.castSucc) (w i.succ)}

def liftCell {n : ℕ} (p : Fin n × Fin n) : Point := (p.1,p.2)

theorem lift_inj {n : ℕ} : Function.Injective (@liftCell n) := by
  intro a b h
  apply Prod.ext <;> apply Fin.ext
  · have e : (a.1:ℤ) = (b.1:ℤ) := congrArg Prod.fst h
    exact_mod_cast e
  · have e : (a.2:ℤ) = (b.2:ℤ) := congrArg Prod.snd h
    exact_mod_cast e

def getWord {n : ℕ} (w : Walk n) (i : Fin 5) : Fin 4 :=
  direction (liftCell (w.val i.succ) - liftCell (w.val i.castSucc))

theorem get_step {n : ℕ} (w : Walk n) (i : Fin 5) :
    unitDir (getWord w i) = liftCell (w.val i.succ) - liftCell (w.val i.castSucc) := by
  apply unit_dir
  have h := w.property.2 i
  unfold Adjacent at h
  simpa [liftCell, abs_sub_comm] using h

theorem get_path {n : ℕ} (w : Walk n) (i : Fin 6) :
    liftCell (w.val i) = liftCell (w.val 0) + atPos (getWord w) i := by
  induction i using Fin.induction with
  | zero => simp [at_zero]
  | succ i ih =>
    rw [at_succ, get_step, ← add_assoc, ← ih]
    abel

def walkShape {n : ℕ} (w : Walk n) : Shape :=
  ⟨getWord w, fun i j e => w.property.1 (lift_inj (by rw [get_path w i, get_path w j, e]))⟩

abbrev Offset (n : ℕ) (f : Fin 6 → ℤ) := Fin (n - span f)

def toCell {n : ℕ} (f : Fin 6 → ℤ) (offset : Offset n f) (i : Fin 6) : Fin n :=
  ⟨((offset:ℤ) + f i - lo f).toNat, by
    have h := offset.isLt
    have h₁ := lo_le f i
    have h₂ := le_hi f i
    have h₃ := span_eq f
    omega⟩

theorem toCell_eq {n : ℕ} (f : Fin 6 → ℤ) (t : Offset n f) (i : Fin 6) :
    (toCell f t i : ℤ) = (t:ℤ) + f i - lo f := by
  have := lo_le f i
  change (((t:ℤ) + f i - lo f).toNat:ℤ) = _
  omega

theorem mkOffset_bound {n : ℕ} (f : Fin 6 → ℤ) (t : ℤ)
    (h : ∀ i, 0 ≤ t + f i ∧ t + f i < n) :
    0 ≤ t + lo f ∧ (t + lo f).toNat < n - span f := by
  obtain ⟨i, _, ei⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin 6))) Finset.univ_nonempty f
  obtain ⟨j, _, ej⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin 6))) Finset.univ_nonempty f
  change lo f = f i at ei
  change hi f = f j at ej
  have h₁ := (h i).1
  have h₂ := (h j).2
  have h₃ := span_eq f
  omega

abbrev Params (n : ℕ) := Σ s : Shape, Offset n (xpos s) × Offset n (ypos s)

def placeCell {n : ℕ} (v : Params n) (i : Fin 6) : Fin n × Fin n :=
  (toCell (xpos v.1.val) v.2.1 i, toCell (ypos v.1.val) v.2.2 i)

theorem placed_eq {n : ℕ} (v : Params n) (i : Fin 6) :
    liftCell (placeCell v i) =
      ((v.2.1:ℤ) - lo (xpos v.1.val), (v.2.2:ℤ) - lo (ypos v.1.val)) + atPos v.1.val i := by
  apply Prod.ext <;> simp [liftCell, placeCell, toCell_eq, xpos, ypos] <;> ring

def place {n : ℕ} (v : Params n) : Walk n :=
  ⟨placeCell v, by
    constructor
    · intro i j e
      have h := congrArg liftCell e
      rw [placed_eq, placed_eq] at h
      exact v.1.property (add_left_cancel h)
    · intro i
      have h : liftCell (placeCell v i.castSucc) - liftCell (placeCell v i.succ) =
          -unitDir (v.1.val i) := by
        rw [placed_eq, placed_eq, at_succ]
        abel
      have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      change (↑(placeCell v i.castSucc).1 : ℤ) - ↑(placeCell v i.succ).1 = _ at hx
      change (↑(placeCell v i.castSucc).2 : ℤ) - ↑(placeCell v i.succ).2 = _ at hy
      unfold Adjacent
      rw [hx, hy]
      generalize v.1.val i = k
      fin_cases k <;> decide⟩

theorem word_place {n : ℕ} (v : Params n) : getWord (place v) = v.1.val := by
  funext i
  unfold getWord
  change direction (liftCell (placeCell v i.succ) - liftCell (placeCell v i.castSucc)) = _
  rw [placed_eq, placed_eq, at_succ]
  rw [show ∀ a b c : Point, a + (b+c) - (a+b) = c by intros; abel, dir_unit]

theorem place_injective {n : ℕ} : Function.Injective (@place n) := by
  rintro ⟨s, x, y⟩ ⟨s', x', y'⟩ h
  have e : s = s' := Subtype.ext (by simpa only [word_place] using congrArg getWord h)
  subst s'
  have h0 := congrArg (fun w : Walk n => liftCell (w.val 0)) h
  change liftCell (placeCell ⟨s,x,y⟩ 0) = liftCell (placeCell ⟨s,x',y'⟩ 0) at h0
  rw [placed_eq, placed_eq, at_zero] at h0
  simp only [add_zero, Prod.mk.injEq, sub_left_inj] at h0
  have ex : x = x' := Fin.ext (by exact_mod_cast h0.1)
  have ey : y = y' := Fin.ext (by exact_mod_cast h0.2)
  subst x'; subst y'; rfl

theorem place_surjective {n : ℕ} : Function.Surjective (@place n) := by
  intro w
  let s := walkShape w
  let t := liftCell (w.val 0)
  have h : ∀ i, liftCell (w.val i) = t + atPos s.val i := get_path w
  have hx (i : Fin 6) : (↑(w.val i).1 : ℤ) = t.1 + xpos s.val i := congrArg Prod.fst (h i)
  have hy (i : Fin 6) : (↑(w.val i).2 : ℤ) = t.2 + ypos s.val i := congrArg Prod.snd (h i)
  have bx := mkOffset_bound (n := n) (xpos s.val) t.1 (fun i => by
    rw [← hx]; exact ⟨by positivity, by exact_mod_cast (w.val i).1.isLt⟩)
  have by' := mkOffset_bound (n := n) (ypos s.val) t.2 (fun i => by
    rw [← hy]; exact ⟨by positivity, by exact_mod_cast (w.val i).2.isLt⟩)
  let x : Offset n (xpos s.val) := ⟨_,bx.2⟩
  let y : Offset n (ypos s.val) := ⟨_,by'.2⟩
  refine ⟨⟨s,x,y⟩, Subtype.ext (funext fun i => lift_inj ?_)⟩
  change liftCell (placeCell ⟨s,x,y⟩ i) = _
  rw [placed_eq, h]
  congr 1
  apply Prod.ext
  · change (((t.1 + lo (xpos s.val)).toNat:ℤ) - lo (xpos s.val)) = t.1
    omega
  · change (((t.2 + lo (ypos s.val)).toNat:ℤ) - lo (ypos s.val)) = t.2
    omega

theorem count_shapes (n : ℕ) : a n = ∑ s : Shape, (n - span (xpos s)) * (n - span (ypos s)) := by
  calc
    a n = Fintype.card (Walk n) := (Fintype.card_subtype _).symm
    _ = Fintype.card (Params n) := (Fintype.card_congr (Equiv.ofBijective place
      ⟨place_injective, place_surjective⟩)).symm
    _ = _ := by simp [Params, Offset]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem span_bounds : ∀ s : Shape, span (xpos s) ≤ 5 ∧ span (ypos s) ≤ 5 := by
  decide +kernel

def placements (n : ℕ) (s : Shape) := (n - span (xpos s)) * (n - span (ypos s))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem census : Fintype.card Shape = 284 ∧
    (∑ s : Shape, ((5 - span (xpos s)) + (5 - span (ypos s)))) = 1612 ∧
    (∑ s : Shape, placements 5 s) = 2112 ∧
    (∑ s : Shape, placements 4 s) = 800 ∧
    (∑ s : Shape, placements 3 s) = 128 ∧
    (∑ s : Shape, placements 2 s) = 0 ∧
    (∑ s : Shape, placements 1 s) = 0 ∧
    (∑ s : Shape, placements 0 s) = 0 := by
  decide +kernel

theorem large_count (m : ℕ) : a (m + 5) = 284*m^2 + 1612*m + 2112 := by
  obtain ⟨hc, hd, he, _⟩ := census
  have expand (s : Shape) :
      (m+5 - span (xpos s)) * (m+5 - span (ypos s)) =
        m^2 + m * ((5 - span (xpos s)) + (5 - span (ypos s))) + placements 5 s := by
    have ⟨hx,hy⟩ := span_bounds s
    rw [show m+5-span (xpos s) = m+(5-span (xpos s)) by omega,
      show m+5-span (ypos s) = m+(5-span (ypos s)) by omega]
    unfold placements; ring
  rw [count_shapes]
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hd, he]
  simp [hc, Nat.mul_comm]

theorem quadratic (n : ℕ) (h : 5 ≤ n) :
    (a n : ℤ) = 284*(n:ℤ)^2 - 1228*(n:ℤ) + 1152 := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m+5 := ⟨n-5,by omega⟩
  rw [large_count]; push_cast; ring

theorem recurrence (n : ℕ) (h : 7 < n) :
    (a n : ℤ) = 3 * a (n-1) - 3 * a (n-2) + a (n-3) := by
  rw [quadratic n (by omega),quadratic (n-1) (by omega),quadratic (n-2) (by omega),
    quadratic (n-3) (by omega)]
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega)]
  ring

open PowerSeries

theorem generating_function :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X)^3 =
      8*X^3*(16+52*X+12*X^2-7*X^3-2*X^4) := by
  let A := PowerSeries.mk (fun n => (a n : ℤ))
  change A * (1-X)^3 = _
  have left' : A*(1-X)^3 =
      A - C 3*(A*X^1) + C 3*(A*X^2) - A*X^3 := by simp; ring
  have right' : (8*X^3*(16+52*X+12*X^2-7*X^3-2*X^4) : PowerSeries ℤ) =
      C 128*X^3 + C 416*X^4 + C 96*X^5 - C 56*X^6 - C 16*X^7 := by simp; ring
  rw [left',right']
  ext k
  simp only [map_sub,map_add,coeff_C_mul_X_pow]
  simp only [coeff_C_mul,coeff_mul_X_pow',A,coeff_mk]
  by_cases hk : k ≤ 7
  · obtain ⟨_,_,_,e4,e3,e2,e1,e0⟩ := census
    change (∑ s : Shape, placements 4 s) = _ at e4
    have hsmall (n : ℕ) : a n = ∑ s : Shape, placements n s := count_shapes n
    have h0 := (hsmall 0).trans e0
    have h1 := (hsmall 1).trans e1
    have h2 := (hsmall 2).trans e2
    have h3 := (hsmall 3).trans e3
    have h4 := (hsmall 4).trans e4
    have h5 : a 5 = 2112 := large_count 0
    have h6 : a 6 = 4008 := large_count 1
    have h7 : a 7 = 6472 := large_count 2
    interval_cases k <;> norm_num [h0,h1,h2,h3,h4,h5,h6,h7]
  · have hr := recurrence k (by omega)
    simp only [if_pos (show 1≤k by omega),if_pos (show 2≤k by omega),
      if_pos (show 3≤k by omega),if_neg (show k≠3 by omega),if_neg (show k≠4 by omega),
      if_neg (show k≠5 by omega),if_neg (show k≠6 by omega),if_neg (show k≠7 by omega)]
    linarith

end GridSix

theorem OMA.solution : type_of% @OMA.S_oeis_a188151.main :=
  ⟨GridSix.generating_function, GridSix.recurrence⟩
