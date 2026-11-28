import OMAStatements.S_oeis_a273481
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

open OMA.S_oeis_a273481

namespace OMA.A273481

private abbrev Point := ℤ × ℤ

private def picture (background : Bool) (exceptions : List Point) (p : Point) : Bool :=
  if p ∈ exceptions then !background else background

private def update (r : ℕ) (f : Point → Bool) (p : Point) : Bool :=
  ruleOf r (f p) ((nbrs p).countP f)

private theorem adjacent_symm {p q : Point} (h : q ∈ nbrs p) : p ∈ nbrs q := by
  rcases p with ⟨x,y⟩
  simp only [nbrs,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [nbrs]

/-- Only exceptional cells and their neighbors can change the uniform background update. -/
private def candidates (before after : List Point) :=
  after ++ before.flatMap (fun q => q :: nbrs q)

private theorem advance {r : ℕ} {b c : Bool} {xs ys : List Point}
    (background : ruleOf r b (if b then 4 else 0) = c)
    (finiteCheck : ∀ p ∈ candidates xs ys, update r (picture b xs) p = picture c ys p) :
    update r (picture b xs) = picture c ys := by
  funext p
  by_cases hp : p ∈ candidates xs ys
  · exact finiteCheck p hp
  have hy : p ∉ ys := fun h => hp (List.mem_append_left _ h)
  have away (q : Point) (hq : q ∈ xs) : p ∉ q :: nbrs q := by
    intro h
    exact hp (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q,hq,h⟩))
  have hx : p ∉ xs := fun h => away p h (by simp)
  have hn (q : Point) (hq : q ∈ nbrs p) : q ∉ xs :=
    fun h => away q h (List.mem_cons_of_mem _ (adjacent_symm hq))
  have cnt : (nbrs p).countP (picture b xs) = (nbrs p).countP (fun _ => b) :=
    List.countP_congr (fun q hq => by simp [picture,hn q hq])
  unfold update
  rw [cnt]
  cases b <;> simpa [picture,hx,hy,nbrs] using background

private theorem liftStep (r t : ℕ) {f g : Point → Bool}
    (h : stateOf r t = f) (e : update r f = g) : stateOf r (t+1) = g := by
  funext p
  change update r (stateOf r t) p = g p
  rw [h,e]

private def center : List Point := [(0,0)]
private def cross : List Point := [(-1,0),(0,-1),(0,1),(1,0)]
private def corners : List Point := [(-1,-1),(-1,1),(1,-1),(1,1)]

private theorem initial (r : ℕ) : stateOf r 0 = picture false center := by
  funext p
  simp [stateOf,picture,center]

private theorem baseState (t : ℕ) : state t = stateOf 737 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    change ruleOf 737 (state t p) ((nbrs p).countP (state t)) = _
    rw [ih]
    rfl

private theorem baseCount (n : ℕ) : a n = aOf 737 n := by
  simp only [a,aOf,baseState]

private def squareSum (s : ℕ) (f : Point → ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2*s+1), ∑ y ∈ Finset.range (2*s+1), f ((x:ℤ)-s,(y:ℤ)-s)

private def inSquare (s : ℕ) (q : Point) : Prop :=
  -(s:ℤ) ≤ q.1 ∧ q.1 ≤ s ∧ -(s:ℤ) ≤ q.2 ∧ q.2 ≤ s

private theorem oneCell (s : ℕ) (q : Point) (hq : inSquare s q) :
    squareSum s (fun p => if p=q then 1 else 0) = 1 := by
  obtain ⟨a,b,c,d⟩ := hq
  let i := ((s:ℤ)+q.1).toNat
  let j := ((s:ℤ)+q.2).toNat
  have hi : (i:ℤ) = s+q.1 := Int.toNat_of_nonneg (by omega)
  have hj : (j:ℤ) = s+q.2 := Int.toNat_of_nonneg (by omega)
  have im : i ∈ Finset.range (2*s+1) := Finset.mem_range.mpr (by omega)
  have jm : j ∈ Finset.range (2*s+1) := Finset.mem_range.mpr (by omega)
  have point (x y : ℕ) : ((x:ℤ)-s,(y:ℤ)-s)=q ↔ x=i ∧ y=j := by
    rw [Prod.ext_iff]
    change ((x:ℤ)-s=q.1 ∧ (y:ℤ)-s=q.2) ↔ _
    omega
  unfold squareSum
  simp_rw [point,ite_and]
  simp [Finset.sum_ite_irrel,im,jm]

private theorem litCount (s : ℕ) (xs : List Point) (nodup : xs.Nodup)
    (bounds : ∀ q ∈ xs, inSquare s q) :
    squareSum s (fun p => if picture true xs p then 1 else 0) + xs.length = (2*s+1)^2 := by
  induction xs with
  | nil => simp [squareSum,picture,pow_two]
  | cons q xs ih =>
    obtain ⟨outside,hn⟩ := List.nodup_cons.mp nodup
    have hh := oneCell s q (bounds q (by simp))
    have countTail := ih hn (fun v hv => bounds v (by simp [hv]))
    have plus (p : Point) :
        (if picture true (q::xs) p then 1 else 0) + (if p=q then 1 else 0) =
          (if picture true xs p then 1 else 0 : ℕ) := by
      by_cases h : p=q <;> by_cases hm : p ∈ xs <;> simp_all [picture]
    have add : squareSum s (fun p => if picture true (q::xs) p then 1 else 0) +
        squareSum s (fun p => if p=q then 1 else 0) =
          squareSum s (fun p => if picture true xs p then 1 else 0) := by
      simp only [squareSum,← Finset.sum_add_distrib,plus]
    rw [hh] at add
    simp only [List.length_cons]
    omega

private def darkRing : List Point := cross ++ corners

private theorem fixedAfter {r : ℕ} {f : Point → Bool}
    (h : stateOf r 2 = f) (fixed : update r f = f) (t : ℕ) (ht : 2 ≤ t) : stateOf r t = f := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction k with
  | zero => exact h
  | succ k ih => exact liftStep r _ ih fixed

private def total (r t : ℕ) : ℕ := squareSum t (fun p => if stateOf r t p then 1 else 0)

private theorem difference {r n : ℕ} (hn : 2 ≤ n) {xs : List Point}
    (fixed : ∀ t ≥ 2, stateOf r t = picture true xs)
    (distinct : xs.Nodup) (nearby : ∀ t ≥ 2, ∀ p ∈ xs, inSquare t p) :
    aOf r n = 8*(1+(n:ℤ)) := by
  have count (t : ℕ) (ht : 2 ≤ t) : (total r t : ℤ) + xs.length = (2*(t:ℤ)+1)^2 := by
    have raw : total r t + xs.length = (2*t+1)^2 := by
      unfold total
      rw [fixed t ht]
      exact litCount t xs distinct (nearby t ht)
    exact_mod_cast raw
  have u := count n hn
  have v := count (n+1) (by omega)
  push_cast at v
  change (total r (n+1) : ℤ) - total r n = _
  linarith only [u,v]

private theorem layer737_1 : stateOf 737 1 = picture true (center ++ cross) :=
  liftStep 737 0 (initial 737) (advance (by decide) (by decide))

private theorem layer737_2 : stateOf 737 2 = picture true [] :=
  liftStep 737 1 (layer737_1) (advance (by decide) (by decide))

private theorem diff737 (n : ℕ) (hn : 2 ≤ n) : aOf 737 n = 8*(1+(n:ℤ)) := by
  apply difference hn (xs:=[])
  · exact fixedAfter layer737_2 (advance (by decide) (by decide))
  · decide
  · simp

private theorem layer643_1 : stateOf 643 1 = picture true cross :=
  liftStep 643 0 (initial 643) (advance (by decide) (by decide))

private theorem layer643_2 : stateOf 643 2 = picture true darkRing :=
  liftStep 643 1 (layer643_1) (advance (by decide) (by decide))

private theorem diff643 (n : ℕ) (hn : 2 ≤ n) : aOf 643 n = 8*(1+(n:ℤ)) := by
  apply difference hn (xs:=darkRing)
  · exact fixedAfter layer643_2 (advance (by decide) (by decide))
  · decide
  · intro t ht q hq
    simp [darkRing,cross,corners] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold inSquare <;> dsimp <;> omega

private theorem formula (n : ℕ) (h : 2 ≤ n) : a n = 8*(1+(n:ℤ)) := by
  rw [baseCount,diff737 n h]

private theorem recurrence (n : ℕ) (hn : 3 < n) : a n = 2*a (n-1)-a (n-2) := by
  rw [formula n (by omega),formula (n-1) (by omega),formula (n-2) (by omega)]
  push_cast [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub (by omega : 2 ≤ n)]
  ring

open PowerSeries

private theorem generating : A = (3 + 15*X - 15*X^2 + 5*X^3) * ((1-X)^2)⁻¹ := by
  have c0 : a 0 = 3 := by decide
  have c1 : a 1 = 21 := by decide
  have form (n : ℕ) (h : 2 ≤ n) : (a n : ℚ) = 8*(1+(n:ℚ)) := by exact_mod_cast formula n h
  have fs : A * (1-X)^2 = (3 + 15*X - 15*X^2 + 5*X^3) := by
    have num : (3 + 15*X - 15*X^2 + 5*X^3) = (C (3:ℚ) + C (15:ℚ) * X^1 + C (-15:ℚ) * X^2 + C (5:ℚ) * X^3 : ℚ⟦X⟧) := by
      simp only [map_ofNat,map_neg]
      ring
    rw [num,show A * (1-X)^2 = A - A*X^1 - A*X^1 + A*X^2 by ring]
    ext n
    simp only [map_add,map_sub,coeff_mul_X_pow',coeff_C,A,coeff_mk]
    by_cases h : n < 4
    · interval_cases n <;> norm_num [c0,c1,form 2 (by decide),form 3 (by decide)]
    · have hn : 2 ≤ n-2 := by omega
      have hm : 2 ≤ n-1 := by omega
      have hl : 2 ≤ n := by omega
      simp [show 1 ≤ n by omega,hl,show 3 ≤ n by omega,show n ≠ 0 by omega,
        show n-1 ≠ 0 by omega,show n-2 ≠ 0 by omega,show n-3 ≠ 0 by omega,
        form n hl,form (n-1) hm,form (n-2) hn,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_sub hl]
      ring
  rw [← fs,mul_assoc,PowerSeries.mul_inv_cancel _ (by simp),mul_one]

end OMA.A273481

theorem OMA.solution : type_of% @OMA.S_oeis_a273481.main := by
  open OMA.A273481 in
    refine ⟨fun n hn => ?_,fun n hn => ?_,recurrence,generating⟩
    · exact_mod_cast formula n hn
    · rw [formula n hn,diff643 n hn]
