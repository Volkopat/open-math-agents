import OMAStatements.S_oeis_a273848
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

open OMA.S_oeis_a273848

namespace OMA.A273848

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

private theorem baseState (t : ℕ) : state t = stateOf 969 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    change ruleOf 969 (state t p) ((nbrs p).countP (state t)) = _
    rw [ih]
    rfl

private theorem baseCount (n : ℕ) : a n = aOf 969 n := by
  simp only [a,aOf,baseState]

private theorem layer969_1 : stateOf 969 1 = picture true (center ++ cross) :=
  liftStep 969 0 (initial 969) (advance (by decide) (by decide))

private theorem layer969_2 : stateOf 969 2 = picture true corners :=
  liftStep 969 1 (layer969_1) (advance (by decide) (by decide))

private theorem layer969_3 : stateOf 969 3 = picture true cross :=
  liftStep 969 2 (layer969_2) (advance (by decide) (by decide))

private theorem layer969_4 : stateOf 969 4 = picture true (center ++ corners) :=
  liftStep 969 3 (layer969_3) (advance (by decide) (by decide))

private theorem layer969_5 : stateOf 969 5 = picture true [] :=
  liftStep 969 4 (layer969_4) (advance (by decide) (by decide))

private theorem full969 (t : ℕ) (h : 5 ≤ t) : stateOf 969 t = picture true [] := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact layer969_5
  | succ k ih => exact liftStep 969 _ ih (advance (by decide) (by decide))

private theorem layer985_1 : stateOf 985 1 = picture true (center ++ cross) :=
  liftStep 985 0 (initial 985) (advance (by decide) (by decide))

private theorem layer985_2 : stateOf 985 2 = picture true corners :=
  liftStep 985 1 (layer985_1) (advance (by decide) (by decide))

private theorem layer985_3 : stateOf 985 3 = picture true cross :=
  liftStep 985 2 (layer985_2) (advance (by decide) (by decide))

private theorem layer985_4 : stateOf 985 4 = picture true (center ++ corners) :=
  liftStep 985 3 (layer985_3) (advance (by decide) (by decide))

private theorem layer985_5 : stateOf 985 5 = picture true [] :=
  liftStep 985 4 (layer985_4) (advance (by decide) (by decide))

private theorem full985 (t : ℕ) (h : 5 ≤ t) : stateOf 985 t = picture true [] := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact layer985_5
  | succ k ih => exact liftStep 985 _ ih (advance (by decide) (by decide))

private theorem countFull (r n : ℕ)
    (h : stateOf r (2^n-1) = picture true []) :
    aOf r n = (2*(2^n-1)+1)^2 := by
  simp [aOf,h,picture,pow_two]

private theorem late (n : ℕ) (hn : 2 < n) : 5 ≤ 2^n-1 := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ n by omega)
  change 8 ≤ 2^n at h
  omega

end OMA.A273848

theorem OMA.solution : type_of% @OMA.S_oeis_a273848.main := by
  open OMA.A273848 in
    constructor
    · intro n
      rw [baseCount]
      by_cases h : 2 < n
      · rw [countFull _ _ (full969 _ (late n h)),countFull _ _ (full985 _ (late n h))]
      · interval_cases n <;> decide
    · intro n hn
      rw [baseCount,countFull _ _ (full969 _ (late n hn))]
      have hp : 0 < 2^n := pow_pos (by decide) _
      rw [Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ 2^n)]
      push_cast
      rw [show (4:ℚ)^n = ((2:ℚ)^n)^2 by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num]
      ring
