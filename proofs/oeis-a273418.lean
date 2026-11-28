import OMAStatements.S_oeis_a273418
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

open OMA.S_oeis_a273418

namespace OMA.A273418

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

private theorem baseState (t : ℕ) : state t = stateOf 705 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext p
    change ruleOf 705 (state t p) ((nbrs p).countP (state t)) = _
    rw [ih]
    rfl

private theorem baseCount (n : ℕ) : a n = aOf 705 n := by
  simp only [a,aOf,baseState]

private theorem twoCycle {r t : ℕ} {f g : Point → Bool}
    (first : stateOf r t = f) (fg : update r f = g) (gf : update r g = f) (k : ℕ) :
    stateOf r (t+2*k) = f := by
  induction k with
  | zero => simpa using first
  | succ k ih =>
    rw [show t+2*(k+1)=(t+2*k+1)+1 by omega]
    exact liftStep r _ (liftStep r _ ih fg) gf

private theorem sampled {n : ℕ} (hn : 2 ≤ n) : ∃ k, 2^n-1=3+2*k := by
  obtain ⟨j,rfl⟩ : ∃ j, n=j+2 := ⟨n-2, by omega⟩
  have h : 0 < 2^j := pow_pos (by decide) _
  exact ⟨2*2^j-2, by simp only [pow_succ]; omega⟩

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

private theorem layer705_1 : stateOf 705 1 = picture true (center ++ cross) :=
  liftStep 705 0 (initial 705) (advance (by decide) (by decide))

private theorem layer705_2 : stateOf 705 2 = picture true corners :=
  liftStep 705 1 (layer705_1) (advance (by decide) (by decide))

private theorem layer705_3 : stateOf 705 3 = picture true (cross ++ corners) :=
  liftStep 705 2 (layer705_2) (advance (by decide) (by decide))

private theorem sampled705 (n : ℕ) (hn : 2 ≤ n) :
    stateOf 705 (2^n-1) = picture true (cross ++ corners) := by
  obtain ⟨k,hk⟩ := sampled hn
  rw [hk]
  exact twoCycle (g := picture true (center ++ cross ++ corners)) layer705_3
    (advance (by decide) (by decide)) (advance (by decide) (by decide)) k

private theorem layer713_1 : stateOf 713 1 = picture true (center ++ cross) :=
  liftStep 713 0 (initial 713) (advance (by decide) (by decide))

private theorem layer713_2 : stateOf 713 2 = picture true corners :=
  liftStep 713 1 (layer713_1) (advance (by decide) (by decide))

private theorem layer713_3 : stateOf 713 3 = picture true (cross ++ corners) :=
  liftStep 713 2 (layer713_2) (advance (by decide) (by decide))

private theorem sampled713 (n : ℕ) (hn : 2 ≤ n) :
    stateOf 713 (2^n-1) = picture true (cross ++ corners) := by
  obtain ⟨k,hk⟩ := sampled hn
  rw [hk]
  exact twoCycle (g := picture true (center ++ cross ++ corners)) layer713_3
    (advance (by decide) (by decide)) (advance (by decide) (by decide)) k

private theorem layer643_1 : stateOf 643 1 = picture true cross :=
  liftStep 643 0 (initial 643) (advance (by decide) (by decide))

private theorem layer643_2 : stateOf 643 2 = picture true (cross ++ corners) :=
  liftStep 643 1 (layer643_1) (advance (by decide) (by decide))

private theorem layer643_3 : stateOf 643 3 = picture true (cross ++ corners) :=
  liftStep 643 2 (layer643_2) (advance (by decide) (by decide))

private theorem sampled643 (n : ℕ) (hn : 2 ≤ n) :
    stateOf 643 (2^n-1) = picture true (cross ++ corners) := by
  obtain ⟨k,hk⟩ := sampled hn
  rw [hk]
  exact twoCycle (g := picture true (cross ++ corners)) layer643_3
    (advance (by decide) (by decide)) (advance (by decide) (by decide)) k

private theorem countLarge (n : ℕ) (hn : 2 ≤ n) :
    aOf 705 n + 8 = (2*(2^n-1)+1)^2 := by
  have ps := sampled705 n hn
  have hs : 1 ≤ 2^n-1 := by obtain ⟨k,hk⟩ := sampled hn; omega
  change squareSum (2^n-1) (fun p => if stateOf 705 (2^n-1) p then 1 else 0) + 8 = _
  rw [ps]
  apply litCount _ (cross ++ corners) (by decide)
  intro q hq
  simp [cross,corners] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold inSquare <;> dsimp <;> omega

end OMA.A273418

theorem OMA.solution : type_of% @OMA.S_oeis_a273418.main := by
  open OMA.A273418 in
    refine ⟨?_,?_,?_⟩
    · intro n
      rw [baseCount]
      by_cases h : 2 ≤ n
      · simp only [aOf,sampled713 _ h,sampled705 _ h]
      · interval_cases n <;> decide
    · intro n h
      simp only [baseCount,aOf,sampled705 _ h,sampled643 _ h]
    · intro n hn
      rw [baseCount]
      have hc := countLarge n hn
      have hp : 1 ≤ 2^n := Nat.one_le_two_pow
      have e : (aOf 705 n : ℚ) + 8 = ((2*(2^n-1)+1 : ℕ) : ℚ)^2 := by exact_mod_cast hc
      push_cast [Nat.cast_sub hp] at e
      rw [show (4:ℚ)^n = ((2:ℚ)^n)^2 by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num]
      linarith only [e]
