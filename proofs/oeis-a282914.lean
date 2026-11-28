import OMAStatements.S_oeis_a282914


/-!
# The horizontal binary word of Rule 526

This proves Colin Barker's recurrence and generating function for Robert
Price's A282914 (https://oeis.org/A282914). Behind the right edge, the
axis has a period-four stripe, and the first and second rows away from
it alternate with opposite parities. These three rows are stable under
the update whatever the remaining cells do. A finite moving-edge orbit
supplies the boundary conditions. The low six bits and the settled
prefix give the binary first-order correction and hence both targets.
The method of certifying the finite moving edge and grid is adapted from
https://github.com/lefttosolve2/open-math-agents/pull/32902.
-/

namespace Rule526
open OMA.S_oeis_a282914

def step (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (526 : ℕ).testBit ((f x y).toNat + 2*((f (x+1) y).toNat +
    (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat))

theorem cell_step (t : ℕ) : cell 526 (t+1) = step (cell 526 t) := rfl

def stripe (x y : ℤ) : Bool :=
  if y=0 then decide (x%4≠2) else if y=1 then decide (x%2=0) else decide (x%2=1)

end Rule526

namespace Rule526
open OMA.S_oeis_a282914

theorem mirrorX (t : ℕ) (x y : ℤ) : cell 526 t (-x) y = cell 526 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -x+1 = -(x-1) by omega, show -x-1 = -(x+1) by omega,ih]
    ac_rfl

theorem mirrorY (t : ℕ) (x y : ℤ) : cell 526 t x (-y) = cell 526 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -y+1 = -(y-1) by omega, show -y-1 = -(y+1) by omega,ih]
    ac_rfl

private theorem adjacent_abs (u v : ℤ) (hl : u-1≤v) (hr : v≤u+1) : |u| ≤ |v|+1 := by
  have hv := abs_le.mp (le_refl |v|)
  exact abs_le.mpr (by omega)

theorem outside (t : ℕ) (x y : ℤ) (h : (t:ℤ) < |x| + |y|) :
    cell 526 t x y = false := by
  induction t generalizing x y with
  | zero =>
    change decide (x=0 ∧ y=0) = false
    apply decide_eq_false
    rintro ⟨rfl,rfl⟩
    simp at h
  | succ t ih =>
    have xp := adjacent_abs x (x+1) (by omega) (by omega)
    have xm := adjacent_abs x (x-1) (by omega) (by omega)
    have yp := adjacent_abs y (y+1) (by omega) (by omega)
    have ym := adjacent_abs y (y-1) (by omega) (by omega)
    simp only [cell,ih x y (by omega),ih (x+1) y (by omega),ih (x-1) y (by omega),
      ih x (y+1) (by omega),ih x (y-1) (by omega)]
    decide

end Rule526

namespace Rule526
open OMA.S_oeis_a282914 Finset

/-- One quadrant per time step, with consecutive bits indexed by the y-coordinate. -/
private def table : ℕ → ℕ
  | 0 => 0x1
  | 1 => 0x803
  | 2 => 0x400807
  | 3 => 0x200c0200d
  | 4 => 0x100200802019
  | 5 => 0x8030020080a83b
  | 6 => 0x4008070020480a87b
  | 7 => 0x200c0200d02a0e8228db
  | 8 => 0x10020080200902a0a82299b
  | 9 => 0x8030020080280b02a0a8aabbb
  | 10 => 0x4008070020080280b02a4a8aafbb
  | _ => 0

private def preview (t : ℕ) (x y : ℤ) : Bool :=
  if t=0 then decide (x=0 ∧ y=0)
  else if (t:ℤ) < |x|+|y| then false
  else (table t).testBit (11*x.natAbs+y.natAbs)

private theorem checked (t : Fin 10) (i : Fin 11) : ∀ j : Fin 11,
    step (preview t) i j = preview (t.val+1) i j := by
  fin_cases t <;> fin_cases i <;> decide +kernel

private theorem cell_abs (t : ℕ) (x y : ℤ) : cell 526 t |x| |y| = cell 526 t x y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp only [abs_of_nonneg,abs_of_nonpos,hx,hy,mirrorX,mirrorY]

private theorem preview_abs (t : ℕ) (x y : ℤ) : preview t |x| |y| = preview t x y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp [preview,abs_of_nonneg,abs_of_nonpos,hx,hy]

private theorem cell_preview (t : ℕ) (ht : t≤10) : cell 526 t = preview t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x y
    rw [← cell_abs (t+1) x y,← preview_abs (t+1) x y]
    by_cases h : ((t+1:ℕ):ℤ) < |x|+|y|
    · rw [outside (t+1) _ _ (by simpa only [abs_abs] using h)]
      simp only [preview,Nat.succ_ne_zero,if_false,abs_abs,h,if_true]
    · have hx : x.natAbs < 11 := by
        have he := Int.natCast_natAbs x
        have hp := abs_nonneg y
        omega
      have hy : y.natAbs < 11 := by
        have he := Int.natCast_natAbs y
        have hp := abs_nonneg x
        omega
      rw [cell_step,ih (by omega)]
      simpa only [Int.natCast_natAbs] using
        checked ⟨t,by omega⟩ ⟨x.natAbs,hx⟩ ⟨y.natAbs,hy⟩

theorem early_values (t : Fin 11) : a t =
    (![1,3,7,11,19,55,111,219,435,887,1775] : Fin 11 → ℤ) t := by
  unfold a
  rw [cell_preview _ (by omega)]
  fin_cases t <;> decide +kernel

end Rule526

namespace Rule526
open OMA.S_oeis_a282914

/-- In the right-moving frame, the first five stages are followed by an eight-cycle. -/
private def edgePhase (t : ℕ) : ℕ := if t < 5 then t else 5 + (t-5)%8

private def edgeRow (s : ℕ) (u y : ℤ) : Bool :=
  if u < 0 ∨ y < -6 ∨ 6 < y then false
  else if s=0 then decide (u=0 ∧ y=0)
  else (0x829908080810a0828d080c08b0a080870204a8b0a0808302a8a8908080818ae8a8d080c0fb2a480870204abb2a0808302082190808081020c20d080c08000040870204000000008302000000000001 : ℕ).testBit
    (49*s + 7*u.toNat + y.natAbs)

private def edgeUpdate (s : ℕ) (u y : ℤ) : Bool :=
  (526 : ℕ).testBit ((edgeRow s (u-1) y).toNat + 2*((edgeRow s (u-2) y).toNat +
    (edgeRow s u y).toNat + (edgeRow s (u-1) (y+1)).toNat +
    (edgeRow s (u-1) (y-1)).toNat))

private theorem edge_transition (s : Fin 13) (u y : ℤ) (hu : u ≤ 6) :
    edgeUpdate s u y = edgeRow (if s.val=12 then 5 else s.val+1) u y := by
  by_cases inner : 0 ≤ u ∧ -7 ≤ y ∧ y ≤ 7
  · let i : Fin 7 := ⟨u.toNat,by omega⟩
    let j : Fin 15 := ⟨(y+7).toNat,by omega⟩
    have hi : (i:ℤ) = u := by dsimp [i]; omega
    have hj : (j:ℤ)-7 = y := by dsimp [j]; omega
    have checked (q : Fin 13) (v : Fin 7) : ∀ w : Fin 15,
        edgeUpdate q v ((w:ℤ)-7) = edgeRow (if q.val=12 then 5 else q.val+1) v ((w:ℤ)-7) := by
      fin_cases q <;> fin_cases v <;> decide +kernel
    simpa only [hi,hj] using checked s i j
  · have off (q : ℕ) (v z : ℤ) (h : v < 0 ∨ z < -6 ∨ 6 < z) : edgeRow q v z = false := if_pos h
    simp only [edgeUpdate, off _ _ _ (show u-1<0 ∨ y < -6 ∨ 6<y by omega),
      off _ _ _ (show u<0 ∨ y < -6 ∨ 6<y by omega),
      off _ _ _ (show u-2<0 ∨ y < -6 ∨ 6<y by omega),
      off _ _ _ (show u-1<0 ∨ y+1 < -6 ∨ 6<y+1 by omega),
      off _ _ _ (show u-1<0 ∨ y-1 < -6 ∨ 6<y-1 by omega)]
    rfl

private theorem edge_live (t : ℕ) (u y : ℤ) (hu : u ≤ 6) :
    cell 526 t ((t:ℤ)-u) y = edgeRow (edgePhase t) u y := by
  induction t generalizing u y with
  | zero =>
    simp only [edgePhase,show 0<5 by decide,if_true,edgeRow,Nat.cast_zero,zero_sub,cell,neg_eq_zero]
    split_ifs with h
    · simp only [decide_eq_false_iff_not]; omega
    · rfl
  | succ t ih =>
    have hbound : edgePhase t < 13 := by unfold edgePhase; split <;> omega
    have hnext : edgePhase (t+1) = if edgePhase t=12 then 5 else edgePhase t+1 := by
      simp only [edgePhase]; split_ifs <;> omega
    rw [hnext,cell]
    dsimp only
    have ab : ((t+1:ℕ):ℤ)-u = (t:ℤ)-(u-1) := by omega
    have ar : ((t+1:ℕ):ℤ)-u+1 = (t:ℤ)-(u-2) := by omega
    have al : ((t+1:ℕ):ℤ)-u-1 = (t:ℤ)-u := by omega
    rw [ar,al,ab,ih (u-1) y (by omega),ih u y hu,ih (u-2) y (by omega),
      ih (u-1) (y+1) (by omega),ih (u-1) (y-1) (by omega)]
    exact edge_transition ⟨_,hbound⟩ u y hu

/-- The six low binary places, with the rightmost cell at bit zero. -/
def edgeBits (t : ℕ) : ℕ := [51,55,47,27][t%4]!

theorem edge_axis (t : ℕ) (u : Fin 6) (ht : 5≤t) :
    cell 526 t ((t:ℤ)-(u:ℤ)) 0 = (edgeBits t).testBit u.val := by
  rw [edge_live t u 0 (by omega)]
  let s : Fin 8 := ⟨(t-5)%8,by omega⟩
  have hphase : edgePhase t = 5+s.val := if_neg (by omega)
  have hs : (5+s.val)%4=t%4 := by dsimp [s]; omega
  have checked : ∀ (a : Fin 8) (j : Fin 6), edgeRow (5+a.val) j 0 =
      (edgeBits (5+a.val)).testBit j.val := by decide +kernel
  simpa only [hphase,edgeBits,hs] using checked s u

theorem edge_inner (t : ℕ) (u y : ℤ) (ht : u≤(t:ℤ)) (hu : 5≤u ∧ u≤6) (hy : 0≤y ∧ y≤2) :
    cell 526 t ((t:ℤ)-u) y = stripe ((t:ℤ)-u) y := by
  rw [edge_live t u y hu.2]
  let s : Fin 8 := ⟨(t-5)%8,by omega⟩
  let i : Fin 2 := ⟨(u-5).toNat,by omega⟩
  let j : Fin 3 := ⟨y.toNat,by omega⟩
  have hphase : edgePhase t = 5+s.val := if_neg (by omega)
  have hi : 5+(i:ℤ)=u := by dsimp [i]; omega
  have hj : (j:ℤ)=y := by dsimp [j]; omega
  have checked : ∀ (a : Fin 8) (v : Fin 2) (z : Fin 3), edgeRow (5+a.val) (5+(v:ℤ)) z =
      stripe (13+(a:ℤ)-(5+(v:ℤ))) z := by decide +kernel
  rw [hphase]
  calc
    edgeRow (5+s.val) u y = stripe (13+(s:ℤ)-u) y := by simpa only [hi,hj] using checked s i j
    _ = stripe ((t:ℤ)-u) y := by
      have h₄ : (13+(s:ℤ)-u)%4=((t:ℤ)-u)%4 := by dsimp [s]; omega
      have h₂ : (13+(s:ℤ)-u)%2=((t:ℤ)-u)%2 := by dsimp [s]; omega
      simp only [stripe,h₄,h₂]

end Rule526

namespace Rule526

/-- Each interior site of the three-row stripe reproduces its value.
Above the third row either neighbor value gives the same result. -/
theorem stripe_local (f : ℤ → ℤ → Bool) (x y : ℤ) (hy0 : 0 ≤ y) (hy2 : y ≤ 2)
    (localBits : ∀ u v : ℤ, x-1 ≤ u → u ≤ x+1 → 0 ≤ v → v ≤ 2 → f u v = stripe u v)
    (mirror : f x (-1) = f x 1) : step f x y = stripe x y := by
  have hneg : f x (-1) = stripe x 1 := mirror.trans (localBits _ _ (by omega) (by omega) (by decide) (by decide))
  have residue : x%4=0 ∨ x%4=1 ∨ x%4=2 ∨ x%4=3 := by omega
  cases h3 : f x 3 <;>
    interval_cases y <;>
    rcases residue with hm | hm | hm | hm <;>
    simp (disch := omega) only [step, Int.reduceAdd, Int.reduceSub, hneg, localBits, h3,
      stripe, if_neg, decide_eq_true, decide_eq_false] <;> decide

theorem stripe_reflect (x y : ℤ) : stripe (-x) y = stripe x y := by
  by_cases y0 : y=0
  · simp only [stripe, y0, if_true, decide_eq_decide]
    omega
  · by_cases y1 : y=1
    · simp only [stripe, if_neg y0, if_pos y1, decide_eq_decide]
      omega
    · simp only [stripe, if_neg y0, if_neg y1, decide_eq_decide]
      omega

end Rule526

namespace Rule526

open OMA.S_oeis_a282914

theorem stable_of_edge
    (edge : ∀ (t : ℕ) (u y : ℤ), u ≤ (t:ℤ) → 5 ≤ u ∧ u ≤ 6 → 0 ≤ y ∧ y ≤ 2 →
      cell 526 t ((t:ℤ)-u) y = stripe ((t:ℤ)-u) y)
    (t : ℕ) (x y : ℤ) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (hx : |x|+5 ≤ (t:ℤ)) :
    cell 526 t x y = stripe x y := by
  induction t generalizing x y with
  | zero =>
    have ha := abs_nonneg x
    omega
  | succ t ih =>
    by_cases near : (t:ℤ)+1-|x| ≤ 6
    · have ha := abs_nonneg x
      have atAbs := edge (t+1) ((t+1:ℕ)-|x|) y (by push_cast; omega)
        (by push_cast; omega) ⟨hy0,hy2⟩
      rw [sub_sub_cancel] at atAbs
      rcases le_total 0 x with xp | xn
      · simpa [abs_of_nonneg xp] using atAbs
      · simpa [abs_of_nonpos xn, mirrorX, stripe_reflect] using atAbs
    · rw [cell_step]
      apply stripe_local _ _ _ hy0 hy2
      · intro u v hu1 hu2 hv0 hv2
        apply ih u v hv0 hv2
        have bounds := abs_le.mp (le_refl |x|)
        have inside : |u| ≤ (t:ℤ)-5 := abs_le.mpr (by omega)
        omega
      · exact mirrorY t x 1

end Rule526

namespace Rule526

open OMA.S_oeis_a282914

theorem stable (t : ℕ) (x y : ℤ) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (hx : |x|+5 ≤ (t:ℤ)) :
    cell 526 t x y = stripe x y :=
  stable_of_edge edge_inner t x y hy0 hy2 hx

end Rule526

namespace Rule526
open OMA.S_oeis_a282914 Finset

/-- Value of the first m settled binary digits, from the origin outwards. -/
def prefixValue (m : ℕ) : ℤ :=
  ∑ k ∈ range m, if k%4≠2 then (2:ℤ)^(m-1-k) else 0

theorem prefix_succ (m : ℕ) :
    prefixValue (m+1) = 2*prefixValue m + (if m%4≠2 then 1 else 0) := by
  simp only [prefixValue,sum_range_succ,mul_sum]
  congr 1
  · apply sum_congr rfl
    intro k hk
    have h := mem_range.mp hk
    rw [show m+1-1-k=(m-1-k)+1 by omega,pow_succ]
    split_ifs <;> ring
  · simp

/-- Paste a settled prefix together with the six bit positions at the right edge. -/
theorem paste (packet : ℕ → ℕ)
    (inside : ∀ t k : ℕ, k+5 ≤ t → cell 526 t k 0 = decide (k%4≠2))
    (front : ∀ (t : ℕ) (u : Fin 6), 5≤t →
      cell 526 t ((t:ℤ)-(u:ℤ)) 0=(packet t).testBit u.val)
    (readout : ∀ t : ℕ, (∑ k ∈ range 6, if (packet t).testBit (5-k) then (2:ℤ)^(5-k) else 0)
      = (packet t:ℤ)) (m : ℕ) :
    a (m+5) = 64*prefixValue m + (packet (m+5):ℤ) := by
  rw [a,show m+5+1=m+6 by omega,sum_range_add,prefixValue,mul_sum,← readout]
  congr 1
  · apply sum_congr rfl
    intro k hk
    have h := mem_range.mp hk
    rw [inside _ _ (by omega),show m+5-k=(m-1-k)+6 by omega,pow_add]
    by_cases he : k%4=2
    · simp [he]
    · simp [he]
      ring
  · apply sum_congr rfl
    intro k hk
    have h := mem_range.mp hk
    let u : Fin 6 := ⟨5-k,by omega⟩
    have e := front (m+5) u (by omega)
    have ex : ((m+5:ℕ):ℤ) - (u:ℤ) = (m+k:ℕ) := by dsimp [u]; omega
    rw [ex] at e
    rw [e]
    change (if (packet (m+5)).testBit (5-k) then (2:ℤ)^(m+5-(m+k)) else 0) = _
    rw [show m+5-(m+k)=5-k by omega]

end Rule526

namespace Rule526
open PowerSeries OMA.S_oeis_a282914 Finset

def firstTerms : Fin 11 → ℤ := ![1,3,7,11,19,55,111,219,435,887,1775]
def edgeNat (t : ℕ) : ℕ := [51,55,47,27][t%4]!
def changeAt (n : ℕ) : ℤ := [17,1,-3,-3][n%4]!

theorem read_packet (t : ℕ) : (∑ k ∈ range 6,
    if (edgeNat t).testBit (5-k) then (2:ℤ)^(5-k) else 0) = (edgeNat t : ℤ) := by
  have h : t%4=0 ∨ t%4=1 ∨ t%4=2 ∨ t%4=3 := by omega
  rcases h with h|h|h|h <;> simp only [edgeNat,h] <;> decide +kernel

theorem increments (init : ∀ t : Fin 11, a t=firstTerms t)
    (pack : ∀ m, a (m+5)=64*prefixValue m + (edgeNat (m+5):ℤ))
    (n : ℕ) (hn : 1≤n) : a (n+1) - 2*a n = changeAt n := by
  by_cases hl : n<5
  · have small : ∀ i : Fin 4,
        firstTerms ⟨i.val+2,by omega⟩ - 2*firstTerms ⟨i.val+1,by omega⟩ =
        changeAt (i.val+1) := by decide +kernel +revert
    have h1 := init ⟨n+1,by omega⟩
    have h0 := init ⟨n,by omega⟩
    change a (n+1)=_ at h1
    change a n=_ at h0
    rw [h1,h0]
    obtain ⟨j,rfl⟩ : ∃ j, n=j+1 := ⟨n-1,by omega⟩
    exact small ⟨j,by omega⟩
  · obtain ⟨m,rfl⟩ : ∃ m, n=m+5 := ⟨n-5,by omega⟩
    rw [show m+5+1=m+1+5 by omega,pack,pack,prefix_succ]
    have hp : m%4=0 ∨ m%4=1 ∨ m%4=2 ∨ m%4=3 := by omega
    rcases hp with h|h|h|h <;>
      simp (disch := omega) [edgeNat,changeAt,h,Nat.add_mod] <;> ring_nf <;> decide +kernel

theorem rec (inc : ∀ n : ℕ, 1≤n → a (n+1)-2*a n=changeAt n) (n : ℕ) (hn : 6≤n) :
    (a n : ℚ)=2*a (n-1)+a (n-4)-2*a (n-5) := by
  have h1 := inc (n-1) (by omega)
  have h2 := inc (n-5) (by omega)
  rw [show n-1+1=n by omega] at h1
  rw [show n-5+1=n-4 by omega] at h2
  have he : changeAt (n-1)=changeAt (n-5) := by
    simp only [changeAt,show (n-1)%4=(n-5)%4 by omega]
  rw [he,←h2] at h1
  exact_mod_cast (show a n=2*a (n-1)+a (n-4)-2*a (n-5) by linarith)

def gen : PowerSeries ℚ := mk (fun n => (a n:ℚ))

theorem solve (init : ∀ t : Fin 11, a t=firstTerms t)
    (pack : ∀ m, a (m+5)=64*prefixValue m+(edgeNat (m+5):ℤ)) :
    type_of% @OMA.S_oeis_a282914.main := by
  have rr := rec (increments init pack)
  refine ⟨rr,?_⟩
  have den : gen*((1-X)*(1+X)*(1-2*X)*(1+X^2)) =
      gen - C 2*(gen*X^1) - gen*X^4 + C 2*(gen*X^5) := by
    simp only [map_ofNat]; ring
  have num : (1+X+X^2-3*X^3-4*X^4+16*X^5 : PowerSeries ℚ) =
      C 1+X^1+X^2-C 3*X^3-C 4*X^4+C 16*X^5 := by simp only [map_ofNat,map_one,pow_one]
  change gen*_ = _
  rw [den,num]
  ext n
  simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_X_pow,coeff_C,gen,coeff_mk]
  by_cases h : n<6
  · have e (k : ℕ) (hk : k<11) : a k=firstTerms ⟨k,hk⟩ := init ⟨k,hk⟩
    interval_cases n <;> norm_num [e,firstTerms]
  · simp (disch := omega) only [if_pos,if_neg,add_zero,sub_zero]
    linarith only [rr n (by omega)]

end Rule526

open Rule526 in
theorem OMA.solution : type_of% @OMA.S_oeis_a282914.main := by
  apply solve early_values
  apply paste edgeNat _ edge_axis read_packet
  intro t k hk
  have h := stable t (k:ℤ) 0 (by decide) (by decide)
    (by rw [abs_of_nonneg (Int.natCast_nonneg k)]; exact_mod_cast hk)
  rw [h]
  change decide ((k:ℤ)%4≠2) = decide (k%4≠2)
  by_cases hp : k%4=2 <;> simp (disch := omega) only [decide_eq_true,decide_eq_false]
