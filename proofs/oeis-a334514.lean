import OMAStatements.S_oeis_a334514
import Mathlib

/-! Barker's conjectures for cyclic Rule 107. From width 17 onwards a pair
of off cells travels four places every four steps, with three intervening
patterns. The exact period is lcm(n,4). Smaller cycles are certified directly. -/

open OMA.S_oeis_a334514

/-- The exceptional cells in the first twelve stages, against the alternating
uniform background. Indices n-j represent negative offsets. -/
private def rule107Mask (n : ℕ) : ℕ → ℕ → Bool
  | 0, i => decide (i = 0)
  | 1, i => !decide (i = 0 ∨ i = 1)
  | 2, i => decide (i = n-1 ∨ i = 1 ∨ i = 2)
  | 3, i => !decide (i = n-1 ∨ i = 3)
  | 4, i => decide (i = n-2 ∨ i = n-1 ∨ i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4)
  | 5, i => !decide (i = n-1 ∨ i = 3 ∨ i = 5)
  | 6, i => decide (i = n-2 ∨ i = n-1 ∨ i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6)
  | 7, i => !decide (i = n-1 ∨ i = 7)
  | 8, i => decide (i = n-2 ∨ i = n-1 ∨ i = 0 ∨ i = 6 ∨ i = 7 ∨ i = 8)
  | 9, i => !decide (i = n-1 ∨ i = 1 ∨ i = 7 ∨ i = 9)
  | 10, i => decide (i = n-2 ∨ i = n-1 ∨ i = 1 ∨ i = 2 ∨ i = 6 ∨ i = 7 ∨ i = 9 ∨ i = 10)
  | _, i => !decide (i = 3 ∨ i = 11)

private lemma rule107_pred_val {n : ℕ} (i : Fin n) :
    (i.val+n-1) % n = if i.val = 0 then n-1 else i.val-1 := by
  split_ifs with h
  · rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]
  · rw [show i.val+n-1 = i.val-1+n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

private lemma rule107_succ_val {n : ℕ} (i : Fin n) :
    (i.val+1) % n = if i.val+1 = n then 0 else i.val+1 := by
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

set_option maxHeartbeats 1200000 in
private lemma rule107_mask_step {n : ℕ} (hn : 17 ≤ n) (i : Fin n)
    (t : ℕ) (ht : t < 11) :
    step 107 n (fun j => rule107Mask n t j.val) i = rule107Mask n (t+1) i.val := by
  simp only [step, rule107_pred_val, rule107_succ_val]
  have hi := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨
      i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨
      i.val = 11 ∨ i.val = n-1 ∨ i.val = n-2 ∨ i.val = n-3 ∨
      (12 ≤ i.val ∧ i.val + 3 < n) := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|⟨h,h'⟩ <;> interval_cases t <;>
    simp (disch := omega) only [rule107Mask, if_pos, if_neg, true_or, or_true,
      decide_eq_true, decide_eq_false] <;> decide

private lemma rule107_state_mask {n : ℕ} (hn : 17 ≤ n) (t : ℕ) (ht : t ≤ 11) (i : Fin n) :
    state 107 n t i = rule107Mask n t i.val := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    rw [state, show state 107 n t = fun j => rule107Mask n t j.val by
      funext j
      exact ih (by omega) j]
    exact rule107_mask_step hn i t (by omega)

private lemma rule107_seven {n : ℕ} (hn : 17 ≤ n) (i : Fin n) :
    state 107 n 7 i = !decide (i.val = n-1 ∨ i.val = 7) :=
  rule107_state_mask hn 7 (by decide) i

private lemma rule107_eight {n : ℕ} (hn : 17 ≤ n) (i : Fin n) :
    state 107 n 8 i = decide (i.val = n-2 ∨ i.val = n-1 ∨ i.val = 0 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8) :=
  rule107_state_mask hn 8 (by decide) i

private lemma rule107_nine {n : ℕ} (hn : 17 ≤ n) (i : Fin n) :
    state 107 n 9 i = !decide (i.val = n-1 ∨ i.val = 1 ∨ i.val = 7 ∨ i.val = 9) :=
  rule107_state_mask hn 9 (by decide) i

private lemma rule107_ten {n : ℕ} (hn : 17 ≤ n) (i : Fin n) :
    state 107 n 10 i = decide (i.val = n-2 ∨ i.val = n-1 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 9 ∨ i.val = 10) :=
  rule107_state_mask hn 10 (by decide) i

private lemma rule107_eleven {n : ℕ} [NeZero n] (hn : 17 ≤ n) (i : Fin n) :
    state 107 n 11 i = state 107 n 7 (i - 4) := by
  rw [rule107_state_mask hn 11 (by decide), rule107_seven hn]
  simp only [rule107Mask, Bool.not_inj_iff, decide_eq_decide, Fin.val_sub,
    show (4 : Fin n).val = 4 from Nat.mod_eq_of_lt (by omega : 4 < n)]
  by_cases hi : i.val < 4
  · rw [Nat.mod_eq_of_lt (by omega : n-4+i.val < n)]
    omega
  · rw [show n-4+i.val = i.val-4+n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : i.val-4 < n)]
    omega

open OMA.S_oeis_a334514

private lemma rule107_stabilizer {n : ℕ} [NeZero n] (hn : 17 ≤ n)
    (h7 : ∀ i : Fin n, state 107 n 7 i = !decide (i.val=n-1 ∨ i.val=7))
    (s : Fin n) (h : ∀ i : Fin n, state 107 n 7 (i+s) = state 107 n 7 i) :
    s = 0 := by
  apply Fin.ext
  change s.val = 0
  by_contra hs
  have hleft := h ⟨n-1, by omega⟩
  have hsub : (n-1+s.val)%n = s.val-1 := by
    rw [show n-1+s.val = s.val-1+n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : s.val-1 < n)]
  simp only [h7, Fin.val_add, hsub, Bool.not_inj_iff, decide_eq_decide, true_or, iff_true] at hleft
  have hs8 : s.val = 8 := by omega
  have hright := h ⟨7,by omega⟩
  simp only [h7, Fin.val_add, hs8, show (7+8)%n = 15 from Nat.mod_eq_of_lt (by omega),
    Bool.not_inj_iff, decide_eq_decide, or_true, iff_true] at hright
  omega

/-- If a shifted configuration has three distinct holes, it cannot agree
with the seventh row, which has only two. -/
private lemma rule107_three_holes {n : ℕ} [NeZero n]
    (h7 : ∀ i : Fin n, state 107 n 7 i = !decide (i.val=n-1 ∨ i.val=7))
    (t : Fin n → Bool) (x y z : Fin n)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hx : t x = false) (hy : t y = false) (hz : t z = false)
    (s : Fin n) : ¬ ∀ i, t (i+s) = state 107 n 7 i := by
  intro h
  have hole (a : Fin n) (ha : t a = false) : (a-s).val = n-1 ∨ (a-s).val = 7 := by
    have hh : state 107 n 7 (a-s) = false := by rw [← h, sub_add_cancel, ha]
    simp [h7] at hh
    tauto
  have inj : Function.Injective (fun a : Fin n => (a-s).val) := by
    intro a b hab
    have he : a-s = b-s := Fin.ext hab
    simpa using he
  have h1 : (x-s).val ≠ (y-s).val := inj.ne hxy
  have h2 : (y-s).val ≠ (z-s).val := inj.ne hyz
  have h3 : (x-s).val ≠ (z-s).val := inj.ne hxz
  have := hole x hx
  have := hole y hy
  have := hole z hz
  omega

private lemma rule107_no_other_shift {n : ℕ} [NeZero n] (hn : 17 ≤ n)
    (h7 : ∀ i : Fin n, state 107 n 7 i = !decide (i.val=n-1 ∨ i.val=7))
    (h8 : ∀ i : Fin n, state 107 n 8 i = decide (i.val=n-2 ∨ i.val=n-1 ∨ i.val=0 ∨
      i.val=6 ∨ i.val=7 ∨ i.val=8))
    (h9 : ∀ i : Fin n, state 107 n 9 i = !decide (i.val=n-1 ∨ i.val=1 ∨ i.val=7 ∨ i.val=9))
    (h10 : ∀ i : Fin n, state 107 n 10 i = decide (i.val=n-2 ∨ i.val=n-1 ∨ i.val=1 ∨
      i.val=2 ∨ i.val=6 ∨ i.val=7 ∨ i.val=9 ∨ i.val=10)) :
    ∀ q : ℕ, 0 < q → q < 4 → ∀ s : Fin n, ¬ ∀ i, state 107 n (7+q) (i+s) = state 107 n 7 i := by
  intro q hq hq4 s
  interval_cases q
  · apply rule107_three_holes h7 (state 107 n 8) ⟨5,by omega⟩ ⟨11,by omega⟩ ⟨12,by omega⟩
      (by norm_num) (by norm_num) (by norm_num) _ _ _ s
    all_goals
      simp [h8]
      omega
  · apply rule107_three_holes h7 (state 107 n 9) ⟨1,by omega⟩ ⟨7,by omega⟩ ⟨9,by omega⟩
      (by norm_num) (by norm_num) (by norm_num) _ _ _ s
    all_goals simp [h9]
  · apply rule107_three_holes h7 (state 107 n 10) ⟨5,by omega⟩ ⟨11,by omega⟩ ⟨12,by omega⟩
      (by norm_num) (by norm_num) (by norm_num) _ _ _ s
    all_goals
      simp [h10]
      omega

open OMA.S_oeis_a334514 Fin.NatCast

private lemma rule107_prev {n : ℕ} [NeZero n] (hn : 17 ≤ n) (i : Fin n) :
    (⟨(i.val+n-1)%n, Nat.mod_lt _ (Fin.pos i)⟩ : Fin n) = i-1 := by
  apply Fin.ext
  simp only [Fin.sub_def, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1<n)]
  congr 1
  omega

private lemma rule107_step_shift {n : ℕ} [NeZero n] (hn : 17 ≤ n)
    (x : Fin n → Bool) (s i : Fin n) :
    step 107 n (fun j => x (j+s)) i = step 107 n x (i+s) := by
  have next (j : Fin n) : (⟨(j.val+1)%n, Nat.mod_lt _ (Fin.pos j)⟩ : Fin n) = j+1 := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one',Nat.mod_eq_of_lt (by omega : 1<n)]
  unfold step
  rw [rule107_prev hn i,rule107_prev hn (i+s),next i,next (i+s)]
  dsimp only
  rw [show i-1+s=(i+s)-1 by abel, show i+1+s=(i+s)+1 by abel]

private lemma rule107_orbit {n : ℕ} [NeZero n] (hn : 17 ≤ n)
    (shift : ∀ i : Fin n, state 107 n 11 i = state 107 n 7 (i-4))
    (stabilizer : ∀ s : Fin n, (∀ i, state 107 n 7 (i+s) = state 107 n 7 i) → s=0)
    (different : ∀ q : ℕ, 0 < q → q < 4 → ∀ s : Fin n,
      ¬ ∀ i, state 107 n (7+q) (i+s) = state 107 n 7 i) :
    a n = n * (4 / Nat.gcd n 4) := by
  let x := state 107 n
  have slide (t : ℕ) : ∀ i : Fin n, x (11+t) i = x (7+t) (i-4) := by
    induction t with
    | zero => simpa [x] using shift
    | succ t ih =>
      intro i
      change step 107 n (x (11+t)) i = step 107 n (x (7+t)) (i-4)
      rw [funext ih]
      simpa only [sub_eq_add_neg] using rule107_step_shift hn (x (7+t)) (-4) i
  have phases (q k : ℕ) : ∀ i : Fin n,
      x (7+(4*k+q)) i = x (7+q) (i-((4*k : ℕ):Fin n)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro i
      rw [show 7+(4*(k+1)+q) = 11+(4*k+q) by omega, slide, ih,
        show 4*(k+1)=4*k+4 by omega,Nat.cast_add]
      push_cast
      congr 1
      abel
  let L := Nat.lcm n 4
  have dn : n ∣ L := Nat.dvd_lcm_left _ _
  have d4 : 4 ∣ L := Nat.dvd_lcm_right _ _
  have pos : 0 < L := Nat.lcm_pos (by omega) (by decide)
  have hl : 4*(L/4) = L := Nat.mul_div_cancel' d4
  have zcast : ((L:ℕ):Fin n) = 0 := by
    apply Fin.ext
    simpa only [Fin.val_natCast,Fin.val_zero] using Nat.mod_eq_zero_of_dvd dn
  have per : Function.Periodic (fun j => x (7+j)) L := by
    intro j
    induction j with
    | zero =>
      simpa only [hl,zcast,add_zero,zero_add,sub_zero] using funext (phases 0 (L/4))
    | succ j ih =>
      change x (7+(j+1+L)) = x (7+(j+1))
      rw [show 7+(j+1+L)=(7+(j+L))+1 by omega]
      exact congrArg (step 107 n) ih
  let G := {p : ℕ | 0<p ∧ EventualPeriod 107 n p}
  have mem : L ∈ G := by
    refine ⟨pos,7,?_⟩
    intro t ht
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa only [Nat.add_assoc] using per j
  have heq : L = n*(4/Nat.gcd n 4) := by
    have h := Nat.gcd_mul_lcm n 4
    have d := Nat.div_mul_cancel (Nat.gcd_dvd_right n 4)
    have nz : 0 < Nat.gcd n 4 := Nat.gcd_pos_of_pos_right n (by decide)
    apply Nat.eq_of_mul_eq_mul_left nz
    calc
      n.gcd 4 * L = n*4 := h
      _ = n*((4/n.gcd 4)*n.gcd 4) := congrArg (n*·) d.symm
      _ = n.gcd 4 * (n*(4/n.gcd 4)) := by ring
  rw [a,if_neg (by omega : n≠0),← heq]
  change sInf G = L
  refine le_antisymm (Nat.sInf_le mem) (le_csInf ⟨_,mem⟩ ?_)
  rintro r ⟨hr,U,hU⟩
  have hu : U ≤ 7+U*L := by nlinarith
  have p0 := per.nat_mul U 0
  have pr := per.nat_mul U r
  simp only [Nat.cast_id, zero_add, add_zero] at p0 pr
  have same : x (7+r) = x 7 := by
    calc
      _ = x (7+(r+U*L)) := pr.symm
      _ = x (7+U*L+r) := by congr 1; omega
      _ = x (7+U*L) := hU _ hu
      _ = _ := p0
  let k := r/4
  let q := r%4
  have split_r : r = 4*k+q := by dsimp [k,q]; omega
  rw [split_r] at same
  have trans0 (i : Fin n) : x (7+q) (i+ -((4*k:ℕ):Fin n)) = x 7 i := by
    simpa only [← sub_eq_add_neg] using (phases q k i).symm.trans (congrFun same i)
  have q0 : q=0 := by
    by_contra h
    exact different q (by omega) (by dsimp [q]; omega) _ trans0
  have fix := stabilizer (-((4*k:ℕ):Fin n)) (by simpa only [q0,add_zero] using trans0)
  have md := congrArg Fin.val (neg_eq_zero.mp fix)
  simp only [Fin.val_natCast,Fin.val_zero] at md
  have rk : r=4*k := by omega
  exact Nat.le_of_dvd hr (Nat.lcm_dvd ((rk ▸ Nat.dvd_of_mod_eq_zero md) : n ∣ r) ⟨k,rk⟩)

open OMA.S_oeis_a334514

private lemma rule107_certify {n T P : ℕ} (hn : n ≠ 0) (hp : 0 < P) (table : List ℕ)
    (h0 : ∀ i : Fin n, decide (i.val = 0) = (table.getD 0 0).testBit i.val)
    (hstep : ∀ j : Fin (T+P), ∀ i : Fin n,
      step 107 n (fun k => (table.getD j.val 0).testBit k.val) i =
        (table.getD (j.val+1) 0).testBit i.val)
    (hcycle : table.getD (T+P) 0 = table.getD T 0)
    (hmin : ∀ j : Fin P, 0 < j.val → ∃ i : Fin n,
      (table.getD (T+j.val) 0).testBit i.val ≠ (table.getD T 0).testBit i.val) :
    a n = P := by
  have tab (t : ℕ) (ht : t ≤ T+P) :
      state 107 n t = fun i => (table.getD t 0).testBit i.val := by
    induction t with
    | zero => exact funext h0
    | succ t ih =>
      change step 107 n (state 107 n t) = _
      rw [ih (by omega)]
      exact funext (hstep ⟨t, by omega⟩)
  have per : Function.Periodic (fun j => state 107 n (T+j)) P := by
    intro j
    induction j with
    | zero =>
      change state 107 n (T+(0+P)) = state 107 n (T+0)
      rw [zero_add, add_zero, tab (T+P) le_rfl, tab T (by omega), hcycle]
    | succ j ih =>
      change state 107 n (T + (j+1+P)) = state 107 n (T + (j+1))
      rw [show T+(j+1+P) = (T+(j+P))+1 by omega, show T+(j+1) = (T+j)+1 by omega]
      exact congrArg (step 107 n) ih
  have eventual : EventualPeriod 107 n P := by
    refine ⟨T, ?_⟩
    intro t ht
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa only [Nat.add_assoc] using per s
  let good := {p : ℕ | 0 < p ∧ EventualPeriod 107 n p}
  have mem : P ∈ good := ⟨hp,eventual⟩
  rw [a, if_neg hn]
  change sInf good = P
  refine le_antisymm (Nat.sInf_le mem) ?_
  apply le_csInf ⟨P, mem⟩
  rintro r ⟨hr, U, he⟩
  by_contra! small
  have hu : U ≤ T + U*P := by nlinarith
  have h0' := per.nat_mul U 0
  have hr' := per.nat_mul U r
  simp only [Nat.cast_id, zero_add, add_zero] at h0' hr'
  have same : state 107 n (T+r) = state 107 n T := by
    calc
      _ = state 107 n (T+(r+U*P)) := hr'.symm
      _ = state 107 n (T+U*P+r) := by congr 1; omega
      _ = state 107 n (T+U*P) := he _ hu
      _ = _ := h0'
  obtain ⟨i,hi⟩ := hmin ⟨r,small⟩ hr
  apply hi
  rw [tab (T+r) (by omega), tab T (by omega)] at same
  exact congrFun same i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_1 : a 1 = 2 := by
  apply rule107_certify (T := 0) (by decide) (by decide)
      [1, 0, 1] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_2 : a 2 = 2 := by
  apply rule107_certify (T := 0) (by decide) (by decide)
      [1, 2, 1] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_3 : a 3 = 3 := by
  apply rule107_certify (T := 0) (by decide) (by decide)
      [1, 4, 2, 1] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_4 : a 4 = 2 := by
  apply rule107_certify (T := 2) (by decide) (by decide)
      [1, 12, 14, 11, 14] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_5 : a 5 = 15 := by
  apply rule107_certify (T := 1) (by decide) (by decide)
      [1, 28, 22, 15, 25, 13, 30, 19, 26, 29, 7, 21,
       27, 14, 11, 23, 28] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_6 : a 6 = 2 := by
  apply rule107_certify (T := 5) (by decide) (by decide)
      [1, 60, 38, 23, 45, 63, 0, 63] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_7 : a 7 = 28 := by
  apply rule107_certify (T := 4) (by decide) (by decide)
      [1, 124, 70, 55, 125, 7, 117, 27, 95, 112, 94, 51,
       123, 14, 107, 54, 63, 97, 61, 102, 119, 28, 87, 108,
       126, 67, 122, 77, 111, 56, 47, 89, 125] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_8 : a 8 = 2 := by
  apply rule107_certify (T := 3) (by decide) (by decide)
      [1, 252, 134, 119, 221, 119] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_9 : a 9 = 36 := by
  apply rule107_certify (T := 6) (by decide) (by decide)
      [1, 508, 262, 247, 413, 215, 493, 63, 417, 221, 502, 287,
       464, 366, 251, 399, 232, 183, 381, 455, 116, 347, 446, 483,
       58, 429, 223, 497, 29, 470, 367, 504, 270, 235, 439, 252,
       135, 373, 475, 126, 323, 442, 493] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_10 : a 10 = 20 := by
  apply rule107_certify (T := 7) (by decide) (by decide)
      [1, 1020, 518, 503, 797, 471, 877, 511, 769, 509, 774, 1015,
       28, 983, 108, 895, 448, 383, 705, 1021, 7, 1013, 27, 991,
       112, 863, 432, 511] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_11 : a 11 = 11 := by
  apply rule107_certify (T := 1) (by decide) (by decide)
      [1, 2044, 1030, 1015, 1565, 983, 1645, 895, 1985, 125, 1862, 1463,
       2044] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_12 : a 12 = 12 := by
  apply rule107_certify (T := 3) (by decide) (by decide)
      [1, 4092, 2054, 2039, 3101, 2007, 3181, 1919, 3521, 1917, 3526, 3959,
       476, 3447, 1756, 2039] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_13 : a 13 = 117 := by
  apply rule107_certify (T := 11) (by decide) (by decide)
      [1, 8188, 4102, 4087, 6173, 4055, 6253, 3967, 6593, 3453, 7878, 5111,
       6684, 7638, 5999, 7672, 5902, 3563, 7991, 444, 7655, 1844, 5563, 7150,
       7739, 942, 6875, 3582, 3843, 6651, 3342, 3819, 7095, 3836, 2951, 5877,
       8091, 222, 7923, 922, 6877, 3575, 7965, 471, 7533, 1791, 6017, 7421,
       1671, 6005, 7643, 1918, 5571, 7034, 8141, 111, 8057, 461, 7534, 5883,
       8078, 4331, 7862, 4991, 7104, 7806, 4931, 7098, 7917, 959, 6881, 3517,
       8166, 4151, 8124, 4326, 3767, 7037, 4039, 6261, 3931, 6591, 3552, 3903,
       6561, 3549, 8054, 4575, 7536, 5854, 4083, 6171, 4062, 2163, 5979, 7614,
       6115, 7226, 6061, 7391, 1776, 6047, 7376, 5870, 4027, 6383, 3768, 2927,
       6137, 7181, 2031, 5177, 7085, 3807, 7153, 3613, 7126, 7791, 888, 7119,
       3688, 2935, 6109, 7287, 1884, 5559, 7164, 7686, 5111] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_14 : a 14 = 28 := by
  apply rule107_certify (T := 11) (by decide) (by decide)
      [1, 16380, 8198, 8183, 12317, 8151, 12397, 8063, 12737, 7549, 14022, 16375,
       28, 16343, 108, 16255, 448, 15743, 1728, 14335, 7168, 6143, 11265, 16381,
       7, 16373, 27, 16351, 112, 16223, 432, 15871, 1792, 13823, 6912, 8191,
       12289, 8189, 12294, 16375] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_15 : a 15 = 60 := by
  apply rule107_certify (T := 7) (by decide) (by decide)
      [1, 32764, 16390, 16375, 24605, 16343, 24685, 16255, 25025, 15741, 26310, 30711,
       7196, 22487, 27756, 32638, 16835, 32122, 18125, 30703, 7224, 22447, 27864, 32510,
       17283, 31482, 19853, 28655, 14392, 12207, 22745, 32509, 903, 31477, 3483, 28639,
       14448, 12127, 22961, 32253, 1799, 30197, 6939, 24543, 28784, 24414, 12723, 32251,
       1806, 30187, 6966, 24511, 28896, 24254, 13155, 31739, 3598, 27627, 13878, 16319,
       24801, 16061, 25446, 31735, 3612, 27607, 13932, 16255] <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private lemma rule107_small_16 : a 16 = 8 := by
  apply rule107_certify (T := 7) (by decide) (by decide)
      [1, 65532, 32774, 32759, 49181, 32727, 49261, 32639, 49601, 32125, 50886, 63479,
       7196, 55255, 27756, 32639] <;> decide +kernel

private lemma rule107_small (n : ℕ) (hn : n < 17) :
    a n = ([0, 2, 2, 3, 2, 15, 2, 28, 2, 36, 20, 11, 12, 117, 28, 60, 8] : List ℕ).getD n 0 := by
  interval_cases n
  · rfl
  · exact rule107_small_1
  · exact rule107_small_2
  · exact rule107_small_3
  · exact rule107_small_4
  · exact rule107_small_5
  · exact rule107_small_6
  · exact rule107_small_7
  · exact rule107_small_8
  · exact rule107_small_9
  · exact rule107_small_10
  · exact rule107_small_11
  · exact rule107_small_12
  · exact rule107_small_13
  · exact rule107_small_14
  · exact rule107_small_15
  · exact rule107_small_16

open OMA.S_oeis_a334514 PowerSeries

set_option maxHeartbeats 3000000 in
private lemma rule107_conclusion
    (hs : ∀ n : ℕ, n < 17 → a n = ([0,2,2,3,2,15,2,28,2,36,20,11,12,117,28,60,8] : List ℕ).getD n 0)
    (tailLaw : ∀ n : ℕ, 17 ≤ n → a n = n * (4 / Nat.gcd n 4)) :
    (∀ n : ℕ, 24 < n → (a n : ℤ) = 2 * a (n - 4) - a (n - 8)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2) =
      X * (2 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + 11 * X ^ 4 - 2 * X ^ 5 + 22 * X ^ 6 -
           2 * X ^ 7 + 8 * X ^ 8 + 18 * X ^ 9 - 42 * X ^ 10 + 10 * X ^ 11 + 60 * X ^ 12 -
           10 * X ^ 13 + 66 * X ^ 14 - 14 * X ^ 15 - 130 * X ^ 16 - 33 * X ^ 18 +
           16 * X ^ 19 + 65 * X ^ 20 - 8 * X ^ 23) := by
  have hrec (n : ℕ) (hn : 24 < n) : (a n : ℤ) = 2 * a (n-4) - a (n-8) := by
    have g₄ := Nat.gcd_sub_self_left (show 4 ≤ n by omega)
    have g₈ : (n-8).gcd 4 = n.gcd 4 := by
      rw [show n-8 = (n-4)-4 by omega, Nat.gcd_sub_self_left (by omega), g₄]
    rw [tailLaw n (by omega), tailLaw (n-4) (by omega), tailLaw (n-8) (by omega), g₄, g₈]
    push_cast [Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub (by omega : 8 ≤ n)]
    ring
  refine ⟨hrec, ?_⟩
  let A := mk (fun n => (a n : ℤ))
  have lhs : A * ((1-X)^2*(1+X)^2*(1+X^2)^2) = A - C 2 * (A*X^4) + A*X^8 := by
    norm_num [map_ofNat]
    ring
  have rhs : X * (2 + 2*X + 3*X^2 + 2*X^3 + 11*X^4 - 2*X^5 + 22*X^6 -
      2*X^7 + 8*X^8 + 18*X^9 - 42*X^10 + 10*X^11 + 60*X^12 - 10*X^13 +
      66*X^14 - 14*X^15 - 130*X^16 - 33*X^18 + 16*X^19 + 65*X^20 - 8*X^23) =
      C (2 : ℤ)*X^1 + C 2*X^2 + C 3*X^3 + C 2*X^4 + C 11*X^5 - C 2*X^6 + C 22*X^7 - C 2*X^8 + C 8*X^9
      + C 18*X^10 - C 42*X^11 + C 10*X^12 + C 60*X^13 - C 10*X^14 + C 66*X^15 - C 14*X^16 - C
      130*X^17 - C 33*X^19 + C 16*X^20 + C 65*X^21 - C 8*X^24 := by
    norm_num [map_ofNat]
    ring
  change A * ((1-X)^2*(1+X)^2*(1+X^2)^2) = _
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_C]
  by_cases large : 24 < n
  · simp (disch := omega) only [if_neg, if_pos]
    linarith [hrec n large]
  · have val (k : ℕ) : a k = if k < 17 then
        ([0,2,2,3,2,15,2,28,2,36,20,11,12,117,28,60,8] : List ℕ).getD k 0
        else k * (4 / Nat.gcd k 4) := by
      by_cases h : k < 17
      · rw [if_pos h, hs _ h]
      · rw [if_neg h, tailLaw _ (by omega)]
    interval_cases n <;> norm_num [val, List.getD]

theorem OMA.solution : type_of% @OMA.S_oeis_a334514.main := by
  apply rule107_conclusion rule107_small
  intro n hn
  haveI : NeZero n := ⟨by omega⟩
  exact rule107_orbit hn (rule107_eleven hn) (rule107_stabilizer hn (rule107_seven hn))
    (rule107_no_other_shift hn (rule107_seven hn) (rule107_eight hn) (rule107_nine hn)
      (rule107_ten hn))
