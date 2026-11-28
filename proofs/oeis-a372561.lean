import OMAStatements.S_oeis_a372561
import Mathlib

/-!
Antti Karttunen's minimum-coin conjectures for A372561.

The reduced iterates of 27 reach 1. Stretching changes the exponent in
`3N + 1 = 4^e (3y + 1)` and advances the same reduced orbit. To certify
minimum coin counts we use the base-four digit sums of a sum of powers
of two and of its double. Both give lower bounds; shifted Jacobsthal
representations attain them.
-/

namespace OMA.S_oeis_a372561

private def ds (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n % 4 + ds (n / 4)
termination_by n

private theorem ds_digit (n d : ℕ) (hd : d < 4) : ds (4*n+d) = ds n+d := by
  by_cases h : 4*n+d = 0
  · have hn : n = 0 := by omega
    have hd' : d = 0 := by omega
    simp [hn,hd']
  · rw [ds, dif_neg h]
    rw [show (4*n+d)%4=d by omega, show (4*n+d)/4=n by omega]
    omega

private theorem ds_one (n : ℕ) : ds (n+1) ≤ ds n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n % 4 = 3
    · have h₁ : n = 4*(n/4)+3 := by omega
      have h₂ : n+1 = 4*(n/4+1)+0 := by omega
      rw [h₂, ds_digit _ _ (by decide)]
      rw [show ds n = ds (n/4)+3 by conv_lhs => rw [h₁, ds_digit _ _ (by decide)]]
      have := ih (n/4) (by omega)
      omega
    · have h₁ : ds n = ds (n/4) + n%4 := by
        have hx := ds_digit (n/4) (n%4) (by omega)
        rwa [show 4*(n/4)+n%4=n by omega] at hx
      have h₂ := ds_digit (n/4) (n%4+1) (by omega)
      rw [show 4*(n/4)+(n%4+1) = n+1 by omega] at h₂
      omega

private theorem ds_add_pow (n k : ℕ) : ds (n+4^k) ≤ ds n+1 := by
  induction k generalizing n with
  | zero => simpa using ds_one n
  | succ k ih =>
    have h₁ := ds_digit (n/4 + 4^k) (n%4) (by omega)
    have h₂ := ds_digit (n/4) (n%4) (by omega)
    rw [show 4*(n/4)+n%4 = n by omega] at h₂
    rw [show 4*(n/4+4^k)+n%4 = n+4^(k+1) by rw [pow_succ]; omega] at h₁
    have := ih (n/4)
    omega

private theorem ds_add_twice (n k : ℕ) : ds (n+2*4^k) ≤ ds n+2 := by
  have := ds_add_pow n k
  have := ds_add_pow (n+4^k) k
  rw [show n+4^k+4^k = n+2*4^k by omega] at this
  omega

private theorem jac_pair (k : ℕ) :
    3*jac (2*k)+1=4^k ∧ 3*jac (2*k+1)=2*4^k+1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    change 3*jac (2*k+2)+1=4^(k+1) ∧ 3*jac (2*k+3)=2*4^(k+1)+1
    simp only [jac, pow_succ]
    omega

private theorem coin_bound (m : Multiset ℕ) (hm : ∀ i ∈ m, 2 ≤ i) :
    ∃ u v t : ℕ, u+v=m.card ∧ 4*t+v=3*value m+u ∧
      ds t ≤ u+2*v ∧ ds (2*t) ≤ 2*u+v := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0,0,0,by decide,by decide,by simp [ds],by simp [ds]⟩
  | cons i m ih =>
    obtain ⟨u,v,t,hc,ht,hs,hd⟩ := ih (fun j hj => hm j (Multiset.mem_cons_of_mem hj))
    have hi := hm i (Multiset.mem_cons_self i m)
    have hv : value (i ::ₘ m) = jac i + value m := by simp [value]
    let k := (i-2)/2
    have hcases : i=2*(k+1) ∨ i=2*(k+1)+1 := by dsimp [k]; omega
    rcases hcases with he|ho
    · have h := (jac_pair (k+1)).1
      rw [← he, pow_succ] at h
      refine ⟨u+1,v,t+4^k,?_,?_,?_,?_⟩
      · simp; omega
      · rw [hv]; omega
      · have := ds_add_pow t k; omega
      · rw [Nat.mul_add]; have := ds_add_twice (2*t) k; omega
    · have h := (jac_pair (k+1)).2
      rw [← ho, pow_succ] at h
      refine ⟨u,v+1,t+2*4^k,?_,?_,?_,?_⟩
      · simp; omega
      · rw [hv]; omega
      · have := ds_add_twice t k; omega
      · have hh := ds_add_pow (2*t) (k+1)
        rw [pow_succ] at hh
        rw [show 2*(t+2*4^k) = 2*t+4^k*4 by omega]
        omega

private def NoShort (A r : ℕ) : Prop := ∀ u v t : ℕ, u+v < r →
  4*t+v+1 = A+u → ds t ≤ u+2*v → ds (2*t) ≤ 2*u+v → False

private def test (A r : ℕ) : Bool :=
  (List.range r).all fun u => (List.range r).all fun v =>
    let t := (A+u-v-1)/4
    decide (r ≤ u+v ∨ 4*t+v+1 ≠ A+u ∨ u+2*v < ds t ∨ 2*u+v < ds (2*t))

private theorem test_sound {A r : ℕ} (h : test A r = true) : NoShort A r := by
  intro u v t hr ht h₁ h₂
  have hu : u ∈ List.range r := List.mem_range.mpr (by omega)
  have hv : v ∈ List.range r := List.mem_range.mpr (by omega)
  have hk := List.all_eq_true.mp (List.all_eq_true.mp h u hu) v hv
  simp only [decide_eq_true_eq] at hk
  have hh : (A+u-v-1)/4=t := by omega
  simp only [hh] at hk
  omega

private theorem ds_block (n : ℕ) :
    ds n = ds (n/16) + (n/4)%4 + n%4 := by
  have h := ds_digit (n/4) (n%4) (by omega)
  have h' := ds_digit (n/16) ((n/4)%4) (by omega)
  rw [show 4*(n/4)+n%4=n by omega] at h
  rw [show 4*(n/16)+(n/4)%4=n/4 by omega] at h'
  omega

-- Inserting one base-four digit between the high part and the last two
-- digits preserves or increases the digit sum (including across a borrow).
private theorem ds_insert (w x z : ℕ) (he : x+16*w=z+64*w)
    (hl : 64*w ≤ x+15) (hh : x ≤ 64*w+15) : ds z ≤ ds x := by
  have h₁ := ds_block x
  have h₂ := ds_block z
  have h₃ : x%4=z%4 := by omega
  have h₄ : (x/4)%4=(z/4)%4 := by omega
  by_cases h : 64*w ≤ x
  · have hx : x/16=4*w+0 := by omega
    have hz : z/16=w := by omega
    rw [hx, ds_digit _ _ (by decide)] at h₁
    rw [hz] at h₂
    omega
  · have hx : x/16=4*(w-1)+3 := by omega
    have hz : z/16=w-1 := by omega
    rw [hx, ds_digit _ _ (by decide)] at h₁
    rw [hz] at h₂
    omega

private theorem grow_lower {w r : ℕ} (hr : r ≤ 10) (h : NoShort (64*w) r) :
    NoShort (256*w) r := by
  intro u v t hnum he h₁ h₂
  let z := t-48*w
  have hz : z+48*w=t := by dsimp [z]; omega
  have hd := ds_insert w t z (by omega) (by omega) (by omega)
  have hd' := ds_insert (2*w) (2*t) (2*z) (by omega) (by omega) (by omega)
  exact h u v z hnum (by omega) (by omega) (by omega)

private theorem all_lower {A r : ℕ} (hr : r ≤ 10) (h : NoShort (4^3*A) r)
    (e : ℕ) (he : 3 ≤ e) : NoShort (4^e*A) r := by
  induction e, he using Nat.le_induction with
  | base => exact h
  | succ e he ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le he
    have hh := grow_lower (w := 4^k*A) hr
    rw [show 4^(3+k)*A = 64*(4^k*A) by rw [pow_add]; ring] at ih
    rw [show 4^(3+k+1)*A = 256*(4^k*A) by rw [pow_succ,pow_add]; ring]
    exact hh ih

private theorem jac_shift (e i : ℕ) :
    3*(jac (2*e+i) : ℤ) = (4:ℤ)^e * 2^i - (-1:ℤ)^i := by
  rcases Nat.even_or_odd' i with ⟨k, h|h⟩
  · subst i
    have hk : (3:ℤ)*jac (2*(e+k))+1=4^(e+k) := by exact_mod_cast (jac_pair (e+k)).1
    rw [Nat.mul_add] at hk
    rw [pow_mul,pow_mul,pow_add] at *
    norm_num at *
    linarith
  · subst i
    have hk : (3:ℤ)*jac (2*(e+k)+1)=2*4^(e+k)+1 := by exact_mod_cast (jac_pair (e+k)).2
    rw [Nat.mul_add,add_assoc,pow_add] at hk
    rw [pow_succ,pow_succ,pow_mul,pow_mul]
    norm_num at *
    linarith

private def shifted (e : ℕ) (l : List ℕ) : Multiset ℕ :=
  (l.map (fun i => 2*e+i) : List ℕ)

private theorem shifted_value (e : ℕ) (l : List ℕ) :
    3*(value (shifted e l) : ℤ) =
      (4:ℤ)^e * ((l.map (fun i => 2^i)).sum : ℕ) - (l.map (fun i => (-1:ℤ)^i)).sum := by
  induction l with
  | nil => simp [value,shifted]
  | cons i l ih =>
    have hv : value (shifted e (i::l)) = jac (2*e+i) + value (shifted e l) := by
      simp [value,shifted]
    simp only [hv,Nat.cast_add,List.map_cons,List.sum_cons]
    simp only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
    linear_combination jac_shift e i + ih

private def good (y : ℕ) (L : List ℕ) : Bool :=
  let A := 3*reduced y+1
  let r := L.length
  decide (0 < valuation y ∧ r ≤ 10 ∧ (L.map (fun i => (2:ℕ)^i)).sum = A ∧
    (L.map (fun i => (-1:ℤ)^i)).sum = 1) &&
    (decide (1 < valuation y) || test (4*A) r) &&
    (decide (2 < valuation y) || test (16*A) r) && test (64*A) r

private theorem coin_min {y e N : ℕ} {L : List ℕ} (h : good y L = true)
    (hl : valuation y ≤ e) (he : 3*N+1=4^e*(3*reduced y+1)) : minCoins N = L.length := by
  simp only [good,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hp,hr,hs,hc⟩,h₁⟩,h₂⟩,h₃⟩ := h
  have hlow : NoShort (4^e*(3*reduced y+1)) L.length := by
    by_cases e1 : e=1
    · subst e
      exact test_sound (h₁.resolve_left (by omega))
    by_cases e2 : e=2
    · subst e
      exact test_sound (h₂.resolve_left (by omega))
    exact all_lower hr (test_sound h₃) e (by omega)
  have hm : represents N (shifted e L) := by
    constructor
    · intro i hi
      change i ∈ (L.map (fun i => 2*e+i)) at hi
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
      omega
    · have hv := shifted_value e L
      rw [hs,hc] at hv
      have hh : (3:ℤ)*N+1=(4:ℤ)^e*((3*reduced y+1 : ℕ) : ℤ) := by exact_mod_cast he
      omega
  have hmem : L.length ∈ {r : ℕ | ∃ m : Multiset ℕ, represents N m ∧ m.card=r} :=
    ⟨shifted e L,hm,by simp [shifted]⟩
  apply le_antisymm (csInf_le (OrderBot.bddBelow _) hmem)
  apply le_csInf ⟨_,hmem⟩
  rintro r ⟨m,⟨hm,hv⟩,hc⟩
  obtain ⟨u,v,t,hu,ht,ha,hb⟩ := coin_bound m hm
  by_contra! hh
  exact hlow u v t (by omega) (by omega) ha hb

private theorem four_denom (v : ℕ) : 3*((4^v-1)/3)+1=4^v := by
  have h : 4^v%3=1 := by
    induction v with
    | zero => decide
    | succ v ih => rw [pow_succ,Nat.mul_mod]; omega
  have hp : 0 < (4:ℕ)^v := by positivity
  generalize (4:ℕ)^v = z at *
  have hd : 3 ∣ z-1 := Nat.dvd_of_mod_eq_zero (by omega)
  rw [Nat.mul_div_cancel' hd,Nat.sub_add_cancel (by omega)]

private theorem advance {x y e : ℕ} (hx : 3*x+1=4^e*(3*y+1)) :
    3*stretch x+1=4^(2*e+valuation y)*(3*reduced y+1) := by
  have hp (i : ℕ) : (4:ℕ)^i=2^(2*i) := by rw [pow_mul]; rfl
  have hv : valuation x=2*e+valuation y := by
    unfold valuation
    rw [hx,hp,padicValNat.mul (by positivity) (by positivity),padicValNat.prime_pow]
  have hy : 2^(valuation y)*reduced y=3*y+1 :=
    Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 2) (n := 3*y+1))
  have hfactor : 3*x+1=2^(valuation x)*reduced y := by
    rw [hv,pow_add,← hp, Nat.mul_assoc, hy,hx]
  have hd := four_denom (valuation x)
  unfold stretch
  rw [← hv]
  calc
    3*((3*x+1)*2^(valuation x)+(4^(valuation x)-1)/3)+1 =
        3*((3*x+1)*2^(valuation x))+4^(valuation x) := by omega
    _ = 4^(valuation x)*(3*reduced y+1) := by
      rw [hfactor,show (4:ℕ)^(valuation x)=(2^(valuation x))^2 by
        rw [hp,mul_comm,pow_mul]]
      ring

private def orb (k : ℕ) := reduced^[k] 27

private theorem orb_succ (n : ℕ) : orb (n+1)=reduced (orb n) :=
  Function.iterate_succ_apply' _ _ _

private theorem normal (n k : ℕ) : ∃ e : ℕ,
    3*(stretch^[n] (orb k))+1=4^e*(3*orb (n+k)+1) := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨e,h⟩ := ih
    exact ⟨_,by simpa only [Function.iterate_succ_apply',Nat.succ_add,orb_succ] using advance h⟩

private def witnesses : ℕ → List ℕ
  | 27 => [2, 3, 4, 5, 6]
  | 41 => [1, 2, 3, 4, 6]
  | 31 => [1, 2, 3, 6, 6]
  | 47 => [1, 2, 4, 6, 7]
  | 71 => [1, 6, 8]
  | 107 => [2, 5, 6, 7, 8]
  | 161 => [2, 3, 5, 6, 8]
  | 121 => [1, 4, 8]
  | 91 => [2, 3, 4, 7, 8]
  | 137 => [1, 2, 4, 5, 8]
  | 103 => [1, 4, 6, 7, 8]
  | 155 => [2, 3, 4, 5, 7, 8, 8]
  | 233 => [1, 2, 3, 8, 8]
  | 175 => [1, 2, 4, 8, 9]
  | 263 => [1, 5, 6, 6, 10]
  | 395 => [2, 4, 5, 6, 7, 9, 10]
  | 593 => [3, 4, 5, 8, 10]
  | 445 => [1, 2, 4, 5, 6, 7, 8]
  | 167 => [1, 4, 5, 6, 7, 8, 8]
  | 251 => [2, 3, 5, 6, 10]
  | 377 => [1, 4, 6, 8, 9]
  | 283 => [2, 3, 4, 5, 6, 7, 10]
  | 425 => [1, 2, 3, 4, 5, 7, 8, 8, 8]
  | 319 => [1, 2, 3, 4, 7, 8, 10]
  | 479 => [1, 2, 3, 5, 6, 10, 10]
  | 719 => [1, 2, 5, 7, 10, 10, 10]
  | 1079 => [1, 3, 4, 5, 6, 7, 8, 8, 12]
  | 1619 => [3, 4, 5, 6, 10, 11, 12]
  | 2429 => [1, 2, 3, 5, 7, 8, 8, 10, 10]
  | 911 => [1, 2, 12]
  | 1367 => [1, 3, 10, 10, 12]
  | 2051 => [4, 10, 13]
  | 3077 => [2, 6, 7, 9, 10]
  | 577 => [2, 4, 8, 9, 9]
  | 433 => [4, 6, 7, 8, 9]
  | 325 => [3, 4, 5, 6, 6]
  | 61 => [1, 2, 6]
  | 23 => [1, 3, 4, 4, 6]
  | 35 => [5, 6, 6]
  | 53 => [4]
  | 5 => [2]
  | 1 => [2]
  | _ => []

private def states : List ℕ :=
  [27, 41, 31, 47, 71, 107, 161, 121, 91, 137, 103, 155, 233, 175, 263, 395, 593, 445, 167, 251, 377, 283, 425, 319, 479, 719, 1079, 1619, 2429, 911, 1367, 2051, 3077, 577, 433, 325, 61, 23, 35, 53, 5, 1]

private theorem states_closed : states.all (fun y => states.contains (reduced y)) = true := by
  decide +kernel

private theorem orb_mem (n : ℕ) : orb n ∈ states := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [orb_succ]
    exact List.contains_iff_mem.mp (List.all_eq_true.mp states_closed _ ih)

private theorem certificates : states.all (fun y => good y (witnesses y)) = true := by
  decide +kernel

private theorem grid_count (n k : ℕ) :
    minCoins (grid (n+2) (k+1)) = (witnesses (orb (n+k))).length := by
  obtain ⟨e,h⟩ := normal n k
  have hg := List.all_eq_true.mp certificates _ (orb_mem (n+k))
  have ha := advance h
  apply coin_min hg (e := 2*e+valuation (orb (n+k))) (by omega)
  change 3*(stretch^[n+1] (orb k))+1=_
  rwa [Function.iterate_succ_apply']

end OMA.S_oeis_a372561

open OMA.S_oeis_a372561 in
theorem OMA.solution : type_of% @OMA.S_oeis_a372561.main := by
  constructor
  · intro n k hn hk hsum
    obtain ⟨a, rfl⟩ : ∃ a, n=a+2 := ⟨n-2,by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k=b+1 := ⟨k-1,by omega⟩
    rw [grid_count,show a+b=11 by omega]
    decide +kernel
  constructor
  · intro n k hn hk hsum
    obtain ⟨a, rfl⟩ : ∃ a, n=a+2 := ⟨n-2,by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k=b+1 := ⟨k-1,by omega⟩
    rw [grid_count,show a+b=28 by omega]
    decide +kernel
  · intro n k hn hk
    obtain ⟨a, rfl⟩ : ∃ a, n=a+2 := ⟨n-2,by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, k=b+2 := ⟨k-2,by omega⟩
    change minCoins (grid (a+2) ((b+1)+1)) = minCoins (grid (b+2) ((a+1)+1))
    rw [grid_count,grid_count,show a+(b+1)=b+(a+1) by omega]
