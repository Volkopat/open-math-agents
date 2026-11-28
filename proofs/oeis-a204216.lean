import OMAStatements.S_oeis_a204216

/-! Seven-step excursions split into two three-step prefixes joined by a
single step. The allowable heights for that step give four explicit
counting formulas. Their weighted sum proves Hardin's sextic and Barker's
recurrence and generating-function conjectures for A204216. -/


namespace ExcursionPrefix

open Finset

def fibre (n h : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n+1) ×ˢ range (2*n+1)).filter fun p =>
    p.1 ≤ p.2+n ∧ p.2 ≤ p.1+n ∧ p.2 ≤ h+n ∧ h ≤ p.2+n)

def F (n h : ℕ) : ℕ := (fibre n h).card

end ExcursionPrefix


namespace ExcursionPrefix
open Finset

private def weight (n v : ℕ) : ℚ := (n:ℚ)+1-((v-n : ℕ):ℚ)
private def cumulative (n m : ℕ) : ℚ := ∑ v ∈ range m, weight n v

private theorem prefix_sum (n h : ℕ) (hh : h ≤ 3*n) :
    (F n h : ℚ) = cumulative n (min (2*n) (h+n) + 1) - cumulative n (h-n) := by
  let s := Icc (h-n) (min (2*n) (h+n))
  have hm : (fibre n h : Set (ℕ × ℕ)).MapsTo Prod.snd s := by
    rintro ⟨u,v⟩ hp
    change (u,v) ∈ fibre n h at hp
    simp only [fibre, mem_filter, mem_product, mem_range] at hp
    change v ∈ Icc _ _
    simp only [mem_Icc, le_min_iff]
    omega
  have hf (v : ℕ) (hv : v ∈ s) :
      ((fibre n h).filter (fun p => p.2 = v)).card = n+1-(v-n) := by
    have hv' : h-n ≤ v ∧ v ≤ 2*n ∧ v ≤ h+n := by simpa [s, le_min_iff] using hv
    have he : ((fibre n h).filter (fun p => p.2 = v)) = Icc (v-n) n ×ˢ {v} := by
      ext ⟨a,b⟩
      simp only [fibre,mem_filter,mem_product,mem_range,mem_Icc,mem_singleton]
      omega
    rw [he, card_product, card_singleton, mul_one, Nat.card_Icc]
  have hcard := card_eq_sum_card_fiberwise hm
  have hc : (F n h : ℚ) = ∑ v ∈ s, weight n v := by
    unfold F
    rw [hcard]
    push_cast
    apply sum_congr rfl
    intro v hv
    have hv' : v ≤ 2*n := (le_min_iff.mp (mem_Icc.mp hv).2).1
    rw [hf v hv, Nat.cast_sub (by omega : v-n ≤ n+1)]
    simp [weight]
  rw [hc]
  change ∑ v ∈ Icc _ _, weight n v = _
  rw [show Icc (h-n) (min (2*n) (h+n)) = Ico (h-n) (min (2*n) (h+n)+1) by
    ext v; simp, sum_Ico_eq_sub _ (by omega)]
  rfl

private theorem cumulative_low (n m : ℕ) (hm : m ≤ n+1) :
    cumulative n m = (m:ℚ)*(n+1) := by
  unfold cumulative
  calc
    _ = ∑ _v ∈ range m, ((n:ℚ)+1) := by
      apply sum_congr rfl
      intro v hv
      simp [weight, show v - n = 0 by have := mem_range.mp hv; omega]
    _ = _ := by simp; ring

private theorem cumulative_high (n t : ℕ) :
    cumulative n (n+t) = ((n:ℚ)+t)*(n+1) - (t:ℚ)*(t-1)/2 := by
  induction t with
  | zero => simpa using cumulative_low n n (by omega)
  | succ t ih =>
    rw [show n+(t+1) = (n+t)+1 by omega, cumulative, sum_range_succ]
    change cumulative n (n+t) + weight n (n+t) = _
    rw [ih]
    simp only [weight, Nat.add_sub_cancel_left, Nat.cast_succ]
    ring

theorem low (n h : ℕ) (hh : h ≤ n) :
    (F n h : ℚ) = ((n:ℚ)+1)^2 + h*((n:ℚ)+1) - (h:ℚ)*(h+1)/2 := by
  rw [prefix_sum n h (by omega), min_eq_right (by omega), show h-n=0 by omega,
    show h+n+1 = n+(h+1) by omega, cumulative_high, cumulative_low n 0 (by omega)]
  push_cast
  ring

theorem middle (n t : ℕ) (ht : t ≤ n) :
    (F n (n+t) : ℚ) = ((n:ℚ)+1)*(3*n+2-2*t)/2 := by
  rw [prefix_sum n (n+t) (by omega), min_eq_left (by omega), Nat.add_sub_cancel_left,
    show 2*n+1=n+(n+1) by omega, cumulative_high, cumulative_low n t (by omega)]
  push_cast
  ring

theorem high (n t : ℕ) (ht : t ≤ n) :
    (F n (2*n+t) : ℚ) = ((n:ℚ)-t+1)*(n-t+2)/2 := by
  rw [prefix_sum n (2*n+t) (by omega), min_eq_left (by omega),
    show 2*n+t-n=n+t by omega, show 2*n+1=n+(n+1) by omega, cumulative_high, cumulative_high]
  push_cast
  ring

end ExcursionPrefix


namespace ExcursionBridge

open OMA.S_oeis_a204216 ExcursionPrefix Finset

private theorem adjacent {x y n : ℕ} :
    |(x : ℤ) - y| ≤ (n : ℤ) ↔ x ≤ y+n ∧ y ≤ x+n := by
  rw [abs_le]
  omega

private theorem fibre_member {n h x y : ℕ} :
    (x,y) ∈ fibre n h ↔
      x ≤ n ∧ y ≤ 2*n ∧ x ≤ y+n ∧ y ≤ x+n ∧ y ≤ h+n ∧ h ≤ y+n := by
  rw [fibre, mem_filter, mem_product, mem_range, mem_range]
  simp [and_assoc]

private abbrev Pieces := Σ _ : ℕ, Σ _ : ℕ, (ℕ × ℕ) × (ℕ × ℕ)

private def join (p : Pieces) : Fin 8 → ℕ :=
  ![0,p.2.2.1.1,p.2.2.1.2,p.1,p.2.1,p.2.2.2.2,p.2.2.2.1,0]

private theorem join_injective : Function.Injective join := by
  rintro ⟨h,k,⟨⟨x,y⟩,⟨z,w⟩⟩⟩ ⟨h',k',⟨⟨x',y'⟩,⟨z',w'⟩⟩⟩ eq
  have ex := congrFun eq (1 : Fin 8)
  have ey := congrFun eq (2 : Fin 8)
  have eh := congrFun eq (3 : Fin 8)
  have ek := congrFun eq (4 : Fin 8)
  have ew := congrFun eq (5 : Fin 8)
  have ez := congrFun eq (6 : Fin 8)
  change x = x' at ex
  change y = y' at ey
  change h = h' at eh
  change k = k' at ek
  change w = w' at ew
  change z = z' at ez
  subst_vars
  rfl

private def splitSet (n : ℕ) : Finset Pieces :=
  (range (3*n+1)).sigma fun h =>
    ((range (3*n+1)).filter (fun k => h ≤ k+n ∧ k ≤ h+n)).sigma
      fun k => fibre n h ×ˢ fibre n k

private theorem joins_path {n : ℕ} {p : Pieces} (hp : p ∈ splitSet n) :
    join p ∈ arrays n := by
  rcases p with ⟨h,k,⟨⟨x,y⟩,⟨z,w⟩⟩⟩
  obtain ⟨_, tail⟩ := mem_sigma.mp hp
  obtain ⟨neighbor,pair⟩ := mem_sigma.mp tail
  change k ∈ (range (3*n+1)).filter (fun k => h ≤ k+n ∧ k ≤ h+n) at neighbor
  obtain ⟨hk,kh⟩ := (mem_filter.mp neighbor).2
  obtain ⟨left,right⟩ := mem_product.mp pair
  change (x,y) ∈ fibre n h at left
  change (z,w) ∈ fibre n k at right
  obtain ⟨xN,yN,xy,yx,yh,hy⟩ := fibre_member.mp left
  obtain ⟨zN,wN,zw,wz,wk,kw⟩ := fibre_member.mp right
  refine ⟨rfl,rfl,?_⟩
  intro i j eq
  apply adjacent.mpr
  fin_cases i <;> fin_cases j <;> norm_num at eq <;> norm_num [join] <;> omega

private theorem splits_path {n : ℕ} {v : Fin 8 → ℕ} (hv : v ∈ arrays n) :
    ∃ p ∈ splitSet n, join p = v := by
  obtain ⟨first,last,dist⟩ := hv
  have h01 := adjacent.mp (dist 0 1 (by decide))
  have h12 := adjacent.mp (dist 1 2 (by decide))
  have h23 := adjacent.mp (dist 2 3 (by decide))
  have h34 := adjacent.mp (dist 3 4 (by decide))
  have h45 := adjacent.mp (dist 4 5 (by decide))
  have h56 := adjacent.mp (dist 5 6 (by decide))
  have h67 := adjacent.mp (dist 6 7 (by decide))
  have leftHt : v 3 < 3*n+1 := by omega
  have rightHt : v 4 < 3*n+1 := by omega
  refine ⟨⟨v 3,v 4,(v 1,v 2),(v 6,v 5)⟩,?_,?_⟩
  · apply mem_sigma.mpr
    refine ⟨mem_range.mpr leftHt,mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_range.mpr rightHt,h34⟩,?_⟩⟩
    apply mem_product.mpr
    exact ⟨fibre_member.mpr ⟨by omega,by omega,h12.1,h12.2,h23.1,h23.2⟩,
      fibre_member.mpr ⟨by omega,by omega,h56.2,h56.1,h45.2,h45.1⟩⟩
  · funext i
    fin_cases i <;> simp [join, first,last]

theorem count_with_bridge (n : ℕ) :
    a n = ∑ h ∈ range (3*n+1), ∑ k ∈ (range (3*n+1)).filter (fun k => h ≤ k+n ∧ k ≤ h+n),
      F n h * F n k := by
  classical
  have eq : (↑((splitSet n).image join) : Set (Fin 8 → ℕ)) = arrays n := by
    ext v
    constructor
    · intro hv
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
      exact joins_path hp
    · intro hv
      obtain ⟨p,hp,rfl⟩ := splits_path hv
      exact mem_image.mpr ⟨p,hp,rfl⟩
  unfold a
  rw [← eq, Set.ncard_coe_finset, card_image_of_injective _ join_injective]
  simp [splitSet, card_sigma, card_product, F]

end ExcursionBridge


namespace ExcursionNeighbor

def lowP (x t : ℚ) : ℚ := (x+1)^2 + t*(x+1) - t*(t+1)/2
def midP (x t : ℚ) : ℚ := (x+1)*(3*x+2-2*t)/2
def highP (x t : ℚ) : ℚ := (x-t+1)*(x-t+2)/2

def lowS (x y : ℚ) : ℚ := y*(x+1)^2 + (x+1)*y*(y+1)/2 - y*(y+1)*(y+2)/6
def midS (x y : ℚ) : ℚ := (x+1)*y*(3*x+1-y)/2
def highS (x y : ℚ) : ℚ :=
  (x*(x+1)*(x+2) - (x-y)*(x-y+1)*(x-y+2))/6

def constantPart (x : ℚ) : ℚ := (x+1)^2*((x+1)^2+lowS x x)

def slicePart (x k : ℚ) : ℚ :=
  lowP x (k+1)*((x+1)^2+lowS x x+midS x (k+1)) +
  midP x (k+1)*(lowS x x-lowS x k+midS x x+highS x (k+1)) +
  highP x (k+1)*(midS x x-midS x k+highS x x)

end ExcursionNeighbor


namespace ExcursionNeighbor
open Finset
open ExcursionPrefix

private theorem sum_low (x : ℚ) (y : ℕ) :
    ∑ t ∈ range y, lowP x ((t:ℚ)+1) = lowS x y := by
  induction y with
  | zero => simp [lowS]
  | succ y ih => rw [sum_range_succ,ih]; push_cast; unfold lowP lowS; ring

private theorem sum_mid (x : ℚ) (y : ℕ) :
    ∑ t ∈ range y, midP x ((t:ℚ)+1) = midS x y := by
  induction y with
  | zero => simp [midS]
  | succ y ih => rw [sum_range_succ,ih]; push_cast; unfold midP midS; ring

private theorem sum_high (x : ℚ) (y : ℕ) :
    ∑ t ∈ range y, highP x ((t:ℚ)+1) = highS x y := by
  induction y with
  | zero => simp [highS]
  | succ y ih => rw [sum_range_succ,ih]; push_cast; unfold highP highS; ring

private def pre (n b : ℕ) : ℚ := ∑ k ∈ range b, (F n k : ℚ)

private theorem pre_low (n t : ℕ) (ht : t≤n) :
    pre n (1+t) = ((n:ℚ)+1)^2 + lowS n t := by
  rw [pre,sum_range_add,sum_range_one,low n 0 (by omega),←sum_low]
  simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, sub_zero]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkn := mem_range.mp hk
  rw [low n (1+k) (by omega)]
  push_cast
  unfold lowP
  ring

private theorem pre_mid (n t : ℕ) (ht : t≤n) :
    pre n (1+n+t) = ((n:ℚ)+1)^2 + lowS n n + midS n t := by
  rw [pre,sum_range_add]
  change pre n (1+n) + _ = _
  rw [pre_low n n le_rfl,←sum_mid]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkn := mem_range.mp hk
  rw [show 1+n+k = n+(k+1) by omega,middle n (k+1) (by omega)]
  push_cast
  rfl

private theorem pre_high (n t : ℕ) (ht : t≤n) :
    pre n (1+n+n+t) = ((n:ℚ)+1)^2 + lowS n n + midS n n + highS n t := by
  rw [pre,sum_range_add]
  change pre n (1+n+n) + _ = _
  rw [pre_mid n n le_rfl,←sum_high]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkn := mem_range.mp hk
  rw [show 1+n+n+k = 2*n+(k+1) by omega,high n (k+1) (by omega)]
  push_cast
  rfl

private def neighbors (n h : ℕ) : ℚ :=
  ∑ k ∈ (range (3*n+1)).filter (fun k => h≤k+n ∧ k≤h+n), (F n k : ℚ)

private theorem neighbor_pre (n h : ℕ) (hh : h≤3*n) :
    neighbors n h = pre n (min (3*n) (h+n)+1) - pre n (h-n) := by
  have he : (range (3*n+1)).filter (fun k => h≤k+n ∧ k≤h+n) =
      Ico (h-n) (min (3*n) (h+n)+1) := by
    ext k
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [neighbors,he,sum_Ico_eq_sub _ (by omega)]
  rfl

private theorem neighbor_zero (n : ℕ) : neighbors n 0 = ((n:ℚ)+1)^2 + lowS n n := by
  rw [neighbor_pre n 0 (by omega), show min (3*n) (0+n)+1 = 1+n by omega,
    show 0-n = 0 by omega, pre_low n n le_rfl]
  simp [pre]

private theorem neighbor_low (n k : ℕ) (hk : k<n) :
    neighbors n (1+k) = ((n:ℚ)+1)^2 + lowS n n + midS n ((k:ℚ)+1) := by
  rw [neighbor_pre n (1+k) (by omega), show min (3*n) (1+k+n)+1 = 1+n+(k+1) by omega,
    show 1+k-n=0 by omega,pre_mid n (k+1) (by omega)]
  simp [pre]

private theorem neighbor_mid (n k : ℕ) (hk : k<n) :
    neighbors n (1+n+k) = lowS n n - lowS n k + midS n n + highS n ((k:ℚ)+1) := by
  rw [neighbor_pre n (1+n+k) (by omega),
    show min (3*n) (1+n+k+n)+1=1+n+n+(k+1) by omega,show 1+n+k-n=1+k by omega,
    pre_high n (k+1) (by omega),pre_low n k (by omega)]
  push_cast
  ring

private theorem neighbor_high (n k : ℕ) (hk : k<n) :
    neighbors n (1+n+n+k) = midS n n - midS n k + highS n n := by
  rw [neighbor_pre n (1+n+n+k) (by omega),
    show min (3*n) (1+n+n+k+n)+1=1+n+n+n by omega,show 1+n+n+k-n=1+n+k by omega,
    pre_high n n le_rfl,pre_mid n k (by omega)]
  ring

theorem decompose (n : ℕ) :
    (∑ h ∈ range (3*n+1), ∑ k ∈ (range (3*n+1)).filter (fun k => h≤k+n ∧ k≤h+n),
      (F n h:ℚ)*(F n k:ℚ)) = constantPart n + ∑ k ∈ range n, slicePart n (k:ℚ) := by
  simp_rw [← mul_sum]
  change (∑ h ∈ range (3*n+1), (F n h : ℚ)*neighbors n h) = _
  rw [show 3*n+1=(1+n+n)+n by omega,sum_range_add,sum_range_add,sum_range_add,sum_range_one,
    low n 0 (by omega), neighbor_zero]
  simp only [Nat.cast_zero,zero_mul,zero_div,add_zero,sub_zero]
  change constantPart n + _ + _ + _ = _
  rw [add_assoc,add_assoc,←sum_add_distrib,←sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hkn := mem_range.mp hk
  rw [neighbor_low n k hkn,neighbor_mid n k hkn,neighbor_high n k hkn,
    low n (1+k) (by omega),show 1+n+k=n+(k+1) by omega,middle n (k+1) (by omega),
    show 1+n+n+k=2*n+(k+1) by omega,high n (k+1) (by omega)]
  push_cast
  unfold slicePart lowP midP highP
  ring

end ExcursionNeighbor


namespace ExcursionNeighbor
open Finset

/-- The sum of the first y slice contributions, with the strip width x held fixed. -/
private def partialSum (x y : ℚ) : ℚ :=
  (y*(294+1999*x+5145*x^2+6410*x^3+3945*x^4+975*x^5)
   - y^2*(165+705*x+1020*x^2+675*x^3+195*x^4)
   + y^3*(60+140*x+180*x^2+100*x^3) - y^4*(15+60*x+45*x^2)
   + y^5*(6+6*x))/180

private theorem sum_slicePart (x : ℚ) (m : ℕ) :
    ∑ k ∈ range m, slicePart x (k:ℚ) = partialSum x m := by
  induction m with
  | zero => simp [partialSum]
  | succ m ih =>
    rw [sum_range_succ,ih]
    push_cast
    unfold partialSum slicePart lowP midP highP lowS midS highS
    ring

theorem sextic (n : ℕ) :
    constantPart n + ∑ k ∈ range n, slicePart n (k:ℚ) =
    (841*(n:ℚ)^6 + 3636*(n:ℚ)^5 + 6625*(n:ℚ)^4 + 6570*(n:ℚ)^3
     + 3784*(n:ℚ)^2 + 1224*(n:ℚ) + 180)/180 := by
  rw [sum_slicePart]
  unfold constantPart lowS partialSum
  ring

end ExcursionNeighbor


namespace ExcursionSevenSeries

open PowerSeries OMA.S_oeis_a204216

private def P (x : ℚ) : ℚ :=
  (841*x^6 + 3636*x^5 + 6625*x^4 + 6570*x^3 + 3784*x^2 + 1224*x + 180) / 180

private theorem difference (x : ℚ) :
    P x = 7*P (x-1) - 21*P (x-2) + 35*P (x-3) - 35*P (x-4) +
      21*P (x-5) - 7*P (x-6) + P (x-7) := by
  unfold P
  ring

private theorem seriesPoly :
    PowerSeries.mk (fun n => if n = 0 then 0 else P n) * (1 - X)^7 =
      X * (127 + 1036*X + 1684*X^2 + 481*X^3 + 42*X^4 - 7*X^5 + X^6) := by
  let f : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then 0 else P n)
  change f * (1 - X)^7 = _
  have expand : f * (1 - X)^7 =
      f - (7:ℕ) • (f*X^1) + (21:ℕ) • (f*X^2) - (35:ℕ) • (f*X^3) +
        (35:ℕ) • (f*X^4) - (21:ℕ) • (f*X^5) + (7:ℕ) • (f*X^6) - f*X^7 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have right : X * (127 + 1036*X + 1684*X^2 + 481*X^3 + 42*X^4 - 7*X^5 + X^6) =
      (127:ℕ) • (X : PowerSeries ℚ)^1 + (1036:ℕ) • X^2 + (1684:ℕ) • X^3 +
        (481:ℕ) • X^4 + (42:ℕ) • X^5 - (7:ℕ) • X^6 + X^7 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [expand, right]
  ext k
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, f, coeff_mk]
  by_cases low : k ≤ 7
  · interval_cases k <;> norm_num [P]
  · have le (j : ℕ) (hj : j ≤ 7) : j ≤ k := by omega
    have ne (j : ℕ) (hj : j ≤ 7) : k ≠ j := by omega
    have nz (j : ℕ) (hj : j ≤ 7) : k - j ≠ 0 := by omega
    simp (disch := omega) [le, ne, nz, Nat.cast_sub]
    linarith only [difference (k : ℚ)]

theorem from_count (count : ∀ n : ℕ, (a n : ℚ) =
    (841*(n:ℚ)^6 + 3636*(n:ℚ)^5 + 6625*(n:ℚ)^4 + 6570*(n:ℚ)^3 +
      3784*(n:ℚ)^2 + 1224*n + 180) / 180) : type_of% @OMA.S_oeis_a204216.main := by
  have cp (n : ℕ) : (a n : ℚ) = P n := count n
  refine ⟨?_, ?_⟩
  · simpa only [cp] using seriesPoly
  · intro n hn
    apply Rat.intCast_injective
    push_cast
    simp only [cp, Nat.cast_sub (by omega : 1≤n), Nat.cast_sub (by omega : 2≤n),
      Nat.cast_sub (by omega : 3≤n), Nat.cast_sub (by omega : 4≤n),
      Nat.cast_sub (by omega : 5≤n), Nat.cast_sub (by omega : 6≤n),
      Nat.cast_sub (by omega : 7≤n), Nat.cast_ofNat]
    exact difference n

end ExcursionSevenSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a204216.main := by
  apply ExcursionSevenSeries.from_count
  intro n
  rw [ExcursionBridge.count_with_bridge]
  push_cast
  rw [ExcursionNeighbor.decompose]
  exact ExcursionNeighbor.sextic n
