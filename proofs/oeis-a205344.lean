import OMAStatements.S_oeis_a205344

/-! Six-step excursions with flat steps excluded. The middle-height
decomposition counts pairs of three-step prefixes. Inclusion-exclusion over
the three possible flat steps gives the prefix count. Summing its square
proves Hardin's quintic and Barker's two conjectured identities in A205344. -/


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


namespace ExcursionNonflat

open Finset

def fibre (n h : ℕ) : Finset (ℕ × ℕ) :=
  (ExcursionPrefix.fibre n h).filter fun p => p.1 ≠ 0 ∧ p.1 ≠ p.2 ∧ p.2 ≠ h

def F (n h : ℕ) : ℕ := (fibre n h).card

end ExcursionNonflat


namespace ExcursionNonflat
open Finset

private lemma count_avoid {α : Type*} (s : Finset α) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] :
    ((s.filter fun x => ¬P x ∧ ¬Q x ∧ ¬R x).card : ℚ) =
      s.card - (s.filter P).card - (s.filter Q).card - (s.filter R).card
      + (s.filter fun x => P x ∧ Q x).card + (s.filter fun x => P x ∧ R x).card
      + (s.filter fun x => Q x ∧ R x).card - (s.filter fun x => P x ∧ Q x ∧ R x).card := by
  simp only [natCast_card_filter]
  rw [show (s.card : ℚ) = ∑ _x ∈ s, (1:ℚ) by simp]
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  by_cases hp : P x <;> by_cases hq : Q x <;> by_cases hr : R x <;> simp [hp,hq,hr]

private lemma middleCard (n h : ℕ) :
    ((ExcursionPrefix.fibre n h).filter (fun p => p.1 = p.2)).card =
      (Icc (h-n) n).card := by
  let d : ℕ → ℕ × ℕ := fun x => (x,x)
  have he : ((ExcursionPrefix.fibre n h).filter (fun p => p.1 = p.2)) =
      (Icc (h-n) n).image d := by
    ext ⟨u,v⟩
    simp only [ExcursionPrefix.fibre,mem_filter,mem_product,mem_range,mem_image,mem_Icc,
      d,Prod.mk.injEq]
    constructor
    · rintro ⟨hp, rfl⟩
      exact ⟨u,by omega,rfl,rfl⟩
    · rintro ⟨x,hx,rfl,rfl⟩
      omega
  rw [he, card_image_of_injective]
  exact fun u v h => congrArg Prod.fst h

/-- Delete one or more prescribed flat steps from a three-step prefix. -/
private theorem count_formula (n h : ℕ) :
    (F n h : ℚ) = (ExcursionPrefix.F n h : ℚ) - 3*((n+1-(h-n) : ℕ):ℚ)
      + (if h ≤ n then 3 else 0) - (if h = 0 then 1 else 0) := by
  let b := ExcursionPrefix.fibre n h
  let J := Icc (h-n) n
  have e1 : b.filter (fun p => p.1 = 0) = {0} ×ˢ J := by
    ext ⟨u,v⟩
    simp only [b,J,ExcursionPrefix.fibre,mem_filter,mem_product,mem_range,mem_Icc,mem_singleton]
    omega
  have e3 : b.filter (fun p => p.2 = h) = J ×ˢ {h} := by
    ext ⟨u,v⟩
    simp only [b,J,ExcursionPrefix.fibre,mem_filter,mem_product,mem_range,mem_Icc,mem_singleton]
    omega
  have d12 : b.filter (fun p => p.1=0 ∧ p.1=p.2) = if h≤n then {(0,0)} else ∅ := by
    ext ⟨u,v⟩
    by_cases hh : h≤n <;> simp [b, ExcursionPrefix.fibre,hh,Prod.ext_iff] <;> omega
  have d13 : b.filter (fun p => p.1=0 ∧ p.2=h) = if h≤n then {(0,h)} else ∅ := by
    ext ⟨u,v⟩
    by_cases hh : h≤n <;> simp [b, ExcursionPrefix.fibre,hh,Prod.ext_iff] <;> omega
  have d23 : b.filter (fun p => p.1=p.2 ∧ p.2=h) = if h≤n then {(h,h)} else ∅ := by
    ext ⟨u,v⟩
    by_cases hh : h≤n <;> simp [b, ExcursionPrefix.fibre,hh,Prod.ext_iff] <;> omega
  have tri : b.filter (fun p => p.1=0 ∧ p.1=p.2 ∧ p.2=h) =
      if h=0 then {(0,0)} else ∅ := by
    ext ⟨u,v⟩
    by_cases hz : h=0 <;> simp [b, ExcursionPrefix.fibre,hz,Prod.ext_iff] <;> omega
  have d := count_avoid b (fun p => p.1=0) (fun p => p.1=p.2) (fun p => p.2=h)
  rw [e1,e3,d12,d13,d23,tri,middleCard] at d
  change ((b.filter (fun p => p.1 ≠ 0 ∧ p.1 ≠ p.2 ∧ p.2 ≠ h)).card : ℚ) = _
  rw [d]
  by_cases hh : h≤n <;> by_cases hz : h=0 <;>
    simp [hh,hz,J,ExcursionPrefix.F,b,Nat.card_Icc] <;> ring

theorem zero (n : ℕ) : (F n 0 : ℚ) = ((n:ℚ)+1)^2 - 3*n - 1 := by
  rw [count_formula, ExcursionPrefix.low n 0 (by omega)]
  simp
  ring

theorem low (n h : ℕ) (hp : 0<h) (hh : h≤n) :
    (F n h : ℚ) = ((n:ℚ)+1)^2 + h*((n:ℚ)+1) - (h:ℚ)*(h+1)/2 - 3*n := by
  rw [count_formula, ExcursionPrefix.low n h hh]
  simp [hh, show h≠0 by omega, show h-n=0 by omega]
  ring

theorem middle (n t : ℕ) (hp : 0<t) (ht : t≤n) :
    (F n (n+t) : ℚ) = ((n:ℚ)+1)*(3*n+2-2*t)/2 - 3*((n:ℚ)-t+1) := by
  rw [count_formula, ExcursionPrefix.middle n t ht]
  simp [show ¬n+t≤n by omega, show t≠0 by omega, Nat.cast_sub (by omega : t≤n+1)]
  ring

theorem high (n t : ℕ) (hp : 0<t) (ht : t≤n) :
    (F n (2*n+t) : ℚ) = ((n:ℚ)-t+1)*(n-t+2)/2 := by
  rw [count_formula, ExcursionPrefix.high n t ht]
  simp [show ¬2*n+t≤n by omega, show t≠0 by omega, show n+1-(2*n+t-n)=0 by omega]

end ExcursionNonflat


namespace ExcursionNonflatMidpoint

open OMA.S_oeis_a205344 ExcursionNonflat Finset

private theorem steps {x y n : ℕ} :
    |(x : ℤ) - y| ≤ (n : ℤ) ↔ x ≤ y+n ∧ y ≤ x+n := by
  rw [abs_le]
  omega

private theorem fibre_member {n h x y : ℕ} :
    (x,y) ∈ fibre n h ↔
      x ≤ n ∧ y ≤ 2*n ∧ x ≤ y+n ∧ y ≤ x+n ∧ y ≤ h+n ∧ h ≤ y+n ∧ x ≠ 0 ∧ x ≠ y ∧ y ≠ h := by
  rw [fibre, mem_filter, ExcursionPrefix.fibre, mem_filter, mem_product, mem_range, mem_range]
  simp [and_assoc]

private abbrev SplitData := Σ _ : ℕ, (ℕ × ℕ) × (ℕ × ℕ)

private def build (z : SplitData) : Fin 7 → ℕ :=
  ![0, z.2.1.1, z.2.1.2, z.1, z.2.2.2, z.2.2.1, 0]

private theorem build_injective : Function.Injective build := by
  rintro ⟨h,⟨⟨x,y⟩,⟨z,w⟩⟩⟩ ⟨h',⟨⟨x',y'⟩,⟨z',w'⟩⟩⟩ eq
  have e1 := congrFun eq (1 : Fin 7)
  have e2 := congrFun eq (2 : Fin 7)
  have e3 := congrFun eq (3 : Fin 7)
  have e4 := congrFun eq (4 : Fin 7)
  have e5 := congrFun eq (5 : Fin 7)
  change x = x' at e1
  change y = y' at e2
  change h = h' at e3
  change w = w' at e4
  change z = z' at e5
  subst_vars
  rfl

private def splitSet (n : ℕ) : Finset SplitData :=
  (range (3*n+1)).sigma fun h => fibre n h ×ˢ fibre n h

private theorem builds_path {n : ℕ} {p : SplitData} (hp : p ∈ splitSet n) :
    build p ∈ arrays n := by
  rcases p with ⟨h,⟨⟨x,y⟩,⟨z,w⟩⟩⟩
  obtain ⟨_, pair⟩ := mem_sigma.mp hp
  obtain ⟨l,r⟩ := mem_product.mp pair
  change (x,y) ∈ fibre n h at l
  change (z,w) ∈ fibre n h at r
  obtain ⟨xN,yN,xy,yx,yh,hy,xnz,xny,ynh⟩ := fibre_member.mp l
  obtain ⟨zN,wN,zw,wz,wh,hw,znz,znw,wnh⟩ := fibre_member.mp r
  refine ⟨rfl,rfl,?_⟩
  intro i j eq
  constructor
  · fin_cases i <;> fin_cases j <;> norm_num at eq <;> norm_num [build] <;> omega
  · apply steps.mpr
    fin_cases i <;> fin_cases j <;> norm_num at eq <;> norm_num [build] <;> omega

private theorem split_path {n : ℕ} {v : Fin 7 → ℕ} (hv : v ∈ arrays n) :
    ∃ p ∈ splitSet n, build p = v := by
  obtain ⟨ends₀,ends₆,localSteps⟩ := hv
  have step01 := localSteps 0 1 (by decide)
  have len01 := steps.mp step01.2
  have step12 := localSteps 1 2 (by decide)
  have len12 := steps.mp step12.2
  have step23 := localSteps 2 3 (by decide)
  have len23 := steps.mp step23.2
  have step34 := localSteps 3 4 (by decide)
  have len34 := steps.mp step34.2
  have step45 := localSteps 4 5 (by decide)
  have len45 := steps.mp step45.2
  have step56 := localSteps 5 6 (by decide)
  have len56 := steps.mp step56.2
  have height : v 3 < 3*n+1 := by omega
  refine ⟨⟨v 3,(v 1,v 2),(v 5,v 4)⟩,?_,?_⟩
  · refine mem_sigma.mpr ⟨mem_range.mpr height, mem_product.mpr ⟨?_,?_⟩⟩
    · exact fibre_member.mpr ⟨by omega, by omega, len12.1,len12.2,len23.1,len23.2,
        by simpa [ends₀] using step01.1.symm, step12.1, step23.1⟩
    · exact fibre_member.mpr ⟨by omega, by omega, len45.2,len45.1,len34.2,len34.1,
        by simpa [ends₆] using step56.1, step45.1.symm, step34.1.symm⟩
  · funext i
    fin_cases i <;> simp [build, ends₀, ends₆]

theorem count_by_height (n : ℕ) : a n = ∑ h ∈ range (3*n+1), (F n h)^2 := by
  classical
  have eq : (↑((splitSet n).image build) : Set (Fin 7 → ℕ)) = arrays n := by
    ext v
    constructor
    · intro hv
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
      exact builds_path hp
    · intro hv
      obtain ⟨p,hp,rfl⟩ := split_path hv
      exact mem_image.mpr ⟨p,hp,rfl⟩
  unfold a
  rw [← eq, Set.ncard_coe_finset, card_image_of_injective _ build_injective]
  simp [splitSet, card_sigma, card_product, F, pow_two]

end ExcursionNonflatMidpoint


namespace ExcursionNonflat
open Finset

private def squareTotal (x t : ℚ) : ℚ :=
  ((x+1)^2 + t*(x+1) - t*(t+1)/2 - 3*x)^2 +
  ((x+1)*(3*x+2-2*t)/2 - 3*(x-t+1))^2 + ((x-t+1)*(x-t+2)/2)^2

/-- Sum of the three squared slice counts at offsets 1 through y. -/
private def sumPolynomial (x y : ℚ) : ℚ :=
  (y*(124+100*x+100*x^2-180*x^3+210*x^4)
   - y^2*(135+60*x-120*x^2+60*x^3) + y^3*(80-10*x+50*x^2)
   - y^4*(15+30*x) + 6*y^5)/60

private theorem sum_squareTotal (x : ℚ) (m : ℕ) :
    ∑ k ∈ range m, squareTotal x ((k:ℚ)+1) = sumPolynomial x m := by
  induction m with
  | zero => simp [sumPolynomial]
  | succ m ih =>
    rw [sum_range_succ,ih]
    push_cast
    unfold sumPolynomial squareTotal
    ring

theorem quartic (n : ℕ) :
    (∑ h ∈ range (3*n+1), (F n h : ℚ)^2) =
    (176*(n:ℚ)^5 - 25*(n:ℚ)^4 + 25*(n:ℚ)^2 + 124*(n:ℚ))/60 := by
  have hsplit : (∑ h ∈ range (3*n+1), (F n h : ℚ)^2) =
      (F n 0 : ℚ)^2 + ∑ k ∈ range n, squareTotal n ((k:ℚ)+1) := by
    rw [show 3*n+1 = (1+n+n)+n by omega, sum_range_add, sum_range_add, sum_range_add,
      sum_range_one]
    rw [add_assoc, add_assoc, ← sum_add_distrib, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro k hk
    have hkn : k+1 ≤ n := mem_range.mp hk
    rw [show 1+k = k+1 by omega, low n (k+1) (by omega) hkn,
      show 1+n+k = n+(k+1) by omega, middle n (k+1) (by omega) hkn,
      show 1+n+n+k = 2*n+(k+1) by omega, high n (k+1) (by omega) hkn]
    push_cast
    unfold squareTotal
    ring
  rw [hsplit, sum_squareTotal, zero n]
  unfold sumPolynomial
  ring

end ExcursionNonflat


namespace ExcursionNonflatSeries

open PowerSeries OMA.S_oeis_a205344

private def P (x : ℚ) : ℚ :=
  (176*x^5-25*x^4+25*x^2+124*x)/60

private theorem difference (x : ℚ) :
    P x = 6*P (x-1) - 15*P (x-2) + 20*P (x-3) -
      15*P (x-4) + 6*P (x-5) - P (x-6) := by
  unfold P
  ring

private theorem seriesPoly :
    (PowerSeries.mk (fun n => if n=0 then 0 else P n)) * (1 - X)^6 =
       X * (5 + 63*X + 206*X^2 + 73*X^3 + 5*X^4) := by
  let f : PowerSeries ℚ := PowerSeries.mk (fun n => if n=0 then 0 else P n)
  change f * (1 - X)^6 = _
  have expand : f * (1 - X)^6 =
      f - (6:ℕ) • (f*X^1) + (15:ℕ) • (f*X^2) - (20:ℕ) • (f*X^3) +
        (15:ℕ) • (f*X^4) - (6:ℕ) • (f*X^5) + f*X^6 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have right : X * (5 + 63*X + 206*X^2 + 73*X^3 + 5*X^4) =
      (5:ℕ) • (X:PowerSeries ℚ)^1 + (63:ℕ) • X^2 + (206:ℕ) • X^3 +
        (73:ℕ) • X^4 + (5:ℕ) • X^5 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [expand, right]
  ext k
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,f,coeff_mk]
  by_cases low : k ≤ 6
  · interval_cases k <;> norm_num [P]
  · have h1 : 1 ≤ k := by omega
    have h2 : 2 ≤ k := by omega
    have h3 : 3 ≤ k := by omega
    have h4 : 4 ≤ k := by omega
    have h5 : 5 ≤ k := by omega
    have h6 : 6 ≤ k := by omega
    have e1 : k ≠ 1 := by omega
    have e2 : k ≠ 2 := by omega
    have e3 : k ≠ 3 := by omega
    have e4 : k ≠ 4 := by omega
    have e5 : k ≠ 5 := by omega
    have ek : ∀ i : ℕ, i ≤ 6 → k-i ≠ 0 := by omega
    simp [h1,h2,h3,h4,h5,h6,e1,e2,e3,e4,e5,
      ek _ (by decide : 1≤6), ek _ (by decide : 2≤6), ek _ (by decide : 3≤6),
      ek _ (by decide : 4≤6), ek _ (by decide : 5≤6), ek _ (by decide : 6≤6),
      show k ≠ 0 by omega,Nat.cast_sub]
    linarith only [difference (k : ℚ)]

theorem from_count (count : ∀ n : ℕ, (a n : ℚ) =
    (176*(n:ℚ)^5-25*(n:ℚ)^4+25*(n:ℚ)^2+124*n)/60) :
    type_of% @OMA.S_oeis_a205344.main := by
  have cp (n : ℕ) : (a n : ℚ) = P n := count n
  refine ⟨?_,?_⟩
  · simpa only [cp] using seriesPoly
  · intro n hn
    apply Rat.intCast_injective
    push_cast
    simp only [cp, Nat.cast_sub (by omega : 1≤n), Nat.cast_sub (by omega : 2≤n),
      Nat.cast_sub (by omega : 3≤n), Nat.cast_sub (by omega : 4≤n),
      Nat.cast_sub (by omega : 5≤n), Nat.cast_sub (by omega : 6≤n), Nat.cast_ofNat]
    exact difference n

end ExcursionNonflatSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a205344.main := by
  apply ExcursionNonflatSeries.from_count
  intro n
  rw [ExcursionNonflatMidpoint.count_by_height]
  push_cast
  exact ExcursionNonflat.quartic n
