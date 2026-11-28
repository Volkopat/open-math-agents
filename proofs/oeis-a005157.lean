import OMAStatements.S_oeis_a005157

/-!
The product is integral by counting multiples of each prime power in its
telescoped factors. For p ≥ 5, both products have the same number of units
in each nonzero residue class. Their linear terms modulo p² cancel under
r ↦ p − r, after the factors divisible by p supply the power of two.
-/

/- Exact multiplicities and their arithmetic identities. -/

namespace PlaneCongruence

def numeratorMultiplicity (n a : ℕ) : ℕ := (min (a-n) (3*n-a)+1)/2

def denominatorMultiplicity (n a : ℕ) : ℕ :=
  min n ((a+1)/2) - (a+1)/3

abbrev N := numeratorMultiplicity
abbrev D := denominatorMultiplicity

theorem partial_count (d r : ℕ) (hr : r < d) :
    D r d + D r (2*d) ≤ N r d + N r (2*d) := by
  unfold D N numeratorMultiplicity denominatorMultiplicity
  rw [min_eq_left (show r ≤ (2*d+1)/2 by omega)]
  by_cases h3 : 3*r ≤ d
  · have h0 : min r ((d+1)/2) - (d+1)/3 = 0 := by
      have hmin := min_le_left r ((d+1)/2)
      omega
    rw [h0, show r - (2*d+1)/3 = 0 by omega]
    omega
  by_cases h2 : 2*r ≤ d
  · rw [min_eq_left (show r ≤ (d+1)/2 by omega),
      min_eq_right (show 3*r-d ≤ d-r by omega),
      show r - (2*d+1)/3 = 0 by omega]
    have hfloor : r - (d+1)/3 = (3*r-d+1)/3 := by omega
    rw [hfloor]
    have hle : (3*r-d+1)/3 ≤ (3*r-d+1)/2 := by omega
    omega
  rw [min_eq_right (show (d+1)/2 ≤ r by omega),
      min_eq_left (show d-r ≤ 3*r-d by omega),
      min_eq_right (show 3*r-2*d ≤ 2*d-r by omega)]
  by_cases h' : 3*r ≤ 2*d
  · rw [show r - (2*d+1)/3 = 0 by omega,
      show 3*r-2*d = 0 by omega]
    simp only [Nat.zero_add, Nat.reduceDiv, Nat.add_zero]
    have hmod : d % 6 < 6 := Nat.mod_lt _ (by decide)
    interval_cases hd : d % 6 <;> omega
  · have hfloor : (d+1)/3 + (2*d+1)/3 = d := by omega
    have hsum : (d+1)/2 - (d+1)/3 + (r - (2*d+1)/3) = r-d/2 := by omega
    rw [hsum]
    omega

theorem full_denominator (d : ℕ) :
    D d d + D d (2*d) = (d+1)/2 := by
  unfold D denominatorMultiplicity
  omega

theorem full_numerator (d r : ℕ) (hr : r < d) :
    (d+1)/2 ≤ N d (2*d-r) + N d (3*d-r) := by
  unfold N numeratorMultiplicity
  omega

theorem multiples (p : ℕ) (hp : 5 ≤ p) (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    N p p = 0 ∧ N p (2*p) = D p p + D p (2*p) := by
  unfold N D numeratorMultiplicity denominatorMultiplicity
  omega

theorem p_factor (p : ℕ) (hp : 5 ≤ p) (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    (p % 6 = 1 → D p p = (p+5)/6) ∧
      (p % 6 = 5 → D p p = (p+1)/6) := by
  unfold D denominatorMultiplicity
  omega

private theorem numerator_residues (p r : ℕ) (hr : r < p) :
    N p (p+r) = (r+1)/2 ∧ N p (2*p+r) = (p-r+1)/2 := by
  unfold N numeratorMultiplicity
  rw [min_eq_left (show p+r-p ≤ 3*p-(p+r) by omega),
    min_eq_right (show 3*p-(2*p+r) ≤ 2*p+r-p by omega)]
  omega

private theorem denominator_residues (p r : ℕ) (hr : r < p) :
    D p r = (r+1)/2 - (r+1)/3 ∧
    D p (p+r) = (p+r+1)/2 - (p+r+1)/3 ∧
    D p (2*p+r) = p - (2*p+r+1)/3 := by
  unfold D denominatorMultiplicity
  rw [min_eq_right (show (r+1)/2 ≤ p by omega),
    min_eq_right (show (p+r+1)/2 ≤ p by omega),
    min_eq_left (show p ≤ (2*p+r+1)/2 by omega)]
  exact ⟨rfl,rfl,rfl⟩

private theorem thirds (p r : ℕ) (h3 : p % 3 ≠ 0) :
    (r+1)/3 + (p+r+1)/3 + (2*p+r+1)/3 = p+r := by
  have hp : p % 3 < 3 := Nat.mod_lt _ (by decide)
  have hr : r % 3 < 3 := Nat.mod_lt _ (by decide)
  have m₀ : (r+1)%3 = (r%3+1)%3 := by rw [Nat.add_mod r 1 3]
  have m₁ : (p+r+1)%3 = ((p%3+r%3)%3+1)%3 := by
    rw [Nat.add_mod (p+r) 1 3, Nat.add_mod p r 3]
  have m₂ : (2*p+r+1)%3 = (((2*(p%3))%3+r%3)%3+1)%3 := by
    rw [Nat.add_mod (2*p+r) 1 3, Nat.add_mod (2*p) r 3, Nat.mul_mod 2 p 3]
  interval_cases hp' : p % 3 <;> interval_cases hr' : r % 3 <;>
    simp [hp', hr'] at m₀ m₁ m₂ <;> omega

theorem residue_count (p r : ℕ) (_hp : 5 ≤ p) (h2 : p % 2 = 1)
    (h3 : p % 3 ≠ 0) (_hr : 0 < r) (hr' : r < p) :
    N p (p+r) + N p (2*p+r) = D p r + D p (p+r) + D p (2*p+r) := by
  obtain ⟨hn₁,hn₂⟩ := numerator_residues p r hr'
  obtain ⟨hd₀,hd₁,hd₂⟩ := denominator_residues p r hr'
  rw [hn₁,hn₂,hd₀,hd₁,hd₂]
  have h := thirds p r h3
  omega

def firstOrder (p r : ℕ) : ℤ :=
  (N p (p+r) : ℤ) + 2*(N p (2*p+r) : ℤ) -
    (D p (p+r) : ℤ) - 2*(D p (2*p+r) : ℤ)

theorem firstOrder_formula (p r : ℕ) (_hp : 5 ≤ p) (h2 : p % 2 = 1)
    (h3 : p % 3 ≠ 0) (_hr : 0 < r) (hr' : r < p) :
    firstOrder p r = (((2*p+r+1)/3:ℕ):ℤ) - (((r+1)/3:ℕ):ℤ) - ((p/2:ℕ):ℤ) := by
  obtain ⟨hn₁,hn₂⟩ := numerator_residues p r hr'
  obtain ⟨_,hd₁,hd₂⟩ := denominator_residues p r hr'
  rw [firstOrder,hn₁,hn₂,hd₁,hd₂, Nat.cast_sub (by omega : (p+r+1)/3 ≤ (p+r+1)/2),
    Nat.cast_sub (by omega : (2*p+r+1)/3 ≤ p)]
  have h := thirds p r h3
  have hsum : (r+1)/2 + (p-r+1)/2 = p/2+1 := by omega
  have hhalf : (p+r+1)/2 = p/2+1+r/2 := by omega
  have hrhalf : (r+1)/2 + r/2 = r := by omega
  omega

theorem reflect_order (p r : ℕ) (hp : 5 ≤ p) (h2 : p % 2 = 1)
    (h3 : p % 3 ≠ 0) (hr : 0 < r) (hr' : r < p) :
    firstOrder p (p-r) = firstOrder p r := by
  rw [firstOrder_formula p r hp h2 h3 hr hr',firstOrder_formula p (p-r) hp h2 h3 (by omega) (by omega)]
  omega

end PlaneCongruence

/- Count each value by the allowed interval for a single coordinate. -/

namespace PlaneCongruence

open Finset

def triangle (n : ℕ) : Finset (ℕ×ℕ) :=
  (range n ×ˢ range n).filter fun i => i.1 ≤ i.2

def numerator (n : ℕ) (i : ℕ×ℕ) : ℕ := n+1+i.1+i.2
def denominator (i : ℕ×ℕ) : ℕ := 1+i.1+2*i.2

@[simp]
theorem mem_triangle {n : ℕ} (i : ℕ×ℕ) :
    i ∈ triangle n ↔ i.1 ≤ i.2 ∧ i.2 < n := by
  rw [triangle, mem_filter, mem_product, mem_range, mem_range]
  omega

theorem num_pos (n : ℕ) (i : ℕ×ℕ) : 0 < numerator n i := by
  unfold numerator
  omega

theorem den_pos (i : ℕ×ℕ) : 0 < denominator i := by
  unfold denominator
  omega

theorem num_bound (n : ℕ) (i : ℕ×ℕ) (hi : i ∈ triangle n) : numerator n i < 3*n := by
  rw [mem_triangle] at hi
  unfold numerator
  omega

theorem den_bound (n : ℕ) (i : ℕ×ℕ) (hi : i ∈ triangle n) : denominator i < 3*n := by
  rw [mem_triangle] at hi
  unfold denominator
  omega

theorem count_denominator (n z : ℕ) (hz : 0 < z) :
    ((triangle n).filter fun i => denominator i=z).card = D n z := by
  let L := (z+1)/3
  let U := min n ((z+1)/2)
  have hc : ((triangle n).filter fun i => denominator i=z).card = (Ico L U).card := by
    apply card_bij (fun i _ => i.2)
    · intro i hi
      rw [mem_filter, mem_triangle] at hi
      rw [mem_Ico]
      dsimp [denominator,L,U] at *
      omega
    · intro i hi j hj e
      rw [mem_filter, mem_triangle] at hi hj
      dsimp [denominator] at hi hj
      exact Prod.ext (by omega) e
    · intro y hy
      rw [mem_Ico] at hy
      let i : ℕ×ℕ := (z-1-2*y,y)
      refine ⟨i,?_ ,rfl⟩
      rw [mem_filter, mem_triangle]
      dsimp [i,denominator,L,U] at *
      omega
  rw [hc,Nat.card_Ico]
  rfl

theorem count_numerator (n z : ℕ) :
    ((triangle n).filter fun i => numerator n i=z).card = N n z := by
  by_cases h : z ≤ n
  · have he : (triangle n).filter (fun i => numerator n i=z) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      rw [mem_filter] at hi
      dsimp [numerator] at hi
      omega
    simp [he, N, numeratorMultiplicity, Nat.sub_eq_zero_of_le h]
  · let s := z-n-1
    let L := s+1-n
    let U := s/2+1
    have hc : ((triangle n).filter fun i => numerator n i=z).card = (Ico L U).card := by
      apply card_bij (fun i _ => i.1)
      · intro i hi
        rw [mem_filter,mem_triangle] at hi
        rw [mem_Ico]
        dsimp [numerator,L,U,s] at *
        omega
      · intro i hi j hj e
        rw [mem_filter,mem_triangle] at hi hj
        dsimp [numerator] at hi hj
        exact Prod.ext e (by omega)
      · intro x hx
        rw [mem_Ico] at hx
        let i : ℕ×ℕ := (x,s-x)
        refine ⟨i,?_,rfl⟩
        rw [mem_filter,mem_triangle]
        dsimp [i,numerator,L,U,s] at *
        omega
    rw [hc,Nat.card_Ico]
    unfold N numeratorMultiplicity
    dsimp [L,U,s]
    omega

end PlaneCongruence

/- Partition a triangle by an initial block of width d. The rectangle gives one hit per row. -/

namespace PlaneCongruence

open Finset

def hits (n d A B : ℕ) : Finset (ℕ × ℕ) :=
  (triangle n).filter fun i => d ∣ A+i.1+B*i.2

def rectangle (s d A B : ℕ) : Finset (ℕ × ℕ) :=
  (range d ×ˢ Ico d (d+s)).filter fun i => d ∣ A+i.1+B*i.2

def translate (d : ℕ) : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun i := (i.1+d,i.2+d)
  inj' := by
    intro i j h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)

@[simp] theorem translate_apply (d : ℕ) (i : ℕ × ℕ) :
    translate d i = (i.1+d,i.2+d) := rfl

private theorem rectangle_card (s d A B : ℕ) (hd : 0 < d) :
    (rectangle s d A B).card = s := by
  suffices h : (rectangle s d A B).card = (Ico d (d+s)).card by
    simpa [Nat.card_Ico] using h
  apply card_bij (fun i _ => i.2)
  · intro i hi
    rw [rectangle, mem_filter, mem_product] at hi
    exact hi.1.2
  · intro i hi j hj e
    rw [rectangle, mem_filter, mem_product, mem_range] at hi hj
    refine Prod.ext ?_ e
    have h := (Nat.modEq_zero_iff_dvd.mpr hi.2).trans
      (Nat.modEq_zero_iff_dvd.mpr hj.2).symm
    rw [e, show A+i.1+B*j.2 = i.1+(A+B*j.2) by omega,
      show A+j.1+B*j.2 = j.1+(A+B*j.2) by omega] at h
    have hm := Nat.ModEq.add_right_cancel' (A+B*j.2) h
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hi.1.1, Nat.mod_eq_of_lt hj.1.1] using hm
  · intro y hy
    let c := (A+B*y)%d
    let x := (d-c)%d
    refine ⟨(x,y), ?_, rfl⟩
    rw [rectangle, mem_filter, mem_product, mem_range]
    refine ⟨⟨Nat.mod_lt _ hd, hy⟩, ?_⟩
    have hc : c < d := Nat.mod_lt _ hd
    have he : c+(d-c) = d := by omega
    change d ∣ A+x+B*y
    rw [show A+x+B*y = (A+B*y)+x by omega, Nat.dvd_iff_mod_eq_zero,
      Nat.add_mod]
    change (c+((d-c)%d)%d)%d = 0
    rw [Nat.mod_mod]
    calc
      (c+(d-c)%d)%d = (c+(d-c))%d := by
        rw [Nat.add_mod c (d-c) d, Nat.mod_eq_of_lt hc]
      _ = 0 := by rw [he,Nat.mod_self]

private theorem translate_div (d A B : ℕ) (i : ℕ × ℕ) :
    (d ∣ A+(translate d i).1+B*(translate d i).2) ↔ d ∣ A+i.1+B*i.2 := by
  change (d ∣ A+(i.1+d)+B*(i.2+d)) ↔ d ∣ A+i.1+B*i.2
  rw [show A+(i.1+d)+B*(i.2+d) = (A+i.1+B*i.2)+d*(B+1) by ring]
  exact (Nat.dvd_add_iff_left (dvd_mul_right d (B+1))).symm

theorem hits_step (s d A B : ℕ) (hd : 0 < d) :
    (hits (d+s) d A B).card = (hits d d A B).card + s + (hits s d A B).card := by
  have he : hits (d+s) d A B =
      (hits d d A B ∪ rectangle s d A B) ∪ (hits s d A B).map (translate d) := by
    ext i
    simp only [mem_union, mem_map, hits, rectangle, mem_filter, mem_triangle,
      mem_product, mem_range, mem_Ico]
    constructor
    · intro ⟨⟨hxy,hy⟩,hv⟩
      by_cases ht : i.2 < d
      · exact Or.inl (Or.inl ⟨⟨hxy,ht⟩,hv⟩)
      by_cases hx : i.1 < d
      · exact Or.inl (Or.inr ⟨⟨hx,by omega,hy⟩,hv⟩)
      let j := (i.1-d,i.2-d)
      have hj : translate d j = i := Prod.ext (by dsimp [j]; omega) (by dsimp [j]; omega)
      exact Or.inr ⟨j, ⟨⟨by dsimp [j]; omega, by dsimp [j]; omega⟩,
        (translate_div d A B j).mp (hj ▸ hv)⟩, hj⟩
    · rintro ((⟨⟨hxy,hy⟩,hv⟩ | ⟨⟨hx,hd',hy⟩,hv⟩) | ⟨j,⟨⟨hxy,hy⟩,hv⟩,rfl⟩)
      · exact ⟨⟨hxy,by omega⟩,hv⟩
      · exact ⟨⟨by omega,hy⟩,hv⟩
      · exact ⟨⟨by simp only [translate_apply]; omega, by simp only [translate_apply]; omega⟩,
          (translate_div d A B j).mpr hv⟩
  have h₁ : Disjoint (hits d d A B) (rectangle s d A B) := by
    apply disjoint_left.mpr
    simp only [hits, rectangle, mem_filter, mem_triangle, mem_product, mem_range, mem_Ico]
    intro i hi hj
    omega
  have h₂ : Disjoint (hits d d A B ∪ rectangle s d A B)
      ((hits s d A B).map (translate d)) := by
    apply disjoint_left.mpr
    simp only [mem_union, mem_map, hits, rectangle, mem_filter, mem_triangle,
      mem_product, mem_range, mem_Ico, translate_apply]
    rintro i (hi | hi) ⟨j,_,rfl⟩ <;> omega
  rw [he, card_union_of_disjoint h₂, card_union_of_disjoint h₁, card_map, rectangle_card _ _ _ _ hd]

end PlaneCongruence

/- Compare the number of factors divisible by every prime power. -/

namespace PlaneCongruence

open Finset

private theorem card_two_multiples (s d : ℕ) (f : ℕ × ℕ → ℕ) (hd : 0 < d)
    (hf : ∀ i ∈ triangle s, 0 < f i ∧ f i < 3*d) :
    ((triangle s).filter fun i => d ∣ f i).card =
      ((triangle s).filter fun i => f i = d).card +
      ((triangle s).filter fun i => f i = 2*d).card := by
  have he : (triangle s).filter (fun i => d ∣ f i) =
      (triangle s).filter (fun i => f i = d) ∪ (triangle s).filter (fun i => f i = 2*d) := by
    ext i
    simp only [mem_filter, mem_union, ← and_or_left]
    refine and_congr_right fun hi => ⟨?_,?_⟩
    · rintro ⟨k,hk⟩
      obtain ⟨hpos,hbound⟩ := hf i hi
      have hlt : k < 3 := by
        apply (Nat.mul_lt_mul_left hd).mp
        rw [← hk,mul_comm d 3]
        exact hbound
      have hk₀ : 0 < k := by
        by_contra! h
        simp [show k=0 by omega] at hk
        omega
      interval_cases k <;> simp_all [mul_comm]
    · rintro (h | h)
      · simp [h]
      · exact ⟨2,by simpa [mul_comm] using h⟩
  rw [he,card_union_of_disjoint]
  apply disjoint_left.mpr
  intro i hi hj
  rw [mem_filter] at hi hj
  omega

private theorem count_den_hits (s d : ℕ) (hd : 0 < d) (hs : s ≤ d) :
    (hits s d 1 2).card = D s d + D s (2*d) := by
  change ((triangle s).filter fun i => d ∣ denominator i).card = _
  rw [card_two_multiples _ _ _ hd (fun i hi => ⟨den_pos i,(den_bound s i hi).trans_le (by omega)⟩),
    count_denominator _ _ hd,count_denominator _ _ (by omega)]

private theorem count_partial_num_hits (r d : ℕ) (hd : 0 < d) (hr : r < d) :
    (hits r d (r+1) 1).card = N r d + N r (2*d) := by
  have h : hits r d (r+1) 1 = (triangle r).filter (fun i => d ∣ numerator r i) := by
    simp only [hits,one_mul]
    rfl
  rw [h,card_two_multiples _ _ _ hd (fun i hi => ⟨num_pos r i,(num_bound r i hi).trans_le (by omega)⟩),
    count_numerator,count_numerator]

private theorem count_full_num_hits (r d : ℕ) (hd : 0 < d) (hr : r < d) :
    (hits d d (r+1) 1).card = N d (2*d-r) + N d (3*d-r) := by
  let f (i : ℕ × ℕ) := r+1+i.1+i.2
  have h : hits d d (r+1) 1 = (triangle d).filter (fun i => d ∣ f i) := by
    simp [hits,f]
  have hf (i : ℕ × ℕ) (hi : i ∈ triangle d) : 0 < f i ∧ f i < 3*d := by
    rw [mem_triangle] at hi
    dsimp [f]
    omega
  have h₁ : (triangle d).filter (fun i => f i=d) =
      (triangle d).filter (fun i => numerator d i = 2*d-r) := by
    apply Finset.ext
    intro i
    rw [mem_filter,mem_filter]
    refine and_congr_right fun _ => ?_
    dsimp [f,numerator]
    omega
  have h₂ : (triangle d).filter (fun i => f i=2*d) =
      (triangle d).filter (fun i => numerator d i = 3*d-r) := by
    apply Finset.ext
    intro i
    rw [mem_filter,mem_filter]
    refine and_congr_right fun _ => ?_
    dsimp [f,numerator]
    omega
  rw [h,card_two_multiples _ _ _ hd hf,h₁,h₂,count_numerator,count_numerator]

theorem numerator_has_more_hits (n d : ℕ) (hd : 0 < d) :
    ((triangle n).filter fun i => d ∣ denominator i).card ≤ 
      ((triangle n).filter fun i => d ∣ numerator n i).card := by
  let r := n%d
  have hr : r < d := Nat.mod_lt _ hd
  have hle (q : ℕ) : (hits (d*q+r) d 1 2).card ≤ (hits (d*q+r) d (r+1) 1).card := by
    induction q with
    | zero =>
      simpa only [mul_zero,zero_add,count_den_hits r d hd hr.le,count_partial_num_hits r d hd hr]
        using partial_count d r hr
    | succ q ih =>
      rw [show d*(q+1)+r = d+(d*q+r) by ring,hits_step _ _ _ _ hd,hits_step _ _ _ _ hd]
      have hf : (hits d d 1 2).card ≤ (hits d d (r+1) 1).card := by
        rw [count_den_hits _ _ hd le_rfl,full_denominator,count_full_num_hits _ _ hd hr]
        exact full_numerator d r hr
      omega
  have hn : d*(n/d)+r=n := by dsimp [r]; exact Nat.div_add_mod n d
  have h := hle (n/d)
  rw [hn] at h
  have hh : hits n d (r+1) 1 = (triangle n).filter (fun i => d ∣ numerator n i) := by
    apply Finset.ext
    intro i
    unfold hits
    rw [mem_filter,mem_filter]
    simp only [one_mul,numerator]
    refine and_congr_right fun _ => ?_
    conv_rhs => rw [← hn]
    rw [show d*(n/d)+r+1+i.1+i.2 = (r+1+i.1+i.2)+d*(n/d) by ring]
    exact Nat.dvd_add_iff_left (dvd_mul_right d (n/d))
  rw [hh] at h
  exact h

private theorem sum_factorization_by_hits (n p : ℕ) (hp : p.Prime) (f : ℕ × ℕ → ℕ)
    (hf : ∀ i ∈ triangle n, 0 < f i ∧ f i < 3*n) :
    (∏ i ∈ triangle n, f i).factorization p =
      ∑ k ∈ Ico 1 (3*n), ((triangle n).filter fun i => p^k ∣ f i).card := by
  rw [Nat.factorization_prod_apply (fun i hi => (hf i hi).1.ne')]
  have hf' (i : ℕ × ℕ) (hi : i ∈ triangle n) : f i < p^(3*n) :=
    (hf i hi).2.trans_le (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt))
  calc
    _ = ∑ i ∈ triangle n, ∑ k ∈ Ico 1 (3*n), (if p^k ∣ f i then 1 else 0 : ℕ) := by
      apply sum_congr rfl
      intro i hi
      rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (hf i hi).1 (hf' i hi),
        ← sum_filter]
      simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      rw [← sum_filter]
      simp

theorem denominator_dvd_numerator (n : ℕ) :
    (∏ i ∈ triangle n, denominator i) ∣ (∏ i ∈ triangle n, numerator n i) := by
  rw [← Nat.factorization_le_iff_dvd
    (prod_ne_zero_iff.mpr fun i _ => (den_pos i).ne')
    (prod_ne_zero_iff.mpr fun i _ => (num_pos n i).ne')]
  intro p
  by_cases hp : p.Prime
  · rw [sum_factorization_by_hits n p hp denominator (fun i hi => ⟨den_pos i,den_bound n i hi⟩),
      sum_factorization_by_hits n p hp (numerator n) (fun i hi => ⟨num_pos n i,num_bound n i hi⟩)]
    exact sum_le_sum (fun k _ => numerator_has_more_hits n (p^k) (pow_pos hp.pos k))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

end PlaneCongruence

/- Group the factors by value, then by their residues modulo p. -/

namespace PlaneCongruence

open Finset

def unitProduct (p : ℕ) (m : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Ico 1 p, r^(m r) * (p+r)^(m (p+r)) * (2*p+r)^(m (2*p+r))

private theorem residue_product (p : ℕ) (m : ℕ → ℕ) (hp : 0 < p) :
    (∏ z ∈ (Ico 1 (3*p)).filter (fun z => ¬p ∣ z), z^(m z)) = unitProduct p m := by
  have h : (∏ ij ∈ Ico 1 p ×ˢ range 3, (ij.1+ij.2*p)^(m (ij.1+ij.2*p))) =
      ∏ z ∈ (Ico 1 (3*p)).filter (fun z => ¬p ∣ z), z^(m z) := by
    apply prod_bij (fun i _ => i.1+i.2*p)
    · intro i hi
      rw [mem_product,mem_Ico,mem_range] at hi
      rw [mem_filter,mem_Ico,Nat.dvd_iff_mod_eq_zero]
      have hh : (i.1+i.2*p)%p = i.1 := by
        rw [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hi.1.2]
      rw [hh]
      have hb : i.2*p ≤ 2*p := Nat.mul_le_mul_right p (by omega)
      omega
    · intro i hi j hj e
      rw [mem_product,mem_Ico,mem_range] at hi hj
      have he := congrArg (fun k => k%p) e
      simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi.1.2,
        Nat.mod_eq_of_lt hj.1.2] at he
      refine Prod.ext he ?_
      rw [he] at e
      exact (Nat.mul_left_inj hp.ne').mp (Nat.add_left_cancel e)
    · intro z hz
      rw [mem_filter,mem_Ico,Nat.dvd_iff_mod_eq_zero] at hz
      refine ⟨(z%p,z/p),?_,by simpa [mul_comm] using Nat.mod_add_div z p⟩
      rw [mem_product,mem_Ico,mem_range]
      exact ⟨⟨by omega,Nat.mod_lt _ hp⟩, (Nat.div_lt_iff_lt_mul hp).mpr hz.1.2⟩
    · intro i hi
      rfl
  rw [← h,prod_product,unitProduct]
  apply prod_congr rfl
  intro r hr
  simp only [prod_range_succ,prod_range_zero,zero_mul,one_mul,add_zero,
    Nat.reduceAdd, mul_comm r p, add_comm r p, add_comm r (2*p)]

private theorem factor_by_value (p : ℕ) (f : ℕ × ℕ → ℕ) (m : ℕ → ℕ)
    (hf : ∀ i ∈ triangle p, 0 < f i ∧ f i < 3*p)
    (hm : ∀ z > 0, ((triangle p).filter fun i => f i=z).card = m z) :
    (∏ i ∈ triangle p, f i) = ∏ z ∈ Ico 1 (3*p), z^(m z) := by
  calc
    _ = ∏ z ∈ Ico 1 (3*p), ∏ i ∈ (triangle p).filter (fun i => f i=z), z := by
      symm
      apply prod_fiberwise_of_maps_to' (g := f)
      intro i hi
      rw [mem_Ico]
      obtain ⟨h₁,h₂⟩ := hf i hi
      exact ⟨h₁,h₂⟩
    _ = _ := by
      apply prod_congr rfl
      intro z hz
      rw [prod_const,hm z (mem_Ico.mp hz).1]

theorem product_split (p : ℕ) (hp : 0 < p) (f : ℕ × ℕ → ℕ) (m : ℕ → ℕ)
    (hf : ∀ i ∈ triangle p, 0 < f i ∧ f i < 3*p)
    (hm : ∀ z > 0, ((triangle p).filter fun i => f i=z).card = m z) :
    (∏ i ∈ triangle p, f i) = p^(m p)*(2*p)^(m (2*p))*unitProduct p m := by
  rw [factor_by_value p f m hf hm, ← prod_filter_mul_prod_filter_not _ (fun z => p ∣ z),
    residue_product p m hp]
  have he : (Ico 1 (3*p)).filter (fun z => p ∣ z) = {p,2*p} := by
    ext z
    simp only [mem_filter,mem_Ico,mem_insert,mem_singleton]
    constructor
    · rintro ⟨⟨h₁,h₂⟩,k,rfl⟩
      have hpos : 0 < k := by
        by_contra! h
        simp [show k=0 by omega] at h₁
      have hlt : k < 3 := (Nat.mul_lt_mul_left hp).mp (by simpa [mul_comm p 3] using h₂)
      interval_cases k <;> simp [mul_comm]
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega,by omega⟩,dvd_rfl⟩
      · exact ⟨⟨by omega,by omega⟩,dvd_mul_left p 2⟩
  rw [he,prod_insert (by simp; omega : p ∉ ({2*p} : Finset ℕ)),prod_singleton]

end PlaneCongruence

/- Expand the units in ZMod (p ^ 2). The linear terms cancel in reflected pairs. -/

namespace PlaneCongruence

open Finset

private theorem linear_mul {R : Type*} [CommRing R] {t : R} (ht : t*t = 0) (a b : R) :
    (1+t*a)*(1+t*b) = 1+t*(a+b) := by
  calc
    _ = 1+t*(a+b)+(t*t)*(a*b) := by ring
    _ = _ := by rw [ht,zero_mul,add_zero]

private theorem linear_pow {R : Type*} [CommRing R] {t : R} (ht : t*t=0) (a : R) (k : ℕ) :
    (1+t*a)^k = 1+t*((k:R)*a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,ih,linear_mul ht,Nat.cast_succ,add_mul,one_mul]

private theorem linear_prod {R α : Type*} [CommRing R] {t : R} (ht : t*t=0)
    (s : Finset α) (a : α → R) :
    (∏ r ∈ s, (1+t*a r)) = 1+t*(∑ r ∈ s, a r) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert r s hr ih => rw [prod_insert hr,sum_insert hr,ih,linear_mul ht]

private theorem modulus_sq (p : ℕ) : (p : ZMod (p^2)) * (p : ZMod (p^2)) = 0 := by
  calc
    _ = ((p*p : ℕ) : ZMod (p^2)) := (Nat.cast_mul p p).symm
    _ = ((p^2 : ℕ) : ZMod (p^2)) := congrArg (fun z : ℕ => (z : ZMod (p^2))) (pow_two p).symm
    _ = 0 := ZMod.natCast_self (p^2)

private theorem residue_unit (p r : ℕ) (hp : p.Prime) (hr : r ∈ Ico 1 p) :
    IsUnit (r : ZMod (p^2)) := by
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2)]
  exact fun h => (Nat.not_le_of_lt (mem_Ico.mp hr).2) (Nat.le_of_dvd (mem_Ico.mp hr).1 h)

private theorem shifted_unit (p r j : ℕ) (hp : p.Prime) (hr : r ∈ Ico 1 p) :
    IsUnit ((j*p+r : ℕ) : ZMod (p^2)) := by
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2)]
  intro h
  have hr' : p ∣ r := (Nat.dvd_add_iff_right (dvd_mul_left p j)).mpr h
  exact (Nat.not_le_of_lt (mem_Ico.mp hr).2) (Nat.le_of_dvd (mem_Ico.mp hr).1 hr')

theorem unitProduct_isUnit (p : ℕ) (m : ℕ → ℕ) (hp : p.Prime) :
    IsUnit ((unitProduct p m : ℕ) : ZMod (p^2)) := by
  rw [unitProduct,Nat.cast_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one ?_
  intro r hr
  push_cast
  have h₁ := (residue_unit p r hp hr).pow (m r)
  have h₂ := (shifted_unit p r 1 hp hr).pow (m (p+r))
  have h₃ := (shifted_unit p r 2 hp hr).pow (m (2*p+r))
  simp only [one_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h₂ h₃
  exact (h₁.mul h₂).mul h₃

private def weighting (p : ℕ) (m : ℕ → ℕ) (r : ℕ) : ZMod (p^2) :=
  ((m (p+r) : ZMod (p^2)) + 2*(m (2*p+r) : ZMod (p^2))) * (r : ZMod (p^2))⁻¹

private theorem unitProduct_expansion (p : ℕ) (m : ℕ → ℕ) (hp : p.Prime) :
    (unitProduct p m : ZMod (p^2)) =
      (∏ r ∈ Ico 1 p, (r : ZMod (p^2))^(m r + m (p+r) + m (2*p+r))) *
      (1+(p : ZMod (p^2))*(∑ r ∈ Ico 1 p, weighting p m r)) := by
  rw [unitProduct,Nat.cast_prod,← linear_prod (modulus_sq p),← prod_mul_distrib]
  apply prod_congr rfl
  intro r hr
  let R := ZMod (p^2)
  let x : R := r
  let t : R := p
  have hx : x*x⁻¹ = 1 := ZMod.mul_inv_of_unit x (residue_unit p r hp hr)
  have h₁ : (p : R)+(r : R) = x*(1+t*x⁻¹) := by
    change t+x = x*(1+t*x⁻¹)
    calc
      _ = x+t*(x*x⁻¹) := by rw [hx]; ring
      _ = _ := by ring
  have h₂ : (2 : R)*(p : R)+(r : R) = x*(1+t*(2*x⁻¹)) := by
    change 2*t+x = x*(1+t*(2*x⁻¹))
    calc
      _ = x+2*t*(x*x⁻¹) := by rw [hx]; ring
      _ = _ := by ring
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Nat.cast_pow,Nat.cast_add,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,h₁,h₂,mul_pow,mul_pow,
    linear_pow (modulus_sq p),linear_pow (modulus_sq p)]
  rw [pow_add,pow_add]
  calc
    _ = (x^m r * x^m (p+r) * x^m (2*p+r)) *
        ((1+t*((m (p+r) : R)*x⁻¹))*(1+t*((m (2*p+r) : R)*(2*x⁻¹)))) := by ring
    _ = _ := by rw [linear_mul (modulus_sq p),weighting]; ring

private theorem weighted_sum_zero (p : ℕ) (hp : p.Prime) (hp₅ : 5 ≤ p)
    (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    (∑ r ∈ Ico 1 p, (p : ZMod (p^2)) * ((firstOrder p r : ℤ) : ZMod (p^2)) *
      (r : ZMod (p^2))⁻¹) = 0 := by
  let R := ZMod (p^2)
  let t : R := p
  let F (r : ℕ) : R := t * (firstOrder p r : R) * (r : R)⁻¹
  change (∑ r ∈ Ico 1 p, F r) = 0
  have mem_reflect (r : ℕ) (hr : r ∈ Ico 1 p) : p-r ∈ Ico 1 p := by
    rw [mem_Ico] at hr ⊢
    omega
  have reflect : (∑ r ∈ Ico 1 p, F (p-r)) = ∑ r ∈ Ico 1 p, F r := by
    apply sum_bij (fun r _ => p-r)
    · exact mem_reflect
    · intro i hi j hj h
      rw [mem_Ico] at hi hj
      omega
    · intro j hj
      refine ⟨p-j,mem_reflect j hj,?_⟩
      rw [mem_Ico] at hj
      omega
    · intro i hi
      rfl
  have pair (r : ℕ) (hr : r ∈ Ico 1 p) : F r+F (p-r)=0 := by
    let x : R := r
    let y : R := ((p-r : ℕ) : R)
    have hrr := (mem_Ico.mp hr).2
    have hxy : x+y=t := by
      have hn : r+(p-r) = p := by omega
      change (r : R) + ((p-r : ℕ) : R) = (p : R)
      rw [← Nat.cast_add,hn]
    have hx := ZMod.mul_inv_of_unit x (residue_unit p r hp hr)
    have hy := ZMod.mul_inv_of_unit y (residue_unit p (p-r) hp (mem_reflect r hr))
    let e : R := (firstOrder p r : ℤ)
    have he : firstOrder p (p-r) = firstOrder p r :=
      reflect_order p r hp₅ h2 h3 (mem_Ico.mp hr).1 hrr
    dsimp only [F]
    rw [he]
    change t*e*x⁻¹ + t*e*y⁻¹ = 0
    calc
      _ = t*e*x⁻¹*(y*y⁻¹) + t*e*y⁻¹*(x*x⁻¹) := by rw [hx,hy,mul_one,mul_one]
      _ = (t*(x+y))*(e*x⁻¹*y⁻¹) := by ring
      _ = 0 := by rw [hxy,modulus_sq p,zero_mul]
  have hzero : (∑ r ∈ Ico 1 p, F r) + (∑ r ∈ Ico 1 p, F r) = 0 := by
    calc
      _ = (∑ r ∈ Ico 1 p, F r) + (∑ r ∈ Ico 1 p, F (p-r)) :=
        congrArg (fun z => (∑ r ∈ Ico 1 p, F r)+z) reflect.symm
      _ = _ := by rw [← sum_add_distrib]; exact sum_eq_zero pair
  have hunit : IsUnit (2 : R) := by
    exact_mod_cast residue_unit p 2 hp (mem_Ico.mpr (by omega))
  apply hunit.mul_left_cancel
  rw [two_mul,hzero,mul_zero]

theorem equal_unitProducts (p : ℕ) (hp : p.Prime) (hp₅ : 5 ≤ p)
    (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    (unitProduct p (N p) : ZMod (p^2)) = (unitProduct p (D p) : ZMod (p^2)) := by
  rw [unitProduct_expansion p _ hp,unitProduct_expansion p _ hp]
  congr 1
  · apply prod_congr rfl
    intro r hr
    obtain ⟨hr₀,hrp⟩ := mem_Ico.mp hr
    rw [show N p r = 0 by unfold N numeratorMultiplicity; omega, zero_add]
    rw [residue_count p r hp₅ h2 h3 hr₀ hrp,add_assoc]
  · congr 1
    apply sub_eq_zero.mp
    rw [← mul_sub,← sum_sub_distrib,mul_sum]
    convert weighted_sum_zero p hp hp₅ h2 h3 using 1
    apply sum_congr rfl
    intro r hr
    simp [weighting,firstOrder,Int.cast_sub,Int.cast_add,Int.cast_mul]
    ring

end PlaneCongruence

/- Telescope the original product and transfer the modular equality to the rational statement. -/

namespace PlaneCongruence

open Finset

private theorem telescope (i j n : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hjn : j ≤ n) :
    (∏ k ∈ Icc j n, ((i+j+k : ℚ)-1)/((i+j+k : ℚ)-2)) =
      ((i+j+n : ℚ)-1)/((i+j+j : ℚ)-2) := by
  induction n, hjn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [prod_Icc_succ_top (by omega), ih, Nat.cast_succ]
    have h : (i+j+n : ℚ)-1 ≠ 0 := by
      have hi' : (1:ℚ) ≤ i := by exact_mod_cast hi
      have hj' : (1:ℚ) ≤ j := by exact_mod_cast hj
      have hn' : (0:ℚ) ≤ n := by positivity
      linarith
    have h' : (i+j+(n+1) : ℚ)-2 = (i+j+n : ℚ)-1 := by ring
    rw [h']
    field_simp <;> ring

private theorem shifted_products (n : ℕ) (F : ℕ → ℕ → ℚ) :
    (∏ i ∈ Icc 1 n, ∏ j ∈ Icc i n, F i j) =
      ∏ u ∈ triangle n, F (u.1+1) (u.2+1) := by
  let old := ((Icc 1 n) ×ˢ (Icc 1 n)).filter fun i : ℕ × ℕ => i.1 ≤ i.2
  have hold : (∏ i ∈ old,F i.1 i.2) = ∏ i ∈ Icc 1 n, ∏ j ∈ Icc i n,F i j := by
    dsimp only [old]
    rw [prod_filter,prod_product]
    apply prod_congr rfl
    intro i hi
    rw [← prod_filter]
    congr 1
    ext j
    simp only [mem_filter,mem_Icc]
    rw [mem_Icc] at hi
    omega
  rw [← hold]
  symm
  apply prod_bij (fun u _ => (u.1+1,u.2+1))
  · intro u hu
    rw [mem_triangle] at hu
    change (u.1+1,u.2+1) ∈
      (((Icc 1 n) ×ˢ (Icc 1 n)).filter fun i : ℕ × ℕ => i.1 ≤ i.2)
    rw [mem_filter,mem_product,mem_Icc,mem_Icc]
    dsimp
    omega
  · intro i hi j hj h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)
  · intro u hu
    change u ∈ (((Icc 1 n) ×ˢ (Icc 1 n)).filter fun i : ℕ × ℕ => i.1 ≤ i.2) at hu
    rw [mem_filter,mem_product,mem_Icc,mem_Icc] at hu
    refine ⟨(u.1-1,u.2-1),?_,Prod.ext ?_ ?_⟩
    · rw [mem_triangle]
      dsimp
      omega
    · dsimp
      omega
    · dsimp
      omega
  · intro u hu
    rfl

private theorem ratio (n : ℕ) :
    OMA.S_oeis_a005157.a n =
      ((∏ i ∈ triangle n,numerator n i : ℕ) : ℚ) /
      ((∏ i ∈ triangle n,denominator i : ℕ) : ℚ) := by
  rw [OMA.S_oeis_a005157.a]
  have h : (∏ i ∈ Icc 1 n, ∏ j ∈ Icc i n,
      ∏ k ∈ Icc j n, ((i+j+k : ℚ)-1)/((i+j+k : ℚ)-2)) =
      ∏ i ∈ Icc 1 n, ∏ j ∈ Icc i n, ((i+j+n : ℚ)-1)/((i+j+j : ℚ)-2) := by
    apply prod_congr rfl
    intro i hi
    apply prod_congr rfl
    intro j hj
    exact telescope i j n (mem_Icc.mp hi).1
      ((mem_Icc.mp hi).1.trans (mem_Icc.mp hj).1) (mem_Icc.mp hj).2
  rw [h, shifted_products, Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
  apply prod_congr rfl
  intro u hu
  simp only [numerator,denominator,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  congr 1 <;> ring

private theorem cross_products (p : ℕ) (hp : p.Prime) (hp₅ : 5 ≤ p)
    (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    (∏ i ∈ triangle p, numerator p i)*unitProduct p (D p) =
       (∏ i ∈ triangle p, denominator i)*(2^(D p p)*unitProduct p (N p)) := by
  rw [product_split p hp.pos (numerator p) (N p)
       (fun i hi => ⟨num_pos p i,num_bound p i hi⟩) (fun z _ => count_numerator p z),
      product_split p hp.pos denominator (D p)
       (fun i hi => ⟨den_pos i,den_bound p i hi⟩) (count_denominator p)]
  obtain ⟨hz,hs⟩ := multiples p hp₅ h2 h3
  rw [hz,hs,pow_zero,one_mul,pow_add,mul_pow]
  ring

private theorem congruence (p : ℕ) (hp : p.Prime) (hp₅ : 5 ≤ p)
    (h2 : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    ∃ m : ℤ, OMA.S_oeis_a005157.a p - (2 : ℚ)^(D p p) = (p : ℚ)^2*m := by
  let b := ∏ i ∈ triangle p,denominator i
  let U := unitProduct p (N p)
  let V := unitProduct p (D p)
  let e := D p p
  have hb : b ≠ 0 := prod_ne_zero_iff.mpr fun i _ => (den_pos i).ne'
  obtain ⟨a,ha⟩ := denominator_dvd_numerator p
  change (∏ i ∈ triangle p,numerator p i) = b*a at ha
  have haRat : OMA.S_oeis_a005157.a p = (a : ℚ) := by
    rw [ratio,ha,Nat.cast_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hb)
  have haMul : a*V = 2^e*U := by
    apply (Nat.mul_right_inj hb).mp
    calc
      b*(a*V) = (∏ i ∈ triangle p,numerator p i)*V := by rw [ha,mul_assoc]
      _ = _ := cross_products p hp hp₅ h2 h3
  let R := ZMod (p^2)
  have haMod : (a : R) = (2 : R)^e := by
    have he : ((a*V : ℕ) : ZMod (p^2)) = ((2^e*U : ℕ) : ZMod (p^2)) :=
      congrArg (fun z : ℕ => (z : ZMod (p^2))) haMul
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at he
    change (a : ZMod (p^2))*(unitProduct p (D p) : ZMod (p^2)) =
      (2 : ZMod (p^2))^e*(unitProduct p (N p) : ZMod (p^2)) at he
    rw [equal_unitProducts p hp hp₅ h2 h3] at he
    exact (unitProduct_isUnit p (D p) hp).mul_right_cancel he
  have hd : ((p^2 : ℕ) : ℤ) ∣ (a : ℤ)-(2 : ℤ)^e := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [Int.cast_sub,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
    exact sub_eq_zero.mpr haMod
  obtain ⟨m,hm⟩ := hd
  refine ⟨m,?_⟩
  rw [haRat]
  exact_mod_cast hm

end PlaneCongruence

open PlaneCongruence

theorem OMA.solution : type_of% @OMA.S_oeis_a005157.main := by
  constructor <;> intro p hp hr
  · have h := hp.two_le
    have hx := (p_factor p (by omega) (by omega) (by omega)).1 hr
    rw [← hx]
    exact congruence p hp (by omega) (by omega) (by omega)
  · have hx := (p_factor p (by omega) (by omega) (by omega)).2 hr
    rw [← hx]
    exact congruence p hp (by omega) (by omega) (by omega)
