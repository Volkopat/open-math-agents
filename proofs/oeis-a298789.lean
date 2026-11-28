import OMAStatements.S_oeis_a298789

-- Credit: @Aryan-Poonacha
-- Colin Barker conjectured both identities in January 2018.
-- The proof computes the geodesic distance in Sigrist’s horizontal-line model
-- of the bey net, counts line intersections with each sphere, then sums.

namespace BeyMetric
open OMA.S_oeis_a298789

/-- Minimum required number of horizontal steps to reach a given line. -/
def gap (r : ℤ) : ℤ := if 0 < r then (r+1)/2-1 else (-r)/2

def depth (v : Vertex) : ℤ :=
  max v.1 (-v.1) + max (max v.2 (-v.2)) (gap v.1 + (v.2 - gap v.1)%2)

theorem depth_zero (v : Vertex) : depth v ≤ 0 ↔ v = (0,0) := by
  obtain ⟨r,u⟩ := v
  simp [depth,gap,Prod.ext_iff]; split_ifs <;> omega

theorem adjacent (r u : ℤ) (w : Vertex) : w ∈ neighbors (r,u) ↔
    w = (r,u-1) ∨ w = (r,u+1) ∨ (vertical r u ∧ w=(r+1,u)) ∨
    (vertical (r-1) u ∧ w=(r-1,u)) := by
  by_cases h : vertical r u <;> by_cases k : vertical (r-1) u <;>
    simp [neighbors,h,k]

set_option maxHeartbeats 5000000 in
theorem next (v : Vertex) :
    (∀ w ∈ neighbors v, depth w ≤ depth v + 1) ∧
    (v ≠ (0,0) → ∃ w ∈ neighbors v, depth w < depth v) := by
  obtain ⟨r,u⟩ := v
  constructor
  · intro w hw
    rcases (adjacent r u w).mp hw with rfl | rfl | ⟨hv,rfl⟩ | ⟨hv,rfl⟩
    all_goals simp only [depth, gap, vertical] at *
    all_goals split_ifs <;> omega
  · intro ne
    have nz : r ≠ 0 ∨ u ≠ 0 := by
      by_contra! he
      exact ne (Prod.ext he.1 he.2)
    have h : depth (r,u-1) < depth (r,u) ∨ depth (r,u+1) < depth (r,u) ∨
        (vertical r u ∧ depth (r+1,u) < depth (r,u)) ∨
        (vertical (r-1) u ∧ depth (r-1,u) < depth (r,u)) := by
      simp only [depth,gap,vertical] at *
      split_ifs <;> omega
    rcases h with h | h | ⟨hv,h⟩ | ⟨hv,h⟩
    · exact ⟨_,(adjacent r u _).mpr (Or.inl rfl),h⟩
    · exact ⟨_,(adjacent r u _).mpr (Or.inr (Or.inl rfl)),h⟩
    · exact ⟨_,(adjacent r u _).mpr (Or.inr (Or.inr (Or.inl ⟨hv,rfl⟩))),h⟩
    · exact ⟨_,(adjacent r u _).mpr (Or.inr (Or.inr (Or.inr ⟨hv,rfl⟩))),h⟩

theorem edge (v w : Vertex) : w ∈ neighbors v ↔ v ∈ neighbors w := by
  suffices forward : ∀ v w : Vertex, w ∈ neighbors v → v ∈ neighbors w from
    ⟨forward v w,forward w v⟩
  rintro ⟨r,u⟩ w h
  rcases (adjacent r u w).mp h with rfl | rfl | ⟨hv,rfl⟩ | ⟨hv,rfl⟩
  all_goals rw [adjacent]
  all_goals simp [*]

theorem ball_depth (n : ℕ) (v : Vertex) : v ∈ ball n ↔ depth v ≤ n := by
  induction n generalizing v with
  | zero => simpa [ball,eq_comm] using (depth_zero v).symm
  | succ n ih =>
    rw [ball,Finset.mem_union,Finset.mem_biUnion]
    constructor
    · rintro (h | ⟨w,hw,e⟩)
      · have := (ih v).mp h; omega
      · have := (ih w).mp hw
        have := (next w).1 v e
        omega
    · intro h
      by_cases old : depth v ≤ n
      · exact Or.inl ((ih v).mpr old)
      · have nz : v ≠ (0,0) := by
          intro he
          have := (depth_zero v).mpr he
          omega
        obtain ⟨w,e,hw⟩ := (next v).2 nz
        exact Or.inr ⟨w,(ih w).mpr (by omega),(edge v w).mp e⟩

end BeyMetric

namespace BeyColumns

noncomputable def cols (g h : ℤ) : Finset ℤ :=
  if h < g then ∅ else if h ≤ g+1 then
    (Finset.Icc 0 h).image (fun i => 2*i-h) else {-h,h}

theorem mem_cols {g h u : ℤ} (hg : 0 ≤ g) :
    u ∈ cols g h ↔ max (max u (-u)) (g+(u-g)%2) = h := by
  unfold cols
  split_ifs with h₁ h₂
  · simp; omega
  · simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨w,⟨lo,hi⟩,rfl⟩
      omega
    · intro hh
      refine ⟨(u+h)/2, ⟨?_,?_⟩,?_⟩ <;> omega
  · simp; omega

theorem card_cols {g h : ℤ} (hg : 0 ≤ g) :
    ((cols g h).card : ℤ) = if h<g then 0 else if h≤g+1 then h+1 else 2 := by
  unfold cols
  split_ifs with h₁ h₂
  · simp
  · rw [Finset.card_image_of_injective _ (by intro a b eq; change 2*a-h=2*b-h at eq; omega), Int.card_Icc]
    omega
  · have : -h ≠ h := by omega
    simp [this]

end BeyColumns

namespace BeyBands

def part (b c n k : ℕ) : ℤ :=
  if 3*k+b=n then (k:ℤ)+c+1 else if 3*k+b+1=n then (k:ℤ)+c+2
  else if 3*k+b+1<n then 2 else 0

def total (b c n : ℕ) : ℤ := ∑ k ∈ Finset.range (n+1), part b c n k

theorem total_value (b c n : ℕ) (hb : b+1 ≤ n) :
    total b c n = 2*((((n-b+1)/3 : ℕ)):ℤ) +
      (if (n-b)%3=0 then ((((n-b)/3 : ℕ)):ℤ)+c+1 else 0) +
      (if (n-b-1)%3=0 then ((((n-b-1)/3 : ℕ)):ℤ)+c+2 else 0) := by
  let cut :=  (n-b+1)/3
  let p := (n-b)/3
  let q := (n-b-1)/3
  have term (k : ℕ) : part b c n k =
      (if k<cut then (2:ℤ) else 0) +
      (if (n-b)%3=0 ∧ k=p then (p:ℤ)+c+1 else 0) +
      (if (n-b-1)%3=0 ∧ k=q then (q:ℤ)+c+2 else 0) := by
    dsimp [part,cut,p,q]; split_ifs <;> omega
  have cutoff : (Finset.range (n+1)).filter (fun k => k<cut) = Finset.range cut := by
    ext k; simp [cut]; omega
  simp only [total,term,Finset.sum_add_distrib]
  rw [← Finset.sum_filter,cutoff]
  have hp : p<n+1 := by dsimp [p]; omega
  have hq : q<n+1 := by dsimp [q]; omega
  by_cases h : (n-b)%3=0 <;> by_cases j : (n-b-1)%3=0 <;>
    simp [h,j,Finset.mem_range,hp,hq,cut,p,q] <;> ring

set_option maxHeartbeats 1500000 in
theorem closed (n : ℕ) (hn : 4 ≤ n) :
    2 + 2 * total 1 0 n + total 3 1 n + total 2 0 n =
    if n%3=0 then 10*((n/3:ℕ):ℤ) else
    11*((n/3:ℕ):ℤ) + (if n%3=1 then 4 else 7) := by
  rw [total_value _ _ _ (by omega),total_value _ _ _ (by omega),total_value _ _ _ (by omega)]
  have cases' : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases cases' with h|h|h <;> simp (disch := omega) only [if_pos,if_neg] <;> omega

end BeyBands

namespace BeyCount
open OMA.S_oeis_a298789 BeyMetric BeyColumns BeyBands

def sphere (n : ℕ) := (ball n).filter (fun v => depth v=n)

@[simp] theorem mem_sphere (n : ℕ) (v : Vertex) : v ∈ sphere n ↔ depth v = n := by
  simp [sphere,ball_depth]; omega

def key (r : ℤ) : ℕ × Fin 4 :=
  if 0 ≤ r then ((r/2).toNat, if r%2=1 then 0 else 2)
  else (((-r-1)/2).toNat, if r%2=0 then 1 else 3)

def ordinate (k : ℕ) : Fin 4 → ℤ
  | 0 => 2*(k:ℤ)+1
  | 1 => -2*(k:ℤ)-2
  | 2 => 2*(k:ℤ)
  | 3 => -2*(k:ℤ)-1

theorem key_ordinate (k : ℕ) (t : Fin 4) : key (ordinate k t) = (k,t) := by
  fin_cases t <;> simp [key,ordinate] <;> split_ifs <;> simp <;> omega

theorem ordinate_key (r : ℤ) : ordinate (key r).1 (key r).2 = r := by
  by_cases h : 0 ≤ r <;> by_cases hr : r%2=1 <;> by_cases h0 : r%2=0 <;>
    simp [key,ordinate,h,hr,h0] <;> omega

theorem row_bound (n : ℕ) (v : Vertex) (h : v∈sphere n) : (key v.1).1<n+1 := by
  obtain ⟨r,u⟩ := v
  rw [mem_sphere] at h
  simp only [depth,gap] at h
  simp [key]
  split_ifs at * <;> omega

def fiber (n k : ℕ) (t : Fin 4) := (sphere n).filter (fun v => key v.1=(k,t))

theorem fiber_eq (n k : ℕ) (t : Fin 4) :
    fiber n k t = let r := ordinate k t
      (cols (gap r) (n - max r (-r))).image (fun u => (r,u)) := by
  dsimp only
  let r := ordinate k t
  have hg : 0 ≤ gap r := by simp [gap]; split_ifs <;> omega
  ext v
  obtain ⟨s,z⟩ := v
  simp only [fiber,Finset.mem_filter,mem_sphere,Finset.mem_image]
  constructor
  · rintro ⟨hd,hk⟩
    have hs : s=r := by
      have he := ordinate_key s
      change key s = (k,t) at hk
      rw [hk] at he
      exact he.symm
    subst s
    refine ⟨z,(mem_cols hg).mpr ?_,rfl⟩
    unfold depth at hd; dsimp only at hd; omega
  · rintro ⟨i,hi,he⟩
    cases he
    refine ⟨?_,key_ordinate k t⟩
    have d := (mem_cols hg).mp hi
    change max r (-r) + max (max z (-z)) (gap r+(z-gap r)%2)=_
    omega

theorem fiber_card (n k : ℕ) (t : Fin 4) :
    ((fiber n k t).card : ℤ) =
      let r := ordinate k t
      let h := (n:ℤ) - max r (-r)
      if h < gap r then 0 else if h ≤ gap r+1 then h+1 else 2 := by
  rw [fiber_eq]
  dsimp only
  rw [Finset.card_image_of_injective _ (by intro i j eq; exact (Prod.mk.inj eq).2)]
  apply card_cols
  simp [gap]; split_ifs <;> omega

end BeyCount

namespace BeyCount
open OMA.S_oeis_a298789 BeyMetric BeyColumns BeyBands

set_option maxHeartbeats 2000000 in
theorem group_count (n k : ℕ) (hn : 4 ≤ n) :
    ∑ t : Fin 4, ((fiber n k t).card : ℤ) =
    2*part 1 0 n k + part 3 1 n k + (if k=0 then 2 else part 2 0 n (k-1)) := by
  cases k with
  | zero =>
    simp [Fin.sum_univ_succ,fiber_card,ordinate,gap,part]
    split_ifs <;> omega
  | succ k =>
    have cases' : n<3*k+2 ∨ n=3*k+2 ∨ n=3*k+3 ∨ n=3*k+4 ∨ n=3*k+5 ∨ n=3*k+6 ∨ n=3*k+7 ∨
        3*k+7<n := by omega
    simp [Fin.sum_univ_succ,fiber_card,ordinate,gap,part]
    rcases cases' with h|h|h|h|h|h|h|h <;> simp (disch := omega) <;> omega

theorem sphere_closed (n : ℕ) (hn : 4 ≤ n) :
    ((sphere n).card : ℤ) = if n%3=0 then 10*((n/3:ℕ):ℤ) else
    11*((n/3:ℕ):ℤ) + (if n%3=1 then 4 else 7) := by
  rw [← BeyBands.closed n hn]
  have maps : ((sphere n):Set Vertex).MapsTo (fun v => key v.1)
      ((Finset.range (n+1) ×ˢ (Finset.univ : Finset (Fin 4))) : Finset _) := by
    intro f hf
    simpa using row_bound n f hf
  have sum := Finset.card_eq_sum_card_fiberwise maps
  rw [Finset.sum_product] at sum
  rw [sum]
  push_cast
  change ∑ k ∈ Finset.range (n+1), ∑ t : Fin 4, ((fiber n k t).card : ℤ) = _
  simp only [group_count n _ hn, Finset.sum_add_distrib]
  have shift : ∑ k ∈ Finset.range (n+1), (if k=0 then (2:ℤ) else part 2 0 n (k-1)) =
      total 2 0 n + 2 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true]
    unfold total
    rw [Finset.sum_range_succ]
    simp [part]; split_ifs <;> omega
  rw [shift,← Finset.mul_sum]
  unfold total
  ring

theorem source (n : ℕ) : a n = (sphere n).card := by
  cases n with
  | zero => decide +kernel
  | succ n =>
    have sub : ball n ⊆ ball (n+1) := by
      intro f hf
      rw [ball_depth] at *
      omega
    have eq : sphere (n+1) = ball (n+1) \ ball n := by
      ext f
      simp only [mem_sphere,Finset.mem_sdiff,ball_depth]
      omega
    have := Finset.card_sdiff_add_card_eq_card sub
    rw [eq]
    simp only [a]
    omega

theorem recurrence (n : ℕ) (hn : 6 < n) : a n = 2*a (n-3)-a (n-6) := by
  by_cases h : n<10
  · interval_cases n <;> decide +kernel
  · rw [source,source,source,sphere_closed n (by omega),sphere_closed (n-3) (by omega),
      sphere_closed (n-6) (by omega)]
    split_ifs <;> omega

end BeyCount

open OMA.S_oeis_a298789 BeyCount PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a298789.main := by
  refine ⟨?_,recurrence⟩
  let A : PowerSeries ℤ := mk a
  let X : PowerSeries ℤ := PowerSeries.X
  change A*((1-X)^2*(1+X+X^2)^2) = (1+X)^4*(1+X^2)
  have den : A*((1-X)^2*(1+X+X^2)^2) = A-C (2:ℤ)*(A*X^3)+A*X^6 := by
    simp only [map_ofNat]; ring
  have num : (1+X)^4*(1+X^2) =
      1+C (4:ℤ)*X+C (7:ℤ)*X^2+C (8:ℤ)*X^3+C (7:ℤ)*X^4+C (4:ℤ)*X^5+X^6 := by
    simp only [map_ofNat]; ring
  rw [den,num]
  ext n
  simp only [map_sub,map_add,coeff_C_mul]
  simp only [X,A,coeff_mul_X_pow',coeff_mk,coeff_one,coeff_X,coeff_X_pow]
  by_cases h : n≤6
  · interval_cases n <;> norm_num <;> decide +kernel
  · have hn := recurrence n (by omega)
    simp (disch := omega) only [if_pos,if_neg, mul_zero, add_zero]
    linarith
