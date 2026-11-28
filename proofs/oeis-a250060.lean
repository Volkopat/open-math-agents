import OMAStatements.S_oeis_a250060
import Mathlib

namespace OMA.Gaps250060

open OMA.S_oeis_a250060 Finset PowerSeries

private abbrev Pair := {s : Finset (Fin 7) // s.card = 2}
private abbrev Word (n : ℕ) := Fin 7 → Fin (n+1)

private def Weak {n : ℕ} (x : Word n) (s : Pair) : Prop :=
  ∀ i ∈ s.val, ∀ j ∉ s.val, x i ≤ x j

private def Gap {n : ℕ} (x : Word n) (s : Pair) : Prop :=
  ∀ i ∈ s.val, ∀ j ∉ s.val, x i < x j

private theorem weak_exists {n : ℕ} (x : Word n) : ∃ s : Pair, Weak x s := by
  let e := Tuple.sort x
  let s : Finset (Fin 7) := {e 0,e 1}
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  refine ⟨⟨s,by simp [s,h01]⟩,?_⟩
  intro i hi j hj
  obtain ⟨k,rfl⟩ := e.surjective j
  have hk : 1 < k := by
    by_contra! h
    have : k=0 ∨ k=1 := by omega
    rcases this with rfl | rfl <;> simp [s] at hj
  simp only [s,mem_insert,mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact Tuple.monotone_sort x (Fin.zero_le k)
  · exact Tuple.monotone_sort x hk.le

private theorem same {n : ℕ} {x : Word n} {s t : Pair} (hs : Gap x s) (ht : Weak x t) : s=t := by
  by_contra hn
  have one {a b : Pair} (h : a ≠ b) : ∃ i ∈ a.val, i ∉ b.val := by
    by_contra! hall
    exact h (Subtype.ext (eq_of_subset_of_card_le hall (by rw [a.property,b.property])))
  obtain ⟨i,hi,hit⟩ := one hn
  obtain ⟨j,hj,hjs⟩ := one (Ne.symm hn)
  exact (hs i hi j hjs).not_ge (ht j hj i hit)

private theorem valid {n : ℕ} (x : Word n) :
    good x = true ↔ ∃ s : Pair, Gap x s := by
  simp only [good,decide_eq_true_eq,Nat.lt_one_iff,forall_eq,zero_add,
    mem_powersetCard,subset_univ,true_and,OMA.S_oeis_a250060.get,Fin.is_lt,dif_pos]
  constructor
  · intro h
    obtain ⟨s,hs⟩ := weak_exists x
    refine ⟨s,fun i hi j hj => lt_of_le_of_ne (hs i hi j hj) ?_⟩
    intro eqn
    apply h
    exact ⟨s.val,s.property,(x i).val,(x i).isLt,
      fun k hk => (hs k hk j hj).trans_eq eqn.symm,
      ⟨i,hi,rfl⟩,fun k hk => hs i hi k hk,⟨j,hj,congrArg Fin.val eqn.symm⟩⟩
  · rintro ⟨s,hs⟩ ⟨t,ht,v,hv,lo,⟨i,hi,ei⟩,up,⟨j,hj,ej⟩⟩
    have ht' : Weak x ⟨t,ht⟩ := fun k hk l hl => (lo k hk).trans (up l hl)
    have hst : s.val=t := congrArg Subtype.val (same hs ht')
    have hh := hs i (hst ▸ hi) j (hst ▸ hj)
    change (x i).val < (x j).val at hh
    change (x i).val = v at ei
    change (x j).val = v at ej
    omega

private def Fits {n : ℕ} (x : Word n) (s : Pair) (b : Fin (n+1)) : Prop :=
  (∀ i ∈ s.val, x i ≤ b) ∧ (∃ i ∈ s.val, x i = b) ∧ ∀ j ∉ s.val, b < x j

private theorem fits_gap {n : ℕ} {x : Word n} {s : Pair} {b : Fin (n+1)}
    (h : Fits x s b) : Gap x s := fun i hi j hj => (h.1 i hi).trans_lt (h.2.2 j hj)

private theorem fits_exists {n : ℕ} {x : Word n} {s : Pair} (h : Gap x s) :
    ∃ b, Fits x s b := by
  have ne : s.val.Nonempty := card_pos.mp (by rw [s.property]; decide)
  let t := s.val.image x
  have nt : t.Nonempty := ne.image x
  let b := t.max' nt
  obtain ⟨i,hi,hei⟩ := mem_image.mp (t.max'_mem nt)
  exact ⟨b,fun j hj => t.le_max' _ (mem_image_of_mem x hj),⟨i,hi,hei⟩,
    fun j hj => lt_of_eq_of_lt (show b = x i from hei.symm) (h i hi j hj)⟩

private theorem fits_unique {n : ℕ} {x : Word n} {s t : Pair} {b c : Fin (n+1)}
    (h : Fits x s b) (g : Fits x t c) : s=t ∧ b=c := by
  have st := same (fits_gap h) (fun i hi j hj => (fits_gap g i hi j hj).le)
  subst t
  obtain ⟨i,hi,ei⟩ := h.2.1
  obtain ⟨j,hj,ej⟩ := g.2.1
  exact ⟨rfl,le_antisymm (ei ▸ g.1 i hi) (ej ▸ h.1 j hj)⟩

private abbrev Class (n : ℕ) (s : Pair) (b : Fin (n+1)) := {x : Word n // Fits x s b}

private def forget {n : ℕ} (z : Σ s : Pair, Σ b : Fin (n+1), Class n s b) :
    {x : Word n // good x = true} := ⟨z.2.2.val,(valid _).mpr ⟨z.1,fits_gap z.2.2.property⟩⟩

private theorem forget_bij (n : ℕ) : Function.Bijective (@forget n) := by
  constructor
  · rintro ⟨s,b,⟨x,h⟩⟩ ⟨t,c,⟨y,g⟩⟩ eqn
    have xy : x=y := congrArg Subtype.val eqn
    subst y
    obtain ⟨rfl,rfl⟩ := fits_unique h g
    rfl
  · rintro ⟨x,h⟩
    obtain ⟨s,hs⟩ := (valid x).mp h
    obtain ⟨b,hb⟩ := fits_exists hs
    exact ⟨⟨s,b,⟨x,hb⟩⟩,rfl⟩

private abbrev Low (s : Pair) (b : ℕ) :=
  {f : ↥s.val → Fin (b+1) // ∃ i, (f i).val = b}

private abbrev Outside (s : Pair) := {j : Fin 7 // j ∉ s.val}

private def unpack {n : ℕ} (s : Pair) (b : Fin (n+1)) :
    Class n s b ≃ Low s b.val × (Outside s → Fin (n-b.val)) where
  toFun x := (⟨fun i => ⟨(x.val i.val).val,Nat.lt_succ_of_le (x.property.1 _ i.property)⟩,by
    obtain ⟨i,hi,e⟩ := x.property.2.1
    exact ⟨⟨i,hi⟩,congrArg Fin.val e⟩⟩,fun j =>
      ⟨(x.val j.val).val-(b.val+1),by
        have := x.property.2.2 _ j.property
        change b.val < (x.val j.val).val at this
        have := (x.val j.val).isLt
        omega⟩)
  invFun y :=
    let x : Word n := fun j => if h : j ∈ s.val then
      ⟨(y.1.val ⟨j,h⟩).val,by have := (y.1.val ⟨j,h⟩).isLt; omega⟩
      else ⟨b.val+1+(y.2 ⟨j,h⟩).val,by have := (y.2 ⟨j,h⟩).isLt; omega⟩
    ⟨x, by
      refine ⟨fun i hi => ?_,?_,fun j hj => ?_⟩
      · change (x i).val ≤ b.val
        simpa [x,hi] using Nat.le_of_lt_succ (y.1.val ⟨i,hi⟩).isLt
      · obtain ⟨i,he⟩ := y.1.property
        exact ⟨i.val,i.property,Fin.ext (by simpa [x,i.property] using he)⟩
      · change b.val < (x j).val
        simp [x,hj]; omega⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    by_cases h : j ∈ s.val
    · simp [h]
    · have hh := x.property.2.2 j h
      change b.val < (x.val j).val at hh
      simp [h]; omega
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      apply Fin.ext
      simp [i.property]
    · funext i
      apply Fin.ext
      simp [i.property]

private theorem low_card (s : Pair) (b : ℕ) :
    (Fintype.card (Low s b) : ℤ) = (b+1 : ℤ)^2 - (b : ℤ)^2 := by
  classical
  let miss : {f : ↥s.val → Fin (b+1) // ¬ ∃ i, (f i).val=b} ≃ (↥s.val → Fin b) :=
    ⟨fun f i => ⟨(f.val i).val,by
      have ne : (f.val i).val ≠ b := fun e => f.property ⟨i,e⟩
      have := (f.val i).isLt
      omega⟩,fun g => ⟨fun i => (g i).castSucc,by
      rintro ⟨i,eqn⟩
      have := (g i).isLt
      change (g i).val=b at eqn
      omega⟩,fun _ => rfl,fun _ => rfl⟩
  have h := Fintype.card_congr (Equiv.sumCompl (fun f : ↥s.val → Fin (b+1) => ∃ i, (f i).val=b))
  rw [Fintype.card_sum,Fintype.card_congr miss] at h
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,s.property] at h
  change Fintype.card (Low s b) + b^2 = (b+1)^2 at h
  have hh : (Fintype.card (Low s b) : ℤ) + (b : ℤ)^2 = (b+1 : ℤ)^2 := by exact_mod_cast h
  linarith

private theorem outside_card (s : Pair) : Fintype.card (Outside s) = 5 := by
  have h := Fintype.card_congr (Equiv.sumCompl (fun i : Fin 7 => i ∈ s.val))
  rw [Fintype.card_sum,Fintype.card_fin] at h
  change Fintype.card ↥s.val + Fintype.card (Outside s) = 7 at h
  rw [Fintype.card_coe,s.property] at h
  omega

private theorem class_card (n : ℕ) (s : Pair) (b : Fin (n+1)) [Fintype (Class n s b)] :
    (Fintype.card (Class n s b) : ℤ) = (2*(b.val : ℤ)+1)*((n : ℤ)-b.val)^5 := by
  rw [Fintype.card_congr (unpack s b), Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,outside_card]
  push_cast [Nat.cast_sub (Nat.le_of_lt_succ b.isLt)]
  rw [low_card]
  ring

private theorem pair_card : Fintype.card Pair = 21 := by decide +kernel

private theorem count (n : ℕ) :
    a n = 21 * ∑ b ∈ range (n+1), (2*(b : ℤ)+1)*((n : ℤ)-b)^5 := by
  classical
  have h := Fintype.card_congr (Equiv.ofBijective forget (forget_bij n))
  rw [Fintype.card_subtype] at h
  have h' : a n = ∑ s : Pair, ∑ b : Fin (n+1), (Fintype.card (Class n s b) : ℤ) := by
    unfold a
    rw [← h,Fintype.card_sigma]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Fintype.card_sigma,Nat.cast_sum]
  rw [h']
  simp_rw [class_card]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Finset.sum_const,Finset.card_univ,pair_card,nsmul_eq_mul]
  rfl

private def Q (x t : ℚ) : ℚ :=
    (x^5)*t/1 +
    (- 3 + 15*x - 30*x^2 + 30*x^3 - 15*x^4 + 2*x^5)*t*(t-1)/2 +
    (- 154 + 370*x - 340*x^2 + 140*x^3 - 20*x^4)*t*(t-1)*(t-2)/6 +
    (- 1230 + 1680*x - 780*x^2 + 120*x^3)*t*(t-1)*(t-2)*(t-3)/24 +
    (- 3360 + 2520*x - 480*x^2)*t*(t-1)*(t-2)*(t-3)*(t-4)/120 +
    (- 3720 + 1200*x)*t*(t-1)*(t-2)*(t-3)*(t-4)*(t-5)/720 +
    (- 1440)*t*(t-1)*(t-2)*(t-3)*(t-4)*(t-5)*(t-6)/5040

private theorem sum_eval (x : ℚ) (t : ℕ) :
    (∑ j ∈ range t, (2*(j : ℚ)+1)*(x-j)^5) = Q x t := by
  induction t with
  | zero => simp [Q]
  | succ t ih => rw [sum_range_succ,ih]; push_cast; unfold Q; ring

private def P (x : ℚ) : ℚ := 21*Q x (x+1)

private theorem value (n : ℕ) : (a n : ℚ) = P n := by
  have h := congrArg (fun k : ℤ => (k : ℚ)) (count n)
  push_cast at h
  simpa [P, sum_eval] using h

private theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+9 := ⟨n-9,by omega⟩
  simp only [show m+9-1 = m+8 by omega,show m+9-2 = m+7 by omega,show m+9-3 = m+6 by omega,show m+9-4 = m+5 by omega,show m+9-5 = m+4 by omega,show m+9-6 = m+3 by omega,show m+9-7 = m+2 by omega,show m+9-8 = m+1 by omega,value,P,Q]
  push_cast
  ring

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = 21 * X * (1 + X) * (1 + 26 * X + 66 * X ^ 2 + 26 * X ^ 3 + X ^ 4) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^8 = S - (8:ℕ) • (S*X^1) + (28:ℕ) • (S*X^2) - (56:ℕ) • (S*X^3) + (70:ℕ) • (S*X^4) - (56:ℕ) • (S*X^5) + (28:ℕ) • (S*X^6) - (8:ℕ) • (S*X^7) + (S*X^8) := by simp only [nsmul_eq_mul]; ring
  have rhs : (21 * X * (1 + X) * (1 + 26 * X + 66 * X ^ 2 + 26 * X ^ 3 + X ^ 4) : PowerSeries ℚ) = (21:ℕ) • X^1 + (567:ℕ) • X^2 + (1932:ℕ) • X^3 + (1932:ℕ) • X^4 + (567:ℕ) • X^5 + (21:ℕ) • X^6 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 9 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [value,P,Q]

theorem result : type_of% @OMA.S_oeis_a250060.main := ⟨generating,recurrence⟩

end OMA.Gaps250060

theorem OMA.solution : type_of% @OMA.S_oeis_a250060.main := OMA.Gaps250060.result
