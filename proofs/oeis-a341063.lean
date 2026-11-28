import OMAStatements.S_oeis_a341063

/-!
# Triangular product sum of the totatives of a semiprime

Reversing the ordered totatives of N sends each x to N-x. This turns
the triangular sum into a combination of the first two moments and a
sum of absolute differences. For the cyclic difference d = x-y mod N,
N |x-y| = (x-y)^2 + d(N-d). The Chinese remainder theorem counts
the pairs with a given d independently at the two primes.

Conjecture of J. M. Bergot and Robert Israel: https://oeis.org/A341063
-/

open Finset OMA.S_oeis_a341063

namespace Tot341

private theorem tot_mem {N x : ℕ} (hN : 2 ≤ N) :
    x ∈ totatives N ↔ x < N ∧ x.Coprime N := by
  simp only [totatives, List.mem_filter, decide_eq_true_eq, List.mem_range', one_mul]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hc⟩
    have hn : 1+i ≠ N := fun he => by
      rw [he, Nat.coprime_self] at hc
      omega
    exact ⟨by omega, hc⟩
  · rintro ⟨hx, hc⟩
    have hp : 0 < x := by
      by_contra! h
      have hx0 : x = 0 := by omega
      rw [hx0, Nat.coprime_zero_left] at hc
      omega
    exact ⟨⟨x-1, by omega, by omega⟩, hc⟩

private theorem tot_sorted (N : ℕ) : (totatives N).Pairwise (· < ·) :=
  List.Pairwise.filter _ (List.pairwise_lt_range' 1 (by decide))

private theorem tot_reflect_mem {N x : ℕ} (hN : 2 ≤ N) (hx : x ∈ totatives N) :
    N-x ∈ totatives N := by
  obtain ⟨hu, hc⟩ := (tot_mem hN).1 hx
  have hn : x ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hc
    omega
  exact (tot_mem hN).2 ⟨by omega,(Nat.coprime_self_sub_left hu.le).2 hc⟩

private theorem tot_rev_list (N : ℕ) (hN : 2 ≤ N) :
    ((totatives N).reverse.map (N - ·)) = totatives N := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) _ (tot_sorted N)
  · intro x
    simp only [List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact tot_reflect_mem hN hy
    · intro hx
      have hu := ((tot_mem hN).1 hx).1
      exact ⟨N-x,tot_reflect_mem hN hx,by omega⟩
  · rw [List.pairwise_map, List.pairwise_reverse]
    refine (tot_sorted N).imp_of_mem fun {x y} hx hy hxy => ?_
    have := ((tot_mem hN).1 hy).1
    omega

theorem tot_rev_get (N : ℕ) (hN : 2 ≤ N) (i : Fin (totatives N).length) :
    (totatives N).get i.rev = N - (totatives N).get i := by
  let l := totatives N
  have H : l.reverse.map (N - ·) = l := tot_rev_list N hN
  have hi : i.rev.val < (l.reverse.map (N - ·)).length := by simpa [l] using i.rev.isLt
  change l[i.rev.val] = N - l[i.val]
  calc
    _ = (l.reverse.map (N - ·))[i.rev.val]'hi := by simp [H]
    _ = N - l[i.val] := by
      simp only [List.getElem_map,List.getElem_reverse,Fin.val_rev]
      congr 2
      have := i.isLt
      dsimp only [l] at *
      omega

private theorem tot_sum (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℤ) :
    (∑ i : Fin (totatives N).length, f ((totatives N).get i)) =
      ∑ x ∈ (range N).filter (fun x => x.Coprime N), f x := by
  refine sum_bij (fun i _ => (totatives N).get i) ?_ ?_ ?_ (by intros; rfl)
  · intro i _
    simpa only [mem_filter, mem_range] using (tot_mem hN).1 ((totatives N).get_mem i)
  · intro i _ j _ h
    exact (tot_sorted N).sortedLT.strictMono_get.injective h
  · intro y hy
    obtain ⟨i,hi⟩ := List.mem_iff_get.1 ((tot_mem hN).2 (by simpa using hy))
    exact ⟨i,mem_univ _,hi⟩

theorem triangle_ordered (N : ℕ) (hN : 2 ≤ N) :
    let U := (range N).filter (fun x => x.Coprime N)
    (a N : ℤ) = ∑ x ∈ U, ∑ y ∈ U, if x ≤ y then (x : ℤ) * ((N : ℤ) - y) else 0 := by
  dsimp only
  let l := totatives N
  have hm : StrictMono l.get := (tot_sorted N).sortedLT.strictMono_get
  have hf (i : Fin l.length) :
      (∑ j : Fin l.length, if i.val+j.val<l.length then (l.get i : ℤ) * (l.get j : ℤ) else 0)
        = ∑ y ∈ (range N).filter (fun x => x.Coprime N),
          if l.get i ≤ y then (l.get i : ℤ) * ((N : ℤ)-y) else 0 := by
    rw [← Equiv.sum_comp Fin.revPerm (fun j : Fin l.length =>
      if i.val+j.val<l.length then (l.get i : ℤ) * (l.get j : ℤ) else 0)]
    rw [← tot_sum N hN (fun y => if l.get i ≤ y then (l.get i : ℤ) * ((N : ℤ)-y) else 0)]
    refine sum_congr rfl fun j _ => ?_
    have hr : l.get j.rev = N-l.get j := tot_rev_get N hN j
    have hj := ((tot_mem hN).1 (l.get_mem j)).1.le
    have hcond : i.val+j.rev.val<l.length ↔ l.get i ≤ l.get j := by
      rw [Fin.val_rev, hm.le_iff_le]
      have hi := i.isLt
      have hj' := j.isLt
      change _ ↔ i.val ≤ j.val
      omega
    simp only [Fin.revPerm_apply, hcond, hr, Nat.cast_sub hj]
    rfl
  change ((∑ i : Fin l.length, ∑ j : Fin l.length,
    if i.val+j.val<l.length then l.get i * l.get j else 0 : ℕ) : ℤ) = _
  push_cast
  simp_rw [hf]
  exact tot_sum N hN (fun x => ∑ y ∈ (range N).filter (fun z => z.Coprime N),
    if x ≤ y then (x : ℤ)*((N : ℤ)-y) else 0)


private theorem triangle_algebra (s : Finset ℕ) (N : ℕ) :
    2 * (∑ x ∈ s, ∑ y ∈ s, if x ≤ y then (x : ℤ) * ((N : ℤ)-y) else 0) =
      (∑ x ∈ s, ∑ y ∈ s, (x : ℤ) * ((N : ℤ)-y)) +
      (∑ x ∈ s, (x : ℤ) * ((N : ℤ)-x)) -
      (N : ℤ) * ∑ x ∈ s, ∑ y ∈ s, if x < y then (y : ℤ)-x else 0 := by
  let w (x y : ℕ) : ℤ := (x : ℤ)*((N : ℤ)-y)
  let u (x y : ℕ) : ℤ := if x < y then w y x else 0
  have point (x y : ℕ) :
      2 * (if x ≤ y then w x y else 0) =
      w x y + u x y - u y x + (if x=y then w x x else 0) -
        (N : ℤ)*(if x < y then (y : ℤ)-x else 0) := by
    rcases lt_trichotomy x y with h | rfl | h
    · simp [u,w,h,h.le,h.ne,h.not_gt]
      ring
    · simp [u,w]; ring
    · simp [u,w,h,h.not_ge,h.ne',h.not_gt]
  have hsum := Finset.sum_congr (s₁ := s) rfl
    (fun x _ => Finset.sum_congr (s₁ := s) rfl (fun y _ => point x y))
  have hdiag : (∑ x ∈ s, ∑ y ∈ s, if x=y then w x x else 0) =
      ∑ x ∈ s, w x x := by
    apply sum_congr rfl
    intro x hx
    simp [hx]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hdiag, Finset.sum_comm (f := fun x y => u y x)] at hsum
  simpa only [add_sub_cancel_right, w] using hsum

theorem triangle_identity (N : ℕ) (hN : 2 ≤ N) :
    let U := (range N).filter (fun x => x.Coprime N)
    2 * (a N : ℤ) = (∑ x ∈ U, (x : ℤ))^2 +
      (∑ x ∈ U, (x : ℤ) * ((N : ℤ)-x)) -
      (N : ℤ) * (∑ x ∈ U, ∑ y ∈ U, if x < y then (y : ℤ)-x else 0) := by
  dsimp only
  let U := (range N).filter (fun x => x.Coprime N)
  have hs : (∑ x ∈ U, ((N : ℤ)-x)) = ∑ x ∈ U, (x : ℤ) := by
    change (∑ x ∈ (range N).filter (fun x => x.Coprime N), ((N : ℤ)-x)) =
      ∑ x ∈ (range N).filter (fun x => x.Coprime N), (x : ℤ)
    rw [← tot_sum N hN (fun x => (N : ℤ)-x), ← tot_sum N hN (fun x => (x : ℤ))]
    calc
      _ = ∑ i : Fin (totatives N).length, ((totatives N).get i.rev : ℤ) := by
        refine sum_congr rfl fun i _ => ?_
        have hx := ((tot_mem hN).1 ((totatives N).get_mem i)).1.le
        rw [tot_rev_get N hN, Nat.cast_sub hx]
      _ = _ := Equiv.sum_comp Fin.revPerm (fun i : Fin (totatives N).length => ((totatives N).get i : ℤ))
  have ht : (∑ x ∈ U, ∑ y ∈ U, (x : ℤ)*((N : ℤ)-y)) = (∑ x ∈ U, (x : ℤ))^2 := by
    simp_rw [← mul_sum,hs]
    rw [← sum_mul, pow_two]
  change 2 * (a N : ℤ) = (∑ x ∈ U, (x : ℤ))^2 + _ - _
  rw [triangle_ordered N hN]
  exact (triangle_algebra U N).trans (by rw [ht])

end Tot341

namespace Tot341
open Finset

theorem unit_card {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ((range (p*q)).filter (fun a => a.Coprime (p*q))).card = (p-1)*(q-1) := by
  simpa only [Nat.totient_eq_card_coprime,@Nat.coprime_comm (p*q)] using
    ((Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hne)).trans
      (congrArg₂ (·*·) (Nat.totient_prime hp) (Nat.totient_prime hq)))

theorem range_moments (N : ℕ) :
    2*(∑ i ∈ range N, (i:ℤ)) = (N:ℤ)*(N-1) ∧
    6*(∑ i ∈ range N, (i:ℤ)^2) = (N:ℤ)*(N-1)*(2*N-1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [sum_range_succ,Nat.cast_succ]
    constructor
    · linear_combination ih.1
    · linear_combination ih.2

theorem multiples_sum (p q : ℕ) (hp : 0<p) (f : ℕ → ℤ) :
    (∑ d ∈ (range (p*q)).filter (p ∣ ·), f d) = ∑ i ∈ range q, f (p*i) := by
  have eq : (range (p*q)).filter (p ∣ ·) = (range q).image (p*·) := by
    ext d
    constructor
    · intro h
      obtain ⟨hd,⟨i,rfl⟩⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨i,mem_range.mpr ((Nat.mul_lt_mul_left hp).mp (mem_range.mp hd)),rfl⟩
    · intro h
      obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨mem_range.mpr ((Nat.mul_lt_mul_left hp).mpr (mem_range.mp hi)),dvd_mul_right _ _⟩
  rw [eq,sum_image]
  exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp h

theorem common_multiple_zero {p q d : ℕ} (hc : p.Coprime q) (h : d<p*q)
    (ha : p∣d) (hb : q∣d) : d=0 := by
  by_contra hz
  exact h.not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) (hc.mul_dvd_of_dvd_of_dvd ha hb))

theorem unit_sum_partition {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (f : ℕ → ℤ) (h0 : f 0=0) :
    (∑ a ∈ (range (p*q)).filter (fun a => a.Coprime (p*q)), f a) +
      (∑ i ∈ range q, f (p*i)) + (∑ i ∈ range p, f (q*i)) =
      ∑ d ∈ range (p*q), f d := by
  rw [← multiples_sum p q hp.pos f, ← multiples_sum q p hq.pos f,Nat.mul_comm q p]
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hc : d.Coprime (p*q) ↔ ¬p∣d ∧ ¬q∣d := by
    rw [Nat.coprime_comm, Nat.coprime_mul_iff_left, hp.coprime_iff_not_dvd,hq.coprime_iff_not_dvd]
  by_cases ha : p∣d <;> by_cases hb : q∣d
  · have hz := common_multiple_zero ((Nat.coprime_primes hp hq).mpr hne) (mem_range.mp hd) ha hb
    simp [hz,h0]
  all_goals simp [hc,ha,hb]

theorem unit_sum_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    2*(∑ a ∈ (range (p*q)).filter (fun a => a.Coprime (p*q)), (a:ℤ)) =
      (p:ℤ)*q*(p-1)*(q-1) := by
  have hu := unit_sum_partition hp hq hne (fun i => (i:ℤ)) rfl
  simp only [Nat.cast_mul, ← mul_sum] at hu
  have hN := (range_moments (p*q)).1
  push_cast at hN
  linear_combination 2*hu + hN - (p:ℤ)*(range_moments q).1 - (q:ℤ)*(range_moments p).1

theorem unit_sum_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    6*(∑ a ∈ (range (p*q)).filter (fun a => a.Coprime (p*q)), (a:ℤ)^2) =
      (p:ℤ)*q*(p-1)*(q-1)*(2*p*q+1) := by
  have hu := unit_sum_partition hp hq hne (fun i => (i:ℤ)^2) (by simp)
  simp only [Nat.cast_mul, mul_pow, ← mul_sum] at hu
  have hN := (range_moments (p*q)).2
  push_cast at hN
  linear_combination 6*hu + hN - (p:ℤ)^2*(range_moments q).2 - (q:ℤ)^2*(range_moments p).2

theorem interval_weight_sum (n : ℕ) :
    6*(∑ d ∈ range n,(d:ℤ)*(n-d)) = (n:ℤ)*(n^2-1) := by
  have h := range_moments n
  simp only [mul_sub,← sq,sum_sub_distrib,← sum_mul]
  linear_combination 3*(n:ℤ)*h.1 - h.2

theorem weighted_difference_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    6*(∑ d ∈ range (p*q), (d:ℤ)*((p:ℤ)*q-d)*
      ((p:ℤ)-2 + if p∣d then 1 else 0)*((q:ℤ)-2 + if q∣d then 1 else 0)) =
    ((p:ℤ)-2)*(q-2)*(p*q)*((p*q)^2-1) +
      (q-2)*p^2*q*(q^2-1) + (p-2)*q^2*p*(p^2-1) := by
  let w (d : ℕ) : ℤ := d*((p:ℤ)*q-d)
  let I := range (p*q)
  have he : (∑ d ∈ I, w d * ((p:ℤ)-2 + if p∣d then 1 else 0) *
      ((q:ℤ)-2 + if q∣d then 1 else 0)) =
      ((p:ℤ)-2)*(q-2)*(∑ d ∈ I,w d)+(q-2)*(∑ d ∈ I.filter (p∣·),w d)+
      (p-2)*(∑ d ∈ I.filter (q∣·),w d) := by
    simp only [sum_filter,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    by_cases ha : p∣d <;> by_cases hb : q∣d
    · have hz := common_multiple_zero ((Nat.coprime_primes hp hq).mpr hne) (mem_range.mp hd) ha hb
      simp [hz,w]
    all_goals
      simp [ha,hb]
      ring
  have hpW : (∑ d ∈ I.filter (p∣·),w d) =
      (p:ℤ)^2*∑ i ∈ range q,(i:ℤ)*(q-i) := by
    rw [mul_sum,multiples_sum p q hp.pos]
    apply sum_congr rfl
    intro i _
    simp only [w,Nat.cast_mul]
    ring
  have hqW : (∑ d ∈ I.filter (q∣·),w d) =
      (q:ℤ)^2*∑ i ∈ range p,(i:ℤ)*(p-i) := by
    dsimp only [I]
    rw [Nat.mul_comm p q,mul_sum,multiples_sum q p hq.pos]
    apply sum_congr rfl
    intro i _
    simp only [w,Nat.cast_mul]
    ring
  have hN := interval_weight_sum (p*q)
  push_cast at hN
  change 6*(∑ d ∈ I, w d*_*_) = _
  rw [he,hpW,hqW]
  dsimp only [I,w]
  linear_combination ((p:ℤ)-2)*(q-2)*hN + ((q:ℤ)-2)*p^2*(interval_weight_sum q) +
    ((p:ℤ)-2)*q^2*(interval_weight_sum p)

end Tot341

namespace Tot341
open Finset

/-- Parametrize the ordered pairs in each difference fiber by their first
coordinate in the residue ring. -/
theorem difference_fiber_ring (N d : ℕ) [NeZero N] (hd : d<N) :
    let U := (range N).filter (fun a => Nat.Coprime a N)
    ((U×ˢU).filter (fun z => (z.1+N-z.2)%N=d)).card =
      ((univ : Finset (ZMod N)).filter (fun x => IsUnit x ∧ IsUnit (x-(d:ZMod N)))).card := by
  classical
  intro U
  have rep (a b : ℕ) (ha : a<N) (hb : b<N) (e : (a:ZMod N)=(b:ZMod N)) : a=b := by
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using congrArg ZMod.val e
  have diff (x y : ℕ) (hy : y<N) :
      (x+N-y)%N=d ↔ (y:ZMod N)=(x:ZMod N)-(d:ZMod N) := by
    have castdiff : (((x+N-y)%N:ℕ):ZMod N)=(x:ZMod N)-(y:ZMod N) := by
      rw [ZMod.natCast_mod,Nat.cast_sub (by omega),Nat.cast_add,ZMod.natCast_self,add_zero]
    constructor
    · intro h
      rw [h] at castdiff
      rw [castdiff]
      abel
    · intro h
      apply rep _ _ (Nat.mod_lt _ (NeZero.pos N)) hd
      rw [castdiff,h]
      abel
  have mem (z : ℕ×ℕ) :
      z∈(U×ˢU).filter (fun z => (z.1+N-z.2)%N=d) ↔
      z.1<N ∧ z.2<N ∧ IsUnit (z.1 : ZMod N) ∧ IsUnit (z.2 : ZMod N) ∧
      (z.2 : ZMod N)=(z.1 : ZMod N)-(d:ZMod N) := by
    simp only [U,mem_filter,mem_product,mem_range,←ZMod.isUnit_iff_coprime]
    constructor
    · rintro ⟨⟨⟨hx,hu⟩,hy,hv⟩,h⟩
      exact ⟨hx,hy,hu,hv,(diff _ _ hy).mp h⟩
    · rintro ⟨hx,hy,hu,hv,h⟩
      exact ⟨⟨⟨hx,hu⟩,hy,hv⟩,(diff _ _ hy).mpr h⟩
  apply card_bij (fun z _ => (z.1:ZMod N))
  · intro z hz
    obtain ⟨_,_,hu,hv,he⟩ := (mem z).mp hz
    exact mem_filter.mpr ⟨mem_univ _,hu,he ▸ hv⟩
  · intro z hz w hw he
    obtain ⟨hx,hy,_,_,heq⟩ := (mem z).mp hz
    obtain ⟨hx',hy',_,_,heq'⟩ := (mem w).mp hw
    apply Prod.ext (rep _ _ hx hx' he)
    exact rep _ _ hy hy' (by rw [heq,heq',he])
  · intro z hz
    obtain ⟨_,hu,hv⟩ := mem_filter.mp hz
    refine ⟨(z.val,(z-d).val),(mem _).mpr ?_,ZMod.natCast_zmod_val z⟩
    exact ⟨z.val_lt,(z-d).val_lt,by simpa using hu,by simpa using hv,by simp⟩

theorem difference_multiplicity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (d : ℕ) (hd : d<p*q) :
    let N := p*q
    let U := (range N).filter (fun a => Nat.Coprime a N)
    ((U×ˢU).filter (fun z => (z.1+N-z.2)%N=d)).card =
      (p-2 + if p∣d then 1 else 0)*(q-2 + if q∣d then 1 else 0) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let N := p*q
  intro _ U
  rw [difference_fiber_ring _ _ hd]
  let C := ZMod.chineseRemainder (hp.coprime_iff_not_dvd.mpr (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)))
  let P := (univ.erase (0:ZMod p)).erase (d:ZMod p)
  let Q := (univ.erase (0:ZMod q)).erase (d:ZMod q)
  have whole (x : ZMod (p*q)) : IsUnit x ↔ IsUnit (C x) :=
    ⟨fun h => h.map C,fun h => by simpa using h.map C.symm⟩
  have fiber : ((univ : Finset (ZMod (p*q))).filter (fun x => IsUnit x ∧ IsUnit (x-(d:ZMod (p*q))))).card =
      (P×ˢQ).card := by
    apply card_bijective C C.bijective
    intro z
    simp only [mem_filter,mem_univ,true_and,mem_product,P,Q,mem_erase,whole,
      Prod.isUnit_iff,isUnit_iff_ne_zero,map_sub,map_natCast,Prod.fst_sub,Prod.snd_sub,
      Prod.fst_natCast,Prod.snd_natCast,sub_ne_zero]
    tauto
  have local_card (r : ℕ) (hr : r.Prime) [NeZero r] :
      ((univ.erase (0:ZMod r)).erase (d:ZMod r)).card =
        r-2 + if r∣d then 1 else 0 := by
    have h0 : (univ.erase (0:ZMod r)).card = r-1 := by simp [card_erase_of_mem,ZMod.card]
    by_cases h : r∣d
    · have hd0 := (ZMod.natCast_eq_zero_iff d r).mpr h
      rw [hd0,erase_idem,h0,if_pos h]
      have := hr.two_le
      omega
    · have hd0 := mt (ZMod.natCast_eq_zero_iff d r).mp h
      rw [card_erase_of_mem (by simp [hd0]),h0,if_neg h]
      omega
  rw [fiber,card_product,local_card p hp,local_card q hq]

/-- Sum a weight over all ordered differences by first fixing its residue. -/
theorem weighted_differences {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (f : ℕ → ℤ) :
    let N := p*q
    let U := (range N).filter (fun a => Nat.Coprime a N)
    (∑ x ∈ U, ∑ y ∈ U, f ((x+N-y)%N)) =
      ∑ d ∈ range N, (((p-2 + if p∣d then 1 else 0)*
        (q-2 + if q∣d then 1 else 0) : ℕ):ℤ)*f d := by
  intro N U
  let diff (z : ℕ×ℕ) := (z.1+N-z.2)%N
  have hbound : ∀ z ∈ U×ˢU, diff z ∈ range N := fun z _ =>
    mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hp.pos hq.pos))
  calc
    _ = ∑ z ∈ U×ˢU, f (diff z) := (sum_product ..).symm
    _ = ∑ d ∈ range N, ∑ z ∈ (U×ˢU).filter (fun z => diff z=d), f d :=
        (sum_fiberwise_of_maps_to' hbound f).symm
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [sum_const,nsmul_eq_mul]
      exact congrArg (fun k : ℕ => (k:ℤ)*f d)
        (difference_multiplicity hp hq hne d (mem_range.mp hd))

end Tot341

namespace Tot341
open Finset

/-- The oriented modular distance determines the absolute difference once
its square is known. All coordinates are represented in [0,N). -/
theorem cyclic_distance {N x y : ℕ} (hx : x<N) (hy : y<N) :
    let d := (x+N-y)%N
    (N:ℤ) * |(x:ℤ)-y| = ((x:ℤ)-y)^2 + (d:ℤ)*((N:ℤ)-d) := by
  intro d
  by_cases h : y ≤ x
  · have hd : d=x-y := by
      dsimp [d]
      rw [show x+N-y = (x-y)+N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hd,Nat.cast_sub h,abs_of_nonneg (by omega)]
    ring
  · have hxy : x ≤ y := by omega
    have hd : d=N-(y-x) := by
      dsimp [d]
      rw [show x+N-y=N-(y-x) by omega, Nat.mod_eq_of_lt (by omega)]
    rw [hd,Nat.cast_sub (by omega),Nat.cast_sub hxy,abs_of_nonpos (by omega)]
    ring

/-- General identity for the moments of a reflection-symmetric triangle.
The remaining cyclic term can be evaluated by the difference correlations. -/
theorem triangle_moments {N : ℕ} (U : Finset ℕ) (hU : U ⊆ range N) (A : ℤ)
    (tri : 2*A = (∑ x ∈ U,(x:ℤ))^2 + (∑ x ∈ U,(x:ℤ)*((N:ℤ)-x)) -
      (N:ℤ)*(∑ x ∈ U,∑ y ∈ U,if x<y then (y:ℤ)-x else 0)) :
    4*A = 4*(∑ x ∈ U,(x:ℤ))^2 + 2*(N:ℤ)*(∑ x ∈ U,(x:ℤ)) -
      2*(1+(U.card:ℤ))*(∑ x ∈ U,(x:ℤ)^2) -
      ∑ x ∈ U,∑ y ∈ U, (((x+N-y)%N:ℕ):ℤ)*((N:ℤ)-((x+N-y)%N:ℕ)) := by
  let F (x y : ℕ) : ℤ := if x<y then (y:ℤ)-x else 0
  have point (x y : ℕ) : F x y + F y x = |(x:ℤ)-y| := by
    by_cases h : x<y
    · have ny : ¬y<x := by omega
      have nz : (x:ℤ) - y ≤ 0 := by omega
      simp only [F,if_pos h,if_neg ny,add_zero,abs_of_nonpos nz]
      ring
    · have nz : 0 ≤ (x:ℤ)-y := by omega
      by_cases he : y<x
      · simp [F,h,he,abs_of_nonneg nz]
      · have := Nat.le_antisymm (by omega : x≤y) (by omega : y≤x)
        subst y
        simp [F]
  have twice :
      2*(∑ x ∈ U,∑ y ∈ U,F x y) = ∑ x ∈ U,∑ y ∈ U, |(x:ℤ)-y| := by
    simp_rw [←point, sum_add_distrib]
    rw [sum_comm (f:=fun x y => F y x)]
    ring
  have sq :
      (∑ x ∈ U,∑ y ∈ U, ((x:ℤ)-y)^2) =
      2*(U.card:ℤ)*(∑ x ∈ U,(x:ℤ)^2)-2*(∑ x ∈ U,(x:ℤ))^2 := by
    simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, ←mul_sum, sum_const, nsmul_eq_mul,
      ←sum_mul, ←mul_sum]
    ring
  have rad :
      (N:ℤ) * (∑ x ∈ U,∑ y ∈ U, |(x:ℤ)-y|) = (∑ x ∈ U,∑ y ∈ U, ((x:ℤ)-y)^2) +
      ∑ x ∈ U,∑ y ∈ U, (((x+N-y)%N:ℕ):ℤ)*((N:ℤ)-((x+N-y)%N:ℕ)) := by
    simp_rw [mul_sum, ←sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    exact cyclic_distance (mem_range.mp (hU hx)) (mem_range.mp (hU hy))
  have diag : (∑ x ∈ U,(x:ℤ)*((N:ℤ)-x)) = (N:ℤ)*(∑ x ∈ U,(x:ℤ)) - ∑ x ∈ U,(x:ℤ)^2 := by
    simp_rw [mul_sub, sum_sub_distrib, ←sum_mul, ←pow_two]
    ring
  change 2*A = _ + _ - (N:ℤ)*(∑ x ∈ U,∑ y ∈ U,F x y) at tri
  rw [←twice,sq] at rad
  rw [diag] at tri
  linarith only [tri,rad]

end Tot341

open Finset Tot341

theorem OMA.solution : type_of% @OMA.S_oeis_a341063.main := by
  intro p q hp hq hne
  let N := p*q
  let U := (range N).filter (fun x => x.Coprime N)
  let w (d : ℕ) : ℤ := (d:ℤ)*((N:ℤ)-d)
  let W := ∑ x ∈ U, ∑ y ∈ U, w ((x+N-y)%N)
  have hN : 2 ≤ N := by dsimp [N]; nlinarith [hp.two_le, hq.two_le]
  have ht := triangle_moments U (filter_subset _ _) _ (triangle_identity N hN)
  change 4*(OMA.S_oeis_a341063.a N:ℤ) = _ + _ - _ - W at ht
  have hc : (U.card:ℤ) = ((p:ℤ)-1)*(q-1) := by
    dsimp only [U,N]
    rw [unit_card hp hq hne,Nat.cast_mul,Nat.cast_sub hp.pos,Nat.cast_sub hq.pos,Nat.cast_one]
  have hsum : W = ∑ d ∈ range (p*q), (d:ℤ)*((p:ℤ)*q-d)*
      ((p:ℤ)-2 + if p∣d then 1 else 0)*((q:ℤ)-2 + if q∣d then 1 else 0) := by
    change (∑ x ∈ U,∑ y ∈ U,w ((x+N-y)%N)) = _
    rw [show (∑ x ∈ U,∑ y ∈ U,w ((x+N-y)%N)) = _ from weighted_differences hp hq hne w]
    apply sum_congr rfl
    intro d _
    dsimp only [w,N]
    split_ifs <;> push_cast [Nat.cast_sub hp.two_le, Nat.cast_sub hq.two_le] <;> ring
  rw [hc] at ht
  dsimp only [U,N] at ht
  simp only [Nat.cast_mul] at ht
  have hw := weighted_difference_sum hp hq hne
  rw [←hsum] at hw
  have h1 := unit_sum_one hp hq hne
  have h2 := unit_sum_two hp hq hne
  have h1sq := congrArg (fun z:ℤ => z^2) h1
  linear_combination 6*ht + 6*h1sq + (6*(p:ℤ)*q)*h1 - 2*(1+((p:ℤ)-1)*(q-1))*h2 - hw
