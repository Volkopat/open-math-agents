import OMAStatements.S_mo_315485
import Mathlib

/-!
Dividing a chain by its first part gives the divisor recursion. For eventual
existence, odd totals are obtained by adjoining one to a doubled partition.
A sufficiently large power of two dividing the total instead supplies a
scaled copy of the chain with parts one, three, twelve, and so on. Scaling
partitions of distinct odd totals to a common multiple gives distinct first
parts. The least sum forces equality at every doubling between neighbors.
-/

namespace OMA.P_mo_315485
open OMA.S_mo_315485

private def bound (d : ℕ) (l : List ℕ) := ∀ a ∈ l, d ≤ a

private lemma sum_scale (d : ℕ) (l : List ℕ) : (l.map (d * ·)).sum = d*l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add]
private lemma scale {d n k : ℕ} {l : List ℕ} (hd : 0<d) (h : IsPartition n k l) :
    IsPartition (d*n) k (l.map (d*·)) := by
  obtain ⟨hs,hl,hp,hrel⟩:=h
  refine ⟨by rw [sum_scale,hs],by simpa using hl,?_,?_⟩
  · intro x hx; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx; exact Nat.mul_pos hd (hp _ hb)
  · rw [List.pairwise_map]
    exact hrel.imp (fun hh => ⟨Nat.mul_lt_mul_of_pos_left hh.1 hd, Nat.mul_dvd_mul_left d hh.2⟩)

private lemma prepend {n k d : ℕ} {l : List ℕ} (hd : 0<d) (h : IsPartition n k l)
    (hb : bound 2 l) : IsPartition (d*(n+1)) (k+1) (d :: l.map (d*·)) := by
  have hs:=scale hd h
  refine ⟨by simp only [List.sum_cons,hs.1]; ring,by simp [h.2.1],?_,?_⟩
  · intro x hx; rcases List.mem_cons.mp hx with rfl|hx
    · exact hd
    · exact hs.2.2.1 _ hx
  · apply List.pairwise_cons.mpr
    refine ⟨?_,hs.2.2.2⟩
    intro x hx; obtain ⟨b,hb',rfl⟩:=List.mem_map.mp hx
    have h2:=hb b hb'
    exact ⟨by simpa using Nat.mul_lt_mul_of_pos_left (show 1<b by omega) hd, dvd_mul_right _ _⟩

private lemma divide {n k d : ℕ} {l : List ℕ} (h : IsPartition n (k+1) (d::l)) :
    ∃ u : List ℕ, d ∣ n ∧ l=u.map (d*·) ∧ IsPartition (n/d-1) k u ∧ bound 2 u := by
  have hd := h.2.2.1 d (by simp)
  have rel := (List.pairwise_cons.mp h.2.2.2).1
  let u := l.map (·/d)
  have reconstruct : u.map (d*·)=l := by
    dsimp [u]; rw [List.map_map,List.map_congr_left (g:=id) (fun b hb => ?_),List.map_id]
    exact Nat.mul_div_cancel' (rel b hb).2
  have sumEq : d*(u.sum+1)=n := by
    rw [Nat.mul_add,Nat.mul_one,←sum_scale,reconstruct,Nat.add_comm]; exact h.1
  have hn : u.sum+1 = n/d := by rw [←sumEq,Nat.mul_div_cancel_left _ hd]
  have hb : bound 2 u := by
    intro b hb; obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hb
    have hgt := (rel v hv).1
    have he := Nat.mul_div_cancel' (rel v hv).2
    by_contra! hh
    have hh' := Nat.mul_le_mul_left d (show v/d≤1 by omega)
    omega
  refine ⟨u,⟨_,sumEq.symm⟩,reconstruct.symm,⟨by omega,?_,fun x hx => by have := hb x hx; omega,?_⟩,hb⟩
  · have hl:=h.2.1
    simpa [u] using (show l.length=k by simpa using hl)
  · have hh := (List.pairwise_cons.mp h.2.2.2).2
    rw [←reconstruct,List.pairwise_map] at hh
    apply hh.imp
    intro a b hab
    exact ⟨(Nat.mul_lt_mul_left hd).mp hab.1,(Nat.dvd_of_mul_dvd_mul_left hd hab.2)⟩

private lemma membership (lo k n : ℕ) (l : List ℕ) :
    l ∈ partitions lo k n ↔ IsPartition n k l ∧ bound lo l := by
  induction k generalizing lo n l with
  | zero =>
    cases l with
    | nil => by_cases hn : n=0 <;> simp_all [partitions,IsPartition,bound,eq_comm]
    | cons a l => simp [partitions,IsPartition]; split <;> simp
  | succ k ih =>
    constructor
    · intro hm
      rw [partitions,Finset.mem_biUnion] at hm
      obtain ⟨d,hd,him⟩:=hm
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp him
      obtain ⟨hdiv,hlo⟩:=Finset.mem_filter.mp hd
      obtain ⟨hdn,hn⟩:=Nat.mem_divisors.mp hdiv
      have hdpos:= Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn)
      have hq : 0<n/d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) hdpos
      have he : d*(n/d-1+1)=n := by
        rw [show n/d-1+1=n/d by omega,Nat.mul_div_cancel' hdn]
      obtain ⟨hu',hb⟩:=(ih 2 _ _).mp hu
      exact ⟨he ▸ prepend hdpos hu' hb,fun x hx => by
        rcases List.mem_cons.mp hx with rfl|hx
        · exact hlo
        · obtain ⟨b,hb',rfl⟩:=List.mem_map.mp hx
          exact hlo.trans (by simpa using Nat.mul_le_mul_left d (show 1≤b from hu'.2.2.1 b hb'))⟩
    · rintro ⟨h,hlo⟩
      cases l with
      | nil => simp [IsPartition] at h
      | cons d l =>
        obtain ⟨u,hd,he,hu,hb⟩:=divide h
        have hp:=h.2.2.1 d (by simp)
        have hs:=h.1
        have hn : n ≠ 0 := by simp only [List.sum_cons] at hs; omega
        rw [partitions,Finset.mem_biUnion]
        exact ⟨d,Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd,hn⟩,hlo d (by simp)⟩,
          Finset.mem_image.mpr ⟨u,(ih 2 _ _).mpr ⟨hu,hb⟩,by rw [←he]⟩⟩

private lemma cardinal (lo k n : ℕ) : (partitions lo k n).card=count lo k n := by
  induction k generalizing lo n with
  | zero => simp [partitions,count]; split <;> simp
  | succ k ih =>
    rw [partitions,count, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro d hd
      have hp := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
      rw [Finset.card_image_of_injective,ih]
      intro u v he
      have hh: u.map (d*·)=v.map (d*·) := (List.cons.inj he).2
      exact (List.map_injective_iff.mpr (fun a b (hab : d*a=d*b) => Nat.eq_of_mul_eq_mul_left hp hab)) hh
    · intro d hd e he hne
      apply Finset.disjoint_left.mpr
      intro u hu hv
      obtain ⟨s,_,hs⟩:=Finset.mem_image.mp hu
      obtain ⟨t,_,ht⟩:=Finset.mem_image.mp hv
      exact hne (List.cons.inj (hs.trans ht.symm)).1

private lemma odd_part {k t : ℕ} {l : List ℕ} (h : IsPartition t k l) :
    IsPartition (2*t+1) (k+1) (1::l.map (2*·)) := by
  have hh := scale (d:=2) (by decide) h
  have hb : bound 2 (l.map (2*·)) := by
    intro a ha; obtain ⟨v,hv,rfl⟩:=List.mem_map.mp ha
    have := h.2.2.1 v hv; omega
  simpa [Function.comp_def] using prepend (d:=1) (by decide) hh hb

private def fours : ℕ → List ℕ
  | 0 => [1]
  | k+1 => fours k ++ [3*4^k]

private lemma four_spec (k : ℕ) : IsPartition (4^k) (k+1) (fours k) ∧
    ∀ a ∈ fours k, a ≤ 4^k ∧ a ∣ 3*4^k := by
  induction k with
  | zero => simp [fours,IsPartition]
  | succ k ih =>
    have hpos : 0<(4:ℕ)^k := by positivity
    obtain ⟨h,hh⟩:=ih
    constructor
    · refine ⟨by simp [fours,h.1,pow_succ]; omega,by simp [fours,h.2.1],?_,?_⟩
      · intro a ha; simp only [fours,List.mem_append,List.mem_singleton] at ha
        rcases ha with ha|rfl
        · exact h.2.2.1 _ ha
        · omega
      · rw [fours,List.pairwise_append]; refine ⟨h.2.2.2,by simp,?_⟩
        intro a ha y hy; simp only [List.mem_singleton] at hy; subst y
        exact ⟨by have ht:=(hh a ha).1; omega,(hh a ha).2⟩
    · intro a ha; simp only [fours,List.mem_append,List.mem_singleton] at ha
      rw [pow_succ,←Nat.mul_assoc]
      rcases ha with ha|rfl
      · exact ⟨by have ht:=(hh a ha).1; omega,dvd_mul_of_dvd_left (hh a ha).2 _⟩
      · exact ⟨by omega,dvd_mul_right _ _⟩

private lemma cutoff_pos (k : ℕ) : 0<cutoff k := by cases k <;> simp [cutoff]
private lemma large (k : ℕ) : ∀ n, cutoff k ≤ n → ∃ l, IsPartition n (k+1) l := by
  induction k with
  | zero => intro n hn; exact ⟨[n],by simpa [IsPartition] using (show 0<n from hn)⟩
  | succ k ih =>
    intro n hn
    have hnpos := lt_of_lt_of_le (cutoff_pos _) hn
    obtain ⟨s,q,hodd,hfac⟩:=Nat.exists_eq_two_pow_mul_odd hnpos.ne'
    have four : (4:ℕ)^(k+1)=2^(2*(k+1)) := by rw [pow_mul]; rfl
    by_cases h : 2*(k+1) ≤ s
    · have hd : 4^(k+1) ∣ n := by
        rw [four,hfac]; exact dvd_mul_of_dvd_left (pow_dvd_pow 2 h) q
      obtain ⟨t,ht⟩:=hd
      have htpos : 0<t := by
        cases t with
        | zero => simp [ht] at hnpos
        | succ t => omega
      obtain ⟨hs,_⟩:=four_spec (k+1)
      refine ⟨(fours (k+1)).map (t*·),?_⟩
      simpa only [ht,Nat.mul_comm (4^(k+1)) t] using scale htpos hs
    · have hd : 2^s ≤ 2^(2*(k+1)) := Nat.pow_le_pow_right (by decide) (by omega)
      have hq : 2*cutoff k+1 ≤ q := by
        rw [cutoff,hfac] at hn
        by_contra! hlt
        have hstrict:=Nat.mul_lt_mul_of_pos_left hlt (by positivity : 0 < 2^s)
        exact (not_lt_of_ge hn) (hstrict.trans_le (Nat.mul_le_mul_right _ hd))
      obtain ⟨t,ht⟩:=hodd
      have ht' : cutoff k ≤ t := by omega
      obtain ⟨l,hl⟩:=ih t ht'
      have he : n=2^s*(2*t+1) := by rw [hfac,ht]
      exact ⟨(1::l.map (2*·)).map ((2^s)*·),he ▸ scale (by positivity) (odd_part hl)⟩

private def stairs (b : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => b :: stairs (2*b) k
private def low (k : ℕ) := 2^k-1
private lemma low_succ (k : ℕ) : low (k+1)=1+2*low k := by
  have hp : 0<(2:ℕ)^k := by positivity
  unfold low; rw [pow_succ]; omega

private lemma stair_spec {b : ℕ} (hb : 0<b) (k : ℕ) :
    IsPartition (b*low k) k (stairs b k) ∧
      ∀ x ∈ stairs b k, b ≤ x ∧ b ∣ x := by
  induction k generalizing b with
  | zero => simp [stairs,low,IsPartition]
  | succ k ih =>
    obtain ⟨h,hh⟩:=ih (b:=2*b) (by omega)
    constructor
    · refine ⟨by simp [stairs,h.1,low_succ]; ring,by simp [stairs,h.2.1],?_,?_⟩
      · intro x hx; rcases List.mem_cons.mp hx with rfl|hx
        · exact hb
        · exact h.2.2.1 x hx
      · rw [stairs,List.pairwise_cons]
        refine ⟨?_,h.2.2.2⟩
        intro x hx
        have hx':=hh x hx
        exact ⟨by omega,dvd_trans (dvd_mul_left b 2) hx'.2⟩
    · intro x hx; rcases List.mem_cons.mp hx with rfl|hx
      · simp
      · have hx':=hh x hx
        exact ⟨by omega,dvd_trans (dvd_mul_left b 2) hx'.2⟩

private lemma lower {n k b : ℕ} {l : List ℕ} (h : IsPartition n k l) (hb : bound b l) :
    b*low k ≤ n ∧ (b*low k=n → l=stairs b k) := by
  induction k generalizing n b l with
  | zero =>
    have hl:=h.2.1
    have he:=List.length_eq_zero_iff.mp hl
    simp [he,low,stairs]
  | succ k ih =>
    cases l with
    | nil => simp [IsPartition] at h
    | cons d l =>
      have hd:=h.2.2.1 d (by simp)
      have hb' := hb d (by simp)
      have hrel := List.pairwise_cons.mp h.2.2.2
      have hl : IsPartition l.sum k l :=
        ⟨rfl,by simpa using h.2.1,fun x hx => h.2.2.1 x (by simp [hx]),hrel.2⟩
      have hb2 : bound (2*d) l := by
        intro x hx
        obtain ⟨hlt,u,rfl⟩:=hrel.1 x hx
        have hu : 2 ≤ u := by
          by_contra! h'
          have ht:=Nat.mul_le_mul_left d (show u≤1 by omega)
          omega
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hu
      obtain ⟨hmin,heq⟩:=ih hl hb2
      have hs : d+l.sum=n := h.1
      have rule (z : ℕ) : z*low (k+1)=z+(2*z)*low k := by rw [low_succ]; ring
      have hl' : d*low (k+1) ≤ n := by rw [rule]; omega
      have hbd := Nat.mul_le_mul_right (low (k+1)) hb'
      refine ⟨hbd.trans hl',?_⟩
      intro hbn
      have hpos : 0<low (k+1) := by rw [low_succ]; omega
      have he : b=d := by
        by_contra hne
        have ht:=Nat.mul_lt_mul_of_pos_right (lt_of_le_of_ne hb' hne) hpos
        omega
      subst b
      rw [rule] at hbn
      rw [stairs,heq (by omega)]

private lemma abundance (k b : ℕ) : ∃ M : ℕ, 0<M ∧
    ∀ n : ℕ, 0<n → M ∣ n → b ≤ count 1 (k+2) n := by
  classical
  let size (i : Fin b) := 2*(cutoff k+i.val)+1
  let M := (2*(cutoff k+b)+1).factorial
  refine ⟨M,Nat.factorial_pos _,?_⟩
  intro n hn hd
  have hsize (i : Fin b) : size i ∣ n := by
    apply dvd_trans _ hd
    apply Nat.dvd_factorial
    · dsimp [size]; omega
    · dsimp [size]; omega
  choose l hl using (fun i : Fin b => large k (cutoff k+i.val) (by omega))
  let d (i : Fin b) := n / size i
  have he (i : Fin b) : d i * size i=n := Nat.div_mul_cancel (hsize i)
  have hp (i : Fin b) : 0<d i := by
    apply Nat.div_pos (Nat.le_of_dvd hn (hsize i)); dsimp [size]; omega
  let v (i : Fin b) := (1::(l i).map (2*·)).map (d i*·)
  have hv (i : Fin b) : v i ∈ partitions 1 (k+2) n := by
    have hh : IsPartition n (k+2) (v i) := he i ▸ scale (hp i) (odd_part (hl i))
    exact (membership _ _ _ _).mpr ⟨hh,hh.2.2.1⟩
  let f (i : Fin b) : ↥(partitions 1 (k+2) n) := ⟨v i,hv i⟩
  have hf : Function.Injective f := by
    intro i j h
    have hv' : v i=v j := congrArg Subtype.val h
    have he' : d i=d j := by simpa [v] using (List.cons.inj hv').1
    have hm : d i * size i = d i * size j := by rw [he,he',he]
    have hs := Nat.eq_of_mul_eq_mul_left (hp i) hm
    apply Fin.ext; dsimp [size] at hs; omega
  have hh:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Fintype.card_coe, cardinal] using hh

end OMA.P_mo_315485
open OMA.S_mo_315485 OMA.P_mo_315485 in
theorem OMA.solution : type_of% @OMA.S_mo_315485.main := by
  refine ⟨?_,fun n k => cardinal 1 k n,fun n k => large k n,abundance,?_⟩
  · intro n k l
    exact (membership _ _ _ _).trans ⟨And.left,fun h => ⟨h,h.2.2.1⟩⟩
  · intro k
    refine ⟨fun n l h => ?_,stairs 1 k,?_,?_⟩
    · simpa only [one_mul,low] using (lower (b:=1) h h.2.2.1).1
    · simpa only [one_mul,low] using (stair_spec (b:=1) (by decide) k).1
    · intro l hl; exact (lower (b:=1) hl hl.2.2.1).2 (one_mul _)
