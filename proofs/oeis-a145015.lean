import OMAStatements.S_oeis_a145015
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! Denis Boigelot's conjecture about the binary digit imbalance. We locate
the two runs adjacent to a change from negative to positive by examining
aligned binary blocks on either side of the change. -/
namespace OMA.BinaryRuns
open OMA.S_oeis_a145015

private theorem bits {p : ℕ} (hp : 0 < p) :
    balance (2*p) = balance p + 1 ∧ balance (2*p+1) = balance p - 1 := by
  have e := Nat.digits_add 2 (by decide) 0 p (by decide) (Or.inr hp.ne')
  have o := Nat.digits_add 2 (by decide) 1 p (by decide) (Or.inr hp.ne')
  simp only [zero_add] at e
  rw [Nat.add_comm 1] at o
  simp only [balance,if_neg (show 2*p ≠ 0 by omega),if_neg (show 2*p+1 ≠ 0 by omega),
    if_neg hp.ne',e,o]
  simp
  omega

private def start (p r : ℕ) := p*2^r
private def last (p r : ℕ) := start p r + (2^r-1)

private theorem ends (p r : ℕ) (hp : 0 < p) :
    balance (start p r) = balance p + r ∧ balance (last p r) = balance p - r := by
  induction r with
  | zero => simp [start,last]
  | succ r ih =>
    have pw : 0 < 2^r := by positivity
    have ha : 0 < start p r := Nat.mul_pos hp pw
    have hb : 0 < last p r := by unfold last; omega
    have e : start p (r+1) = 2*start p r := by simp [start,pow_succ]; ring
    have f : last p (r+1) = 2*last p r+1 := by unfold last; rw [e,pow_succ]; omega
    rw [e,f,(bits ha).1,(bits hb).2,ih.1,ih.2]; push_cast; omega

/-- The first suffix (all zeros) uniquely maximizes the balance. The last
suffix (all ones) uniquely minimizes it. Every other value differs by at least two. -/
private theorem extrema (p r j : ℕ) (hp : 0 < p) (hj : j < 2^r) :
    balance (start p r + j) ≤ balance p + r - (if j=0 then 0 else 2) ∧
    balance p - r + (if j+1=2^r then 0 else 2) ≤ balance (start p r + j) := by
  induction r generalizing j with
  | zero =>
    have : j=0 := by simpa using hj
    subst j; simp [start]
  | succ r ih =>
    have pw : 0 < 2^r := by positivity
    have d : j/2 < 2^r := by rw [pow_succ] at hj; omega
    have h := ih (j/2) d
    have ha : 0 < start p r := Nat.mul_pos hp pw
    have hb := bits (show 0 < start p r+j/2 by omega)
    have e : start p (r+1) = 2*start p r := by simp [start,pow_succ]; ring
    rw [e,pow_succ]; push_cast
    rcases Nat.mod_two_eq_zero_or_one j with he | he
    · rw [show 2*start p r+j=2*(start p r+j/2) by omega,hb.1]
      split_ifs at * <;> omega
    · rw [show 2*start p r+j=2*(start p r+j/2)+1 by omega,hb.2]
      split_ifs at * <;> omega

private theorem strict_pos {i : ℕ} (h : 0 < balance i) : positive i = true := by
  cases i with
  | zero => rfl
  | succ i => simp [positive,ne_of_gt h,h]

private theorem strict_neg {i : ℕ} (h : balance i < 0) : positive i = false := by
  cases i with
  | zero => change (1:ℤ) < 0 at h; omega
  | succ i => simp [positive,ne_of_lt h,not_lt_of_ge h.le]

private theorem neutral {i : ℕ} (h : balance (i+1)=0) : positive (i+1)=positive i := by
  simp [positive,h]

private theorem keep_pos (s j : ℕ) (first : positive s = true)
    (h : ∀ i ≤ j, 0 ≤ balance (s+i)) : positive (s+j) = true := by
  induction j with
  | zero => simpa using first
  | succ j ih =>
    have hb := h (j+1) le_rfl
    rcases eq_or_lt_of_le hb with hz | hz
    · rw [show s+(j+1)=s+j+1 by omega,neutral (by simpa [Nat.add_assoc] using hz.symm)]
      exact ih (fun i hi => h i (by omega))
    · exact strict_pos hz

private theorem keep_neg (s j : ℕ) (first : positive s = false)
    (h : ∀ i ≤ j, balance (s+i) ≤ 0) : positive (s+j) = false := by
  induction j with
  | zero => simpa using first
  | succ j ih =>
    have hb := h (j+1) le_rfl
    rcases eq_or_lt_of_le hb with hz | hz
    · rw [show s+(j+1)=s+j+1 by omega,neutral (by simpa [Nat.add_assoc] using hz)]
      exact ih (fun i hi => h i (by omega))
    · exact strict_neg hz

private def allowed (k : ℕ) : Prop :=
  (∃ j : ℕ, 1 ≤ j ∧ k=2^j-1) ∨ (∃ j : ℕ, 3 ≤ j ∧ k=2^j-3)

private theorem pow_split (r h : ℕ) (hr : h ≤ r) : 2^r=2^(r-h)*2^h := by
  rw [← pow_add, Nat.sub_add_cancel hr]

private def headLength (z : ℤ) : ℕ := 2^(z/2+1).toNat-1
private def tailLength (z : ℤ) : ℕ := 2^((-z)/2+1).toNat - (if z%2=0 then 3 else 1)

/-- Positive runs beginning at the first point of a mixed block. -/
private theorem head_run (p r : ℕ) (hp : 0 < p) (hpos : 0 < balance (start p r))
    (hneg : balance (last p r) < 0) :
    ∃ k, k=headLength (balance (start p r)) ∧ allowed k ∧ (∀ j<k, positive (start p r+j)=true) ∧ positive (start p r+k)=false := by
  let h := ((balance (start p r))/2+1).toNat
  have he := ends p r hp
  have hb : 1 ≤ h ∧ h ≤ r ∧ balance (start p r) < 2*(h:ℤ) ∧
      2*(h:ℤ) ≤ balance (start p r)+2 := by dsimp [h]; omega
  let q := p*2^(r-h)
  have hq : 0 < q := Nat.mul_pos hp (by positivity)
  have eq : start q h = start p r := by unfold start q; rw [pow_split r h hb.2.1]; ring
  have ed := ends q h hq
  rw [eq] at ed
  have pw : 0 < 2^h := by positivity
  refine ⟨2^h-1,rfl,Or.inl ⟨h,hb.1,rfl⟩,?_,?_⟩
  · intro j hj
    apply keep_pos _ _ (strict_pos hpos)
    intro i hi
    have g := (extrema q h i hq (by omega)).2
    rw [eq,if_neg (show i+1≠2^h by omega)] at g; omega
  · apply strict_neg
    have g := ed.2
    unfold last at g; rw [eq] at g; omega

private theorem first_four (d : ℕ) (hd : 0<d) :
    balance (4*d+1)=balance (4*d)-2 ∧ balance (4*d+2)=balance (4*d)-2 ∧
    balance (4*d+3)=balance (4*d)-4 := by
  have a := bits hd
  have b := bits (show 0<2*d by omega)
  have c := bits (show 0<2*d+1 by omega)
  rw [show 4*d=2*(2*d) by omega,show 2*(2*d)+2=2*(2*d+1) by omega,
      show 2*(2*d)+3=2*(2*d+1)+1 by omega]
  omega

/-- The rightmost subblock starting strictly positive has initial balance
one or two. In the second case its next two entries are ties. -/
private theorem tail_run (p r : ℕ) (hp : 0<p) (hpos : 0<balance (start p r))
    (hneg : balance (last p r)<0) :
    ∃ s k, k=tailLength (balance (last p r)) ∧ 0<s ∧ s+k=start p r+2^r ∧ allowed k ∧ positive (s-1)=true ∧
      ∀ j<k, positive (s+j)=false := by
  let h := ((-balance (last p r))/2+1).toNat
  have he := ends p r hp
  have hb : 1 ≤ h ∧ h ≤ r ∧ 0 < balance (last p r)+2*(h:ℤ) ∧
      balance (last p r)+2*(h:ℤ) ≤ 2 := by dsimp [h]; omega
  let q := (p+1)*2^(r-h)-1
  have f : q+1=(p+1)*2^(r-h) := by
    have : 0 < (p+1)*2^(r-h) := by positivity
    dsimp [q]; omega
  have hq : 0<q := by
    have : 1 ≤ 2^(r-h) := Nat.one_le_two_pow
    nlinarith [f]
  have endEq : start q h+2^h=start p r+2^r := by
    unfold start
    calc
      q*2^h+2^h = (q+1)*2^h := by ring
      _ = (p+1)*2^r := by rw [f,pow_split r h hb.2.1]; ring
      _ = _ := by ring
  have pw : 0<2^h := by positivity
  have pw' : 0<2^r := by positivity
  have same : last q h=last p r := by unfold last; omega
  have ed := ends q h hq
  rw [same] at ed
  let a := start q h
  have top : balance a = balance (last p r)+2*(h:ℤ) := by dsimp [a]; omega
  have nonpos (i : ℕ) (hi : 0<i) (hi' : i<2^h) : balance (a+i) ≤ 0 := by
    have g := (extrema q h i hq hi').1
    rw [if_neg hi.ne'] at g; change balance (start q h+i) ≤ 0; omega
  have finish (c : ℕ) (hc : 0<c) (hc' : c<2^h) (ha : allowed (2^h-c))
      (lengthEq : 2^h-c=tailLength (balance (last p r)))
      (before : positive (a+c-1)=true) (after : positive (a+c)=false) :
      ∃ s k, k=tailLength (balance (last p r)) ∧ 0<s ∧ s+k=start p r+2^r ∧ allowed k ∧ positive (s-1)=true ∧
        ∀ j<k, positive (s+j)=false := by
    refine ⟨a+c,2^h-c,lengthEq,by omega,by dsimp [a]; omega,ha,before,?_⟩
    intro j hj
    apply keep_neg _ _ after
    intro i hi; rw [Nat.add_assoc]; exact nonpos _ (by omega) (by omega)
  have ha := strict_pos (show 0<balance a by omega)
  by_cases one : balance a=1
  · have size : 1<2^h := Nat.one_lt_two_pow (by omega)
    apply finish 1 (by decide) size (Or.inl ⟨h,hb.1,rfl⟩) (by
      have hz : balance (last p r)%2≠0 := by omega
      simp [tailLength,h,hz]) (by simpa using ha)
    apply strict_neg
    have g := (extrema q h 1 hq size).1
    simp only [Nat.one_ne_zero,if_false] at g
    change balance (start q h)=1 at one
    change balance (start q h+1)<0
    omega
  · have two : balance a=2 := by omega
    have h2 : 2 ≤ h := by omega
    have four : 4 ≤ 2^h := Nat.pow_le_pow_right (by decide : 0<2) h2
    let d := q*2^(h-2)
    have hd : 0<d := Nat.mul_pos hq (by positivity)
    have eq : a=4*d := by
      dsimp [a,d,start]; rw [pow_split h 2 h2]; ring
    have g := first_four d hd
    rw [← eq] at g
    have hz1 := neutral (show balance (a+1)=0 by omega)
    have hz2 := neutral (i:=a+1) (show balance (a+1+1)=0 by change balance (a+2)=0; omega)
    have ok : allowed (2^h-3) := by
      rcases eq_or_lt_of_le h2 with h2' | h2'
      · rw [← h2']; exact Or.inl ⟨1,by decide,by decide⟩
      · exact Or.inr ⟨h,h2',rfl⟩
    apply finish 3 (by decide) (by omega) ok (by
      have hz : balance (last p r)%2=0 := by omega
      simp [tailLength,h,hz])
    · rw [show a+3-1=a+1+1 by omega,hz2,hz1,ha]
    · apply strict_neg; omega

private theorem rise_blocks (e : ℕ) (he : 5 ≤ e) (prev : positive (e-1)=false)
    (now : positive e=true) :
    ∃ p r u v : ℕ, 0<p ∧ 0<u ∧ start p r=e ∧ start u v+2^v=e ∧
      0<balance (start p r) ∧ balance (last p r)<0 ∧
      0<balance (start u v) ∧ balance (last u v)<0 := by
  have hpos : 0<balance e := by
    by_contra! h
    rcases eq_or_lt_of_le h with h | h
    · have eq := neutral (i:=e-1) (by simpa [Nat.sub_add_cancel (show 1≤e by omega)] using h)
      rw [Nat.sub_add_cancel (by omega),prev,now] at eq; contradiction
    · rw [strict_neg h] at now; contradiction
  obtain ⟨r,p,oddp,eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : e≠0)
  have size : start p r=e := by unfold start; rw [eq,Nat.mul_comm]
  obtain ⟨d,hd⟩ := oddp
  have hp : 0<p := by omega
  have hi := ends p r hp
  by_cases dz : d=0
  · have p1 : p=1 := by omega
    rw [p1] at size hi
    have pr : 3≤r := by
      by_contra! h
      interval_cases r <;> norm_num [start] at size <;> omega
    let v := r-1
    have eqv : v+1=r := by dsimp [v]; omega
    have left : start 1 v+2^v=e := by
      have h : e=2^r := by simpa [start] using size.symm
      rw [h,← eqv,pow_succ]; simp [start]; omega
    have b1 : balance 1 = -1 := by decide
    have bl := ends 1 v (by decide)
    refine ⟨1,r,1,v,by decide,by decide,size,left,?_,?_,?_,?_⟩
    all_goals omega
  · let u := 2*d
    have hu : 0<u := by dsimp [u]; omega
    have rel : balance u=balance p+2 := by
      have h := bits (show 0<d by omega)
      have e' : p=2*d+1 := by omega
      rw [e']; dsimp [u]; omega
    have left : start u r+2^r=e := by
      rw [← size]; unfold start; have : p=u+1 := by dsimp [u]; omega
      rw [this]; ring
    have hl := ends u r hu
    have rt : 0 < balance (start p r) := size.symm ▸ hpos
    have first : 0<balance (start u r) := by omega
    have lastNeg : balance (last u r)<0 := by
      by_contra! h
      have pw : 0<2^r := by positivity
      have hz := keep_pos (start u r) (2^r-1) (strict_pos first) (by
        intro j hj
        have g := (extrema u r j hu (by omega)).2
        split_ifs at g <;> omega)
      have e' : start u r+(2^r-1)=e-1 := by omega
      rw [e',prev] at hz; contradiction
    exact ⟨p,r,u,r,hp,hu,size,left,rt,by omega,first,lastNeg⟩

private theorem classify (k : ℕ) (hk : IsRunLength k) : allowed k := by
  obtain ⟨hk,s,hs,run,stop⟩ := hk
  by_cases color : positive s=true
  · have st : positive (s+k)=false := by cases h : positive (s+k) <;> simp_all
    have small (h : s≤4) : allowed k := by
      have one : k=1 := by
        by_contra! h1
        have n := run 1 (by omega)
        have init : ∀ i : Fin 5, positive i.val=true → positive (i.val+1)=false := by decide
        have f := init ⟨s,by omega⟩ color
        change positive (s+1)=false at f
        rw [f,color] at n; contradiction
      exact Or.inl ⟨1,by decide,by omega⟩
    by_cases sl : s≤4
    · exact small sl
    have prev : positive (s-1)=false := by
      rcases hs with h | h
      · omega
      · cases h' : positive (s-1) <;> simp_all
    obtain ⟨p,r,u,v,hp,_,eq,_,hs',he',_,_⟩ := rise_blocks s (by omega) prev color
    obtain ⟨len,_,ok,inside,outside⟩ := head_run p r hp hs' he'
    rw [eq] at inside outside
    rcases lt_trichotomy k len with lt | same | gt
    · have := inside k lt; simp_all
    · simpa [same] using ok
    · have := run len gt; simp_all
  · have c : positive s=false := by cases z : positive s <;> simp_all
    have st : positive (s+k)=true := by cases z : positive (s+k) <;> simp_all
    have hs0 : 0<s := by
      by_contra! h; have h' : s=0 := by omega
      rw [h'] at c; contradiction
    have prev : positive (s-1)=true := by
      rcases hs with h | h
      · omega
      · cases z : positive (s-1) <;> simp_all
    by_cases sm : s+k≤4
    · have init : ∀ i : Fin 4, 0<i.val → positive (i.val-1)=true → positive i.val=false → i.val=1 := by decide
      have ends' : ∀ i : Fin 5, 1<i.val → positive i.val=true → i.val=4 := by decide
      have h1 : s=1 := init ⟨s,by omega⟩ hs0 prev c
      have h4 : s+k=4 := ends' ⟨s+k,by omega⟩ (by change 1<s+k; omega) st
      exact Or.inl ⟨2,by decide,by omega⟩
    have bef : positive (s+k-1)=false := by
      rw [show s+k-1=s+(k-1) by omega,run (k-1) (by omega),c]
    obtain ⟨p,r,u,v,_,hu,_,eq,_,_,hs',he'⟩ := rise_blocks (s+k) (by omega) bef st
    obtain ⟨w,len,_,hw,ee,ok,before,inside⟩ := tail_run u v hu hs' he'
    rw [eq] at ee
    have same : s=w := by
      rcases lt_trichotomy s w with lt | same | gt
      · have h := run (w-1-s) (by omega)
        rw [show s+(w-1-s)=w-1 by omega,before,c] at h; contradiction
      · exact same
      · have h := inside (s-1-w) (by omega)
        rw [show w+(s-1-w)=s-1 by omega,prev] at h; contradiction
    have : k=len := by omega
    simpa [this] using ok

/-- Both families occur at boundaries between consecutive binary word lengths. -/
private theorem realize (k : ℕ) (ok : allowed k) : IsRunLength k := by
  have b1 : balance 1 = -1 := by decide
  rcases ok with ⟨j,hj,rfl⟩ | ⟨j,hj,rfl⟩
  · let r := 2*j
    have bounds := ends 1 r (by decide)
    have br : (r:ℤ)=2*(j:ℤ) := by simp [r]
    have hm : r-1+1=r := by dsimp [r]; omega
    have prevLen := ends 1 (r-1) (by decide)
    have pp : start 1 r-1 = last 1 (r-1) := by
      unfold start last; simp only [one_mul,start]
      nth_rw 1 [← hm,pow_succ]
      have h : 0 < 2^(r-1) := by positivity
      omega
    have prev : positive (start 1 r-1)=false := by rw [pp]; apply strict_neg; omega
    have pos : 0<balance (start 1 r) := by omega
    obtain ⟨len,eq,_,run,stop⟩ := head_run 1 r (by decide) pos (by omega)
    have hlen : len=2^j-1 := by
      rw [eq,headLength,show (balance (start 1 r)/2+1).toNat=j by omega]
    rw [hlen] at run stop
    have h := Nat.one_lt_two_pow (by omega : j≠0)
    refine ⟨by omega,start 1 r,Or.inr ?_,?_,?_⟩
    · rw [prev,strict_pos pos]; decide
    · intro i hi; rw [run i hi,strict_pos pos]
    · rw [stop,strict_pos pos]; decide
  · let r := 2*j-3
    have br : (r:ℤ)=2*(j:ℤ)-3 := by dsimp [r]; omega
    have bounds := ends 1 r (by decide)
    obtain ⟨s,len,eq,_,e,_,prev,run⟩ := tail_run 1 r (by decide) (by omega) (by omega)
    have hlen : len=2^j-3 := by
      have hz : balance (last 1 r)%2=0 := by omega
      rw [eq,tailLength,show ((-balance (last 1 r))/2+1).toNat=j by omega,if_pos hz]
    rw [hlen] at e run
    have pw : 8≤2^j := Nat.pow_le_pow_right (by decide : 0<2) hj
    have sgn := run 0 (by omega)
    rw [Nat.add_zero] at sgn
    have next : start 1 r+2^r=start 1 (r+1) := by simp [start,pow_succ]; omega
    have upper := ends 1 (r+1) (by decide)
    have en : positive (s+(2^j-3))=true := by
      rw [e,next]; apply strict_pos; push_cast at upper; omega
    refine ⟨by omega,s,Or.inr ?_,?_,?_⟩
    · rw [prev,sgn]; decide
    · intro i hi; rw [run i hi,sgn]
    · rw [en,sgn]; decide

/-- Exact classification of all run lengths, including attainment of both families. -/
theorem run_length_iff (k : ℕ) : IsRunLength k ↔
    (∃ j : ℕ, 1 ≤ j ∧ k=2^j-1) ∨ (∃ j : ℕ, 3 ≤ j ∧ k=2^j-3) :=
  ⟨classify k,realize k⟩

end OMA.BinaryRuns

theorem OMA.solution : type_of% @OMA.S_oeis_a145015.main := fun k => (OMA.BinaryRuns.run_length_iff k).mp
