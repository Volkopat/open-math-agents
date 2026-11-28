import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2_H1_R1
import Mathlib

/-!
# Three-matching graphs of finite nilpotent groups of odd order

For a noncommuting generating pair, select a Sylow subgroup on which the
two generators do not commute. Two maximal subgroups give a quotient
onto the two-dimensional vector space over the corresponding prime field.
In its matching graph, three equal-length paths have disjoint interiors.
Their common length is four for p = 3, eight for p = 5, and sixteen for
p ≥ 7. The last pattern fits in a seven-by-five rectangle.

Lift the paths from each kernel element. If two lifted endpoints coincide
there is already a simple cycle of twice the path length. Otherwise these
routes subdivide three matchings on the smaller nilpotent kernel. Strong
induction gives a dyadic cycle, and subdivision preserves the dyadic length.

This extends the order-three descent of @mejiasd3v (PR 7326). We use
the project's cycle-from-period and local commutation lemmas.
-/

namespace Erdos64.Theta
open SimpleGraph


open OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2 (cycle_from_period adj_mod)

private def cyclicIndex {n : ℕ} (hn : 0 < n) (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt k hn⟩

private def next {n : ℕ} (i : Fin n) : Fin n := cyclicIndex (Nat.zero_lt_of_lt i.isLt) (i.val+1)

private theorem next_index {n : ℕ} (hn : 0 < n) (k : ℕ) :
    next (cyclicIndex hn k) = cyclicIndex hn (k+1) := Fin.ext (Nat.mod_add_mod k n 1)

private theorem concatenate {V : Type*} (G : SimpleGraph V) (n l : ℕ) (hn : 2 ≤ n) (hl : 0 < l)
    (path : Fin n → ℕ → V)
    (edge : ∀ i t, t < l → G.Adj (path i t) (path i (t+1)))
    (join : ∀ i, path i l = path (next i) 0)
    (inj : ∀ i j t u, t < l → u < l → path i t = path j u → i=j ∧ t=u) :
    cycleGraph (n*l) ⊑ G := by
  let idx := cyclicIndex (show 0 < n by omega)
  let p (k : ℕ) := path (idx (k/l)) (k%l)
  apply cycle_from_period G (n*l) (by nlinarith) p
  · intro k
    have dec := Nat.mod_add_div k l
    have bound := Nat.mod_lt k hl
    have e := edge (idx (k/l)) (k%l) bound
    by_cases last : k%l+1=l
    · have eq : k+1=(k/l+1)*l := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (k/l) l]; omega
      simpa [p,eq,hl,last,join,next_index,idx] using e
    · have lt : k%l+1<l := by omega
      have eq : k+1 = (k%l+1) + l*(k/l) := by omega
      simpa [p,eq,Nat.add_mul_div_left,hl,Nat.div_eq_of_lt lt,Nat.mod_eq_of_lt lt] using e
  · simp [p,idx,cyclicIndex,hl]
  · intro i j hi hj eq
    obtain ⟨e1,e2⟩ := inj _ _ _ _ (Nat.mod_lt _ hl) (Nat.mod_lt _ hl) eq
    have vals := congrArg Fin.val e1
    have il : i/l < n := (Nat.div_lt_iff_lt_mul hl).mpr hi
    have jl : j/l < n := (Nat.div_lt_iff_lt_mul hl).mpr hj
    have quot : i/l=j/l := by simpa [idx,cyclicIndex,Nat.mod_eq_of_lt il,Nat.mod_eq_of_lt jl] using vals
    exact (Nat.mod_add_div i l).symm.trans (by rw [e2,quot,Nat.mod_add_div])

/-- A family of paths meeting only at their prescribed branch vertices.
Interior points identify both the route and the position along it. -/
structure Routes {V X E : Type*} (G : SimpleGraph V) (l : ℕ) where
  branch : X ↪ V
  left : E → X
  right : E → X
  route : E → ℕ → V
  start : ∀ e, route e 0 = branch (left e)
  finish : ∀ e, route e l = branch (right e)
  edge : ∀ e t, t < l → G.Adj (route e t) (route e (t+1))
  avoids : ∀ e t, 0 < t → t < l → ∀ x, route e t ≠ branch x
  unique : ∀ e e' t u, 0 < t → t < l → 0 < u → u < l →
    route e t = route e' u → e=e' ∧ t=u

private theorem Routes.loop {V X E : Type*} {G : SimpleGraph V} {l n : ℕ}
    (r : Routes (X:=X) (E:=E) G l) (hn : 2 ≤ n) (hl : 0 < l)
    (v : Fin n ↪ X) (e : Fin n ↪ E) (dir : Fin n → Bool)
    (ends : ∀ i, if dir i then r.left (e i) = v i ∧ r.right (e i) = v (next i)
                            else r.right (e i) = v i ∧ r.left (e i) = v (next i)) :
    cycleGraph (n*l) ⊑ G := by
  let pos (i : Fin n) (t : ℕ) := if dir i then t else l-t
  let p (i : Fin n) (t : ℕ) := r.route (e i) (pos i t)
  have start (i : Fin n) : p i 0 = r.branch (v i) := by
    have h := ends i
    cases hd : dir i <;> simp [hd] at h <;> simp [p,pos,hd,r.start,r.finish,h]
  have finish (i : Fin n) : p i l = r.branch (v (next i)) := by
    have h := ends i
    cases hd : dir i <;> simp [hd] at h <;> simp [p,pos,hd,r.start,r.finish,h]
  have interior (i : Fin n) (t : ℕ) (h : 0<t) (h' : t<l) : 0 < pos i t ∧ pos i t < l := by
    cases hd : dir i <;> simp [pos,hd] <;> omega
  apply concatenate G n l hn hl p
  · intro i t ht
    cases hd : dir i
    · have edge := (r.edge (e i) (l-(t+1)) (by omega)).symm
      simpa [p,pos,hd,show l-(t+1)+1=l-t by omega] using edge
    · simpa [p,pos,hd] using r.edge (e i) t ht
  · intro i; rw [finish,start]
  · intro i j t u ht hu eq
    rcases Nat.eq_zero_or_pos t with rfl|tp
    · rcases Nat.eq_zero_or_pos u with rfl|up
      · rw [start,start] at eq
        exact ⟨v.injective (r.branch.injective eq),rfl⟩
      · rw [start] at eq
        exact (r.avoids _ _ (interior j u up hu).1 (interior j u up hu).2 _ eq.symm).elim
    · rcases Nat.eq_zero_or_pos u with rfl|up
      · rw [start] at eq
        exact (r.avoids _ _ (interior i t tp ht).1 (interior i t tp ht).2 _ eq).elim
      · obtain ⟨edgeId,time⟩ := r.unique _ _ _ _ (interior i t tp ht).1 (interior i t tp ht).2
          (interior j u up hu).1 (interior j u up hu).2 eq
        obtain rfl := e.injective edgeId
        refine ⟨rfl,?_⟩
        cases hd : dir i <;> simp [pos,hd] at time <;> omega

private theorem next_twice_ne {n : ℕ} (hn : 3≤n) (i : Fin n) : next (next i) ≠ i := by
  intro eq
  have inc (j : Fin n) : (next j).val=j.val+1 ∨ (next j).val=0 ∧ j.val+1=n := by
    by_cases lt : j.val+1<n
    · exact .inl (Nat.mod_eq_of_lt lt)
    · have wrap : j.val+1=n := by omega
      exact .inr ⟨by simp [next,cyclicIndex,wrap],wrap⟩
  have h := congrArg Fin.val eq
  rcases inc i with h|h <;> rcases inc (next i) with j|j <;> omega

theorem Routes.lift {V X E : Type*} {G : SimpleGraph V} {l n : ℕ}
    (r : Routes (X:=X) (E:=E) G l) (B : SimpleGraph X)
    (covers : ∀ x y, B.Adj x y → ∃ e, (r.left e=x ∧ r.right e=y) ∨ (r.right e=x ∧ r.left e=y))
    (hn : 3≤n) (hl : 0<l) (cycle : cycleGraph n ⊑ B) : cycleGraph (n*l) ⊑ G := by
  classical
  obtain ⟨v⟩ := cycle
  have along (i : Fin n) := covers (v i) (v (next i))
    (v.toHom.map_adj ((adj_mod (by omega) i (next i)).mpr (.inl rfl)))
  choose e he using along
  have ei : Function.Injective e := by
    intro i j eq
    have h := he i
    rw [eq] at h
    have t := he j
    have alt : v i=v j ∨ (v (next i)=v j ∧ v (next j)=v i) := by grind
    rcases alt with same|⟨a,b⟩
    · exact v.injective same
    · exact (next_twice_ne hn i ((congrArg next (v.injective a)).trans (v.injective b))).elim
  let dir (i : Fin n) := decide (r.left (e i)=v i ∧ r.right (e i)=v (next i))
  apply r.loop (by omega) hl ⟨v,v.injective⟩ ⟨e,ei⟩ dir
  intro i
  change if dir i then r.left (e i)=v i ∧ r.right (e i)=v (next i)
                  else r.right (e i)=v i ∧ r.left (e i)=v (next i)
  by_cases h : r.left (e i)=v i ∧ r.right (e i)=v (next i)
  · simpa only [dir,decide_eq_true h,if_true] using h
  · simpa only [dir,decide_eq_false h,Bool.false_eq_true,if_false] using (he i).resolve_left h

theorem Routes.parallel {V X E : Type*} {G : SimpleGraph V} {l : ℕ}
    (r : Routes (X:=X) (E:=E) G l) (hl : 0<l) (e f : E) (ne : e≠f)
    (apart : r.left e ≠ r.right e) (sameL : r.left e = r.left f) (sameR : r.right e = r.right f) :
    cycleGraph (2*l) ⊑ G := by
  let v : Fin 2 ↪ X := ⟨![r.left e,r.right e],by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  let ed : Fin 2 ↪ E := ⟨![e,f],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  apply r.loop (by decide) hl v ed ![true,false]
  intro i
  fin_cases i
  · exact ⟨rfl,rfl⟩
  · exact ⟨sameR.symm,sameL.symm⟩

def graph {A : Type*} [Group A] (a b : A) : SimpleGraph (Bool × A) :=
  SimpleGraph.fromRel fun u v =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=u.2*a ∨ v.2=u.2*b)

def Good {A : Type*} [Group A] (a b : A) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ graph a b

def step {A : Type*} [Group A] (a b : A) (j : Fin 3) (v : Bool × A) : Bool × A :=
  let s := (![1,a,b] : Fin 3 → A) j
  (!v.1, if v.1 then v.2*s⁻¹ else v.2*s)

def trail {A : Type*} [Group A] (a b : A) (word : ℕ → Fin 3) : ℕ → Bool × A
  | 0 => (false,1)
  | n+1 => step a b (word n) (trail a b word n)

def proj {A Q : Type*} [Group A] [Group Q] (f : A →* Q) (v : Bool × A) : Bool × Q :=
  (v.1, f v.2)

theorem trail_map {A Q : Type*} [Group A] [Group Q] (f : A →* Q) (a b : A)
    (word : ℕ → Fin 3) (n : ℕ) :
    proj f (trail a b word n) = trail (f a) (f b) word n := by
  induction n with
  | zero => simp [proj,trail]
  | succ n ih =>
    rw [trail,trail,←ih]
    generalize trail a b word n = z
    rcases z with ⟨t,x⟩
    generalize word n = j
    cases t <;> fin_cases j <;> simp [proj,step]

private def shift {A : Type*} [Group A] (x : A) (z : Bool × A) : Bool × A := (z.1,x*z.2)

private theorem shift_adj {A : Type*} [Group A] (a b x : A) (v : Bool × A) (j : Fin 3) :
    (graph a b).Adj (shift x v) (shift x (step a b j v)) := by
  obtain ⟨t,u⟩ := v
  cases t <;> fin_cases j <;> simp [graph,shift,step,SimpleGraph.fromRel,mul_assoc]

/-- Three equally long paths from the identity to a different vertex in its part.
The internal vertices are distinct across all three paths. -/
structure Certificate {Q : Type*} [Group Q] (a b : Q) (l : ℕ) where
  word : Fin 3 → ℕ → Fin 3
  target : Q
  different : target ≠ 1
  finish : ∀ i, trail a b (word i) l = (false,target)
  avoids : ∀ i t, 0<t → t<l → trail a b (word i) t ≠ (false,1) ∧
                                  trail a b (word i) t ≠ (false,target)
  unique : ∀ i j t u, 0<t → t<l → 0<u → u<l →
    trail a b (word i) t = trail a b (word j) u → i=j ∧ t=u

theorem compress {A Q : Type*} [Group A] [Group Q] (f : A →* Q) (a b : A) (s : ℕ)
    (positive : 0<s) (cert : Certificate (f a) (f b) (2^s))
    (recurse : ∀ d e : f.ker, d≠1 → e≠1 → d≠e → Good d e) : Good a b := by
  classical
  let l := 2^s
  let path (i : Fin 3) := trail a b (cert.word i)
  let g (i : Fin 3) := (path i l).2
  have image (i : Fin 3) (t : ℕ) : proj f (path i t) = trail (f a) (f b) (cert.word i) t :=
    trail_map f a b _ _
  have last (i : Fin 3) : proj f (path i l) = (false,cert.target) :=
    (image i l).trans (cert.finish i)
  have fg (i : Fin 3) : f (g i) = cert.target := congrArg Prod.snd (last i)
  let d (i : Fin 3) : f.ker := ⟨g i*(g 0)⁻¹,by simp [MonoidHom.mem_ker,fg]⟩
  have d0 : d 0 = 1 := Subtype.ext (mul_inv_cancel _)
  let branch : (Bool × f.ker) ↪ (Bool × A) := {
    toFun z := (false, if z.1 then (z.2:A)*g 0 else z.2)
    inj' := by
      rintro ⟨u,x⟩ ⟨v,y⟩ eq
      have he := congrArg Prod.snd eq
      have fx : f (x:A)=1 := x.property
      have fy : f (y:A)=1 := y.property
      cases u <;> cases v <;> dsimp at he
      · exact Prod.ext rfl (Subtype.ext he)
      · exact (cert.different (by simpa [fx,fy,fg] using (congrArg f he).symm)).elim
      · exact (cert.different (by simpa [fx,fy,fg] using congrArg f he)).elim
      · exact Prod.ext rfl (Subtype.ext (mul_right_cancel he)) }
  let route (e : f.ker × Fin 3) (t : ℕ) := shift (e.1:A) (path e.2 t)
  have project (e : f.ker × Fin 3) (t : ℕ) :
      proj f (route e t) = trail (f a) (f b) (cert.word e.2) t := by
    rw [← image]
    simp [route,shift,proj,show f (e.1:A)=1 from e.1.property]
  let r : Routes (X:=Bool × f.ker) (E:=f.ker × Fin 3) (graph a b) l := {
    branch := branch
    left := fun e => (false,e.1)
    right := fun e => (true,e.1*d e.2)
    route := route
    start := by rintro ⟨x,i⟩; change (false,(x:A)*1) = (false,(x:A)); rw [mul_one]
    finish := by
      rintro ⟨x,i⟩
      apply Prod.ext
      · change (path i l).1 = false
        exact congrArg (fun z : Bool × Q => z.1) (last i)
      · change (x:A)*g i = ((x:A)*(g i*(g 0)⁻¹))*g 0
        simp [mul_assoc]
    edge := fun e t _ => shift_adj a b _ _ _
    avoids := by
      rintro ⟨x,i⟩ t ht ht' ⟨side,y⟩ eq
      have h := (project (x,i) t).symm.trans (congrArg (proj f) eq)
      have fy : f (y:A)=1 := y.property
      cases side
      · change _ = (false,f (y:A)) at h
        exact (cert.avoids i t ht ht').1 (by simpa [fy] using h)
      · change _ = (false,f ((y:A)*g 0)) at h
        exact (cert.avoids i t ht ht').2 (by simpa [fy,fg] using h)
    unique := by
      rintro ⟨x,i⟩ ⟨y,j⟩ t u ht ht' hu hu' eq
      obtain ⟨rfl,rfl⟩ := cert.unique i j t u ht ht' hu hu' <|
        (project (x,i) t).symm.trans ((congrArg (proj f) eq).trans (project (y,j) u))
      exact ⟨Prod.ext (Subtype.ext (mul_right_cancel (congrArg Prod.snd eq))) rfl,rfl⟩ }
  by_cases distinct : Function.Injective d
  · have sep : d 1 ≠ 1 ∧ d 2 ≠ 1 ∧ d 1 ≠ d 2 := by
      rw [← d0]
      exact ⟨fun h => (by decide : (1:Fin 3) ≠ 0) (distinct h),
        fun h => (by decide : (2:Fin 3) ≠ 0) (distinct h),
        fun h => (by decide : (1:Fin 3) ≠ 2) (distinct h)⟩
    obtain ⟨k,hk,cyc⟩ := recurse _ _ sep.1 sep.2.1 sep.2.2
    have cover (x y : Bool × f.ker) (edge : (graph (d 1) (d 2)).Adj x y) :
        ∃ e,(r.left e=x ∧ r.right e=y) ∨ (r.right e=x ∧ r.left e=y) := by
      have orient (u v : Bool × f.ker) (h : u.1=false ∧ v.1=true ∧
          (v.2=u.2 ∨ v.2=u.2*d 1 ∨ v.2=u.2*d 2)) : ∃ e,r.left e=u ∧ r.right e=v := by
        rcases u with ⟨su,x⟩; rcases v with ⟨sv,y⟩
        rcases h with ⟨rfl,rfl,h|h|h⟩
        · exact ⟨(x,0),rfl,Prod.ext rfl (by simpa [r,d0] using h.symm)⟩
        · exact ⟨(x,1),rfl,Prod.ext rfl h.symm⟩
        · exact ⟨(x,2),rfl,Prod.ext rfl h.symm⟩
      rcases edge.2 with h|h
      · obtain ⟨e,t⟩ := orient _ _ h; exact ⟨e,.inl t⟩
      · obtain ⟨e,t⟩ := orient _ _ h; exact ⟨e,.inr ⟨t.2,t.1⟩⟩
    refine ⟨k+s,by omega,?_⟩
    rw [pow_add]
    exact r.lift _ cover (by have := Nat.pow_le_pow_right (by decide : 0<2) hk; omega) (by positivity) cyc
  · rw [Function.Injective] at distinct
    push Not at distinct
    obtain ⟨i,j,eq,ne⟩ := distinct
    let e : f.ker × Fin 3 := (1,i)
    let e' : f.ker × Fin 3 := (1,j)
    have parallel := r.parallel (by dsimp [l]; positivity) e e'
      (fun h => ne (congrArg Prod.snd h)) (fun h => Bool.false_ne_true (congrArg Prod.fst h))
      rfl (Prod.ext rfl (congrArg (fun t : f.ker => 1*t) eq))
    exact ⟨1+s,by omega,by rw [pow_add,pow_one]; exact parallel⟩

abbrev Grid (R : Type*) := Multiplicative R × Multiplicative R
def axisX (R : Type*) [Zero R] [One R] : Grid R := (Multiplicative.ofAdd 1,Multiplicative.ofAdd 0)
def axisY (R : Type*) [Zero R] [One R] : Grid R := (Multiplicative.ofAdd 0,Multiplicative.ofAdd 1)

private def extendWord (n : ℕ) (w : Fin 3 → Fin n → Fin 3) (i : Fin 3) (t : ℕ) : Fin 3 :=
  if h : t<n then w i ⟨t,h⟩ else 0

private theorem trail_table {Q : Type*} [Group Q] {n : ℕ} (a b : Q)
    (w : Fin 3 → Fin n → Fin 3) (tab : Fin 3 → Fin (n+1) → Bool × Q)
    (start : ∀ i, tab i 0 = (false,1))
    (edge : ∀ i (t : Fin n), tab i t.succ = step a b (w i t) (tab i t.castSucc))
    (i : Fin 3) (t : Fin (n+1)) : trail a b (extendWord n w i) t.val = tab i t := by
  induction t using Fin.induction with
  | zero => exact (start i).symm
  | succ j ih =>
    rw [Fin.val_succ,trail,← Fin.val_castSucc j,ih,edge]
    simp [extendWord,j.isLt]

private def ofTable {Q : Type*} [Group Q] (a b q : Q) (n : ℕ)
    (w : Fin 3 → Fin n → Fin 3) (tab : Fin 3 → Fin (n+1) → Bool × Q)
    (diff : q≠1) (start : ∀ i, tab i 0 = (false,1))
    (edge : ∀ i (t : Fin n), tab i t.succ = step a b (w i t) (tab i t.castSucc))
    (last : ∀ i, tab i (Fin.last n) = (false,q))
    (apart : ∀ i (t : Fin (n+1)), 0<t.val → t.val<n → tab i t≠(false,1) ∧ tab i t≠(false,q))
    (unique : ∀ i j (t u : Fin (n+1)), 0<t.val → t.val<n → 0<u.val → u.val<n →
      tab i t = tab j u → i=j ∧ t=u) : Certificate a b n where
  word := extendWord n w
  target := q
  different := diff
  finish := fun i => (trail_table a b w tab start edge i (Fin.last n)).trans (last i)
  avoids := by
    intro i t ht lt
    let t' : Fin (n+1) := ⟨t,by omega⟩
    exact (trail_table a b w tab start edge i t') ▸ apart i t' ht lt
  unique := by
    intro i j t u ht lt hu lu eq
    let t' : Fin (n+1) := ⟨t,by omega⟩
    let u' : Fin (n+1) := ⟨u,by omega⟩
    obtain ⟨same,time⟩ := unique i j t' u' ht lt hu lu
      ((trail_table a b w tab start edge i t').symm.trans (eq.trans (trail_table a b w tab start edge j u')))
    exact ⟨same,congrArg Fin.val time⟩

private def cell {R : Type*} (b : Bool) (x y : R) : Bool × Grid R :=
  (b, Multiplicative.ofAdd x, Multiplicative.ofAdd y)

private def wordsThree : Fin 3 → Fin 4 → Fin 3 :=
  ![![0,1,0,2],![1,2,1,0],![2,0,2,1]]

private def tableThree : Fin 3 → Fin 5 → Bool × Grid (ZMod 3) :=
  ![![cell false (0) (0), cell true (0) (0), cell false (2) (0), cell true (2) (0), cell false (2) (2)],
    ![cell false (0) (0), cell true (1) (0), cell false (1) (2), cell true (2) (2), cell false (2) (2)],
    ![cell false (0) (0), cell true (0) (1), cell false (0) (1), cell true (0) (2), cell false (2) (2)]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def certThree : Certificate (axisX (ZMod 3)) (axisY (ZMod 3)) 4 :=
  ofTable _ _ (Multiplicative.ofAdd (2),Multiplicative.ofAdd (2)) 4 wordsThree tableThree
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wordsFive : Fin 3 → Fin 8 → Fin 3 :=
  ![![0,1,0,1,0,1,0,2],![1,2,0,2,1,0,2,0],![2,0,2,1,2,1,2,1]]

private def tableFive : Fin 3 → Fin 9 → Bool × Grid (ZMod 5) :=
  ![![cell false (0) (0), cell true (0) (0), cell false (4) (0), cell true (4) (0), cell false (3) (0),
      cell true (3) (0), cell false (2) (0), cell true (2) (0), cell false (2) (4)],
    ![cell false (0) (0), cell true (1) (0), cell false (1) (4), cell true (1) (4), cell false (1) (3),
      cell true (2) (3), cell false (2) (3), cell true (2) (4), cell false (2) (4)],
    ![cell false (0) (0), cell true (0) (1), cell false (0) (1), cell true (0) (2), cell false (4) (2),
      cell true (4) (3), cell false (3) (3), cell true (3) (4), cell false (2) (4)]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def certFive : Certificate (axisX (ZMod 5)) (axisY (ZMod 5)) 8 :=
  ofTable _ _ (Multiplicative.ofAdd (2),Multiplicative.ofAdd (4)) 8 wordsFive tableFive
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def wordsWide : Fin 3 → Fin 16 → Fin 3 :=
  ![![0,1,0,1,2,0,2,1,0,2,0,2,0,1,2,1],![1,2,0,1,0,1,0,1,0,1,0,1,2,1,2,0],![2,0,2,1,0,1,2,1,0,1,0,1,0,2,0,2]]

private def tableWide : Fin 3 → Fin 17 → Bool × Grid ℤ :=
  ![![cell false (0) (0), cell true (0) (0), cell false (-1) (0), cell true (-1) (0), cell false (-2) (0),
      cell true (-2) (1), cell false (-2) (1), cell true (-2) (2), cell false (-3) (2), cell true (-3) (2),
      cell false (-3) (1), cell true (-3) (1), cell false (-3) (0), cell true (-3) (0), cell false (-4) (0),
      cell true (-4) (1), cell false (-5) (1)],
    ![cell false (0) (0), cell true (1) (0), cell false (1) (-1), cell true (1) (-1), cell false (0) (-1),
      cell true (0) (-1), cell false (-1) (-1), cell true (-1) (-1), cell false (-2) (-1), cell true (-2) (-1),
      cell false (-3) (-1), cell true (-3) (-1), cell false (-4) (-1), cell true (-4) (0), cell false (-5) (0),
      cell true (-5) (1), cell false (-5) (1)],
    ![cell false (0) (0), cell true (0) (1), cell false (0) (1), cell true (0) (2), cell false (-1) (2),
      cell true (-1) (2), cell false (-2) (2), cell true (-2) (3), cell false (-3) (3), cell true (-3) (3),
      cell false (-4) (3), cell true (-4) (3), cell false (-5) (3), cell true (-5) (3), cell false (-5) (2),
      cell true (-5) (2), cell false (-5) (1)]]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def certWide : Certificate (axisX ℤ) (axisY ℤ) 16 :=
  ofTable _ _ (Multiplicative.ofAdd (-5),Multiplicative.ofAdd (1)) 16 wordsWide tableWide
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def reduceGrid (p : ℕ) : Grid ℤ →* Grid (ZMod p) :=
  let f := (Int.castAddHom (ZMod p)).toMultiplicative
  f.prodMap f

private def box (z : Grid ℤ) : Prop :=
  -5 ≤ z.1.toAdd ∧ z.1.toAdd ≤ 1 ∧ -1 ≤ z.2.toAdd ∧ z.2.toAdd ≤ 3

private theorem box_inj (p : ℕ) (hp : 7≤p) {x y : Grid ℤ} (hx : box x) (hy : box y)
    (h : reduceGrid p x = reduceGrid p y) : x=y := by
  have coord (u v : ℤ) (close : -6 ≤ v-u ∧ v-u ≤ 6) (eq : (u:ZMod p) = v) : u=v := by
    have dvd := (ZMod.intCast_eq_intCast_iff_dvd_sub u v p).mp eq
    have vanish := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs dvd
      (show (v-u).natAbs < (p:ℤ).natAbs by omega)
    omega
  rcases hx with ⟨hx1,hx2,hx3,hx4⟩
  rcases hy with ⟨hy1,hy2,hy3,hy4⟩
  exact Prod.ext (coord x.1.toAdd y.1.toAdd (by omega) (congrArg Prod.fst h))
    (coord x.2.toAdd y.2.toAdd (by omega) (congrArg Prod.snd h))

set_option maxRecDepth 12000 in
private theorem wide_box (i : Fin 3) (t : ℕ) (ht : t≤16) :
    box (trail (axisX ℤ) (axisY ℤ) (certWide.word i) t).2 := by
  let j : Fin 17 := ⟨t,by omega⟩
  have value := trail_table (axisX ℤ) (axisY ℤ) wordsWide tableWide (by decide) (by decide) i j
  have bounds : ∀ i j, -5 ≤ (tableWide i j).2.1.toAdd ∧ (tableWide i j).2.1.toAdd ≤ 1 ∧
      -1 ≤ (tableWide i j).2.2.toAdd ∧ (tableWide i j).2.2.toAdd ≤ 3 := by decide
  exact value ▸ bounds i j

private def modWide (p : ℕ) (hp : 7≤p) :
    Certificate (axisX (ZMod p)) (axisY (ZMod p)) 16 := by
  let f := reduceGrid p
  have fx : f (axisX ℤ)=axisX (ZMod p) := by ext <;> simp [f,reduceGrid,axisX]
  have fy : f (axisY ℤ)=axisY (ZMod p) := by ext <;> simp [f,reduceGrid,axisY]
  let path (i : Fin 3) := trail (axisX ℤ) (axisY ℤ) (certWide.word i)
  have projected (i : Fin 3) (t : ℕ) :
      trail (axisX (ZMod p)) (axisY (ZMod p)) (certWide.word i) t = proj f (path i t) := by
    rw [← fx,← fy]; exact (trail_map f _ _ _ _).symm
  have pinj {u v : Bool × Grid ℤ} (hu : box u.2) (hv : box v.2) (eq : proj f u = proj f v) : u=v :=
    Prod.ext (congrArg (fun z : Bool × Grid (ZMod p) => z.1) eq)
      (box_inj p hp hu hv (congrArg Prod.snd eq))
  have startBox : box 1 := by unfold box; decide
  have endBox : box certWide.target := by unfold box; decide
  refine ⟨certWide.word,f certWide.target,?_,?_,?_,?_⟩
  · intro eq
    exact certWide.different (box_inj p hp endBox startBox (eq.trans (map_one f).symm))
  · intro i; rw [projected,show path i 16=(false,certWide.target) from certWide.finish i]; rfl
  · intro i t ht lt
    rw [projected]
    have bounded := wide_box i t lt.le
    constructor
    · intro eq
      apply (certWide.avoids i t ht lt).1
      exact pinj bounded startBox (by simpa [proj] using eq)
    · intro eq
      exact (certWide.avoids i t ht lt).2 (pinj bounded endBox eq)
  · intro i j t u ht lt hu lu eq
    rw [projected,projected] at eq
    exact certWide.unique i j t u ht lt hu lu (pinj (wide_box i t lt.le) (wide_box j u lu.le) eq)

theorem grid_certificate (p : ℕ) (prime : p.Prime) (hp : 3≤p) :
    ∃ s : ℕ, 0<s ∧ s≤4 ∧ Nonempty (Certificate (axisX (ZMod p)) (axisY (ZMod p)) (2^s)) := by
  by_cases small : p<7
  · interval_cases p
    · exact ⟨2,by decide,by decide,⟨certThree⟩⟩
    · norm_num at prime
    · exact ⟨3,by decide,by decide,⟨certFive⟩⟩
    · norm_num at prime
  · exact ⟨4,by decide,by decide,⟨modWide p (by omega)⟩⟩

private theorem maximal_card {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime] (pgrp : IsPGroup p A)
    (M : Subgroup A) [M.Normal] (max : IsCoatom M) : Nat.card (A ⧸ M)=p := by
  classical
  let f := QuotientGroup.mk' M
  have proper : M≠⊤ := max.1
  have nontrivial : Nontrivial (A ⧸ M) := by
    obtain ⟨x,h⟩ := SetLike.exists_not_mem_of_ne_top M proper
    exact ⟨f x,1,fun eq => h ((QuotientGroup.eq_one_iff x).mp eq)⟩
  have pg := pgrp.to_quotient M
  have dv : p ∣ Nat.card (A ⧸ M) := (pg.card_eq_or_dvd).resolve_left
    (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr nontrivial))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p dv
  let C := Subgroup.zpowers x
  let J := C.comap f
  have le : M ≤ J := by
    intro z hz
    change f z ∈ C
    have id : f z=1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [id]; exact C.one_mem
  have top : J=⊤ := by
    apply max.2
    apply lt_of_le_of_ne le
    intro eq
    obtain ⟨z,hz⟩ := QuotientGroup.mk_surjective x
    have mem : z ∈ J := by
      change f z ∈ C
      change f z=x at hz
      rw [hz]; exact Subgroup.mem_zpowers x
    have val := (QuotientGroup.eq_one_iff z).mpr (eq ▸ mem)
    have xeq : x=1 := hz ▸ val
    simp [xeq] at hx
    exact (Fact.out : p.Prime).ne_one hx.symm
  have ctop : C=⊤ := by
    apply Subgroup.comap_injective (f := f) QuotientGroup.mk_surjective
    simpa [J] using top
  exact (orderOf_eq_card_of_zpowers_eq_top ctop).symm.trans hx


private theorem noncyclic_character {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (pg : IsPGroup p P) (a b : P) (nc : ¬Commute a b)
    (gen : Subgroup.closure ({a,b} : Set P) = ⊤) :
    ∃ f : P →* Multiplicative (ZMod p), f a = 1 ∧ f b = Multiplicative.ofAdd 1 := by
  have proper : Subgroup.zpowers a ≠ ⊤ := by
    intro top
    let : IsCyclic P := ⟨a,fun x => Subgroup.mem_zpowers_iff.mp
      (show x ∈ Subgroup.zpowers a from top ▸ Subgroup.mem_top x)⟩
    exact nc ((IsCyclic.commGroup (α:=P)).mul_comm _ _)
  obtain ⟨M,maximal,inside⟩ := (eq_top_or_exists_le_coatom _).resolve_left proper
  let : M.Normal := ((Group.isNilpotent_of_finite_tfae (G:=P)).out 0 2 rfl rfl).mp pg.isNilpotent M maximal
  let q := QuotientGroup.mk' M
  have am : a ∈ M := inside (Subgroup.mem_zpowers _)
  have bn : q b ≠ 1 := by
    intro eq
    apply maximal.1
    apply top_unique
    rw [← gen,Subgroup.closure_le]
    intro x hx
    rcases (show x=a ∨ x=b by simpa using hx) with rfl|rfl
    · exact am
    · exact (QuotientGroup.eq_one_iff _).mp eq
  have card := maximal_card pg M maximal
  have generates (x : P ⧸ M) : x ∈ Subgroup.zpowers (q b) := mem_zpowers_of_prime_card card bn
  let e := zmodMulEquivOfGenerator generates card
  refine ⟨e.symm.toMonoidHom.comp q,?_,zmodMulEquivOfGenerator_symm_apply_generator ..⟩
  change e.symm (q a)=1
  rw [show q a=1 from (QuotientGroup.eq_one_iff _).mpr am,map_one]

private theorem axes_quotient {A : Type*} [Group A] [Finite A] [Group.IsNilpotent A]
    (odd : Odd (Nat.card A)) (a b : A) (nc : ¬ Commute a b)
    (gen : Subgroup.closure ({a,b} : Set A) = ⊤) :
    ∃ (p : ℕ) (_ : p.Prime) (_ : 3≤p) (f : A →* Grid (ZMod p)),
      f a = axisX (ZMod p) ∧ f b = axisY (ZMod p) := by
  classical
  let iso := Sylow.directProductOfNormal (G:=A) (fun _ => inferInstance)
  have bad : ∃ (i : (Nat.card A).primeFactors) (P : Sylow i.val A),
      ¬ Commute (iso.symm a i P) (iso.symm b i P) := by
    by_contra! h
    apply nc
    apply iso.symm.injective
    ext i P : 2
    simpa only [map_mul,Pi.mul_apply] using (h i P).eq
  obtain ⟨i,P,ncP⟩ := bad
  have prime := Nat.prime_of_mem_primeFactors i.property
  let _ : Fact i.val.Prime := ⟨prime⟩
  let f₁ := Pi.evalMonoidHom (fun j : (Nat.card A).primeFactors => ∀ R : Sylow j A, R) i
  let f₂ := Pi.evalMonoidHom (fun R : Sylow i.val A => R) P
  let π := f₂.comp (f₁.comp iso.symm.toMonoidHom)
  have onto : Function.Surjective π := by
    intro x
    refine ⟨iso (Pi.mulSingle i (Pi.mulSingle P x)),?_⟩
    simp [π,f₁,f₂,Pi.evalMonoidHom]
  have generated : Subgroup.closure ({π a,π b} : Set P) = ⊤ := by
    have h := π.map_closure ({a,b} : Set A)
    rw [Set.image_insert_eq,Set.image_singleton,gen,← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr onto] at h
    exact h.symm
  obtain ⟨fy,hya,hyb⟩ := noncyclic_character P.isPGroup' (π a) (π b) ncP generated
  obtain ⟨fx,hxb,hxa⟩ := noncyclic_character P.isPGroup' (π b) (π a) (fun h => ncP h.symm)
    (by rwa [Set.pair_comm])
  have ne : i.val ≠ 2 := by
    intro eq
    have dvd := Nat.dvd_of_mem_primeFactors i.property
    exact Nat.not_even_iff_odd.mpr odd (even_iff_two_dvd.mpr (eq ▸ dvd))
  refine ⟨i.val,prime,by have := prime.two_le; omega,(fx.prod fy).comp π,?_,?_⟩
  · exact Prod.ext hxa hya
  · exact Prod.ext hxb hyb

private theorem good_of_commute {A : Type*} [Group A] (a b : A) (sep : a≠1 ∧ b≠1 ∧ a≠b)
    (comm : Commute a b) : Good a b := by
  let p := Equiv.mulRight a
  let q := Equiv.mulRight b
  have separated (x : A) : p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x := by simpa [p,q] using sep
  have squares (x : A) : p (q x) = q (p x) := by
    change x*b*a=x*a*b
    rw [mul_assoc,comm.symm.eq,← mul_assoc]
  have edge (x y : A) (h : y=x ∨ y=x*a ∨ y=x*b) : (graph a b).Adj (false,x) (true,y) :=
    ⟨by simp,.inl ⟨rfl,rfl,h⟩⟩
  rcases OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0 (graph a b) p q
    separated (fun x => edge x x (.inl rfl)) (fun x => edge x _ (.inr (.inl rfl)))
    (fun x => edge x _ (.inr (.inr rfl))) 1 (squares _) (squares _) (squares _) (squares _) with h|h|h
  · exact ⟨2,by decide,h⟩
  · exact ⟨3,by decide,h⟩
  · exact ⟨4,by decide,h⟩

private theorem good_subgroup {A : Type*} [Group A] {H : Subgroup A} (a b : H)
    (h : Good a b) : Good (a:A) (b:A) := by
  let f : (Bool × H) ↪ (Bool × A) :=
    (Function.Embedding.refl Bool).prodMap ⟨Subtype.val,Subtype.coe_injective⟩
  have inc : graph a b ⊑ graph (a:A) (b:A) := by
    apply isContained_iff_exists_le_comap.mpr
    refine ⟨f,?_⟩
    have dir (x y : Bool × H) (u : x.1=false ∧ y.1=true ∧
        (y.2=x.2 ∨ y.2=x.2*a ∨ y.2=x.2*b)) : (f x).1=false ∧ (f y).1=true ∧
        ((f y).2=(f x).2 ∨ (f y).2=(f x).2*(a:A) ∨ (f y).2=(f x).2*(b:A)) := by
      refine ⟨u.1,u.2.1,?_⟩
      rcases u.2.2 with h|h|h
      · exact .inl (congrArg Subtype.val h)
      · exact .inr (.inl (congrArg Subtype.val h))
      · exact .inr (.inr (congrArg Subtype.val h))
    intro x y edge
    refine ⟨fun eq => edge.ne (f.injective eq),?_⟩
    exact edge.2.imp (dir x y) (dir y x)
  obtain ⟨k,hk,cyc⟩ := h
  exact ⟨k,hk,cyc.trans inc⟩

theorem nilpotent_right {A : Type*} [Group A] [Finite A] [Group.IsNilpotent A]
    (odd : Odd (Nat.card A)) (a b : A) (sep : a≠1 ∧ b≠1 ∧ a≠b) : Good a b := by
  classical
  generalize size : Nat.card A = m
  induction m using Nat.strong_induction_on generalizing A with
  | h m ih =>
    have smaller (H : Subgroup A) (proper : H≠⊤) (d e : H) (hd : d≠1) (he : e≠1) (hne : d≠e) :
        Good d e := by
      have lt : Nat.card H < m := by
        rw [←size]
        exact lt_of_le_of_ne H.card_le_card_group (fun eq => proper (H.card_eq_iff_eq_top.mp eq))
      exact ih _ lt (odd.of_dvd_nat H.card_subgroup_dvd_card) d e ⟨hd,he,hne⟩ rfl
    by_cases gen : Subgroup.closure ({a,b} : Set A) = ⊤
    · by_cases comm : Commute a b
      · exact good_of_commute _ _ sep comm
      obtain ⟨p,prime,large,f,fa,fb⟩ := axes_quotient odd a b comm gen
      obtain ⟨s,hs,_,⟨cert⟩⟩ := grid_certificate p prime large
      let _ : NeZero p := ⟨prime.ne_zero⟩
      let _ : Fact p.Prime := ⟨prime⟩
      have nontriv : f a ≠ 1 := by
        rw [fa]; intro eq
        have h : (1 : ZMod p)=0 := congrArg (fun x : Grid (ZMod p) => x.1.toAdd) eq
        exact one_ne_zero h
      have proper : f.ker ≠ ⊤ := fun h => nontriv (show a ∈ f.ker from h ▸ Subgroup.mem_top a)
      apply compress f a b s hs _ (smaller f.ker proper)
      rwa [fa,fb]
    · let H := Subgroup.closure ({a,b} : Set A)
      let d : H := ⟨a,Subgroup.subset_closure (by simp)⟩
      let e : H := ⟨b,Subgroup.subset_closure (by simp)⟩
      exact good_subgroup d e (smaller H gen d e
        (fun h => sep.1 (congrArg Subtype.val h)) (fun h => sep.2.1 (congrArg Subtype.val h))
        (fun h => sep.2.2 (congrArg Subtype.val h)))

theorem nilpotent_left {A : Type*} [Group A] [Finite A] [Group.IsNilpotent A]
    (odd : Odd (Nat.card A)) (a b : A) (sep : a≠1 ∧ b≠1 ∧ a≠b) :
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2)) := by
  let L := SimpleGraph.fromRel (fun u v : Bool × A =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))
  let f : (Bool × A) ↪ (Bool × A) := {
    toFun x := (!x.1,x.2⁻¹)
    inj' := by
      rintro ⟨i,x⟩ ⟨j,y⟩ eq
      exact Prod.ext (by simpa using congrArg Prod.fst eq) (inv_injective (congrArg Prod.snd eq)) }
  have inc : graph a b ⊑ L := by
    apply isContained_iff_exists_le_comap.mpr
    refine ⟨f,?_⟩
    have dir (u v : Bool × A) (h : u.1=false ∧ v.1=true ∧
        (v.2=u.2 ∨ v.2=u.2*a ∨ v.2=u.2*b)) :
        (f v).1=false ∧ (f u).1=true ∧
        ((f u).2=(f v).2 ∨ (f u).2=a*(f v).2 ∨ (f u).2=b*(f v).2) := by
      rcases u with ⟨i,x⟩; rcases v with ⟨j,y⟩
      rcases h with ⟨rfl,rfl,h⟩
      refine ⟨rfl,rfl,?_⟩
      change x⁻¹=y⁻¹ ∨ x⁻¹=a*y⁻¹ ∨ x⁻¹=b*y⁻¹
      dsimp at h
      rcases h with rfl|rfl|rfl <;> simp
    intro x y edge
    refine ⟨fun eq => edge.ne (f.injective eq),?_⟩
    exact edge.2.symm.imp (dir y x) (dir x y)
  obtain ⟨k,hk,cycle⟩ := nilpotent_right odd a b sep
  exact ⟨k,hk,cycle.trans inc⟩

end Erdos64.Theta

theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2_H1_R1.H1 := by
  intro A _ _ a b _ ha hb hab odd _ _ _ _ nil _
  let _ : Group.IsNilpotent A := nil
  exact Erdos64.Theta.nilpotent_left odd a b ⟨ha,hb,hab⟩
