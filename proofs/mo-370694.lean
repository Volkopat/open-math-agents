import OMAStatements.S_mo_370694
import Mathlib.Tactic

/-!
Root gathering in complete binary trees.
Credit: @Chihiro-g

At each height, clear a band of levels into the root and recurse on the
remaining core. Heights through 62 have explicit checked move certificates.
From height 63 onward a uniform construction clears the deepest six levels.
-/

/- The heap labels start at one. Repeatedly halving the larger label
computes the graph distance. Moves internal to a smaller tree lift to an ambient
tree with the frogs from the removed levels already gathered at its root. -/
namespace FrogDistance
open OMA.S_mo_370694

def steps (a b : ℕ) : ℕ :=
  if a = b then 0 else if a < b then steps a (b / 2) + 1 else steps (a / 2) b + 1
termination_by a + b
decreasing_by all_goals omega

@[simp] theorem self (a : ℕ) : steps a a = 0 := by rw [steps]; simp
theorem left {a b : ℕ} (h : b < a) : steps a b = steps (a/2) b + 1 := by
  rw [steps]; simp [Nat.ne_of_gt h, Nat.not_lt_of_ge h.le]
theorem right {a b : ℕ} (h : a < b) : steps a b = steps a (b/2) + 1 := by
  rw [steps]; simp [Nat.ne_of_lt h, h]

theorem lip (a b : ℕ) : steps a b ≤ steps (a/2) b + 1 ∧
    steps (a/2) b ≤ steps a b + 1 := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    rcases lt_trichotomy a b with hlt | he | hgt
    · rw [right hlt, right (show a/2<b by omega)]
      obtain ⟨hl,hr⟩ := ih (b/2) (by omega)
      omega
    · subst b
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [right (show a/2<a by omega), self, self]
        omega
    · rw [left hgt]
      omega

theorem adjLip {h : ℕ} {u v : Vertex h} (ha : (binaryTree h).Adj u v) (a : ℕ) :
    steps (u.val+1) a ≤ steps (v.val+1) a + 1 := by
  change _ ∧ (_ ∨ _) at ha
  rcases ha.2 with hp | hp
  · change (u.val+1)/2 = v.val+1 at hp
    exact hp ▸ (lip (u.val+1) a).1
  · change (v.val+1)/2 = u.val+1 at hp
    exact hp ▸ (lip (v.val+1) a).2

theorem lower {h : ℕ} {u v : Vertex h} (p : (binaryTree h).Walk u v) :
    steps (u.val+1) (v.val+1) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w ha p ih =>
    have := adjLip ha (w.val+1)
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem walk {h : ℕ} (u v : Vertex h) :
    ∃ p : (binaryTree h).Walk u v, p.length = steps (u.val+1) (v.val+1) := by
  rcases lt_trichotomy u.val v.val with hl | he | hg
  · let t : Vertex h := ⟨(v.val+1)/2-1, by have := v.isLt; omega⟩
    have ht : t.val+1=(v.val+1)/2 := by dsimp [t]; omega
    have ha : (binaryTree h).Adj t v := by
      change t ≠ v ∧ (_ ∨ _)
      exact ⟨fun e => by have := congrArg Fin.val e; omega, Or.inr ht.symm⟩
    obtain ⟨p,hp⟩ := walk u t
    refine ⟨p.concat ha,?_⟩
    rw [SimpleGraph.Walk.length_concat,hp,right (by omega : u.val+1<v.val+1),ht]
  · have e : u=v := Fin.ext he
    subst v
    exact ⟨.nil, by simp⟩
  · let t : Vertex h := ⟨(u.val+1)/2-1, by have := u.isLt; omega⟩
    have ht : t.val+1=(u.val+1)/2 := by dsimp [t]; omega
    have ha : (binaryTree h).Adj u t := by
      change u ≠ t ∧ (_ ∨ _)
      exact ⟨fun e => by have := congrArg Fin.val e; omega, Or.inl ht.symm⟩
    obtain ⟨p,hp⟩ := walk t v
    refine ⟨.cons ha p,?_⟩
    rw [SimpleGraph.Walk.length_cons,hp,left (by omega : v.val+1<u.val+1),ht]
termination_by u.val+v.val
decreasing_by all_goals omega

theorem distance {h : ℕ} (u v : Vertex h) :
    (binaryTree h).dist u v = steps (u.val+1) (v.val+1) := by
  obtain ⟨p,hp⟩ := walk u v
  apply Nat.le_antisymm
  · exact hp ▸ SimpleGraph.dist_le p
  · obtain ⟨q,hq⟩ := (show (binaryTree h).Reachable u v from ⟨p⟩).exists_walk_length_eq_dist
    exact hq ▸ lower q
end FrogDistance

namespace FrogCore
open OMA.S_mo_370694
theorem cardMono {k h : ℕ} (hk : k ≤ h) : 2^(k+1)-1 ≤ 2^(h+1)-1 := by
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)) 1

def vertex {k h : ℕ} (hk : k ≤ h) (u : Vertex k) : Vertex h :=
  ⟨u.val, lt_of_lt_of_le u.isLt (cardMono hk)⟩

def state {k h : ℕ} (r : Vertex k) (_hk : k ≤ h) (extra : ℕ)
    (a : Vertex k → ℕ) (v : Vertex h) : ℕ :=
  if hi : v.val < 2^(k+1)-1 then a ⟨v.val,hi⟩ + if v.val=r.val then extra else 0 else 0

theorem atVertex {k h : ℕ} (r : Vertex k) (hk : k ≤ h) (extra : ℕ)
    (a : Vertex k → ℕ) (u : Vertex k) :
    state r hk extra a (vertex hk u) = a u + if u=r then extra else 0 := by
  by_cases e : u=r
  · subst u; simp [state,vertex,r.isLt]
  · have ne : u.val ≠ r.val := fun eq => e (Fin.ext eq)
    simp [state,vertex,u.isLt,e,ne]

theorem liftRun {k h : ℕ} (hk : k ≤ h) (r : Vertex k) (extra : ℕ)
    {a b : Vertex k → ℕ} (run : Relation.ReflTransGen (Move k) a b) (finish : 0<b r) :
    Relation.ReflTransGen (Move h) (state r hk extra a) (state r hk extra b) := by
  induction run with
  | refl => exact .refl
  | @tail b c run step ih =>
    obtain ⟨u,v,huv,hu,hv,hd,hc⟩ := step
    have hru : r ≠ u := by
      intro e
      subst u
      simp [hc] at finish
    have prev : 0 < b r := by
      by_cases hr : r=v
      · simpa [hr] using hv
      · simpa [hc,hru,hr] using finish
    apply (ih prev).tail
    refine ⟨vertex hk u, vertex hk v, fun e => huv (Fin.ext (congrArg (fun z : Vertex h => z.val) e)), ?_, ?_, ?_, ?_⟩
    · rw [atVertex]; omega
    · rw [atVertex]; omega
    · rw [FrogDistance.distance] at hd ⊢
      rw [atVertex, if_neg (Ne.symm hru), Nat.add_zero]
      exact hd
    · funext z
      by_cases hz : z.val < 2^(k+1)-1
      · let t : Vertex k := ⟨z.val,hz⟩
        have e : z = vertex hk t := Fin.ext rfl
        have emb (x y : Vertex k) : vertex hk x = vertex hk y ↔ x=y :=
          ⟨fun he => Fin.ext (congrArg (fun z : Vertex h => z.val) he), fun he => congrArg _ he⟩
        rw [e]
        simp only [atVertex,emb,hc]
        by_cases etu : t=u
        · simp [etu,Ne.symm hru]
        by_cases etv : t=v
        · simp [etv,Ne.symm huv,Ne.symm hru,Nat.add_assoc,Nat.add_comm]
        · simp [etu,etv]
      · have nz (u : Vertex k) : z ≠ vertex hk u := by
          intro e
          exact hz (e ▸ u.isLt)
        simp [state,hz,nz]
end FrogCore
namespace FrogCore
open OMA.S_mo_370694

theorem finish_of_solved {k h : ℕ} (hk : k ≤ h)
    (win : Relation.ReflTransGen (Move k) (fun _ => 1)
      (fun v => if v.val = 0 then 2^(k+1)-1 else 0)) :
    Relation.ReflTransGen (Move h)
      (fun v => if v.val = 0 then 2^(h+1)-2^(k+1)+1
                else if v.val+1 < 2^(k+1) then 1 else 0)
      (fun v => if v.val = 0 then 2^(h+1)-1 else 0) := by
  have hkpow : 1 < 2^(k+1) := by exact one_lt_pow₀ (by decide) (by omega)
  have hle : 2^(k+1) ≤ 2^(h+1) := Nat.pow_le_pow_right (by decide) (by omega)
  let r : Vertex k := ⟨0,by omega⟩
  let E := 2^(h+1)-2^(k+1)
  have run := liftRun hk r E win (by simp [r])
  convert run using 1
  · funext v
    by_cases hr : v.val=0
    · simp [state,r,hr,E,show 0<2^(k+1)-1 by omega,Nat.add_comm]
    · by_cases hi : v.val < 2^(k+1)-1
      · have hi' : v.val+1 < 2^(k+1) := by omega
        simp [state,r,hr,hi,hi']
      · have hi' : ¬v.val+1 < 2^(k+1) := by omega
        simp [state,r,hr,hi,hi']
  · funext v
    by_cases hr : v.val=0
    · simp [state,r,hr,E,show 0<2^(k+1)-1 by omega]
      omega
    · by_cases hi : v.val < 2^(k+1)-1 <;> simp [state,r,hr,hi]
end FrogCore

namespace FrogDistance

theorem symmetric (a b : ℕ) : steps a b = steps b a := by
  rcases lt_trichotomy a b with hab | he | hba
  · rw [right hab, left hab, symmetric a (b/2)]
  · subst b; rfl
  · rw [left hba, right hba, symmetric (a/2) b]
termination_by a+b
decreasing_by all_goals omega

theorem rootDepth (e a : ℕ) (hl : 2^e ≤ a) (hr : a < 2^(e+1)) :
    steps a 1 = e := by
  induction e generalizing a with
  | zero =>
    norm_num at hl hr
    have ea : a=1 := by omega
    subst a; exact self 1
  | succ e ih =>
    rw [pow_succ] at hl hr
    have hp : 0 < 2^e := by positivity
    rw [left (by omega : 1 < a), ih (a/2) (by omega) (by omega)]
end FrogDistance

namespace FrogBatch
open OMA.S_mo_370694
open Finset
variable {h : ℕ} {ι : Type} [DecidableEq ι]

def partialMove (a : Vertex h → ℕ) (src dst : ι → Vertex h) (n : ℕ) (s : Finset ι)
    (v : Vertex h) : ℕ :=
  if v ∈ s.image src then 0 else a v + if v ∈ s.image dst then n else 0

theorem transfer (a : Vertex h → ℕ) (src dst : ι → Vertex h) (n : ℕ)
    (hs : Function.Injective src) (hd : Function.Injective dst)
    (separate : ∀ i j, src i ≠ dst j) (hn : 0<n)
    (source : ∀ i, a (src i)=n) (target : ∀ i, 0<a (dst i))
    (length : ∀ i, (binaryTree h).dist (src i) (dst i)=n) (s : Finset ι) :
    Relation.ReflTransGen (Move h) a (partialMove a src dst n s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : partialMove a src dst n ∅ = a := by funext v; simp [partialMove]
    rw [he]
  | @insert i s hi ih =>
    have ns : src i ∉ s.image src := by simpa [Finset.mem_image,hs.eq_iff] using hi
    have nd : dst i ∉ s.image dst := by simpa [Finset.mem_image,hd.eq_iff] using hi
    have nst : src i ∉ s.image dst := by simp [Finset.mem_image, fun j => Ne.symm (separate i j)]
    have nds : dst i ∉ s.image src := by simp [Finset.mem_image,fun j => separate j i]
    have vs : partialMove a src dst n s (src i)=n := by simp [partialMove,ns,nst,source]
    have vd : partialMove a src dst n s (dst i)=a (dst i) := by simp [partialMove,nds,nd]
    apply ih.tail
    refine ⟨src i,dst i,separate i i,by rwa [vs],by rw [vd]; exact target i,by rw [vs]; exact length i,?_⟩
    funext v
    by_cases hx : v=src i
    · subst v; simp [partialMove]
    by_cases hy : v=dst i
    · subst v; simp [partialMove, hx,nds,nd,ns,nst,source]
    · simp [partialMove,hx,hy]

def partialRoot (a : Vertex h → ℕ) (src : ι → Vertex h) (r : Vertex h)
    (n : ℕ) (s : Finset ι) (v : Vertex h) : ℕ :=
  if v ∈ s.image src then 0 else a v + if v=r then s.card*n else 0

theorem collect (a : Vertex h → ℕ) (src : ι → Vertex h) (r : Vertex h) (n : ℕ)
    (hs : Function.Injective src) (hr : ∀ i, src i ≠ r) (hn : 0<n)
    (source : ∀ i, a (src i)=n) (target : 0<a r)
    (length : ∀ i, (binaryTree h).dist (src i) r=n) (s : Finset ι) :
    Relation.ReflTransGen (Move h) a (partialRoot a src r n s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : partialRoot a src r n ∅ = a := by funext v; simp [partialRoot]
    rw [he]
  | @insert i s hi ih =>
    have ns : src i ∉ s.image src := by simpa [Finset.mem_image,hs.eq_iff] using hi
    have nr : r ∉ s.image src := by simp [Finset.mem_image,hr]
    have vs : partialRoot a src r n s (src i)=n := by simp [partialRoot,ns,hr,source]
    have vd : partialRoot a src r n s r=a r+s.card*n := by simp [partialRoot,nr]
    apply ih.tail
    refine ⟨src i,r,hr i,by rwa [vs],by rw [vd]; omega,by rw [vs]; exact length i,?_⟩
    funext v
    by_cases hx : v=src i
    · subst v; simp [partialRoot]
    by_cases hy : v=r
    · subst v; simp [partialRoot, hx,nr,hi,Nat.add_mul,Nat.add_assoc,hr,source,ns]
    · simp [partialRoot,hx,hy]
end FrogBatch

namespace FrogDistance

/-- Paths meeting just above opposite children of p have length i+j+2. -/
theorem fork (p i j a b : ℕ) (hp : 0<p)
    (ha : (2*p)*2^i ≤ a) (ha' : a < (2*p+1)*2^i)
    (hb : (2*p+1)*2^j ≤ b) (hb' : b < (2*p+2)*2^j) :
    steps a b=i+j+2 := by
  have orderLeft (he : i ≤ j) : a<b :=
    lt_of_lt_of_le ha' ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0<2) he)).trans hb)
  have orderRight (he : j < i) : b<a := by
    have h1 : 2^(j+1) ≤ 2^i := Nat.pow_le_pow_right (by decide) he
    have h2 := Nat.mul_le_mul_left (2*p) h1
    rw [pow_succ] at h2
    have h3 := Nat.mul_le_mul_right (2^j) (by omega : 2*p+2 ≤ 4*p)
    nlinarith
  by_cases he : i ≤ j
  · have hab := orderLeft he
    rw [right hab]
    cases j with
    | zero =>
      have iz : i=0 := by omega
      subst i
      simp only [pow_zero, Nat.mul_one] at *
      have ea : a=2*p := by omega
      have eb : b=2*p+1 := by omega
      subst a; subst b
      rw [show (2*p+1)/2=p by omega, left (by omega : p<2*p), show 2*p/2=p by omega, self]
    | succ j =>
      rw [pow_succ, ← Nat.mul_assoc] at hb hb'
      have shorter := fork p i j a (b/2) hp ha ha' (by omega) (by omega)
      omega
  · have hba := orderRight (by omega)
    rw [left hba]
    cases i with
    | zero => omega
    | succ i =>
      rw [pow_succ, ← Nat.mul_assoc] at ha ha'
      have shorter := fork p i j (a/2) b hp (by omega) (by omega) hb hb'
      omega
termination_by i+j
end FrogDistance
namespace FrogDistance

theorem suffixBound {z d t u : ℕ} (ht : t < 2^z) (hu : u < 2^d) :
    t*2^d+u < 2^(z+d) := by
  rw [pow_add]
  have hm := Nat.mul_le_mul_right (2^d) (show t+1 ≤ 2^z by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  omega

/-- Toggle one prefix bit, keeping all other copy bits. Local descendants may have
different depths and suffixes. This is the geometry used by each cross-copy row. -/
theorem crossCopy (p z t d e u v : ℕ) (hp : 0<p)
    (ht : t<2^z) (hu : u<2^d) (hv : v<2^e) :
    steps (((2*p)*2^z+t)*2^d+u) (((2*p+1)*2^z+t)*2^e+v) =
      (z+d)+(z+e)+2 := by
  have su := suffixBound ht hu
  have sv := suffixBound ht hv
  have first : ((2*p)*2^z+t)*2^d+u = 2*p*2^(z+d)+(t*2^d+u) := by rw [pow_add]; ring
  have last : ((2*p+1)*2^z+t)*2^e+v = (2*p+1)*2^(z+e)+(t*2^e+v) := by rw [pow_add]; ring
  rw [first,last]
  apply fork p (z+d) (z+e) _ _ hp
  · omega
  · rw [Nat.add_mul,Nat.one_mul]; omega
  · omega
  · calc
      _ < (2*p+1)*2^(z+e)+2^(z+e) := Nat.add_lt_add_left sv _
      _ = _ := by ring
end FrogDistance


namespace FrogCertificate
open OMA.S_mo_370694
open Finset
variable {h : ℕ}
abbrev V (h : ℕ) := Vertex h

def load (p : V h → V h) (w : V h → ℕ) (s : Finset (V h)) (v : V h) : ℕ :=
  if v ∈ s then 0 else 1 + ∑ u ∈ s, if p u = v then w u else 0

theorem realize (r : V h) (p : V h → V h) (w : V h → ℕ)
    (balance : ∀ v, w v = 1 + ∑ u ∈ univ.erase r, if p u = v then w u else 0)
    (jump : ∀ v, v ≠ r → (binaryTree h).dist v (p v) = w v)
    (s : Finset (V h)) (nr : r ∉ s)
    (closed : ∀ u, u ≠ r → p u ∈ s → u ∈ s) :
    Relation.ReflTransGen (Move h) (fun _ => 1) (load p w s) := by
  classical
  have grows (u : V h) (hu : u ≠ r) : w u < w (p u) := by
    have hu' : u ∈ univ.erase r := by simpa
    have := Finset.single_le_sum (f := fun a => if p a = p u then w a else 0)
      (fun i _ => Nat.zero_le _) hu'
    simp at this
    have hb := balance (p u)
    omega
  induction s using Finset.strongInductionOn
  rename_i s ih
  rcases s.eq_empty_or_nonempty with he | hs
  · subst s
    have emp : load p w ∅ = fun _ => 1 := by funext x; simp [load]
    rw [emp]
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s w hs
  have hvr : v ≠ r := fun e => nr (e ▸ hv)
  have hd : p v ∉ s := by
    intro hp
    exact (Nat.not_le_of_lt (grows v hvr)) (hmax _ hp)
  have hne : v ≠ p v := by intro e; exact hd (e ▸ hv)
  have her : r ∉ s.erase v := fun hr => nr (mem_of_mem_erase hr)
  have hc : ∀ u, u ≠ r → p u ∈ s.erase v → u ∈ s.erase v := by
    intro u hu hp
    exact mem_erase.mpr ⟨fun he => hd (he ▸ mem_of_mem_erase hp), closed u hu (mem_of_mem_erase hp)⟩
  have prev := ih (s.erase v) (erase_ssubset hv) her hc
  have hsub : s.erase v ⊆ univ.erase r := by
    intro u hu
    exact mem_erase.mpr ⟨fun he => her (he ▸ hu), mem_univ _⟩
  have hsour : load p w (s.erase v) v = w v := by
    rw [load, if_neg (notMem_erase _ _), balance v]
    congr 1
    apply Finset.sum_subset hsub
    intro u hu hn
    split_ifs with he
    · exfalso
      have hur := (mem_erase.mp hu).1
      have hmem := closed u hur (he ▸ hv)
      have huv : u ≠ v := by
        intro eq
        subst u
        exact hne he.symm
      exact hn (mem_erase.mpr ⟨huv,hmem⟩)
    · rfl
  have hpnot : p v ∉ s.erase v := fun hm => hd (mem_of_mem_erase hm)
  apply prev.tail
  refine ⟨v, p v, hne, ?_, ?_, ?_, ?_⟩
  · rw [hsour, balance v]; omega
  · simp [load, hpnot]
  · rw [hsour]; exact jump v hvr
  · funext x
    by_cases ex : x = v
    · subst x; simp [load, hv]
    by_cases ep : x = p v
    · subst x
      simp only [if_neg (Ne.symm hne), hsour]
      unfold load
      rw [if_neg hd, if_neg hpnot, ← insert_erase hv]
      simp [Finset.sum_insert, Nat.add_comm, Nat.add_left_comm]
    · have mem : x ∈ s.erase v ↔ x ∈ s := by simp [ex]
      simp only [if_neg ex, if_neg ep]
      unfold load
      simp only [mem]
      split_ifs
      · rfl
      · congr 1
        conv_lhs => rw [← insert_erase hv]
        simp [Ne.symm ep]

theorem solved_of_certificate (r : V h) (p : V h → V h) (w : V h → ℕ)
    (balance : ∀ v, w v = 1 + ∑ u ∈ univ.erase r, if p u = v then w u else 0)
    (jump : ∀ v, v ≠ r → (binaryTree h).dist v (p v) = w v)
    (total : w r = 2 ^ (h+1) - 1) :
    Relation.ReflTransGen (Move h) (fun _ => 1)
      (fun v => if v = r then 2 ^ (h+1) - 1 else 0) := by
  classical
  have run := realize r p w balance jump (univ.erase r) (notMem_erase _ _)
    (fun u hu _ => mem_erase.mpr ⟨hu,mem_univ _⟩)
  convert run using 1
  funext v
  by_cases hv : v = r
  · subst v
    simpa [load, ← balance] using total.symm
  · simp [load, hv]

end FrogCertificate

namespace FrogExamples

def compute : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, a, b => if a=b then 0 else if a<b then compute n a (b/2)+1 else compute n (a/2) b+1

theorem compute_eq (n a b : ℕ) (hn : a+b ≤ n) :
    compute n a b = FrogDistance.steps a b := by
  induction n generalizing a b with
  | zero =>
    have ha : a=0 := by omega
    have hb : b=0 := by omega
    subst a; subst b; simp [compute]
  | succ n ih =>
    rcases lt_trichotomy a b with hl | he | hg
    · simp only [compute, Nat.ne_of_lt hl, if_false, hl, if_true, FrogDistance.right hl]
      rw [ih _ _ (by omega)]
    · subst b; simp [compute]
    · simp only [compute, Nat.ne_of_gt hg, if_false, Nat.not_lt_of_ge hg.le, FrogDistance.left hg]
      rw [ih _ _ (by omega)]

open OMA.S_mo_370694
open Finset
theorem fromTables {h : ℕ} (r : Vertex h) (p : Vertex h → Vertex h) (w : Vertex h → ℕ)
    (balance : ∀ v, w v = 1 + ∑ u ∈ univ.erase r, if p u = v then w u else 0)
    (jump : ∀ v, v ≠ r → compute (v.val+1+((p v).val+1)) (v.val+1) ((p v).val+1) = w v)
    (total : w r = 2 ^ (h+1) - 1) :
    Relation.ReflTransGen (Move h) (fun _ => 1)
      (fun v => if v = r then 2 ^ (h+1) - 1 else 0) :=
  FrogCertificate.solved_of_certificate r p w balance
    (fun v hv => (FrogDistance.distance v _).trans ((compute_eq _ _ _ (le_refl _)).symm.trans (jump v hv))) total

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem height0 : Relation.ReflTransGen (Move 0) (fun _ => 1)
    (fun v => if v.val = 0 then 1 else 0) := by
  let p : Vertex 0 → Vertex 0 := fun v =>
    ⟨(#[0] : Array ℕ)[v.val]! % 1, Nat.mod_lt _ (by decide)⟩
  let w : Vertex 0 → ℕ := fun v => (#[1] : Array ℕ)[v.val]!
  have run := fromTables (h:=0) (r:=((0 : Fin 1) : Vertex 0)) p w
    (by decide +revert) (by decide +revert) (by decide +revert)
  have root (v : Vertex 0) : v = (0 : Fin 1) ↔ v.val = 0 :=
    ⟨fun e => congrArg Fin.val e, fun e => Fin.ext e⟩
  convert run using 1
  funext v
  by_cases e : v.val=0
  · simp only [if_pos e,if_pos ((root v).mpr e)]
    all_goals decide
  · simp only [if_neg e,if_neg (fun eq => e ((root v).mp eq))]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem height1 : Relation.ReflTransGen (Move 1) (fun _ => 1)
    (fun v => if v.val = 0 then 3 else 0) := by
  let p : Vertex 1 → Vertex 1 := fun v =>
    ⟨(#[0, 0, 0] : Array ℕ)[v.val]! % 3, Nat.mod_lt _ (by decide)⟩
  let w : Vertex 1 → ℕ := fun v => (#[3, 1, 1] : Array ℕ)[v.val]!
  have run := fromTables (h:=1) (r:=((0 : Fin 3) : Vertex 1)) p w
    (by decide +revert) (by decide +revert) (by decide +revert)
  have root (v : Vertex 1) : v = (0 : Fin 3) ↔ v.val = 0 :=
    ⟨fun e => congrArg Fin.val e, fun e => Fin.ext e⟩
  convert run using 1
  funext v
  by_cases e : v.val=0
  · simp only [if_pos e,if_pos ((root v).mpr e)]
    all_goals decide
  · simp only [if_neg e,if_neg (fun eq => e ((root v).mp eq))]

end FrogExamples

/- A local type represents one vertex in each of a family of isomorphic
subtrees. A jump between two distinct types may permute the copies. Injectivity
lets us perform those jumps one at a time without changing the source masses. -/

namespace FrogModel
open OMA.S_mo_370694
open Finset
variable {h : ℕ} {G T : Type} [Fintype G] [DecidableEq T]

structure Frame (h : ℕ) (G T : Type) where
  site : G × T ↪ Vertex h
  root : Vertex h
  avoids : ∀ z, site z ≠ root

noncomputable def paint (F : Frame h G T) (base : Vertex h → ℕ)
    (b : Option T → ℕ) (v : Vertex h) : ℕ := by
  classical
  exact if hv : ∃ z, F.site z = v then b (some hv.choose.2)
    else if v = F.root then base v + Fintype.card G * b none else base v

theorem atSite (F : Frame h G T) (base : Vertex h → ℕ) (b : Option T → ℕ) (g : G) (t : T) :
    paint F base b (F.site (g,t)) = b (some t) := by
  classical
  let hv : ∃ z, F.site z = F.site (g,t) := ⟨_,rfl⟩
  rw [paint, dif_pos hv, F.site.injective hv.choose_spec]

theorem atRoot (F : Frame h G T) (base : Vertex h → ℕ) (b : Option T → ℕ) :
    paint F base b F.root = base F.root + Fintype.card G * b none := by
  classical
  simp [paint, F.avoids]

theorem outside (F : Frame h G T) (base : Vertex h → ℕ) (b : Option T → ℕ)
    (x : Vertex h) (hx : ¬ ∃ z, F.site z=x) (hr : x ≠ F.root) :
    paint F base b x = base x := by classical simp [paint,hx,hr]

def update (b : Option T → ℕ) (i : T) (j : Option T) (t : Option T) : ℕ :=
  if t=some i then 0 else if t=j then b j+b (some i) else b t

theorem imageIff (F : Frame h G T) (p : G ≃ G) (i t : T) (g : G) :
    F.site (g,t) ∈ (univ.image (fun a => F.site (p a,i))) ↔ t=i := by
  classical
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨z,hz⟩
    exact (congrArg Prod.snd (F.site.injective hz)).symm
  · rintro rfl
    exact ⟨p.symm g, by simp⟩

theorem internal (F : Frame h G T) (base : Vertex h → ℕ) (b : Option T → ℕ)
    (i j : T) (ne : i ≠ j) (p : G ≃ G)
    (si : 0<b (some i)) (sj : 0<b (some j))
    (dist : ∀ g, (binaryTree h).dist (F.site (g,i)) (F.site (p g,j)) = b (some i)) :
    Relation.ReflTransGen (Move h) (paint F base b) (paint F base (update b i (some j))) := by
  classical
  have run := FrogBatch.transfer (paint F base b) (fun g => F.site (g,i))
    (fun g => F.site (p g,j)) (b (some i))
    (fun _ _ hd => congrArg Prod.fst (F.site.injective hd))
    (fun _ _ hd => p.injective (congrArg Prod.fst (F.site.injective hd)))
    (fun _ _ hd => ne (congrArg Prod.snd (F.site.injective hd))) si
    (fun _ => atSite ..) (fun _ => by simpa only [atSite] using sj) dist univ
  convert run using 1
  funext x
  by_cases hx : ∃ z, F.site z = x
  · obtain ⟨⟨g,t⟩,rfl⟩ := hx
    have hm := imageIff F (Equiv.refl G) i t g
    simp only [Equiv.refl_apply] at hm
    simp only [FrogBatch.partialMove,hm,imageIff,atSite,update,Option.some.injEq]
    split_ifs <;> simp_all [Nat.add_comm]
  · have miss (f : G → G) (v : T) : x ∉ univ.image (fun a => F.site (f a,v)) := by
      rintro he
      obtain ⟨g,_,hg⟩ := mem_image.mp he
      exact hx ⟨_,hg⟩
    have src := miss id i
    simp only [id_eq] at src
    simp only [FrogBatch.partialMove,if_neg src,if_neg (miss p j),Nat.add_zero]
    by_cases hr : x=F.root
    · subst x; simp [atRoot,update]
    · rw [outside F base _ x hx hr,outside F base _ x hx hr]

theorem toRoot (F : Frame h G T) (base : Vertex h → ℕ) (b : Option T → ℕ) (i : T)
    (si : 0<b (some i)) (sr : 0<base F.root)
    (dist : ∀ g, (binaryTree h).dist (F.site (g,i)) F.root = b (some i)) :
    Relation.ReflTransGen (Move h) (paint F base b) (paint F base (update b i none)) := by
  classical
  have run := FrogBatch.collect (paint F base b) (fun g => F.site (g,i))
    F.root (b (some i)) (fun _ _ hd => congrArg Prod.fst (F.site.injective hd))
    (fun _ => F.avoids _) si (fun _ => atSite ..) (by rw [atRoot]; omega) dist univ
  convert run using 1
  funext x
  by_cases hx : ∃ z, F.site z = x
  · obtain ⟨⟨g,t⟩,rfl⟩ := hx
    have hm := imageIff F (Equiv.refl G) i t g
    simp only [Equiv.refl_apply] at hm
    simp [FrogBatch.partialRoot,hm,F.avoids,atSite,update]
  · have miss : x ∉ univ.image (fun g => F.site (g,i)) := by
      rintro he
      obtain ⟨g,_,hg⟩ := mem_image.mp he
      exact hx ⟨_,hg⟩
    simp only [FrogBatch.partialRoot,if_neg miss,card_univ]
    by_cases hr : x=F.root
    · subst x; simp [atRoot,update,Nat.mul_add,Nat.add_assoc]
    · simp [outside F base _ x hx hr,hr]
end FrogModel


namespace FrogLabels
def width (i : ℕ) := 2^i.log2
def offset (i : ℕ) := i-width i
def label (p i : ℕ) := p*width i+offset i

theorem wpos (i : ℕ) : 0 < width i := by unfold width; positivity
theorem offset_lt {i : ℕ} (hi : 0 < i) : offset i < width i := by
  have hl := Nat.log2_self_le (by omega : i≠0)
  have hu := Nat.lt_log2_self (n:=i)
  rw [pow_succ] at hu
  unfold offset width
  omega

theorem level {b p i : ℕ} (lo : 2^b ≤ p) (up : p < 2^(b+1)) (hi : 0 < i) :
    (label p i).log2 = b+i.log2 := by
  have hw := wpos i
  have ho := offset_lt hi
  have hlo := Nat.mul_le_mul_right (width i) lo
  have hup := Nat.mul_le_mul_right (width i) (show p+1 ≤ 2^(b+1) by omega)
  rw [Nat.add_mul,Nat.one_mul] at hup
  have hp : 0 < 2^b := by positivity
  have hn : 0 < p*width i := Nat.mul_pos (by omega) hw
  apply (Nat.log2_eq_iff (by unfold label; omega)).mpr
  rw [pow_add,show b+i.log2+1=(b+1)+i.log2 by omega,pow_add (2:ℕ) (b+1)]
  change 2^b*width i ≤ p*width i+offset i ∧ p*width i+offset i < 2^(b+1)*width i
  omega

theorem recover {b p q i j : ℕ} (pl : 2^b ≤ p) (pu : p < 2^(b+1))
    (ql : 2^b ≤ q) (qu : q < 2^(b+1)) (hi : 0 < i) (hj : 0<j)
    (he : label p i = label q j) : p=q ∧ i=j := by
  have a := congrArg Nat.log2 he
  rw [level pl pu hi,level ql qu hj] at a
  have hw : width i = width j := by unfold width; rw [show i.log2=j.log2 by omega]
  have d (x n : ℕ) (hn : 0<n) : label x n / width n = x := by
    rw [label,Nat.mul_comm x _,Nat.add_comm, Nat.add_mul_div_left _ _ (wpos n),
      Nat.div_eq_of_lt (offset_lt hn),Nat.zero_add]
  have qeq : p=q := by rw [← d p i hi, he,hw,d q j hj]
  have os : offset i = offset j := by unfold label at he; rw [qeq,hw] at he; omega
  have li := Nat.log2_self_le (by omega : i≠0)
  have lj := Nat.log2_self_le (by omega : j≠0)
  change width i ≤ i at li
  change width j ≤ j at lj
  unfold offset at os
  exact ⟨qeq,by omega⟩

theorem alternate {p i : ℕ} (hp : 0<p) (hi : 0 < i) :
    label p i = (p-1)*width i + i := by
  have w := Nat.log2_self_le (by omega : i≠0)
  change width i ≤ i at w
  have ep : p-1+1=p := by omega
  have a := congrArg (fun n => n*width i) ep
  simp only [Nat.add_mul,Nat.one_mul] at a
  unfold label offset
  omega

theorem ordered {p i j : ℕ} (hp : 0<p) (hi : 0 < i) (hlt : i<j) : label p i < label p j := by
  have hw : width i ≤ width j := Nat.pow_le_pow_right (by decide) ((Nat.le_log2 (by omega : j ≠ 0)).mpr ((Nat.log2_self_le (by omega : i ≠ 0)).trans hlt.le))
  rw [alternate hp hi, alternate hp (by omega)]
  have := Nat.mul_le_mul_left (p-1) hw
  omega

theorem halve {p i : ℕ} (hp : 0<p) (hi : 2 ≤ i) : label p i / 2 = label p (i/2) := by
  have l := Nat.log2_self_le (by omega : i/2≠0)
  have u := Nat.lt_log2_self (n:=i/2)
  have e : i.log2=(i/2).log2+1 := by
    apply (Nat.log2_eq_iff (by omega)).mpr
    rw [pow_succ,pow_succ (2:ℕ) ((i/2).log2+1)]
    omega
  have hw : width i=width (i/2)*2 := by simp [width,e,pow_succ]
  rw [alternate hp (by omega),alternate hp (by omega),hw,← Nat.mul_assoc,
    Nat.add_comm, Nat.add_mul_div_right _ _ (by decide : 0<2),Nat.add_comm]

theorem localDistance (p i j : ℕ) (hp : 0<p) (hi : 0 < i) (hj : 0<j) :
    FrogDistance.steps (label p i) (label p j) = FrogDistance.steps i j := by
  rcases lt_trichotomy i j with hs | he | hg
  · rw [FrogDistance.right (ordered hp hi hs), FrogDistance.right hs, halve hp (by omega),
      localDistance p i (j/2) hp hi (by omega)]
  · subst j; simp
  · rw [FrogDistance.left (ordered hp hj hg), FrogDistance.left hg, halve hp (by omega),
      localDistance p (i/2) j hp (by omega) hj]
termination_by i+j
decreasing_by all_goals omega
end FrogLabels


namespace FrogBand
open OMA.S_mo_370694
open FrogLabels
abbrev Slot (z L : ℕ) := {i : ℕ // 2^z ≤ i ∧ i < 2^(L+1)}
abbrev Groups (b : ℕ) := Fin (2^b)
def pref {b : ℕ} (g : Groups b) : ℕ := 2^b+g.val

theorem prefixBounds {b : ℕ} (g : Groups b) : 2^b ≤ pref g ∧ pref g < 2^(b+1) := by
  have := g.isLt
  simp only [pref,pow_succ]; omega

theorem slotBounds {z L : ℕ} (i : Slot z L) : 0 < i.val ∧ z ≤ i.val.log2 ∧ i.val.log2 ≤ L := by
  obtain ⟨a,d⟩ := i.property
  have hp : 0<2^z := by positivity
  have hi : 0 < i.val := by omega
  exact ⟨hi,(Nat.le_log2 (by omega)).mpr a, by have := (Nat.log2_lt (by omega)).mpr d; omega⟩

theorem bounds {b z L : ℕ} (g : Groups b) (i : Slot z L) :
    2^(b+z) ≤ label (pref g) i.val ∧ label (pref g) i.val < 2^(b+L+1) := by
  obtain ⟨hp,hq⟩ := prefixBounds g
  obtain ⟨hi,hz,hl⟩ := slotBounds i
  have he := level hp hq hi
  have hpos : 0<label (pref g) i.val := by
    have pp : 0<2^b := by positivity
    have hh := Nat.mul_pos (lt_of_lt_of_le pp hp) (wpos i.val)
    unfold label; omega
  exact ⟨(Nat.le_log2 (by omega)).mp (by omega),(Nat.log2_lt (by omega)).mp (by omega)⟩

def root (h : ℕ) : Vertex h := ⟨0,by have : 1 < 2^(h+1) := one_lt_pow₀ (by decide) (by omega); omega⟩

def point {h b z L : ℕ} (bh : b+L≤h) (g : Groups b) (i : Slot z L) : Vertex h :=
  ⟨label (pref g) i.val-1, by
    obtain ⟨lo,up⟩ := bounds g i
    have hp : 0<2^(b+z) := by positivity
    have cap := Nat.pow_le_pow_right (by decide : 0<2) (show b+L+1 ≤ h+1 by omega)
    omega⟩

theorem point_label {h b z L : ℕ} (bh : b+L≤h) (g : Groups b) (i : Slot z L) :
    (point bh g i).val+1=label (pref g) i.val := by
  have lo := (bounds g i).1
  have hp : 0<2^(b+z) := by positivity
  unfold point; dsimp; omega

def frame {h b z L : ℕ} (hb : 0<b) (bh : b+L≤h) : FrogModel.Frame h (Groups b) (Slot z L) where
  site := ⟨fun z => point bh z.1 z.2, by
    rintro ⟨g,i⟩ ⟨g',i'⟩ eq
    have e := congrArg (fun v : Vertex h => v.val+1) eq
    change (point bh g i).val+1=(point bh g' i').val+1 at e
    rw [point_label,point_label] at e
    obtain ⟨pg,ig⟩ := recover (prefixBounds g).1 (prefixBounds g).2 (prefixBounds g').1
      (prefixBounds g').2 (slotBounds i).1 (slotBounds i').1 e
    exact Prod.ext (Fin.ext (Nat.add_left_cancel pg)) (Subtype.ext ig)⟩
  root := root h
  avoids := by
    rintro ⟨g,i⟩ eq
    have hp : 1<2^(b+z) := one_lt_pow₀ (by decide) (by omega)
    have lo := (bounds g i).1
    have e := point_label bh g i
    change point bh g i=root h at eq
    rw [eq] at e
    change 0+1=label (pref g) i.val at e
    omega

theorem represented {h b z L : ℕ} (bh : b+L≤h) (x : Vertex h)
    (lo : 2^(b+z) ≤ x.val+1) (up : x.val+1 < 2^(b+L+1)) :
    ∃ g : Groups b, ∃ i : Slot z L, point bh g i=x := by
  let a := x.val+1
  let d := a.log2-b
  have low : b+z ≤ a.log2 := (Nat.le_log2 (by dsimp [a]; omega)).mpr lo
  have high : a.log2 < b+L+1 := (Nat.log2_lt (by dsimp [a]; omega)).mpr up
  have bd : b+d=a.log2 := by dsimp [d]; omega
  have dl : z ≤ d := by dsimp [d]; omega
  have du : d ≤ L := by dsimp [d]; omega
  let W := 2^d
  have wp : 0<W := by dsimp [W]; positivity
  have alo : 2^b*W ≤ a := by rw [← pow_add,bd]; exact Nat.log2_self_le (by dsimp [a]; omega)
  have ahi : a < 2^(b+1)*W := by
    change a < 2^(b+1)*2^d
    rw [← pow_add,show b+1+d=a.log2+1 by omega]
    exact Nat.lt_log2_self
  let p := a/W
  have pl : 2^b ≤ p := (Nat.le_div_iff_mul_le wp).mpr alo
  have pu : p < 2^(b+1) := (Nat.div_lt_iff_lt_mul wp).mpr ahi
  let g : Groups b := ⟨p-2^b,by rw [pow_succ] at pu; omega⟩
  have pg : pref g=p := by simp only [pref,g]; omega
  let u := W+a%W
  have rem := Nat.mod_lt a wp
  have ul : u.log2=d := (Nat.log2_eq_iff (by dsimp [u]; omega)).mpr (by
    change W ≤ W+a%W ∧ W+a%W < 2^(d+1)
    rw [pow_succ]; change _ ∧ _ < W*2; omega)
  let i : Slot z L := ⟨u,(Nat.le_log2 (by dsimp [u]; omega)).mp (by omega),
    (Nat.log2_lt (by dsimp [u]; omega)).mp (by omega)⟩
  refine ⟨g,i,Fin.ext ?_⟩
  have w : width u=W := by simp [width,ul,W]
  have eql : label (pref g) i.val=a := by
    change pref g * width u + (u-width u) = a
    rw [pg,w]
    have div := Nat.div_add_mod a W
    change p*W + (W+a%W-W)=a
    simpa [p,Nat.mul_comm] using div
  have finish := point_label bh g i
  change (point bh g i).val=x.val
  dsimp [a] at eql; omega
end FrogBand

/- Two labels in different copies meet above the first differing
prefix bit. Switching that bit realizes any length of the right parity between
the two bounds in Cross. -/
namespace FrogBand
open OMA.S_mo_370694 FrogLabels
def join (a r b : ℕ) (eb : b=a+1+r) : (Groups a × (Fin 2 × Groups r)) ≃ Groups b :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by rw [eb,pow_add,pow_succ]; ring))

theorem join_pref {a r b : ℕ} (eb : b=a+1+r) (c : Groups a) (j : Fin 2) (t : Groups r) :
    pref (join a r b eb (c,j,t)) = (2*pref c+j.val)*2^r+t.val := by
  change 2^b + (t.val + 2^r*j.val + (2*2^r)*c.val) =
    (2*(2^a+c.val)+j.val)*2^r+t.val
  rw [eb,pow_add,pow_succ]; ring

def flipped (a r b : ℕ) (eb : b=a+1+r) : Groups b ≃ Groups b :=
  ((join a r b eb).symm.trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl _)))).trans (join a r b eb)

theorem flip_apply {a r b : ℕ} (eb : b=a+1+r) (c : Groups a) (j : Fin 2) (t : Groups r) :
    flipped a r b eb (join a r b eb (c,j,t)) =
      join a r b eb (c,Equiv.swap (0 : Fin 2) 1 j,t) := by simp [flipped]

theorem across {a r b : ℕ} (eb : b=a+1+r) (g : Groups b) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    FrogDistance.steps (label (pref g) i) (label (pref (flipped a r b eb g)) j) =
      (r+i.log2)+(r+j.log2)+2 := by
  obtain ⟨⟨c,f,t⟩,rfl⟩ := (join a r b eb).surjective g
  rw [flip_apply,join_pref,join_pref]
  have hp : 0<pref c := Nat.lt_of_lt_of_le (by positivity : 0<2^a) (prefixBounds c).1
  fin_cases f
  · simp only [Equiv.swap_apply_left,Fin.val_zero,Fin.val_one,Nat.add_zero]
    exact FrogDistance.crossCopy (pref c) r t.val i.log2 j.log2 (offset i) (offset j) hp t.isLt
      (offset_lt hi) (offset_lt hj)
  · simp only [Equiv.swap_apply_right,Fin.val_zero,Fin.val_one,Nat.add_zero]
    rw [FrogDistance.symmetric, Nat.add_comm (r+i.log2) (r+j.log2)]
    exact FrogDistance.crossCopy (pref c) r t.val j.log2 i.log2 (offset j) (offset i) hp t.isLt
      (offset_lt hj) (offset_lt hi)

def Cross (b i j w : ℕ) : Prop :=
  let n := i.log2+j.log2+2
  n ≤ w ∧ (w-n)%2 = 0 ∧ (w-n)/2 < b

theorem matchDistance {b i j w : ℕ} (hi : 0 < i) (hj : 0 < j)
    (ok : FrogDistance.steps i j=w ∨ Cross b i j w) :
    ∃ e : Groups b ≃ Groups b, ∀ g, FrogDistance.steps
      (label (pref g) i) (label (pref (e g)) j) = w := by
  rcases ok with he | hc
  · refine ⟨Equiv.refl _,fun g => ?_⟩
    exact (localDistance _ i j (Nat.lt_of_lt_of_le (by positivity : 0<2^b)
      (prefixBounds g).1) hi hj).trans he
  · obtain ⟨hle,heven,hr⟩ := hc
    let r := (w-(i.log2+j.log2+2))/2
    let a := b-1-r
    have hb : b=a+1+r := by dsimp [a,r]; omega
    refine ⟨flipped a r b hb,fun g => ?_⟩
    rw [across hb g i j hi hj]
    dsimp [r]
    omega

theorem rootLength {h b z L : ℕ} (bh : b+L≤h) (g : Groups b) (i : Slot z L) :
    (binaryTree h).dist (point bh g i) (root h) = b+i.val.log2 := by
  rw [FrogDistance.distance,point_label]
  change FrogDistance.steps (label (pref g) i.val) 1 = _
  have he := level (prefixBounds g).1 (prefixBounds g).2 (slotBounds i).1
  have pp : 0 < label (pref g) i.val := by
    have := (bounds g i).1
    have : 0<2^(b+z) := by positivity
    omega
  apply FrogDistance.rootDepth
  · exact (Nat.le_log2 (by omega)).mp he.ge
  · exact (Nat.log2_lt (by omega)).mp (by omega)
end FrogBand

/- The bounded cases use a sparse binary table of masses. Entry zero
counts the mass sent to the common root per copy. Every other active entry
represents one local heap label. The checker tests positivity, distance and
the final mass at every active entry. -/
namespace FrogCheck

inductive Table where
  | uniform (n : ℕ)
  | branch (left right : Table)

def Table.read (t : Table) (i : ℕ) : ℕ :=
  match t with
  | .uniform n => n
  | .branch l r => if i%2=0 then l.read (i/2) else r.read (i/2)

def Table.putAux : ℕ → Table → ℕ → ℕ → Table
  | 0, _, _, n => .uniform n
  | d+1, t, i, n =>
    let l := match t with | .uniform k => .uniform k | .branch a _ => a
    let r := match t with | .uniform k => .uniform k | .branch _ a => a
    if i%2=0 then .branch (putAux d l (i/2) n) r
    else .branch l (putAux d r (i/2) n)

theorem read_put (d : ℕ) (t : Table) (i j n : ℕ) (hi : i < 2^d) (hj : j < 2^d) :
    (Table.putAux d t i n).read j = if j=i then n else t.read j := by
  induction d generalizing t i j with
  | zero =>
    have e : j=i := by simp at hi hj; omega
    simp [Table.putAux,Table.read,e]
  | succ d ih =>
    rw [pow_succ] at hi hj
    have hi' : i/2 < 2^d := by omega
    have hj' : j/2 < 2^d := by omega
    by_cases pi : i%2=0 <;> by_cases pj : j%2=0 <;> cases t <;>
      simp [Table.putAux,Table.read,pi,pj,ih _ _ _ hi' hj'] <;> (try split_ifs) <;> first | rfl | omega

def heapDist : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n+1, a, b => if a=b then 0 else if a<b then heapDist n a (b/2)+1 else heapDist n (a/2) b+1

def legal (b z L : ℕ) (t : Table) (i j : ℕ) : Bool :=
  let n := t.read i
  let k := i.log2+j.log2+2
  decide (2^z ≤ i ∧ i<2^(L+1) ∧ 0<n ∧
    (if j=0 then n=b+i.log2 else
      2^z ≤ j ∧ j<2^(L+1) ∧ i≠j ∧ 0<t.read j ∧
      (heapDist (i+j) i j = n ∨ (k ≤ n ∧ (n-k)%2=0 ∧ (n-k)/2<b))))

def move (L : ℕ) (t : Table) (i j : ℕ) : Table :=
  Table.putAux (L+1) (Table.putAux (L+1) t i 0) j (t.read j+t.read i)

def start (L : ℕ) := Table.putAux (L+1) (.uniform 1) 0 0

def run (b z L : ℕ) : List (ℕ × ℕ) → Table → Option Table
  | [], t => some t
  | (i,j)::rows, t => if legal b z L t i j then run b z L rows (move L t i j) else none

def finished (z L : ℕ) (t : Table) : Bool :=
  let n := 2^(L+1)-2^z
  t.read 0 == n && (List.range n).all fun k => t.read (2^z+k) == 0

def check (b z L : ℕ) (rows : List (ℕ × ℕ)) : Bool :=
  match run b z L rows (start L) with
  | some t => finished z L t
  | none => false
end FrogCheck


namespace FrogBand
open OMA.S_mo_370694 FrogCheck FrogModel
def key {z L : ℕ} : Option (Slot z L) → ℕ
  | none => 0
  | some i => i.val

theorem keyInj {z L : ℕ} : Function.Injective (@key z L) := by
  intro x y e
  cases x <;> cases y <;> simp only [key] at e
  · rfl
  · rename_i j; have := (slotBounds j).1; omega
  · rename_i j; have := (slotBounds j).1; omega
  · exact congrArg some (Subtype.ext e)

theorem keyLt {z L : ℕ} (i : Option (Slot z L)) : key i < 2^(L+1) := by
  cases i with
  | none => exact Nat.two_pow_pos _
  | some i => exact i.property.2

def view {z L : ℕ} (t : Table) (i : Option (Slot z L)) := t.read (key i)

theorem viewMove {z L : ℕ} (t : Table) (i : Slot z L) (j : Option (Slot z L)) (hne : some i ≠ j) :
    view (move L t i.val (key j)) = update (view t) i j := by
  funext x
  simp only [view,move,read_put _ _ _ _ _ (keyLt j) (keyLt x),
    read_put _ _ _ _ _ i.property.2 (keyLt x),update,keyInj.eq_iff]
  have hx : key x = i.val ↔ x=some i := @Function.Injective.eq_iff _ _ _ (keyInj (z:=z) (L:=L)) x (some i)
  split_ifs <;> simp_all [view,key] <;> omega

theorem calc_eq (n i j : ℕ) (hl : i+j ≤ n) : heapDist n i j = FrogDistance.steps i j := by
  induction n generalizing i j with
  | zero =>
    have hi : i=0 := by omega
    have hj : j=0 := by omega
    subst i; subst j; simp [heapDist]
  | succ n ih =>
    rcases lt_trichotomy i j with hlt | he | hgt
    · simp only [heapDist,Nat.ne_of_lt hlt,if_false,hlt,if_true,FrogDistance.right hlt]
      rw [ih _ _ (by omega)]
    · subst j; simp [heapDist]
    · simp only [heapDist,Nat.ne_of_gt hgt,if_false,Nat.not_lt_of_ge hgt.le,FrogDistance.left hgt]
      rw [ih _ _ (by omega)]

theorem one {h b z L : ℕ} (hb : 0<b) (bh : b+L≤h) (base : Vertex h → ℕ)
    (hr : 0<base (root h)) (t : Table) (i j : ℕ) (hl : legal b z L t i j=true) :
    let F := frame (z:=z) hb bh
    Relation.ReflTransGen (Move h) (paint F base (view t)) (paint F base (view (move L t i j))) := by
  simp only [legal,decide_eq_true_eq] at hl
  obtain ⟨hil,hiu,hs,hl⟩ := hl
  let I : Slot z L := ⟨i,hil,hiu⟩
  let F := frame (z:=z) hb bh
  change Relation.ReflTransGen _ (paint F base (view t)) _
  by_cases zero : j=0
  · subst j
    simp only [if_pos rfl] at hl
    have hu := viewMove t I none (by simp)
    change view (move L t i 0) = update (view t) I none at hu
    rw [hu]
    apply toRoot F base (view t) I hs hr
    intro g
    exact (rootLength bh g I).trans hl.symm
  · simp only [if_neg zero] at hl
    obtain ⟨hjl,hju,hne,ht,hroute⟩ := hl
    let J : Slot z L := ⟨j,hjl,hju⟩
    have ne : I≠J := fun e => hne (congrArg Subtype.val e)
    have hu := viewMove t I (some J) (by simpa using ne)
    change view (move L t i j) = update (view t) I (some J) at hu
    rw [hu]
    rw [calc_eq _ _ _ (by omega)] at hroute
    obtain ⟨perm,dist⟩ := matchDistance (slotBounds I).1 (slotBounds J).1 hroute
    apply internal F base (view t) I J ne perm hs ht
    intro g
    change (binaryTree h).dist (point bh g I) (point bh (perm g) J) = _
    rw [FrogDistance.distance,point_label,point_label]
    exact dist g

theorem many {h b z L : ℕ} (hb : 0<b) (bh : b+L≤h) (base : Vertex h → ℕ)
    (hr : 0<base (root h)) (rows : List (ℕ×ℕ)) (t t' : Table)
    (he : run b z L rows t=some t') : let F := frame (z:=z) hb bh
    Relation.ReflTransGen (Move h) (paint F base (view t)) (paint F base (view t')) := by
  induction rows generalizing t with
  | nil => simp only [run,Option.some.injEq] at he; subst t'; exact .refl
  | cons xy rest ih =>
    obtain ⟨i,j⟩ := xy
    rw [run] at he
    split at he
    next hl => exact (one hb bh base hr t i j hl).trans (ih _ he)
    next => contradiction

def core (h k : ℕ) (v : Vertex h) := if v.val=0 then 2^(h+1)-2^(k+1)+1
  else if v.val+1<2^(k+1) then 1 else 0

theorem beginBand {h b z L : ℕ} (hb : 0<b) (bh : b+L≤h) :
    let F := frame (z:=z) hb bh
    paint F (core h (b+L)) (view (start L)) = core h (b+L) := by
  let F := frame (z:=z) hb bh
  funext v
  by_cases hv : ∃ q, F.site q=v
  · rcases hv with ⟨⟨g,i⟩,rfl⟩
    rw [atSite]
    have hn : (point bh g i).val≠0 := fun e => F.avoids (g,i) (Fin.ext e)
    have hu := (bounds g i).2
    have hlab := point_label bh g i
    change (start L).read i.val = core h (b+L) (point bh g i)
    rw [core,if_neg hn,if_pos (by omega)]
    simp [start,read_put _ _ _ _ _ (Nat.two_pow_pos _) i.property.2, (slotBounds i).1.ne',Table.read]
  · by_cases eq : v=F.root
    · subst v; rw [atRoot]
      simp [view,key,start,read_put _ _ _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _),F]
    · exact outside F _ _ v hv eq

theorem endBand {h b z L : ℕ} (hb : 0<b) (bh : b+L≤h) (zl : z≤L)
    (t : Table) (hf : finished z L t=true) : let F := frame (z:=z) hb bh
    paint F (core h (b+L)) (view t) = core h (b+z-1) := by
  let F := frame (z:=z) hb bh
  simp only [finished,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range] at hf
  obtain ⟨amount,empty⟩ := hf
  have sub : b+z-1+1=b+z := by omega
  have mul : 2^b*(2^(L+1)-2^z)=2^(b+L+1)-2^(b+z) := by
    rw [Nat.mul_sub,←pow_add,←pow_add, Nat.add_assoc]
  have lh := Nat.pow_le_pow_right (by decide : 0<2) (show b+L+1≤h+1 by omega)
  have zh := Nat.pow_le_pow_right (by decide : 0<2) (show b+z≤b+L+1 by omega)
  funext v
  by_cases hv : ∃ q, F.site q=v
  · rcases hv with ⟨⟨g,i⟩,rfl⟩
    rw [atSite]
    have e := empty (i.val-2^z) (by have := i.property; omega)
    rw [show 2^z+(i.val-2^z)=i.val by have := i.property.1; omega] at e
    have hn : (point bh g i).val≠0 := fun eq => F.avoids (g,i) (Fin.ext eq)
    have bl := (bounds g i).1
    have hlab := point_label bh g i
    change t.read i.val = core h (b+z-1) (point bh g i)
    simpa [core,hn,sub,hlab,Nat.not_lt_of_ge bl] using e
  · by_cases eq : v=F.root
    · subst v; rw [atRoot]
      change core h (b+L) (root h) + Fintype.card (Groups b)*t.read 0 = core h (b+z-1) (root h)
      simp only [core,root,if_true,Fintype.card_fin,amount,sub,mul]
      omega
    · rw [outside F _ _ v hv eq]
      have hn : v.val≠0 := fun e => eq (Fin.ext e)
      simp only [core,if_neg hn,sub]
      split_ifs <;> try rfl
      · exfalso
        obtain ⟨g,i,hi⟩ := represented (z:=z) bh v (by omega) (by assumption)
        exact hv ⟨(g,i),hi⟩
      · omega

theorem verified {h b z L : ℕ} (hb : 0<b) (bh : b+L≤h) (zl : z≤L) (rows : List (ℕ×ℕ))
    (hc : check b z L rows=true) :
    Relation.ReflTransGen (Move h) (core h (b+L)) (core h (b+z-1)) := by
  unfold check at hc
  cases he : run b z L rows (start L) with
  | none => simp [he] at hc
  | some t =>
    simp only [he] at hc
    have run := many (z:=z) hb bh (core h (b+L)) (by simp [core,root]) rows _ t he
    dsimp only at run
    rwa [beginBand (z:=z) hb bh,endBand hb bh zl t hc] at run
end FrogBand

/- The finite witnesses pack groups of at most 32 commands into
natural numbers. The upper sentinel marks the end, the low three bits select a
move, and the next bit reuses the previous destination as the source. Commands
6 and 7 expand the two-move gathers on a cherry. Only the expanded and checked
list of legal moves is used in the proof. -/
namespace FrogCheck
def unpack (bits : ℕ) : ℕ → ℕ → ℕ → List (ℕ×ℕ)
  | 0, _, _ => []
  | fuel+1, word, previous =>
    if word=1 then [] else
    let op := word%8
    let rest := word/16
    let reused := (word/8)%2=1
    let i := if reused then previous else rest%2^bits
    let next := if reused then rest else rest/2^bits
    if op=6 then (2*i,i)::(2*i+1,i)::unpack bits fuel next i
    else if op=7 then (i,2*i+1)::(2*i+1,2*i)::unpack bits fuel next (2*i)
    else
      let j := match op with
        | 0 => 0 | 1 => i/2 | 2 => 2*i | 3 => 2*i+1
        | 4 => if i%2=0 then i+1 else i-1
        | _ => next%2^bits
      (i,j)::unpack bits fuel (if op=5 then next/2^bits else next) j

def rows (L : ℕ) (chunks : List ℕ) : List (ℕ×ℕ) :=
  chunks.flatMap (fun w => unpack (L+1) 32 w 0)
end FrogCheck

namespace FrogFinite
def data3 : List ℕ := [0x617]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked3 : FrogCheck.check 2 0 1 (FrogCheck.rows 1 data3) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data4 : List ℕ := [0x623540da892]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked4 : FrogCheck.check 2 0 2 (FrogCheck.rows 2 data4) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data5 : List ℕ := [0x1c09080ce58b5e65955bd1df1d1a1433223]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked5 : FrogCheck.check 2 0 3 (FrogCheck.rows 3 data5) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data6 : List ℕ := [0x188d53b6]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked6 : FrogCheck.check 4 1 2 (FrogCheck.rows 2 data6) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data7 : List ℕ := [0x18715b27]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked7 : FrogCheck.check 5 1 2 (FrogCheck.rows 2 data7) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data8 : List ℕ := [0x313365b51]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked8 : FrogCheck.check 6 0 2 (FrogCheck.rows 2 data8) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data9 : List ℕ := [0x18ac557818516c75674776]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked9 : FrogCheck.check 6 0 3 (FrogCheck.rows 3 data9) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data10 : List ℕ := [0x12010341c51b5275345d4a476466352]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked10 : FrogCheck.check 7 0 3 (FrogCheck.rows 3 data10) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data11 : List ℕ := [0xc4221f58ad60965fd15795b316825cf159d5e797a1515545250b57c359a54aad6c0dc5e6e250a4d0636]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked11 : FrogCheck.check 7 0 4 (FrogCheck.rows 4 data11) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data12 : List ℕ := [0x18a4557475467c57667]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked12 : FrogCheck.check 9 2 3 (FrogCheck.rows 3 data12) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data13 : List ℕ := [0x186e566e85778554756]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked13 : FrogCheck.check 10 2 3 (FrogCheck.rows 3 data13) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data14 : List ℕ := [0x188ddd4dc2758556476c15691]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked14 : FrogCheck.check 11 1 3 (FrogCheck.rows 3 data14) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data15 : List ℕ := [0x18a25574117475467c57667]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked15 : FrogCheck.check 12 0 3 (FrogCheck.rows 3 data15) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data16 : List ℕ := [0x1854465e556e25772651766]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked16 : FrogCheck.check 13 0 3 (FrogCheck.rows 3 data16) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data17 : List ℕ := [0x182851785547575567c57667]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked17 : FrogCheck.check 14 0 3 (FrogCheck.rows 3 data17) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data18 : List ℕ := [0x18145164a546ac557c756776]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked18 : FrogCheck.check 15 0 3 (FrogCheck.rows 3 data18) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data19 : List ℕ := [0x110c8132a06063141b3d04af58525514ccdaab3619814630224a099ffc57ecd742b565c595732590a95934e54ccc1d23be716ed1c4ba77, 0x152dd0e2ba7ac6955bc6c8a8dcf5e51ef4312a87b5b956bd4ecaa9cd0351ae70428e7dce15bbe414ac9f13d562fd99abb7bc8157bb87eae1842e5, 0x1879415e342c8cab1a1b5656cd086d2a1684479513439a8ae5a14f45]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked19 : FrogCheck.check 13 1 6 (FrogCheck.rows 6 data19) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data20 : List ℕ := [0x140f5a92ab7d8615b3eed0addff7a57ef6022ac7d0d55a3d250aa5f233564f1912a37f4f15eb9806a31c221504e8581b3c66accd943226, 0x11cebdcaaf674e15d32e48ab996aa55aced8abb64ef953b264aa999256548cc7f2b1655015533ed8af99ce0572c96c2a5671b95c360c8ac1e0465, 0x182899453c165ea2de0d3a51af0413a887824ed44bc1e5ca3de0e2d5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked20 : FrogCheck.check 14 1 6 (FrogCheck.rows 6 data20) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data21 : List ℕ := [0x1c06561c6414668d8a56dca11457112511b8df35f679f8d759c74354d55d46435174192d5b5775992d4dd26, 0x607c9476cb8565e34c15a7]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked21 : FrogCheck.check 16 2 5 (FrogCheck.rows 5 data21) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data22 : List ℕ := [0x14192e9526562555bae15d7232511e2b9517b9f55df8195c7c81565c6594667db57d81794166f456d9e395e658a5599a71dc57, 0x184d554da18495868510551882]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked22 : FrogCheck.check 17 0 5 (FrogCheck.rows 5 data22) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data23 : List ℕ := [0x141ea69557c92565d87d58669356992455264f654d9fa15f6442545b6395b7a2e551c2e941739e51dee59577e9c575d66719e6, 0x60aa94578320519e08c94478185]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked23 : FrogCheck.check 18 0 5 (FrogCheck.rows 5 data23) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data24 : List ℕ := [0x63c755e7711d6736571b6815b78f9a57dda655a6670565b0a15878364d4d9278351641e8db357659e8d55947]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked24 : FrogCheck.check 19 4 5 (FrogCheck.rows 5 data24) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data25 : List ℕ := [0x187ba579bae15d7e1b571db415b687f457db4c95a7c98565d8495864354d55d46435174192d5b5775992d4dd26]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked25 : FrogCheck.check 20 4 5 (FrogCheck.rows 5 data25) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data26 : List ℕ := [0xb8790b5523984ca31f109562ecdaab365aa156b2646a99962a558c257289655595532388a8d9452550cd742b565d795732f752eadda3a27, 0x172cf5dabd61ce94733078ac19032540cf252bc67f095fb32dcac99d6c574cefe2bb6958952bfc9caf9e170542fb242b67dc615bbce58a9df8335, 0x182881453c1060a21e1e88f782c3945bc1a72a35dcbf5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked26 : FrogCheck.check 20 3 6 (FrogCheck.rows 6 data26) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data27 : List ℕ := [0xbc671995c327bca9d959e556d9b02b378909513deb0abdc946512e7ba28f7848150bc610a8df031560f616aac7e8ed5d388640cb598b3b6, 0x150f9352b2791a1523fcd8af9e57a54af31caa67f4dd5ebe852ad1f63f56cfa972b57529d54b3770add972b55cce5e2b967ea95fb2a88aa99e125, 0xc0aa0a29a076451cd033e28c681b2146b40b94a2da84c5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked27 : FrogCheck.check 21 3 6 (FrogCheck.rows 6 data27) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data28 : List ℕ := [0x1721e57269248549732675197c66256377f3e57f6ae5655771ef051e6108451061ad651a6f67a57b7b21655977a66b71f7626676566166787427486, 0x15ca855c671f25716de1d56f7d266569711b65116fc7257e775365756c2c656171d7f51d6949254a7f2f65797661a5666b6b255b7a8ae5547363251b714105146, 0x1602a5606ee4d5777307c51874d6e54d6a68a55377c4457c626de51376a5c56a64f7554f624fc5127417154166c1156c62ad251576ec256e68a14545744945446, 0x1747aa3055576d4356d6a2ba5517801475016b0ca55874c6854c6ecfa57670460504647245476fa6a57d768265686ba4155d743a65436ca4f56578c6c5467, 0x15017550684e1c54e68705e57064baa54b680c4c506752c8552617e8517680a0450571cb051c680e6d50775eec55e640a25406c8ee5647e88c5, 0x187352573685a4b55a685f4055f6500]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked28 : FrogCheck.check 21 0 7 (FrogCheck.rows 7 data28) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data29 : List ℕ := [0x5d8c3bee28ed9494a552337770add617de145ec165ba82ddf9fa57e3371d78e906133a19d34ec3752ba15ddced3776bbf5d1ec8b767badd940ea27, 0x150b3219cac86588bd562cfb7e2bed94744551b4711ea8e742429508c2726289d86186518334b4cad2614501450d22482a45d373454db21e18a87645459514ccecf2b399d9da5, 0x154ba0508a81608471410e8d452a35a49225493a0d0ea8366d3755b4ce31dab8d9d6ec575b29946aa66578a155ec9e4daa79af41655ebb5da4ad764a89d52acc9182b25942a45, 0x10739193ca237a72bd54eeb5bd2ad58f8eb51f3861f6a0c78c205518e5658a8adc6a1051ab4011aa8078820d510e9d922a75ba4e3574be2192ac470f35d41efa26d2b45ea4a65, 0x166b96a20a2d749ad5526d302b2a61e09385413df830abf75d275574d7c232af9f187c5633da038ab47fa7495f4f2e802a5dd5c3555735b2a4ab679c255538f5850aab1c38c85, 0x168338accae26546d9550ce4982b919ed7657b327f18a9f6664b9598c20be28819977e565b2e334ab866c9695b2d720f2ae5f6d8856dbd9ab0ab37bb539576f2c8c2a59f35a25, 0x14a339596ae567aa7d5eacd6712b59ac98a5593b7d56adf67c3415f0dc0e82b81de304578b74174ae8770da15c2de4572bc9d57f4555b32a58aca67fdb15fed8a49ab15da1725, 0x1053569fcaad7f73015eefe01c2bc1f04d5560bbe598af966a2a15a8cd8722b61ba9e45753a65eca9961b38546ccfe102bf9980ff56030fdb2a3f61c2e1470cd578ab55928ca5, 0x1de2655bcf606b2ac1fbcdf577bf307eae67f33e55e6e6272a8c5fd0f857a3c49b0a897804f51412d546a2aa9f08945613f39eaae77c70d958ef00db22835a015c05, 0x252c128a5e0e96051d3c12bdca257821639442f058f028b1e088625113c193cca32782e77945cf068c228d1e0a9bc5153c19a24a337, 0x1839551472f06ee628dde0f5e851ebc122b4a24783c739478e520]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked29 : FrogCheck.check 21 3 8 (FrogCheck.rows 8 data29) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data30 : List ℕ := [0x537911549d1615168b9055dd01d5061cc51d8c29467284515c469446635cd75dc663597619ad7b5f7799ad6dda6, 0x18b15559d445594995469a45]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked30 : FrogCheck.check 25 2 5 (FrogCheck.rows 5 data30) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data31 : List ℕ := [0x5364a2549a2c151785e055da03950738651dc61546614851588e1447c374d6d9a7c359661f8df35f679f8d759c7, 0x185aa559aaa1557a13551d24]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked31 : FrogCheck.check 26 2 5 (FrogCheck.rows 5 data31) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data32 : List ℕ := [0x557a13551d361536839251dd245526460545a029507284515c469446635cd75dc663597619ad7b5f7799ad6dda6, 0x18317519d645d96a9566aa85]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked32 : FrogCheck.check 27 2 5 (FrogCheck.rows 5 data32) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data33 : List ℕ := [0x556526551a6c153781e451da489527890545d01550614851588e1447c374d6d9a7c359661f8df35f679f8d759c7, 0x181ae519aeb1577b15559d44]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked33 : FrogCheck.check 28 2 5 (FrogCheck.rows 5 data33) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data34 : List ℕ := [0x53749a549a1d455d6460545a03950738651dc61546614851588a14476b5ed7dde66b5b769a8db357659e8d55947, 0x1809c505dc655c6670565b0995879925]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked34 : FrogCheck.check 29 0 5 (FrogCheck.rows 5 data34) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data35 : List ℕ := [0x161aae155783a851de8455474111640c5418c29467284515c449446e37cd7d9e7e35d671d2d5b5775992d4dd26, 0x601d9416db456df4655a76119662a5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked35 : FrogCheck.check 30 0 5 (FrogCheck.rows 5 data35) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data36 : List ℕ := [0x147653575536181f5186444254465550555670745706418054161ad651a64286542674ea57461ffc51f650a25506572a55764077e71574375177576b7, 0x16963a9051d7fed457f79cba54e728f05147ec265767c2f25617b09655879047548726535137d41e56a7f0185787ba5555d7f2705797964454b71e1a51e647415, 0x16c7f84a57c7b87b55c7526555264d44c67d6957d67b5457b64a4654a61149511645675456679c567654b05546493a54964d2854d665fe565646c2546669ec5, 0x14f656c055665aee55a664c6564659e25596bc3655e7c02c5607b6f855b7e2b85717eec45777e4d85727c6d056372c4c5167365251b7d0455687c4115627d87d5, 0x18f46e57a78cc6f56678be1255f781c5a51c68105951066f6d56f66e7356e68194f51968175651761264512673bc57366db656d64fe45]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked36 : FrogCheck.check 29 4 7 (FrogCheck.rows 7 data36) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data37 : List ℕ := [0x10573cf851e724985127940854a7d63656b7c4c25627984d54c7bc5f55e7f87d57c7366e51b73218519708445047c26056174d65f66e66067d6446186, 0x16777e4357e6761c5766071d50764265542606645066147b5146175751761d0a51d6439454367b3457b664d65646653c5656572455761cc451c6343251a70abc5, 0x1496588a55866dd456d622ce51172c8c5167a22a55178a8e5457d4aa56a720ba5107a6cc55372a065157aa0755578e175477ba4255d7cc7e56678c145467ce765, 0x11f7e26f5717b2785597e84b5747b45655a7565855664b7554b6784957867f6357f65b7755b6706d57066f7256f6752257566320563677a6577672a25726492c5, 0x14f6841a8541685cf455c6848265486840e65406a8a05547d83e56c726e25137e6b45737f4b257a79ce854e7f2d05797a07f5507d05b56873e705, 0x1869d85696852f2552684f9c5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked37 : FrogCheck.check 30 2 7 (FrogCheck.rows 7 data37) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data38 : List ℕ := [0x16765717557642445426585e5586464154660613506663c456365ebe55e675e8575641805416448a5446139a5136172c51767476274d74071675f7457, 0x17d694ac54a7a2925517aa365557e2d85717c8085647b296559786b4543708725047d86756c7360651b7b45755a792465497964254b7ac5855677275572667635, 0x17670e6050773c6f51e7487d5486604e56065c6155c6687756866f7856f6055d50561f6551f64eb254e661aa561665a256565dc855d67786577678e257867d945, 0x16964ce054c615f251566af656a67ada57a6e0a65707f2dc5797f60e57b73a8e51d7a4ec5527fea057f7da3c56d7a06855078e055477dc4856e7a65c5537ec1f5, 0x11878287c51478346651a78244f51278326b51974f7354f6545b55466b6956b61c1551c67e4c57e6666a56667c7a57c65b3a55b673fe573669a45, 0x18201c51078227e5117830545]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked38 : FrogCheck.check 31 2 7 (FrogCheck.rows 7 data38) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data39 : List ℕ := [0x17959e47f437f0dfd35fb67e9ff0d7e59f87f437d4d7ad9ea7f435e967a1fd8dfe37fcd7fd9fe7fe35fd67f1fd8df735ef67b9fd8d7b59ec7, 0x5ce7e635cd6731fc0df837e4d7cd9f27f835f167c1fc0df135e36789fc0d7859e07f237e8dfb35f767d9fe8d7d59f47f237ccd79d9e67f21e55, 0x1e335c76719f88d7159c47e437b0ded35db6769fb0d7659d87e43794d72d9ca7e435c96721f98dee37bcd77d9de7ee35dd6771f98de735cf6, 0x5bc7d6375cd6bd9ae7d635ad66b1f80de837a4d74d9d27e835d16741f80de135c36709f80d7059c07e237a8deb35d76759fa8d7559d47e238c5, 0x1da35b566d1f48dd335a76699f48d6959a47d43770ddd35bb66e9f70d6e59b87d43754d6ad9aa7d435a966a1f58dde377cd6fd9be7de35bd6, 0x167d99e7ce359d6671f18dc7358f6639f18d63598c7d03760dd935b366c9f60d6c59b07d03744d68d9a27d035a16681f48dda376cd6dd9b67, 0x728dcb35976659f28d6559947c2370cd61d9867c235856611f10dcc3734d66d99a7cc35996661f10dc5358b6629f10d6259887c63738dcf19f5, 0x558656b57ad5fb57f75f997ad5edd7a656b55ed57dd5e656b55b7569b00dc83724d64d9927c835916641f00dc135836609f00d6059807c23285, 0x15435517541952d5cb576d5ddd7665cb57375c9952d55b5577559952d54dd526563578d5f357d75f1978d5e5d78656355cd575d5c65635597, 0x1535d4c6523549752194ad5ab56ed5bdd6e65ab56b75a994ad53b54f753994ad52dd4a6543570d5d357575d1970d5c5d706543554d555d546, 0x540d5135457511940d505d40650b562d59b5677599962d58dd62650b546d51dd46650b5437509948d5a356cd5b5d6c65a356975a1948d5329a5, 0x14e5d38646351cd475d1c6463519746191ad4eb53ed4fdd3e64eb53b74e991ad47b51f747991ad46dd1a6503560d5935657591960d585d606, 0x626a039535703806501dc060154066014085015808f61404744b532d4db53774d9932d4cdd32644b516d45dd16644b5137449918d4e353cd4f5d3c64e2725, 0x6600d953070d81a506dc1a06541a6064305065830f01418789882e54c5c2e05941770581550598150a141560a3c85051e268099534709812504dc120454126044205045820f414107, 0x14b5c8e11944771184551198452214456223885111e25c21952e721842510dc421054426104805105880e41440789783e54bdc3e07941f70781d507981d0e141d60e3985071e600, 0x129852514dc521454526144a051458a0d41450789589e54adc9e13944f71384d513984d26144d6263585131e25825952c72584a512dc4a12544a6124905125890e01448789688e5, 0x45f71785d517985d2e145d62e3185171e2502d952872d85a516dc5a16545a6164b051658b0d0145878948ae54a5cae15945771585551598552a145562a3485151e25429952a7, 0x11a86951a986934146963430051a1e24a339525733866519dc661954666194c851958c8c2146478930c65499cc618946371886151898613014616303105181e24e2f952772f85e5, 0x181f4e851f58e839947473987251cdc72549472681f8e251f98e238147173806f51c1c6f56146f681fcdc51fd8dc36946e73686c51b5c6c56946c68920d65491cd61a946b7, 0x50b7851095429d09509509681ea1051e9a10839508783906541dd06521506681ee0a51eda0a8215057821035411d03529503681f20451f1a048095027809005405d005415006, 0x1485a07690147669022a5481e2a4515157451185451a077889477688a205445e2043d510743d1a543da07887147868721a5439e1a43150d7431405431a079859479685a145, 0x6075919475691a44548de444855227485125]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked39 : FrogCheck.check 30 2 9 (FrogCheck.rows 9 data39) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data40 : List ℕ := [0x174ddd267635f8d7f35fd77f19f8d7e5df867635dcd775ddc67635d977619dad7eb5fed7fddfe67eb5fb77e99dad77b5df77799dad76ddda6, 0x5ce672b5cb77299d0d7c35f4d7d5df467c35f177c19d0d7535d577519d0d745dd0674b5f2d7db5f777d99f2d7cddf2674b5d6d75ddd6674ba65, 0x171b5c777199c2d70ddc267235e8d7b35ed77b19e8d7a5de867235ccd735dcc67235c977219cad7ab5eed7bddee67ab5eb77a99cad73b5cf7, 0x5ba666b59ed67dd9e666b59b76699c0d7835e4d795de467835e177819c0d7135c577119c0d705dc0670b5e2d79b5e777999e2d78dde26709c65, 0x16cb5b376c9992d65b5977659992d64dd9266635b8d6f35bd76f19b8d6e5db8666359cd675d9c6663599766199ad6eb5bed6fddbe66eb5bb7, 0x16bddae66ab5ab76a998ad63b58f763998ad62dd8a66435b0d6d35b576d19b0d6c5db06643594d655d9466435917641992d6cb5b6d6dddb66, 0x5a2d69b5a776999a2d68dda2660b586d61dd86660b5837609988d6a35acd6b5dac66a35a976a1988d63358d7631988d625d88662b5aad6bb5e5, 0x5687b636f8dbf357f65f9ef8d5f597c7b636dcd5bd96e7b6356d65b1d80d6835a4d695da466835a17681980d6135857611980d605d806609a25, 0x1b035616581ec8dba36ecd5dd9767ba357565d1ec8db335676599ec8d5959647b436f0dbd357b65e9ef0d5e59787b436d4d5ad96a7b435696, 0x152d94a7a435496521e98dae36bcd57d95e7ae355d6571e98da7354f6539e98d53594c7b036e0db9357365c9ee0d5c59707b036c4d58d9627, 0x680da135436509e80d5059407a236a8dab35576559ea8d5559547a2368cd51d9467a235456511e90dac36b4d56d95a7ac35596561e90da514b5, 0x14e59387943654d4ad92a794352964a1e58d9e367cd4fd93e79e353d64f1e58d97352f64b9e58d4b592c7a036a0da935536549ea0d5459507, 0x613301d533601c0c501d80c0294067028045015c047694046923668d9b353764d9e68d4d5934792364cd49d92679235256491e50d9c3674d4ed93a79c1395, 0x53011953061188a511988a2214457220435111c43741443684c44254c58422094426208805105c800514407051d25051a13204d532604c24504d8240894127088105045c107614106, 0x14858522894526288a05145ca013d450713dc2513da12213952261389a513989a26144d72604b5131c4b72144b6848c4a548d84a24944a6248905125c9011d448711dca511d9300, 0x1178ba51798ba2e145d72e05b5171c5b66145b6847c5a547d85a2c945a62c8b05165cb015d458715d9a515da1201595206158aa51598aa2a145572a0535151c5370145368484525, 0x46a6348d051a5cd019d468719d8a519da11c19951c6198ca51998ca3214657320635191c63641463684746254758623094626308c05185cc017d460717d92517da11e17951e6, 0x13a8e851d5ce81cd47471cd8051cda1191c951961c8e251c98e238147173806f51c1c6f60946f684686e546986e36946e6368d851b5cd81ad46c71ad8851ada11b1a951b61a8d25, 0x180e87f5075c7e41fd87e3e947e63eac851f5e03c1f141e71f07b51f187b3d147b63d2d051e9e03e1e541f71e107961e0ee51e18eeb61477784607654618763a94766, 0x142d90a84950a684a885425e03442141a74210754219078315076832905419e03641541b74111056412065411a06a61503780e1025071d024055026406005405a00b015007, 0x1455e02c45141674511354519138915136892505449e02e445417744111164421e5441a1e96150f780c10e5061d0e43550e6436185435a18a0150c780c90b5065d0a4, 0x180a9175055d16445d9168a951668aa485]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked40 : FrogCheck.check 31 2 9 (FrogCheck.rows 9 data40) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data41 : List ℕ := [0x17959e47f437f0dfd35fb67e9ff0d7e59f87f437d4d7ad9ea7f435e967a1fd8dfe37fcd7fd9fe7fe35fd67f1fd8df735ef67b9fd8d7b59ec7, 0x5ce7e635cd6731fc0df837e4d7cd9f27f835f167c1fc0df135e36789fc0d7859e07f237e8dfb35f767d9fe8d7d59f47f237ccd79d9e67f21e55, 0x1e335c76719f88d7159c47e437b0ded35db6769fb0d7659d87e43794d72d9ca7e435c96721f98dee37bcd77d9de7ee35dd6771f98de735cf6, 0x5bc7d6375cd6bd9ae7d635ad66b1f80de837a4d74d9d27e835d16741f80de135c36709f80d7059c07e237a8deb35d76759fa8d7559d47e238c5, 0x1da35b566d1f48dd335a76699f48d6959a47d43770ddd35bb66e9f70d6e59b87d43754d6ad9aa7d435a966a1f58dde377cd6fd9be7de35bd6, 0x167d99e7ce359d6671f18dc7358f6639f18d63598c7d03760dd935b366c9f60d6c59b07d03744d68d9a27d035a16681f48dda376cd6dd9b67, 0x728dcb35976659f28d6559947c2370cd61d9867c235856611f10dcc3734d66d99a7cc35996661f10dc5358b6629f10d6259887c63738dcf19f5, 0x558656b57ad5fb57f75f997ad5edd7a656b55ed57dd5e656b55b7569b00dc83724d64d9927c835916641f00dc135836609f00d6059807c23285, 0x15435517541952d5cb576d5ddd7665cb57375c9952d55b5577559952d54dd526563578d5f357d75f1978d5e5d78656355cd575d5c65635597, 0x1535d4c6523549752194ad5ab56ed5bdd6e65ab56b75a994ad53b54f753994ad52dd4a6543570d5d357575d1970d5c5d706543554d555d546, 0x540d5135457511940d505d40650b562d59b5677599962d58dd62650b546d51dd46650b5437509948d5a356cd5b5d6c65a356975a1948d5329a5, 0x14e5d38646351cd475d1c6463519746191ad4eb53ed4fdd3e64eb53b74e991ad47b51f747991ad46dd1a6503560d5935657591960d585d606, 0x60fe03947f703806501dc060154066014085015808f61404744b532d4db53774d9932d4cdd32644b516d45dd16644b5137449918d4e353cd4f5d3c64e2725, 0x4f823147c7230455119c444115844219444621bc0510de0fa21147d7210415109c4041058400a144060a3c85051e0fc09947e709812504dc120454126044205045820f414107, 0x4797290515149c504145850279450627b88513de0f427147a72704d5139c4c413584c25944c625b90512de0f625147b7250495129c484125848239448623b98511dcf80, 0x4bc17545e717105d6170b651718b6d4145b783b8b451ddcb416545a71610596160ae51618aed61457783c0ac51e1cac15545671510556150a651518a6e01453783c8a45, 0x11a9c6841a5868339468633b18519de0e83314747330655199c644195864319464631b40518de0ea3114757310615189c6041858602f946062fb48517de0ec2f14767, 0x5044415904819504681b00540de0e28114717811015409d004405900379500637b0851bde0e437147273706d51b9c6c41b586c35946c635b1051ade0e63514737350695, 0x180761e5075a1e87150f78710d5439d0d54950d6807a185079a1885950c78590a542dd0a56150a6807e12507da128415097841075421d07569507683820c51c1e0c4155067, 0x5277931255499d255095256806a485069a48919524791922548dd225215226806e42506da429015217901155481d1552951568072285071a288895147889105445d105415106, 0x14c5a01698141669825e54c1e5e4b952f74b91854b9a017969417696a5854b5e584ad52c74ad1a54ada01895141869525254a9e524a152974a14054a1a019939419693a4c5, 0x60159a941569aa6854d5e684c553474c5125]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked41 : FrogCheck.check 32 2 9 (FrogCheck.rows 9 data41) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data42 : List ℕ := [0x5e39c62a39e423548ec44ab1646d151b2010a81846a510c27b289668595a36adcad5fb1e576e5a928b7a4a154b9e7ca3df73656eed99433e6, 0x144d6b02ad7e5095cbcea8a9de13a542f515aaa7c0bd583af64abd9d0c574cadfaab665615933f94afd865c518d6242ac795e152bdc38ab9fc205, 0x18ccf559bc0a44a29a06a651acf5c2bd671395c326b4a9991725]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked42 : FrogCheck.check 36 3 6 (FrogCheck.rows 6 data42) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data43 : List ℕ := [0x52b2a34aa99462550d8ab2b1731b14639ac8a35f60a56cf91dab27ac8955b8a4ea29910b544cedeabb64e4953b0bb0a2d9ef857ac25de3ac7, 0x166ed14ab466eb55bb3540ad594e0552c82e2a065b7956b5e38abdf048560f7382ae7380d473c87ea91f839570e0d2a8367ea95fb3950ae592985, 0x61f1057cd0e8f2ba68470951b4298a85cf6651ee402288708d1413cc6ea99f3355]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked43 : FrogCheck.check 37 1 6 (FrogCheck.rows 6 data43) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data44 : List ℕ := [0x53bd26aaa5e43e548ed452b566ecd5bb3e4aaf98570514c96b2a5667c959b720cae5f876570f5822ab708854138662a0dfb3a576e8598b3a6, 0x22d887a510f1302a27f1795e3de68abdf036560fe962bd768a15a33640ad996a2c651195432da8ab59064540d5272aa7c949593c690a8de7375, 0x6093f512f069728d78383d473bf16afd878c51ecb932ae618414632688a9985f85]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked44 : FrogCheck.check 38 1 6 (FrogCheck.rows 6 data44) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data45 : List ℕ := [0x149ba49931ab8d5e6af5d78cb8d5cbae1931a9cd4eba71931a9974c326b575abed5fbaf9975abb75d326b53da9f74f326b536e9a6, 0x28e6456a2dd14c90d586ad356aeb46586ac5d60c90d4a6a55d28c90d48ba41925ab2d5b6addd6ccb2d59bac9925a96d4bba59925265, 0x1ee6bbd9dcfd8d76b3b1d11aa8d566ab5d58ca8d54baa1911a8cd46ba31911a89744322b555aaed57bab9955aab755322b51da8f7, 0x2f47e46f335cece67e46b959c8fd0df86fd35f6cfa7f86be59f0fd0dea6bad9d4fd0d74b3a1fb1bf8dfe6bfd9fcff8d7eb3f1fb1dc5, 0x1dc6b759b8f98dce6b3d99cf98d66b331f81be0df26bcd9e4fe0d78b3c1f81bc4d71b389f81ae16703f237d1becd7bb3d9fd1af56, 0x12b0a9456e2a14a8a985250514b1409ca2872709944ee264c2899a36c4a56db92848a2571208d448c2322288d88842511390840a21710269440d98ddc6ef35becde7, 0x3b0372b61cdc3651bb8d86aa3661a9a146ac683328d1ccc32519b8c920a3268d91895b2e621828c5c602f51830bcb8a2f62e16945ce5a1628b5c5892516346d0acada7, 0x542f1aca02b59e80875503a1910ec86852a19a1508542bc2106a84741a21506d1ae822b5de08815413a01102c803a2a018e87251d39c870a3971c229470db00, 0xb19d888c5662619588d86e42b0de07d8451f361304ac27c1301582ec053ab0194f4c553b533a0aa6781fd2947ed4aa42a95e90a35523a89146ca2a12a89a85d85, 0xc0ef54a3b6d56a15aafa869ab51da48d36696895a4da2cc2b45e079a051e36832cad07cb329596eca64ab2999390564b64380ac8781ee3947ad8ec62b1df18c55]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked45 : FrogCheck.check 37 5 8 (FrogCheck.rows 8 data45) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data46 : List ℕ := [0x15959647b436f0dbd357b65e9ef0d5e59787b436d4d5ad96a7b4356965a1ed8dbe36fcd5fd97e7be357d65f1ed8db7356f65b9ed8d5b596c7, 0x54e7a6354d6531ec0db836e4d5cd9727b8357165c1ec0db135636589ec0d5859607b236e8dbb357765d9ee8d5d59747b236ccd59d9667b21655, 0x1a335476519e88d5159447a436b0dad355b6569eb0d5659587a43694d52d94a7a435496521e98dae36bcd57d95e7ae355d6571e98da7354f6, 0x53c796365cd4bd92e796352d64b1e80da836a4d54d9527a835516541e80da135436509e80d5059407a236a8dab35576559ea8d5559547a228c5, 0x19a353564d1e48d9335276499e48d4959247943670d9d353b64e9e70d4e59387943654d4ad92a794352964a1e58d9e367cd4fd93e79e353d6, 0x147d91e78e351d6471e18d87350f6439e18d43590c7903660d99353364c9e60d4c59307903644d48d92279035216481e48d9a366cd4dd9367, 0x5fad7fb5ff77f99fad7eddfa676b5ded77ddde676b5db7769a10d8c3634d46d91a78c35196461e10d85350b6429e10d4259087863638d8f11f5, 0x5d0674b5f2d7db5f777d99f2d7cddf2674b5d6d75ddd6674b5d377499d8d7e35fcd7f5dfc67e35f977e19d8d7735dd77719d8d765dd86769fa5, 0x17235c977219cad7ab5eed7bddee67ab5eb77a99cad73b5cf77399cad72ddca67435f0d7d35f577d19f0d7c5df067435d4d755dd467435d17, 0x1715dc467035c177019c2d78b5e6d79dde6678b5e377899c2d71b5c777199c2d70ddc267235e8d7b35ed77b19e8d7a5de867235ccd735dcc6, 0x104dc120454126044205045820b61410766b5bad6fb5bf76f99bad6eddba666b59ed67dd9e666b59b76699c0d7835e4d795de467835e177819c0d7138a5, 0x4497240475121c46411d846229446622ac85115e1bc1115bc61108651118862114437210415109c4041058400b144060b2d05059e1bd0555bd60542850558280994147098125, 0x45662a8a85155ca814d45471490536148a251498a2a61451786e05056e185027945062789c513dc9c13544e713104d6130965131896b0144b786e44a56e584a24944a6248905, 0x5b56188c251898c230146173005f5181c5e417d85e2e945e62ea885175e1b61715b66170b651718b62d145b72d0595169c5841658582b945862ba90515de1b71595b76158aa5, 0x186cc6e56cd86e36946e6368d851b5cd81ad46c71a906b61a8d251a98d2961469786d06856d18683394686338cc519dccc19546671910656190c651918c6a01463786d4625, 0x4f690147b786c47a56c587a3c947a63c8f051e5cf01dd47871d907761d8ea51d98ea921475786c87456c98743994746398e451cdce41c547271c107161c0de51c18de94146f7, 0x510839510683a10541de1af4195af641a0a5419a0a8215057821035411d02440d902809502680a185405e1b04015b06400fe54018fe3f147f73f07d51f9c7c41f587c3d947c6, 0x585c215856c23065611f066095837609d85609a03e60541f760118166022e5601a2e8b151778b1155459d15769515686b91456b9914899514689a24544de2444551274411116, 0x1645a03864141c76418f564198fc7158f6c731a5639f1a63158d7631d05631a03a62d41d762918b662b125629b12c415897c41875621d87749587680f1865079d866155866, 0x1689b42d015a17d019d5681d9d70959d680d19c5069d9c66559c6667305665b30cb95987cb996565dd96721596680d995506dd944655994c995946c9b24564df246455927645ca5, 0x180b9ad505ddac46b59acd595ac6d5b5456adf546a55aa76a59a56a5a0306a141876a1a756a19a7d315a76d334a5699f4a6915a57691c05691a03268d41976891a3668b425]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked46 : FrogCheck.check 37 4 9 (FrogCheck.rows 9 data46) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data47 : List ℕ := [0x154dd526563578d5f357d75f1978d5e5d78656355cd575d5c6563559756195ad5eb57ed5fdd7e65eb57b75e995ad57b55f757995ad56dd5a6, 0x54e652b54b7529950d5c3574d5d5d7465c357175c1950d5535557551950d545d50654b572d5db57775d9972d5cdd72654b556d55dd56654aa65, 0x151b5477519942d50dd426523568d5b356d75b1968d5a5d68652354cd535d4c6523549752194ad5ab56ed5bdd6e65ab56b75a994ad53b54f7, 0x53a646b51ed47dd1e646b51b7469940d583564d595d6465835617581940d5135457511940d505d40650b562d59b5677599962d58dd626509465, 0x14cb53374c9912d45b5177459912d44dd126463538d4f353d74f1938d4e5d38646351cd475d1c6463519746191ad4eb53ed4fdd3e64eb53b7, 0x14bdd2e64ab52b74a990ad43b50f743990ad42dd0a6443530d4d353574d1930d4c5d306443514d455d1464435117441912d4cb536d4ddd366, 0x7f8dff35ff67f9ff8d7f59fc7f637dcd7bd9ee7f635ed67b1d08d4a352cd4b5d2c64a352974a1908d43350d7431908d425d08642b52ad4ba5e5, 0x5e07f237e8dfb35f767d9fe8d7d59f47f237ccd79d9e67f235e56791fd0dfc37f4d7ed9fa7fc35f967e1fd0df535eb67a9fd0d7a59e87f63f85, 0x1e435c96721f98dee37bcd77d9de7ee35dd6771f98de735cf6739f98d7359cc7f037e0df935f367c9fe0d7c59f07f037c4d78d9e27f035e16, 0x170d9c27e035c16701f88dea37acd75d9d67ea35d56751f88de335c76719f88d7159c47e437b0ded35db6769fb0d7659d87e43794d72d9ca7, 0x104d8240894127088105045c105694106d63778ddf35bf66f9f78d6f59bc7d6375cd6bd9ae7d635ad66b1f80de837a4d74d9d27e835d16741f80de11c35, 0x112584823944862388c511dc8c1154467115525115a0fc22147e7220435111c42410d8422094426208805105c800594407059585059a0fe0a947f70a8145055c1404d414604c245, 0x1159c5441558542994546298a4514dca414545271454a5145a0f828147c72804f5141c4e413d84e26944e6268985135c9812d44c712d50512da0fa25147d7250495129c484, 0x4797310615189c6041858602f946062f8bc517dcbc17545e7175425175a0f42e147a72e05b5171c5a416d85a2c945a62c8b05165cb015d458715d48515da0f62b147b72b0555, 0x183b8dc51ddcdc1b546e71b106d61b0d651b18d635146b73506951a9c69469469683c0d051e1cd019d46871990676198ca51998ca3214657320635191c63501463683c8c45, 0x521441521683aa4051d5e4041d5207419107641a0a5419a0a8215057821035411d03449503683b20451d9e0440550274011016400e254018e238147173806f51c1c6f46146f6, 0x70c6155867615085615a0e6c214737c21835611d82460d982c095826c0b005605f0049d580749d0a549da0e89314747931255499d244495924919524691a44548de444855227, 0x7266495937649915649991c815916c83d05641e01fc7941f6c7b1c563df1c63558e763118d6633165631b16f6158b783931451c9f1462558a762118966230e5621b0ec315877, 0x167de01ccf141c6cf33a5679f3a67159d76719b567199bcd159b6cd3c05669e01dcc941d6ccb305665f3065d5987659197665b2a5659b2af215957807b285079b28c995947, 0x5b076a91ab66ab5256a9b52e215a97806b505069b50d395a87d39a6569dda66955a66697485695b48e415a47806f46506db46d115a37d11a15689da046859a0cf95a06cfb985, 0x6017dd94176ddb7456edf746e55ba76e11b966e36e56e1b6ed615b7780636c5061b6cda95b67da9b456d5db46cd5b466cf6456cdb64e015b278067625065b62d815b17d81ab5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked47 : FrogCheck.check 38 4 9 (FrogCheck.rows 9 data47) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data48 : List ℕ := [0x63e795f779d5799de15d6e36571f6695b769956999c1596c26561e6495374915499181516828541e8db357659e8d55947]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked48 : FrogCheck.check 43 4 5 (FrogCheck.rows 5 data48) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data49 : List ℕ := [0x61ff15f6f3a579fa715d771b5719bd15b6d32569f26159761556195a1556a22551e24151741254192d5b5775992d4dd26]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked49 : FrogCheck.check 44 4 5 (FrogCheck.rows 5 data49) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data50 : List ℕ := [0x16373a6451d79a4454d78c4e5467441354466e6956e64e4b54e6186c5186641b5646139e51366cda56c61bde51b669d056964b2454b66d74f71276876f7, 0x16b61f1151f6455f5456485554867e5d57e65fa255f65db855d657b255761120511655f05556a23a5517b89a55c7f0c6578720f65107b28c5597f61857b7c66e5, 0x17267180571662c0562675ce575677a0577647b05476ce94567780d45407c0fe5607a03c5507b0ac55873c6b51e7fe4857f7944554a7ac7e5567d41f56a76b575, 0x166670b45706b43855a7fab657d7f2845797e8a657472c865167a6735537b65e55b7384951c7847c5427867254377c6257c6497554965e7155e67347573672775, 0x18346551a78287a514782e5251778324c519782a4151574c6154c665765656416654167a5457a65270552654fa554661f2561676e85766662c5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked50 : FrogCheck.check 43 4 7 (FrogCheck.rows 7 data50) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data51 : List ℕ := [0x17959e47f437f0dfd35fb67e9ff0d7e59f87f437d4d7ad9ea7f435e967a1fd8dfe37fcd7fd9fe7fe35fd67f1fd8df735ef67b9fd8d7b59ec7, 0x5ce7e635cd6731fc0df837e4d7cd9f27f835f167c1fc0df135e36789fc0d7859e07f237e8dfb35f767d9fe8d7d59f47f237ccd79d9e67f21e55, 0x1e335c76719f88d7159c47e437b0ded35db6769fb0d7659d87e43794d72d9ca7e435c96721f98dee37bcd77d9de7ee35dd6771f98de735cf6, 0x5bc7d6375cd6bd9ae7d635ad66b1f80de837a4d74d9d27e835d16741f80de135c36709f80d7059c07e237a8deb35d76759fa8d7559d47e238c5, 0x1da35b566d1f48dd335a76699f48d6959a47d43770ddd35bb66e9f70d6e59b87d43754d6ad9aa7d435a966a1f58dde377cd6fd9be7de35bd6, 0x167d99e7ce359d6671f18dc7358f6639f18d63598c7d03760dd935b366c9f60d6c59b07d03744d68d9a27d035a16681f48dda376cd6dd9b67, 0x728dcb35976659f28d6559947c2370cd61d9867c235856611f10dcc3734d66d99a7cc35996661f10dc5358b6629f10d6259887c63738dcf19f5, 0x558656b57ad5fb57f75f997ad5edd7a656b55ed57dd5e656b55b7569b00dc83724d64d9927c835916641f00dc135836609f00d6059807c23285, 0x4416203d85101d52d5cb576d5ddd7665cb57375c9952d55b5577559952d54dd526563578d5f357d75f1978d5e5d78656355cd575d5c65635597, 0x49e13944f71384d513984d26144d6260965131c9612944b71284951298492414496243d05121e2ea239575723846511dc461154466114885115888219444721842510dc421054426104805, 0x4b82d945c72d85a516dc5a16545a6164b051658b0f0145878b88ae55c5cae15945771585551598552a145562a0a65151ca614945371485151498512814516283c85141e2e82795747, 0x46934146963439051a1e2de33956f733866519dc661954666194c851958c8319464731862518dc621854626184c051858c0e6146078b80be55c1cbe17945f71785d517985d2e145d6, 0x15b5cee1d947771d87551d98753a147563a0e651d1ce61c947371c87151c987138147163838851c1e2dc37956e73786e51bdc6e1b546e61b4d851b58d835946c73586a51adc6a1a546a6, 0x508683a0c541de0c41550674111056412065411a06d6150378b620455b1e0440550274011016400f854018f83d947c73d87a51edc7a1e547a61e4f051e58f0e0147878b68ee5, 0x1455914899514689b48544de2d489156a7891115449d104445910879510687a1c543de1c43550e743110d6432165431a16d4150b78b5a1455ade1442550a742110964220e5, 0x6d09115687911215489d2044859208f952068fa3c547de3c47551e747111d6472365471a36d0151b78b4a3455a5e3446551a746111964622e5461a2e8b151778b1155459d144, 0x530979530697a5c54bde5c4b552e74b112d64b25654b1a56c4152b78b3a54559de544a552a74a112964a24e54a1a4e9315277931255499d244495924919524691b18548ded00, 0x53c44f593c9d953c69db0054ede2ca9d156579d13954e9d3844e59389b953869ba6c54dde6c4d553674d113564d26654d1a66c2153378b32645599e644c553274c11316, 0x54a56154a681fe9251fda92a415497a41475521d46451d946a295466a2a885515e8850d544750d5a550da2c8a115647a11415509d4045059409f954069fa7c54fde7c4f553e7, 0x181f6c651f5ac6b115637b11615589d604585960aa95606aaaa85555ea85455547545525545a07ea8147e6a829e5541e9e53954f75394d553994da6154d6a62965531e9652954b7]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked51 : FrogCheck.check 42 6 9 (FrogCheck.rows 9 data51) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data52 : List ℕ := [0x169bb499b1af8d7e6bf5df8cf8d7cbbe19b1adcd6ebb719b1ad976c336b5f5afed7fbbf99f5afb77d336b5bdadf76f336b5b6eda6, 0x2ce6656b2dd94cd0d786bd35eaef46786bc5de0cd0d6a6b55da8cd0d68bb419a5af2d7b6bdddeccf2d79bbc99a5ad6d6bbb599a5a65, 0x1636b1dd8ccc2d61bb09991ae8d766bb5dd8ce8d74bba1991accd66bb31991ac9764332b5d5aeed77bbb99d5aeb775332b59dacf7, 0x2bc7ac6d7355ecae7ac6ab5958ec0d706b935caee46706b85dc0cc0d626b15d88cc0d60bb01985ae2d736b9ddccce2d71bb89984c65, 0x20c05a83181614505b05024a0a709021412e086d2821aa1b70dba6aed974f70d5cb2e1ea1b54d55b2a9ea1aa96543d636f1b7cd5fb2f9ef1abd6, 0x2561528adc54d2515342d852ab6614941452c502728a1c9c26513b8984aa2661292144ac48232891c8c22511b889b0a22685b88556ec212028858801a510386818a0d7, 0x568c393828e58e06e51c39b86ca3771b0d546cc353428d58d06651a399864a33719341464d0b518aad586260518b180bca3072f0b945ee2e16a8b985a58516b160aca2c7, 0x28774321550cc85842a15a11065423c1904a83741321504d0b340aacd90300540b400fca8073f0f947ee3e1ea8f987a7851eb1e0eca3c73b0e9476e3a6528e9a168395, 0x294793249526e92602a49a16291558b24640a91690479520f1e472a3dd1c8d547323630a8d68c459518f16452a2dd14c2545342c912ab2644c41512d10872a21e1c865, 0x2a1780f28141eea04faa8193f3c54fb4f274a9e79d27153ae9c4daa719373454db4d2b0a9a7858265560c99982a65a612e54c3cb92ca9774b25552cc95942a55a51265, 0x301c53a839d4c8a765352954cd4aa42a95e90a35523a89146ca2a12a89a85505]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked52 : FrogCheck.check 44 3 8 (FrogCheck.rows 8 data52) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data53 : List ℕ := [0x172b391fa1bf0dfa6bed9f4ff0d7cb3e1fa1bd4d75b3a9fa1ae96743f637f1bfcd7fb3f9ff1afd67e3f637b9aef6773f635dacec7, 0x2ce7cc6b35998fc0df06f935e6cf27f06bc59e0fc0de26b8d9c4fc0d70b381f91be8df66bdd9ecfe8d7ab3d1f91bccd73b399f90e55, 0x1c66b1d98cf88d62b311f21bb0dda6b6d9b4fb0d6cb361f21b94d65b329f21ac96643e63771bbcd6fb379f71add66e3e63739acf6, 0x2ba64d6a7b53ee9e64d6a6dd34d80dd06e935a6cd27d06b459a0f80dc26b0d984f80d60b301f11ba8dd66b5d9acfa8d6ab351f118c5, 0x2180b2831c2c0a505b82812a0a604841412c10ec2821d31ab8d5e6af5d78cb8d5cbae1931a9cd4eba71931a9974c326b575abed5fbaf9975abb7, 0x22b2a28ad8a9c85153c1f0a4a3e7290a1452e2813a8a184e4c513b13094a2672509144ae2411a89184644511b113a0a22783f10947ee42102885c400d510303430a0d6, 0x478f02402a05d003754030dcd8a376361a946ce6a1a28d5c683351a30ccc8a33632701464f07a3128f5cc430518b8c05ea3061797145ec5c2d28b9cb42c516b8b056a2c6, 0x28f68e46951cf1a462a35d188b546322e28a8b68a641514f0768928ede2488544ba210ea88643c3150ed0c852a19e1484542ba1106a84641c11506d04cc2a09e0f1025, 0x2a4651d11546d44c02a89e0e54251cbd0940aa175025d540c97962a5da592a54b3ca928a9574a24d528c93922a4da49885493c1d244a3a791241522e9047aa4191f1c5, 0x2b16807d8141ed60af2ac1ebcae557bab95aaae656d6155ad58ab2ab1eacaa555baa934aaa6838549470f52542aa5d50a7554329e98aa76a652954cf4a522a95d48a35, 0x601d6e50735bad8ab77b62d556ceb445ab2d2ccab46b3591566f6458aac9d62985]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked53 : FrogCheck.check 45 3 8 (FrogCheck.rows 8 data53) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data54 : List ℕ := [0x1666f07657874f2e54f618f6518676735766b8bc55c7f63e57b72eb451773c0c51e70c615067b41655a773e457363e0751f7bc5f55e71666165f6727076, 0x11179aa054d7e8845747a2a855176f1556f6a05b5507ba5655d715da515684045427a8705547daf056d7044f504656185566705257065b6655b652b85526663c5, 0x14866a2056a68a635457946754a79c6854e7864b5437684656864b6454b6636e563620285107674156766e9a56e664a25646286f514741e854164622546622ba5, 0x16c7361351b7554c55561349513660475606fe8057f7441954464cd654c619fa51968048540747b2547649f45496b29c5597d68a56b7f49457a7fa8657d7486a5, 0x11d7951d6655856568027c501757ee557675a6575658fc5586790a57960ad850577c6257c6a6365537eee25777fc2457e762fe5626e244571724605127d8555, 0x18d265569781c7551c681a5751a61d0]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked54 : FrogCheck.check 47 0 7 (FrogCheck.rows 7 data54) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data55 : List ℕ := [0x1586944754a73e1551f790455487aca855671512515645405456171151764743547611885116129251264320543640825406a8555547417497556107447, 0x172673655736644c56460c9650676b5f56b665365656961d54b75fa455f64cb654c66d3456d6a48c5527b69455b7349051a71d5851d6363e51b78c17546758ac5, 0x16967cc257c6f64e57b71cd851c674c05746183c51864e4254e6c0fa5607c2b456173cec51e7d8fc56c7ec6b5767fa7257d7b47355a7fc6457e7420c5426726d5, 0x16f677fe5776ba9a55d719625196ce265677bcd055e7fe2857f7267151375011479a4f54d762dc5626d0695687dcf656e7507c55064f1c54f67118571669745, 0x1167808c65047c6755637f0795787a2665517801b25016e0535707b2f45597666a566675775756796f5796535c55366abc56a6f41957a75cce55c66fba5, 0x18572c557680ee0507780af050572ca25]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked55 : FrogCheck.check 48 0 7 (FrogCheck.rows 7 data55) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data56 : List ℕ := [0x17c9fb27615d978690c5435e784f553c7e09c05705c2c5814167a10505509d41664d9d2673590c66d997e61f19c664f59db67dd977615d9c0676187561419606, 0x1525facea15d673bbb251ddce83b147473b1db51d9fec7dd5f67bf97e55fdf6e6d95b770a1415051f987355cc7ea0755751c3a74941d70b977505df8e7195c770a8575055f2464d5927f907c5, 0x11e1a7c9e153e728a845145ef8bf957c787a1a543dcfaf9147d7e13825709ccac9146573983a51cdeb80a955c7e7b98573dfeafb15f57b782c55bdf68db95b47e238e5711efa0b957d7a48285, 0x1775853ae1453672788572587e3b947e65029255019cae115ca616afa51699309f15306620ca56218713e9471616ca2516d872eb147261a36851a19c3e795c36162f8516190587950561e0e85, 0x17f199d1c959d67edc357ed96d50156d66107156119ac6215ac64205354219074c1507618ddd518d85541545567b86857b9947599547649458549586d16946d659ade55999f8fa95f86774e65, 0x11fdf207b95907f605e57b1ebe18d55f7f49b157a5ff46115fa7f21ac5791cc241d46179186a548de9642154b79a14754d1c5e1e145e61a9f851a986072946066c47e56c581816d41867f1c95, 0x1595c92a594497ee22e5771e263d95137dc8c256e5e642395327e28965715ce0fd14707830605419e2e5b551772599d512dcf61b547b7239fc511de660615337250555129cac7ed45673f9255, 0x16a99160d951664038a54019f9f595f9614bc251498369a141b7a8b205545fc28315e17d4a6656a5fd6af95eb7b43d255a1e4c2b15267973d854b9c9891944c7228fe5115e5af2152d7b28945, 0x16b599948159965ba5a55b998d24958d65c25c55c19a6d495a667c26457c1972229572673bb857399a39315a3655f72555d9de8995de67fed057fd9853815856482a254819e52615e566aaca5, 0x535643970543996355d56367c11f165556e55559e77395e765a98d55a994414954461118551119e068d5e065d97255d99317e553167f9e557f994f6a954f660d16560d8797fd47966b5de5, 0x1655fda5555ed7f413157a1e201115107d21f15691e9c58d54e7d413556a1e347f951a7ac9765565e5679d52b7c89ba5645e3860d51c7ca16a5651f3e78159f7dc14456e1dba6995ba64d5005, 0x1521f3cc8959e7323145191faed415d77a6b3e5535e443615227d9a9c56cdf7eca15bf784b2a5425ea8ac95547a9bda554ded8bd956c7c51995629cd843946c7cc14f5661ef66b557b7ca8795, 0x169586620946664766e547598fc5958f66ba1256b986ea9946e663aa85639902a6950265aee255adae28d157178a3d05451c828814417c0a385605f16d2158b79bb3054ddf0cdc15867a42565, 0x15759fd63d5fd65301955319e21b95e26529a5552987a04947a60677e5065904c0950464e2d854e19abcf15ab604bae50499438a154365cf0c55cd9e33215e364aa9054a99f3d995f36696445, 0x1601c9c57544e79b10354d9d296ad52965194355199ea4095ea64798e547999b5cd59b674c66574d91b78d51b6769ae57699014e150165852a55859bc7cd5bc640d1d540d91841151865756b5, 0x14ede1646d50b78a9295455f5e4055af7909da5485e7e74d53f7d09185685ef478957a7fa07a57d1f2e4795977081ea5041f605195b07d014c5681c865294437bc96155e5e4e6f15277c01fd5, 0x1721ea4d015527f322a5799ee89b157478f820547de14d8150a7242765121ec8cb95647ba89c55d5eb6fa155b7eab425755e32bd15197892425449e22d795117d927e56c9e58bc952c79d99b5, 0x17bd945f3154564be7454bd840ba14406747645745962ba956261523e5151958ea955864922454919a2ad95a26624905625982e41582661ec8561da7421953a79421654a1f76c015bb7e424e5, 0x180798250799964e55966541625541a01c6f941c6669a256699b54915b56559ef5559a01161d41164e63254e59d0a915d06673765671967889567677e14577d9be9615be67be505, 0x1135e0b857945c783495a51a5e01315141366f55856f595e74555e663189563196951556968069df5069978671578672c40572da01f59d41f669dd0569d95a4bd55a6, 0x182e9965175e0de5a546f7827950513de08c6f5446782119a5109e0be69d45f78311785189e0b255945978359b551ade0ce72d467782698c5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked56 : FrogCheck.check 47 4 9 (FrogCheck.rows 9 data56) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data57 : List ℕ := [0x154dd526563578d5f357d75f1978d5e5d78656355cd575d5c6563559756195ad5eb57ed5fdd7e65eb57b75e995ad57b55f757995ad56dd5a6, 0x54e652b54b7529950d5c3574d5d5d7465c357175c1950d5535557551950d545d50654b572d5db57775d9972d5cdd72654b556d55dd56654aa65, 0x151b5477519942d50dd426523568d5b356d75b1968d5a5d68652354cd535d4c6523549752194ad5ab56ed5bdd6e65ab56b75a994ad53b54f7, 0x53a646b51ed47dd1e646b51b7469940d583564d595d6465835617581940d5135457511940d505d40650b562d59b5677599962d58dd626509465, 0x14cb53374c9912d45b5177459912d44dd126463538d4f353d74f1938d4e5d38646351cd475d1c6463519746191ad4eb53ed4fdd3e64eb53b7, 0x14bdd2e64ab52b74a990ad43b50f743990ad42dd0a6443530d4d353574d1930d4c5d306443514d455d1464435117441912d4cb536d4ddd366, 0x7f8dff35ff67f9ff8d7f59fc7f637dcd7bd9ee7f635ed67b1d08d4a352cd4b5d2c64a352974a1908d43350d7431908d425d08642b52ad4ba5e5, 0x4406f237e8dfb35f767d9fe8d7d59f47f237ccd79d9e67f235e56791fd0dfc37f4d7ed9fa7fc35f967e1fd0df535eb67a9fd0d7a59e87f63f85, 0x44e13544e613498513589825944c72584a512dc4a56144a68f989257cdc92121449712047512184723144762308a5119c8a11144571104351118432114436210825109c8210144171015a5, 0x1175c5c16d45c616cb4516d8b42c945a72c8585165c5815d458615cac515d8ac2a945672a8545155c5454945468f90a657c9ca6149453714851514985128145162809e5141c9e13944f7, 0x46a73486851a5c6852946868f80ce57c1cce19946771986551998653214656320c65191cc618946371886151898613014616300be5181cbe17945f7179505179a3e22e95f172e85c5, 0x4f03b947873b87651ddc761d547661d4e851d58e839947473987251cdc7252147268f18e2578dce21c147171c06f51c186f37146f6370da51b9cda1b146d71b06b51b186b35146b6350d25, 0x63c29015e17901075481d06441d906829506682a085415e0840d5047409103640a025409a0280150178007c5401c7c50947c68f10f65789cf61e947b71e87951e98793c14796, 0x161d986c295866c2b085615f0860d584760d1a560da3c0c115e07c11815609d804605980939580693a4c549de4c49552674911256492465491a469115237911215489d215015216, 0x5944655994c995946c9b24564df24645592764119166431e5641b1ec7158f7c718d5639d8d46158d68efb18577df1862d58c762918b662b125629b12c415897c41875621d864, 0x7446855a27685105685a3bad015dd7d019f5681d9e467d99ece959e6ceb385675f3866d59c766919b666b325669b32cc15997cc1975661d9744959768ef32c5779f2c6555967, 0x5b17d81af56c1dae46bd9aed695ae6d6b5856b5f586ad5ac76ad0a56ada3b8d515dc7d51a956a9da846a59a8d395a86d3b4c569df4c6955a676911a56693465691b46d115a37, 0x1ed37c5769f7c6f55be76f11bd66f37656f1b76dd15bb7dd1b956e9db846e59b8db95b86dbb6c56ddf6c6d55b676d50856d5a3b6da15db7da1b356d1db246cd9b2d895b26d8b605, 0x1e63965731f967295cb7729c957299c9e415c96e43d05721e07fe3947f6e3b8c571df8c7155c677111c56713865711b86e115c37e11c15709dc047059c0df95c06dfbd856fdfb40, 0x607dec947d6ecbb05765fb075d5d877591d7675baa5759baaea15d57ea1d35751dd2474d9d2e895d26e8bc85745e07ee8147e6e839e5741f9e7395cf7739cd57399cde615cd6]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked57 : FrogCheck.check 48 6 9 (FrogCheck.rows 9 data57) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data58 : List ℕ := [0x152b291ea1b70dba6aed974f70d5cb2e1ea1b54d55b2a9ea1aa96543d636f1b7cd5fb2f9ef1abd65e3d636b9aaf6573d6355acac7, 0x28e78c6a35918f40db06d93566cb27b06ac5960f40da26a8d944f40d50b281e91b68db66add96cf68d5ab2d1e91b4cd53b299e90a55, 0x16f6b7ddbccdad6dbb69a21b30d9a6a6d934f30d4cb261e21b14d45b229e21a896443c63671b3cd4fb279e71a9d64e3c63639a8f6, 0x2f26696b5b5aeed66696b4dda4cd8d7c6bf35faefc67c6be5df0cd8d6e6b75db8cd8d6cbb619b5afad7f6bfddfccfad7dbbe99b4de5, 0x49550512bc3d448af5612119448c4622288dc88215113881042c200c288183016506385814a0b705025414c09082825821585043b4b5e5af6d7bbbd99e5af37, 0x8d18cc64519b99062a3271820c58605e518317a90a2f787a0b95e8c2e2d28b98b458516b96056a2c71520ad854525153148a0a2972809d450e26413b09894a266, 0x141409504d02802a05e003f54038f907ec3e3d28f98f47851eb9e076a3c71d20ed8747251d31ca80a3978788e15e2c383728e18dc6c51bb9b06aa3671a20d5868665, 0x52c89764b4a952cd2a882a55e1de94577b2524ca94693491526f2448aa49d20891648439520d0e862a1de18855433a1110ac84832a11a0d18541bc3c104af06, 0x167366b30acd7cc32d598eca465b32b24aca6c9641592f9063ab21d8eda563b43b98caee66362958cd8ac42b15f10c35623b09186cc2c12b09b0580560be012eac07, 0x173bf31caae6772b495cad01c722839dc8e3572338f88ae36e27095c4fc2702b85dc0d5570335750ad56d46895a8fa2682b45da0d8568340799ea0f767233d99d9a5, 0x301a76a835dd88ed6767595d8dd6ea2badfa8e95753ba11d2ce8e72ba1b9dcc5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked58 : FrogCheck.check 50 3 8 (FrogCheck.rows 8 data58) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data59 : List ℕ := [0x149ba49931ab8d5e6af5d78cb8d5cbae1931a9cd4eba71931a9974c326b575abed5fbaf9975abb75d326b53da9f74f326b536e9a6, 0x28e6456a2dd14c90d586ad356aeb46586ac5d60c90d4a6a55d28c90d48ba41925ab2d5b6addd6ccb2d59bac9925a96d4bba59925265, 0x1ee6bbd9dcfd8d76b3b1d11aa8d566ab5d58ca8d54baa1911a8cd46ba31911a89744322b555aaed57bab9955aab755322b51da8f7, 0x2f47e46f335cece67e46b959c8fd0df86fd35f6cfa7f86be59f0fd0dea6bad9d4fd0d74b3a1fb1bf8dfe6bfd9fcff8d7eb3f1fb1dc5, 0x44a98512b41f890a3f72408d448e22411b08884a22621101442e40062881c180b506302c28a0b60a049414e12042825c109a50437237d1becd7bb3d9fd1af56, 0x8d1c64833619189464c623028c5cc02f51838bd24a2f683e17147ce5c16a8b9c5882d616159458c562a28adca82951538a1052c282728a189c4c513b9304aa267, 0x1a021d540e86443b21a14a8668542150af0841aa11d04883641409504d02802a05e003954038e520a39683d1c147ae701ba8e1c6c83761b1a946cc6a3428d5cd0335, 0xe2b10ac57c430d588ec3442b0da0ed8451dbe1182ac276023059814e560353a98aa77a629554cea4452b2928caa46a3511546f4450aa89d428a550b41e280a3c7, 0x5a8ed2469b34b44ad26d16815a2fa067ab41d9c8cf66766959cd9aec2b35e0e99851d3e6196acc765232d99592565364b20ac97c831d590ec6463b31b14ac66, 0x2e16706f95c0dbee42b7de01dbc50736f374ade7dd3715baedc6dab719b7b456db6d364ada7d93615b2ed86bab619afac56bb6b3a0ad67807ea941edaad42b55f50d35, 0x300df32835bcde4579bf91e2af277823c59e1c6578371b88ae37e23855c4ee04]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked59 : FrogCheck.check 51 3 8 (FrogCheck.rows 8 data59) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data60 : List ℕ := [0x171f6695b769956999c1596c26561e649537491549918151680e541ce194771855198521456228511e8db357659e8d55947, 0x63e795f779d5799de15d6e365]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked60 : FrogCheck.check 55 2 5 (FrogCheck.rows 5 data60) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data61 : List ℕ := [0x1719bd15b6d32569f26159761556195a1556a22551e241517407541873147630a519ca1145711251192d5b5775992d4dd26, 0x61ff15f6f3a579fa715d771b5]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked61 : FrogCheck.check 56 2 5 (FrogCheck.rows 5 data61) = true := by decide +kernel
end FrogFinite
namespace FrogFinite
def data62 : List ℕ := [0x175f86d5c7691b66b2569b2c1597c13561d244d92895268a0545e0195071855198521456228511e8db357659e8d55947, 0x1839f51dde47d9ee95e6eb85]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 12000000 in
theorem checked62 : FrogCheck.check 57 2 5 (FrogCheck.rows 5 data62) = true := by decide +kernel
end FrogFinite

namespace FrogFinite
open OMA.S_mo_370694 FrogBand

theorem through62 (h k : ℕ) (kh : k≤h) (bound : k≤62) (ne : k≠2) :
    Relation.ReflTransGen (Move h) (core h k) (fun v => if v.val=0 then 2^(h+1)-1 else 0) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have step (b z L : ℕ) (w : List ℕ) (hk : k=b+L) (hb : 0<b) (zl : z≤L)
        (neq : b+z-1≠2) (cert : FrogCheck.check b z L (FrogCheck.rows L w)=true) :
        Relation.ReflTransGen (Move h) (core h k) (fun v => if v.val=0 then 2^(h+1)-1 else 0) := by
      have less : b+z-1<k := by omega
      have run := verified hb (show b+L≤h by omega) zl _ cert
      rw [←hk] at run
      exact run.trans (ih _ less (by omega) (by omega) neq)
    match k with
    | 0 => exact FrogCore.finish_of_solved kh FrogExamples.height0
    | 1 => exact FrogCore.finish_of_solved kh FrogExamples.height1
    | 2 => exact (ne rfl).elim
    | 3 => exact step 2 0 1 _ rfl (by decide) (by decide) (by decide) checked3
    | 4 => exact step 2 0 2 _ rfl (by decide) (by decide) (by decide) checked4
    | 5 => exact step 2 0 3 _ rfl (by decide) (by decide) (by decide) checked5
    | 6 => exact step 4 1 2 _ rfl (by decide) (by decide) (by decide) checked6
    | 7 => exact step 5 1 2 _ rfl (by decide) (by decide) (by decide) checked7
    | 8 => exact step 6 0 2 _ rfl (by decide) (by decide) (by decide) checked8
    | 9 => exact step 6 0 3 _ rfl (by decide) (by decide) (by decide) checked9
    | 10 => exact step 7 0 3 _ rfl (by decide) (by decide) (by decide) checked10
    | 11 => exact step 7 0 4 _ rfl (by decide) (by decide) (by decide) checked11
    | 12 => exact step 9 2 3 _ rfl (by decide) (by decide) (by decide) checked12
    | 13 => exact step 10 2 3 _ rfl (by decide) (by decide) (by decide) checked13
    | 14 => exact step 11 1 3 _ rfl (by decide) (by decide) (by decide) checked14
    | 15 => exact step 12 0 3 _ rfl (by decide) (by decide) (by decide) checked15
    | 16 => exact step 13 0 3 _ rfl (by decide) (by decide) (by decide) checked16
    | 17 => exact step 14 0 3 _ rfl (by decide) (by decide) (by decide) checked17
    | 18 => exact step 15 0 3 _ rfl (by decide) (by decide) (by decide) checked18
    | 19 => exact step 13 1 6 _ rfl (by decide) (by decide) (by decide) checked19
    | 20 => exact step 14 1 6 _ rfl (by decide) (by decide) (by decide) checked20
    | 21 => exact step 16 2 5 _ rfl (by decide) (by decide) (by decide) checked21
    | 22 => exact step 17 0 5 _ rfl (by decide) (by decide) (by decide) checked22
    | 23 => exact step 18 0 5 _ rfl (by decide) (by decide) (by decide) checked23
    | 24 => exact step 19 4 5 _ rfl (by decide) (by decide) (by decide) checked24
    | 25 => exact step 20 4 5 _ rfl (by decide) (by decide) (by decide) checked25
    | 26 => exact step 20 3 6 _ rfl (by decide) (by decide) (by decide) checked26
    | 27 => exact step 21 3 6 _ rfl (by decide) (by decide) (by decide) checked27
    | 28 => exact step 21 0 7 _ rfl (by decide) (by decide) (by decide) checked28
    | 29 => exact step 21 3 8 _ rfl (by decide) (by decide) (by decide) checked29
    | 30 => exact step 25 2 5 _ rfl (by decide) (by decide) (by decide) checked30
    | 31 => exact step 26 2 5 _ rfl (by decide) (by decide) (by decide) checked31
    | 32 => exact step 27 2 5 _ rfl (by decide) (by decide) (by decide) checked32
    | 33 => exact step 28 2 5 _ rfl (by decide) (by decide) (by decide) checked33
    | 34 => exact step 29 0 5 _ rfl (by decide) (by decide) (by decide) checked34
    | 35 => exact step 30 0 5 _ rfl (by decide) (by decide) (by decide) checked35
    | 36 => exact step 29 4 7 _ rfl (by decide) (by decide) (by decide) checked36
    | 37 => exact step 30 2 7 _ rfl (by decide) (by decide) (by decide) checked37
    | 38 => exact step 31 2 7 _ rfl (by decide) (by decide) (by decide) checked38
    | 39 => exact step 30 2 9 _ rfl (by decide) (by decide) (by decide) checked39
    | 40 => exact step 31 2 9 _ rfl (by decide) (by decide) (by decide) checked40
    | 41 => exact step 32 2 9 _ rfl (by decide) (by decide) (by decide) checked41
    | 42 => exact step 36 3 6 _ rfl (by decide) (by decide) (by decide) checked42
    | 43 => exact step 37 1 6 _ rfl (by decide) (by decide) (by decide) checked43
    | 44 => exact step 38 1 6 _ rfl (by decide) (by decide) (by decide) checked44
    | 45 => exact step 37 5 8 _ rfl (by decide) (by decide) (by decide) checked45
    | 46 => exact step 37 4 9 _ rfl (by decide) (by decide) (by decide) checked46
    | 47 => exact step 38 4 9 _ rfl (by decide) (by decide) (by decide) checked47
    | 48 => exact step 43 4 5 _ rfl (by decide) (by decide) (by decide) checked48
    | 49 => exact step 44 4 5 _ rfl (by decide) (by decide) (by decide) checked49
    | 50 => exact step 43 4 7 _ rfl (by decide) (by decide) (by decide) checked50
    | 51 => exact step 42 6 9 _ rfl (by decide) (by decide) (by decide) checked51
    | 52 => exact step 44 3 8 _ rfl (by decide) (by decide) (by decide) checked52
    | 53 => exact step 45 3 8 _ rfl (by decide) (by decide) (by decide) checked53
    | 54 => exact step 47 0 7 _ rfl (by decide) (by decide) (by decide) checked54
    | 55 => exact step 48 0 7 _ rfl (by decide) (by decide) (by decide) checked55
    | 56 => exact step 47 4 9 _ rfl (by decide) (by decide) (by decide) checked56
    | 57 => exact step 48 6 9 _ rfl (by decide) (by decide) (by decide) checked57
    | 58 => exact step 50 3 8 _ rfl (by decide) (by decide) (by decide) checked58
    | 59 => exact step 51 3 8 _ rfl (by decide) (by decide) (by decide) checked59
    | 60 => exact step 55 2 5 _ rfl (by decide) (by decide) (by decide) checked60
    | 61 => exact step 56 2 5 _ rfl (by decide) (by decide) (by decide) checked61
    | 62 => exact step 57 2 5 _ rfl (by decide) (by decide) (by decide) checked62
    | _+63 => omega
end FrogFinite

/- A packet occupies a finite set of local types. Forms records how
to gather it at a chosen host starting with a single frog on each type, while
preserving the rest of the board. Disjoint packets can subsequently be merged. -/
namespace FrogPacket
open OMA.S_mo_370694 FrogModel Finset
variable {h : ℕ} {G T : Type} [Fintype G] [DecidableEq T]

def joined (b : Option T → ℕ) (S : Finset T) (i : T) (n : ℕ) : Option T → ℕ
  | none => b none
  | some t => if t∈S then if t=i then n else 0 else b (some t)

def Forms (F : Frame h G T) (S : Finset T) (i : T) (n : ℕ) : Prop :=
  i ∈ S ∧ 0<n ∧ ∀ base b, (∀ t ∈ S, b (some t)=1) →
    Relation.ReflTransGen (Move h) (paint F base b) (paint F base (joined b S i n))

theorem single (F : Frame h G T) (i : T) : Forms F {i} i 1 := by
  refine ⟨by simp,by decide,?_⟩
  intro base b one
  have eq : joined b {i} i 1 = b := by
    funext t
    cases t with
    | none => rfl
    | some t =>
      by_cases e : t=i
      · subst t; simpa [joined] using (one i (by simp)).symm
      · simp [joined,e]
  rw [eq]

theorem merge (F : Frame h G T) {S U : Finset T} {i j : T} {m n : ℕ}
    (fs : Forms F S i m) (fu : Forms F U j n) (dis : Disjoint S U)
    (geom : ∃ p : G ≃ G, ∀ g, (binaryTree h).dist (F.site (g,i)) (F.site (p g,j))=m) :
    Forms F (S∪U) j (m+n) := by
  rcases fs with ⟨hi,hm,buildS⟩
  rcases fu with ⟨hj,hn,buildU⟩
  have nj : j ∉ S := fun he => disjoint_left.mp dis he hj
  have ni : i ∉ U := fun he => disjoint_left.mp dis hi he
  have ne : i≠j := fun e => nj (e ▸ hi)
  refine ⟨mem_union_right _ hj,by omega,?_⟩
  intro base b one
  have runS := buildS base b (fun a ha => one a (mem_union_left _ ha))
  let b1 := joined b S i m
  have runU := buildU base b1 (by
    intro a ha
    have ex : a ∉ S := fun hs => disjoint_left.mp dis hs ha
    simpa [b1,joined,ex] using one a (mem_union_right _ ha))
  let b2 := joined b1 U j n
  have bi : b2 (some i)=m := by simp [b2,b1,joined,hi,ni]
  have bj : b2 (some j)=n := by simp [b2,joined,hj]
  rcases geom with ⟨p,hp⟩
  have run := internal F base b2 i j ne p (by omega) (by omega) (fun g => (hp g).trans bi.symm)
  have finish : update b2 i (some j) = joined b (S∪U) j (m+n) := by
    funext a
    cases a with
    | none => rfl
    | some t =>
      by_cases ei : t=i
      · subst t; simp [update,joined,hi,ne]
      by_cases ej : t=j
      · subst t; simp [update,joined,hj,ei,bi,bj,Nat.add_comm]
      by_cases eu : t ∈ U
      · simp [update,b2,b1,joined,eu,ei,ej]
      · by_cases es : t ∈ S <;> simp [update,b2,b1,joined,eu,es,ei,ej]
  rw [finish] at run
  exact (runS.trans runU).trans run
end FrogPacket

/- Partition the six bottom levels into cherries, each consisting of
one parent and its two children. Their frog mass is three, and it can be gathered
at either the parent or its left child. This choice controls the depth parity. -/

namespace FrogCherry
open OMA.S_mo_370694 FrogBand FrogPacket FrogLabels Finset

abbrev Index (z : ℕ) := Fin (2^(z+4)) ⊕ (Fin (2^(z+2)) ⊕ Fin (2^z))
abbrev T (z : ℕ) := Slot z (z+5)

def depth {z : ℕ} : Index z → ℕ
  | .inl _ => z+4
  | .inr (.inl _) => z+2
  | .inr (.inr _) => z

def number {z : ℕ} : Index z → ℕ
  | .inl g => g.val
  | .inr (.inl g) => g.val
  | .inr (.inr g) => g.val

def parent {z : ℕ} (c : Index z) := 2^(depth c) + number c

theorem numberLt {z : ℕ} (c : Index z) : number c < 2^(depth c) := by
  rcases c with c | c
  · exact c.isLt
  · rcases c with c | c <;> exact c.isLt

theorem parentDepth {z : ℕ} (c : Index z) : (parent c).log2 = depth c := by
  have hn := numberLt c
  have hp : 0<2^(depth c) := by positivity
  apply (Nat.log2_eq_iff (by unfold parent; omega)).mpr
  unfold parent; rw [pow_succ]; omega

theorem parentRange {z : ℕ} (c : Index z) : 2^z ≤ parent c ∧ 2*parent c+1 < 2^(z+5+1) := by
  have dl : z ≤ depth c ∧ depth c ≤ z+4 := by rcases c with c | c; simp [depth]; rcases c with c | c <;> simp [depth]
  have h1 := Nat.pow_le_pow_right (by decide : 0<2) dl.1
  have h2 := Nat.pow_le_pow_right (by decide : 0<2) dl.2
  have hn := numberLt c
  change _ ∧ _ < 2^((z+4)+2)
  rw [pow_add (2:ℕ) (z+4) 2]
  unfold parent; omega

def center {z : ℕ} (c : Index z) : T z := ⟨parent c,(parentRange c).1,by have := (parentRange c).2; omega⟩
def child {z : ℕ} (c : Index z) (right : Bool) : T z :=
  ⟨2*parent c+right.toNat,by have := (parentRange c).1; omega,by
    have := (parentRange c).2; cases right <;> simp_all <;> omega⟩

def head {z : ℕ} (c : Index z) (leaf : Bool) : T z := if leaf then child c false else center c
def vertices {z : ℕ} (c : Index z) : Finset (T z) := {center c,child c false,child c true}

theorem childDepth {z : ℕ} (c : Index z) (right : Bool) : (child c right).val.log2 = depth c+1 := by
  have hl := Nat.log2_self_le (show parent c≠0 by
    have := (parentRange c).1; have hz : 0<2^z := by positivity
    omega)
  have hu := Nat.lt_log2_self (n:=parent c)
  rw [parentDepth] at hl hu
  have hp : 0<2^(depth c) := by positivity
  change (2*parent c+right.toNat).log2=depth c+1
  have hr : right.toNat ≤ 1 := by cases right <;> decide
  apply (Nat.log2_eq_iff (by omega)).mpr
  rw [pow_succ] at hu
  rw [pow_succ (2:ℕ) (depth c+1),pow_succ]; omega

theorem headDepth {z : ℕ} (c : Index z) (leaf : Bool) :
    (head c leaf).val.log2 = depth c+leaf.toNat := by
  cases leaf
  · simpa [head,center] using parentDepth c
  · simpa [head] using childDepth c false

theorem localGeom {h b z L : ℕ} (hb : 0<b) (bh : b+L≤h) {i j : Slot z L} {n : ℕ}
    (he : FrogDistance.steps i.val j.val=n ∨ Cross b i.val j.val n) :
    let F := frame (z:=z) hb bh
    ∃ p : Groups b ≃ Groups b, ∀ g, (binaryTree h).dist (F.site (g,i)) (F.site (p g,j))=n := by
  obtain ⟨p,hp⟩ := matchDistance (slotBounds i).1 (slotBounds j).1 he
  refine ⟨p,fun g => ?_⟩
  change (binaryTree h).dist (point bh g i) (point bh (p g) j) = n
  rw [FrogDistance.distance,point_label,point_label]
  exact hp g

theorem three {h b z : ℕ} (hb : 0<b) (bh : b+(z+5)≤h) (c : Index z) (leaf : Bool) :
    Forms (frame hb bh) (vertices c) (head c leaf) 3 := by
  let F := frame (z:=z) hb bh
  let u := center c
  let l := child c false
  let r := child c true
  have hp : 0<parent c := lt_of_lt_of_le (by positivity : 0<2^z) (parentRange c).1
  have hlu : l ≠ u := fun eq => by
    have he := congrArg Subtype.val eq
    change 2*parent c+0=parent c at he; omega
  have hru : r ≠ u := fun eq => by
    have he := congrArg Subtype.val eq
    change 2*parent c+1=parent c at he; omega
  have hrl : r ≠ l := fun eq => by
    have he := congrArg Subtype.val eq
    change 2*parent c+1=2*parent c+0 at he; omega
  have halfL : l.val/2=u.val := by change (2*parent c+0)/2=parent c; omega
  have halfR : r.val/2=u.val := by change (2*parent c+1)/2=parent c; omega
  have ul : u.val<l.val := by change parent c<2*parent c+0; omega
  have ur : u.val<r.val := by change parent c<2*parent c+1; omega
  have lr : l.val<r.val := by change 2*parent c+0<2*parent c+1; omega
  have toL : FrogDistance.steps u.val l.val=1 := by rw [FrogDistance.right ul,halfL,FrogDistance.self]
  have toR : FrogDistance.steps u.val r.val=1 := by rw [FrogDistance.right ur,halfR,FrogDistance.self]
  cases leaf
  · have first := merge F (single F l) (single F u) (by simpa using hlu)
      (localGeom hb bh (Or.inl (by rw [FrogDistance.symmetric]; exact toL)))
    have groups := merge F (single F r) first (by simp [hrl,hru])
      (localGeom hb bh (Or.inl (by rw [FrogDistance.symmetric]; exact toR)))
    have eq : {r}∪({l}∪{u})=vertices c := by ext x; simp [vertices,u,l,r]; tauto
    simpa only [head,Bool.false_eq_true,if_false,eq] using groups
  · have first := merge F (single F u) (single F r) (by simpa using Ne.symm hru)
      (localGeom hb bh (Or.inl toR))
    have across : FrogDistance.steps r.val l.val=2 := by rw [FrogDistance.left lr,halfR,toL]
    have groups := merge F first (single F l) (by simp [hlu,Ne.symm hrl])
      (localGeom hb bh (Or.inl across))
    have eq : ({u}∪{r})∪{l}=vertices c := by ext x; simp [vertices,u,l,r]; tauto
    simpa only [head,if_true,eq] using groups
end FrogCherry


namespace FrogCherry
open OMA.S_mo_370694 FrogBand FrogPacket FrogLabels Finset

theorem depthEven {z : ℕ} (c : Index z) : depth c % 2 = z % 2 := by
  rcases c with c | (c | c) <;> simp only [depth] <;> omega

theorem parentInj {z : ℕ} : Function.Injective (@parent z) := by
  intro c d he
  have hd : depth c = depth d := by simpa only [parentDepth] using congrArg Nat.log2 he
  have hn : number c = number d := by unfold parent at he; rw [hd] at he; omega
  rcases c with c | (c | c) <;> rcases d with d | (d | d) <;>
    simp only [depth,number] at hd hn <;> first | omega | congr 1 <;> first | exact Fin.ext hn | congr 1; exact Fin.ext hn

theorem owner {z : ℕ} {c : Index z} {v : T z} (hv : v∈vertices c) :
    (if v.val.log2%2=z%2 then v.val else v.val/2) = parent c := by
  have par := depthEven c
  simp only [vertices,mem_insert,mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · change (if (parent c).log2%2=z%2 then _ else _) = _
    rw [parentDepth,if_pos par]; rfl
  · rw [childDepth,if_neg (by omega)]
    change (2*parent c+0)/2=parent c; omega
  · rw [childDepth,if_neg (by omega)]
    change (2*parent c+1)/2=parent c; omega

theorem separate {z : ℕ} {c d : Index z} (hne : c≠d) : Disjoint (vertices c) (vertices d) := by
  intro S hc hd
  intro a ha
  exact (hne (parentInj ((owner (hc ha)).symm.trans (owner (hd ha))))).elim

def places {z : ℕ} (S : Finset (Index z)) := S.biUnion vertices

theorem placesSep {z : ℕ} {S U : Finset (Index z)} (hd : Disjoint S U) :
    Disjoint (places S) (places U) := by
  apply disjoint_left.mpr
  intro a h1 h2
  obtain ⟨c,hc,ac⟩ := mem_biUnion.mp h1
  obtain ⟨d,he,ad⟩ := mem_biUnion.mp h2
  exact disjoint_left.mp hd hc ((parentInj ((owner ac).symm.trans (owner ad))).symm ▸ he)

theorem placesUnion {z : ℕ} (S U : Finset (Index z)) :
    places (S∪U)=places S∪places U := Finset.union_biUnion

theorem covers {z : ℕ} (v : T z) : ∃ c : Index z, v∈vertices c := by
  let d := v.val.log2
  have lo : z ≤ d := (slotBounds v).2.1
  have hi : d ≤ z+5 := (slotBounds v).2.2
  have left := Nat.log2_self_le (show v.val≠0 from (slotBounds v).1.ne')
  have right := Nat.lt_log2_self (n:=v.val)
  change 2^d≤v.val at left
  change v.val<2^(d+1) at right
  have atLevel (e : ℕ) (f : Fin (2^e) → Index z) (hf : ∀ a, parent (f a)=2^e+a.val)
      (ed : d=e ∨ d=e+1) : ∃ c : Index z, v∈vertices c := by
    rcases ed with he | he
    · subst e
      rw [pow_succ (2:ℕ) d] at right
      let a : Fin (2^d) := ⟨v.val-2^d,by omega⟩
      refine ⟨f a, ?_⟩
      have eq : v=center (f a) := Subtype.ext (by
        change v.val=parent (f a); rw [hf]; dsimp [a]; omega)
      simp [vertices,eq]
    · rw [he,pow_succ (2:ℕ) e] at left
      rw [he,pow_succ (2:ℕ) (e+1),pow_succ (2:ℕ) e] at right
      let a : Fin (2^e) := ⟨v.val/2-2^e,by omega⟩
      have half : parent (f a) = v.val/2 := by rw [hf]; dsimp [a]; omega
      refine ⟨f a,?_⟩
      by_cases ev : v.val%2=0
      · have eq : v=child (f a) false := Subtype.ext (by change v.val=2*parent (f a)+0; rw [half]; omega)
        simp [vertices,eq]
      · have eq : v=child (f a) true := Subtype.ext (by change v.val=2*parent (f a)+1; rw [half]; omega)
        simp [vertices,eq]
  by_cases bot : z+4≤d
  · exact atLevel (z+4) Sum.inl (fun _ => rfl) (by omega)
  by_cases mid : z+2≤d
  · exact atLevel (z+2) (fun a => .inr (.inl a)) (fun _ => rfl) (by omega)
  · exact atLevel z (fun a => .inr (.inr a)) (fun _ => rfl) (by omega)

end FrogCherry

namespace FrogSeed
open OMA.S_mo_370694 FrogBand FrogCherry FrogPacket FrogModel Finset

variable {h b z : ℕ} {F : Frame h (Groups b) (T z)}

structure Seed (F : Frame h (Groups b) (T z)) (e : ℕ) (leaf : Bool) where
  trees : Finset (Index z)
  c : Index z
  member : c∈trees
  size : trees.card = 2^e
  forms : Forms F (places trees) (head c leaf) (3*2^e)

def Inside (p D : ℕ) (c : Index z) : Prop :=
  depth c=z+4 ∧ p*2^D ≤ parent c ∧ parent c < (p+1)*2^D

theorem halves (p D : ℕ) {c : Index z} :
    (Inside (2*p) D c ∨ Inside (2*p+1) D c) → Inside p (D+1) c := by
  simp only [Inside,pow_succ]
  rcases Nat.eq_zero_or_pos (2^D) with hx|hx <;> intro ha <;>
    rcases ha with ⟨hd,hl,hu⟩|⟨hd,hl,hu⟩ <;> exact ⟨hd,by nlinarith,by nlinarith⟩

theorem splitSep (p D : ℕ) {S U : Finset (Index z)}
    (ls : ∀ c∈S,Inside (2*p) D c) (rs : ∀ c∈U,Inside (2*p+1) D c) : Disjoint S U := by
  apply disjoint_left.mpr
  intro c h1 h2
  exact (ls c h1).2.2.not_ge (rs c h2).2.1

theorem insideDist {p D : ℕ} {c d : Index z} (hp : 0<p) (l : Inside (2*p) D c)
    (r : Inside (2*p+1) D d) (u v : Bool) :
    FrogDistance.steps (head c u).val (head d v).val = (D+u.toNat)+(D+v.toNat)+2 := by
  obtain ⟨_,cl,cr⟩ := l
  obtain ⟨_,dl,dr⟩ := r
  have scale (c : Index z) (a : Bool) : (head c a).val=parent c*2^a.toNat := by
    cases a <;> simp [head,center,child,Nat.mul_comm]
  rw [scale,scale]
  apply FrogDistance.fork p (D+u.toNat) (D+v.toNat) _ _ hp
  · rw [pow_add,←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ cl
  · rw [pow_add,←Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right cr (by positivity)
  · rw [pow_add,←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ dl
  · rw [pow_add,←Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right dr (by positivity)

structure Pool (F : Frame h (Groups b) (T z)) (D e p : ℕ) (leaf : Bool) where
  row : Fin (2^(D-e)) → Seed F e leaf
  inside : ∀ i c, c∈(row i).trees → Inside p D c
  apart : ∀ i j, i≠j → Disjoint (row i).trees (row j).trees

theorem singletonPool (hb : 0<b) (bh : b+(z+5)≤h)
    (p : ℕ) (l : 2^(z+4)≤p) (r : p<2^(z+5)) (w : Bool) :
    Nonempty (Pool (frame hb bh) 0 0 p w) := by
  have rp : p<2^(z+4)*2 := by simpa only [pow_succ (2:ℕ) (z+4)] using r
  let a : Fin (2^(z+4)) := ⟨p-2^(z+4),by omega⟩
  let c : Index z := Sum.inl a
  have idp : parent c=p := by change 2^(z+4)+(p-2^(z+4))=p; omega
  let s : Seed (frame hb bh) 0 w := ⟨{c},c,by simp,by simp,
    by simpa [places] using three hb bh c w⟩
  refine ⟨⟨fun _ => s,?_,?_⟩⟩
  · intro i d hd
    have eq : d=c := mem_singleton.mp hd
    subst d; exact ⟨rfl,by simp [idp],by simp [idp]⟩
  · intro i j ne
    exact (ne (show i=j from Fin.ext (by have hi := i.isLt; have hj := j.isLt; change i.val<1 at hi; change j.val<1 at hj; omega))).elim

noncomputable def widen {p D e : ℕ} {w : Bool} (de : e≤D)
    (A : Pool F D e (2*p) w) (B : Pool F D e (2*p+1) w) :
    Pool F (D+1) e p w := by
  let n := 2^(D-e)
  let split : (Fin n ⊕ Fin n) ≃ Fin (2^(D+1-e)) := finSumFinEquiv.trans (finCongr (by
    rw [show D+1-e=D-e+1 by omega,pow_succ]; dsimp [n]; omega))
  let row : (Fin n ⊕ Fin n) → Seed F e w := Sum.elim A.row B.row
  refine ⟨fun i => row (split.symm i),?_,?_⟩
  · intro i c hc
    cases hi : split.symm i with
    | inl a => rw [hi] at hc; exact halves p D (Or.inl (A.inside _ _ hc))
    | inr a => rw [hi] at hc; exact halves p D (Or.inr (B.inside _ _ hc))
  · intro i j hn
    have ne : split.symm i≠split.symm j := fun e => hn (split.symm.injective e)
    cases hi : split.symm i <;> cases hj : split.symm j <;> simp only [hi,hj] at ne
    · exact A.apart _ _ (fun e => ne (congrArg Sum.inl e))
    · exact splitSep p D (A.inside _) (B.inside _)
    · exact (splitSep p D (A.inside _) (B.inside _)).symm
    · exact B.apart _ _ (fun e => ne (congrArg Sum.inr e))

noncomputable def double (hb : 0<b) (bh : b+(z+5)≤h) {p D e : ℕ} {u w : Bool}
    (hp : 0<p) (dist : (D+u.toNat)+(D+w.toNat)+2=3*2^e)
    (A : Pool (frame hb bh) D e (2*p) u) (B : Pool (frame hb bh) D e (2*p+1) w) :
    Pool (frame hb bh) (D+1) (e+1) p w := by
  have dis (i j) := splitSep p D (A.inside i) (B.inside j)
  let row (i : Fin (2^(D-e))) : Seed (frame hb bh) (e+1) w :=
    ⟨(A.row i).trees∪(B.row i).trees, (B.row i).c, mem_union_right _ (B.row i).member,
      by rw [card_union_of_disjoint (dis i i),(A.row i).size,(B.row i).size,pow_succ]; omega,
      by
        rw [placesUnion]
        have geom := (insideDist hp (A.inside i _ (A.row i).member) (B.inside i _ (B.row i).member) u w).trans dist
        have joined := merge _ (A.row i).forms (B.row i).forms (placesSep (dis i i)) (localGeom hb bh (Or.inl geom))
        simpa only [show 3*2^(e+1)=3*2^e+3*2^e by rw [pow_succ]; omega] using joined⟩
  have eq : (D+1)-(e+1)=D-e := by omega
  let conv := finCongr (congrArg (2^·) eq)
  refine ⟨fun i => row (conv i),?_,?_⟩
  · intro i c hi
    rcases mem_union.mp hi with hc|hc
    · exact halves p D (Or.inl (A.inside _ _ hc))
    · exact halves p D (Or.inr (B.inside _ _ hc))
  · intro i j hn
    have ne : conv i≠conv j := fun e => hn (conv.injective e)
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨A.apart _ _ ne,dis _ _⟩,
      disjoint_union_right.mpr ⟨(dis _ _).symm,B.apart _ _ ne⟩⟩
end FrogSeed

/- Dyadically aligned blocks of bottom cherries supply disjoint seeds.
When two equal packets merge, their hosts lie in the two halves of the current
block. Its depth is chosen so their distance equals the moving packet's mass.
At other depths the independent pools in the two halves are simply combined. -/

namespace FrogSeed
open OMA.S_mo_370694 FrogBand FrogCherry FrogModel

def need : ℕ → Bool → ℕ
  | 0, _ => 0
  | 1, _ => 1
  | e+2, w => 3*2^e-w.toNat

theorem needGrow (e : ℕ) (w : Bool) : need e w < need (e+1) w := by
  obtain _|_|e := e
  · cases w <;> decide
  · cases w <;> decide
  · have pos : 0<2^e := by positivity
    change 3*2^e-w.toNat<3*2^(e+1)-w.toNat
    rw [pow_succ]; have le : w.toNat≤1 := by cases w <;> decide
    omega

theorem needBound (e : ℕ) (w : Bool) : e≤need e w := by
  induction e with
  | zero => exact Nat.zero_le _
  | succ e ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (needGrow e w))

theorem makePool {h b z : ℕ} (hb : 0<b) (bh : b+(z+5)≤h) (D e p : ℕ) (w : Bool)
    (en : need e w≤D) (lo : 2^(z+4)≤p*2^D) (hi : (p+1)*2^D≤2^(z+5)) :
    Nonempty (Pool (frame hb bh) D e p w) := by
  induction D generalizing e p w with
  | zero =>
    have ee := needBound e w
    have ez : e=0 := by omega
    subst e
    exact singletonPool hb bh p (by simpa using lo) (by simpa using hi) w
  | succ D ih =>
    have leftEq : (2*p)*2^D=p*2^(D+1) := by rw [pow_succ]; ring
    have rightEq : ((2*p+1)+1)*2^D=(p+1)*2^(D+1) := by rw [pow_succ]; ring
    have low : 2^(z+4)≤(2*p)*2^D := leftEq.symm ▸ lo
    have up : ((2*p+1)+1)*2^D≤2^(z+5) := rightEq.symm ▸ hi
    have mid : (2*p+1)*2^D≤2^(z+5) := (Nat.mul_le_mul_right _ (by omega : 2*p+1≤2*p+1+1)).trans up
    have mid' : 2^(z+4)≤(2*p+1)*2^D := low.trans (Nat.mul_le_mul_right _ (by omega))
    have pp : 0<p := by by_contra! hz; simp [Nat.le_zero.mp hz] at lo
    by_cases smaller : need e w≤D
    · obtain ⟨A⟩ := ih e (2*p) w smaller low mid
      obtain ⟨B⟩ := ih e (2*p+1) w smaller mid' up
      exact ⟨widen ((needBound e w).trans smaller) A B⟩
    · have fixed : D+1=need e w := by omega
      cases e with
      | zero => simp [need] at smaller
      | succ e =>
        cases e with
        | zero =>
          have D0 : D=0 := by simpa [need] using fixed
          obtain ⟨A⟩ := ih 0 (2*p) (!w) (by simp [need]) low mid
          obtain ⟨B⟩ := ih 0 (2*p+1) w (by simp [need]) mid' up
          exact ⟨double hb bh pp (by subst D; cases w <;> decide) A B⟩
        | succ e =>
          have less : need (e+1) w≤D := by have := needGrow (e+1) w; omega
          obtain ⟨A⟩ := ih (e+1) (2*p) w less low mid
          obtain ⟨B⟩ := ih (e+1) (2*p+1) w less mid' up
          have length : (D+w.toNat)+(D+w.toNat)+2=3*2^(e+1) := by
            have positive : 0<2^e := by positivity
            cases w <;> simp only [need,Bool.toNat,pow_succ] at fixed ⊢ <;> omega
          exact ⟨double hb bh pp length A B⟩
end FrogSeed

namespace FrogSeed
open OMA.S_mo_370694 FrogBand FrogCherry FrogModel Finset

theorem needPow (e : ℕ) (w : Bool) : need e w≤2^e := by
  obtain _|_|e := e
  · cases w <;> decide
  · cases w <;> decide
  · simp only [need,pow_succ]; omega

theorem select {h b z : ℕ} (hb : 0<b) (bh : b+(z+5)≤h) (e M : ℕ) (w : Fin M → Bool)
    (enough : ∀ f, need e f≤z+3) (cap : 2^e*M≤8*2^z) :
    ∃ s : (i : Fin M) → Seed (frame hb bh) e (w i),
      (∀ i j, i≠j → Disjoint (s i).trees (s j).trees) ∧
      (∀ i c, c∈(s i).trees → depth c=z+4) := by
  have bound : e≤z+3 := (needBound e false).trans (enough false)
  have le : M≤2^(z+3-e) := by
    apply Nat.le_of_mul_le_mul_left (c:=2^e) _ (Nat.two_pow_pos e)
    rw [←pow_add,show e+(z+3-e)=z+3 by omega,pow_add]
    simpa [Nat.mul_comm] using cap
  let index (i : Fin M) : Fin (2^(z+3-e)) := ⟨i.val,i.isLt.trans_le le⟩
  have inj : Function.Injective index := fun i j he => Fin.ext (congrArg (fun a : Fin (2^(z+3-e)) => a.val) he)
  obtain ⟨A⟩ := makePool hb bh (z+3) e 2 false (enough false)
    (by rw [show z+4=z+3+1 by omega,pow_succ]; omega)
    (by rw [show z+5=z+3+2 by omega,pow_add (2:ℕ) (z+3) 2]; omega)
  obtain ⟨B⟩ := makePool hb bh (z+3) e 3 true (enough true)
    (by rw [show z+4=z+3+1 by omega,pow_succ]; omega)
    (by rw [show z+5=z+3+2 by omega,pow_add (2:ℕ) (z+3) 2]; omega)
  let get (v : Bool) (i : Fin M) : Seed (frame hb bh) e v :=
    match v with | false => A.row (index i) | true => B.row (index i)
  have apart (vi vj : Bool) (i j : Fin M) (hn : i≠j) :
      Disjoint (get vi i).trees (get vj j).trees := by
    have ne : index i≠index j := fun he => hn (inj he)
    cases vi <;> cases vj
    · exact A.apart _ _ ne
    · exact splitSep 1 (z+3) (A.inside _) (B.inside _)
    · exact (splitSep 1 (z+3) (A.inside _) (B.inside _)).symm
    · exact B.apart _ _ ne
  have bottom (v : Bool) (i : Fin M) (c : Index z) (hc : c∈(get v i).trees) : depth c=z+4 := by
    cases v
    · exact (A.inside _ _ hc).1
    · exact (B.inside _ _ hc).1
  exact ⟨fun i => get (w i) i,fun i j hn => apart _ _ i j hn,fun i c hc => bottom _ i c hc⟩
end FrogSeed

/- After a seed is large enough, its mass exceeds twice the height
of the local template. Successive jumps can then reach a fresh cherry of any
type by choosing the host parity and permuting the copies. The parity recursion
works backward from the required terminal depth. -/
namespace FrogChain
open OMA.S_mo_370694 FrogBand FrogCherry FrogPacket FrogModel Finset

def want (i t p : ℕ) : ℕ := match t with
  | 0 => p%2
  | t+1 => (want (i+1) t p + 3*i)%2

theorem wantLt (i t p : ℕ) : want i t p<2 := by cases t <;> exact Nat.mod_lt _ (by decide)

def leafFor (d p : ℕ) : Bool := decide (d%2≠p%2)

theorem selected (d p : ℕ) : (d+(leafFor d p).toNat)%2=p%2 := by
  by_cases he : d%2=p%2 <;> simp [leafFor,he] <;> omega

theorem extend {h b z m : ℕ} (hb : 0<b) (bh : b+(z+5)≤h) {S : Finset (Index z)}
    {i : T z} (start : Forms (frame hb bh) (places S) i (3*m))
    (c : Index z) (w : Bool) (new : c∉S)
    (low : 2*(z+5)+2≤3*m) (high : 3*m≤b+(z+5)) (deep : 3<b+z)
    (par : i.val.log2%2=((head c w).val.log2+3*m)%2) :
    Forms (frame hb bh) (places (S∪{c})) (head c w) (3*(m+1)) := by
  have a := (slotBounds i).2
  have j := (slotBounds (head c w)).2
  have route : Cross b i.val (head c w).val (3*m) := by
    unfold Cross
    exact ⟨by omega,by omega,by omega⟩
  have one : Forms (frame hb bh) (places {c}) (head c w) 3 := by simpa [places] using three hb bh c w
  rw [placesUnion]
  convert merge _ start one (placesSep (by simpa using new)) (localGeom hb bh (Or.inr route)) using 1 <;> omega

theorem build {h b z : ℕ} (hb : 0<b) (bh : b+(z+5)≤h) (deep : 3<b+z)
    (rest : List (Index z)) (terminal : Index z) (w : Bool) (m : ℕ) (S : Finset (Index z)) (i : T z)
    (nodup : rest.Nodup) (fresh : ∀ c∈rest, c∉S) (term : terminal∉S) (unused : terminal∉rest)
    (start : Forms (frame hb bh) (places S) i (3*m)) (low : 2*(z+5)+2≤3*m)
    (high : 3*(m+rest.length+1)≤b+(z+5))
    (par : i.val.log2%2=want m (rest.length+1) (head terminal w).val.log2) :
    Forms (frame hb bh) (places (S∪rest.toFinset∪{terminal})) (head terminal w) (3*(m+rest.length+1)) := by
  induction rest generalizing m S i with
  | nil =>
    simp only [List.length_nil,Nat.add_zero,List.toFinset_nil,union_empty] at *
    exact extend hb bh start terminal w term low (by omega) deep (by simp only [want] at par; omega)
  | cons c cs ih =>
    have nol := List.nodup_cons.mp nodup
    have nc := fresh c (by simp)
    have nt : terminal≠c := by intro e; exact unused (by simp [e])
    let p := want (m+1) (cs.length+1) (head terminal w).val.log2
    let v := leafFor (depth c) p
    have ep : (head c v).val.log2%2=p := by
      rw [headDepth,selected,Nat.mod_eq_of_lt (wantLt ..)]
    have parity : i.val.log2%2=((head c v).val.log2+3*m)%2 := by
      change i.val.log2%2=(p+3*m)%2 at par
      omega
    have move := extend hb bh start c v nc low (by simp only [List.length_cons] at high; omega) deep parity
    have endrun := ih (m+1) (S∪{c}) (head c v) nol.2 (by
      intro a ha
      have hs := fresh a (List.mem_cons_of_mem _ ha)
      have ne : a≠c := fun e => nol.1 (e ▸ ha)
      simp [hs,ne]) (by simp [term,nt]) (fun he => unused (List.mem_cons_of_mem _ he)) move
      (by omega) (by simp only [List.length_cons] at high; omega) ep
    have sets : S∪(c::cs).toFinset∪{terminal} = (S∪{c})∪cs.toFinset∪{terminal} := by
      ext a; simp <;> tauto
    simpa only [sets,List.length_cons,show m+(cs.length+1)+1=m+1+cs.length+1 by omega] using endrun
end FrogChain

namespace FrogCherry
open FrogBand Finset

def eligible {z : ℕ} (d : ℕ) (B : Finset (Index z)) :=
  (univ.filter (fun c : Index z => depth c=d ∨ depth c+1=d)) \ B

theorem room {z d : ℕ} (B : Finset (Index z)) (bot : ∀ c∈B, depth c=z+4)
    (small : B.card≤8*2^z) (lo : z≤d) (hi : d≤z+5) : 2^z≤(eligible d B).card := by
  classical
  have tier (e : ℕ) (f : Fin (2^e) ↪ Index z) (he : ∀ a,depth (f a)=e)
      (atD : e=d ∨ e+1=d) :
      let A := univ.map f
      A \ B ⊆ eligible d B := by
    dsimp only
    intro c hc
    obtain ⟨ha,hn⟩ := mem_sdiff.mp hc
    obtain ⟨i,_,rfl⟩ := mem_map.mp ha
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by simpa [he] using atD⟩,hn⟩
  have freeTier (e : ℕ) (f : Fin (2^e) ↪ Index z) (he : ∀ a,depth (f a)=e)
      (atD : e=d ∨ e+1=d) (ne : e≠z+4) : 2^e≤(eligible d B).card := by
    have dis : Disjoint (univ.map f) B := by
      apply disjoint_left.mpr
      intro a h1 h2; obtain ⟨i,_,rfl⟩ := mem_map.mp h1
      exact ne ((he i).symm.trans (bot _ h2))
    have le := card_le_card (tier e f he atD)
    simpa [sdiff_eq_self_of_disjoint dis] using le
  by_cases hb : z+4≤d
  · let f : Fin (2^(z+4)) ↪ Index z := ⟨Sum.inl,Sum.inl_injective⟩
    have lower := card_le_card (tier (z+4) f (fun _ => rfl) (by omega))
    have count := le_card_sdiff B (univ.map f)
    have eq : (univ.map f).card=2^z*16 := by simp [pow_add]
    rw [eq] at count
    omega
  by_cases hm : z+2≤d
  · let f : Fin (2^(z+2)) ↪ Index z := ⟨fun a => Sum.inr (Sum.inl a),Sum.inr_injective.comp Sum.inl_injective⟩
    have lower := freeTier (z+2) f (fun _ => rfl) (by omega) (by omega)
    rw [pow_add] at lower; omega
  · let f : Fin (2^z) ↪ Index z := ⟨fun a => Sum.inr (Sum.inr a),Sum.inr_injective.comp Sum.inr_injective⟩
    exact freeTier z f (fun _ => rfl) (by omega) (by omega)
end FrogCherry

namespace FrogPacket
open OMA.S_mo_370694 FrogModel Finset
variable {h : ℕ} {G T I : Type} [Fintype G] [DecidableEq T] [DecidableEq I]

def cleared (b : Option T → ℕ) (S : Finset T) (mass : ℕ) : Option T → ℕ
  | none => b none+mass
  | some i => if i∈S then 0 else b (some i)

theorem harvest (F : Frame h G T) (base : Vertex h → ℕ) (hr : 0<base F.root)
    (b : Option T → ℕ) (S : I → Finset T) (t : I → T) (n : I → ℕ)
    (forms : ∀ i, Forms F (S i) (t i) (n i)) (apart : ∀ i j, i≠j → Disjoint (S i) (S j))
    (lengths : ∀ i g, (binaryTree h).dist (F.site (g,t i)) F.root=n i)
    (one : ∀ i v, v∈S i → b (some v)=1) (is : Finset I) :
    Relation.ReflTransGen (Move h) (paint F base b) (paint F base (cleared b (is.biUnion S) (∑ i∈is,n i))) := by
  induction is using Finset.induction_on with
  | empty =>
    have e : cleared b ∅ 0=b := by funext a; cases a <;> simp [cleared]
    simpa [e] using (Relation.ReflTransGen.refl : Relation.ReflTransGen (Move h) (paint F base b) (paint F base b))
  | insert i is hi ih =>
    let U := is.biUnion S
    let m := ∑ j∈is,n j
    let c := cleared b U m
    have free : Disjoint (S i) U := by
      apply disjoint_left.mpr
      intro a ha he
      obtain ⟨j,hj,ha'⟩ := mem_biUnion.mp he
      exact disjoint_left.mp (apart i j (by rintro rfl; contradiction)) ha ha'
    obtain ⟨ht,hp,make⟩ := forms i
    have build := make base c (by
      intro a ha
      have ex : a∉U := fun he => disjoint_left.mp free ha he
      simp [c,cleared,ex,one i a ha])
    let d := joined c (S i) (t i) (n i)
    have pile : d (some (t i))=n i := by simp [d,joined,ht]
    have drop := toRoot F base d (t i) (by omega) hr (fun g => (lengths i g).trans pile.symm)
    have e : update d (t i) none=cleared b ((insert i is).biUnion S) (∑ j∈insert i is,n j) := by
      funext a
      cases a with
      | none => simp [update,d,c,joined,cleared,ht,m,sum_insert hi,pile,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm]
      | some a =>
        by_cases et : a=t i
        · subst a; simp [update,cleared,ht]
        by_cases us : a∈S i <;> by_cases uu : a∈U <;>
          simp [update,d,c,joined,cleared,et,us,U] at *
    rw [e] at drop
    exact (ih.trans build).trans drop
end FrogPacket


namespace FrogAllocation
open Finset
variable {C I : Type} [DecidableEq C] [DecidableEq I] [Fintype C] [Fintype I]

theorem chooseDistinct (n : ℕ) (sets : Fin n → Finset C) (enough : ∀ i, n≤(sets i).card) :
    ∃ f : Fin n → C, Function.Injective f ∧ ∀ i, f i∈sets i := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    have ht := enough 0
    obtain ⟨c,hc⟩ := card_pos.mp (show 0<(sets 0).card by omega)
    let rest (i : Fin n) := (sets i.succ).erase c
    obtain ⟨g,inj,mem⟩ := ih rest (by
      intro i
      have he := enough i.succ
      by_cases hv : c∈sets i.succ
      · simp only [rest,card_erase_of_mem hv]; omega
      · simpa [rest,erase_eq_of_notMem hv] using le_trans (Nat.le_succ _) he)
    refine ⟨Fin.cons c g,?_,?_⟩
    · refine Fin.cons_injective_of_injective ?_ inj
      rintro ⟨a,ha⟩
      exact (mem_erase.mp (mem a)).1 ha
    · intro i; exact Fin.cases (by simpa using hc) (fun j => by simpa using (mem_erase.mp (mem j)).2) i

theorem divide (used : I → Finset C) (n : I → ℕ) (apart : ∀ i j, i≠j → Disjoint (used i) (used j))
    (amount : (∑ i,((used i).card+n i)) = Fintype.card C) :
    ∃ rest : I → List C,
      (∀ i, (rest i).Nodup ∧ (rest i).length=n i) ∧
      (∀ i j c, c∈rest i → c∉used j) ∧
      (∀ i j, i≠j → Disjoint (rest i).toFinset (rest j).toFinset) ∧
      (∀ c, ∃ i, c∈used i ∨ c∈rest i) := by
  classical
  let U := univ.biUnion used
  let free := univ \ U
  have size : U.card=∑ i,(used i).card := card_biUnion (fun _ _ _ _ ne => apart _ _ ne)
  have eqc : Fintype.card (Σ i, Fin (n i)) = Fintype.card (↥free) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_coe]
    change _=(univ \ U).card
    rw [card_sdiff_of_subset (subset_univ U),card_univ,size]
    rw [Finset.sum_add_distrib] at amount; omega
  let bij := Fintype.equivOfCardEq eqc
  let get (i : I) (j : Fin (n i)) : C := (bij ⟨i,j⟩).val
  let rest (i : I) := List.ofFn (get i)
  have unique {i j : I} {a : Fin (n i)} {b : Fin (n j)} (he : get i a=get j b) :
      (⟨i,a⟩ : Σ i, Fin (n i))=⟨j,b⟩ := bij.injective (Subtype.ext he)
  refine ⟨rest,?_,?_,?_,?_⟩
  · intro i
    refine ⟨List.nodup_ofFn_ofInjective (fun a b he => ?_),List.length_ofFn⟩
    exact eq_of_heq (Sigma.mk.inj (unique he)).2
  · intro i j c hc hj
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hc
    have hfree := (bij ⟨i,a⟩).property
    exact (mem_sdiff.mp hfree).2 (mem_biUnion.mpr ⟨j,mem_univ _,hj⟩)
  · intro i j ne
    apply disjoint_left.mpr
    intro c hi hj
    obtain ⟨a,ha⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hi)
    obtain ⟨b,hb⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hj)
    exact ne (congrArg Sigma.fst (unique (ha.trans hb.symm)))
  · intro c
    by_cases yes : c∈U
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp yes
      exact ⟨i,Or.inl hi⟩
    · let v : ↥free := ⟨c,mem_sdiff.mpr ⟨mem_univ _,yes⟩⟩
      obtain ⟨⟨i,j⟩,hj⟩ := bij.surjective v
      exact ⟨i,Or.inr (List.mem_ofFn.mpr ⟨j,congrArg Subtype.val hj⟩)⟩
end FrogAllocation

/- Choose disjoint seeds, reserve a fresh terminal at each required
depth, and distribute every remaining cherry among the intermediate positions.
Each chain of k cherries finishes at depth 3k with mass 3k and jumps to the
global root. Together the chains exhaust the six bottom levels. -/
namespace FrogStrip
open OMA.S_mo_370694 FrogBand FrogPacket FrogModel FrogCherry FrogSeed FrogChain FrogAllocation Finset

theorem strip {h b z : ℕ} (hb : 0<b) (bh : b+(z+5)≤h) (deep : 3<b+z)
    (e M : ℕ) (k : Fin M → ℕ) (enough : ∀ f, need e f≤z+3) (cap : 2^e*M≤8*2^z)
    (num : M≤2^z) (seedLow : 2*(z+5)+2≤3*2^e) (growth : ∀ i, 2^e<k i)
    (terminalRange : ∀ i, b+z≤3*k i ∧ 3*k i≤b+(z+5)) (count : ∑ i,k i=21*2^z) :
    Relation.ReflTransGen (Move h) (core h (b+(z+5))) (core h (b+z-1)) := by
  classical
  let s := 2^e
  let F := frame (z:=z) hb bh
  let d (i : Fin M) := 3*k i-b
  let w (i : Fin M) := leafFor (z+4) (want s (k i-s) (d i))
  obtain ⟨seed,sep,bot⟩ := select hb bh e M w enough cap
  let A (i : Fin M) := (seed i).trees
  let B := univ.biUnion A
  have bmem {c : Index z} (hc : c∈B) : depth c=z+4 := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hc
    exact bot i c hi
  have bsize : B.card=s*M := by
    have eq := card_biUnion (s:=univ) (t:=A) (fun _ _ _ _ ne => sep _ _ ne)
    simpa [B,A,(fun i => (seed i).size),s,Nat.mul_comm] using eq
  have room' (i : Fin M) : M≤(eligible (d i) B).card := by
    have depthR := terminalRange i
    exact num.trans (room B (fun _ hc => bmem hc) (by simpa only [bsize,s] using cap)
      (by dsimp [d]; omega) (by dsimp [d]; omega))
  obtain ⟨t,inj,allowed⟩ := chooseDistinct M (fun i => eligible (d i) B) room'
  have out (i j : Fin M) : t i∉A j := by
    intro hv
    exact (mem_sdiff.mp (allowed i)).2 (mem_biUnion.mpr ⟨j,mem_univ _,hv⟩)
  let tw (i : Fin M) := leafFor (depth (t i)) (d i)
  have level (i : Fin M) : (head (t i) (tw i)).val.log2=d i := by
    have ht := (mem_filter.mp (mem_sdiff.mp (allowed i)).1).2
    rw [headDepth]
    rcases ht with he|he
    · simp [tw,leafFor,he]
    · have ne : depth (t i)%2 ≠ d i%2 := by omega
      simp [tw,leafFor,ne,he]
  let used (i : Fin M) := A i∪{t i}
  let n (i : Fin M) := k i-s-1
  have uSize (i) : (used i).card=s+1 := by
    change (A i ∪ {t i}).card=s+1
    rw [card_union_of_disjoint (by simpa using out i i),card_singleton]; exact congrArg (·+1) (seed i).size
  have uSep (i j) (ne : i≠j) : Disjoint (used i) (used j) := by
    have tne : t i≠t j := fun h => ne (inj h)
    exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨sep _ _ ne,by simpa using out j i⟩,
      disjoint_union_right.mpr ⟨by simpa using out i j,by simpa using tne⟩⟩
  have total : (∑ i, ((used i).card+n i))=Fintype.card (Index z) := by
    calc
      _ = ∑ i,k i := by
        apply sum_congr rfl; intro i _
        have hi := growth i
        rw [uSize]; dsimp [n,s]; omega
      _ = 21*2^z := count
      _ = _ := by simp [Fintype.card_sum,Index,pow_add] <;> ring
  obtain ⟨cs,csSize,csFree,csSep,coverage⟩ := divide used n uSep total
  let subset (i : Fin M) := A i∪(cs i).toFinset∪{t i}
  have member (i : Fin M) (c : Index z) : c∈subset i ↔ c∈used i ∨ c∈cs i := by
    simp [subset,used] <;> tauto
  have chains (i : Fin M) : Forms F (places (subset i)) (head (t i) (tw i)) (3*k i) := by
    have bigger := growth i
    change s<k i at bigger
    have len : s+(cs i).length+1=k i := by rw [(csSize i).2]; dsimp [n]; omega
    have ini : (head (seed i).c (w i)).val.log2%2=want s ((cs i).length+1) (head (t i) (tw i)).val.log2 := by
      rw [headDepth,bot i _ (seed i).member,level,show (cs i).length+1=k i-s by omega]
      exact (selected _ _).trans (Nat.mod_eq_of_lt (wantLt ..))
    have run := build hb bh deep (cs i) (t i) (tw i) s (A i) _ (csSize i).1
      (fun c hc ha => csFree i i c hc (mem_union_left _ ha)) (out i i)
      (fun hc => csFree i i _ hc (mem_union_right _ (mem_singleton_self _)))
      (seed i).forms seedLow (by rw [len]; exact (terminalRange i).2) ini
    simpa only [len] using run
  have dis (i j : Fin M) (ne : i≠j) : Disjoint (places (subset i)) (places (subset j)) := by
    apply placesSep
    apply disjoint_left.mpr
    intro c ha hb'
    rcases (member i c).mp ha with a|a <;> rcases (member j c).mp hb' with b'|b'
    · exact disjoint_left.mp (uSep i j ne) a b'
    · exact csFree _ _ _ b' a
    · exact csFree _ _ _ a b'
    · exact disjoint_left.mp (csSep i j ne) (List.mem_toFinset.mpr a) (List.mem_toFinset.mpr b')
  have all (v : T z) : v∈univ.biUnion (fun i => places (subset i)) := by
    obtain ⟨c,hc⟩ := covers v
    obtain ⟨i,hi⟩ := coverage c
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨c,(member i c).mpr hi,hc⟩⟩
  let base := core h (b+(z+5))
  let initial : Option (T z) → ℕ := view (FrogCheck.start (z+5))
  have initialOne (v : T z) : initial (some v)=1 := by
    change (FrogCheck.start (z+5)).read v.val=1
    simp [FrogCheck.start,FrogCheck.read_put _ _ _ _ _ (Nat.two_pow_pos _) v.property.2,(slotBounds v).1.ne',FrogCheck.Table.read]
  have run := harvest F base (by simp [base,F,frame,core,root]) initial _ _ _ chains dis (by
    intro i g
    change (binaryTree h).dist (point bh g (head (t i) (tw i))) (root h) = 3*k i
    rw [rootLength,level]
    have l := (terminalRange i).1
    dsimp [d]; omega) (fun _ v _ => initialOne v) univ
  let amount := 2^(z+5+1)-2^z
  let tab := FrogCheck.Table.putAux (z+5+1) (.uniform 0) 0 amount
  have readTab (a : ℕ) (ha : a<2^(z+5+1)) :
      tab.read a=if a=0 then amount else 0 := by
    simp only [tab,FrogCheck.read_put _ _ _ _ _ (Nat.two_pow_pos _) ha,FrogCheck.Table.read]
  have finalTab : FrogCheck.finished z (z+5) tab=true := by
    simp only [FrogCheck.finished,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range]
    refine ⟨by simp [readTab 0 (Nat.two_pow_pos _),amount],?_⟩
    intro j hj
    have hp : 0<2^z := by positivity
    rw [readTab _ (by omega),if_neg (by omega)]
  have eq : cleared initial (univ.biUnion fun i => places (subset i)) (∑ i : Fin M,3*k i)=view tab := by
    funext u
    cases u with
    | none =>
      have sum : (∑ i,3*k i)=3*(21*2^z) := by rw [←Finset.mul_sum,count]
      change (FrogCheck.start (z+5)).read 0 + _ = tab.read 0
      rw [readTab 0 (Nat.two_pow_pos _),if_pos rfl,sum]
      simp [FrogCheck.start,FrogCheck.read_put _ _ _ _ _ (Nat.two_pow_pos _) (Nat.two_pow_pos _),amount,pow_add]
      omega
    | some v =>
      change (if v∈_ then 0 else _) = tab.read v.val
      rw [if_pos (all v),readTab _ v.property.2,if_neg (slotBounds v).1.ne']
  rw [eq] at run
  exact (beginBand (z:=z) hb bh) ▸ (endBand hb bh (by omega : z≤z+5) tab finalTab) ▸ run
end FrogStrip

/- For large height t, let q be the integer part of t/3. The
terminal depths 3q and 3(q-1) lie in the bottom six levels. Choose a power-of-two
seed size and split all cherries into chains of q or q-1, subject to the supply
of seeds and terminals. -/

-- Reduction of the root-gathering problem to a bounded core and a six-level strip.
-- Credit: @Chihiro-g
namespace OMA.R_mo_370694_R1

open OMA.S_mo_370694



/-- Exponential supply of available bottom cherries in the large-height regime. -/
theorem powerDominates (s : ℕ) (hs : 32 ≤ s) : (64*s)^2 ≤ 2^(s-2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hs
  induction n with
  | zero => decide
  | succ n ih =>
    have he : 32+(n+1)-2 = (32+n-2)+1 := by omega
    rw [he, pow_succ]
    calc
      (64*(32+(n+1)))^2 ≤ 2*(64*(32+n))^2 := by nlinarith [Nat.zero_le (n^2)]
      _ ≤ _ := by omega

/-- Split U cherries into chains with q and q-1 cherries. -/
theorem chainCounts {q U : ℕ} (hq : 2 ≤ q) (hb : q*q ≤ U) :
    ∃ x y : ℕ, q*x + (q-1)*y = U ∧ (q-1)*(x+y) ≤ U := by
  have hd := Nat.div_add_mod U q
  have he : q - 1 + 1 = q := by omega
  have hbound : q ≤ U/q := (Nat.le_div_iff_mul_le (by omega)).mpr hb
  by_cases hh : U%q = 0
  · refine ⟨U/q,0,?_,?_⟩
    · simpa [hh] using hd
    · simp only [Nat.add_zero, hh] at *
      nlinarith [Nat.mul_le_mul_right (U/q) (Nat.sub_le q 1)]
  · have hm := Nat.mod_lt U (by omega : 0 < q)
    let y := q-U%q
    have hy : y + U%q = q := by dsimp [y]; omega
    let x := U/q+1-y
    have hx : x+y = U/q+1 := by dsimp [x]; omega
    have mul := congrArg (fun m : ℕ => q*m) hx
    have submul := congrArg (fun m : ℕ => m*y) he
    have eq : q*x+(q-1)*y = U := by nlinarith
    refine ⟨x,y,eq,?_⟩
    nlinarith [Nat.mul_le_mul_right x (Nat.sub_le q 1)]

/-- Per-copy capacities for the six-level strip. One cherry has three frogs.
The two terminal depths are 3q and 3q-3, and a seed contains s cherries. -/
theorem parameters (h : ℕ) (hh : 129 ≤ h) :
    ∃ e x y : ℕ, let s := 2^e; let L := s+3; let A := 2^(L-5); let q := h/3
      16 ≤ s ∧ L < h ∧ 2*L+2 ≤ 3*s ∧ s < q-1 ∧
      q*x+(q-1)*y = 21*A ∧ x+y ≤ A ∧ s*(x+y) ≤ 8*A := by
  have finish (s : ℕ) (hcap : 21*s ≤ 8*(h/3-1))
      (hbig : h/3*(h/3) ≤ 21*2^(s-2)) :
      ∃ x y : ℕ, h/3*x+(h/3-1)*y=21*2^(s-2) ∧ x+y ≤ 2^(s-2) ∧
        s*(x+y) ≤ 8*2^(s-2) := by
    obtain ⟨x,y,hxy,hm⟩ := chainCounts (q := h/3) (by omega) hbig
    have a := Nat.mul_le_mul_right (x+y) (by omega : 21 ≤ h/3-1)
    have b := Nat.mul_le_mul_right (x+y) hcap
    refine ⟨x,y,hxy,by nlinarith,?_⟩
    nlinarith [Nat.mul_le_mul_left 8 hm]
  by_cases small : h < 1024
  · have hq : h/3 ≤ 341 := by omega
    have hc : 21*16 ≤ 8*(h/3-1) := by omega
    have hb : h/3*(h/3) ≤ 21*2^(16-2) :=
      (Nat.mul_le_mul hq hq).trans (by decide)
    obtain ⟨x,y,hxy,h1,h2⟩ := finish 16 hc hb
    exact ⟨4,x,y,by decide,by omega,by decide,by omega,hxy,h1,h2⟩
  · let e := Nat.log 2 (h/32)
    let s := 2^e
    have lo : s ≤ h/32 := Nat.pow_log_le_self 2 (by omega)
    have hi : h/32 < 2*s := by
      simpa [s,e,pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (b:=2) (by decide) (h/32)
    have hs : 32 ≤ s := by
      have he : 5 ≤ e := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
      exact Nat.pow_le_pow_right (by decide : 0 < 2) he
    have sq := powerDominates s hs
    have hq : h/3 ≤ 64*s := by omega
    have hc : 21*s ≤ 8*(h/3-1) := by omega
    have hb : h/3*(h/3) ≤ 21*2^(s-2) := by
      have a := Nat.mul_le_mul hq hq
      nlinarith
    obtain ⟨x,y,hxy,h1,h2⟩ := finish s hc hb
    refine ⟨e,x,y,?_⟩
    change 16 ≤ s ∧ s+3 < h ∧ 2*(s+3)+2 ≤ 3*s ∧ s < h/3-1 ∧
      h/3*x+(h/3-1)*y = 21*2^(s+3-5) ∧ x+y ≤ 2^(s+3-5) ∧ s*(x+y) ≤ 8*2^(s+3-5)
    rw [show s+3-5=s-2 by omega]
    exact ⟨by omega, by omega, by omega, by omega, hxy, h1, h2⟩


end OMA.R_mo_370694_R1

namespace FrogStrip
open OMA.S_mo_370694 FrogBand FrogSeed Finset

theorem byCounts {h t e z x y : ℕ} (th : t≤h) (ht : z+5<t) (deep : 9≤t)
    (need : ∀ f, FrogSeed.need e f≤z+3) (lower : 2*(z+5)+2≤3*2^e)
    (growth : 2^e<t/3-1) (count : t/3*x+(t/3-1)*y=21*2^z)
    (num : x+y≤2^z) (cap : 2^e*(x+y)≤8*2^z) :
    Relation.ReflTransGen (Move h) (core h t) (core h (t-6)) := by
  let b := t-(z+5)
  have fit : b+(z+5)=t := by dsimp [b]; omega
  let len : Fin x ⊕ Fin y → ℕ := Sum.elim (fun _ => t/3) (fun _ => t/3-1)
  let k (i : Fin (x+y)) := len (finSumFinEquiv.symm i)
  have kg (i) : 2^e<k i := by
    dsimp only [k]
    cases finSumFinEquiv.symm i <;> dsimp [len] <;> omega
  have rng (i) : b+z≤3*k i ∧ 3*k i≤b+(z+5) := by
    dsimp only [k]
    cases finSumFinEquiv.symm i <;> dsimp [len] <;> omega
  have tot : (∑ i,k i)=21*2^z := by
    calc
      _ = ∑ i : Fin x ⊕ Fin y, len i := Equiv.sum_comp finSumFinEquiv.symm len
      _ = _ := by simpa [Fintype.sum_sum_type,len,Nat.mul_comm] using count
  have run := strip (show 0<b by omega) (show b+(z+5)≤h by omega) (by omega) e (x+y) k need cap num lower kg rng tot
  simpa only [fit,show b+z-1=t-6 by omega] using run

theorem uniform {h t : ℕ} (th : t≤h) (ht : 129≤t) :
    Relation.ReflTransGen (Move h) (core h t) (core h (t-6)) := by
  obtain ⟨e,x,y,params⟩ := OMA.R_mo_370694_R1.parameters t ht
  dsimp only at params
  obtain ⟨large,fit,low,grow,cnt,num,cap⟩ := params
  let z := 2^e+3-5
  have zz : z+5=2^e+3 := by dsimp [z]; omega
  exact byCounts (z:=z) th (by omega) (by omega) (fun f => (needPow e f).trans (by dsimp [z]; omega))
    (by omega) grow cnt num cap
end FrogStrip

/- For heights 63 through 128, the same construction uses the
explicit parameters below. Each line checks the size and capacity inequalities. -/
namespace FrogStrip
open OMA.S_mo_370694 FrogBand
set_option maxHeartbeats 8000000 in
theorem middle {h t : ℕ} (th : t≤h) (lo : 63≤t) (hi : t≤128) :
    Relation.ReflTransGen (Move h) (core h t) (core h (t-6)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le lo
  have bound : n≤65 := by omega
  interval_cases n
  · apply byCounts (e:=2) (z:=0) (x:=1) (y:=0) th <;> decide
  · apply byCounts (e:=2) (z:=0) (x:=1) (y:=0) th <;> decide
  · apply byCounts (e:=2) (z:=0) (x:=1) (y:=0) th <;> decide
  · apply byCounts (e:=2) (z:=0) (x:=0) (y:=1) th <;> decide
  · apply byCounts (e:=2) (z:=0) (x:=0) (y:=1) th <;> decide
  · apply byCounts (e:=2) (z:=0) (x:=0) (y:=1) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=6) (y:=9) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=6) (y:=9) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=6) (y:=9) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=7) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=7) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=7) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=0) (y:=7) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=0) (y:=7) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=0) (y:=7) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=11) (y:=2) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=11) (y:=2) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=11) (y:=2) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=22) (y:=3) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=22) (y:=3) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=22) (y:=3) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=6) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=6) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=6) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=0) (y:=6) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=0) (y:=6) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=0) (y:=6) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=5) (y:=18) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=5) (y:=18) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=5) (y:=18) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=6) (y:=5) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=6) (y:=5) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=6) (y:=5) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=21) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=21) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=21) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=0) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=0) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=0) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=3) (y:=2) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=3) (y:=2) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=3) (y:=2) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=18) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=18) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=18) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=7) (y:=12) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=7) (y:=12) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=7) (y:=12) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=12) (y:=25) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=12) (y:=25) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=12) (y:=25) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=3) (y:=6) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=3) (y:=6) th <;> decide
  · apply byCounts (e:=3) (z:=4) (x:=3) (y:=6) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=14) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=14) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=14) (y:=21) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=9) (y:=8) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=9) (y:=8) th <;> decide
  · apply byCounts (e:=3) (z:=5) (x:=9) (y:=8) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=24) (y:=9) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=24) (y:=9) th <;> decide
  · apply byCounts (e:=3) (z:=6) (x:=24) (y:=9) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=4) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=4) (y:=0) th <;> decide
  · apply byCounts (e:=3) (z:=3) (x:=4) (y:=0) th <;> decide
end FrogStrip

open OMA.S_mo_370694

theorem OMA.solution : type_of% @OMA.S_mo_370694.main := by
  intro h ne
  have win (k : ℕ) (kh : k≤h) (nk : k≠2) :
      Relation.ReflTransGen (Move h) (FrogBand.core h k) (fun v => if v.val=0 then 2^(h+1)-1 else 0) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases low : k≤62
      · exact FrogFinite.through62 h k kh low nk
      have run : Relation.ReflTransGen (Move h) (FrogBand.core h k) (FrogBand.core h (k-6)) := by
        by_cases mid : k≤128
        · exact FrogStrip.middle kh (by omega) mid
        · exact FrogStrip.uniform kh (by omega)
      exact run.trans (ih (k-6) (by omega) (by omega) (by omega))
  have initial : FrogBand.core h h=fun _ => 1 := by
    funext v
    have hv := v.isLt
    change v.val<2^(h+1)-1 at hv
    simp [FrogBand.core,show v.val+1<2^(h+1) by omega]
  simpa only [initial] using win h (le_refl _) ne
