import OMAStatements.S_oeis_a289096
open OMA.S_oeis_a289096
namespace Guard545

def oddStep (c l r d u : Bool) := c || ((l.xor r).xor (d.xor u))

def g : ℕ → ℤ → ℤ → Bool
  | 0,x,y => decide (x=0 ∧ y=0)
  | t+1,x,y => oddStep (g t x y) (g t (x-1) y) (g t (x+1) y) (g t x (y-1)) (g t x (y+1))

lemma symmetric (t : ℕ) (x y : ℤ) : g t y x = g t x y := by
  induction t generalizing x y with
  | zero => simp [g,and_comm]
  | succ t ih =>
    rw [g,g,ih x y,ih x (y-1),ih x (y+1),ih (x-1) y,ih (x+1) y]
    unfold oddStep; rw [Bool.xor_comm (Bool.xor _ _)]

lemma stays (s t : ℕ) (hs : s≤t) (x y : ℤ) (h : g s x y = true) : g t x y = true := by
  induction t, hs using Nat.le_induction with
  | base => exact h
  | succ t _ ih => simp [g,oddStep,ih]

lemma diagonal (t : ℕ) (x : ℤ) (hx : x≠0) : g t x x = false := by
  induction t with
  | zero => simp [g,hx]
  | succ t ih =>
    rw [g,ih,symmetric t x (x-1),symmetric t x (x+1)]
    cases g t x (x-1) <;> cases g t x (x+1) <;> rfl

lemma far (t : ℕ) (x y : ℤ) (h : (t:ℤ) < |x| + |y|) : g t x y = false := by
  induction t generalizing x y with
  | zero =>
    have hn : ¬(x=0 ∧ y=0) := by rintro ⟨rfl,rfl⟩; norm_num at h
    simp [g,hn]
  | succ t ih =>
    rw [g,ih x y,ih (x-1) y,ih (x+1) y,ih x (y-1),ih x (y+1)]
    · rfl
    all_goals simp only [Int.natCast_succ,abs_eq_max_neg] at *; omega

lemma axis (t : ℕ) : g t t 0 = true := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [g,show (↑(t+1):ℤ)-1=t by omega,ih,far t _ 0,far t _ 0,far t _ (0-1),far t _ (0+1)]
    · rfl
    all_goals simp only [abs_eq_max_neg,Int.natCast_succ]; omega

def B (n k : ℕ) := (n.choose k % 2 == 1)

lemma pascal (n k : ℕ) : B (n+1) (k+1) = (B n k).xor (B n (k+1)) := by
  unfold B; rw [Nat.choose_succ_succ, Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one (n.choose k) with h|h <;>
    rcases Nat.mod_two_eq_zero_or_one (n.choose (k+1)) with j|j <;> rw [h,j] <;> decide

lemma front (t x y : ℕ) (h : x+y=t) : g t (x:ℤ) y = B t x := by
  induction t generalizing x y with
  | zero =>
    obtain rfl : x=0 := by omega
    obtain rfl : y=0 := by omega
    rfl
  | succ t ih =>
    cases x with
    | zero =>
      have hy : y=t+1 := by omega
      subst y; simp only [Nat.cast_zero]; rw [symmetric,axis]; simp [B]
    | succ x =>
      cases y with
      | zero =>
        have hx : x=t := by omega
        subst x; simp only [Nat.cast_zero]; rw [axis]; simp [B]
      | succ y =>
        rw [g,show (↑(x+1):ℤ)-1=x by omega,show (↑(y+1):ℤ)-1=y by omega,
          ih x (y+1) (by omega),ih (x+1) y (by omega),far t (x+1:ℕ) (y+1:ℕ),
          far t ((x+1:ℕ)+1:ℤ) (y+1:ℕ),far t (x+1:ℕ) ((y+1:ℕ)+1:ℤ),pascal]
        · cases B t x <;> cases B t (x+1) <;> rfl
        all_goals simp only [abs_eq_max_neg,Int.natCast_succ]; omega

lemma full (k i : ℕ) (hi : i<2^k) : B (2^k-1) i = true := by
  induction i with
  | zero => simp [B]
  | succ i ih =>
    have h := ih (by omega)
    have d := Nat.prime_two.dvd_choose_pow (by omega : i+1≠0) (by omega : i+1≠2^k)
    have hp : 0 < (2:ℕ)^k := by positivity
    rw [←show 2^k-1+1=2^k by omega, Nat.choose_succ_succ] at d
    simp only [B,beq_iff_eq] at h ⊢
    have dm := Nat.mod_eq_zero_of_dvd d
    rw [Nat.add_mod,h] at dm
    change (1 + (2^k-1).choose (i+1)%2)%2=0 at dm
    omega

lemma top (k v : ℕ) (hv : v<2^k) : B (2^k+v) (2^k) = true := by
  -- Lucas reduction keeps the leading digit in the same position in both arguments.
  induction k generalizing v with
  | zero =>
    have h : v=0 := by simpa using hv
    subst v; decide
  | succ k ih =>
    let N := 2^k
    have hN : 0<N := by dsimp [N]; positivity
    have hp : 2^(k+1)=2*N := by dsimp [N]; rw [pow_succ]; omega
    rw [hp] at hv ⊢
    have h := ih (v/2) (by omega)
    have luc := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2*N+v) (2*N) 2 inferInstance
    change _ % 2 = _ % 2 at luc
    rw [show 2*N%2=0 by omega, Nat.choose_zero_right,one_mul,
      show (2*N+v)/2=N+v/2 by omega,show 2*N/2=N by omega] at luc
    simp only [B,beq_iff_eq] at h ⊢
    exact luc.trans h

lemma wall (k t : ℕ) (x y : ℤ) (hx : 0≤x) (hy : 0≤y) (hxy : x+y=(2^k:ℕ)-1)
    (ht : 2^k-1≤t) : g t x y = true := by
  have hN : 0<(2:ℕ)^k := by positivity
  have he : x.toNat+y.toNat=2^k-1 := by omega
  have hf := (front _ _ _ he).trans (full k x.toNat (by omega))
  rw [Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hy] at hf
  exact stays _ _ ht _ _ hf

lemma wedge (k t : ℕ) (x y : ℤ) (hx : 0≤x) (hy : 0≤y)
    (hX : x≤(2^k:ℕ)) (hY : y≤(2^k:ℕ)) (hxy : (2^k:ℕ)≤x+y)
    (ht : (t:ℤ)<2*(2^k:ℕ)-|x-y|) : g t x y=false := by
  let N : ℕ := 2^k
  change x≤(N:ℤ) at hX
  change y≤(N:ℤ) at hY
  change (N:ℤ)≤x+y at hxy
  change (t:ℤ)<2*(N:ℤ)-|x-y| at ht
  have pos : 0<N := by dsimp [N]; positivity
  induction t generalizing x y with
  | zero => exact far 0 x y (by rw [abs_of_nonneg hx,abs_of_nonneg hy]; omega)
  | succ t ih =>
    by_cases edge : x=N ∨ y=N
    · apply far; simp only [abs_eq_max_neg,Int.natCast_succ] at *; omega
    have early (a b : ℤ) (ha : 0≤a) (hb : 0≤b) (ha' : a≤N) (hb' : b≤N)
        (hc : (N:ℤ)≤a+b) (hd : |a-b|≤|x-y|+1) : g t a b=false :=
      ih _ _ ha hb ha' hb' hc (by omega)
    have center := early x y hx hy hX hY hxy (by omega)
    have east := early (x+1) y (by omega) hy (by omega) hY (by omega) (by simp only [abs_eq_max_neg]; omega)
    have north := early x (y+1) hx (by omega) hX (by omega) (by omega) (by simp only [abs_eq_max_neg]; omega)
    rw [g,center,east,north]
    by_cases base : x+y=N
    · have same : g t (x-1) y = g t x (y-1) := by
        by_cases done' : N-1≤t
        · rw [wall k t (x-1) y (by omega) hy (by change _=(N:ℤ)-1; omega) done',
            wall k t x (y-1) hx (by omega) (by change _=(N:ℤ)-1; omega) done']
        · rw [far,far] <;> simp only [abs_eq_max_neg] <;> omega
      rw [same]; cases g t x (y-1) <;> rfl
    · rw [early (x-1) y (by omega) hy (by omega) hY (by omega) (by simp only [abs_eq_max_neg]; omega),
        early x (y-1) hx (by omega) hX (by omega) (by omega) (by simp only [abs_eq_max_neg]; omega)]
      rfl


lemma silent (k t u v : ℕ) (huv : u≤v) (hl : u+v≤2^k) (ht : t<2^k+u+v) :
    g t ((2^k:ℕ)-u:ℤ) (v:ℤ) = false := by
  apply wedge k <;> try omega
  rw [abs_of_nonneg (by omega)]; omega

lemma ballot (k m : ℕ) (u v : ℕ) (hm : u+v=m) (huv : u≤v) (ht : m<2^k) :
    g (2^k+m) ((2^k:ℕ)-u:ℤ) (v:ℤ) = B (m+1) u := by
  let N : ℕ := 2^k
  change m<N at ht
  change g (N+m) ((N:ℤ)-u) v = _
  induction m generalizing u v with
  | zero =>
    obtain rfl : u=0 := by omega
    obtain rfl : v=0 := by omega
    simp [B,axis]
  | succ m ih =>
    cases u with
    | zero =>
      have hv : v=m+1 := by omega
      subst v
      simp only [Nat.cast_zero,sub_zero]
      rw [front _ N (m+1) rfl, top k (m+1) ht]; simp [B]
    | succ u =>
      cases v with
      | zero => omega
      | succ v =>
        have east := ih u (v+1) (by omega) (by omega) (by omega)
        let t := N+m
        let x : ℤ := (N:ℤ)-(u+1:ℕ)
        let y : ℤ := (v+1:ℕ)
        change g (t+1) x y = _
        have ex : x+1=(N:ℤ)-u := by dsimp [x]; omega
        have wx : x-1=(N:ℤ)-(u+2:ℕ) := by dsimp [x]; omega
        have ny : y+1=(v+2:ℕ) := by dsimp [y]; omega
        have sy : y-1=(v:ℤ) := by dsimp [y]; omega
        have cen : g t x y=false := silent k t (u+1) (v+1) huv (by change _≤N; omega) (by dsimp [t]; change _<N+_+_; omega)
        have up : g t x (v+2:ℕ)=false := silent k t (u+1) (v+2) (by omega) (by change _≤N; omega) (by dsimp [t]; change _<N+_+_; omega)
        rw [g,cen,ex,ny,up]
        change g (N+m) ((N:ℤ)-u) (v+1:ℕ) = _ at east
        change g t ((N:ℤ)-u) y = _ at east
        rw [east,pascal,sy]
        by_cases he : u=v
        · subst v
          have wl : g t (x-1) y=true := by
            apply wall k
            · dsimp only [x]; omega
            · dsimp only [y]; omega
            · change x-1+y=(N:ℤ)-1; dsimp only [x,y]; omega
            · change N-1≤N+m; omega
          have sl : g t x (u:ℤ)=true := by
            apply wall k
            · dsimp only [x]; omega
            · positivity
            · change x+(u:ℤ)=(N:ℤ)-1; dsimp only [x]; omega
            · change N-1≤N+m; omega
          have even' := Nat.mod_eq_zero_of_dvd (Nat.two_dvd_centralBinom_succ u)
          change ((2*(u+1)).choose (u+1))%2=0 at even'
          have off : B (m+1) (u+1)=false := by
            unfold B; simp only [show m+1=2*(u+1) by omega,even']; decide
          rw [wl,sl,off]; cases B (m+1) u <;> rfl
        · have west : g t ((N:ℤ)-(u+2:ℕ)) y=false :=
            silent k t (u+2) (v+1) (by omega) (by change _≤N; omega) (by dsimp [t]; change _<N+_+_; omega)
          have south := ih (u+1) v (by omega) (by omega) (by omega)
          change g t x (v:ℤ) = _ at south
          rw [wx,west,south]; cases B (m+1) u <;> cases B (m+1) (u+1) <;> rfl

lemma twin (k a : ℕ) (ha : 2^k≤2*a+2) (hb : a+2≤2^k) (t : ℕ) :
    g t (a+2:ℕ) (a:ℤ) = decide (2*2^k-2≤t) := by
  let N : ℕ := 2^k
  change N ≤ 2*a+2 at ha
  change a+2 ≤ N at hb
  let u := N-(a+2)
  have hu : u≤a := by dsimp [u]; omega
  have hsum : u+a=N-2 := by dsimp [u]; omega
  have hx : (N:ℤ)-u=(a+2:ℕ) := by dsimp [u]; omega
  by_cases h : 2*N-2≤t
  · have b := ballot k (N-2) u a hsum hu (by change _<N; omega)
    change g (N+(N-2)) ((N:ℤ)-u) a = _ at b
    rw [hx,show N-2+1=2^k-1 by change _=N-1; omega,full k u (by change u<N; omega)] at b
    change g t _ _ = decide (2*N-2≤t)
    rw [decide_eq_true h]
    exact stays _ _ (by omega) _ _ b
  · have b := silent k t u a hu (by change _≤N; omega) (by change t<N+u+a; omega)
    change g t ((N:ℤ)-u) a = false at b
    rw [hx] at b
    change g t _ _ = decide (2*N-2≤t)
    simpa only [decide_eq_false h] using b

lemma power_band (m : ℕ) (hm : 0 < m) : ∃ k : ℕ, 2^k ≤ m ∧ m < 2*2^k := by
  exact ⟨m.log2, Nat.log2_self_le (by omega), by simpa [pow_succ, Nat.mul_comm] using (@Nat.lt_log2_self m)⟩

lemma guard (a : ℕ) (ha : 2≤a) (he : a%2=0) (t : ℕ) : g t (a+1:ℕ) a=false := by
  obtain ⟨k,hk,hk'⟩ := power_band a (by omega)
  have large : 2≤2^k := by by_contra! h; omega
  have evenN : 2∣2^(k+1) := by rw [pow_succ]; exact dvd_mul_left _ _
  have top' : a+2≤2^(k+1) := by rw [pow_succ] at *; omega
  have bottom : 2^(k+1) ≤ 2*a := by rw [pow_succ]; omega
  induction t with
  | zero => simp [g]; omega
  | succ t ih =>
    rw [g,ih]
    have dx : ((a+1:ℕ):ℤ)-1=a := by omega
    have ex : ((a+1:ℕ):ℤ)+1=(a+2:ℕ) := by omega
    have dy : (a:ℤ)-1=(a-1:ℕ) := by omega
    have ey : (a:ℤ)+1=(a+1:ℕ) := by omega
    rw [dx,ex,dy,ey,diagonal t a (by omega),diagonal t (a+1:ℕ) (by omega),
      twin (k+1) a (by omega) top',show a+1=(a-1)+2 by omega,
      twin (k+1) (a-1) (by omega) (by omega)]
    cases decide (2*2^(k+1)-2≤t) <;> rfl


abbrev Pt := ℤ × ℤ

def adj (p : Pt) (i : Fin 4) : Pt :=
  if i=0 then (p.1-1,p.2) else if i=1 then (p.1+1,p.2) else
    if i=2 then (p.1,p.2-1) else (p.1,p.2+1)

def rev (i : Fin 4) : Fin 4 := if i=0 then 1 else if i=1 then 0 else if i=2 then 3 else 2
lemma adj_back (p : Pt) (i : Fin 4) : adj (adj p i) (rev i)=p := by
  rcases p with ⟨x,y⟩; fin_cases i <;> simp [adj,rev]

def I (t : ℕ) (p : Pt) := g t p.1 p.2
def R (t : ℕ) (p : Pt) := state t p.1 p.2
def realBit (c l r d u : Bool) := Nat.testBit 545 (c.toNat+2*(l.toNat+r.toNat+d.toNat+u.toNat))

lemma Istep (t : ℕ) (p : Pt) : I (t+1) p = oddStep (I t p)
    (I t (adj p 0)) (I t (adj p 1)) (I t (adj p 2)) (I t (adj p 3)) := rfl
lemma Rstep (t : ℕ) (p : Pt) : R (t+1) p = realBit (R t p)
    (R t (adj p 0)) (R t (adj p 1)) (R t (adj p 2)) (R t (adj p 3)) := rfl

lemma prevDark (t : ℕ) (p : Pt) (h : I (t+1) p = false) : I t p = false := by
  rw [Istep] at h; simpa [oddStep] using (Bool.or_eq_false_iff.mp h).1

lemma first (p : Pt) : R 1 p = !(I 1 p) := by
  rw [Rstep,Istep]
  rcases p with ⟨x,y⟩
  by_cases hx : x=0 <;> by_cases hy : y=0 <;> by_cases hl : x-1=0 <;> by_cases hr : x+1=0 <;>
    by_cases hd : y-1=0 <;> by_cases hu : y+1=0 <;>
    simp only [R,I,state,g,oddStep,adj] <;>
    first | contradiction | (simp [*,realBit] <;> first | decide | omega) | omega

lemma complementRule : ∀ l r d u : Bool, (l=false ∨ r=false ∨ d=false ∨ u=false) →
    realBit true (!l) (!r) (!d) (!u) = !(oddStep false l r d u) := by decide

lemma touchedRule : ∀ l r d u : Bool, (l=true ∨ r=true ∨ d=true ∨ u=true) →
    realBit false l r d u=false := by decide

def Matches (t : ℕ) (p : Pt) := R t p = !(I t p) ∧ ∀ d, R t (adj p d) = !(I t (adj p d))
def Spare (t : ℕ) (p : Pt) := ∃ d, I t (adj p d)=false

lemma updateMatch (t : ℕ) (p : Pt) (hp : I t p=false) (sp : Spare t p) (m : Matches t p) :
    R (t+1) p = !(I (t+1) p) := by
  rw [Rstep,Istep,m.1,m.2,m.2,m.2,m.2,hp]
  apply complementRule
  obtain ⟨i,h⟩ := sp; fin_cases i <;> tauto

lemma keepFalse (t : ℕ) (q : Pt) (i : Fin 4) (hq : R t q=false) (on : R t (adj q i)=true) :
    R (t+1) q=false := by
  rw [Rstep,hq]; apply touchedRule
  fin_cases i <;> tauto

lemma matches_on_edges (n : ℕ) (p : Pt) (hp : I (n+1) p=false) (sp : Spare (n+1) p) :
    Matches (n+1) p := by
  induction n generalizing p with
  | zero => exact ⟨first p, fun _ => first _⟩
  | succ n ih =>
    let t := n+1
    change I (t+1) p=false at hp
    obtain ⟨b,hb⟩ := sp
    have dark := prevDark t p hp
    have pm := ih p dark ⟨b,prevDark t _ hb⟩
    have on : R t p=true := by rw [pm.1,dark]; rfl
    refine ⟨updateMatch t p dark ⟨b,prevDark t _ hb⟩ pm,?_⟩
    intro i
    let q := adj p i
    have back : adj q (rev i) = p := adj_back _ _
    change R (t+1) q = !(I (t+1) q)
    cases h : I t q with
    | false =>
      have qs : Spare t q := ⟨rev i,by rw [back]; exact dark⟩
      exact updateMatch t q h qs (ih q h qs)
    | true =>
      have off : R t q=false := by change R t (adj p i)=false; rw [pm.2 i]; change (!(I t q))=false; rw [h]; rfl
      have now := keepFalse t q (rev i) off (by rw [back]; exact on)
      have hi : I (t+1) q=true := stays t (t+1) (by omega) _ _ h
      rw [now,hi]; rfl

lemma diagonal_on (t x : ℕ) (ht : 0<t) (hx : 2≤x) : state t x x=true := by
  obtain ⟨n,rfl⟩ : ∃ n,t=n+1 := ⟨t-1,by omega⟩
  let p : Pt := (x,x)
  have dark : I (n+1) p=false := diagonal _ _ (by dsimp [p]; omega)
  have sp : Spare (n+1) p := by
    rcases Nat.mod_two_eq_zero_or_one x with h|h
    · refine ⟨1,?_⟩
      change g (n+1) ((x:ℤ)+1) x=false
      simpa only [Nat.cast_add,Nat.cast_one] using guard x hx h (n+1)
    · refine ⟨0,?_⟩
      change g (n+1) ((x:ℤ)-1) x=false
      rw [symmetric]
      have hg := guard (x-1) (by omega) (by omega) (n+1)
      rw [show x-1+1=x by omega] at hg
      simpa only [show (↑(x-1:ℕ):ℤ)=(x:ℤ)-1 by omega] using hg
  have h := (matches_on_edges n p dark sp).1
  rw [dark] at h; exact h

end Guard545

namespace Digits545
open OMA.S_oeis_a289096 PowerSeries Guard545

def bit (c l r d u : Bool) : Bool :=
  Nat.testBit 545 (c.toNat + 2*(l.toNat+r.toNat+d.toNat+u.toNat))

lemma tick (t : ℕ) (x y : ℤ) : state (t+1) x y =
    bit (state t x y) (state t (x-1) y) (state t (x+1) y) (state t x (y-1)) (state t x (y+1)) := rfl

lemma symmetries (t : ℕ) : (∀ x y, state t y x = state t x y) ∧
    (∀ x y, state t (-x) (-y) = state t x y) := by
  induction t with
  | zero =>
    constructor <;> intro x y <;> simp [state, and_comm]
  | succ t ih =>
    constructor
    · intro x y
      simp only [state,OMA.S_oeis_a289096.step]
      rw [ih.1 x y,ih.1 x (y-1),ih.1 x (y+1),ih.1 (x-1) y,ih.1 (x+1) y]
      congr 1
      omega
    · intro x y
      simp only [state,OMA.S_oeis_a289096.step]
      rw [show -x-1 = -(x+1) by omega,show -x+1 = -(x-1) by omega,
          show -y-1 = -(y+1) by omega,show -y+1 = -(y-1) by omega]
      simp only [ih.2]
      congr 1
      omega

def OuterDiagonal : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ x : ℕ, 2 ≤ x → state t x x = true

lemma center (outer : OuterDiagonal) (k : ℕ) :
    state (k+4) 0 0 = decide (k%2=0) ∧ state (k+4) 1 1 = decide (k%2=1) ∧
    state (k+4) 1 0 = false ∧ state (k+4) 2 1 = false := by
  induction k with
  | zero => decide
  | succ k ih =>
    let t := k+4
    obtain ⟨h0,h1,h10,h21⟩ := ih
    change state t 0 0 = _ at h0
    change state t 1 1 = _ at h1
    change state t 1 0 = _ at h10
    change state t 2 1 = _ at h21
    have h01 : state t 0 1 = false := (symmetries t).1 1 0 |>.trans h10
    have h12 : state t 1 2 = false := (symmetries t).1 2 1 |>.trans h21
    have hm10 : state t (-1) 0 = false := (symmetries t).2 1 0 |>.trans h10
    have h0m1 : state t 0 (-1) = false := (symmetries t).1 (-1) 0 |>.trans hm10
    have h22 : state t 2 2 = true := outer t (by dsimp [t]; omega) 2 (by decide)
    change state (t+1) 0 0 = _ ∧ state (t+1) 1 1 = _ ∧ state (t+1) 1 0 = _ ∧ state (t+1) 2 1 = _
    simp only [tick]
    norm_num only [show (0:ℤ)-1 = -1 by decide,show (0:ℤ)+1=1 by decide,
      show (1:ℤ)-1=0 by decide,show (1:ℤ)+1=2 by decide,show (2:ℤ)-1=1 by decide,
      show (2:ℤ)+1=3 by decide]
    simp only [h0,h1,h10,h21,h01,h12,hm10,h0m1,h22]
    rcases Nat.mod_two_eq_zero_or_one k with hk|hk <;>
      simp [Nat.add_mod,hk,bit] <;> cases state t 2 0 <;> cases state t 1 (-1) <;>
        cases state t 3 1 <;> decide


lemma read_num (n : ℕ) : (a n : ℤ) =
    ∑ d ∈ Finset.range (n+1), ((state n d d).toNat : ℤ)*10^d := by
  unfold a
  push_cast
  rw [←Finset.sum_range_reflect (fun d => ((state n d d).toNat : ℤ)*10^d) (n+1)]
  apply Finset.sum_congr rfl; intro j hj
  have hj' := Finset.mem_range.mp hj
  have h : (j:ℤ)-n = -((n-j : ℕ):ℤ) := by omega
  rw [show n+1-1=n by omega,h,(symmetries n).2]

lemma geom (n : ℕ) : 9*(∑ d ∈ Finset.range (n+1), (10:ℤ)^d) = 10^(n+1)-1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ,pow_succ (10:ℤ) (n+1)]; linarith only [ih]

lemma gap (n e : ℕ) (he : e≤n) (h : ∀ d : ℕ, state n d d = decide (d≠e)) :
    9*(a n:ℤ)=10^(n+1)-1-9*10^e := by
  rw [read_num]
  have dig (d : ℕ) : ((state n d d).toNat : ℤ)*10^d = 10^d - (if d=e then (10:ℤ)^d else 0) := by
    by_cases hd : d=e <;> simp [h,hd]
  simp_rw [dig]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range, if_pos (show e<n+1 by omega), mul_sub]
  rw [geom]

def T (n : ℕ) : ℤ := 10^(n+1)-1-9*10^(if n%2=0 then 1 else 0)

lemma tail (n : ℕ) (hn : 3≤n) : 9*(a n:ℤ)=T n := by
  by_cases h3 : n=3
  · subst n; decide
  obtain ⟨k,rfl⟩ : ∃ k,n=k+4 := ⟨n-4,by omega⟩
  have outer : OuterDiagonal := fun t ht x hx => diagonal_on t x (by omega) hx
  obtain ⟨h0,h1,_,_⟩ := center outer k
  rcases Nat.mod_two_eq_zero_or_one k with hk|hk
  · have h := gap (k+4) 1 (by omega) (by
      intro d; rcases d with _|(_|d)
      · simpa [hk] using h0
      · simpa [hk] using h1
      · simpa [add_assoc] using outer (k+4) (by omega) (d+2) (by omega))
    simpa [T,Nat.add_mod,hk] using h
  · have h := gap (k+4) 0 (by omega) (by
      intro d; rcases d with _|(_|d)
      · simpa [hk] using h0
      · simpa [hk] using h1
      · simpa [add_assoc] using outer (k+4) (by omega) (d+2) (by omega))
    simpa [T,Nat.add_mod,hk] using h

lemma recur : ∀ n : ℕ, 5 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+6 := ⟨n-6,by omega⟩
  rw [show k+6-1=k+5 by omega, show k+6-2=k+4 by omega, show k+6-3=k+3 by omega]
  have q3 := tail (k+3) (by omega)
  have q4 := tail (k+4) (by omega)
  have q5 := tail (k+5) (by omega)
  have q6 := tail (k+6) (by omega)
  rcases Nat.mod_two_eq_zero_or_one k with hk|hk
  · simp only [T,show (k+3)%2=1 by omega, show (k+4)%2=0 by omega, show (k+5)%2=1 by omega, show (k+6)%2=0 by omega] at q3 q4 q5 q6
    norm_num at q3 q4 q5 q6
    simp only [show k+3-1=k+2 by omega, show k+4-1=k+3 by omega, show k+5-1=k+4 by omega, show k+6-1=k+5 by omega,Nat.sub_zero,pow_add] at q3 q4 q5 q6
    linarith only [q3,q4,q5,q6]
  · simp only [T,show (k+3)%2=0 by omega, show (k+4)%2=1 by omega, show (k+5)%2=0 by omega, show (k+6)%2=1 by omega] at q3 q4 q5 q6
    norm_num at q3 q4 q5 q6
    simp only [show k+3-1=k+2 by omega, show k+4-1=k+3 by omega, show k+5-1=k+4 by omega, show k+6-1=k+5 by omega,Nat.sub_zero,pow_add] at q3 q4 q5 q6
    linarith only [q3,q4,q5,q6]

lemma series : PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (X + 1) * (10 * X - 1)) =
      100 * X ^ 5 - 10 * X ^ 4 + 10 * X ^ 2 + 1 := by
  suffices h : (1:ℤ) • (mk (fun n => (a n:ℤ)) * X^0) + (-10:ℤ) • (mk (fun n => (a n:ℤ)) * X^1) + (-1:ℤ) • (mk (fun n => (a n:ℤ)) * X^2) + (10:ℤ) • (mk (fun n => (a n:ℤ)) * X^3) = (1:ℤ) • ((X:PowerSeries ℤ)^0) + (10:ℤ) • ((X:PowerSeries ℤ)^2) + (-10:ℤ) • ((X:PowerSeries ℤ)^4) + (100:ℤ) • ((X:PowerSeries ℤ)^5) by
    simp only [zsmul_eq_mul] at h; linear_combination h
  ext n
  simp only [map_add,map_zsmul,coeff_mul_X_pow',coeff_X_pow,coeff_mk]
  by_cases hv : 5<n
  · simp only [zsmul_eq_mul,Nat.sub_zero, if_pos (show 0≤n by omega), if_pos (show 1≤n by omega), if_pos (show 2≤n by omega), if_pos (show 3≤n by omega),
      if_neg (show n≠0 by omega), if_neg (show n≠1 by omega), if_neg (show n≠2 by omega), if_neg (show n≠3 by omega), if_neg (show n≠4 by omega), if_neg (show n≠5 by omega)]
    norm_num
    linarith only [recur n hv]
  · interval_cases n <;> decide
end Digits545

theorem OMA.solution : type_of% @OMA.S_oeis_a289096.main := ⟨Digits545.recur,Digits545.series⟩
