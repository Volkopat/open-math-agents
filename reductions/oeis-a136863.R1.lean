import OMAStatements.S_oeis_a136863
import Mathlib

/-!
Robert Israel’s restricted-square problem. Any new example has at least four
nonzero digits. Starting at the units end, its first two are 1 and 7. The
spacing of the third digit, and sometimes its value, are forced by the square.
The two remaining hypotheses distinguish a 7 in the tens position from a
longer initial zero gap. Both follow from the original conjecture.
-/
namespace OMA.R_oeis_a136863_R1
open OMA.S_oeis_a136863

lemma last_ok {n : ℕ} (h : UsesDigits n) :
    n%10=0 ∨ n%10=1 ∨ n%10=4 ∨ n%10=7 := by
  by_cases hn : n=0
  · simp [hn]
  · have hm : n%10 ∈ Nat.digits 10 n := by rw [Nat.digits_eq_cons_digits_div (by decide) hn]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using h _ hm

lemma div_one_ok {n : ℕ} (h : UsesDigits n) : UsesDigits (n/10) := by
  by_cases hn : n=0
  · simp [hn,UsesDigits]
  · intro d hd
    apply h
    rw [Nat.digits_eq_cons_digits_div (by decide) hn]
    exact List.mem_cons_of_mem _ hd

lemma div_ok {n : ℕ} (h : UsesDigits n) (j : ℕ) : UsesDigits (n/10^j) := by
  induction j with
  | zero => simpa
  | succ j ih => simpa only [pow_succ,← Nat.div_div_eq_div_mul] using div_one_ok ih

lemma read_high {n lo hi : ℕ} (j : ℕ) (h : UsesDigits n)
    (eq : n=lo+10^j*hi) (bound : lo<10^j) : UsesDigits hi := by
  have hh := div_ok h j
  rw [eq,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt bound,Nat.zero_add] at hh
  exact hh

lemma read_low {v : ℕ} (h : UsesDigits v) (hs : UsesDigits (v^2)) (hv : v%10≠0) :
    v%10=1 := by
  have u := last_ok hs
  rw [pow_two,Nat.mul_mod] at u
  rcases last_ok h with e|e|e|e <;> simp_all

lemma power10_zero {j : ℕ} (h : 0<j) : 10^j%10=0 := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  simp [pow_succ]

lemma no_gap {l v j : ℕ} (hj : 0<j) (h : UsesDigits (l+10^j*v))
    (hs : UsesDigits ((l+10^j*v)^2)) (hl : l%10=1) (hv : v%10≠0)
    (bound : l^2<10^j) (mid : 2*l*v<10^j) : False := by
  have ll : l<10^j := by by_cases e : l=0 <;> simp_all <;> nlinarith [Nat.one_le_pow j 10 (by decide)]
  have vgood := read_high j h rfl ll
  have w := read_high j hs (lo:=l^2) (hi:=2*l*v+10^j*v^2) (by ring) bound
  have v2 := read_high j w rfl mid
  have tail := read_low vgood v2 hv
  have fail := last_ok w
  have e : (2*l*v+10^j*v^2) ≡ 2*1*1+0*v^2 [MOD 10] :=
    (((Nat.ModEq.refl 2).mul (show l ≡ 1 [MOD 10] from hl)).mul
      (show v ≡ 1 [MOD 10] from tail)).add
      ((show 10^j ≡ 0 [MOD 10] from power10_zero hj).mul_right _)
  have eq : (2*l*v+10^j*v^2)%10=2 := by simpa only [Nat.ModEq,zero_mul,add_zero,mul_one] using e
  omega

lemma next_digit {u t : ℕ} (ht : 0<t) (h : UsesDigits (1+10^t*u))
    (hs : UsesDigits ((1+10^t*u)^2)) (hu : u%10≠0) : u%10=7 := by
  have base : 1<10^t := one_lt_pow₀ (by decide) ht.ne'
  have a := last_ok (read_high t h rfl base)
  have w := read_high t hs (lo:=1) (hi:=2*u+10^t*u^2) (by ring) base
  have e := last_ok w
  have val : (2*u+10^t*u^2) ≡ 2*(u%10)+0*u^2 [MOD 10] :=
    ((Nat.ModEq.refl 2).mul (show u ≡ u%10 [MOD 10] by simp [Nat.ModEq])).add
      ((show 10^t ≡ 0 [MOD 10] from power10_zero ht).mul_right _)
  change (2*u+10^t*u^2)%10=(2*(u%10)+0*u^2)%10 at val
  rcases a with z|z|z|z <;> simp_all

open OMA.S_oeis_a136863

lemma top_squared {l v j : ℕ} (h : UsesDigits ((l+10^j*v)^2))
    (hl : l<10^j) (hu : (2*v+1)*l<10^j) : UsesDigits (v^2) := by
  apply read_high (j+j) h (lo:=l^2+2*l*10^j*v)
  · rw [pow_add]; ring
  · rw [pow_add]
    calc l^2+2*l*10^j*v ≤ (2*v+1)*l*10^j := by nlinarith [Nat.mul_le_mul_left l hl.le]
         _ < 10^j*10^j := Nat.mul_lt_mul_of_pos_right hu (by positivity)

lemma spaced {t d a : ℕ} (ht : 3≤t) (hd : 3≤d) (ha : a=1 ∨ a=4 ∨ a=7)
    (hs : UsesDigits ((1+7*10^t+10^(t+d)*a)^2)) : False := by
  let p := 10^t
  let q := 10^d
  have hp : 1000≤p := Nat.pow_le_pow_right (by decide : 0<10) ht
  have hq : 1000≤q := Nat.pow_le_pow_right (by decide : 0<10) hd
  have eq : 10^(t+d)=p*q := pow_add _ _ _
  have small : (2*a+1)*(1+7*p)<p*q := by
    rcases ha with rfl|rfl|rfl <;> nlinarith [Nat.mul_le_mul_left p hq]
  have le : 1+7*p<p*q := by nlinarith [Nat.mul_le_mul_left p hq]
  have top := top_squared (l:=1+7*p) (v:=a) (j:=t+d) hs (by rwa [eq]) (by rwa [eq])
  have aone : a=1 := by
    have z := last_ok top
    rcases ha with h|h|h
    · exact h
    · norm_num [h] at z
    · norm_num [h] at z
  subst a
  change UsesDigits ((1+7*p+10^(t+d)*1)^2) at hs
  rw [eq,mul_one] at hs
  have low : 1+14*p<p*q := by nlinarith [Nat.mul_le_mul_left p hq]
  have low2 : 1+14*p<p*p := by nlinarith [Nat.mul_le_mul_left p hp]
  rcases lt_trichotomy d t with lt|same|gt
  · let r := 10^(t-(d+1))
    have hpq : p=q*10*r := by
      dsimp [p,q,r]
      conv_lhs => rw [show t=d+1+(t-(d+1)) by omega,pow_add,pow_succ]
    let w := 49*r+14*q*r+q^2*r
    have high : UsesDigits (2+10*w) := by
      apply read_high (t+d) hs (lo:=1+14*p)
      · rw [eq]; dsimp [w]; rw [hpq]; ring
      · rwa [eq]
    have z := last_ok high
    omega
  · subst d
    have pq : q=p := rfl
    let r := 10^(t-2)
    have hp2 : p=100*r := by
      dsimp [p,r]
      conv_lhs => rw [show t=2+(t-2) by omega,pow_add]
      norm_num
    let w := 14*r+100*r^2
    have high : UsesDigits (51+100*w) := by
      apply read_high (t+t) hs (lo:=1+14*p)
      · rw [eq,pq]; dsimp [w]; rw [hp2]; ring
      · simpa only [eq,pq] using low2
    have z := last_ok (div_one_ok high)
    omega
  · let r := 10^(d-(t+1))
    have hqp : q=p*10*r := by
      dsimp [p,q,r]
      conv_lhs => rw [show d=t+1+(d-(t+1)) by omega,pow_add,pow_succ]
    let w := 4+2*r+14*p*r+10*(p*r)^2
    have high : UsesDigits (9+10*w) := by
      apply read_high (t+t) hs (lo:=1+14*p)
      · rw [pow_add]; change (1+7*p+p*q)^2=1+14*p+p*p*(9+10*w)
        dsimp [w]; rw [hqp]; ring
      · simpa only [pow_add] using low2
    have z := last_ok high
    omega

lemma sparse_three {t d a : ℕ} (ht : 0<t) (hd : 0<d) (ha : a=1 ∨ a=4 ∨ a=7)
    (h : UsesDigits (1+7*10^t+10^(t+d)*a)) (hs : UsesDigits ((1+7*10^t+10^(t+d)*a)^2)) :
    1+7*10^t+10^(t+d)*a=1071 := by
  have small := not_and_or.mp (fun e : 3≤t ∧ 3≤d => spaced e.1 e.2 ha hs)
  have aa : a≤7 := by omega
  have aa' : a%10≠0 := by omega
  have bottom : (1+7*10^t)%10=1 := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    rw [pow_succ]; omega
  have bounds : t≤3 ∧ d≤4 := by
    rcases small with st|sd
    · have p : 10^t≤100 := Nat.pow_le_pow_right (by decide : 0<10) (by omega : t≤2)
      by_contra! bad
      have big : 1000000≤10^(t+d) := Nat.pow_le_pow_right (by decide : 0<10) (by omega : 6≤t+d)
      apply no_gap (by omega : 0<t+d) h hs bottom aa'
      · nlinarith [Nat.mul_self_le_mul_self (show 1+7*10^t≤701 by omega)]
      · nlinarith [Nat.mul_le_mul (show 1+7*10^t≤701 by omega) aa]
    · have q : 10^d≤100 := Nat.pow_le_pow_right (by decide : 0<10) (by omega : d≤2)
      by_contra! bad
      have big : 10000≤10^t := Nat.pow_le_pow_right (by decide : 0<10) (by omega : 4≤t)
      have form : 1+7*10^t+10^(t+d)*a=1+10^t*(7+10^d*a) := by rw [pow_add]; ring
      rw [form] at h hs
      have unit : (7+10^d*a)%10≠0 := by
        obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
        rw [pow_succ]; ring_nf; omega
      exact no_gap ht h hs rfl unit (by norm_num; omega)
        (by nlinarith [Nat.mul_le_mul q aa])
  rcases bounds with ⟨tmax,dmax⟩
  interval_cases t <;> interval_cases d <;> rcases ha with rfl|rfl|rfl <;>
    first | rfl | exfalso; revert hs; unfold UsesDigits; decide
open OMA.S_oeis_a136863

lemma strip (u : ℕ) (hu : 0<u) :
    ∃ t v : ℕ, v%10≠0 ∧ u=10^t*v := by
  by_cases h : u%10=0
  · obtain ⟨t,v,hv,eq⟩ := strip (u/10) (by omega)
    refine ⟨t+1,v,hv,?_⟩
    have e : u=10*(u/10) := by omega
    calc u = 10*(u/10) := e
         _ = 10^(t+1)*v := by rw [eq,pow_succ]; ring
  · exact ⟨0,u,h,by simp⟩
termination_by u
decreasing_by omega

lemma append_ok {l t u : ℕ} (hl : l=1 ∨ l=7) (ht : 0<t) (hu : UsesDigits u) :
    UsesDigits (l+10^t*u) := by
  by_cases e : u=0
  · subst u
    rcases hl with rfl|rfl <;> simp [UsesDigits]
  · have dt : (Nat.digits 10 l).length = 1 := by rcases hl with rfl|rfl <;> decide
    have w := Nat.digits_append_zeroes_append_digits (b:=10) (m:=u) (n:=l)
      (k:=t-1) (by decide) (by omega)
    rw [dt,show 1+(t-1)=t by omega] at w
    intro a ha
    rw [← w] at ha
    rcases List.mem_append.mp ha with hh|hh
    · rcases List.mem_append.mp hh with hh|hh
      · have digits : Nat.digits 10 l = [l] := by rcases hl with rfl|rfl <;> decide
        rw [digits,List.mem_singleton] at hh
        rcases hl with rfl|rfl <;> simp [hh]
      · have eq := List.eq_of_mem_replicate hh
        simp [eq]
    · exact hu a hh

lemma no_two {t : ℕ} (ht : 0<t) (h : UsesDigits (1+10^t*7))
    (hs : UsesDigits ((1+10^t*7)^2)) : False := by
  by_cases e : t=1
  · subst t
    revert hs
    unfold UsesDigits
    decide +kernel
  · have big : 100≤10^t := Nat.pow_le_pow_right (by decide : 0<10) (by omega : 2≤t)
    exact no_gap ht h hs rfl (by decide) (by norm_num; omega) (by omega)

lemma third_window {t d v : ℕ} (ht : 0<t) (hd : 0<d)
    (h : UsesDigits ((1+10^t*(7+10^d*v))^2)) : d ≤ max 2 t := by
  by_contra! hh
  by_cases e : t=1
  · subst t
    let r := 10^(d-3)
    have eq : 10^d=1000*r := by
      dsimp [r]
      conv_lhs => rw [show d=3+(d-3) by omega,pow_add]
      norm_num
    have high : UsesDigits (5+10*(142*r*v+10000*(r*v)^2)) := by
      apply read_high 3 h (lo:=41)
      · rw [eq]; ring
      · decide
    have bad := last_ok high
    omega
  · let p := 10^t
    let r := 10^(d-(t+1))
    have eq : 10^d=p*10*r := by
      dsimp [p,r]
      conv_lhs => rw [show d=t+1+(d-(t+1)) by omega,pow_add,pow_succ]
    have big : 100≤p := Nat.pow_le_pow_right (by decide : 0<10) (by omega : 2≤t)
    let z := r*v
    have high : UsesDigits (9+10*(4+2*z+14*p*z+10*p^2*z^2)) := by
      apply read_high (t+t) h (lo:=1+14*p)
      · rw [eq,pow_add]; change (1+p*(7+p*10*r*v))^2=1+14*p+p*p*_
        dsimp [z]; ring
      · rw [pow_add]; change 1+14*p<p*p; nlinarith [Nat.mul_le_mul_left p big]
    have bad := last_ok high
    omega

lemma sparse_tail_ne {d v : ℕ} (hd : 0<d) (hv : 10≤v) (nz : v%10≠0) :
    7+10^d*v≠107 := by
  intro eq
  by_cases e : d=1
  · subst d; norm_num at eq; omega
  · have q : 100≤10^d := Nat.pow_le_pow_right (by decide : 0<10) (by omega : 2≤d)
    nlinarith [Nat.mul_le_mul q hv]
open OMA.S_oeis_a136863

lemma alignment {t d v : ℕ} (ht : 2≤t) (hd : 0<d) (hv : v%10≠0)
    (vg : UsesDigits v) (sq : UsesDigits ((1+10^t*(7+10^d*v))^2)) :
    2≤d ∧ ((d=t ∧ (v%10=1 ∨ v%10=4)) ∨ (d<t ∧ v%10=7)) := by
  let p := 10^t
  let q := 10^d
  have win := third_window (by omega : 0<t) hd sq
  have small : d≤t := by omega
  have ppos : 100≤p := Nat.pow_le_pow_right (by decide : 0<10) ht
  have top : UsesDigits (2*(7+q*v)+p*(7+q*v)^2) := by
    apply read_high t sq (lo:=1) 
    · change (1+p*(7+q*v))^2=1+p*(2*(7+q*v)+p*(7+q*v)^2); ring
    · change 1<p; omega
  have digits := last_ok vg
  have rule : ∀ (b w : ℕ), UsesDigits (b+2*v+10*w) →
        (b+2*(v%10))%10=0 ∨ (b+2*(v%10))%10=1 ∨
        (b+2*(v%10))%10=4 ∨ (b+2*(v%10))%10=7 := by
    intro b w good
    have hi := last_ok good
    have E : (b+2*v+10*w) ≡ b+2*(v%10)+0*w [MOD 10] :=
      ((Nat.ModEq.refl b).add ((Nat.ModEq.refl 2).mul
        (show v ≡ v%10 [MOD 10] by simp [Nat.ModEq]))).add
        ((show 10 ≡ 0 [MOD 10] by decide).mul_right _)
    change (b+2*v+10*w)%10=(b+2*(v%10)+0*w)%10 at E
    simp only [zero_mul,add_zero] at E
    simpa only [E] using hi
  have two : 2≤d := by
    by_contra! hh
    have e : d=1 := by omega
    have qp : q=10 := by simp [q,e]
    let r := 10^(t-2)
    have eq : p=100*r := by
      dsimp [p,r]
      conv_lhs => rw [show t=2+(t-2) by omega,pow_add]
      norm_num
    have g : UsesDigits (1+2*v+10*(r*(7+10*v)^2)) := by
      apply read_high 1 top (lo:=4)
      · rw [qp,eq]; ring
      · decide
    have z := rule 1 _ g
    omega
  refine ⟨two,?_⟩
  rcases eq_or_lt_of_le small with eq|lt
  · left; refine ⟨eq,?_⟩
    have qp : q=p := by simp [q,p,eq]
    let r := 10^(t-1)
    have pr : p=10*r := by
      dsimp [p,r]
      conv_lhs => rw [show t=1+(t-1) by omega,pow_add]
      norm_num
    let w := 14*r*v+10*r^2*v^2
    have g : UsesDigits (49+2*v+10*w) := by
      apply read_high (t+t) sq (lo:=1+14*p)
      · change (1+p*(7+q*v))^2=1+14*p+10^(t+t)*(49+2*v+10*w)
        rw [qp,pow_add]; change (1+p*(7+p*v))^2=1+14*p+p*p*(49+2*v+10*w)
        dsimp [w]; rw [pr]; ring
      · rw [pow_add]; change 1+14*p<p*p; nlinarith [Nat.mul_le_mul_left p ppos]
    have z := rule 49 _ g
    omega
  · right; refine ⟨lt,?_⟩
    let r := 10^(t-(d+1))
    have pr : p=q*10*r := by
      dsimp [p,q,r]
      conv_lhs => rw [show t=d+1+(t-(d+1)) by omega,pow_add,pow_succ]
    have qpos : 100≤q := Nat.pow_le_pow_right (by decide : 0<10) two
    have g : UsesDigits (0+2*v+10*(r*(7+q*v)^2)) := by
      apply read_high d top (lo:=14)
      · change 2*(7+q*v)+p*(7+q*v)^2=14+q*(0+2*v+10*(r*(7+q*v)^2))
        rw [pr]; ring
      · change 14<q; omega
    have z := rule 0 _ g
    omega
open OMA.S_oeis_a136863

def H1 : Prop :=
  ∀ d v : ℕ, 1≤d → d≤2 → 10≤v → v%10≠0 → UsesDigits v →
    let u := 7+10^d*v
    ¬ UsesDigits (2*u+10*u^2)

def H2 : Prop :=
  ∀ t d v : ℕ, 2≤t → 2≤d → 10≤v → v%10≠0 → UsesDigits v →
    ((d=t ∧ (v%10=1 ∨ v%10=4)) ∨ (d<t ∧ v%10=7)) →
    let u := 7+10^d*v
    10^t≤2*u → ¬ UsesDigits (2*u+10^t*u^2)

lemma normalize {n : ℕ} (h : UsesDigits n) (hs : UsesDigits (n^2))
    (hn : ¬10∣n) (ne : n≠1) :
    ∃ t d v : ℕ, 0<t ∧ 0<d ∧ v%10≠0 ∧ UsesDigits v ∧
      n=1+10^t*(7+10^d*v) ∧ UsesDigits (2*(7+10^d*v)+10^t*(7+10^d*v)^2) ∧
      10^t≤2*(7+10^d*v) := by
  have mod := read_low h hs (by simpa only [Nat.dvd_iff_mod_eq_zero] using hn)
  obtain ⟨t,u,un,ue⟩ := strip (n-1) (by omega)
  have tpos : 0<t := by
    by_contra! e
    have : t=0 := by omega
    simp [this] at ue
    omega
  have eq : n=1+10^t*u := by omega
  rw [eq] at h hs
  have p : 1<10^t := one_lt_pow₀ (by decide) tpos.ne'
  have ug := read_high t h rfl p
  have last := next_digit tpos h hs un
  by_cases u7 : u=7
  · subst u; exact (no_two tpos h hs).elim
  have enough : 10^t≤2*u := by
    by_contra! mid
    exact no_gap tpos h hs rfl un (by simpa using p) (by omega)
  have ug2 := read_high t hs (lo:=1) (hi:=2*u+10^t*u^2) (by ring) p
  obtain ⟨d,v,vn,ve⟩ := strip (u-7) (by omega)
  have dpos : 0<d := by
    by_contra! e
    have : d=0 := by omega
    simp [this] at ve
    omega
  have eq2 : u=7+10^d*v := by omega
  have q : 10≤10^d := Nat.pow_le_pow_right (by decide : 0<10) (show 1≤d by omega)
  have vg := read_high d ug eq2 (by omega)
  exact ⟨t,d,v,tpos,dpos,vn,vg,by rwa [← eq2],by rwa [← eq2],by rwa [← eq2]⟩

lemma necessary (claim : {k : ℕ | UsesDigits k ∧ UsesDigits (k^2) ∧ ¬10∣k}={1,1071}) :
    H1 ∧ H2 := by
  have exclude {t d v : ℕ} (ht : 0<t) (hd : 0<d) (hv : 10≤v) (nz : v%10≠0)
      (vg : UsesDigits v) : ¬ UsesDigits (2*(7+10^d*v)+10^t*(7+10^d*v)^2) := by
    intro hs
    let u := 7+10^d*v
    have ug : UsesDigits u := append_ok (Or.inr rfl) hd vg
    have ng := append_ok (l:=1) (Or.inl rfl) ht ug
    have ng2 := append_ok (l:=1) (Or.inl rfl) ht hs
    have nform : (1+10^t*u)^2 = 1+10^t*(2*u+10^t*u^2) := by ring
    have nzero : ¬10∣1+10^t*u := by
      obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
      rw [pow_succ]
      intro h
      have eq : 1+(10^i*10)*u=1+10*(10^i*u) := by ring
      rw [eq] at h; omega
    have mem : 1+10^t*u ∈ ({1,1071} : Set ℕ) := by
      rw [← claim]
      exact ⟨ng,by rwa [nform],nzero⟩
    have up : 0<u := by dsimp [u]; positivity
    have pp : 0<10^t*u := by positivity
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at mem
    rcases mem with e|e
    · omega
    · by_cases t1 : t=1
      · subst t; norm_num at e
        exact sparse_tail_ne hd hv nz (by change u=107; omega)
      · have dvd : 100 ∣ 10^t*u :=
          dvd_mul_of_dvd_left (pow_dvd_pow 10 (show 2≤t by omega)) u
        omega
  constructor
  · intro d v hd _ hv hn hg
    simpa using exclude (t:=1) (by decide) hd hv hn hg
  · intro t d v ht hd hv hn hg _
    change 10^t≤2*(7+10^d*v) → ¬ UsesDigits (2*(7+10^d*v)+10^t*(7+10^d*v)^2)
    intro _
    exact exclude (t:=t) (d:=d) (by omega) (by omega) hv hn hg

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a136863.main := by
  intro h1 h2
  ext n
  simp only [Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨h,hs,hn⟩
    by_cases one : n=1
    · exact Or.inl one
    right
    obtain ⟨t,d,v,ht,hd,vn,vg,eq,ug2,enough⟩ := normalize h hs hn one
    have sq := eq ▸ hs
    have form : 1+10^t*(7+10^d*v)=1+7*10^t+10^(t+d)*v := by rw [pow_add]; ring
    by_cases small : v<10
    · have z := last_ok vg
      have which : v=1 ∨ v=4 ∨ v=7 := by omega
      rw [eq,form]
      exact sparse_three ht hd which (by rwa [← form,← eq]) (by rwa [← form,← eq])
    · by_cases t1 : t=1
      · subst t
        have win := third_window ht hd sq
        exact (h1 d v hd (by omega) (by omega) vn vg (by simpa using ug2)).elim
      · have tt : 2≤t := by omega
        have ali := alignment tt hd vn vg sq
        exact (h2 t d v tt ali.1 (by omega) vn vg ali.2 enough ug2).elim
  · rintro (rfl|rfl) <;> unfold UsesDigits <;> decide

end OMA.R_oeis_a136863_R1
