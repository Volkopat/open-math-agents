import OMAStatements.S_mse_2637546
import Mathlib

/-!
Square-sum paths for every order at least 25, using the paired-path construction
of Robert Gerbicz (2018, OEIS A090461). The finite data encode his substitution
words and seed paths, with later seeds reconstructed by suffix reversals.
At each induction step both paths use the same position parity for each common
label. This determines the sign of its displacement in each lifted block.
-/

namespace SquarePaths

/-- Exactly the new seam must be checked at a Pósa rotation. -/
theorem rotate_chain (a b : List ℕ) (h : (a++b).IsChain (fun x y => IsSquare (x+y)))
    (join : ∀ x ∈ a.getLast?, ∀ y ∈ b.getLast?, IsSquare (x+y)) :
    (a++b.reverse).IsChain (fun x y => IsSquare (x+y)) := by
  obtain ⟨ha,hb,-⟩ := List.isChain_append.mp h
  refine List.IsChain.append ha (List.isChain_reverse.mpr ?_) ?_
  · simpa only [Nat.add_comm] using hb
  · simpa using join

/-- Inside an odd reversed suffix, each old label retains its global position parity. -/
theorem suffix_index (a b : List ℕ) (odd : b.length % 2 = 1) (j : ℕ) (hj : j < b.length) :
    (a.length + (b.length-1-j)) % 2 = (a.length+j) % 2 ∧
    (a ++ b.reverse)[a.length+(b.length-1-j)]'(
      by simp only [List.length_append, List.length_reverse]; omega) =
      (a++b)[a.length+j]'(by simp; omega) := by
  constructor
  · omega
  · simp only [List.getElem_append_right (by omega : a.length ≤ a.length + (b.length-1-j)),
      List.getElem_append_right (by omega : a.length ≤ a.length + j),
      Nat.add_sub_cancel_left, List.getElem_reverse]
    congr 1; omega



/-- Packed seed arithmetic is valid for every split, irrespective of the certificate. -/
def pack : List ℕ → ℕ
  | [] => 0
  | x::xs => x + 2048 * pack xs

theorem pack_append (xs ys : List ℕ) :
    pack (xs ++ ys) = pack xs + 2048^xs.length * pack ys := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih => simp [pack,ih,pow_succ]; ring

theorem pack_lt (xs : List ℕ) (h : ∀ x ∈ xs, x < 2048) :
    pack xs < 2048^xs.length := by
  induction xs with
  | nil => simp [pack]
  | cons a xs ih =>
    have ha := h a (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [pack,List.length_cons,pow_succ]
    omega

theorem split_pack (xs ys : List ℕ) (h : ∀ x ∈ xs, x < 2048) :
    (pack (xs++ys)) >>> (11*xs.length) = pack ys := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul, pack_append]
  change (pack xs + 2048 ^ xs.length * pack ys) / 2048 ^ xs.length = pack ys
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (pack_lt xs h), zero_add]



theorem pack_shift (v k : ℕ) : v <<< (11*k) = 2048^k * v := by
  rw [Nat.shiftLeft_eq, pow_mul, Nat.mul_comm]
  rfl

/-- Both packed words after replacing suffix b by its reversal. -/
theorem spin_pack (a b : List ℕ)
    (ha : ∀ x ∈ a, x < 2048) (hb : ∀ x ∈ b, x < 2048) :
    let f := pack (a++b)
    let r := pack (b.reverse++a.reverse)
    let u := f >>> (11*a.length)
    let v := r >>> (11*b.length)
    pack (a++b.reverse) = f - (u <<< (11*a.length)) +
      ((r-(v <<< (11*b.length))) <<< (11*a.length)) ∧
    pack (b++a.reverse) = (v <<< (11*b.length)) + u := by
  dsimp only
  have hdiv : pack (b.reverse ++ a.reverse) >>> (11*b.length) = pack a.reverse := by
    simpa using split_pack b.reverse a.reverse (by simpa using hb)
  rw [split_pack a b ha,hdiv]
  simp only [pack_append, List.length_reverse, pack_shift, Nat.add_sub_cancel]
  exact ⟨trivial,Nat.add_comm _ _⟩

-- Least significant 11-bit digit is the first label; the largest is 2033.
structure PathCode where
  n : ℕ := 0
  fw : ℕ := 0
  bw : ℕ := 0
  ok : Bool := true
  deriving DecidableEq

def PathCode.appendLabel (p : PathCode) (x : ℕ) : PathCode :=
  { n := p.n+1, fw := p.fw + (x <<< (11*p.n)), bw := x + (p.bw <<< 11),
    ok := p.ok && (p.n == 0 || Nat.sqrt (p.bw%2048+x)^2 == p.bw%2048+x) }

def PathCode.spin (fixed : Bool) (p : PathCode) (k : ℕ) : PathCode :=
  let left := 11*k
  let right := 11*(p.n-k)
  let a := p.fw >>> left
  let b := p.bw >>> right
  let prev := (p.fw >>> (11*(k-1)))%2048
  let sum := prev+p.bw%2048
  { n := p.n, fw := p.fw - (a <<< left) + ((p.bw - (b <<< right)) <<< left),
    bw := (b <<< right) + a,
    ok := p.ok && 0 < k && k+1 < p.n && (!fixed || (p.n-k)%2==1) && sum.sqrt^2==sum }

def endVal (n : ℕ) := if n%2==0 then 8 else 3

def endpoints (p : PathCode) (n : ℕ) :=
  p.ok && p.n==n && p.fw%2048==1 && p.bw%2048==endVal n

abbrev labels (n : ℕ) := (List.range n).map Nat.succ
abbrev Chain (xs : List ℕ) := xs.IsChain (fun x y => IsSquare (x+y))
def Occ (xs : List ℕ) (x j : ℕ) : Prop :=
  ∃ i : Fin xs.length, xs[i.val] = x ∧ i.val % 2 = j
def Trans (xs ys : List ℕ) := ∀ x j, Occ xs x j → Occ ys x j
def Ready (n : ℕ) (xs : List ℕ) :=
  xs.Perm (labels n) ∧ Chain xs ∧ xs.head? = some 1 ∧ xs.getLast? = some (endVal n)
def Paired (n : ℕ) (s t : List ℕ) :=
  Ready n s ∧ Ready (n+1) t ∧ Trans (s++[n+1]) t
def P (n : ℕ) := ∃ s t, Paired n s t

structure Enc (p : PathCode) (xs : List ℕ) : Prop where
  len : p.n = xs.length
  fw : p.fw = pack xs
  bw : p.bw = pack xs.reverse
  bound : ∀ x ∈ xs, x < 2048
  chain : Chain xs

theorem pack_mod (a : ℕ) (xs : List ℕ) (ha : a < 2048) :
    pack (a::xs) % 2048 = a := by simp [pack,Nat.mod_eq_of_lt ha]
theorem digit_head (xs : List ℕ) (hb : ∀ x ∈ xs, x < 2048)
    (hn : xs ≠ []) : xs.head? = some (pack xs % 2048) := by
  cases xs with
  | nil => contradiction
  | cons x xs => simp [pack_mod _ _ (hb x (by simp))]
theorem end_sound {p : PathCode} {n : ℕ} {xs : List ℕ} (he : Enc p xs)
    (hok : endpoints p n = true) (hn : 0 < n) (hp : xs.Perm (labels n)) : Ready n xs := by
  simp only [endpoints, Bool.and_eq_true, beq_iff_eq] at hok
  have hne : xs ≠ [] := by intro h; have := he.len; simp [h] at this; omega
  refine ⟨hp,he.chain,?_,?_⟩
  · rw [digit_head xs he.bound hne, ← he.fw, hok.1.2]
  · rw [← List.head?_reverse, digit_head _ (by simpa using he.bound) (by simpa using hne),
        ← he.bw, hok.2]

theorem rot_trans (a b : List ℕ) (hodd : b.length%2=1) :
    Trans (a++b) (a++b.reverse) := by
  rintro x j ⟨⟨i,hi⟩,hx,rfl⟩
  by_cases hl : i < a.length
  · refine ⟨⟨i,by simp; omega⟩,?_,rfl⟩
    simpa only [List.getElem_append_left hl] using hx
  · have hh : i-a.length < b.length := by simp at hi; omega
    obtain ⟨hp,hv⟩ := suffix_index a b hodd (i-a.length) hh
    have ha : a.length + (i-a.length) = i := by omega
    refine ⟨⟨_,by simp; omega⟩,hv.trans ?_,hp.trans (by rw [ha])⟩
    simpa only [ha] using hx

theorem spin_ok {fix : Bool} {p : PathCode} {k : ℕ} (h : (p.spin fix k).ok = true) :
    p.ok = true := by simp [PathCode.spin] at h; tauto

theorem spin_sound {p : PathCode} {xs : List ℕ} (he : Enc p xs)
    (fix : Bool) (k : ℕ) (hok : (p.spin fix k).ok = true) :
    ∃ ys, Enc (p.spin fix k) ys ∧ ys.Perm xs ∧ (fix=true → Trans xs ys) := by
  simp only [PathCode.spin,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
    Bool.or_eq_true,Bool.not_eq_true'] at hok
  let a := xs.take k
  let b := xs.drop k
  have hab : a++b=xs := List.take_append_drop k xs
  have hk : k < xs.length := by have := he.len; omega
  have la : a.length = k := by simp [a,Nat.min_eq_left hk.le]
  have lb : b.length = p.n-k := by simp [b,he.len]
  have ba : ∀ x ∈ a, x < 2048 := fun x hx => he.bound x (List.mem_of_mem_take hx)
  have bb : ∀ x ∈ b, x < 2048 := fun x hx => he.bound x (List.mem_of_mem_drop hx)
  have hf : p.fw = pack (a++b) := by rw [hab,he.fw]
  have hr : p.bw = pack (b.reverse++a.reverse) := by rw [← List.reverse_append,hab,he.bw]
  have rot := spin_pack a b ba bb
  simp only [← hf,← hr,la,lb] at rot
  have perm : (a++b.reverse).Perm xs := by rw [← hab]; exact b.reverse_perm.append_left a
  refine ⟨a++b.reverse, ⟨he.len.trans perm.length_eq.symm,rot.1.symm,?_,
    fun x hx => he.bound x (perm.mem_iff.mp hx),?_⟩,perm,?_⟩
  · simp only [List.reverse_append,List.reverse_reverse]; exact rot.2.symm
  · apply rotate_chain _ _ (hab ▸ he.chain)
    intro x hx y hy
    have bx := ba x (List.mem_of_mem_getLast? hx)
    have by' := bb y (List.mem_of_mem_getLast? hy)
    obtain ⟨a',ha⟩ := List.getLast?_eq_some_iff.mp hx
    obtain ⟨b',hb⟩ := List.getLast?_eq_some_iff.mp hy
    have hlast : p.bw % 2048 = y := by rw [hr,hb]; simp [pack_mod _ _ by']
    have l : k-1 = a'.length := by rw [ha] at la; simp at la; omega
    have hprev : (p.fw >>> (11*(k-1)))%2048=x := by
      rw [hf,ha,List.append_assoc,l,split_pack _ _ (fun v hv => ba v (by simp [ha,hv]))]
      exact pack_mod _ _ bx
    have hs := hok.2
    rw [hprev,hlast] at hs
    exact ⟨(x+y).sqrt, by simpa [pow_two] using hs.symm⟩
  · intro h
    rw [← hab]
    exact rot_trans _ _ (by simpa [h,lb] using hok.1.2)

theorem spins_ok (ks : List ℕ) (fix : Bool) (q : PathCode)
    (hh : (ks.foldl (PathCode.spin fix) q).ok = true) : q.ok=true := by
  induction ks generalizing q with
  | nil => exact hh
  | cons k ks ih => exact spin_ok (ih _ hh)

theorem spins_sound (ks : List ℕ) (fix : Bool) {p : PathCode} {xs : List ℕ}
    (he : Enc p xs) (hok : (ks.foldl (PathCode.spin fix) p).ok = true) :
    p.ok = true ∧ ∃ ys, Enc (ks.foldl (PathCode.spin fix) p) ys ∧ ys.Perm xs ∧
      (fix=true → Trans xs ys) := by
  induction ks generalizing p xs with
  | nil => exact ⟨hok,xs,he,.refl _,fun _ _ _ h => h⟩
  | cons k ks ih =>
    obtain ⟨ys,hy,hp,ht⟩ := spin_sound he fix k (spins_ok ks fix _ hok)
    obtain ⟨h1,zs,hz,hq,hu⟩ := ih hy hok
    exact ⟨spin_ok h1,zs,hz,hq.trans hp,fun hf x j h => hu hf x j (ht hf x j h)⟩

theorem app_enc {p : PathCode} {xs : List ℕ} {x : ℕ} (he : Enc p xs)
    (hx : x < 2048) (hok : (p.appendLabel x).ok=true) : Enc (p.appendLabel x) (xs++[x]) := by
  refine ⟨by simp [PathCode.appendLabel,he.len],?_,?_,?_,?_⟩
  · simp [PathCode.appendLabel,he.fw,he.len,pack_append,pack_shift,pack]
  · simp [PathCode.appendLabel,he.bw,pack, Nat.shiftLeft_eq, Nat.mul_comm]
  · intro y hy
    simp only [List.mem_append,List.mem_singleton] at hy
    rcases hy with h|rfl
    · exact he.bound _ h
    · exact hx
  · refine List.IsChain.append he.chain (by simp) ?_
    intro a ha b hb
    have ha' := he.bound _ (List.mem_of_mem_getLast? ha)
    obtain ⟨u,hu⟩ := List.getLast?_eq_some_iff.mp ha
    have hlast : p.bw%2048=a := by rw [he.bw,hu]; simp [pack_mod _ _ ha']
    have hn : p.n ≠ 0 := by simp [he.len,hu]
    simp [PathCode.appendLabel,hn,hlast] at hok
    have hb' : b=x := by symm; simpa using hb
    subst b
    exact ⟨(a+x).sqrt,by simpa [pow_two] using hok.2.symm⟩

theorem trans_snoc {s t : List ℕ} (hp : t.Perm s) (h : Trans s t) (z : ℕ) :
    Trans (s++[z]) (t++[z]) := by
  rintro x j ⟨⟨i,hi⟩,hx,rfl⟩
  by_cases hs : i<s.length
  · obtain ⟨⟨k,hk⟩,hv,hpar⟩ := h x (i%2) ⟨⟨i,hs⟩,by simpa [List.getElem_append_left hs] using hx,rfl⟩
    exact ⟨⟨k,by simp; omega⟩,by simpa [List.getElem_append_left hk] using hv,hpar⟩
  · have he : i=s.length := by simp at hi; omega
    have ht := hp.length_eq
    subst i
    simp at hx
    exact ⟨⟨t.length,by simp⟩,by simpa using hx,congrArg (·%2) ht⟩

structure Move where
  prep : List ℕ
  before : List ℕ
  after : List ℕ

def extend (p : PathCode) (m : Move) : PathCode :=
  let a := m.prep.foldl (PathCode.spin false) p
  let s := m.before.foldl (PathCode.spin true) a
  let b := m.after.foldl (PathCode.spin true) (s.appendLabel (p.n+1))
  { b with ok := endpoints a p.n && endpoints b (p.n+1) }

def ValidCode (p : PathCode) := ∃ xs, Enc p xs ∧ xs.Perm (labels p.n)

theorem extend_ok {p : PathCode} {m : Move} (h : (extend p m).ok=true) : p.ok=true := by
  have h1 := (Bool.and_eq_true_iff.mp h).1
  simp only [endpoints,Bool.and_eq_true] at h1
  exact spins_ok _ _ _ h1.1.1.1

theorem extend_n {p : PathCode} {m : Move} (h : (extend p m).ok=true) :
    (extend p m).n = p.n+1 := by
  have h2 := (Bool.and_eq_true_iff.mp h).2
  simp only [endpoints,Bool.and_eq_true,beq_iff_eq] at h2
  exact h2.1.1.2

theorem extend_sound {p : PathCode} {m : Move} (hp : ValidCode p) (hn : 0 < p.n)
    (hl : p.n+1 < 2048) (hok : (extend p m).ok=true) : ValidCode (extend p m) ∧ P p.n := by
  obtain ⟨xs,he,hperm⟩ := hp
  let a := m.prep.foldl (PathCode.spin false) p
  let s := m.before.foldl (PathCode.spin true) a
  let b := m.after.foldl (PathCode.spin true) (s.appendLabel (p.n+1))
  have ⟨ha,hb⟩ : endpoints a p.n=true ∧ endpoints b (p.n+1)=true := Bool.and_eq_true_iff.mp hok
  have hbo : b.ok=true := by unfold endpoints at hb; simp only [Bool.and_eq_true] at hb; exact hb.1.1.1
  have hto := spins_ok m.after true _ hbo
  have hso : s.ok=true := (Bool.and_eq_true_iff.mp hto).1
  have hao := spins_ok m.before true _ hso
  obtain ⟨_,ys,hey,hyp,_⟩ := spins_sound m.prep false he hao
  obtain ⟨_,zs,hez,hzp,hzt⟩ := spins_sound m.before true hey hso
  obtain ⟨_,ts,het,htp,htt⟩ := spins_sound m.after true (app_enc hez hl hto) hbo
  have py := hyp.trans hperm
  have pt : ts.Perm (labels (p.n+1)) := by
    rw [labels,List.range_succ,List.map_append]
    exact htp.trans ((hzp.trans py).append_right _)
  refine ⟨⟨ts,⟨het.len,het.fw,het.bw,het.bound,het.chain⟩,?_⟩,ys,ts,
    end_sound hey ha hn py,end_sound het hb (by omega) pt,?_⟩
  · rw [extend_n hok]; exact pt
  · exact fun x j h => htt rfl x j (trans_snoc hzp (hzt rfl) _ x j h)

def walk (p : PathCode) (ms : List Move) := ms.foldl extend p
theorem walk_back (p : PathCode) (ms : List Move) (h : (walk p ms).ok=true) : p.ok=true := by
  induction ms generalizing p with
  | nil => exact h
  | cons m ms ih => exact extend_ok (ih _ h)

theorem walk_sound {p : PathCode} (ms : List Move) (hp : ValidCode p) (hn : 0 < p.n)
    (hl : p.n+ms.length < 2048) (hok : (walk p ms).ok=true) :
    ValidCode (walk p ms) ∧ ∀ i, p.n ≤ i → i < p.n+ms.length → P i := by
  induction ms generalizing p with
  | nil => exact ⟨hp,by intro i hi hi'; simp at hi'; omega⟩
  | cons m ms ih =>
    have ho := walk_back (extend p m) ms hok
    have he := extend_n ho
    have ⟨hv,hi⟩ := extend_sound hp hn (by simp at hl; omega) ho
    obtain ⟨hv',ht⟩ := ih hv (by omega) (by simp at hl; omega) hok
    refine ⟨hv',fun i h1 h2 => ?_⟩
    by_cases h : i=p.n
    · simpa [h] using hi
    · apply ht <;> simp at h2 <;> omega

theorem perm_of_cover {xs : List ℕ} {n : ℕ} (hl : xs.length=n)
    (hc : ∀ x, 1 ≤ x → x ≤ n → x ∈ xs) : xs.Perm (labels n) := by
  apply List.Perm.symm
  apply List.Subperm.perm_of_length_le _ (by simp [hl])
  apply List.subperm_of_subset (List.nodup_range.map Nat.succ_injective)
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  have := List.mem_range.mp hi
  exact hc _ (by omega) (by omega)

def direct (xs : List ℕ) (n : ℕ) : Prop :=
  xs.length = n ∧ (∀ i : Fin n, i.val+1 ∈ xs) ∧ xs.IsChain (fun a b => (a+b).sqrt^2 = a+b)
instance (xs : List ℕ) (n : ℕ) : Decidable (direct xs n) := by unfold direct; infer_instance
theorem direct_sound {xs : List ℕ} {n : ℕ} (h : direct xs n) :
    xs.Perm (labels n) ∧ Chain xs := by
  refine ⟨perm_of_cover h.1 ?_, h.2.2.imp ?_⟩
  · intro x hx hn
    have he := h.2.1 ⟨x-1,by omega⟩
    simpa [Nat.sub_add_cancel hx] using he
  intro a b he
  exact ⟨(a+b).sqrt,by simpa [pow_two] using he.symm⟩

def directPair (n : ℕ) (s t : List ℕ) : Prop :=
  direct s n ∧ direct t (n+1) ∧ s.head?=some 1 ∧ s.getLast?=some (endVal n) ∧
  t.head?=some 1 ∧ t.getLast?=some (endVal (n+1)) ∧
  ∀ i : Fin (s++[n+1]).length, let x := (s++[n+1])[i.val]
    t[t.idxOf x]? = some x ∧ t.idxOf x % 2 = i.val%2
instance (n : ℕ) (s t : List ℕ) : Decidable (directPair n s t) := by unfold directPair; infer_instance

theorem directPair_sound {n : ℕ} {s t : List ℕ} (h : directPair n s t) : Paired n s t := by
  obtain ⟨hs,ht,h1,h2,h3,h4,h5⟩ := h
  obtain ⟨ps,cs⟩ := direct_sound hs
  obtain ⟨pt,ct⟩ := direct_sound ht
  refine ⟨⟨ps,cs,h1,h2⟩,⟨pt,ct,h3,h4⟩,?_⟩
  rintro x j ⟨i,hx,rfl⟩
  have ⟨hh,hp⟩ := h5 i
  rw [hx] at hh hp
  obtain ⟨hlt,he⟩ := List.getElem?_eq_some_iff.mp hh
  exact ⟨⟨_,hlt⟩,he,hp⟩

def encoded (xs : List ℕ) : PathCode := ⟨xs.length,pack xs,pack xs.reverse,true⟩
theorem literal_start {n : ℕ} {s t : List ℕ} (h : directPair n s t) (hn : n+1 < 2048) :
    P n ∧ ValidCode (encoded t) := by
  have hp := directPair_sound h
  have perm := hp.2.1.1
  have l : (encoded t).n = n+1 := by simpa [encoded] using perm.length_eq
  refine ⟨⟨s,t,hp⟩,t,⟨rfl,rfl,rfl,?_,hp.2.1.2.1⟩, l ▸ perm⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (perm.mem_iff.mp hx)
  have := List.mem_range.mp hy
  omega

theorem little25 : ∃ s, s.Perm (labels 25) ∧ Chain s := ⟨[23,2,14,22,3,13,12,4,21,15,10,6,19,17,8,1,24,25,11,5,20,16,9,7,18],direct_sound (by decide +kernel)⟩
theorem little26 : ∃ s, s.Perm (labels 26) ∧ Chain s := ⟨[15,21,4,12,13,3,22,14,2,23,26,10,6,19,17,8,1,24,25,11,5,20,16,9,7,18],direct_sound (by decide +kernel)⟩
theorem little27 : ∃ s, s.Perm (labels 27) ∧ Chain s := ⟨[12,13,23,26,10,15,21,4,5,20,16,9,27,22,3,6,19,17,8,1,24,25,11,14,2,7,18],direct_sound (by decide +kernel)⟩
theorem little28 : ∃ s, s.Perm (labels 28) ∧ Chain s := ⟨[25,24,1,15,10,26,23,13,12,4,21,28,8,17,19,6,3,22,27,9,16,20,5,11,14,2,7,18],direct_sound (by decide +kernel)⟩
theorem little29 : ∃ s, s.Perm (labels 29) ∧ Chain s := ⟨[28,21,4,5,11,25,24,12,13,3,6,19,17,8,1,15,10,26,23,2,14,22,27,9,16,20,29,7,18],direct_sound (by decide +kernel)⟩
theorem little30 : ∃ s, s.Perm (labels 30) ∧ Chain s := ⟨[30,19,17,8,28,21,15,1,24,25,11,5,4,12,13,3,6,10,26,23,2,14,22,27,9,16,20,29,7,18],direct_sound (by decide +kernel)⟩
theorem little31 : ∃ s, s.Perm (labels 31) ∧ Chain s := ⟨[1,24,25,11,14,22,27,9,16,20,29,7,18,31,5,4,12,13,3,6,30,19,17,8,28,21,15,10,26,23,2],direct_sound (by decide +kernel)⟩
theorem little32 : ∃ s, s.Perm (labels 32) ∧ Chain s := ⟨[30,19,17,32,4,21,28,8,1,15,10,26,23,2,14,22,27,9,16,20,29,7,18,31,5,11,25,24,12,13,3,6],direct_sound (by decide +kernel)⟩
theorem little33 : ∃ s, s.Perm (labels 33) ∧ Chain s := ⟨[30,19,17,32,4,21,28,8,1,15,10,26,23,2,14,22,27,9,16,33,31,18,7,29,20,5,11,25,24,12,13,3,6],direct_sound (by decide +kernel)⟩
theorem little34 : ∃ s, s.Perm (labels 34) ∧ Chain s := ⟨[24,25,11,14,22,27,9,16,33,31,18,7,29,20,5,4,32,17,19,30,6,10,26,23,2,34,15,21,28,8,1,3,13,12],direct_sound (by decide +kernel)⟩
theorem little35 : ∃ s, s.Perm (labels 35) ∧ Chain s := ⟨[24,25,11,14,35,1,8,28,21,15,34,2,23,26,10,6,30,19,17,32,4,5,20,29,7,18,31,33,16,9,27,22,3,13,12],direct_sound (by decide +kernel)⟩
theorem little36 : ∃ s, s.Perm (labels 36) ∧ Chain s := ⟨[3,33,31,18,7,29,35,14,22,27,9,16,20,5,11,25,24,12,13,36,28,21,4,32,17,8,1,15,10,26,23,2,34,30,19,6],direct_sound (by decide +kernel)⟩
theorem little37 : ∃ s, s.Perm (labels 37) ∧ Chain s := ⟨[17,32,4,21,28,36,13,23,26,10,15,34,30,19,6,3,22,14,2,7,18,31,33,16,9,27,37,12,24,25,11,5,20,29,35,1,8],direct_sound (by decide +kernel)⟩
theorem little38 : ∃ s, s.Perm (labels 38) ∧ Chain s := ⟨[9,27,37,12,24,25,11,38,26,23,13,36,28,21,15,10,6,19,30,34,2,14,22,3,33,31,18,7,29,35,1,8,17,32,4,5,20,16],direct_sound (by decide +kernel)⟩
theorem little39 : ∃ s, s.Perm (labels 39) ∧ Chain s := ⟨[14,35,29,20,16,33,31,18,7,9,27,37,12,24,25,39,10,26,38,11,5,4,32,17,8,1,15,21,28,36,13,23,2,34,30,19,6,3,22],direct_sound (by decide +kernel)⟩
theorem little40 : ∃ s, s.Perm (labels 40) ∧ Chain s := ⟨[21,28,36,13,23,26,38,11,25,39,10,15,34,30,19,6,3,33,16,9,40,24,12,37,27,22,14,2,7,18,31,5,20,29,35,1,8,17,32,4],direct_sound (by decide +kernel)⟩
def short41 : List ℕ := [1,8,41,40,9,27,37,12,24,25,39,10,26,38,11,5,4,32,17,19,6,30,34,15,21,28,36,13,23,2,7,18,31,33,16,20,29,35,14,22,3]
def long41 : List ℕ := [1,35,29,20,16,33,3,22,14,2,23,13,36,28,21,15,34,30,6,19,17,32,4,5,31,18,7,42,39,10,26,38,11,25,24,12,37,27,9,40,41,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit41 : directPair 41 short41 long41 := by decide +kernel
theorem base41 : P 41 := (literal_start lit41 (by decide)).1
def short42 : List ℕ := [1,15,10,39,25,24,40,41,23,26,38,11,5,20,29,35,14,2,34,30,19,6,3,22,42,7,18,31,33,16,9,27,37,12,13,36,28,21,4,32,17,8]
def long42 : List ℕ := [1,35,29,20,5,11,38,26,10,15,34,30,19,6,43,21,4,32,17,8,28,36,13,12,37,27,9,16,33,31,18,7,42,39,25,24,40,41,23,2,14,22,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit42 : directPair 42 short42 long42 := by decide +kernel
theorem base42 : P 42 := (literal_start lit42 (by decide)).1
def short43 : List ℕ := [1,15,34,30,19,6,43,21,4,32,17,8,28,36,13,12,37,27,22,42,39,10,26,38,11,25,24,40,41,23,2,14,35,29,20,5,31,18,7,9,16,33,3]
def long43 : List ℕ := [1,15,34,30,19,6,3,33,16,9,7,18,31,5,11,25,24,40,41,23,2,14,35,29,20,44,37,27,22,42,39,10,26,38,43,21,28,36,13,12,4,32,17,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit43 : directPair 43 short43 long43 := by decide +kernel
theorem base43 : P 43 := (literal_start lit43 (by decide)).1
def short44 : List ℕ := [1,15,10,39,42,22,27,9,16,20,5,44,37,12,13,36,28,21,4,32,17,19,30,34,2,23,26,38,43,6,3,33,31,18,7,29,35,14,11,25,24,40,41,8]
def long44 : List ℕ := [1,15,10,39,42,22,27,9,16,20,5,44,37,12,13,23,26,38,11,25,24,40,41,8,28,36,45,19,17,32,4,21,43,6,30,34,2,14,35,29,7,18,31,33,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit44 : directPair 44 short44 long44 := by decide +kernel
theorem base44 : P 44 := (literal_start lit44 (by decide)).1
def short45 : List ℕ := [1,8,41,40,9,27,37,44,5,31,18,7,2,34,15,21,28,36,45,4,32,17,19,30,6,43,38,11,25,24,12,13,23,26,10,39,42,22,14,35,29,20,16,33,3]
def long45 : List ℕ := [1,35,14,22,42,39,10,26,23,13,12,24,25,11,38,43,6,30,19,17,32,4,45,36,28,21,15,34,2,7,29,20,16,33,3,46,18,31,5,44,37,27,9,40,41,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit45 : directPair 45 short45 long45 := by decide +kernel
theorem base45 : P 45 := (literal_start lit45 (by decide)).1
def short46 : List ℕ := [1,35,46,18,31,33,16,20,29,7,42,39,25,24,12,13,3,22,14,11,38,43,6,30,34,2,23,26,10,15,21,28,36,45,19,17,32,4,5,44,37,27,9,40,41,8]
def long46 : List ℕ := [1,8,41,40,9,27,37,44,5,20,16,33,31,18,46,35,29,7,42,22,14,11,38,43,6,30,19,45,36,28,21,15,34,2,47,17,32,4,12,24,25,39,10,26,23,13,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit46 : directPair 46 short46 long46 := by decide +kernel
theorem base46 : P 46 := (literal_start lit46 (by decide)).1
def cp47 := encoded long46
theorem val47 : ValidCode cp47 := (literal_start lit46 (by decide)).2
def moves47 : List Move := [⟨[],[20,16,10],[1]⟩]
def last47 : PathCode := ⟨48,0x100a414009036094160050280740382a02c00c0681703402813819030030020200220bc0102201e0540e02405a04c0f0060560980580e0460b80901f04204018001,0x20c00802103e0481702301c02c1302b00c0780982d0480700a80f044008178110400100601803209c0501a02e0340181605401c0e81400a0b01281b0120a014808,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked47 : walk cp47 moves47 = last47 := by decide +kernel
theorem result47 : ValidCode last47 ∧ ∀ i, 47 ≤ i → i < 48 → P i := by
  have h := walk_sound moves47 val47 (by decide) (by decide) (by rw [checked47]; rfl)
  rw [checked47] at h
  exact h
def short48 : List ℕ := [1,15,10,26,38,43,21,28,36,45,19,6,30,34,47,2,14,11,25,39,42,22,3,13,23,41,40,24,12,37,27,9,7,29,35,46,18,31,33,48,16,20,44,5,4,32,17,8]
def long48 : List ℕ := [1,8,17,32,49,15,10,39,42,22,27,37,12,24,25,11,14,2,47,34,30,6,19,45,4,5,44,20,16,48,33,31,18,46,35,29,7,9,40,41,23,26,38,43,21,28,36,13,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit48 : directPair 48 short48 long48 := by decide +kernel
theorem base48 : P 48 := (literal_start lit48 (by decide)).1
def short49 : List ℕ := [1,8,41,23,26,38,43,21,28,36,13,12,37,44,5,11,14,2,47,17,19,45,4,32,49,15,34,30,6,10,39,25,24,40,9,27,22,42,7,18,31,33,48,16,20,29,35,46,3]
def long49 : List ℕ := [1,15,49,32,4,45,19,17,47,2,34,30,6,10,39,25,24,40,9,16,48,33,3,46,35,29,20,44,5,11,14,50,31,18,7,42,22,27,37,12,13,36,28,21,43,38,26,23,41,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit49 : directPair 49 short49 long49 := by decide +kernel
theorem base49 : P 49 := (literal_start lit49 (by decide)).1
def short50 : List ℕ := [1,24,40,41,23,26,10,39,25,11,38,43,21,4,12,13,3,33,48,16,9,27,37,44,5,20,29,35,46,18,31,50,14,22,42,7,2,47,17,32,49,15,34,30,6,19,45,36,28,8]
def long50 : List ℕ := [1,8,28,36,45,4,21,43,38,11,25,39,10,26,23,41,40,24,12,13,51,30,6,19,17,32,49,15,34,47,2,7,42,22,14,50,31,18,46,35,29,20,5,44,37,27,9,16,48,33,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit50 : directPair 50 short50 long50 := by decide +kernel
theorem base50 : P 50 := (literal_start lit50 (by decide)).1
def cp51 := encoded long50
theorem val51 : ValidCode cp51 := (literal_start lit50 (by decide)).2
def moves51 : List Move := [⟨[1,28,32,38,38,27,27,27,46,28,31,1],[8],[19,1]⟩]
def last51 : PathCode := ⟨52,0x100440980603c0cc068030420c008009036094160050280741a00c0300a0148170340281381901609815815038090168040400c40782205e0080382a02c0381901f0240b811801,0x208c1701203e0c80701605401c0102f04403c188200080b41201c02a0ac1300b03209c0501a02e0a4140180180d00e81400a0b01281b012040180210060341981e00c04c08808,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked51 : walk cp51 moves51 = last51 := by decide +kernel
theorem result51 : ValidCode last51 ∧ ∀ i, 51 ≤ i → i < 52 → P i := by
  have h := walk_sound moves51 val51 (by decide) (by decide) (by rw [checked51]; rfl)
  rw [checked51] at h
  exact h
def short52 : List ℕ := [1,24,12,52,29,35,46,18,31,50,14,11,25,39,10,15,34,47,2,23,26,38,43,6,30,51,49,32,17,19,45,4,21,28,36,13,3,33,48,16,20,5,44,37,27,22,42,7,9,40,41,8]
def long52 : List ℕ := [1,24,25,11,14,50,31,18,46,35,29,7,2,23,26,38,43,6,10,39,42,22,27,37,44,5,20,16,9,40,41,8,17,32,49,51,30,19,45,4,21,15,34,47,53,28,36,13,12,52,48,33,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit52 : directPair 52 short52 long52 := by decide +kernel
theorem base52 : P 52 := (literal_start lit52 (by decide)).1
def short53 : List ℕ := [1,35,46,18,31,50,14,11,53,47,34,30,51,13,23,2,7,29,52,12,24,25,39,42,22,27,37,44,20,5,4,21,28,36,45,19,6,43,38,26,10,15,49,32,17,8,41,40,9,16,48,33,3]
def long53 : List ℕ := [1,35,14,50,31,18,46,54,10,26,23,2,7,29,52,12,37,44,20,5,4,21,28,36,45,19,17,32,49,15,34,47,53,11,38,43,6,30,51,13,3,33,48,16,9,27,22,42,39,25,24,40,41,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit53 : directPair 53 short53 long53 := by decide +kernel
theorem base53 : P 53 := (literal_start lit53 (by decide)).1
def short54 : List ℕ := [1,15,10,26,38,11,53,47,34,2,23,41,40,9,7,18,31,50,14,22,42,39,25,24,12,13,3,33,16,48,52,29,35,46,54,27,37,44,20,5,4,21,43,6,30,51,49,32,17,19,45,36,28,8]
def long54 : List ℕ := [1,8,17,47,53,11,38,26,55,9,40,41,23,13,12,24,25,39,42,22,14,50,31,18,7,2,34,15,10,6,43,21,28,36,45,19,30,51,49,32,4,5,20,44,37,27,54,46,35,29,52,48,16,33,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit54 : directPair 54 short54 long54 := by decide +kernel
theorem base54 : P 54 := (literal_start lit54 (by decide)).1
def short55 : List ℕ := [1,24,25,39,42,7,2,34,47,53,11,38,26,55,45,36,28,8,17,32,49,15,10,54,27,9,40,41,23,13,51,30,19,6,43,21,4,5,44,37,12,52,48,33,16,20,29,35,46,18,31,50,14,22,3]
def long55 : List ℕ := [1,24,12,52,48,33,3,22,27,37,44,56,25,39,42,7,2,34,47,53,11,5,4,21,28,36,45,55,26,38,43,6,19,30,51,13,23,41,40,9,16,20,29,35,14,50,31,18,46,54,10,15,49,32,17,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit55 : directPair 55 short55 long55 := by decide +kernel
theorem base55 : P 55 := (literal_start lit55 (by decide)).1
def cp56 := encoded long55
theorem val56 : ValidCode cp56 := (literal_start lit55 (by decide)).2
def moves56 : List Move := [⟨[],[1],[42,50,8,52,16]⟩,⟨[],[16,52,8,50],[21,35,1]⟩,⟨[],[1,19],[48,8,54,20]⟩,⟨[],[20,54,8,18],[49,29,13,1]⟩,⟨[],[1,13,29,49],[16,46]⟩,⟨[],[38],[41,19,1]⟩,⟨[],[1,35,21],[56,16,20,32]⟩,⟨[],[32,50],[3,25,57,23,49,45,55,1]⟩,⟨[],[1,55,45,49,55,15,39,57,27],[60,14,28,42,26,32]⟩]
def last56 : PathCode := ⟨65,0x300c0ac0a81c0480b41b81a04c02c1a82f0440080382a02c0381901f00a0101003101e0281b02e0240fc1d01701a0cc0f01307c0ec148280780f4138190701041181d0280b01281b012040108300680300c03908004404001,0x1010044200390300301a0300420400481b04a0b00a01d0461041c01904e0f41e0280520ec1f01303c0cc068170740fc0902e06c028078310400100281f0640380b02a00e0081102f06a02c1301a06e0b41201c02a0ac03003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked56 : walk cp56 moves56 = last56 := by decide +kernel
theorem result56 : ValidCode last56 ∧ ∀ i, 56 ≤ i → i < 65 → P i := by
  have h := walk_sound moves56 val56 (by decide) (by decide) (by rw [checked56]; rfl)
  rw [checked56] at h
  exact h
def short65 : List ℕ := [1,24,57,64,36,45,55,26,10,54,27,22,42,7,9,40,41,8,28,53,11,38,43,6,30,19,62,59,5,31,50,14,2,34,47,17,32,4,12,37,44,20,16,65,56,25,39,61,60,21,15,49,51,13,23,58,63,18,46,35,29,52,48,33,3]
def long65 : List ℕ := [1,24,57,64,36,45,55,66,15,34,47,17,32,49,51,13,23,26,10,54,27,22,42,58,63,18,46,35,29,52,48,33,3,61,39,25,56,65,16,20,44,37,12,4,5,31,50,14,2,7,9,40,60,21,28,53,11,38,43,6,30,19,62,59,41,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit65 : directPair 65 short65 long65 := by decide +kernel
theorem base65 : P 65 := (literal_start lit65 (by decide)).1
def cp66 := encoded long65
theorem val66 : ValidCode cp66 := (literal_start lit65 (by decide)).2
def moves66 : List Move := [⟨[],[1,25,45,55],[44,56]⟩]
def last66 : PathCode := ⟨67,0xc1e8270320e0208100280b01281b02c0a81d03f0240b81181d0680c01084306c0280d01701a0cc188200220bc1100f0840dc168240800e40c00c0080140f83201c008038090500f00a81c06a02c1302b00c0780983e0760a404001,0x4040290760f80981e00c0ac1300b06a0700a83c0500240380201c0c80f8050080300c0390800901683708403c1102f0220801883301a05c0d00a06c10c108300680741182e0240fc1d02a02c06c1282c0280402083803209c1e803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked66 : walk cp66 moves66 = last66 := by decide +kernel
theorem result66 : ValidCode last66 ∧ ∀ i, 66 ≤ i → i < 67 → P i := by
  have h := walk_sound moves66 val66 (by decide) (by decide) (by rw [checked66]; rfl)
  rw [checked66] at h
  exact h
def short67 : List ℕ := [1,48,52,12,13,36,64,17,32,4,45,55,66,15,49,51,30,34,47,2,62,19,6,10,26,38,43,21,28,53,11,25,39,42,7,57,24,40,60,61,20,29,35,65,56,8,41,23,58,63,18,31,50,14,22,59,5,44,37,27,9,16,33,67,54,46,3]
def long67 : List ℕ := [1,15,49,51,13,68,32,17,47,53,28,21,43,57,64,36,45,55,66,34,30,19,6,10,26,23,58,63,37,12,24,25,11,38,62,2,7,29,52,48,33,67,54,27,22,42,39,61,3,46,18,31,50,14,35,65,56,44,20,16,9,40,60,4,5,59,41,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit67 : directPair 67 short67 long67 := by decide +kernel
theorem base67 : P 67 := (literal_start lit67 (by decide)).1
def cp68 := encoded long67
theorem val68 : ValidCode cp68 := (literal_start lit67 (by decide)).2
def moves68 : List Move := [⟨[],[57,29],[46,28,36,30]⟩,⟨[],[30,24,34],[21,17,47,55,43,51]⟩,⟨[],[51,43,25],[20,32]⟩,⟨[35,45,41,30,23,23,23,54,21,26,33],[30,36],[11,23,7,53,67,11]⟩,⟨[],[],[52,46]⟩]
def last68 : PathCode := ⟨73,0x307a09c150160361240403808208c0700207c0980d0170740fc1282c028040180210860d81701200e0741a00c08a07c190470140180982d0481000882f06a0702400906e1081101e08c02c0c8180720ac0a83c0500a41d8050080802200d0660c407801,0x101e0c41980d088080020050760a41403c02a0ac1c81803202c2301e0441081b8090900701a82f0221001202d0260180504706407c2280c0680740381205c0d8218210600400a02c04a0fc1d0170340981f00201c08c208380101240d81605409c1e803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked68 : walk cp68 moves68 = last68 := by decide +kernel
theorem result68 : ValidCode last68 ∧ ∀ i, 68 ≤ i → i < 73 → P i := by
  have h := walk_sound moves68 val68 (by decide) (by decide) (by rw [checked68]; rfl)
  rw [checked68] at h
  exact h
def short73 : List ℕ := [1,48,52,69,31,18,7,29,71,50,14,67,33,16,9,72,28,36,64,17,19,30,70,51,49,32,68,53,47,2,62,59,41,8,73,27,22,42,39,25,56,65,35,46,54,10,6,58,63,37,12,4,45,55,66,34,15,21,43,57,24,40,60,61,20,44,5,11,38,26,23,13,3]
def long73 : List ℕ := [1,48,73,27,22,42,7,74,70,51,49,32,68,53,47,34,66,55,45,36,64,17,19,30,6,58,23,26,38,11,5,4,60,40,41,59,62,2,14,50,71,29,52,69,31,18,63,37,12,13,3,46,35,65,56,44,20,61,39,25,24,57,43,21,15,10,54,67,33,16,9,72,28,8]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit73 : directPair 73 short73 long73 := by decide +kernel
theorem base73 : P 73 := (literal_start lit73 (by decide)).1
def cp74 := encoded long73
theorem val74 : ValidCode cp74 := (literal_start lit73 (by decide)).2
def moves74 : List Move := [⟨[3,7,7,11,49,15,15,63,11,3],[3,11],[56,14,26,46,50]⟩,⟨[],[16,70,18,26,36,66],[29,67,47,43,17,11,3]⟩,⟨[],[1,7],[60,68,14]⟩,⟨[28,38,63,64,3,11,11,3,42,43,52,38,28],[],[11,25,33,73,67,7,1]⟩,⟨[],[67],[20,34,62,6]⟩,⟨[],[62,48],[1,13,31,7]⟩,⟨[73,35,13,21,69,69,40,51,63,75,75,63,41,60],[37],[70,4,68,6,28,58]⟩,⟨[],[58,28,6,68],[19,45,13,21]⟩,⟨[62,11,36,52,15,50,78,65],[19,3],[52,76,20,56,32,36,10,14]⟩,⟨[39,1,1,11,53,66,77,77,66,34,78,35],[30,68,16,70],[39,43,53,57,13]⟩,⟨[68,2,77,63,38,38,38,13,61,20,72,38],[33],[28,58,2,54,14]⟩,⟨[],[14],[19,9,65,19,13]⟩,⟨[],[13,19,23],[42,18,78,66]⟩,⟨[],[66,16],[13]⟩,⟨[7,4,79,21,26,34,34],[1],[82,70,36,16,82]⟩,⟨[73,51,51,73,31,31,68,50,56,3,17],[70,64],[79,19,35,15,5,61,69,1]⟩,⟨[20,70,47,6,48,29,63,63,15,25,55,52,24,40,79],[79,67,25],[84,70,26]⟩,⟨[57,40,40,36,28,6,16,1,32],[76,40],[29,3,9,5,25,69,83,37,81]⟩,⟨[74,3,3,3,4,1,44,59,31,17],[17,31,39],[26,88,80,24,46]⟩,⟨[52,14,13,13,41,27,14,66],[28,72,52,48],[9,73,67,15,81,77]⟩]
def last74 : PathCode := ⟨94,0x405c03a050160050760582705b06a07024031040164280290500f02a05501e1081b82d0260442002401a1102605d0660780302b0720600c80b08c1280382a04e0281b05a03e0481700307a14c2b03a02e0681303e0a415c1102f00413c0a80409a10c070230820e02c05107e0940603408a12c2f03208e1240d80902008418001,0x8300420400481b09211c1905e0961141a00c04a0fc288580701041180e0861340201509e008178220ae1481f02603405c1d0560a60f40182e02407c2d03601409c15007094118058190300e41580603c0cc2e84c0880341204002204c1683708403c2a8540780a0148500b2080188480380d42d84e02c0ec0282c0280742e008,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked74 : walk cp74 moves74 = last74 := by decide +kernel
theorem result74 : ValidCode last74 ∧ ∀ i, 74 ≤ i → i < 94 → P i := by
  have h := walk_sound moves74 val74 (by decide) (by decide) (by rw [checked74]; rfl)
  rw [checked74] at h
  exact h
def short94 : List ℕ := [1,48,16,33,88,12,69,52,92,77,23,58,6,43,38,26,55,66,34,15,85,36,45,76,24,57,87,13,3,78,91,30,70,74,47,2,62,82,39,25,75,46,18,63,81,19,17,64,80,89,32,68,53,11,5,59,22,42,79,90,31,50,94,27,73,71,10,54,67,14,86,83,61,20,29,35,65,56,44,37,84,60,4,21,28,72,49,51,93,7,9,40,41,8]
def long94 : List ℕ := [1,48,73,71,29,52,69,12,4,21,28,72,49,51,93,76,5,59,62,82,39,42,22,78,91,30,70,11,53,68,32,89,55,66,34,15,85,36,45,19,17,64,80,20,16,33,88,56,65,35,86,14,67,54,10,26,95,74,47,2,79,90,31,50,94,27,9,7,18,63,81,40,41,8,92,77,44,37,84,60,61,83,38,43,6,58,23,13,87,57,24,25,75,46,3]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem lit94 : directPair 94 short94 long94 := by decide +kernel
theorem base94 : P 94 := (literal_start lit94 (by decide)).1
def cp95 := encoded long94
theorem val95 : ValidCode cp95 := (literal_start lit94 (by decide)).2
def moves95 : List Move := [⟨[81,41,38,38,50,1,43,11,72,5],[36,40,48],[3,53,77,43,53,59,13,39]⟩,⟨[],[7],[2,14,42,92,36]⟩,⟨[36,50,50,46,5,67,40,58,73,86],[86],[9,17,89,41,75]⟩,⟨[],[1,71,31,15,19,73],[34,16,58,30,94,84,18,78,72]⟩,⟨[],[72,94],[77,95,19,1]⟩,⟨[1,40,40,51,56,21,94,89,1],[71,15,67],[88,68,90]⟩,⟨[],[20,82,10],[21,35,3,25,19,71,51]⟩,⟨[],[69,87,41,13],[84,52,68,86,94,58,50,48,32,38,44,54]⟩,⟨[],[54,44,22,78,74,2],[5]⟩,⟨[79,79,1,99,12,42,1],[1,23,9,19],[16,62,80,46,68,44,56,40,80,6,28,8]⟩,⟨[],[8,28,52],[69,49,63,33,1]⟩,⟨[],[89,69,83,93,73,15],[74,46,14,44,92,60,2,58]⟩,⟨[58,2,98,20,72,24,28],[60,16,18,48],[91,59,33,29,21,75,85,77]⟩,⟨[77,85,48,78,30,79,39,39,79,30],[25,29,79,75,53],[72,10,40,8,22,86,62,60,90]⟩,⟨[],[80,58],[35,89,39,99,105]⟩,⟨[],[105,55,17,39],[104,32,8,24,62]⟩,⟨[10,101,42,10],[10,42,50,96],[87,41,95,55,29,25]⟩,⟨[],[],[42,96,88,10]⟩,⟨[],[102,34,26],[21,77,63]⟩,⟨[],[45,49,107],[26,100]⟩,⟨[],[30,88],[111,53,49]⟩,⟨[],[49,39,27,5],[72,60,46,74,8]⟩,⟨[],[],[83,109,53,15,55,65]⟩,⟨[],[65,69,89,71],[106,44,116]⟩,⟨[],[8,42,76,54],[67,35,43,33,29]⟩,⟨[94,27,23,14,87,72,67,66,67,107,43],[77],[16,6,10,112,72,12]⟩,⟨[82,43,106,69,30,42],[42,30,58,116],[75,83,9,39]⟩,⟨[],[39,9,97,65],[68,72,114,110,116]⟩,⟨[12,73,37,55,73,44,44,44,1,40,51],[32],[5,57,19,77,35]⟩,⟨[],[49],[32,108,20,88,60]⟩,⟨[],[60,112],[45,49,17,113,19,39]⟩,⟨[],[29,25],[86,20,56,62,112,28]⟩,⟨[],[28,112,72,54],[37,93,69,75,25,113]⟩,⟨[],[107,81],[28,22,76,32,90,40]⟩,⟨[],[40],[99,103,91,85,63,17,59,93]⟩,⟨[],[25,65],[52,46,76,122,90]⟩,⟨[],[90,108,46,96,32],[59,95,99,25]⟩,⟨[],[23,9,107,123],[28,100,108,92,98,24]⟩,⟨[],[62],[127,17,87,47,29,57,41,9,23]⟩,⟨[],[101,93],[106,50,62,52,108,70]⟩,⟨[],[104,122,84],[51,83,61,117,105]⟩,⟨[],[105,117],[100,36,60]⟩,⟨[],[130,90,16],[55,125,81]⟩,⟨[],[81,91],[54,90]⟩,⟨[],[46,92,102],[119,133,19,109,105,91]⟩,⟨[],[75,119,79],[20,76,28,18,24]⟩,⟨[],[24,80,60],[105,51,93,9,113,73,49,21,31]⟩,⟨[],[31,125,109],[94,124,84,90,38,118,84,88]⟩,⟨[],[56,18,72],[101,75,37,83,35,135,131]⟩,⟨[],[53],[104,70,18,114]⟩,⟨[],[114,140,14],[99,49]⟩,⟨[],[125,113,117],[122,118,18,120]⟩,⟨[],[120,74,34],[93,47,9,61]⟩,⟨[],[11,99,27],[120,42,146]⟩,⟨[],[86,98,120],[35,89,133,111,101,43,11]⟩,⟨[],[121,17],[90,112,54,138]⟩,⟨[],[136,130],[49,55,79,101,45]⟩,⟨[],[45,111],[128,66,50,148,64]⟩,⟨[],[140],[129,17,125]⟩,⟨[],[125,111],[74,148,40,28]⟩,⟨[],[84,130,20],[143,103,35,81,97,69,115]⟩,⟨[],[141,119,63],[56,114,42,100,96]⟩,⟨[],[96,146,38],[97,23,17,139,123,29,97,77]⟩,⟨[],[77,111],[56,44,132,98,116]⟩,⟨[],[116,98],[157,65]⟩,⟨[],[],[64,52,132,22,110]⟩,⟨[],[110,58,14],[159,17,27,117,59,21,93]⟩,⟨[],[65],[114,22,116,4,138,34]⟩,⟨[61,49,144,19,61,25],[126,80,10,132],[97,19,133,7]⟩,⟨[],[1,25,51],[74,4,40,128]⟩,⟨[],[],[119,141,85,1]⟩,⟨[],[45,137,13],[58,110,146,82]⟩,⟨[],[82,130],[147,29,45,107]⟩,⟨[],[139,71],[52,128,54,92,112,162]⟩,⟨[],[162,142,134],[153,121]⟩,⟨[97,78,113,36,35,125,63,3,97,163],[79],[18,90,150,86,46,80,74]⟩,⟨[],[74,118,102],[111,125,67,119,157]⟩,⟨[],[113,37],[6,64,108]⟩,⟨[],[50],[41,81,105,143]⟩,⟨[],[159,135,121],[28,48,128,110]⟩,⟨[],[32,132,92],[73,55,13,17]⟩,⟨[],[35,69],[130,126,70]⟩,⟨[],[152],[93,155,47,35]⟩,⟨[],[109,101],[56,172,60,162,146,160]⟩,⟨[],[160],[51,23,149,129]⟩,⟨[],[129,149,151],[122,68,78]⟩,⟨[],[160,48],[35,171,63]⟩,⟨[],[63,41,177],[50,24,142,48]⟩,⟨[],[4,76,114],[109,165]⟩,⟨[],[119],[18,48,34,112,4]⟩,⟨[],[36],[45,167,37,113,93]⟩,⟨[],[93,111],[68,36]⟩,⟨[],[60],[155,175,157]⟩,⟨[],[1,67],[48,90,84,96,180]⟩,⟨[],[118,178],[75,171,49,155,1]⟩,⟨[],[135,177,21],[74,186,152]⟩,⟨[166,182,62,163,27,95,165,125,161],[20,136,120],[13,71,81,129]⟩,⟨[],[1],[160,44,106,176]⟩,⟨[],[6,24,112,42],[37,139,89,1]⟩,⟨[],[89,159],[62,90,122]⟩]
def last95 : PathCode := ⟨195,0xc3b08a1742bc4a86b04a1501e06d0ae0885107f08a030068b71641382109f0141bc1084313c20c1303e18429c0e8340b81341607d0261985d80909018440010082280408600601e40b81a11e1483901e0662b80b02a0740185187e08c26c148280a21cc4689402a070040a10801a43c0311262385b02b0ca17c41027032060488b30dc248278b1170230020a503e1681b0ab1322205e0440981743381205c1880100e0ac08c5f06313a210600a9036124238320bc30c5307b10a2fc550370b202c1a85b10c1e81784a12e2b43a0501602e4340981581d4360580701c4298110402901e88713403c350771120ec2a82405a1f00a005116258258b51682403803900e2f43209c1503041f801,0x41f8c1150270320bd00e0e4380901682d4258961160140a07c05a0902a83b1121dc3500f13421c1e8a40400442987107016036075158260340b91601403a0ad12e1281787a10c16c1a80b0b20dc550bf10a1ec530c30bc0c8238490362a46008413a18c5f0230ac0380106205c0483385d0981105e0881322ac1b05a03e2940208c1702c4278920dc2cc4881803209c4105f0ca0ac5b08e1260c43c0690802840401c02a250468730a20a01489b08c1f8518060740a80b0ae0660783905211e0680b879060180408a0082040400610900245d8660261f41604d0b80d00e8a71840f81308313c10c1086f01427c2104e1642dc0680c08a1fc510220ae1b41e05404a1ac4a8af1742283b003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked95 : walk cp95 moves95 = last95 := by decide +kernel
theorem result95 : ValidCode last95 ∧ ∀ i, 95 ≤ i → i < 195 → P i := by
  have h := walk_sound moves95 val95 (by decide) (by decide) (by rw [checked95]; rfl)
  rw [checked95] at h
  exact h
def cp195 := last95
theorem val195 : ValidCode cp195 := result95.1
def moves195 : List Move := [⟨[],[170,190,172,92],[83,95,11,57,25]⟩,⟨[188,188,109,158,135,1,1,109],[109,87,23,9,131],[22,146,78,92,176,170]⟩,⟨[39,11,59,101,169,144,2,52,11,65,191],[142,26,64,186,154],[21,25,71,41,143,75,31,27,165,87]⟩,⟨[87,172,53,182,182,170,137,60,108,8,119],[157,77],[52,178,114,80,12]⟩,⟨[],[190,84],[171]⟩,⟨[],[171,37,3],[172,176,108,58]⟩,⟨[],[188,158],[7,69,177,149]⟩,⟨[],[165,59,145],[166,194,178,90,142,124,22,36,52]⟩,⟨[],[136,20,134],[95,123]⟩,⟨[],[153,71],[158,86,24,20,112]⟩,⟨[112,112,142,68,133,130,188,188],[188,4,60,46],[49,159,29,97]⟩,⟨[100,34,196,125,75,135,153,153,157,89],[9,185,65],[46,50,112,150,52,120,40,100]⟩,⟨[189,43,43,189,136,38,60,37,184,60,67,75,189],[180,40,150],[195,81,9]⟩,⟨[],[63],[140,172,120]⟩,⟨[],[22,38,126],[103,127,79]⟩,⟨[],[27,81],[54,172,22]⟩,⟨[],[36,204,140],[201,191,41]⟩,⟨[],[49,205],[210,168,198,126,36]⟩,⟨[],[36,202,106],[123,175,101,49]⟩,⟨[],[41,85],[186,164,108,36]⟩,⟨[],[36,108,138],[197,171,195,161,85,41]⟩,⟨[],[],[164,144,54,36]⟩,⟨[],[106,38],[71,179]⟩,⟨[],[1,149,211],[110,48,186,216]⟩,⟨[],[122,38],[55,213,1]⟩,⟨[],[109],[164,10,190,150]⟩,⟨[],[],[111,143,153]⟩,⟨[],[153,131],[172,112]⟩,⟨[],[30,16],[1,97,221]⟩,⟨[],[95],[220,210,96,114,16]⟩,⟨[],[112],[79,161,61,173]⟩,⟨[],[205,219,187],[28,218,162]⟩,⟨[],[224,206,20,66],[125,9,143]⟩,⟨[],[129,131],[12,112,84,64,226]⟩,⟨[],[70],[15,1,209,101,15,107]⟩,⟨[],[127,95],[56,226,34,144,94]⟩,⟨[],[228,88,122],[95,73,137]⟩,⟨[],[137],[24,192,8,200,198]⟩,⟨[],[50,132],[25,197,139,49,227]⟩,⟨[],[213,203,161],[16,206,48,92,138,210]⟩,⟨[],[206,218,50],[223,11,139,85]⟩,⟨[],[15,97,191],[178,158,96,232,122]⟩,⟨[],[54,66,214],[163,171,203,15]⟩,⟨[203,186,111,134,26,26,61,227,100,104,84,147],[201,101],[222,180,130,146]⟩,⟨[61,152,203,213,1,62,86,112,37,162,40,200,151],[66,78,4,206],[25,155,219,179,173]⟩,⟨[],[183],[186,12,164]⟩,⟨[],[164,132],[141,25,67,81,211]⟩,⟨[],[131,85],[180,68,184,4,150,138]⟩,⟨[],[16,200,140],[59,235,61,207,81,215]⟩,⟨[136,8,206,96,96,121,168,173,61,208,189],[189,211,195],[220,132,50,80,68,222,226]⟩,⟨[71,71,226,106,168,146,3,189,240,198,123],[8],[155,81,67,97,37]⟩,⟨[],[37,97,31],[56,104,8]⟩,⟨[],[8,110],[65,63]⟩,⟨[],[1,83],[8,196,176,166]⟩,⟨[],[26],[187,129,17,1]⟩,⟨[],[131,9,107],[182,108]⟩,⟨[],[118,202,16],[143,141,199,27]⟩,⟨[],[247,13],[146,4,124]⟩,⟨[],[124,228],[199,141,213,183]⟩,⟨[],[215,225,135],[76,204,78,216,212,80]⟩,⟨[],[130,216],[83,159,207,199,93]⟩,⟨[],[31,15],[148,188,62,234]⟩,⟨[],[234],[13,225,117]⟩,⟨[160,216,142,202,211,189,29,137,137,116,88],[107],[54,170]⟩,⟨[],[16,100,228],[161,125,141,51]⟩,⟨[],[241,131],[114,106,226,16]⟩,⟨[],[188],[45,71,83,253,183]⟩,⟨[],[233,221,129],[112,258,252,114]⟩,⟨[],[114],[233]⟩,⟨[],[233],[212,46,196]⟩,⟨[],[206,86,260],[143,155,67]⟩,⟨[],[1,143,223],[122,90]⟩,⟨[],[40,146,242,160,106],[197,163,1]⟩,⟨[],[37,181],[94,60,252]⟩,⟨[],[16],[203,189,5,155,41]⟩,⟨[],[223,67,189],[110,114]⟩,⟨[],[254,260],[231,181,117]⟩,⟨[],[211],[234,94,182]⟩,⟨[74,265,268,268,265,211,249,145,145,249,74],[172,200,54],[259,173,135,61,97]⟩,⟨[],[187,205],[160,266,240,80]⟩,⟨[243,244,109,139,273],[220,34,266],[197,5,127,29]⟩,⟨[],[133,85],[124,136,98,240]⟩,⟨[],[36,54,26],[61,257,221,239,21,109]⟩,⟨[259,254,230,235],[235,193],[184,160]⟩,⟨[],[184,146,180],[109,21,1,247,195]⟩,⟨[96,107,14,203,149,168,168,231],[],[66,68,188,134]⟩,⟨[],[110,216,80],[51,59,37,245,243]⟩,⟨[],[1,205,53],[144,26,118,120,240]⟩,⟨[],[200,196,200],[191,63,1]⟩,⟨[],[237,55,21],[272,46,210,252,156]⟩,⟨[261,250,179,179,179,116,210],[],[217,209,175,247]⟩,⟨[],[247,85,45],[132,152,164]⟩,⟨[],[164,152,256],[173,249]⟩,⟨[91,252,126,203,273,50,246],[1],[188,110,136]⟩,⟨[],[132,154],[281,147,1]⟩,⟨[],[151,251,263],[24,260,56]⟩,⟨[],[280],[195,187,183]⟩,⟨[],[183,39],[226,138,172,88,58]⟩,⟨[],[184,206],[265,51,193]⟩,⟨[],[263,187],[32,160,58,64]⟩]
def last195 : PathCode := ⟨295,0xc7e9140aa2301c10c20a22c6f10607c0ec849081102f0568741ea26c430e31ac24c0b00e0463f88987d08e3684781a20e4282f8e51fe1a8078311602e46b86d0780f461921090070468b720443c408600602506a8e41584340a0cd1d84945f8aa06e0242d81e0660346a02c09a10c930be0c6118058191ce3481704b1f21c01004406a32c2b0ee0f62982d0360143d8270d31cc20c4f11b0ea1b0920c00080547587e146174260052380a0340dc1ba19c5d08a1be194158b611c36c348972441b8598110804105a8b405a0904290b0bc018398ae1c421c3c9171440882b83918e474138d91c0190228bb04c3ec2481b1521e08c0a1010170628a414032478054020084800900a2160448072343dc6108221c40c2084f0041880b83a054268330131622e0809100b21408c8771e4148678ea0fe4445409c1e80308a82f0c2060488d81c22bc4a86b04a2104e8cc0683b43e0c81e23cc3b0ab132340748800523e04c0d11d03f05e92708427c5281f0240fc6092312c3e82511f0e214c671160f43bc650c623c1c8378b21240c8890a703a31090001,0x4900c403a29c890321242c83787223c318650ef0f4458670530e247c250fa12c48c6083f02407c5289f08449c5e8fc1d03444c0f8052200748d01322ac3b0f31e23203e0ed0683304e88404a1ac4a8af1c2360488180c20bc8a80c1e8270541110fe3a8678521e41dc8c8500b2440808b816204c3309a0540e80b86200413c2090321c208610f723401c448580a224080021020150780c91402906285c0102848c07815206c248fb04c2ec228641c03641391d18e0e42b82214445c3c8871c42b8398060bc42c4282405a2d05a9040800445986e24425c348db11c2d8158651be2285d0671ba370340282380142605d1461f8758150083009206c0ea46c4f0831cc34c270f60140d82d0a60f63b82b0cb06a110100701f212c170d21ce064058460c62f89304309a0b06a00d0660782d80906e2a85f9251d83340a10d1583906a8940601804090f2042dc4681c0904846183d0781b46b8b91600c40786a1fe3942f90a20e068478da08e1f4898fe0460380b0931ac38c4309b1ea1d0568bc1104208483b07c4186f08b20a4301c08c0aa4507e803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked195 : walk cp195 moves195 = last195 := by decide +kernel
theorem result195 : ValidCode last195 ∧ ∀ i, 195 ≤ i → i < 295 → P i := by
  have h := walk_sound moves195 val195 (by decide) (by decide) (by rw [checked195]; rfl)
  rw [checked195] at h
  exact h
def cp295 := last195
theorem val295 : ValidCode cp295 := result195.1
def moves295 : List Move := [⟨[],[242],[259,249,149,229,115]⟩,⟨[],[179],[36,226,166,228,178,66]⟩,⟨[],[26],[17,7,35,33,101]⟩,⟨[],[267,63],[134,16]⟩,⟨[],[284,286],[263,33,111]⟩,⟨[],[111,33],[84,186,272,106]⟩,⟨[],[120,168],[147,159,157]⟩,⟨[],[237,209],[58,120,106,82,158]⟩,⟨[],[158,82,158],[225,285,9,225]⟩,⟨[],[41],[292,16,302]⟩,⟨[296,231,237,85,253,253,26,197,172,218],[118],[227,75,147,293]⟩,⟨[],[293,109],[66,148]⟩,⟨[226,99,266,17,228,162,144],[78,124,148],[263,301,15,243,39]⟩,⟨[],[37,55],[22,16,280,52]⟩,⟨[],[268],[213,43,303,31]⟩,⟨[],[39,71],[172,300,208]⟩,⟨[52,60,20,10,25,236,282,191,248],[242,204,50],[217,1,169,269]⟩,⟨[],[189,219],[114,166,148,140]⟩,⟨[],[304,18],[299,85,67,79]⟩,⟨[],[221,275,271,9],[178,196]⟩,⟨[],[104,2,84],[153,229,259]⟩,⟨[13,213,82,308,109,101,13],[261,271],[154,104,44,2,172]⟩,⟨[],[172,120,32],[121,125,5,241]⟩,⟨[],[101,241],[96,234]⟩,⟨[],[124,164,142],[129,171,223]⟩,⟨[],[221,191],[266,192,216,124]⟩,⟨[],[124,178,132],[61,39,135,309]⟩,⟨[],[5,83,243,35],[32,172,256,70,256,130]⟩,⟨[],[22,170],[125,29,5]⟩,⟨[],[149,237,185],[200,206,166]⟩,⟨[],[90,218,58],[187,305,69,63,99]⟩,⟨[],[99,127],[316,144,34,146,128]⟩,⟨[],[242],[39,221,41]⟩,⟨[],[1,233],[126,158,84]⟩,⟨[],[68,214,42],[53,269,253,1]⟩,⟨[127,254,217,149,22,25,251,130],[1,271,103],[252,326]⟩,⟨[],[326,200,300],[327,1]⟩,⟨[],[319,79,169,227],[140,6,148,84]⟩,⟨[],[180,112,172],[35,241,321]⟩,⟨[],[303,265,237,317],[16,132,14,124,326,104]⟩,⟨[231,165,26,103,121,35,287,122,179],[130,288],[123,229]⟩,⟨[],[323,271,51],[120,240,234,300]⟩,⟨[],[42,146,22],[81,269,1,221,71]⟩,⟨[234,183,147,147,183,234],[27,77],[326,242,188,208,136]⟩,⟨[],[186,60],[303,199,225,27]⟩,⟨[],[277],[138,170,6,28,150]⟩,⟨[],[214],[185,129,33,63]⟩,⟨[],[115,247],[16,308,222,38]⟩,⟨[],[20,156],[57,49,187]⟩,⟨[221,221,50,254,254,265,198,270,270,50],[221,79],[76,14,186,192]⟩,⟨[],[6,150],[165,277,227]⟩,⟨[],[109,201],[304,152,252,6]⟩,⟨[249,161,161,249],[174,8,116,82],[253,173,77]⟩,⟨[],[21,213],[260,332,272,90]⟩,⟨[],[90,42],[9,167,227,179]⟩,⟨[],[221,261],[8,300]⟩,⟨[],[300,192,24],[17,119,27,39]⟩,⟨[],[],[190,226,282]⟩,⟨[],[220,214],[63,85,213]⟩,⟨[238,201,316],[219,55,149],[88,168,222,332]⟩,⟨[],[256,104,312],[157,151,331]⟩,⟨[],[331,151],[262,82,338,130]⟩,⟨[],[],[309,75,233,209]⟩,⟨[],[137,271],[206,284,192,278,122]⟩,⟨[],[352,274,212],[107,55,229]⟩,⟨[],[355],[228,238]⟩,⟨[],[316,174],[107,315,43,37,161]⟩,⟨[],[163,41],[180,98,348,304]⟩,⟨[],[310,294,122],[127,19,295,219]⟩,⟨[],[1],[80,318,154,110]⟩,⟨[],[86,360],[319,73,335,1]⟩,⟨[],[361],[270,18]⟩,⟨[196,314,92,219,139,286,16,296,210,82,248],[64,118,26],[135,47,229,115,241]⟩,⟨[],[157,241],[184,70,360,312]⟩,⟨[],[188],[41,139,5,239]⟩,⟨[],[161],[248,150,220,88]⟩,⟨[],[88,220],[253,205,311]⟩,⟨[212,151,305,91,91,232,3,1,272,235],[1,201],[198,44,48,288]⟩,⟨[],[100,234],[251,341,1]⟩,⟨[],[51,329,215],[312,156,150]⟩,⟨[],[150,224,236],[51]⟩,⟨[],[147],[366,334,246]⟩,⟨[],[330,334],[117,233,263]⟩,⟨[],[263,293,189],[120,312,352,374]⟩,⟨[],[242,346],[235,67,319,251]⟩,⟨[9,330,217,152,8,378],[1],[100,122,44,160]⟩,⟨[],[120,34,24],[103,81,173,1]⟩,⟨[28,342,154,154,342,28],[131,69],[142,90,88,334,290]⟩,⟨[],[290,154,258],[165,343,241]⟩,⟨[82,139,139,129,82],[167,325,365],[212,66,140,170]⟩,⟨[],[380,296,226],[95,243,271,237]⟩,⟨[326,128,128,326],[45,143,277],[152,334,58,240,174]⟩,⟨[216,216,216,205,27,21,286,24,208,8,202,301],[278,48,198],[159,245,285,225]⟩,⟨[],[69,187],[128,4,324,150]⟩,⟨[355,62,158,302,236,236,332,62,355],[206,10,220],[73,149,143]⟩,⟨[159,163,286,15,215,359],[139,175],[30,168,244,360]⟩,⟨[],[220,142,20,162],[167,347,131]⟩,⟨[],[355,383],[360,64,358]⟩,⟨[],[364,172],[129,337,87,379]⟩,⟨[],[311,313],[192,296,330,158]⟩]
def last295 : PathCode := ⟨395,0xc030db2121803209c01a030c20ed1ee134219261d65541d97e0244c89f9011702302a80f02a010100e02622cc1718b232560741890b60d49a0b00a00a41411c310170ae8b405a3d0628a41403c0a81541204007203d10e388570732e207c708af2c415c548e7314168278412062d8971761363d43a1702d22a01c9801e227c5296c20a37c328bc1fa090428bf30218cab03a0542688f84a28c32c4f1730e23e0040382185945610d0283b0668542785a06c139270160289182b252c630f329a55c4681c2501a0be095098014059850683304e9470920c04a1252fe044178b216e408878812c6504518a11de3288d0760663b87b00a30c54ca883f04a1ac6c9671541dc7914e08449c5e8fc2884b41e06d1ae2e4458560a62b49b96d0463f84915207c148478da04c2ec229740e05246407c1085800498723a09ca100218453c0d1072d41e80b10b2cc4f8158d50de5286387d226578191121a41c88f12208e5c80f0220dc358498312be5142596e2d61e48b8a200e4f46a02c2c8500688982980747186125e2285d046246304679150f6298750fa12c5ec348972f41a87f8910301e04405914e3a47d9162541982f0c32fa5705a9040805e40b8620fe4e8830de266174339292901209098306c5687312b11c06cba8441ba3709a96f042040888d309c46c3a86c2483007c9781323408a12c1ca17c8508617c2ac870820fc4ec9b0832c250c670131624200c9771920dcc100e2b62249811010031090001,0x4900c4100440980892b6038c10371925dc0c90816204c671432c220c9b13b0fc208870ab17c2188505f1ca4b08a0d01325e07c8c02481b03a91b09c34c888100425bc9a8dc1ba110ba81b11c4ac7315a06c60c908482904a43385d2663788313a0fe1880b9790804105a95c2fa30c2f0662544587d8e914e164440780302447f86a2f425c3497b12c3e8750a60f6454678c12461185d08a25e1847181d298260689402c80b06a13d00e2888b8792d65b8259452be0c4498d60dc0880f17208e4888f0721a44481915e2261f46394a0de3541593e2cc42c0b07a2d441c0d14f184008a102723a61c049601081f0641490e05d0228bb04c3684785207c548490fe0465b49b8ad0a6158458b91ae1b41e12d2883f05e9270845387907715459c6c86b04a0fca895330c0287b0ee0661d88d0ca1de284519412c62048790216e2c8178112fe4944a03009251c4e8cc06861405805098254be0682500704695729a3cc6314b2b2460288582704e46c168278150668ec028434561652180e0040f80e25cc4f0cb28c1288f89a0540e8ab0633022fc428241fa2f0328df20a5b05289f1e26001c8a82d25c03a0f51365d8970b62061042785a31439c548572c42bc7081f2e21cc570e210e0f472100120550a80f0140290628f405a2d0ae85c310470140290a02c09a0350b66247415823262c170b32623801000402a03c2a88c1704049f9320245f81d9551d64982184d1ee3b4c200c01a2703206021236c03003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked295 : walk cp295 moves295 = last295 := by decide +kernel
theorem result295 : ValidCode last295 ∧ ∀ i, 295 ≤ i → i < 395 → P i := by
  have h := walk_sound moves295 val295 (by decide) (by decide) (by rw [checked295]; rfl)
  rw [checked295] at h
  exact h
def cp395 := last295
theorem val395 : ValidCode cp395 := result295.1
def moves395 : List Move := [⟨[142,56,212,16,112],[140,62],[193,43,73,59]⟩,⟨[65,107,107,65],[259,327,135],[142,66,152,330,246]⟩,⟨[],[64,192,214],[303,221,101,307]⟩,⟨[],[59],[16,48,22]⟩,⟨[],[294,272],[235,327]⟩,⟨[],[217],[190,350,232]⟩,⟨[],[22,48],[99,317,219]⟩,⟨[],[143,31,69],[82,324,22]⟩,⟨[],[366,150,4],[57,287,235,133,361]⟩,⟨[394,264,233,248,248,26,26,233,98,142,308,394],[361,5,113],[224,158,210,390]⟩,⟨[],[236,228,18],[401,145,245,295,175]⟩,⟨[],[241,103],[354,64,122,68,26]⟩,⟨[],[110,338],[201,255,127,247]⟩,⟨[343,35,304,217,160,153,246,370,187,99],[255],[176,224,150]⟩,⟨[],[26,194],[349,77,307]⟩,⟨[],[351,363],[376,172,26]⟩,⟨[],[144,18],[155,79]⟩,⟨[143,1,260,260,336,117,81,298,233],[105],[170,292,66]⟩,⟨[],[242],[403,197,263,347]⟩,⟨[],[287,179,285],[380,354,362,200]⟩,⟨[],[290,310],[397,301,131,341]⟩,⟨[],[7,325],[212,166]⟩,⟨[],[296],[149,145,7]⟩,⟨[],[161,193],[56,8,120,84]⟩,⟨[],[28],[159,261,57]⟩,⟨[],[291,393],[132,142,106,230,28]⟩,⟨[],[278],[75,353,123,271]⟩,⟨[],[339,201],[400,56,250]⟩,⟨[],[250,334],[41,173,327]⟩,⟨[382,271,350,397,288,282,118,254,92,297,121,264],[161],[80,218,170]⟩,⟨[],[332],[71,25,151,17,115]⟩,⟨[],[375,313],[228,262,338,84,106]⟩,⟨[],[106,84],[95,223,373,155]⟩,⟨[],[1,113,273],[422,106,158,282]⟩,⟨[],[194,144],[135,267,1]⟩,⟨[],[387,21,387],[152,194,248]⟩,⟨[],[348,230,14],[269,225,337]⟩,⟨[],[],[196,12,312]⟩,⟨[],[58,230],[303,357,141,257]⟩,⟨[],[285],[176,402,266,294,58]⟩,⟨[],[58],[335,153,141,405]⟩,⟨[],[305],[172,58]⟩,⟨[],[],[87,389,375,333]⟩,⟨[],[399,41,401],[174,210,374,296,348]⟩,⟨[],[348,376],[195,343,41,401]⟩,⟨[],[37],[18,266,204,176]⟩,⟨[],[180,376,28],[203,1,337]⟩,⟨[],[337,61],[422,20,26,348,368]⟩,⟨[],[434,116],[155,241,79,311]⟩,⟨[],[89],[204,46,314]⟩,⟨[],[164,344],[245,423,429]⟩,⟨[],[1,165,209],[204,324]⟩,⟨[],[288,150,216],[369,245,1]⟩,⟨[],[431],[46,340,312,356]⟩,⟨[198,257,217,117,305,145,73,84,200,97,97,353,371],[312],[409,427,317,63]⟩,⟨[],[63,317,129],[298,264,112,114]⟩,⟨[],[222,158],[23,275,315]⟩,⟨[],[315,381,47],[76,118]⟩,⟨[1,184,146,14,132,1],[24,344,430],[123,51,235,429]⟩,⟨[],[393,407],[322,92,24]⟩,⟨[],[72,74],[249,71,171,139]⟩,⟨[],[179,149,161,37],[360,400,266,454]⟩,⟨[],[84,196],[261,119]⟩,⟨[],[405,159],[142,418,364,84]⟩,⟨[],[24,114],[185,289,233,389]⟩,⟨[],[1],[328,244,46,154]⟩,⟨[],[34],[177,239,197,1]⟩,⟨[236,304,390,313,93,93,56,56,348,236],[251,171,393],[186,386,84,246]⟩,⟨[],[220,6],[39,21,197]⟩,⟨[177,39,86,331,446,343,224],[169,189],[418,202,234]⟩,⟨[],[200],[203,409,169]⟩,⟨[],[405,97,217],[136,280,424,126]⟩,⟨[131,423,423,131],[284,378,316],[397]⟩,⟨[],[343,77,169],[466,104,358,196]⟩,⟨[],[196,204],[167,269,3,335]⟩,⟨[335,312,374,466,342,250,305],[325,353],[170,136,200,306,140]⟩,⟨[423,433,452,219,212,50,419,104],[248,378],[455,419,51]⟩,⟨[],[65,195],[392,414,136,182]⟩,⟨[],[312,324],[327,13,421]⟩,⟨[1,123,77,39,264,1],[305,429],[362,218,436,216]⟩,⟨[],[376,268,16],[61,199,111,347,51]⟩,⟨[],[51,355,299],[118,100,270,314]⟩,⟨[],[304,238,396],[401,225,89,51]⟩,⟨[],[161,205,245],[430]⟩,⟨[],[216,378],[243,287,381,161]⟩,⟨[],[195],[278,286,250]⟩,⟨[],[118],[219,273,473,457]⟩,⟨[],[29,437],[392]⟩,⟨[392,131,379,57,188,352],[352,398,368],[83,387,29]⟩,⟨[],[175,209,167],[98,174,394]⟩,⟨[],[260],[147,169,107]⟩,⟨[],[461,273],[72,392,110]⟩,⟨[380,380,333,305,13,68,384,41],[284,84,142],[441,423,427,223]⟩,⟨[],[185,297,243],[76,188,120,246]⟩,⟨[],[122,424,24],[263,85,3,345]⟩,⟨[],[345,91],[114,166,352]⟩,⟨[104,230,152,211,485,482,482,139,266,67,85,122],[122,90],[455,377,243,271]⟩,⟨[],[25,133],[314,202,196,108]⟩,⟨[1,223,97,97,186,163,1],[174,184],[59,231,451]⟩,⟨[],[289,397],[356,140,62,318]⟩]
def last395 : PathCode := ⟨495,0xcc6917384388af17b32a6d0ae17d398294b6024080744bc0c80706b0ec10127e4c88716305a6dcac8e71041f89d936106104e80a11001102600523827406138272360249472544586701334c68cb68230ac22c5c9b81106242d8352680404c9203083b4f61981500e4c00f113e094358fe1cc5681b0ca2341d8270b216e408d104201e6a8b313e0a41c8578ba08c078b90471343d8051863146fc4090f1aa1bca50c71925dc0c9cb14c3a87d0963b65b8259452be0c4499de2d61e418021200500688e80301e0e41bc2a8240c08bf10a1ece28ac3281f4e18e103e5c4398ae06617433929176614059ae1245488f84a28c32c0b10b1b209cc90df0ca1f09e82c1a8034c18ee144508e70d60dc0882b9621bc4cc08958298260d40692a03c0501a02082305c0482427bce90d22240c8c391d138754ba04533e414321ad3ae334d21a507e544600d03a84f02a1bd2a6478910ef36a2f0aa8eb02a0709409135e308a781a11e2d49783a2ac18c3082f0f45a85385926e2b4299912903e0bc8170c40b8799b10107707e9142583942f90a3345d84d9d6206684f18c119e454e20e0040664d80090e01c4e79411460188d8293762d86d02607c0084712b3ca590ba99b3d2580a20fc17a49cd90071f20a01e0040c04246d965218210f69971525a0f09e02d25c03a0501e83141d97e02469c3517a12e6a4b38aa06e6080715b1124c0881c90ee4641598e2963180d9062741fce09183182d0ae8e310c7ac2a8cc068774f20f509e168f319e1a6444c98513803909691338c2ac5f0fb1d26202e0682f82549206c0ea5bc9a8dc1ba2ccdf18b29c3c84f1d33dc658a19cd1483b00a10d1ae1b4919b611479c150f709a2509297f3946e8c78b1210670f41d93564b8f11df2625ccce90707a30c2f1b311a55ca68c403a71ca49901605842c1b910e7a8930430cc7687f801,0x47f9da0cc10c931ea10e6e42c161160640a49c703a310a695711a6cc2f0c307a41cce97326277cf112e356764f419c2102c4c79ba3945fc9289409a3dc151e71146d89186d1ae4340a0ec148734a19963dc74c4f0f229c62cdf0b31ba3709a96f0ea1b0920952f81a02e1881d23ec5f0ab38c44c968e4380144c99111a6678f305a09e3d4f21dd0683302a9eb10c38cae8b4318460e087f2744180d8c6296638159190ee7248813011256c0718206e2a8b39a912e5e8351a70245f81d8c51e81403a1702d2780f096815265cf68842185946d9090c00101e0281f201cd912717a3f0a21603d266cba9643ca4ac4700207c0986d0b63760a48d806146504e78710e0024d8199040380e211519e304f19a12067584d9763344282f8e52584507e9dc0106c47982e0c405cbc8f8290644298ad26e1645396a0f40bc308632ac0e8978b511e068a78c235e2449401c02a3acaa8bc36a3bc9111e2a66f42a13c3a83406015107e694d20cd3ae6b43210533e114ba1d5138474c3832224348e91ef2421205c08c208680500f02a01a4d4098298560089331bc5882b8220dc358e71421443b8c180d1a80b09e87c0ca37cc90271b242c0b0cb28c1288f9521246b8059851764a43385d0662b83997103e384e187d3282b0e287b10a2fcc08902a86f0e40780303a068940200084180792d6778498312be5142596e3b62587d0ea14c72c0c97719231ca506f1aa43c409bf314618050f613411cb901e08c2e8578720a44f8b31aa01e108d110216e2c8270762343281b15a1cc3f83582513e3c4c0039150660f60ed3084804c8102680d42d9891106e05c88b0ac08cb69a334c04c6711625451c248d82724e00609d23801426044100284e80411064d89d87e10439cac9b705a58c8713227e404ec1ac070320bc1d1080090b60a53985f4ae1b432a5ecaf0e238445cc6803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked395 : walk cp395 moves395 = last395 := by decide +kernel
theorem result395 : ValidCode last395 ∧ ∀ i, 395 ≤ i → i < 495 → P i := by
  have h := walk_sound moves395 val395 (by decide) (by decide) (by rw [checked395]; rfl)
  rw [checked395] at h
  exact h
def cp495 := last395
theorem val495 : ValidCode cp495 := result395.1
def moves495 : List Move := [⟨[],[146,352,162],[141,257,355]⟩,⟨[],[165],[264,66,200]⟩,⟨[],[450],[19,315,117,397]⟩,⟨[],[11,233],[90,300]⟩,⟨[],[14,364,480],[69,11]⟩,⟨[],[299,309],[442,338,292,490]⟩,⟨[],[404],[85,419,317,179]⟩,⟨[],[283,435,241],[16,126,380,62]⟩,⟨[],[126,254,422],[99,59]⟩,⟨[],[59,221,479],[262,426,336,248]⟩,⟨[408,420,121,502,415,63,178,194,459,495,123,261],[62,32],[89,145,249,117]⟩,⟨[187,107,262,204,15,444,153],[179,383],[276,68,392]⟩,⟨[],[92,172,142],[133,311,95]⟩,⟨[],[95,101],[156,304,92]⟩,⟨[],[64],[289,105,73,67]⟩,⟨[],[409,157],[460,62,222,224]⟩,⟨[],[320,384],[317]⟩,⟨[],[281],[294,36,314,264]⟩,⟨[],[302,466,136],[351,469,343]⟩,⟨[],[1,289],[272,82,4]⟩,⟨[],[446,350],[27,75,493,1]⟩,⟨[],[145,191],[400,62,50]⟩,⟨[],[400,192],[355,481,49,433]⟩,⟨[],[73,427],[264,438,172,184]⟩,⟨[],[476,74],[9,185,249]⟩,⟨[],[],[330,332,478]⟩,⟨[377,270,264,185,280,83,9,9,147,287,195,137],[474,206],[211,407,463,271]⟩,⟨[],[445,191,65],[4,322,308]⟩,⟨[],[514,24,348],[245,191,285]⟩,⟨[],[1,101],[130,522]⟩,⟨[],[],[397,361,87,1]⟩,⟨[141,362,32,245,399,237,111,228],[397,351],[294,258,350]⟩,⟨[],[62,158],[423,303,155]⟩,⟨[],[155,391],[516,434,62]⟩,⟨[],[102,288],[95,269,369]⟩,⟨[],[369,139,105],[86,58,214]⟩,⟨[425,303,323,359,378,464],[470,220],[263,149,297,507]⟩,⟨[450,360,230,230,230,464,324,144,165,165,278,454],[91,157],[190,494,356]⟩,⟨[],[174],[185,111,93,91]⟩,⟨[],[91,505],[30,446,396,522]⟩,⟨[],[222],[61,209,503,481]⟩,⟨[],[63,433],[486,228]⟩,⟨[],[216,144,454],[229,339,63]⟩,⟨[],[483,229],[260,38,194,184]⟩,⟨[],[304,14],[319,271,443]⟩,⟨[],[161],[466,284,372]⟩,⟨[],[494,74,326],[447,171,91,333]⟩,⟨[],[303,409],[468]⟩,⟨[],[274,436],[15,511,93]⟩,⟨[],[457],[16,74,410]⟩,⟨[1,487,1],[470],[207,127,437,359]⟩,⟨[],[323,117],[308]⟩,⟨[],[400,414,210],[233,117,437]⟩,⟨[],[229,433],[232,514,148,360]⟩,⟨[34,475,312,312,312,307,350,459,161,240,240,34],[346],[283,1,171]⟩,⟨[],[297,217],[138,314,64]⟩,⟨[],[392,394,500],[527,221,375]⟩,⟨[],[423,283,341],[364,68,392,190]⟩,⟨[418,386,454,525,386,177,277],[216,232],[443,275,527]⟩,⟨[],[13],[76,150,438,424]⟩,⟨[],[448,320,400],[247,33,511,13]⟩,⟨[],[19,97],[272,394,454]⟩,⟨[23,375,332,311,323,31,260,23],[254,416],[479,551,11,549]⟩,⟨[],[161],[156,266,514]⟩,⟨[],[514,228],[197,243,241]⟩,⟨[],[249],[300,208,544,234]⟩,⟨[],[50,192],[553,305,127,239]⟩,⟨[],[163,49],[66,438,68]⟩,⟨[],[480,384],[55,237,121]⟩,⟨[],[415,559],[46,164]⟩,⟨[],[434,436],[91,121]⟩,⟨[],[323,55],[398,412,196]⟩,⟨[],[78,104],[317,291,465]⟩,⟨[521,521,341,1,1,341],[425,135],[88,186,78]⟩,⟨[],[198,542,498],[539,451,525]⟩,⟨[447,392,350,85,500,315,476,493,5,195,539,439],[515,141,517],[310,230,442]⟩,⟨[],[48,446],[319,145,435,249]⟩,⟨[565,396,253,363,165,459,224],[209,515],[52,174,402,48]⟩,⟨[],[48],[501,379,83,325]⟩,⟨[270,242,171,509,236,432,199],[229,543,107],[478,552,284,360,48]⟩,⟨[],[376,90,110],[29,203,17,303]⟩,⟨[],[1,79],[338,534,2,478]⟩,⟨[],[180,516,198],[461,147,183,1]⟩,⟨[],[103,339,547],[478,76,86,328]⟩,⟨[381,525,525,511,510,392,40,333,351,342,40,381],[480,302,52],[355,413,467]⟩,⟨[],[427,69,459],[508,450,418]⟩,⟨[],[80,286],[217,249,137,259]⟩,⟨[332,19,222,222,91,332,332,332,509],[551,219],[516,152]⟩,⟨[],[260,254,290,206],[397,275,303,423]⟩,⟨[],[423,509,207],[514,570,214]⟩,⟨[258,292,235,366,366,18,324,41],[414,148],[559,555,247,477]⟩,⟨[],[155,61,269],[378,132,322,154]⟩,⟨[269,337,546,428,112,82,557,460,164,334,314,491],[536,242],[201,25,455]⟩,⟨[],[23,47],[62,120,20,410]⟩,⟨[],[556,60],[401,429,495,235]⟩,⟨[],[47,509],[190,164,528]⟩,⟨[],[528,354],[287,439,323,47]⟩,⟨[517,27,157,274,54,218,234,515,282,341,511,327],[325,355],[478,6,588,396]⟩,⟨[505,108,257,589,264,270,195],[66,180],[461,273,285]⟩,⟨[],[45,469],[514,390,298,398]⟩]
def last495 : PathCode := ⟨595,0xc3b11a1ee0a8f388a1be10833899240610468b72b43987f06b04a930fa84b2dc94cd68933bc5ac8301b18c52c0f1724248bcaa8eb44a57c8903230e4744e08517e944d78c22fc048d3a1a3cc58ca084f0b41a8bd09735259c5501a2ec26ceb10334278c60a182d8134161e54365a4b81343b8890b00840ba1306a86f4042887718347c9186514725439cdea4312c76c9a96f0ea33d209bf3148dce49bb31c0084712b43c88ccf046066034121ed32e0886f1621041f89d936106884d00d13a66c5278fa2ee9289d0d721a050760a439a50ccb1ee2443bcda8bc1106247405c42a7ac2a8cc0f00606485822264c289c01c86342b9ba31e2c48419c3d0764d592e3c477c9897333a11c7e9743aa8ac8f0723fe104d19a62d441c851cf0e2800088983505a0549fb22a7107006420a67d1121f1743583720307a54cc308b17240108231320384200693ae8a4cc0a80720ac9f13310c2f8559c647427d02a3c0d05f06203c0088351a0a53985107e0bd24e3a91319b3d22ec949173843891721335c3d80500f06217c7292c2288d4a78f10a6598d52174542bc0a97b32a6d0ae17d40e274ea175088200509d02800a48d9560748186984e02c32ca304a23e3c83b8cd348781101643581943e02d278920fc9501e03d06283b46c538c59be2a42492393d1a81c02a0ac06a16c0480736483cf89584581141a1dd3c83d48e1881124c10ca283320809206c470530928941605848805914e728878810503e5280c02a28cd071f21640bc3d13f1a4748f7a11360241248c7294269050360e62b82908f16a4bca12422fe644a420107e8c92908743a3cc171b62461b45a18c2307051f9451f62552206021236cb287f0c4278d110203e7143d8663b43fcd2a1c25a44caf00b30a550de1c81b8374598b61b40981f01319c458fd0171d20e11ca4b3ec72cdca083f01e4181e11f05e5058061463b4f621445a55ca69fc48a4104624d186858f51260867f43a01c250244281940fa7d10600547643899037304038ad85e3665747181d38e524641783a27c010810460464040d9216738f9a4e0ac08cb693715a4311e9c33fc298cd22703209cc91b72b2601020a02e2760808b80184e09c8d80927dd048d048060431861090484dc001,0x4dc12109018431981480341049f70923609c9380182e0809d82e2281021802b26dcc902703289ccd0a63fc70d1e90c15a4dcb68230ac938f99ce21636404119460040109f03a25e06414938e0747195d366178ad80e3040dc9910e476015061f40fa650280912500703a1fd086498f52161869344610448a7f0a695745a850f60ed146019059791f0784180793f0820dc9cb3ec92d1c8381d205cfd11619c04c1f0261b42d8598dd1b8720de15430a02caf11325a870d28ff3b41983d9c503e408d109e0c41fcb28db212181220951f65151f9c12306305a06d2466d8170f343a21d2923207e804a41912fe908a112f16a23c290ae0e60d90509a29431d24890360844f79d21a44fc3d02f1647c9072332a2301280f9050204879ca14e164881611602509294c4701b0920203328a10c9301126208e0f53c87741a045458560f8a0f36401c0485b06a2b02a0701a84f5238922a46f8c594e46c0ec628f41e0540fca482780b43e065358591101e03483343b8f223e128a30cb02c13869a060745588d829280740508800885d4ea09d40e5f4ae1b432a5ec0a8af45485cd51660a63c4a7a352284b07285f06203c050f635c84d170e238445c948bb3d266d130ea24e2f47e1443982951a20d0080f06217c0d08f10289f474718558be10c4cc9f02b0722a0cc2293ae1a4200e13208c50810017222cc315307a80c370d617487d1119f20a190701c422a7ec5496835026008a000e273c851072d4698d18413fe1c88f22b3aa5d07e84733a5cc989df3c44b8d59d93d0670840b131e6e82b98d1c870028993222160648180f03302a9eb42a170741891102f0da8ef2447b8cb14339a2907601421a35c9d24a2ee3e9279b13a6344d02211064d89d87e1045886f02232e7b41200d066118cf22343c4ac4700231c6ece4a373146fd208cf0ea5bc9a9db12c90cde8e725451c6524647c60c770a24041bc6a84c0ba210b02243b84d0b81694367941604d2d8860609e334240ceb09b2ec0685516735225cbd06a0b413ca09633cc868d38122fc308d7a5117e2144e11d30e0c88915f44a3acaaa2f4245c80f14b18c06c8316b3bc24cd6a532dc12cfaa4c04a1ac7f0e62b42dc46984240264338421be228f382a1ee4683b003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked495 : walk cp495 moves495 = last495 := by decide +kernel
theorem result495 : ValidCode last495 ∧ ∀ i, 495 ≤ i → i < 595 → P i := by
  have h := walk_sound moves495 val495 (by decide) (by decide) (by rw [checked495]; rfl)
  rw [checked495] at h
  exact h
def cp595 := last495
theorem val595 : ValidCode cp595 := result495.1
def moves595 : List Move := [⟨[],[50,572,208],[177,127,485,45]⟩,⟨[10,267,311,527,313,371,566,488,427,221,549,10],[121,491],[428,522,126]⟩,⟨[],[524,42],[453,157,41,417]⟩,⟨[84,347,225,260,192,498,580,84],[457,407],[100,508,258]⟩,⟨[],[156,346],[223,281,189,151]⟩,⟨[],[215,105,89],[266,568,214,204]⟩,⟨[],[526,230],[451,309,83,485]⟩,⟨[],[173,29],[494,98,464]⟩,⟨[],[364,582],[157,489,555,131,151]⟩,⟨[10,21,351,10],[453,233,45],[568,196,72,438]⟩,⟨[],[488],[219,321,141]⟩,⟨[103,309,130,404,434,336,241,241,539,103],[1,55,489],[276,462,372,186]⟩,⟨[],[186,372],[461,1]⟩,⟨[],[321,163,97],[544,340,104,204]⟩,⟨[],[152,258],[509,193,343,341]⟩,⟨[390,603,448,284,229,192,119,119,389,602,245,322],[377,159,411],[152]⟩,⟨[],[152,50,458],[209,551]⟩,⟨[],[135,415],[98,60,502]⟩,⟨[291,208,561,184,11,11,363,524,147,492],[496,26,378],[259,423]⟩,⟨[],[423,245,537],[466,216,498,142]⟩,⟨[],[30,246,488],[397,259,387]⟩,⟨[],[],[150,526,38,30]⟩,⟨[154,245,245,118,138,138,118,154],[562,102,176],[37,583,341,521]⟩,⟨[],[95,427],[334,252]⟩,⟨[],[66,316],[463,387,345]⟩,⟨[],[463,85,113],[360,168,332,66]⟩,⟨[342,378,378,331,555,496,265,3,181,43,150],[],[151,435,523,505]⟩,⟨[],[305,409],[136,212,228]⟩,⟨[],[436,374,68,262],[51,227,73]⟩,⟨[608,95,411,416,555,90,183,212,5,425],[257,385],[76,264,406,402]⟩,⟨[],[544,50,370],[109,475,599]⟩,⟨[],[425,173],[382,142,536,524]⟩,⟨[],[468,8],[59,179,529,359]⟩,⟨[],[333],[604,286]⟩,⟨[395,460,567,378,294,517,531,175,127,315,390,263],[392],[39,571,165,565]⟩,⟨[498,112,307,112,498],[529],[24,150,620,136]⟩,⟨[],[12,562,104],[369,427,217]⟩,⟨[],[353],[166,256,12]⟩,⟨[192,611,362,347,180,620],[324,26],[539,497,73,255]⟩,⟨[],[297,157],[598,452,376]⟩,⟨[],[486,2],[275,435,219]⟩,⟨[538,538,548,148,148,171,559,327,359,171,548],[287,119],[346,510,2,260]⟩,⟨[619,20,376,132,546,519,321,37],[122],[313,267,233,7]⟩,⟨[],[7,105],[376,394]⟩,⟨[],[124,22,530],[495,7]⟩,⟨[],[401],[298,336,144]⟩,⟨[356,197,223,627,504,241,544,178,244,77,544,152],[216,508],[191,129,77,89]⟩,⟨[],[89,215,135],[242,272,514]⟩,⟨[],[100,206,190],[315,573,263,89]⟩,⟨[],[529,105],[312,264,208]⟩,⟨[179,201,249,161,98,616,443,116],[76,430,366],[501,527,285,479,87]⟩,⟨[],[9,557,543],[358,154,360]⟩,⟨[623,347,317,512,10,307,332,62,62,148,215,91],[372,156,2],[505,615,551,513]⟩,⟨[],[1,433],[320,582,220,330]⟩,⟨[],[372,476],[77,189,1]⟩,⟨[],[401,245,465],[98,180,248]⟩,⟨[],[530,460,218],[555,127]⟩,⟨[],[337,579],[92,606,246]⟩,⟨[],[634],[517,491]⟩,⟨[],[379,549,345],[172,636,324,438,252]⟩,⟨[],[40,508],[339,243,391]⟩,⟨[],[479,79],[210,190,40]⟩,⟨[23,96,125,125,96,23],[166,150],[493,445]⟩,⟨[],[385,333],[410,330,460]⟩,⟨[],[314,222,24],[355,121,617,599]⟩,⟨[],[1,365],[144,442,324]⟩,⟨[],[492,176],[471,443,153,1]⟩,⟨[],[5,151,163],[158,626,334]⟩,⟨[],[500,222,336],[559,605,5]⟩,⟨[],[5,141],[178,204,144]⟩,⟨[],[306,124],[647,5]⟩,⟨[],[1,111],[86,568,454]⟩,⟨[],[492,300,48],[275,595,563,1]⟩,⟨[],[11,541],[30,176,420,396]⟩,⟨[],[86],[183,641,11]⟩,⟨[627,395,395,627],[627,261],[308,488,126,280]⟩,⟨[1,26,363,103,569,100,1],[96,360],[51,107,443]⟩,⟨[121,499,82,276,15,443,255,664,38,422,544,63,580],[1,163],[576,440,642,340]⟩,⟨[],[146,668],[431,1]⟩,⟨[],[253,219],[404,238,328]⟩,⟨[496,450,279,131,226,128,153,615,110,28,649,31,342],[410,126,14],[255,587,85]⟩,⟨[],[321,425],[382,348,262,130]⟩,⟨[],[112],[23,115,423,101]⟩,⟨[556,165,77,8,484,455,226,555,510,165,625],[143,603],[652,434,114]⟩,⟨[],[156,510,92],[585]⟩,⟨[479,508,602,567,479],[479,5],[268,336,62,40]⟩,⟨[8,171,350,44,36,640,301,8],[570,236],[97,467,251,45]⟩,⟨[556,318,318,556],[89,395,525],[508,672,140,306]⟩,⟨[],[192,472,462],[613,653,291,89]⟩,⟨[],[311,559],[246,260,428]⟩,⟨[],[8,560,148],[65,527,545,285]⟩,⟨[],[259,415],[490,164,8]⟩,⟨[644,657,657,657,139,36,36,181],[592,454],[359,161,21,605]⟩,⟨[],[9,451],[132,502,206,412]⟩,⟨[8,156,618,464,262,8],[340,140],[475,243,269,365]⟩,⟨[],[515,19,499],[350,642,588]⟩,⟨[],[8,688],[527,13,199]⟩,⟨[],[119,615],[316,390,568,8]⟩,⟨[8,681,270,165,199,642,434,8],[554],[477,563,621,201,389]⟩,⟨[273,86,104,583,623,630,511,231,273,588,333],[489,383,11],[526,684,424]⟩]
def last595 : PathCode := ⟨695,0xc3b03354c66cf49271d497c9294c568094060584987d47203d5383a01c8a83f8110baa8b47c9186527f5226c07a0f0192a002c9604482d4ae088210064138ba3d44992f2262bc98d3315b0bc788ef9312e66749e16815299c3911e3e42c86f06655465cbca0b4f225d592a72b26010223d3867051f83230e474de0281f2780188b02685c0b4a1b55c548492b704487895a960867f5438c22fc048ffa851880f13411c1905e0cc2293ae1a4200e1320ac50c16c1a84f4e98d10e60d937216186a18ff0a627ca0cdf2422844bc889932fa81c4e9d45606453786a0b4028c308b17235d3918e3767251b98a2343dc26a8c1f06b0b210d20883002a3b21cacce89b351c3d88da690e0150f61240408813200d26e4e83f9651b6424301b14208c48c18c4e89544205d09835437855198694362a406a0bd3a89b29211c6d0262863f4ba1d54561182519a44e868d3a9a4ec838bb28a1f425921a4119e454fd9894ee5284d20a2f491d411bf2a29c1501e41eaa3c0a9cf2821e00c0612b08b00a1d028001136954558760b88a03404e5440c12fe5685b8d9400440b0a600f27e1041b93967d925a3907023126a7c528041182112702b14e9a4200a106285c10a2fc551674b43bcda8bc4a84c10c96b52a1ece281f2046894f83a2ac9ac8caa844220d46a3c40a0ec0b22a42e6a94b84213e8e8e311325a871569531da9709417c48a17c508a346c538c582e36c48c368b437a39c95147092a4040029490a04e00b131e6e82b98d4e6358499de34c5a92b9a91f6a24dc121090670d6a532dc4d8ed03726421d0e9e334240ceb1eb42a23cc100e464948291ee24498807a0214431d248904288b4ab94d1e69582722333c798b18ae1764a4a40711a6818850862667744a1503f245c169b711241d0497b32a13ce10e25441b9019810c641859a5d4d8290e69f40fa650a292c1ca06c6314b03c01825a593d0764d592e5266b909a2e5361d4a20fc17a6d0182a93b689475a99016278659464f661476298082380e227d3063b9110822c4a78558be046159271f339c42d5b0ce22c7e80b8e914e728878813e0140489af0c4008470b60561943e11446a53c78a58170620042383903706e867132480c208d038090f685302204c1f2334a29e04c1a83b85b4d19010d09c46c1cc14a8d1068640587942da7e5241f89d80900e6c9079f123e3c83b8cd1381147f9724248bcaaaab32c9a86f88a3ce0a8b325b56a43082a4412a2bc289ef3a43489f87a3ee928bb999450a84af912324abd3099f0343987f06b54a0d0568744ca87cf0aa32ba38c0e9c74f493c9a96f042940600d04808041f801,0x41fa01480340602500425bc9aa4f4f471c0e8e32baa8cf0a1f4ca1d05683454a1ac7f0e603467d30aaf324448afaa1450664bba4a3ee1e89f8d23a47bc288af12a9108290c56a96cb302a3ce2286fa6a32caacaaa2f4245c87f8451383343b8f223e7c5079b200e0249d87e5249f82d9e505819106a3414a7306c2710d0404d196d3b86a04c2784a28cc1f01302214cf6824038234c212013219c6e8dc3908e0041881709607894f46a4503e0650562d8470020c46bc488503e0204879ca14e3a40b9fa22c3395b10b39c7cd270560462f855a9e2c4209110ee3069f4e20e0082a60761854f65186589e016a6475a253b6aa4181b417a3f0a20755368b9099ae5264b8d59d93d09642580603c52c6301b1ca4b0a29940fa7d0e68a44d8974599060c66050186e544388e104f32a5ed049071126dc169173f25404a1dd266218852061a61c4a41291762b8b19e633c88c272561e6534aba2d428241248c714480807a622447b829252464038c108f42a7aceb10334278d0e8872640dced1362dc94cd699c090484dc2891f66a52b96a34c778498d64e66342b9ba31e2c4e02814900a44029009251c950e737a2d03692336c0b8c594e46c28c5085f48a5f09425c1da54d56a1c25a44ce323a13e1094b9aa42e8a80b03b40a8f146883442aa08ca6b2ac0e94f9a220407ce287b52a5ad0c9304a82f0da8ef4b459c550bf10a17062a842006914e8ac270845180105289f12688c0708e5259f63966e5041f80f2980b09104003645b95a2fe30544139340280b89d8558551368042807400a22c2b01840c07828273c0aa8f1ea791502702a26fd412472f48284d14a4ee624fd91519e905218961f4a28bb20e4eca68d3a1a44e66825046456754ba0fd2860986d04729226d3a82f06aa90361a5198154378d5098174422554e86308c2314206c4301091b65943f93a26e03532220040490f60540e09a48d8f651c6cce8ab321c8ec02a0c208434b21ac1f0a30268f72346291b9c9376639390d717222cc300a0b41a9379915607504ea072fa64c8892f284908df28327c298ff286186859370360e6344e993d1a85b10c2b1320384200693ae8a4cc1781904713403c188a14ff8122fc309439fd086a5895a1e044adc4915255c86cb49702682c0189e01f20a0de11d30e0c91f9c13868f5021802b2a9d590974f282cbc9975541986f0b23e4478392671525a09e19d2e64c4ef9e20bc56d332632bc8992f1263d42e813819210220ae0b54485802ca801923c07a1b05229fc6524647ca2cba8443f82a01c8e85380f4721f54981600602556853092a5f1d449cf499b54c0cc3b003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked595 : walk cp595 moves595 = last595 := by decide +kernel
theorem result595 : ValidCode last595 ∧ ∀ i, 595 ≤ i → i < 695 → P i := by
  have h := walk_sound moves595 val595 (by decide) (by decide) (by rw [checked595]; rfl)
  rw [checked595] at h
  exact h
def cp695 := last595
theorem val695 : ValidCode cp695 := result595.1
def moves695 : List Move := [⟨[],[626,34],[239,127,499]⟩,⟨[],[129],[378,286,636,102]⟩,⟨[],[102],[363,129]⟩,⟨[],[443,631],[642,504,102]⟩,⟨[],[286,314,376],[621,541,181,271]⟩,⟨[462,510,694,277,353,327,450,325,162,550,498],[201,659],[152,332,360,392]⟩,⟨[],[534,338,212],[275,193,205]⟩,⟨[],[1,95],[208,478,530,236]⟩,⟨[],[470,696],[645,1]⟩,⟨[397,572,477,400,219,561,561,173,110,134,37,15,353],[647,391,621],[194,614,30,544]⟩,⟨[232,606,643,465,319,486,365,227,341,346],[660],[443,619,577,593]⟩,⟨[],[593,515,609],[490,644,236,454]⟩,⟨[],[438,532],[433]⟩,⟨[],[89,147],[40,42,534,96]⟩,⟨[],[340,200],[531,3,289,377]⟩,⟨[],[517,493],[522,160,40]⟩,⟨[],[432,290,378],[381,471,605]⟩,⟨[],[375],[516,380]⟩,⟨[46,466,46],[708,330],[217,475,179,629]⟩,⟨[],[531,295,195],[86,242,356]⟩,⟨[],[474,216],[187,677]⟩,⟨[],[371,477],[72,692,374,236]⟩,⟨[],[202,224],[275,19,141,45]⟩,⟨[],[325,21],[144,134]⟩,⟨[],[560,308],[633,215,311]⟩,⟨[],[],[280,12,90,516]⟩,⟨[],[618],[529,129,491]⟩,⟨[10,622,588,588,139,122,441,527,234,139,636,157,10],[609,647],[546,58,550,246,528]⟩,⟨[],[154,558,538],[99,395,699,417]⟩,⟨[],[63,155,667],[604,480,24,652]⟩,⟨[561,381,424,97,100,464,508,101,182,342,623,174],[],[441,187,605,141]⟩,⟨[],[337,235,103],[642,466,318,386]⟩,⟨[],[506,378,12],[289,11,255]⟩,⟨[702,170,329,329,641,84,297,3,637,546,347,322],[529,487],[82,716,644,4]⟩,⟨[],[580,692],[33,189,243,407,43]⟩,⟨[21,567,716,117,404,529,682,50,595,355,21],[19,167],[610,50,214]⟩,⟨[],[210,52,680],[699,193,123,19]⟩,⟨[],[527,663],[494,536,654,248]⟩,⟨[],[376,158],[247,207,193]⟩,⟨[],[19,407,551],[406,216,556,640]⟩,⟨[640,671,221,693,415,315],[96,128,372],[145,559,19]⟩,⟨[],[675],[10,88]⟩,⟨[290,289,614,15,333,177,70,166,676,569,232],[306,60,188],[543,345,599,665]⟩,⟨[134,323,105,132,252,86,464,11,355,375,401,530,209],[337,509,239],[110,292,368]⟩,⟨[406,406,304,372,267,391,724,219,653,529],[158,420,96],[281,657]⟩,⟨[],[95],[228,478]⟩,⟨[445,68,692,347,647,337,414],[322,240],[169,551,91,285]⟩,⟨[653,146,445,133,154,342,342,411,411,588,588,253,739],[349,187,457],[148,726,626,520]⟩,⟨[],[4,372,656],[425,621,529]⟩,⟨[],[513],[202,574,4]⟩,⟨[],[306,270,512],[323,533,25,491]⟩,⟨[198,731,462,452,345,704,467,146,170,134,166,254],[1,111,47],[464,108,708]⟩,⟨[],[68,480],[157,1]⟩,⟨[],[1,519],[424,68]⟩,⟨[],[648,682],[619,513,653,1]⟩,⟨[],[593,185,5],[522,622,28]⟩,⟨[],[116,88,336],[607,1,143]⟩,⟨[],[699,555,133],[340,528,566]⟩,⟨[593,338,82,664,139,193,494,151,117,595,357],[66,450,580],[215,477,383]⟩,⟨[],[383,61],[690,696]⟩,⟨[],[658,38],[361]⟩,⟨[26,26,26,57,501,375,719,379,26],[383,423,475],[352,652,534]⟩,⟨[437,561,679,576,318,246,365],[408,392],[717,279,487]⟩,⟨[150,302,727,628,559,559,512,302,150],[21,93],[596,164,548]⟩,⟨[],[138,754,112],[655,537,21]⟩,⟨[],[399],[280,556,166]⟩,⟨[],[420],[439,145,655]⟩,⟨[],[153,555],[74,664,204,558]⟩,⟨[],[114,718,162],[17,153,407]⟩,⟨[],[353],[504,138,652]⟩,⟨[],[652,468,114],[715,307,233,195]⟩,⟨[],[1,157],[328,142,230]⟩,⟨[],[706,116,416],[331,553,1]⟩,⟨[],[83,221],[628,636,280,310]⟩,⟨[],[588,70],[219,579,233]⟩,⟨[],[189,493,479],[202,498,54,404]⟩,⟨[],[676,672],[461,149,227]⟩,⟨[],[701,505],[208,248]⟩,⟨[],[446,448,696],[647,23,179]⟩,⟨[],[437,599,447],[666,456]⟩,⟨[],[404,248,454],[365,573,281]⟩,⟨[],[1,5],[150,588,396]⟩,⟨[],[166,48,710],[149,97,341,1]⟩,⟨[400,101,410,319,386,666,325,500,7,24,178,503],[71,659],[178,586]⟩,⟨[],[602,38],[577,229,397]⟩,⟨[],[193,245],[666,266]⟩,⟨[],[532,776,480],[115,229,307]⟩,⟨[],[129,55],[540,370,94]⟩,⟨[],[176,156,356],[59,111,401,371]⟩,⟨[],[441,235,153],[246,774,262,332]⟩,⟨[],[30,472,470],[751,291,73]⟩,⟨[52,457,505,289,234,191,191,453,638,52],[539,227,379],[750,716,710,30]⟩,⟨[],[210,358],[405,59,721]⟩,⟨[],[555,489,783],[712,752,702,570]⟩,⟨[],[762],[301,55,383]⟩,⟨[488,429,1,639,423,60],[125],[564,734,68,600]⟩,⟨[],[554,302,532],[567,183,569]⟩,⟨[],[495],[70,34,348,776]⟩,⟨[],[366,754],[29,139,653,587]⟩,⟨[],[663,281,497],[448,68,312]⟩]
def last695 : PathCode := ⟨795,0xd070631c264158a18118be1561d83583e128a3314c4f80311b1eca3965ad96300c49c30900e074939195509a0389a04c01e4fc28c09a50c130da0d4b7d890370e48c9290f759403d312ae0561397d8c63564b96916f26a6908028418a171242813802c4c79ba0ae0345ba223bc698b52573523ed44a873fa3706e86713248150a6f06aa90f00f9590b7072b1b24c979131230dac5c748a727a350881c91b65943f93a26e4255c2ec4da64c8892f5245b89b1da4ce474de0e8538af48213c0106208e2e40ca550762984f026106005476439599d12f0320a48474540597d2aa32e5e505a793908e0c49fb62a911661344a0151429ff6226e0908483386b529a31420c00c227c49a8dcc511a0ec3cd869773328a1740613be4c4b9a11460040208bf6046080703247e705841395107f03a9445fa04cff2865a63b8a90920dca8913ae92b08b10a8c40780a028abf5cac303c16c2da950982192d6b5875a253b6bb84b04b5fc61845905218ad52d96605479cce9075f2520ae1154682949f87a3ee928db08a30e8e94781539e354720ac4c88801000405a6dc44858192a002c9604482d567a4119e9e8e38aa2ce9680b9fa22c338d1a1e256a596197e1847882f15b4cc98caf0b33e2b60b48a80729acab03a53ec1405a991600512ea6c148281549183182d02605d108954f612408a270668771e447d70a2f4240b97111e2447b8292be38cc0d2b27353ac1cbea075845fcad2e70c49dca509a414419219bd1ce4a8330de54c66d32a1f3441086f821330505041b9396119159d52e80709425c1da54d56a1c25ac50381d02800a4281f01029605c1010d02e46ba7231c6ed8724b4720e0161e50b69f8e187d3285155d88e42c30d60818032420442fc4288b4ab9f216457c8919255e984cf9712667744a1503f245c7d24f18278d7309e5566593521a5ec14c089a83b8254a7af23ae8a43d9c56083f05e9b45a0100948bb3d2a6c0493b0fcc18219ce3e69382b2ba5d4668252c62f69191f28b10a090f6a9735485c46a8337c908a10025ae3a92f9252989d4179b51785541da05478a3441b0141e6c8e92b212e34977a212c62b8711c209e654f7ada0de154661a50d8b74b210d406605602091362a4b41e10be429030d347a810c015954e9a57815137ea08111472ba38c6b0935e207c2d00a35e58511aed56e734fa2d515e2e8f50ef52ac3c7889f1045894f0ab17c08d5b10b5ea86c7ab0b07c218c594e46c44c7f0e603423cd886056064579a1d10e4c9670b65266b909a2e02469c7ea4c588b803482713a7501e92c5a87d4e607415a0d1380d91c07113e98331abdc6527f5226c07a0f04b27a0ec9705a26cd8b2db46a4503e2cd0180955a2a55fe7288790248e5e81fb0a5349d8a581e2e43fc488334e236024ac740428863a49120bd0a6a74060c6435a6e5d6ae5501e4180340d09033ac7ad6f31306c1cc689d32eca298d1f60365d422080520b2500310528b14be2451965193d9855788343224040228c50ae33cc67951801,0x55199e3ccb8c508a34029003220d5786153d946196914be2c5528c41002c9520200221750367d98d28a2ec74c6887306cc4d6f1eb3ac40cd08d0180791502b95d69b835b190609d0a6af4120924638a2404b1c248d84e20cc488ff2e4078a5a76534c281f97a48e408879ca5fea955a025018b343e11446ab6d8b1b35a25c0ec9e84b23c07a1b05229fc652f731a60d3e9c41c03653803415a1d0e61f55a84b01e9d413a09c34ae05889307e9a70248b9099ae5262d96713210e87579991560180d888f0343987f11346c538c588607cc2c7aa1b5ea42d5b02317c2ad4f16210427c78b0f52a3bcf50ba15eb54fa1cd56ebb51196135e0282d01f5e224c6b0e32ba51c1128237e5457826954e564c020447a34d0310a0be784b40a913682560181406434b22dd0d8694660550deb68f799509e708710ae2c6885778d212eac8e91b241ec0441a8d4788141d9551786d417a752984952f8ea5ae008a124237ca0c46a17354a5cf682410aa2d1f2462f6b182519a5d4ae82b24e3e673821b060fc4ec04a9b3d22ec948405a06d05e8fc6087143da293aebc8a78953b86a0088535ec86935196556279731e318293c7d1173f25404a1dd2665c4cfa6155e6488915f1647c8aba2d428bf044108032061608c342c2395d9453281f4e1a7e0b67941603847292d871bb31c9c86b8b90d04045c2581027c0280292807403831425a871569531da9709401c2e8755158463966e5041413300846f84234487d3299b54c3783312a1ce6f521906414268a52770c4b9cad17f58481cbeb0753a9cd2b30338caf8291ee2444797102e4248bd7091f1e41dc6689c08a490f6255108174260b4318461548a01489b12e814160a6405b0553e0e8ab26b0722a0b4ad83e22ccaf2634cc56c2f1e21845f961a96256878d18ce22c7e80ba5a2ce2a8e3a7a19e905678b54485802ca80192160449b705a010102204c82b0720d539e05547a3a30e228db24a3ee1e89f8a5468454ae1485f241cce9e70545992dab5218414459865fc12c4b2ee3b689475ad62d6864982542da5b03c30c5caafc288280783110aa2c2b0ba513aa20dc248a90ee5a6a18ff0135fa5103a9fc5104e5841c147e0c8071826042fc20810460844b99313be185742283325dd868f30ec468c523749a9f0c23004208c5299ad338120909b86227fd428544a04d16624462a7ecc4a383909e50597932eaa97d01645411ca48c82f07455990e476015060984f0a60761540cab908e1880104f0822bd5383a0de11d4ce7689b16e5244bc889934dabb15c10926e4e83f9651b6724880d427a29c74b170da48d1325e24cc6c72adc5903e4f02a406a9bd5092013219c6e8dc3faa1d448fb35295cb51a63bc8885b80d0ae6e8c78b1380a052405c18aa10801a426a5bd6912e3563197d84e056ab93100f5943dd292320e40dd892df0d43681314309aa30fc0794c068038a685504649381d00ec249c031630b6565a8e1ec46c0313e14c8cd288f8358761562f8118861589901c218d07003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked695 : walk cp695 moves695 = last695 := by decide +kernel
theorem result695 : ValidCode last695 ∧ ∀ i, 695 ≤ i → i < 795 → P i := by
  have h := walk_sound moves695 val695 (by decide) (by decide) (by rw [checked695]; rfl)
  rw [checked695] at h
  exact h
def cp795 := last695
theorem val795 : ValidCode cp795 := result695.1
def moves795 : List Move := [⟨[104,333,195,195,159,219,104],[104],[207,17,443,113]⟩,⟨[],[367],[206,436,118,696]⟩,⟨[22,496,54,557,375,534,158,143,339,22],[702,490],[477,401,333,659]⟩,⟨[],[769,99,123],[336,348,658]⟩,⟨[],[464,438],[419,749,99,557]⟩,⟨[],[83],[480,214,584]⟩,⟨[736,705,705,544,75,79,771,35,764,759,238,223],[54,446],[421,613,121]⟩,⟨[],[297,565],[54]⟩,⟨[],[486,766],[791,669,743]⟩,⟨[],[1,703],[144,22,196]⟩,⟨[],[196],[31,383,255,1]⟩,⟨[],[735,747],[504,680,524,294]⟩,⟨[434,556,274,336,363,372,759,205,506],[270,80],[585,515,795]⟩,⟨[],[1,89],[102,530,596,276]⟩,⟨[],[308,6],[107,211,1]⟩,⟨[50,750,339,743,325,453,50],[615,751],[378,404,242]⟩,⟨[],[246,260],[263,649]⟩,⟨[574,369,369,574],[1],[104,706,62,524]⟩,⟨[],[522,174],[653,319,1]⟩,⟨[707,661,593,493,493,264,339,596,695],[553,109,693],[264,124,590]⟩,⟨[],[608,266,216],[11,17,1,9]⟩,⟨[],[191],[252,232,414]⟩,⟨[],[414,226],[383,291,191]⟩,⟨[],[269,95,111],[346,288,572]⟩,⟨[],[786,672,810],[287,535,139,673]⟩,⟨[],[1,797],[282,766,264]⟩,⟨[],[716,484,24],[603,343,221,1]⟩,⟨[],[123,189],[128,36]⟩,⟨[477,336,336,367,367,121,121,477],[36,700,660],[739,123]⟩,⟨[],[1,331,729],[638,412,238,696]⟩,⟨[],[122,564],[535,803,283,1]⟩,⟨[152,24,143,615,674,40,289,278,144,144,461,703],[69],[768,644,190]⟩,⟨[],[14,376],[625,265,661]⟩,⟨[481,379,672,770,632,636],[405,423],[728,746,238,14]⟩,⟨[],[520,528],[125,273,329]⟩,⟨[329,564,399,667,264,140,716,158,614,661],[653,745,253],[804,318,674]⟩,⟨[],[708,814,780],[173,51,631]⟩,⟨[],[],[752,80,326]⟩,⟨[],[540,102,112],[629,13,667,823]⟩,⟨[481,313,313,481],[291,443],[74,392,316,384]⟩,⟨[],[826,488],[677,411,601]⟩,⟨[],[337,659],[56,196,626]⟩,⟨[],[],[185,281,439,703]⟩,⟨[],[693,147,459],[678,112,452]⟩,⟨[],[206,214],[837,765,639]⟩,⟨[],[639],[440,450,206]⟩,⟨[],[410],[237,629,789]⟩,⟨[821,41,782,473,555,752,265,518,81,61],[3,723,463],[538,820,536]⟩,⟨[],[692,568],[451,3]⟩,⟨[],[585,399],[626,120,694]⟩,⟨[],[88,414],[103,311,685]⟩,⟨[],[407,57,285],[348,646,316]⟩,⟨[],[146,320],[181,57,653]⟩,⟨[],[349,359],[392,368,728]⟩,⟨[67,338,720,584,821,118,730,269,67],[416],[221,413,695]⟩,⟨[],[823,591,95],[500,610,64,802]⟩,⟨[],[280,30],[155,171,353]⟩,⟨[810,739,326,326,428,194,512,194,728,228],[319,553],[732,538,212,296]⟩,⟨[273,463,335,335,463,273],[48,454,418],[155,43,349]⟩,⟨[3,205,666,833,85,335,149,254,825,539,135,806,3],[501,443],[348,690,64]⟩,⟨[],[148],[589,665,491]⟩,⟨[],[1,343],[496,64,430]⟩,⟨[],[236,500],[837,819,1]⟩,⟨[],[1,479],[164,660,702,828]⟩,⟨[],[340,542,554],[693,421,827,1]⟩,⟨[221,231,128,832,832,128,351,837,456,456,221],[391],[124,642,122,848]⟩,⟨[],[512,376],[669,189,367]⟩,⟨[615,680,684,748,748,500,787,746],[367,207],[704,742]⟩,⟨[],[616,14],[689,223,99]⟩,⟨[],[609,763],[696,20,748]⟩,⟨[],[636],[259,251,267]⟩,⟨[],[1,483,497],[396,658,362]⟩,⟨[488,32,477,265,467,16,533,270],[810,678,804],[669,1]⟩,⟨[],[257],[560,66]⟩,⟨[239,371,693,239],[812],[807,687,713,355]⟩,⟨[],[703,581],[204,588,542]⟩,⟨[],[66,510],[201,639,187,757]⟩,⟨[],[105,765],[860,796,66]⟩,⟨[],[66,338],[535,653,769,105]⟩,⟨[],[209,117],[278,42,134,158]⟩,⟨[],[34,482],[471,571,339]⟩,⟨[],[747,429],[582,122,10,852]⟩,⟨[],[552,250],[803,725,681]⟩,⟨[],[681],[474,322,422]⟩,⟨[],[516,664,714],[533,599,689]⟩,⟨[],[497,487],[738,588,202,576]⟩,⟨[],[592,126],[507,147,283]⟩,⟨[],[827,551],[146,478]⟩,⟨[643,810,810,643],[148,354,500],[873,645,261,369]⟩,⟨[],[143,79],[152,806,638,84]⟩,⟨[688,94,94,20,551,49,405,352,664],[134,404],[559,851,267]⟩,⟨[292,276,685,634,156,263,223],[279,575],[500,354,134]⟩,⟨[],[672,90],[573,145,873]⟩,⟨[509,153,864,350,576,757],[629,139,289],[236,810,118,630]⟩,⟨[],[630,538,102],[749,173,837]⟩,⟨[282,745,375,424,17,719,719,437,702],[837,703,319],[410,816]⟩,⟨[],[522,296,16],[57,469,787,685]⟩,⟨[58,880,291,429,295,481,185,588,58],[215,355],[370,366,412,676]⟩,⟨[],[676,740,96],[225,631,345]⟩,⟨[],[777,369,5],[174,344,156]⟩]
def last795 : PathCode := ⟨895,0xd8683c1888549a10c56a96c94b5b0cc40ceb1eb64a17c6137f00a8304c278530b0461a1611caeca292c0c805547a3a30ebf52e3481f20a10c2b1320385701614c01e54b9ed16e8899b88a36cd68151e733acb00e88c66ad70b696c0f0505041086f865156a1c25ac50381a11a0ad01280c59a1f07695307ad1c7d1176da571941193eed886f9c5098ce0449b705a010101c41c0c811c86b16c88d9b1934da750082304225cc989df6f411d9eb031fa50d20acf16a890b03246382948a2355b65986d06a54c379719e633c9895721b1eac2c1f20214431d24ac75245b89b1da44c48c4b2ee3b689475859110ce55c2ec6a82b09c3095d08a150a6f4b48a80b36e344788b38aa38e9e867b720241f98304339c7cd270566d6254a7af23ae8a43d8ee6a6bb489a365269f4c1b01280741a00441ba19ca90920dca89138e96b02a18c8304e85357a0901b2660f62dd0d8694660550deb68f7b21470a44d80f4618b94158d5408600488183f2c5d949a00320e01618d3783a14e2bd2084f03e9c34fcdcc272fb552460c61f86c227c4133f56425d06abc30a3b0668776945fd610ff2e4079b316344207d5d2ea04c2ec2292463aa1cfe8dc3905217c90721481869a3d28eae42b80d678d54ba1d54561192f3466965f961b7d00e5894f0ab272a20fe35d6689c01a0ad5ae008a124259c4c8438e238413ccaa2c1c8a80f20c04a0151429ff6223bcc130267c20c2f15b4cc98d7b0536629cd4eb07084d085f086676d58dd18f302b017211c3107051f83201ca5895a1e3463383b1ca5fea95a617d588930ba81b0124eda48f80100a46b8b93708253db76096bf8c308b20a911663743ca16c872b33a25e064149250b6038b503802c5a78f223eb8517b2a2b4b9c3120f364d78931b311a85cd512f222cc0f0031630b6565a8e1ec46cc49fb62acac8b1fa02e1342e3651362a4b41a86d0070faad46d8250ee9332e267d30aaf3244485393d1a8440e48db2ca1fc9d13769aa901a9dc5509a0ec9e84b23c1a88af1749591721335c18d072334a26bc0505a4949fc652f73a44f8532de6260d9a72a33c2de13ca0b2f265d552fa39ed04402905928018829458a5f0aeb272346291ba4d4f8610aa83b40a8f146a8318c3cc172e223cc8c308e31ac24d7890f664afc62a842006909a8844aac107e21445a55cf90b22beda8d316a4ae6a5b38992409911016421addccc9776a481c8486056064579a1d4ce4744e36465a9dca509a414419219fe026558a718b37c7195f0523dc4881124f182c01082314a66b5b189d04e1a4938bd5186d41787a614a693b14b6fc01935839260864b5ad6074a7d828fb512901008a30ba6d16804002256174b080822fc42a8b47c918bdac6094ce95ba124e4638ddb0e496d6434101170360e61440eac3c78a1f042bbc6932e6240dc392324a43dd6500f6ea550a8379016a64580144ba9b0368742e0124cda655561958f9f1166578a30cb48a4fda2a5f24a5313aa9b3d2dc0acaa74d2bc0a89bf504c89b7ad15a6a198f1ab25cb48b790248e5e81f92a1ce6f45a29546845575a6e3a65d94531a64c08d5b10b5eabf1a20bc4a86b0ec2ac5f0145999964d4868d3b690b0325403710a07c040a584e20ccef37b62c3a9ab9b93967d8570731a2cbccd1ea5be4842419c148280123602d2c6c72adc59092140a03142d7cd888f0343987f34339a7d16aa3b13cb98f1801,0x4f1ae613c8ed6a9f439ad0c7f0e603423cd8b5f14280d40a48590b7072b1b2d2d80120a0148670241215be7a8cd32f1a21cc571f63966e5ab8ea62cdecef0334e2960409f00a0dc5400c90b0da4d3a1a4d4659998515f0ab0ec1ac4a82f1a22fc5ea42d5b02364cc69451763a69b975915468a545a1bd1ce4a81f97a48e408b7ad225c6ad8f2865a6b45b7b225046fca8af04d2a9cacb703d2a6d3a94c24a97da293f48a32ca315e1667c58f865556994cd8492e01d036a6c4ba05058299016de4a81546ea03d650f74a48c839037624cb8692ef04287c78b0f0ea510e60d817040434359496c38dd98e4e48495bb3a094b18bda4647ca2c428bf082c2174958022101681b40ba28d00a405123ed82a9f074b58b5a192600e5358066fc52d3b29a6141e8179b55182f49386904e275b19ad4a68c50830018293c111223dc1495f1c637c62ca71560267f921906414268a527765ad904e11d4ce8757999156018084a076a45dcccb7721a59110264240265b39a94ae5a8d336a2be2c8f915745a8507e3044aa2109a9a4200a1062abf66443d788931ac38c30b2323cb88170f318ca0d46a3c40a0ecaa9844f89351b98a234c9cae97c58aa5188200592a404034139ebe9551972f282d3cb783c2a8da7036626b785313e3a4bdc6527f494168051af4a28cd0706335c84d172561742bda88f04b27a0eca685507701aaa469a4dc9d07f2ca36ce49101a84f453912324abd3099f2e24ccee8946d8b50fa81c6d06a0b40a9136d942e04d02e7e88b32b62a7ecc491b1eca3965ad96300c4f03302224bcd521711a6cc9335e36483c312e72b4ca917ae123e3c9a78b1380d4038ad8250524641783a2acc8705b3cadd16624420a22cc32fe096dd93da093702e46b8290103e1a493b01206cbaa4c5885f5a62a55fe7283b0ce34687895a9601c0c91f9c1310471722c030263cdd3566762185f342084c1d4ea7366214d7b2634cc56c2f08367cc08c10ef6227fd428544a0300f22a01c88b0ca84f3843884393259c908a10025ae2b41a270668d74fe2882722ad4f16200edf56197e696d192f046456754ba3556780342bab928e8f469a0621441d7c948390370fea8763a490228bb04cba95d01f44258db301e2e43fd6117f6941dc668ec30aaf106897564cfc4109f6c27e0c6118552bec273734fc70c3e93c208af54e0e83786341603803268194b173f20604898040835415ae56183d0d8291470c84f7ada0de154661a50d8b74f61981b22417a14d4e80c18c8a86b03a513aa20dc248a90671ba111a01d0280c04c1a7d5268d889aed6a63b83da293aebc8a78956d6159271f339c10d8307e024dc867a7a38e2a8b39e2344db80b22a4b49bd50a285d0c249c0ac6a8bb15c33911016475a253b6bb84b12344c7689b16e524b1d248c71448081f30b1ea86d5726233c799718de54c1a86d1665b68d48a0a5638c90b022416ab3d209431fac0d9e8476f477c989734228c0081d44da64d9b22316c1ad1cb201c07101000405a6dc44b380987146fb623ee4659415c6da45c7d34707a54c7687c59a03012ab41a06843831425a871569946f8421041410f05b0b6b5c66a2300eb2c33a79c1535a36c2299ba2216e7b54b8794c0585700e1320ac50c0281f2d212e2fd30e8e9478150c84b0a2abb11c85861ac15309e04c20c00adfc6105f64a7aceb1030ccd6c94a5b56a4309a2151880f186803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked795 : walk cp795 moves795 = last795 := by decide +kernel
theorem result795 : ValidCode last795 ∧ ∀ i, 795 ≤ i → i < 895 → P i := by
  have h := walk_sound moves795 val795 (by decide) (by decide) (by rw [checked795]; rfl)
  rw [checked795] at h
  exact h
def cp895 := last795
theorem val895 : ValidCode cp895 := result795.1
def moves895 : List Move := [⟨[],[354,458],[249,379,465,659]⟩,⟨[],[891,187,631],[66,100,154,612]⟩,⟨[],[92,744],[189,515,631]⟩,⟨[],[657],[868,522,92]⟩,⟨[],[90,556,532],[453,529,813]⟩,⟨[891,472,462,366,296,323,823,368,856],[543,215],[238,208,474,90]⟩,⟨[],[846,328],[75,819]⟩,⟨[641,373,161,161,690,279,586,586,18,372],[329,189],[114,302]⟩,⟨[],[38,678,256],[895,263]⟩,⟨[],[707,149,371],[166,236,802,38]⟩,⟨[471,471,742,843,576,738],[64,696],[233,799,697]⟩,⟨[],[157,443,113],[674,74,64]⟩,⟨[595,899,364,882,824,213,896,444],[854],[469,671,667]⟩,⟨[348,587,165,701,644,62,251,856],[737,387,57],[780,812,16,754]⟩,⟨[],[546,710],[869,751,347,739]⟩,⟨[],[317,745],[350,122,288]⟩,⟨[],[454,690],[35,267,227]⟩,⟨[],[175,579],[890,584,640]⟩,⟨[148,492,492,148],[626,82],[223,797,861,317]⟩,⟨[],[1,861,291],[656,606,702]⟩,⟨[785,752,579,445,77,634,67,603,365,313,164,350],[692,184],[731,339,715,1]⟩,⟨[667,415,425,205,291,234,527,678,756,270,289,405],[143,555],[234,164,134]⟩,⟨[315,568,295,450,192,722,638],[300],[775,681,197,527]⟩,⟨[296,789,877,340,759,515,11,822,572,857],[67,253,269],[192,134,732,878]⟩,⟨[],[276,468,312],[187,375,67]⟩,⟨[],[687],[412,228,296,878]⟩,⟨[706,384,416,187,185,877,736],[618,42],[587,497,273,349]⟩,⟨[786,530,519,510,103,73,334,660,728,629],[65,899],[588,576,152]⟩,⟨[],[110,438,320],[801,901,65]⟩,⟨[],[219,323],[600,164,824]⟩,⟨[],[240,418],[135,197,347]⟩,⟨[],[347,377,333],[414,200,824]⟩,⟨[],[314,910],[429,813]⟩,⟨[],[591],[48,348,614]⟩,⟨[],[552],[87,691,187]⟩,⟨[],[695,13],[410,284,730,736]⟩,⟨[],[904,780,62],[511,707,697]⟩,⟨[],[503,807],[128,774,832]⟩,⟨[],[688,916],[205,83,431,929]⟩,⟨[],[403,373],[644,498,116,428]⟩,⟨[],[818,66,498],[787,725]⟩,⟨[],[753,533,683],[870,218,66,820]⟩,⟨[],[508,790],[487,239,103,595]⟩,⟨[],[235,901,407],[554,568]⟩,⟨[753,737,478,303,426,777,212,240,631,883,285,91,703],[466,56,798],[147,793,331,649]⟩,⟨[489,885,101,673,364,116,786,806,612,303],[309,483,385],[600,530,240]⟩,⟨[],[926,720],[585,303,507]⟩,⟨[],[243,715],[80,932,148,98]⟩,⟨[],[10,806],[489,325,771,223]⟩,⟨[],[909],[558,94,10]⟩,⟨[692,309,378,809,381,709,147,406,312,223,87,297],[350,596,298],[245,61,417]⟩,⟨[],[325,791],[108,156,664]⟩,⟨[],[104,942,146],[457,725,415]⟩,⟨[145,285,403,435,289,906,468,757,839,145],[485,605],[750,832,710,104]⟩,⟨[416,249,829,829,249,416],[640,8],[127,109,895,371]⟩,⟨[],[93,61,843],[596,420,266]⟩,⟨[],[82,598],[361,53,207]⟩,⟨[91,95,767,855,283,840,12,719,309,275,764],[],[282,922,432]⟩,⟨[],[662,240],[683,179,405]⟩,⟨[],[359,469,565],[650,538,540]⟩,⟨[],[40,124],[557,511,61,573]⟩,⟨[],[887,375],[358,502,40]⟩,⟨[],[],[41,123,955,491]⟩,⟨[],[819,831,95],[790,502,42]⟩,⟨[],[40,728],[245,487,231]⟩,⟨[],[703,109],[350,120,40]⟩,⟨[935,236,236,935],[40,120,898],[423,31,521]⟩,⟨[],[81,551,339],[358,44,474]⟩,⟨[],[492,24,264],[211,99,43]⟩,⟨[],[421,419],[164,36,878,258]⟩,⟨[],[402],[655,713,171,747]⟩,⟨[],[707,709,181],[916,26,582]⟩,⟨[],[944,444],[147,849,257]⟩,⟨[],[431,229],[100,694]⟩,⟨[],[314,662],[251,95,147]⟩,⟨[],[389,601,193],[480,502,784]⟩,⟨[122,749,401,721,512,214,606,122],[486,902],[235,413,675]⟩,⟨[877,671,671,877],[183,447],[948,90,844,134]⟩,⟨[],[878],[3,427,593]⟩,⟨[],[1,905,363],[424,938]⟩,⟨[],[208,602,876],[801,1]⟩,⟨[],[39],[510,156,888,886]⟩,⟨[383,932,582,582,932,383],[886,888],[795,297,39]⟩,⟨[],[613,197,293],[910,264,152,918]⟩,⟨[],[156,264],[181,597,455]⟩,⟨[],[671,409],[284,554,156]⟩,⟨[],[744,732],[465,181,389,305]⟩,⟨[],[891,191],[480,966,890]⟩,⟨[],[890,678],[689,445,281]⟩,⟨[],[89],[388,470,834,334]⟩,⟨[],[448,58],[555,657,39,437]⟩,⟨[],[437,13],[158,626,474]⟩,⟨[515,951,951,515],[50,368,408],[769,219,159]⟩,⟨[805,979,51,409,941,60,965,541,836,986,74,590,347],[21,821],[860,328,466]⟩,⟨[630,67,67,630],[446,162],[891,21]⟩,⟨[],[77,279],[554,476,474,506]⟩,⟨[],[946,948],[461,685,77]⟩,⟨[301,568,981,266,704,739],[39],[972,268,658]⟩,⟨[982,787,787,83,155,972,861,861,674,93],[806,480,448],[487,279,193,39]⟩,⟨[],[1,353,265],[590,104,488,878]⟩]
def last895 : PathCode := ⟨995,0xcb321e346a7855bd90d0aa110aef32a13cf8bb309a95cd4b67132481322202c8435bb9992eed49039090c0c918e3c86e28cd6e86c34a3302a86f5428a07429c07a8d19285f184dfc02a0c1309e08613442a3102eba349c7cce72b6046c998d28a2ec74de88706284b5ce1746aa4bdf08a373ce6d7b34a0ee334a21cc1b02e080970142f8c0eaf35fc048e92f71949fd2535a7144fda2aac3b0e058829416a6f0c6b836c227c4133f56425d06abc7082f4da28d506ef421b060fc96c94b18362a41d80d42207240d8096f6ef8a90ee6a6bb489bb619c26db285c14880164adb62c3a8f7a95168e35d61f83186f47392a35e028c32bb28a4b03201551e8e96b16b4329ad52b4c2fa19c6e8dc3faa1d8e92474aa6d3a94c24a97d7d3974b48a83d30a26ed35520351d86141a270668d74fe2886d269d0d26a32cccc288f318c77819a714b0204f8050280c047fbca4ec52dbf0061b6595d5ae613c8ed6a9f439ad0c7f0e603423dd91f241c32ca315e1662440c1f962eca5dd90e206758f5bb965616464149250d71ee9333ba251b6238522c4d6f0a603cd98b182d36e1690b9aa4ac8b9099ae0c69056797251cb2d6c83762491c813c76e433d5a9cf2f4e58350da4decd40a25d4d855475a5e7c4abd30a2379c0c91f9c15003242c32c33a79c7934f162f4d3699366c9b8a98ed0f8b35e222d238eb5223152deb498fbc517ee09b11f7394d187db0553e7947a3d53089f126a371b2c9cae97c58a6fcc511a0ecf2cc72724247b89102249ee8893a9a6ae6e4e59f615c1495f1c637c62dc2b0c5ca0ac6aa04300e410a0fc608954420407808c508349276e3931841610945d02a01525a0d4368038af5ea13c588930ba9d4678414458566d64659415c768f70e41480e2f407cb480f2e1c7e943682bfdc902f554558099fe6b6f79599d17106211cb201c04119eb0327c34c88b303c07850f8f17260b9e918723a99d0e9a426a42c1c9304a86b062abf66443ddd2d715af5d34997784c886f2a66964e4402591e0d445796200e0a9eb06b3aa8ac230ba2ae535be19455a871129db5dc2593d1c715459cf11a26dc058fd9892363d8270935e29a0ec8385b0a0501b0d0782219cab85d8d5056138590f243c16c7486d5460f80529211e205076e195d2ea04cc8c308e325c6ad8f2865a6b441f8855168f92317b58c1299d3aa5ce5699522f324bc8a78953b89948fae16bea4963a492f0584f421856264070ae06c06c0b022479af0d3ea9346cb69db91214e4f5a38022849096713210ebf5ca1c51bec85683c16f09e5280c03c8234d99266bc6c9078620fe4e8cf9710e63459799a3d4b7c90ba8722c00609e33423415a25c72a71010004700d9196a77294268eb83a40c42883af9730e857815177e8c8390d265c66d749583702e46b8e238445c7d2167b6c257419c0900c5e79414864190539a73e3956e0a86320c13a3cc6da151429ff6223bc08b7378c1ec332e33cc679312ae436898ed1362dc94cd6b6313a09c34a08210be1ccaa72b2dc0f48bb08a8b0721c06a02c1149983d8ee1ec0281388f4a3ab90aeea54b9ed16e8899b88a03e9487baca01edd4aa1506f202d4cba72d2c6d44a40402041182112e64c4efb7a08e1259db563742185f342084c1d4ea7329c30d60a986b292d871bb16cc2c1f20214431d4117e586df5de2356de45575ba62461b406025178111a01d0712add5106e124ebcfaad42da1319c0895f6aa48c3b1120bd1581910a6cc56001944e3a5ac38c0e83d5c798131ebd57e3444c0f80bca0b36c16d3f1c30fa0b122a84200085ef8a5228ed446374598034c188e256a5807182604cf84185e2b6999ed17f58405cfd116556195721a0140091ceaa306cd385915f6d4698b50d675ce2c3ab0f5c447825b764f682404001,0x4042094f6dd82591e5c4c3c3ab8b75c358b51a66d457c5934e06ca8dce82414068172065556458fd0175845fded2662b617841b3e60460807296256238c180d598dd0463b5228295ef821200a112282c0fa70d3f05b36c82cbcbe04c0d117e2f531e605c78f50e8e31ac0e944e065603310a6645582f4120ec48c2a95f62259c04c2dab50fabaf1241b9512b7712741a00441780940606d246e99759156de8d5de37d5865f9410c71448081f30b16c6ed8724b6b2a61608c329c9cd4eb07084d085f086374d599d84908ede8ef9312e68451801040290144b1b2d2e9d4c80b6f2540aa37501eb287ba5203e2299ba2216e7b54bba90aeae4a3a3d1380a1ec3b83d8661148b06a07007222c08a2ecf4b702b2a9dccaf82108203482713ad8cd6a532dc4d8ed226436ab93119e3ccb8c3307b78cdcc088ef6227fd428546daf313a0306322a16e0e573ee6905106486505e7831090671743097b68587d1173843886b8b93705617499b65c3483923277e545783a1730be48390a40c0e8eb89a2949dd96b64700010101c472a9715a0d034278c60b00722ea090adf3d4669978d10e65c4cf93a0fe189079b26bc498d988d3c8301282796f0f05683211be715ca2fd10e4c967242284009a393d14e449dbada46ca4d3ebc379a890b01b06c0b8070990562860f41612f092563a926beb848fa653b8254a7af23248bd9515a5ceea99d04a58c5ed2323e5162141fad15a6a198f1ab25c38c30b2304cba95d3860768151e2480523e1461b57485b03c3c95904e0563545d8ae19c888078c3501a815b00e0eca685e224c270f6236624fd8166dc688f116715471d3d0965dc76d12a1c55a651be14d2ae2e82322b3aa1adeb02a00e58857b511e096440139696a986f32278465d34bd715ab5ddd10f664afc629ac4a84c01c90b26a6910ea6723a61de902e7263c50f9e13c0cc0888d327cc0d9e9041c0c811c98871074559bde6b67f8099565540bdc92ff68250c7eb870f2d207cbd00e2520e43dc768571941196d615845905678750baa4c5884f1ea2bd038da0d4168152a81d025161010531b8e276d2508231780100422556083f10a3903008106a82b5cac31c298b37c7195f05215c7d8e59b96aea6893ba249e088911ee4249c8c73cb0ec468c51bf58a5f0aeb271b28dd26a7c308f547a1e553ec147db463947ddb138217ef158fad22dec55223ad2388b5e22cd0f83b4a9a6e66c64d36bd3162d3c791e733acb02c0c95007051f83279c88d30aaf7c4978759554d89740a3354de368353962f473d5a8cf6e4f1c812476240dd6cacb51c5c967a410c66b909a2e4ac6a90b85a36e0b4b1b6603c2996f3135228e1b60943ba4cdeeb5c25052464059656ee4f59d6206439ddb2962e7e40c091166578a30cb41c7c9d908f0343987f34339a7d16aa3b13cb99d59651b6019bf14b4ecf287fb01280140f80814b09c4199de18c3cc28b3332c9a90d1a76d2a20fe35d6689c01a1851d80d55234d26ec283d22a4b4e5d7d25f24a5313aa9b74a4918ea873fa3706e8672fad3152a6b4325ad6b23a51e0543212c28aaecc300a35e4a8739bd3187e1d638d168a54f78ea62cb6d64a00148171b289b19ced889aed6a63b8a93be6f60240d9c9220351d8290362c6094a5b0fcc1821bbd506a34da0bd708af106897564cfc4109f6c2e0cc69bc16aa51883813b0ab1a293f714d692527f194bdce90125fcbcc0ebe31425c0808b81b0730a20cd0eed297b39b73c28df092f6aa5d1ce12d6281c1e89d32eca298d326046ad8e71f349ce8c2e8c442a4d08627813083002b7f18417d92a3407aa70742285421bc2a8cc34a1b16ea336e2f218e3240c042503b522ee665bb90d2c888132120132d9cd4a5709aeccf884f32abbd10aa80d0f6455a9e346878b3003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked895 : walk cp895 moves895 = last895 := by decide +kernel
theorem result895 : ValidCode last895 ∧ ∀ i, 895 ≤ i → i < 995 → P i := by
  have h := walk_sound moves895 val895 (by decide) (by decide) (by rw [checked895]; rfl)
  rw [checked895] at h
  exact h
def cp995 := last895
theorem val995 : ValidCode cp995 := result895.1
def moves995 : List Move := [⟨[],[294],[193,281,1]⟩,⟨[],[1,281],[44,466,146]⟩,⟨[],[432],[773,257,1]⟩,⟨[],[223,281],[964,630,110,932]⟩,⟨[],[758],[149,995,277]⟩,⟨[],[277],[62,912,672]⟩,⟨[77,305,749,669,443,139,900,741,58,151,170],[390,388,234],[587,391,751]⟩,⟨[],[865,495,413],[812,440,48,814]⟩,⟨[],[98,70],[617,187,827]⟩,⟨[774,195,896,15,485,41,984,622,529,668,644,903,150],[959,243],[248,236,668]⟩,⟨[516,456,374,65,221,678,590],[52],[537,225,313]⟩,⟨[],[327,263],[510,852,680,52]⟩,⟨[],[568],[691,241,765]⟩,⟨[934,877,973,603,556,556,777,777,603,950],[361,763],[742,194,514]⟩,⟨[],[298,688,682],[635,625]⟩,⟨[],[989,577],[298]⟩,⟨[],[508,662],[461,853,607]⟩,⟨[],[93,629],[998,1008,386]⟩,⟨[],[564],[735,945,917,93]⟩,⟨[],[591,877],[434,898,1006]⟩,⟨[],[442,148,254],[865,587,897]⟩,⟨[],[235],[422,446,726]⟩,⟨[],[38,828],[265,463]⟩,⟨[],[879,301,767],[702,688,38]⟩,⟨[],[70,594],[347,753,877]⟩,⟨[1018,490,490,887,887,584,393,458,145,514],[383,355],[692,570,70]⟩,⟨[],[128],[193,463,287]⟩,⟨[],[373,367,585],[226,900,856,128]⟩,⟨[661,955,144,86,882,243,34,813,90,90,152,685,927],[190,952,74],[9,389]⟩,⟨[],[811],[524,126]⟩,⟨[],[276,806,878],[7,689,35,987]⟩,⟨[],[111,125],[402,950,102]⟩,⟨[],[862,326,748],[555,743,481]⟩,⟨[],[805,333],[886,744,546]⟩,⟨[],[252,994,654],[887,619,261]⟩,⟨[],[335,601],[182,146,216]⟩,⟨[729,1004,169,225,245,222,976,362,4,539,539,62,688],[540,406,82],[491,79,229]⟩,⟨[],[181,543],[642,558,644]⟩,⟨[600,10,414,135,188,180,969,875,454,163],[672,488,146],[623,901,761]⟩,⟨[],[651,975,335],[378,116,352,566]⟩,⟨[],[546,690],[771,79,121]⟩,⟨[668,55,55,668],[341,847],[716,454,970,526]⟩,⟨[503,681,652,652,503],[558,82],[173,323,927]⟩,⟨[70,776,775,608,63,790,264,512,504],[821,719],[148,596]⟩,⟨[],[378,40,314],[713,355,869]⟩,⟨[],[869,897],[740,594,596]⟩,⟨[660,660,523,81,593,984,484,511,985,1009],[1032,148],[453,777]⟩,⟨[],[357,263],[310,980,374,172,156]⟩,⟨[],[186,268,412],[67,781,947]⟩,⟨[],[611],[548,538,120,420]⟩,⟨[545,918,556,622,74,765,600,574,920,345,816],[532,552],[627,55,791,283]⟩,⟨[832,693,693,832],[557,807],[974,882,938,918]⟩,⟨[],[918,938],[831,881,379,869]⟩,⟨[362,742,484,97,1,397,266],[177,3],[412,352,292]⟩,⟨[],[792],[75,597]⟩,⟨[],[19,653],[258,342]⟩,⟨[],[384,26],[975,429,19]⟩,⟨[],[591],[296,82,278,478]⟩,⟨[],[112,674],[705,69,535]⟩,⟨[],[875,67,991],[284,694,604,706]⟩,⟨[],[760,444,950],[15,947,825]⟩,⟨[],[235,923],[22,118,338,58]⟩,⟨[127,54,694,342,167,232,696],[718],[349,439,513]⟩,⟨[],[13,61],[810]⟩,⟨[],[780,236,330],[145,349,13]⟩,⟨[],[1,1057],[918,318]⟩,⟨[],[98,902],[319,119,1]⟩,⟨[],[159,1005],[90,896]⟩,⟨[],[110,324],[757,207]⟩,⟨[],[1035],[360,110]⟩,⟨[872,995,995,872],[744,642],[829,297,679]⟩,⟨[592,568,568,592],[309,59,367],[790,42,928]⟩,⟨[],[100],[65,803,457]⟩,⟨[],[93,869],[590,580,474]⟩,⟨[],[942,122],[619,655,93]⟩,⟨[],[305,271],[598,168,450]⟩,⟨[],[810],[609,919,715]⟩,⟨[1,645,463,413,279,1],[781,403],[342,48,244]⟩,⟨[],[448,756],[789,995,603]⟩,⟨[],[235],[800,866,926]⟩,⟨[],[640,970],[109,949]⟩,⟨[569,1053,590,767,936,700,934,569],[55,359],[316,874,544]⟩,⟨[],[226],[47,987,995]⟩,⟨[],[953],[482,1000,662]⟩,⟨[],[848,916,216],[461,651,877]⟩,⟨[],[],[158,122,410]⟩,⟨[],[392,374,240],[769,491,613]⟩,⟨[],[261,231],[948,1038,976]⟩,⟨[],[394,854],[213,593,777]⟩,⟨[],[51,519],[426,360]⟩,⟨[],[],[627,51]⟩,⟨[],[941,399],[346,456]⟩,⟨[],[618,726],[759,465,467]⟩,⟨[945,940,393,402,505,661,398],[219],[770,710,606]⟩,⟨[],[64],[259,737,415]⟩,⟨[],[359,657],[1064,492,64]⟩,⟨[783,663,841,51,198,359,791,1071,180],[878,680],[791,749,643]⟩,⟨[1,807,670,966,443,619,1],[659,29],[444,118,158,294]⟩,⟨[],[262,278],[849,981,135]⟩,⟨[],[751,823,309],[410,204,360,520]⟩]
def last995 : PathCode := ⟨1095,0xda31ca46cb69db91214ee69fb3f353c68d0f16663cb4d433ba5ae2b5eba6932ef09911ee24408927ba224ea69abc392406e4e584617455c1c9304a8fb1fec4753a9cca70c3582a61acc3709a95e1d206586cb8cdc093d0861589901c30bd08a30020fc1282796f0f0568040702c414a0b5208cf58193e716eb849af14d0660f636d799075b9bc60f6199718de54cd2d071f2764cc95f8c58088f10283b25c6ae233a349c7cce72b63166f8e32be306238ab2aa43e7860832962e7e40c0914fe929ad38a27ed15fa0d54090f06a110022ce044afb552461d8b3380d0f9010a218ece55c42c6c8cb53b94a13475c813c76e5078559955de5481f30b16c6ed8724b3ecfed4b27a12cbb8eda250987146fb2114068172065056b94f23c0462840d8a907607d0e6b431fc39895be51c88b0228bb3d2dc11a40c708af0c28344e0a81d02516104e4402591e0d4457c1a1ec3b9a9aed226ed86709b5d209c1e9a74349a8cb40e506ef421c41806435bb84a12e6a5b3b7d7788d437855198694364183b2401422450581f6038c20bec94f59d620643a0138e276d252d929630de53c10c26885447bf5736e7851be125ed561dafe5e6075f18a133e4e83f86241e8c9df9515e0e85f785215c42c8320a7ce065138e96b0e303a06d246e9975bf91a0ad152c3f4a43de0cacb5b20dc469b324cd78d928f47443d00ac83789118ac24300e410a0fc6082f4da28d598dd0463b5228ff1743098605d146405078c3501c3d008080a48c80b2caddcb806227fd428547dabdce93d230e47533c2a42cf6c9a9a46d8250eeb7c328ab50e0882630a0e49471940d9a70b22be5e9cb06a1b49bd9a8144ba9b0aabbb10d10d7b34a07405d6117f7b4998ad80e304c099f0830bc06e1326b4325ad6b2ce484509a10be1f6c15058997d60552e3953881f2042385b00e004119550e61fc0d165e668f52df14a07e111cf21441d7cc40752a5cf68b744458a210427fe4446996d5a87d5d78920dca895bb893a0d00220bc04a1aceaa2b2b2a9df52fa72e9691507a614019bf14b4ecf287fb01870360e64256d6c9811a814906e0ac4017d0ea090b2047271c551673c4689b73cb0ec50c7eb870f302ccc9776a481c84968153081e48782d8e90da8ef842f218e32413ad8cd6a532dc4d8ed226436ab93119e3cc168db82d2c6d980f0a68463b4a9a6e66c64cdb3135bc9ed04b077bad721a09505e185918265d4ae9c33b33e213c20928862261060052c8d942e0687b24dda6aa406a3b07c0c10c01259db56374b299395d2f8b145fbc563eb48b7a9117040471be60b69f8e18211802112a81c0ba311601400a07c0409bf314469b51a62d435825b76636a252014470ac321689c050f61dc0096f6efa159797c0981a22fc5eae7096b145ba8cdb881358c5ee148e737a630fc3ac71a2d14a9ef1d4c596dac94002918ea873fa3706e8672fad307ab8f30263d9d3aa5ce5699522f324bc8a7c0a7beac99f88213ed85c198d82e8a458391600f90e0350682bfdc92124e463a0b3d34dabb1aa0ac2701619640d0ee334b98710a6645582f4120cc467ab5048e7551bee1b6595d5ae613c8ed6ac0f5045f80913284e068951af0146195d945258191ae9fc510da5944116fec4923a3d768035323dc390520ae1156de3483941286497c9294c4eaa6dd292486a0307a1e553efc88f2e261e1d4ce048062f3ca0a433fcd6def2b33a2e20c42b90ae2299b94d4e8cc0f022034278d0e8875fae51561d8359114fd816054f5a0982e7263c60fb1a5145d8e9bd10e1051ea9844f8820840b169e3c8f399d08ede8efa217a03e5a43f101edd4aa1506687720abd457aa7074228542e7c72adc150c6418160360d81700698366240393d838891e6bc34faa4dff0cb28c1ccb8c3341a4f16224c2ea7519e10511615a172632bc2cd6883f10aa2d1f2467f4458fd3f7732be0288f318c77819a714b06a1b41612f092563a926beb848fa655563651ba4d88900064a803828fc193ce44698557be24bc3ac3f3061f445ce10e21ae2e5a3802704d88fbbad2388b5e22cd266a38b92cf48218cd721345c958d521705246c27436016a65d39692e0fa470001,0x4703e92e05a5d3a990170d82711b05285cd525645c84cd7063482b3cb928e266b35e222d238eb4fbb62704009a38b91ae388e11171f4c183f0eb4bcf8957a61446f381923f382a0064c008889351b8d95569948fae16bea4963a492f0585b41a84b09c4199de18c3cc28af8732fdcfd1167f49191f28b10a0fd688b32bc98e170561164159e1d42ea9316213c41b0ccb887328c32dff2934faf0de6a248384f4039898361a57036036058018319150b7072b9f5428a07429c57af520a9dc668540aa37501efc5a40f97a0884efb7a08e674f38f269e2c4842084f8611eac140e0f44e9976514c6a0f8f17260ba09bd6054058fdc45358761563945fa21d0e9e3342880f03304e85359b88a0aeae4c43883a2acdef35b3fc90ca0bcf062120ce07561eb888f3f253e7947a00c86a491d2a9b4ea53092a5f865048390d26de454ae148390f713200d7688f523b126ff045943695107f1ae8642585155d9860146bc9501a84e4c80917e50503d6aa3b13cb99d59651b6fb951b9d048ad467b31120bd1581910a61c4b98cd0ef035960582702b1aa2ec4daf4e0b18e4e4849c92ff682d40e03e4600e445822982e635c1b6113e2099fab27bf028a7af23248bd9515a5ceea99d18f302e3c7ab4c2fa19c6e8dc3faa1d8e8a4400b256db161d47bd4a8b471aeb0fc18c37a39e1497b58c04db8a335bac5096b9c5eabf1a22607c05e615bbe6f6025dc3d805027216b0c70a51120289636dd8258d62d4699b511a3146fc409f00a0501600c40ba0712a884180084e1a7e0b6f9871901170a44b7ad263ef145fac52f857593aca374d599d8490c03047c0ec06aa91a69377b21a02e3652c8015060988624a02084f3e2ecdc32ba5d40999186105e2561a35c7bac1d04a7b5bcc4cdb19366c9b8a98ed8462980f3662c60b4db85a3cc679312ae436898ed1362dc94cd6b6313ac918e3c88423bcdaba42d81e1e4c201525a084a076a45dcccc0b0f2e1c7e9430ecf2db71a23c459c551c7472c8090ba87d1004ac1b8490a0411b266d7094e60d8870c047fbca4ec52dbf0066141e91525a72ebe9f52a72b28acea86b04a2f0223403a0e255baa20dc249d79f55a85b4699117fe10a211624442dcf6a977531017c90721473e1101f14ab7cf519a65e345fc398550464040385b08e20407c388e552e0157d626505b051f62f9a1142484b396b16b4329ae1301b0bc20d9f302304038ada667b45fd61017074d297b44310ceecaaa6c4ba0519aa6f1b41a9cb17a2be2c9a703619451ce4c282622210e2ad328df0ee8946d86909abdb42d0a93391d30ef48e92f77da151429ff622e01dcb2b0b2320a48200090f501b0d07901546174860c25743fc228ed446374598a34da0bd6083f10a3903010918aa44378b210090f474a3cd935e24c6cc468375b2b2e0c8f74a50fd52ab41a0fe575ba62461b43a38c6b03a5138197ce8288310b15c149f7ba15e0545dfa3241e1883f93a33e285f181d5e6bfa1db5525ef8451b9e736fd447a152684313c3796304a52db49276e3a0110e206758f5b250be30a0387d058915421003b3060361a519815437a35778df5b39a912e129bb90d80710421bbd507038cb26a43469c1e8275d226c673b6226bb5a98ee1ed06857b511e096440139610945d02a04e00d0c2abc7090311a3703d22ec22a2c1c8f94958e61fcd0ce69f4760a40d8a10462f00f22e5056195721a0140c846f9c5098894edaee12c9e94b3fb3ec92d871bb16cc2c1f1525de65455c1e6e4f1c811d71345293bb2d6c90b15c33918e2890143e80cccdd8918552bec44b380224406a43c408355fa34527ee29ad24a4fe2440c1f962eca6081e143eaa8ab08e306af8e31be316ad8e71f349ce8e231ab25c0ed02a3c8083155fb327647c90734b54c379718660f6f19b9c1d798db4f61984d0bc449bae7164f981b3d2082d54a310702101683c16f09e5283f00208c108c2f1c264158a183d1024cdb2e58681a1d25709b0ddaca9858230ca727353b11dfebec4a84c01c957174118e59b92410e5aba9a24ee89278222447b9913c232e9a5eb8ad5aeee9432d363c5990f1a353cfcdfb39a14e449dbada46c729a3003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked995 : walk cp995 moves995 = last995 := by decide +kernel
theorem result995 : ValidCode last995 ∧ ∀ i, 995 ≤ i → i < 1095 → P i := by
  have h := walk_sound moves995 val995 (by decide) (by decide) (by rw [checked995]; rfl)
  rw [checked995] at h
  exact h
def cp1095 := last995
theorem val1095 : ValidCode cp1095 := result995.1
def moves1095 : List Move := [⟨[],[738,696],[579,327,353]⟩,⟨[],[967,667,33],[568,424,1040]⟩,⟨[440,333,37,990,1028,144],[854],[301,927,37]⟩,⟨[],[291,79],[532,946,378]⟩,⟨[],[378,234],[587]⟩,⟨[],[371,107,137],[520,126,374]⟩,⟨[],[1026],[811,257,263,655]⟩,⟨[],[147,795],[760,384]⟩,⟨[217,982,1048,830,594,327,531,882,836,500,249,655,217],[954,84],[485,1087,549]⟩,⟨[],[675],[486,84,956]⟩,⟨[],[244,842],[115,1067,349]⟩,⟨[],[239,315,187],[248,176,666]⟩,⟨[],[658,960,616],[1051,981,629]⟩,⟨[],[695,1021],[786,826]⟩,⟨[286,1042,1088,486,711,966,504,843,513,74,896],[10,882],[449,317,737]⟩,⟨[],[1107,591],[336,10]⟩,⟨[],[44,124],[633,637,347]⟩,⟨[1042,193,816,46,464,165,299,444,545,915],[791,513],[1090,1008,44]⟩,⟨[],[680],[497,743,323]⟩,⟨[],[591,1097,147],[66,64,748]⟩,⟨[832,479,621,586,898,389,929,249,229,101,653,458],[526,1084],[883,561,985]⟩,⟨[123,160,856,856,160,993,827,123],[123,511],[928,720,476,670]⟩,⟨[987,644,945,924,292,7,985,975,917,596,488],[1004,196],[55,27,1,769]⟩,⟨[],[881,549],[300,318,620,1004]⟩,⟨[],[1008,632],[963,663,827,979]⟩,⟨[],[93],[96,248,458]⟩,⟨[],[814,1076,404],[299,385,429,93]⟩,⟨[],[109,677,839],[1040,934,932]⟩,⟨[],[1098,658],[1097,331,109]⟩,⟨[],[941,753],[310,808,958]⟩,⟨[],[984,764],[657,499]⟩,⟨[],[1,143],[930,888]⟩,⟨[],[286,1016],[859,163,1]⟩,⟨[],[537],[620,124]⟩,⟨[127,63,720,1081,293,884,637],[162,78,418],[589,43,173,89]⟩,⟨[],[355,161],[164,684,912]⟩,⟨[],[434,872,502],[415,1037,359]⟩,⟨[248,653,58,907,127,453,490,618,517,1050,1054,161],[675,767],[252,176,610,372]⟩,⟨[787,1004,515,875,544,886,535,403,873,50,498],[1052,612],[207,893,643,187]⟩,⟨[],[87,217,381],[754,322]⟩,⟨[],[116,952],[421,573,23,1071]⟩,⟨[],[1,881,907],[504,1018,94]⟩,⟨[],[210,422],[343,315,1]⟩,⟨[],[245,525,913],[902,1014,454]⟩,⟨[],[1126,544,1000],[707,205,1099]⟩,⟨[],[1095],[396,386,778]⟩,⟨[],[408,718],[633,747,829]⟩,⟨[],[103,575],[1138,838,1008,1050]⟩,⟨[],[126,468],[189,617,487,103]⟩,⟨[],[219],[310,410,242]⟩,⟨[],[706],[1091,413,219]⟩,⟨[],[1,475],[492,842,652]⟩,⟨[209,446,807,470,582,582,690,526,362,599,802,209],[184,432,282],[625,1005,1]⟩,⟨[804,155,827,461,39,33,506,649,846,1140,228,609,930],[351,519],[250,358,966]⟩,⟨[],[970],[511,927,459]⟩,⟨[],[177,721],[284,260,384]⟩,⟨[],[556,130],[491,523,1135]⟩,⟨[288,274,999,1135,209,255,831,204,955,432],[115],[824,88,990]⟩,⟨[],[132,84],[537,673,1105]⟩,⟨[],[399,723,379],[1100,312,844]⟩,⟨[],[232,690,574],[771,737,891]⟩,⟨[],[855,251],[250,252,232]⟩,⟨[1,72,592,592,895,1075,498,1],[70],[379,619,431,711]⟩,⟨[],[59,527],[52,362,848]⟩,⟨[],[62,494],[741,1099]⟩,⟨[405,405,362,924,879,209,890,655,1030,301,689],[653],[418,918,62]⟩,⟨[],[116,1076],[973,733,69]⟩,⟨[],[723,619],[750,976,902]⟩,⟨[],[282,778],[655,649,13,587]⟩,⟨[],[913,35],[470,1118,342]⟩,⟨[1107,723,723,671,178,262,996,970,998,596,685,901],[120,630],[11,863,297]⟩,⟨[],[861,1071],[228,1156,904]⟩,⟨[],[148,234,948],[611,1159]⟩,⟨[656,544,363,387,548,1118,722,636],[123,19],[6,290,328]⟩,⟨[],[568],[77,943,977]⟩,⟨[],[587,461],[530,1148]⟩,⟨[],[690,896],[301,213,569]⟩,⟨[],[1,183],[796,34]⟩,⟨[],[366,1038],[363,769,1]⟩,⟨[],[295,459,693],[814,566]⟩,⟨[],[62,102,340],[1027,1011,335]⟩,⟨[1099,492,164,212,626,185,744],[447,835],[842,922,62]⟩,⟨[],[932,924],[519,1049,905]⟩,⟨[713,830,853,1028,1028,655,835,146,160,907],[429,919],[766,388,834,654]⟩,⟨[],[52,948],[1061,1101,821,273]⟩,⟨[],[273,485],[572,52]⟩,⟨[436,90,839,114,114,652,714,789,1073],[486,184,718],[1161,133,91,269]⟩,⟨[],[959,249,905],[128,254,806,182]⟩,⟨[],[1066,308],[203,541,1061]⟩,⟨[],[279,33],[506,446,456]⟩,⟨[],[496,10],[193,459,543]⟩,⟨[],[973],[404,826]⟩,⟨[711,503,503,711],[826,632,828],[825,479,1049]⟩,⟨[],[1065,243],[118,606,552]⟩,⟨[],[1148,1138],[1173,723,719,883]⟩,⟨[289,42,42,289],[289],[704,10,614]⟩,⟨[],[1080,470,618],[553,1189,703]⟩,⟨[106,78,681,258,172,623],[325,465,357],[294,1162,622,1006]⟩,⟨[501,504,504,501,79,356,356,260,969,281,830,115,79],[472,582],[311,25,427]⟩,⟨[],[843,733],[1078,1176,186]⟩]
def last1095 : PathCode := ⟨1195,0xcb313e7161d4ce048062f3e0d06a94c8f9694673b2aac6cbab2ca36e3f1733ac7ad9285f56264070c2f4228c0080306326c1b02e00d31816cacb8323dd2943f54aad218210200a109eb8c6b03a613c7a57ecc9d91f241d20c6b04b5fce4dd301b0bc20e46b5c86904194b173f206048a7f1940d8c188e2accb961a4d46e726141311101e1e4c201525a1f880f0148d96d3b72241f98329e7e6fd9cd0a7394bfdc92124e46399db56374b299395d2f8735a1c4d186b054c3591d00e4ab8ba2546bdb0860362b4d433ba33e0681bc928dcc88f712204493dd109f104cfce8ab37bd199c1c0d0ee3353e1847ab050383d13a69b975ca57f8ba1849388d8df5de2350de154661a50d9061144694f682483af902f1b53ba9974e5a4b83e91c0e90b62188f2f2d6317b8531e13625d028cd486038922ecdc314379af0d3ea937fd28cce9e71e4d3c58908410c209c80b6f29e1960581d88920e2c83789118ac24300e410a2fc928441dcb2b0b26e2440d165e668f52df14a07e111cf2140ea47bb5118075f18a110096645c167a71c58fbc517eb15e60fd1ce6f58638528890144b1b6ec2282bab9120bd1581910a62b5ebb6290e6e4e58461fc39895be51c863416245128db0d21352162b80b2fa7d4a9caca2b78cdcd8f41b1ead30be83c80aa322c3ec4a84c0ba47d78e774039897a03e5a425c86a0307a1e53b8bb4cbbc218501c3ec4c73aa8df720391d04deb02a8b4cd8c9a6d66f166241a912e129bbb6d846c5875127534d5e1cc680c2abdf125e1d70963e128862261060052c9101d4a973da2dc811d71345287b4630ccb8d8724b3ecfed4b27a12cbb8eda25098b123aa1c55a651be14d4e8cc0f01e11f0945d04a468a4fe32ad42da34d3b3ca1fec061c0d8398d11303e02f30ae3b0e32022e250c5f66233e450860f48a8ad3ff085108b12228de168db82d2c6d980f0a65bcc4cdb28b80cccdd89187f0d0627bf55df129cf8e55b82a060b806227fd42854279074c3a3a9543e88b9c21c435c5cb478929214082332d16c372a23c459c551c757a94cb72167b63b9a9c3d008080ccc0b0f2e1daec8c4b09c63997e50503d6aa3b8ac0b83d8157d626505b051f62f9a107f0c483d193bf18b12dcf39b37d20a0fb1a5145da170561170f9010a218ece55c3d90d0171b2c84240d92163bd087105d43e88b8cd0a81548a1145cc2a8232b9dd533a31e605c787153efc88f43b6aa4bdf08a31da54ca8c5389c90cff35b05285cd525645c749e94722fef693321e3472757990d806f982d95e4c7205b41a8930a85a81c07c80712a884180d00221fc510da5944116fec4923a3d76803581b3d2082d54a310702520e41112c0c918e3c88423bcdac3c1a8255b5b264fc70ce098871118457b511e0880d0c9f694bda2184109e504683f972e969378da86c139612e28aea34da0bd608e35d61f8318e12062346e07a654291470b61663742aaeee44b077ba19096145576618c51bf1027c0281405803102e9e365a451763541591924e34d549254ae1156de3483941286497c92c7f574ba81332359c908a14174522c1c8b00920584bc24958ea49afae123e995323dc56a091400c9801110429ec248e954da7529856200840022ce044afb552661342f1126eba4b15b01c6098133e8a48fc328bc8a8e54e207c8112657bbed408355fa24c88a6b0ec2ac728bf443a1d7a90556797251d2ad1cb20242a813803430aaf0641495f0e65a5aa61bc41a4f1a26dca0c4690321d009c713b69296c94b1848218cd721368c0f8a92ae4c4678f33be90cc289b93a494d69c507606677a312d7004e095f1c63f6919fd1163f4fdc04bb87b00a04e42d8e8dd4cdc093d12a5483b03e8471168136e28cd6eb1425ae717ac9b21281da917741b0ccb893359af1240049010a703a06d246985118b6056b94f23c04621cc0337e2967146fb211406817230d2688544783505f268fbbad92f029efab204f288a78f1366499af1b251f1545d845458654f7a95168b41e0b784f29401096f2d4699b511a4d4868d393202443d00bf00a23cc6337b29c9cd4ec477fa44ddb0ce136ba6538b22be5ea3bb7283c2adcb2aa43e149f7ba15e1280f88b35a20fc82b3c3a80f60223c40a0ec971ab88ce8d271f339cad8c5bce06411dbd1df4431c0e838956e249d79f52362797330b90a6ed0343a4ae1361bc6a44e065f3a0a0ce3746e1fd50ec7452200592b6e2f1461965d47e45d28e275b19ad9270396b16b4329ae1347b4d286c1286b3ab1ad131da26cd397919245eca9b391d4cf0a987801,0x587c2a4ce475b3b2a45e6497934e26c7691346b3aa1ac12a1b4d31ee1326b4325ad6b40e9266b5b189d28f1747e17519651a2f2db5928005231d50e7f46e0dd0ce829f381944f1aa1b84d4af0e9031bb90ac2d7309e2367d5d789256ee24e847044277dbd047064f38c5ab639c7cd273a388c6ac9703b40a8f20203d3a8cf08283f5a22ccf8ca05e0e85f785243eaa9cb0ab83cdca3b97a2be2ca53ae9136339db1137fb11d4ea7329cdec630f30a2fc10090f0244c8d3a1a4d4469b51a62d45bc10a504f2de1e0ad0168a54f79954581145dc5551e6c9af1263663c4a7ca204eac9efc0a92eeb4fbc9a05e0d447a15268c35721a0140c846f9c5296df803073462f00f22e50562d911a612461b43a29c010126403c459a4ccb8c3341a5dda920721326d7ab9c25ac516ea336e204d1691c3e8ec1484a93d1024cdb758e90b44e0287b0ee004bf73f4459fd2463f67195f382004b5e311de0661d9c535a4944e89bb0a90cef8f319e4c4ab8a903e68c84cd7063482c6094a5b6924edc740221c40c46a836dc68a4f1061bca99a5b995f0524642bc30a0d1382a0242c811ccab51c5c967c157a887443afd728ab0ec1ac88a931fa0d5408fb57bc998101f0e23958a82f032a3f8a4cf98118201c56e4b3ae126bc534198552bec44b38022102009582989d54dba52487b042c448003254002456af713226523eb85afa9258e924bc161920c01c88b045305ca124259cc8c132ea5751fc92a5f865048390d26de454ae495548d364e464158d517611465a78c2e8c4580500281f01026fcc5186576514960647bac1e44bbb2aadd1662d8470a46541e96e08d2063843187e1d638d6082f4da28d8aeb896104e86c36937a5a72efe46814109e10621af669527cd0a201e0d4457c61710620e09c34fcc99b58951a90f0da8ef842f218e3242c0444e4148702c414a0b5208cf58180d7688f523b126ff045943695107f0223401802112a81c7c8701a82a19306a1b44814c65782dbe680643579c9d346879333da2ff1c9e91d245c958d5217052d6cff24389d14ca89531da28df092f6ab0ec8f3f253e1c5c798131ece9d52e7232aa1cc4518a0550a83348b8fa1d4441086ef616364241211b285c0d0f655c33918e2890143e11615a17176514c6a0fc8237ce6dcf44b18aefd1920f0c41fda10be1f6c15058997d60543d82e8ac8ed6ac0f5045fa39a714b1231aeb870f302ccc8200090f5a98ee7b6858b725357a71c551673c4a883745b32c08d40a48892d1c5c8d71c47088b8fa9548e8c3c1d278151429ff622e00608a85b8395cfc4a5defd627b417f0461d8b3380ca2cdb3135bc2980f3662c60b4db85a8de888b1442084ffcad22a0f421a450cf66317e508b820238e3b42b2f2f81303443983621c3011fef293b0d32dab523293f68b291d02511f0784f03304e8535be19455a8723aac4098894edaee12c9e94b3fb3ec92d872e30cd18c7b14a13475c810b73daa5dd4c402c8015060988624a23e4251d6979f12af0c31a21cb5753449c75316846db5bb84a12e6a62445966e9b4c9b368b40a9eb41391c80df72a373b1303ec07184f08cbaed3b87947a00c86a971a40f97a0624039dd78f1f4ba1304a8fb22c28c80a0f0beb4c1eb06d8f37378c8acacaa77d4be80b0ae2164d4d236c1289141618d1c8f94958e61fc118e59b990ed89eb8ad0a6645582f4120ae42b88a6ecc6d44a40288e15861bd1ce3f5e62c517ef158fc717a705a45a59100285f181d118ed64783a21473e1101f14ab7cf519a65e346441b80b2caddc910928bf10a3903010918aa44378b220e2241d8161962786f202c9cb0841042058b4f1e479cceca37fca4d3ebc379a50dc33b39220e086335028975364788525ed633cb8f2860b63a41c0fa4b816974ea653bc6d02ebe483a094f71a5144180d8694660550de8d5de37d8d84e184ae87f929575a6e3a6f44384147aa6113e0cd0ef035c1c667bcacce8b3f10427dd124f044488f73228dd2481b81a33eee9432d3362181b09af2542e8ab8391d0d654c2c1187135a19cd2f857593aca374d599d98e4e4849c92ff39429dcd3f67e6a798307e224edd6d23601403df8968153081e48781104c6141c946e93561b2e2ac238c18361949fc488183f2c5d94c10868d72468830bc06dd33935fc12c6b48341c7c9d933257f1ea138e96b0e309ea84200842182b454b0fd290f7832b2d6cc600d2b81b01b06320c0082304230bc7099056217d929eb3ac5ce3f0db2caeac6caab3b319d6923e94c1aa0d3cf062120ce0757164f8b3003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1095 : walk cp1095 moves1095 = last1095 := by decide +kernel
theorem result1095 : ValidCode last1095 ∧ ∀ i, 1095 ≤ i → i < 1195 → P i := by
  have h := walk_sound moves1095 val1095 (by decide) (by decide) (by rw [checked1095]; rfl)
  rw [checked1095] at h
  exact h
def cp1195 := last1095
theorem val1195 : ValidCode cp1195 := result1095.1
def moves1195 : List Move := [⟨[],[268,12,428],[965,585,1165]⟩,⟨[],[875,1105,1065],[200,1058,422]⟩,⟨[1112,31,213,442,1059,289,449,115],[1112],[749,181,559]⟩,⟨[],[377,409,333],[1160,514,758]⟩,⟨[],[942,822,778],[799,591,559]⟩,⟨[],[653],[958,312,728]⟩,⟨[],[398,348],[879,545,685]⟩,⟨[],[955,1087],[1016,894,964]⟩,⟨[],[818,312],[875,519]⟩,⟨[1069,50,287,429,184],[983,955],[8,776,80]⟩,⟨[1151,240,468,468,409,293],[838],[999,301,37]⟩,⟨[],[981,917],[476,1108]⟩,⟨[],[774,1172],[633,1075,541]⟩,⟨[1114,172,698,300,27,114,352],[1135,351,1181],[210,1078,522]⟩,⟨[45,799,1098,4,828,362,107,614],[530,228],[283,779,495]⟩,⟨[],[495,857],[710,586]⟩,⟨[136,230,652,1031,1144,91,1002,650,177,574],[862,642],[967,203,793,829]⟩,⟨[],[91,921],[572,446,46,328]⟩,⟨[],[540,798],[1189,385,63,903]⟩,⟨[],[691,1211,519],[714,182,1178]⟩,⟨[],[558],[729,509]⟩,⟨[],[],[794,784,1152,1212]⟩,⟨[87,13,13,590,963,197,208,110,87],[14,10],[219,113]⟩,⟨[],[593,465],[836,238,380]⟩,⟨[],[328,104,806],[211,1047,289]⟩,⟨[],[91,1013,1151],[600,1054,1164,202]⟩,⟨[],[],[45,583,629]⟩,⟨[],[1,1193],[140,1026,810,186]⟩,⟨[],[632,686],[1]⟩,⟨[],[601,371],[814,1036]⟩,⟨[],[810,1070],[431,707,645,775]⟩,⟨[288,328,481,481,732,1040,1046,574,549,288],[103,1007,1117],[494,112]⟩,⟨[],[194,100,892],[947,19,351]⟩,⟨[],[1101,117],[666,890,58]⟩,⟨[58,1193,1193,58],[62,782],[907,1167,247]⟩,⟨[],[319,765],[562,298,62]⟩,⟨[],[366,1060],[899,805,83]⟩,⟨[],[1055,637],[1192,32,344]⟩,⟨[1,557,288,288,45,434,673,289,108,76,384,1],[812,526],[547,571,1173]⟩,⟨[],[139,263],[986,350,494,458]⟩,⟨[],[458,1014,172],[971,107,1203]⟩,⟨[537,977,878,56,1164,754],[1,827],[632,820,144]⟩,⟨[],[778,932],[983,1]⟩,⟨[128,56,56,247,247,598,921,210,621,128],[1211,753,261],[462,1046]⟩,⟨[],[1228,1068],[997,379,703,637]⟩,⟨[755,647,647,755],[1049,257,1045],[292,294,1038]⟩,⟨[],[1140,232],[907,601,717]⟩,⟨[],[213,1105],[1224]⟩,⟨[],[926],[77,257,393]⟩,⟨[],[815],[644,672,530]⟩,⟨[],[602,836],[715,311,761]⟩,⟨[],[415,537],[378,1004,450]⟩,⟨[],[196,1138],[1125,1231,787]⟩,⟨[],[1181],[684,852,196]⟩,⟨[],[394,496],[207,501,435,595]⟩,⟨[1,40,333,450,308,524,468,40,1],[59,253],[652]⟩,⟨[291,777,777,291],[1012,10,462],[253,1175,993]⟩,⟨[643,650,1231,385,499,236,730],[215],[570,492,646]⟩,⟨[],[848,996],[87,303,431]⟩,⟨[],[791,763],[472,1106]⟩,⟨[],[1216,278,1030],[1169,819,903]⟩,⟨[],[903,501],[702,504,488,316]⟩,⟨[1157,548,1013,234,1105,16,324,399,709,504],[48,670],[453,123,557]⟩,⟨[],[853,1003],[578,522,340,48]⟩,⟨[],[50,732,1248],[1251,1187]⟩,⟨[793,711,17,279,972,1223,1151,1116,99],[569,1171],[76,1088,38,744]⟩,⟨[],[740,134],[499,775,1139]⟩,⟨[],[1073,723],[1022,10,42]⟩,⟨[],[42,1182,518],[301,333,393]⟩,⟨[],[121,13,925],[360,504,1098]⟩,⟨[18,855,862,335,1117,18],[914],[325,597]⟩,⟨[1,760,819,971,804,762,979,299,1],[73],[868,412,152]⟩,⟨[996,1034,886,1049,430,873,537],[92,730],[761,549,73]⟩,⟨[],[573,291],[716,644,894]⟩,⟨[],[478,336],[105,11,1013]⟩,⟨[],[1065],[1094,1084]⟩,⟨[],[490,326],[131,599,501]⟩,⟨[],[9,421],[110,1014,1076,674]⟩,⟨[],[796,376],[179,103,9]⟩,⟨[],[253,561],[1240,878,814]⟩,⟨[],[542],[887,687,253]⟩,⟨[],[1043,327],[42,1162,702]⟩,⟨[],[610],[711,309,919]⟩,⟨[],[709,387],[24,404]⟩,⟨[],[266,876],[1277,691,367,633]⟩,⟨[],[295,191],[590,1030,666]⟩,⟨[666,626,1079,1082,125,520,187,187,1143,1272,834,162],[488,808],[999,683,137,901]⟩,⟨[934,40,387],[767,801],[504,894,358]⟩,⟨[],[10,100],[953,1101,573]⟩,⟨[],[1207,791],[598,980,10]⟩,⟨[],[612,180],[1073,45]⟩,⟨[],[1041,561],[1024,1062,478]⟩,⟨[817,1072,1072,817],[834,676],[217,703]⟩,⟨[1132,792,792,1132],[173],[438,842,356,1002]⟩,⟨[],[1052],[903,179,173]⟩,⟨[1,612,378,684,857,817,532,625,1],[313],[296,536,522,1104]⟩,⟨[],[1108,258,102],[1083,165,189]⟩,⟨[211,1145,239,1008,210,167,221,693,814,168],[525,49],[1134,1260,432]⟩,⟨[],[98,614],[899,57,869]⟩,⟨[309,1164,705,393,393,705,1164,309],[869,217],[684,802,258]⟩]
def last1195 : PathCode := ⟨1295,0xc7eb4400a0121eb531dcf6d0b16e4a6af4e38aa2cefc94fa2a0f421a450cf66317e508b8798634c1b4627c0ad72bff2b45fded067414f9c0ca278d50dc26a579c41dcb6a17052d6cdac3c1a82553dc6992f029efab271d0088710381b3cca6a7466078258b381127a254a90760e24e84709e334d8b0ea6aea689394a1ed18c332e361c92cfb3fb52c9e84b2ee3b68965f89a3af2e807bf12d13608cb6b34a1b006a977531017c8178da9dd4c9eb3ac5ce3f0db11d32c22b044aa210603402021a1544e835225c169b70b51bd111621bca99a5b995f0524642bc30b4316ea336e204d1691c3e893561b2e2ad3a8132ea5751fc92a5f865048390d26de454ae0b5528c4124ac7524d7d7091f4ca991ee2b57161d4ce4f50c8f7583c897773995521f3c2ba06cbab2cb0fd290f783262de703215ed447822034327da52f62967143d8159f665a2d86e5449b8a99518a7139219fe30caeca292c73b1303ec07184f08cbaed3b8794958e697c26d74ca716457cbd4776e534843a1d7a905675aa55690c09497b8531e13625d2c8501603806227fd4293ca09300723e58088f10283b9aac5096b9c5eabf0c41c13869f9931ea334cbcaa88f90298caf05b7cd00c869cc0e8e31ac0e97c1305c1c667bcacce8b3fa0a4eda4a5b9bd0880f8a55bf428739bd618e14a2240488181b09af2542ea07a822fd1ce772fb09d0d849af14d0f6264a1b4d31ee1326b43209c1ea9c01007256a375b27c0409bf3152d941b6e34513da08436fcb097145751a6d05ece7552e5d2d4df842f218e4cd6ee12a6349b21281e1c8d70148d96d50f8a4cf98138f30263d9d3aa5cf408f112e357119d1a4e92ceb8291925e4d3a7b2f393b3119285f56264070c2f4227bccaa2c9704e4b5b19060042804614612d16e50d2665c619a0d2eed4a791f2764cca5bb8d7587e0242919507a5b8234818e10c6418450df1b44dc61a4d10accf6ea66ddf4861a69d9e50ff6030e06c2385b0b31ba4d02e0fa4703a42d88623cbcb58cb79898717a03e5a425c86a0307a4b0512edc8907e60ca78d1a1e676d58dd2ca64e574d99266bc6c947c55176b25000a463a0b00a4fc1505a61db5525ef84bc16192032623a9d4e60c5e7c1a0d5298118dd1b87f543cb266f166241110fe18907a3277e31625b9e7366fa4141f634a29433ba33e06a57a3522815437b15848601c8214120ae42b88a6ec12d7f0c3582a61ac8e8a12140204012b05313aa9b74a490f6085889001721a0140c846f86547f3e9d3c420853384585685c5da650da4de0d417c9a3ee5481f20214431d9cab831342118bc03c81700e88c76b23c1d10a39ee29ad24a9de7d5d7c3a40cfac4cba888258e6e87c8112657bbed0a8094359d51390b55b89209e505c44bc65a78c2e8c49c08106abf4499114d64e52b6038c1157072761563945fabd1581910511719a1502a914228b9841826218928230ec599c065172b9f9bf673429ce52ff7248493918ea06285f1a0e9ac5a8d332359d1adeca67854c3dc12be38c7ed233fa22c7e9fb809770e063427c97ae1daec8c4b09c6641c98504c56797203cd9a418d61c71da15979416c147d8be68401d849388d9250880344e0a8090b204732ad472cb98b3fdd109f10535c668ec1f13e4cc0798164159e1d483a61d1d4aa1f445dfcd073baf1e3e974260951f64585190141e06d9d91d56204c168a55fe4a55d73f8f319e4c4ab9559d98ceb491f1c21c530a1f166354959171d27a51ca474137ac0aa2d336a1ce4cbecc393c4189d1376140fd688b33e264cdb4db78c8acacaa77d4be80b0ae2164d4b7cd157f1ea13cd94c08920e13d508401084d49e008008bef4a2e82523fd1983b451d018c01a4d4498542c0d9e904940bc1d0a039c2d8c4e9478ba3f0bac7c84af12400497f0346443bc6fb31c012d78c477a8305315af5db148737272c230fe226ed8672b639c7cd6b40e9266b6723bd858d90904846cab6c54c20792c6c532a37dd2cc7894f94440923b126ff044a44f83326c1b02e0348db04a2452f8735a1c4d218cd4659468bd10c20b0841042058b4f1e479cce90748450a0ba29976b551dc5605c0da6d36a2349a90d1a726404887a019c61d8199b1630904319ae4264da11b6d5a68f4c23d58281c1e89d383c2adcb50b7eb2b0ca2ad4382203c1c84f2de1e0ad05a91949fb456983d60db1e6e62345bced76834104be8378b205e0443f8b35921604c288c5b1ee6451ba490374db3324aaa469b272320ac6a8bb27eb471722c1c8b009d294010b286d2a2060a4f0444888f1bb90ac2d7309e2360182f01b74c48d131da5df129cf86155ef892f0eb972a00121ed9ef0241c491766e18a1bcd7869f4e23958a8fc0288f318cdeca74a37fca4dd6cf46a0701f20e58e8b145fbc563f1c5e9c1691696440449490a042c32c4f0de405a660e6475b3b2a45f2d4778ca4fe2440c1f962eca6084346b923441a213bede823bb9656164dc001,0x4dc059656ee423b7a3be88441c8d6b90d20832962e7e40c0914fe32877cb545eca9b391d0e699805b794f0cb02c28149112440259917059e9c7163ef145fac58e8395f21c06a13d1d6a937fd28ca737b18c3cc28bf08a8e54e227d786f34a1b867672441c4099ee7b4122809723ad2f3e255e185cfc4a5de7691312374c06c2f0062362797330b90a6ec8f12204493c60a886d2ca010a509d2c01c88b0172d1e7eaec6a82b23249c69aa924accc4da0de4946e6447b85b2234c2581922cd3f81105e2c8378fa1048d07693b45b88d6e6c7a0d8f5698d149fc655a8b41e0b784f27203c088438ab4ca4ac7eb42dcb0ab83c74de8870828f54c223d5a6db6119364266b831a416306c4198769c68048781226469d0d26a234daa6d03605d1591dad59768a60b94248441cce9e71e4d3c58908410c2020c438bc51865b35219135a19cd2f89144a36c348b81b01b03333e0a44116fec492390294453c78cb37dca8c5331b79308054adb6cb21090364858ef6721ad9270396b1f339cad8673b62263f8231cb37321db13d715a14e831de8c4b5c014c76faef2440d17f0126403c484b1f0ba8fc8ba51c4eb639c280dd0af09404119eb03543260d40698c1404518ed198ff6523a04a2fbc088209e1351081005084f60e2244c136613c7a57f344b79352162b80b2fa7d4a9caca2b78d36cdb1933e22cd6883f6144dc9d10693d30cbeb93a1ccda2d02a7ad04e474727a47491725635459a1f4c21c47091f2d28ce76555aae4c4678f34fe5d7295fe295168131624759d81b41e405519161f62542605d23ebc73bb41dfc9171f52a91d18783a7519e1058161e4cc4f91f03b066cd710427dd14ff98ab2d474ab472c8090aa04e00d0884948d84e1848076842f87db054165e615c761c635a41b6603c5c967931850726642714b1231aeb8797a9f234381770025fb9fa22cfe9231fb38caf9c130f85499decc6b59cc8cd316a9ac839f18a1a0663939212724bfce50a7734fd9f9cae51701999bb12304a218898418e6228c502a85419a45c050645582f45fae51561d807255cc100e2b7394d6445498fd06aa049c03102e9e365b2f1c414109e2495bc2d138754358250a8fb57bc998101f26e963882ea04cbeb40d0e9d79f59de929ad38a39e4281d48f76a2300e85c3c8f0118d08312ae19c8c71448081f1523ef268178354de36a6517685c15845cce085109d3cfa47e1946fb2114068172400888214f612474aa6d3a94c2b100420050a123a1aca9858230d7f04b6ec2282bab9120851c8180848c54378552288d65781a33eee94328a63507e411be736e7a258c577e8c9078620fe4462445966f2c9439fd1b837411ca60d5069e78314e6a76238c9920584bc3e125ed561d9691513f00a02c63a291002c9177155479b26bc498d995d64eb28dd356676878d1a9e60c1f8893b75132c07a00c86a971a40f97a01c589ade58cf2e3ca182d8e90703e92e1341ba2cc5b08e06c4386023fde52761a7219df19b6eb33d0a93461b371b437c451060c63848188d1b81e9950a44241f8758e365bb327647ca793522ee836199712674356e4b446118680010060c64b59399708b0ca9ef4230bc7099056217d92cc493abce7b34e5e4648293ae92c939d1c463564b8f15025ceea99d18f302e3d8133e8a543d6d23601435e1ca0721326e6304a6ef3358e3c884337d2d39755339c5e9b451b15d712c26fc10da0c4f344db941cb63146fc409f05b28de5681c010a701e8274329ae1347b4d286e64bd84d0bc449c3609cbee774732fca0a078ba2546bdb0860488900a23856186f473d0a5be2940fc229bc96da493ba0acfce8ab37bd199c1cc17c03a5ac38c0e873086c037cc16caf26390223caab2f3347a99327e386704c42fc5eae7096b149aa0ed02a3c808f94724c0a084f1429ff622e01601402c8975364788525ec94c30568a9675c157a887443cd26e51dcbd15f16529d7489b97c398959e53b8bb4cbbc218501c3ec4c73a4b0a2abb30c7f921c4e8a6544a9a6e5441ba2d9969f60543d9c5296bd9a549f3428807835115e0c9e718b8323dd2943f2caeac6cae83c287d554e677722583bdd0c93d4ce075716ad5ee2644ca47d70b5f524b1d24b105282d4ae1156de3483941286497c92c7f574ba8134ea2accb961a4d3e8471168136e28cd6ed0c30aaf0641495f0e65a5aa61bc5891146f0b46dc168973533a154068202d00600844aac1022ccb11c36e3f1733ac7ad4ca778da05d7cc40752a5c0686c34adac8ccd82d0fc407cba3ae26a5fa253b6bb84b27a52cfecfb24b61cb8c334631ec52893a9a6ae3a98b4d39e31c0e8389760a42549e8112ce2589e06609d0a6cf381a40c8740271cac9efc0a92f1a53d8951a90f0dab5b05285cb68779c495c26c378d489c0cbe741419ded17f2b4ffd7282b27cd18c198d7982e250c5f66233e450860f48a94fbf22ce2a8e3abd4a65b90b3db1dcd4e1e80400ad107e803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1195 : walk cp1195 moves1195 = last1195 := by decide +kernel
theorem result1195 : ValidCode last1195 ∧ ∀ i, 1195 ≤ i → i < 1295 → P i := by
  have h := walk_sound moves1195 val1195 (by decide) (by decide) (by rw [checked1195]; rfl)
  rw [checked1195] at h
  exact h
def cp1295 := last1195
theorem val1295 : ValidCode cp1295 := result1195.1
def moves1295 : List Move := [⟨[],[362,62],[1279,611]⟩,⟨[],[495],[470,52,460]⟩,⟨[431,722,785,439,431],[80,958],[577,659,77]⟩,⟨[957,1001,767,459,459,928,1036,1277,404,1167,975,1138,486],[403,291],[736,368,814]⟩,⟨[],[1266,204],[353,1023,119,1185]⟩,⟨[59,59],[707,611],[1072,414,320,1192]⟩,⟨[299,1,443,261,522,548,306,144,167,783],[726,602,1060],[57,407]⟩,⟨[],[893,49,211],[230,142,248]⟩,⟨[],[844,448,1028],[965,277,475]⟩,⟨[],[1087,139],[636,122,1270]⟩,⟨[],[924],[1059,1227,1207]⟩,⟨[],[67,745],[120,978]⟩,⟨[],[1272,424],[487,893,67]⟩,⟨[],[623],[1112,1014]⟩,⟨[],[24],[77,683,677]⟩,⟨[],[35,1203,625],[236,580,1000,24]⟩,⟨[154,24,24,154],[708,790],[695,439,465,463]⟩,⟨[],[879],[448,1266,1270]⟩,⟨[],[540,858,140],[755,571,253]⟩,⟨[],[599,1135,1115],[930,800,944]⟩,⟨[],[1130,394,352],[433,1065,1189]⟩,⟨[],[1193],[124,964,780]⟩,⟨[161,1033,22,369,311,847,597,285,546,979,1165],[1058,930],[259,1129,219]⟩,⟨[],[335,33],[700,1224,180,326]⟩,⟨[],[1134,792],[959,1163,807]⟩,⟨[],[453,717],[776,1098,886]⟩,⟨[],[898,556],[233,197,417]⟩,⟨[581,863,310,611,969,237,385,28,945,558,1150,319],[1,529],[928]⟩,⟨[],[468,1212],[1241,347,1]⟩,⟨[],[439,607],[362,122]⟩,⟨[],[728,928,1086],[349,943,199]⟩,⟨[405,1062,1062,405],[567,1293,161],[582,624]⟩,⟨[783,199,199,370,583,896,325,1105,755,425],[1186,1096],[1313,293,695,1175]⟩,⟨[],[189,253,1047],[1306,382,1262]⟩,⟨[1068,845,845,678,678,1068],[1070,1294],[1317,343,1045,189]⟩,⟨[],[821,501],[172,988,152,576]⟩,⟨[922,588,258,1083,164,514,864,780,1009,109,401,1150],[12,980],[1161,753,899,197]⟩,⟨[],[75,887],[704,1112,12]⟩,⟨[],[286,184],[1063,67,171]⟩,⟨[839,811,940,452,191,790,860,868,707],[707,151],[58,296,952]⟩,⟨[],[952,206,546],[945,315,1125]⟩,⟨[],[623,1159],[542,982,680]⟩,⟨[],[532,646],[203,641,225,1089]⟩,⟨[],[677,1287],[736,44,790]⟩,⟨[],[378,1010],[325,279,1291]⟩,⟨[],[1213,587],[776,654,332]⟩,⟨[1274,211,346,1268,902,471,280,272,1335],[1234,100],[663,595,143]⟩,⟨[],[999,905],[940,1218,1098]⟩,⟨[],[964,850,880],[485,731,527]⟩,⟨[],[165],[976,180,646]⟩,⟨[320,320,874,997,639,344,844,989,989,399,399,918,579],[88,1312],[1021,259,505]⟩,⟨[],[159,585],[320,10,1268]⟩,⟨[1240,301,955,668,495,407],[708,22,56],[147,1213,709]⟩,⟨[],[293],[1078,144,758,950]⟩,⟨[260,139,1151,1192,1192,145,782,624,994,212,895,904],[1100,360],[925,415,715]⟩,⟨[],[109],[152,280,678]⟩,⟨[],[1328,1032],[171,17,1259]⟩,⟨[],[1,531],[638,470,452]⟩,⟨[],[102],[613,801,1199,1]⟩,⟨[],[1179,165],[1254,998,238]⟩,⟨[],[1092,274],[69,989]⟩,⟨[],[351,341],[354,1340,832]⟩,⟨[1287,335,817,817,1197,762,986,840,404],[1098,30],[533,675,1073]⟩,⟨[1073,629,629,1073],[1,717],[558,1176,912]⟩,⟨[981,1319,484,484,820,38,199],[252],[965,239,1]⟩,⟨[766,1144,338,557,1089,33,212,974,1169],[],[708,1326,340,14]⟩,⟨[814,493,493,814],[1150,114],[921,805,975]⟩,⟨[1071,1349,1053,1061,1232,1129,706,1163,860,863,214,584],[441,653,309],[940,764]⟩,⟨[428,844,844,681,681,428],[36,556,74],[1259,75,347]⟩,⟨[],[1231,621],[796,878,36]⟩,⟨[1228,878,269,742,322,346,441,292,494],[],[177,1335,1027,679]⟩,⟨[],[243,379],[1092,1266,1214,178]⟩,⟨[],[286],[729,641,351]⟩,⟨[],[511,1165],[510,138,1220]⟩,⟨[],[1260,1022],[737,233,139]⟩,⟨[1267,800,1261,582,780,1100],[1283,1337,983],[678,1306,608]⟩,⟨[],[36,1190,536],[493,461,407]⟩,⟨[],[1311,799],[750,438,36]⟩,⟨[992,714,288,1067,346,514,735,686,1324],[218,920],[429,1275,59,935]⟩,⟨[],[247,561],[240,1222,1088]⟩,⟨[],[1096,812],[585,1007,1371]⟩,⟨[699,201,360,757,241,342],[229,1067,543],[1270,826,942,1300]⟩,⟨[],[1150,912],[167,69,895,131]⟩,⟨[],[1185,537],[56,992,1212]⟩,⟨[],[1212,992],[353,315,1027,667]⟩,⟨[],[947,235],[712,1030,250,458]⟩,⟨[846,1207,597,1303,546,705,1226,1281,641,195,434,915],[916,962],[1217,601,905,1285]⟩,⟨[],[1327,789,483],[960,914]⟩,⟨[],[292,202],[795,1103,1193]⟩,⟨[],[1,199],[862,1160,1382]⟩,⟨[],[1382,1108,72],[779,1193,1245,1]⟩,⟨[257,568,1309,795,478,528,380,257],[895,43,555],[964,1304,1074]⟩,⟨[],[1158,742],[935,153,1007]⟩,⟨[316,1193,998,1041,612,1281,1245,60,198,194,684,848,1291],[1291],[114,244,808,1250]⟩,⟨[625,758,632,744,151,1242,1261,1254,466,818,1266],[902,136],[555,579,989]⟩,⟨[336,84,804,114,722,472,6,948],[181,711,1209],[1368,366,690]⟩,⟨[1099,1046,1262,1342,378,453],[522,652,1360],[339,851,181]⟩,⟨[1376,983,408,1324,659,392,830,80,392,584,1114,1376],[297],[1380,1142,244]⟩,⟨[],[1300,1260],[5,669,99]⟩,⟨[],[1,981,535],[334,60,628]⟩]
def last1295 : PathCode := ⟨1395,0xc531cba331222cb3796513a299512a69b95106e346a79830433fa372b233d186b054c3591d1424280408025629ccf09a8dc06891376c33ab911f242a8138520948900a2385a394362a3955f8bd5ce12d6293541d92e3c5408c7981ac637411ca60d506aa399d3ce3c90f51b59d1adbf2c25c515d46d5c4680f5019be736e7a258c5a584511acaf03467ea29f42388b6862dd466dc5b988d16f3b5da3304e853679d36566f7a333830fb01c613c29055087f34389a4319ad6c8b0fb152ceb82b5317c149190af12a01d208e0160424300e410a0905728408028427b070c434139e1c56c2cc2ea3f22e9475f552a0b942a9eec599c060fc449dba8937016595bb950f5882114e9467b85b223a2ccb961a4d888214f625525f0a90b52364237eb0c002b28ade34db9d2c00a0c635ac1cd3300b6f29e19640d2064393b3ca1fec061c0d89995744a36c2307e1d638d069371b437c210820be1cda2e5e8951af6c2b7c5281f8453792db492774159f9d1a272c59c08990ed8811122adecca5b9da5df129cf8a218ece55c2a19306a01e4055192b51bad93e0481b2020022fbd28ba0ac1190ee2ed32f2a5483b0669172b42dc2488968a12c73aa8df74b31e253e51102344db941cb63146fc40b402034fcfd3f7012a6dd2d5b51d2ad1cb20a49281783a1251460bc898418e6228c502a8540c4807612f6e075535e29a1ec4c9437478e32be704c3cdd356676ff949bad9e94d45e0443f8b343e0149f82a0b49e05d329c5915f64b47e213a77d2d40580b968f3f576354158c5697a0a7ce064139bd6181e0444884b90d4060f4960181224f53381d5c5ab57b899132d2b05c6d8c98511e6275b1ce19c6805ac38c0e873086c035c228c6333a754b9c8c927534d5c753169a73c6381d0712ade1689c3aa1ac12854aa0285afa92aaf1b5919a62d5359073e3a3b5ccb8c3341a5dda94f23e4ecaa71968b75a693bd96c0b80d25400c8f7583c897770b8bb4ca1b49bc012d78c477a830530ac22e6731b792f1ceed077f245c7d4167a71c58f9f1166b44b85211a03a5f04c1a06ff59e30438a1eda313e606f84bc06c16a5708ab6f1a50f95334b73282d828fb17cd0aafc0271cac9efc0a92f1a53d8951a92155a14c4eab90d054415af5e949bb39332138a58918d754a5550090f5a98eeaa4d3e4d02fa54afe3d4279b29811251511e608778ca4fe2440c1f962eca46bc3940e4264d9f6496c39718666b66d61e005058c74520a0409382a4a47624dfe088b87994d0aea27a2513c8503a91eed4463f82c216140cb8458654f7a1185e384c82b10bf3e91f8651366941fc45498fd06ac3b6aaa71d216c4311e6a5af9880ea54bcf9330cc467d223843898f41b1ead31a293f8cae1206495548d36aa0ec1f152054c20902f0d171d27a51ca474137ac0aa2d336a1ce4cbed679845f94140f1741196532713475e5d00f7e25a10e2ad3292b1fad0b09c46c0350a72e96a6fb659091f1b681701a4dc9d41f634a29433baa8d1f9b5c2578920024ac7492c41ea3bc6fb31d0e8879a4dca3ba6d06f5b65e3888c28c25a3ed5ef26604238a0318034d3b78a52d7b34a41e8c9dfd4149e305443696507a014a172da1de7125709b0dc052365b543e2933e604e3e5aa2f654d9e9d5563c61746244c070c44b99d63d6a653bb7a08e189211072735629c1ac9ca56c0726344277ead46a64c9f8e19c10fe44469c86614e1e5ea7c8d0e05dc0cc1da04cab4ea04cba95d47f24a97e194120e54c92f0eb972fa1049f72a40f9015370db3b23aac4a4b5ae5f0e62567954fbf22ce2a8e3abd4a65ba1b09398c129bbccd638f2210b1848218cd721326c2b8859355973167fba213e20a6b8cd5e9272940c99200e4ec2ac728bf6499ad9c8ef61630d26885667b750982d29e81c65a55cdccd84c2581922800487b67bc09180210c6d04980391f2c0447881585ae613c74de88708295342b88a6ec12d7f3e60b657a999b1067498b5b191cf5649c46c928442984316114f0aab2f0aa1bdc8d10260b41e0b784f2940d81999f0520e45717e0365741e1060042801915607520e9874752aa8d21f555398d5c4674693a4b3ae0a46497934e9ec90cff18623cd9a418d61c71da158167d4958d544753a9cc18bcfa6243c0913234e8693511a6d53681b56e107235ae434820b52b817408b32c470dbacb3124eaf3aa31ce772fb20b02c3c8cb28d17a2184117eb163a0e57c87026896f0432a0f482894317dc535a4953bcfabaf874819f5899751104b1d2e0ec7ed233fa22c63939212724bfce50a7734fd9f9cae517578edaee12c9e94b3fb48b27cd0a201e0d445783279c62e0c8f74329ae1347b1bc41a4f4c3acc8a83d086914abdf14bfad489891ba6036178d99266bc6c947c55176b2500491766e18a1bcd319061145111c10c09497b1ec528ffa85278922248804b322cb32db06a611ea82b5caffcad2678fac4d6f2c67965155dc298f09b12e964280f407cb4855339c5e9b49bb08e9f25287e595d5a957f929575cfe3cc679312ae55676633ad247d3ec0a84f1245fded06747ab4c5893372c2ae0f5431fad10c29c44fa60c30848522b20de11d3e67395b05a8de888b13228dd2495399a3d51591dad59768a5bdbbe336078b92cf2630a134cd06e94b4db82d12e6a6742a80d0170f23c046342004001,0x404508462f00f205c0d0aa2741a912e0b4dbd2d6e934134c28262b3cb901e336ef9bda29976b551dc563d466953c928dcc88b12228de1695b1ce3e6474de2c8522120309834fa710c2b441fb50e0f0ab72c4cc58ad347a19ded17f12413c0acfb47cb4a339d9556ab93119e3cd3f975ca57f8a55d596587e94a9f4239ba6d05ece7552d207cbd02805912ea6c8f10a55d945796b196f3138fa99cad3ff5ca0adea98406ab6cb348b4b220224a48278a14ff94a1ec5ec94c301c144514418318f34a1b86767245002c9177155479b26bc498d985e036e9891a26ad52fdf12af9142183d22aacd30e4f1061bd1ee1326b4323de0c98b79c0c857b511e0880d0c9f48afed4b27a12cbb8edd5e5172b9f9bf673429ce52ff7248493918e22cfe9231fb0ed4b8b1c41750265f5a06874ebcfacef494d69c545f9420a0f4ca80425be689c07c83963a2c517e10621c5e28c32c3cc0b20abee77473aa2bce4ecc4aca36c474cb08a5d2b82d48210d1ae48d1075b81b4da6d44693521a34e4c80910fa62f3c18a7353b11cd52567d405a15c761c635a41b6623c618ff2439ecd39791920a4eba4b24e747118d5ce655487e8d4aa47461e0e9d456064680010060785740d97e15c4e41489f0664d82504f2de1e0ad0261441c886f0aacbcaad3c6110c6981109291b09c5591cec64b5d260666c69995e0b6f997f04b6ec2282bd4d8281c1e89d313cb9985a05479011f28e4981410c68841810267b9ed048a01921604c3360dc95765a0729e8b4098dd667a15268c36163bd9c86b649afd728ab0ec0399203269449c5e83366b88213ee8a7fcc55964d4858ae26c84cd7063482c6210bc8639335bb84a98c24e1b16e4a6af4e38aa2cefc94f9e525639a5f56ba4ab123acec0db4dd0103e2a47dd04be89723ad2f5320e504a1925f24b1fd5d2ea04d3a8ab0131da331dc3818d09f25eb87615218699110fe704e1a7e64d1aaad1df44298c0715b9ca6b29c55827241d2106208ede93ba993d6758b9b110711306205d3c755a9d3676548be5ab8f604cfa2950f5b48d80543709a95e710772da85c149e8650da5440c149f505dfa3241ed297b14b78b4ec34c60a028e2044995eefb65a2308c2e225e56d06e9b63bb729a421d0ecc76faef1ea310492b1c24c80789095b5c7ea8cee94328a63507c9d13701a05db6c7c908d966fa5a72f4280311b09d42dfacac328ab50e1687e203e5d1d7134c9d6504617503d4117e98559cbeb93a1ccda2d02a7ad04e474727a4749173c390308054d481f03b2aa34d549256063848ca4fda2b4c1eb06d8f0e238548867b313313e54bba9880be6a5c794305b1d229c6ab0ec6abf44991141f9a51361951fcfa0beac4c80e185e844f79954592e1408582c2fe0463b591e0e88544fa2489caed347982e208b7f62491ea4ce04082805231d0580161e1b56b619971b0e4967da4d90940f0e46bb2962e7e40c0914fe3287798211f455122609b309e3d2bfa540be4d34faa43b9a9c3d0095554a35d91896138cc83926ee94bd715b510d02e44ea5315a4851a82553dc6992f029efab271d00aafb4217c3ed82a0b732d2d5343e1a4dbc8a95c16a1b0bc3e16064f9a307b38ac119e3fda07305f00e91a1484b82d11667c58fc717a70587d1177f341ceebc7792c6e6708b0ac14e831de8c4b5c0126f1b5328bb42e77722583bdd0c9500d22e06c0f6693d698b665aa73b23e53c9a917741b0ccb8d73a3af8d074d62d469991c6daaea49af8a1aa01501286b3aa27216ab7712742384f19a6c587535753449c8cae7754ce8630a35c300c869cc0e8e31ac2019c7385b189d1e6144c99b605d4ad32a647b8ad5c58753393d5220609603d0064354b9220440786186f4138197ce82a97b15158d51764fd68e2e4583507d2e9e2151f64a57c594a75d2780b48a89f80503e2cd3f81105e5359e8eb549bfe676d58dd30f704af8e351e437325ec2685e354e073db61201cc49502a914228b98418260bcd18250e85784a0a48c811ccab51d56dd2a9b012fdcfd53f202d00409bf3152d941b6e34440a5114f1e32cdf72a373a4b28a225248b72b445c668ec1484a932ebb4ee464ac0e8128bef022081b21203e0b651bcad5190141e1a8930a855c33918e289cfc4a5de76a5bb32ade4881136290e2259c4b1a267459fd05276d252dcde84407c52adf6c26bc9517aa2e734be208210df1b44dc068e35d61f8230db04a55d9983621c3011fef293b10e207035962786f202d330735ad18ca0b009d336de322b2b3002b08df64348d0b42a25e954f608588893561b2ea2c88c5b1ee9465382156250eee595859370a25db9120fd01999bb1a9e50a0bd4a5f451e2e8fc2eab316c07139ed04c441c27aa10802105722410a390301091603802080752a2bc1905257c54c82b3ad52bec8b15b19a90c89ad0c7f542904f08614070fae0e333de5674da7994d4e8cc1da4ed16e235b9b71466b768622d2387d2a299f0352bd1a914a5831625b9e7366f90183d46957146c575c4b09bf46b59d46d0f0f23ce676a3c1a0d5298118ddac6604c7d023c44b81dcd56284b5ce2f55f8e562a50da38e14a2240949481382a024247eb90ce76c44c68b709a93c29c958802100285091d0d654c2c1186cf6b20dc3fa10d8329e3461b95126e2a654629c4e964cde2cc48a3272c53003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1295 : walk cp1295 moves1295 = last1295 := by decide +kernel
theorem result1295 : ValidCode last1295 ∧ ∀ i, 1295 ≤ i → i < 1395 → P i := by
  have h := walk_sound moves1295 val1295 (by decide) (by decide) (by rw [checked1295]; rfl)
  rw [checked1295] at h
  exact h
def cp1395 := last1295
theorem val1395 : ValidCode cp1395 := result1295.1
def moves1395 : List Move := [⟨[],[448,1376,898],[807,603,493,1]⟩,⟨[286,987,987,987,650,320,1026,1326,1321,458,286],[1225,683],[1208,594,1254]⟩,⟨[],[1020,306],[675,1211,423]⟩,⟨[],[423,1211],[1374,1382]⟩,⟨[],[540,258],[807,1159,1269,973]⟩,⟨[923,781,598,621,117,1298,681,236],[1],[790,118]⟩,⟨[],[284,1010],[147,467,1]⟩,⟨[],[489,807,855],[200,98,1288,1038]⟩,⟨[1133,6,1400,273,797,272,1197,907,620,1147],[210,454],[1197,185,611]⟩,⟨[],[845,907],[6,774]⟩,⟨[848,60,1263,839,1178,518,1267,324,363],[1230],[975,67,633,1289]⟩,⟨[],[829,1387],[268,1352]⟩,⟨[],[676,788],[139,589]⟩,⟨[359,821,821,359],[589,923],[922,950,870]⟩,⟨[1099,841,841,1099],[830,1262,1238],[1017,973,589]⟩,⟨[665,429,100,734,336],[73],[1270,314]⟩,⟨[],[1370,820,1032],[133,1029,73]⟩,⟨[],[315,57],[840,972,542]⟩,⟨[613,1286,432,429,652,610],[738,616],[907,81,349]⟩,⟨[],[409,747],[316,298,138,1046]⟩,⟨[],[596,352],[1055]⟩,⟨[462,430,494,804,753,120,859,669,877,819],[537],[1178,872,942]⟩,⟨[],[942,88],[833,453,587]⟩,⟨[],[741,449,635],[52,588]⟩,⟨[],[692,550,494],[73,1097,123]⟩,⟨[],[479],[916,236,532]⟩,⟨[95,664,1276,820,1415,197,1123,600,2,619,679,1151,1184],[906,1304],[709,901,131]⟩,⟨[148,459,935,314,280,651,799,1362,148],[997],[390,186,486]⟩,⟨[574,1330,485,1334,628,605,213,1230,1372,1411,1177,325],[268,964],[1203,1089,575]⟩,⟨[1042,845,845,1042],[1183,1415,659],[704,12,1168]⟩,⟨[118,492,967,1364,104,888,906,906,196,544,995,525,780],[462,786],[1237,1265,255]⟩,⟨[184,615,49,1254,144,159,1316,5,65,1063,1038,978,1031],[569,1075],[920,648,1266]⟩,⟨[],[892,4,1148],[285,707,1283]⟩,⟨[],[1,931],[422,908,954]⟩,⟨[766,490,254,617,1062,825,155,520,1426,895],[860],[787,1]⟩,⟨[55,922,17,704,202,80,1176,37,991,741,84,189],[1313,577],[510,406,1120,964]⟩,⟨[],[1226,1308],[595,961,589]⟩,⟨[],[1369,727],[286,862,780]⟩,⟨[],[100,1120],[603,1351]⟩,⟨[],[1129,177],[1346,100]⟩,⟨[],[512,974],[305,649,1237]⟩,⟨[427,1347,1362,1055,427],[1053,1363],[1060,1362,856]⟩,⟨[],[1368,1370],[843,287,683]⟩,⟨[699,699,303,303],[699,945],[802,742,366,1036]⟩,⟨[],[290,828,1362],[45,1029,1343]⟩,⟨[],[919],[578,184,690]⟩,⟨[],[82],[459,781,1319]⟩,⟨[],[907,1071,999],[122,444,474,82]⟩,⟨[157,232,232,157],[1020],[219,1129,825]⟩,⟨[14,390,1379,395,207,430,14],[259],[1090,764,726,1208]⟩,⟨[1405,367,194,770,1037,92,590,320,9,1194,392,243],[1272],[319,1029,891]⟩,⟨[],[549,563],[774,1056,492]⟩,⟨[],[744,982],[1237,663,1309]⟩,⟨[899,1076,1076,511,149,537],[1309,1227],[308,576,448]⟩,⟨[],[1176,726],[217,783,957]⟩,⟨[338,106,837,559,1281,16,185,175,516],[471],[1336,806,1282]⟩,⟨[718,659,1343,1405,826,874],[528,756,772],[1393,717,597,471]⟩,⟨[326,233,411,912,912,1185,750,404,1351],[1351,561],[1050,1406,718]⟩,⟨[720,654,552,29,581,831,825,1164],[882,662],[45,169,1009]⟩,⟨[138,1309,646,1211,1135,636,586,138],[993,525],[1268,638]⟩,⟨[730,370,370,730],[418,520,96],[1165,1439,947,341]⟩,⟨[],[1311,1285,433],[496,656,1024,590]⟩,⟨[],[114,426],[1083,845,771]⟩,⟨[],[767,479,905],[764,644,1398,114]⟩,⟨[],[1034,1090,138],[13,45,1129]⟩,⟨[],[717],[538,1404]⟩,⟨[],[584],[841,635,1333]⟩,⟨[],[535],[1418,1412]⟩,⟨[],[146,614],[639,705,1069]⟩,⟨[],[1,17],[384,880,162]⟩,⟨[],[1266,1288],[1209,1185,1]⟩,⟨[],[657,1259],[792,416,224]⟩,⟨[1,60,548,561,1432,1],[998],[577,25,1163,391]⟩,⟨[183,948,811,161,805,1437,827],[1061],[562,1414,914]⟩,⟨[],[186,748],[1169,1119,241]⟩,⟨[],[1175],[878,1466,186]⟩,⟨[58,363,762,1043,608,58],[58,712,780],[991,599,339,1125]⟩,⟨[],[683,143],[1458,58]⟩,⟨[],[398],[507,709]⟩,⟨[],[805,137],[1308,1102,1364]⟩,⟨[],[158,600],[165,837,393]⟩,⟨[],[1115,513],[902,270,158]⟩,⟨[608,269,732,692,601,436,1249,760,1123,144,325],[1454,758],[1115,109,983]⟩,⟨[522,518,279,1359,283],[277,803,1401],[1322,992,1002]⟩,⟨[],[598,92,1146],[1363,1225,155,261]⟩,⟨[],[237],[852,1264,638]⟩,⟨[],[496,434],[1271,1313,237]⟩,⟨[],[931,1027],[728,390,1228,258]⟩,⟨[369,1255,335,527,561],[1172,1426,902],[499,215,953]⟩,⟨[],[567,1239],[1478,1358,1122]⟩,⟨[],[734],[1259,567]⟩,⟨[],[1447],[818,350,850]⟩,⟨[],[1080,178],[1337,1311,455]⟩,⟨[],[577],[158,120,668]⟩,⟨[],[830,36],[519,531,997]⟩,⟨[],[463,1247,97],[766,36,1186]⟩,⟨[],[1248,638],[247,1345]⟩,⟨[],[881,695],[936,148,540]⟩,⟨[],[234,962],[1267,705,953]⟩,⟨[],[747,899,861],[100,654,978,788]⟩]
def last1395 : PathCode := ⟨1495,0xd86d374040f8a91f74120dcc10ef1949fee282c00a8304c179a30364cc33119f488e10e21aeca58bd8a20e908310476f49dd4c9eb3ac5cd8883830358c6eaa77d52dd9956f244fba598f129f288811a26dca0e5b18a00d67879a5691d04deb02a8b4cd8099569d4099752ba8ff205082b95404848fd727de945d05608c90f5a9d4e5ecd2907a3277f50527a352294b062d7b5922ee2aa8f36561e84850081004ac5399e1351b85903533a2d41e8650da5444b13c0ba6285747181d0e610db08995323dc56ae2c3abcc83adcdb8a33b6c0ed34cd06e94b4db82d12e129bb80d599755958965dc76eaf28b95cfcdfb39a14eb768622d538e90b65cd8b8cd2b6977b8489e894b266f4362a3955f8bd5ce12d629356ddba6ab477d10a63b0c078cdbbe6f68a65dad5477158f519a0ef3892b96a9ad6ead541a0d529811d8117eb163a0e57c87026896f1a244ddb0ceb873358e5852be2c817c9a69e704e1986b6737611d3e4a44c80910fa62f3ca0cb0a28896e22800487b67bc091803e4144a18bee29ad24a9dea8454169ba130282525ad72f91356a97ef8957c8a10c1e915566987278830de8f6c5697a0a7ce064302449eb66d8329ea96be6203a952f3e4a3a7a52cfed22c9f3428828c9cb14c9a90d1a74b22009cd58a706b27295b01cfc8b38aa38eaf529d969f417d58d939fabb1aa0ac06ab6cb31e31ec5ec94c301c144514418b59536a1c1e156e58998110108e2d8af0892920488183f2b41e0da0ab239d8c96ba4cf69afd42904f08614070fb49decb605c0692a00647bac1e448d0a425c0ecc675a4a1c7eb87764348172433fd64ab3cc22fca0a078ba08d44ce8b3fa0a4eda48b79daed2d693727507d8d28a50ceeaa347e6d7095e24806202c6c795565f744101f1166635c1c667bcace9b4f353b11cd51da5df12abd4af8a2e62e4ad81d2f8260d685b8490360b52b8ff681d8d7a8ef1becc743a21e693728ee9b6be2c8378474f99ce56d6392dcde84407ee92172db210901f05b28de56a8c80a0f052adf6c26bc9517a98cb292305e0642bda8be80b26e144bb72241fa0333376353ca1417a956be70ce3402d62764140e0f44e989e5ccc2d02a3c809701421006002102e8c48987d08e3f449816140cb8458654f7a11690aa6738bda685742e1e47808c4c85a91d0984b0324afb2b0ca2ad4391d5625807c2c0c9f3460f67158233c3a80f5019be736e7a25959456f1a6dce9b4f548771b6246085efab271d00aafb4294ee75518e185e15437b91a204c1488480c218d20b18b13282923204732ad4755b74aa6c04b402034fcfd3f711b0f0dab5b0ccb8d8724b3ec06c24bf8ad24a2de34430a712bac4f1835fe2283f34a26c32a3f134c9d3e98338d4790dcc97b09a178d5347ab4d688f0b432212e4350183561db55b56398959e553f69675aa57d9162b6335219135a18fe34c77a830530ac22e670d6906d988f3238db55d495b230f1a99327eb8d329ebd29376214f625525f6d51a55c51b6de393d23a48bab104229d28cf70b6447459972c349b1128ed732e2940d81999f1662e645d1f85d5879ba6accedff29375a58e20ba8132fad0348b772682a20ad5af729fd11631c9cabb91a6d53681b56e1066f413d320e504a1925f24a3b14c3594004424a46c270c25ed9c99909c6bc218118ed61a410b68bb4ee1a89300c53989d6c6e05dc0cc1da3dd0ca6b84cf0d908dfac3000209a30dd60d06c33a5cc5a69bce317066a447c6da05d2d397a148bd952c74925e0b0c90072761563945fb24cd6ce477b0b0723e537e206dfb419507a52c48c6baa52aa804318f360e54533e06a7b3ab2cb0fd7d04f1245feb28db11d32c22974ae0b50965b8111471c294448129290270af345df4ba788547d92cc493abcea8c739dd4eedf03336323c1d10a39f70601be60b657a99c2e777698c98512d0fc5cf8a24dc1ac12854aa0284a19cd2f88208437c6d13701a38d7587e08c36c129575d1c463573995521fa352a91d2d68c6cb40e53d169056a62f82923215e1055f613a85bf52370f9a94f23e4c7a0d8f5698d149fc657090324aaa469b5509e99c5d078418010a00645580d412a9ee34c97814e19d9dae0867f46e56467a30d60b304e8534ab9b99b0ae19c8c7a54afe3d4279b29811251511e1c47c119760a4254997153082d204d86e0291b2daa1f1499f30271f2d40a4fcb28540c4d08b101a630501a512717a0cd9ae2084fba29ff315659352162b89b213bad48d0b5d30da24e1b40e0ec7297fda254551cce9e71e487a8daceaed13a299512a7645b79153f765407a957f929575cfe3cc679312ae557665b3d3aaad02c3c8cb28d17a21cbd4f91a21ca0721326da72f2324149d749649cb09bf46b3aa27216ab7712742384f1b3e5155dc298f09b12ed8c409382a4a47624dfe088b805219d8e8a4140b92ded3c4a807482380581090c0390428240aa0159f68f80126f1b4b9dd533a7feb9415bd53092f2ea32c6cb37e10bc8290326e459c6c92155a14c4eb73c11057114dd82596eb9631851ae10d0aa24887f22234e4330ab2f2497f5a332d16ee752b57ce0abf0734cc02dbca78310e2230a30968fb57bc998101f1669fc0882f20690321c9d9e50ff6030e06c4cc6f09e4e45717e06d1ae48d2c8501e8530862c219c08990ed88d758b4bc3ae5cdd7424e4a2bae26bc498d9a0e7c65d87d8beb05439c997d24ea69ab8ea97475edcb471722c1a84f4a6af2d632de6264b8f150231f18ae397259e4c614479b604d10accf6ea1323ea672b4a99a5b99416c149e2853fe52acd42a0b51bd111626451b80b42b8ec38dd0c488b252de2b1f8e2f4e0b0fa22efe6839dd78ef258d9f575f0e803d9d1e8c303c001,0x43c30c1e967403c3a75e7d58dbc978e77683bf922e3ea0b3d38e2c7de294b8b3121d08e38ed0ac0b46e6445891146f0b50aacd14a3fea149e305416e65a5aa62b499e3e84c6eb33d0a934b611e61413159e5cae3c6231f408f112e626b79633cba6b3d1a80b0172d1edc9d79743a9aba9a24e5f5c9d0eb042f87d9767c6838d99266bcb8a2bb9242575e5c8eb4bd62cd736290e2259c3088634c1e81402c9235ae1b47e15c4e42796f13306c4386023fde527621c40e068bc0887f16687c8112657bbed9688c230b883109e1bc80b4cc1cebf38257d4aee745b32d68d7f492b2ec2a430d32221fe48aa80d0b84518c6b965b825b7611415c115cf4ea5315a4856c9672e40c9290f2210cdf6cacb2ea4bc308f5415ae57fece9d52e71b49bc0123e9f6054aa090428e40c0424580e008201d4a94f2deae41402918e8670522e208b7f62491ea4ce04096312ea6c8f10a55d945b3f3c6381d0712ade1689c3ab1adbf2c249d259d7052324bc9a749b21281e1cc684f92f621c5e28c32c3cc0baad4e9b3d99556ab93119e3cd3f975ca57f8a5407d953f6455b7d912a654629c4eaecb3a8da1e1e479cced475456897f9ca0ed03a1b0930db74d0b523bac84c9b0ae2164d565cc59fee884f8829ae3357a49ca5140630069b11420c4950b293f00a4b571ec099f452a1eb691b00a86e136d242015265e54a907604647c07111f455122609b309e3d2bfa5431d9cab89b06e4ab94d4e8cc1608c367b5906e1fd0876b9d9b8681525e34a7b12a35158191a00040181e15d06709ed5469aa924ac0c7091949fb456983d60db1e3e53c9a943e236fd68584e5f64155e0c8292be2a64151694f40e32d8c6b591d4aaa3487d554e6357119d1d5d128db08c1f8758e341a4dc6d0df0842082f8734a18a1aa01501286b4dc289cfbf12d0144c9da67770ba9995e0b6f9a01dc139e4281d48f3620cedf53b9dd1cea8af393b31192d1f884e9df4d17af29c2904a4480511c2d1c1116e0962d4ae05d022ccb11c36eb297f12413d7d43f2caeae7b01a33f5160e3cd318012aaa946bb2312c1e9950d06df88137ef947242c77b390d6c935fae51561d8073240b0978492b1d9522fa14e5d2d0176db1f2a4419316f3a69b16a5d0cd06d830dc68c20c00ac237d90bc384c9ad0c8f71da331dc3816c6275398319306a0ee2edb690421a3b5118862bc271990725edb092711b24a110400d654c0ec24a97e194120e54c8139bd1075b81b4da6d446abba7231c459fd5ca5ae2b6a21a077322d033eb132ea22096375aa4dff33b6ac6e9879751f9176e65989f0664d82502e35ce8ec4449ab0d975164462d8f74a329c10ab122e3a4f4a395b751b5711a5b525e954f60853774a5ebccab8c9f99346a30f6c9495578dac8c8f36690635a6708b0ac14e831de34c3f9a1c4d218cd6b64587d8a9675da553e794958e6b56d561d8d50190d52e488b423c168ad347b54d78a687b13250dd1e38c60d3eb271348fc3289b34a0fe22d7f18313eba9c430ad12de128ad2fe02481b3ec92d872e30ccd6cdac3c11afdcfd53f202d0004a9b74b56d474ab472c82924a0b12c61208630c212148930a20e443785585e38551b9d94ed0aafc0271cac9ef8212466d877552b4f3a66dbc645656625b9e7366f90183d3a8cf1821c50f6d189f3037c360162475438ab4ca4acafac90b02611d16a4c82317807902e15da682f673aa9690844f79954592e140858498fd08e1f48983102e884600401425c08088f102b0b5cc278e9bd10e10527635840338e70dafa9505ca154f762cce0307e224edd449b80b2fa1a88af064179232ca98c5e8951af6c2b7c5283c80aa3256a375b27c0904842da85ee901f8453792dd8e56c738f991d378b22be26d8eedca6908743b31dbebbc7a963681bfd2b82d4361245b95a260be01d2b62e4b988a32bebd44a5de768d544753b3ce9b2b37bd199c198d1667c4105d165e556c78b1621201e24256d71faa33ba50ca298d41f2744ded6bb49da2dda493ba0acfce8d1308c2ea07a822fd30ab3d923fc90c170d2764e1c7ea875a519cec970a4234244b077ba192a01a45c0d81ecd270fb01c613c2905509afbdaa4c5ad8c8e7ab3681e0ad03f206048a48892bc2d8a3801004499b9615707aa1d4db59061145111c10c09497b1ec78cb32db06a2b1aa2ec9fb64d5885f9f565929abd38e2a8b3bf201c56e729aca715609c8804b269d0d26a14c72e8ca2034327d22bfb52c9e8a3cf952eea6202f9a96a798359b9ea910300197ce82a97b158f63788349e9875991507a10d22957be297f5a9134bead7496824c0ba05a4542a19de929ad38a8bf284140f91810267b9ed048a02e2225a292c0a0bcfa6243c091324a54fa11cddb66618e19c169f268178b22bf6158e4cdb86339db1131a25be689c07c83963a2c517f60411ca60d506ad55ba9ac5a92bce20ee668f5456476b565da296f6ef8cd81eb0c98d109dfab4e9addcd56284b5ce2f55f8e562a50d66f2ca89227b845deb6b348b9734b63a45388b6862dd14ee69fb3f395ca2eaf1db5dc25995dd5598035bb84a12e0b4dbd2d6e93413483bb6c8cdb8b7383af303ab8b56af7132265b08434e60747195d2282e93c12c5443696507a2d44e8353641b84d49e14e4ac40108014284d87364a3e2a8bb5935ec62d2c2288d527d4177e8c907b4a5ed539a9c3d8c9581d02517df5c88f921540ae5084818feae9750269d455809b368b40a9eb41391c95879d9e00c62a5b2836dc688814a229e3c659bee2455bd994b77d4a9c6ed633020e1889733ac7ad4ca776f411c3124220f6298bb291ae388e152219ecc4cc0d9a305e44c20c00a0b2e2a7f1943bcc10374127dca903e4054dd86803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1395 : walk cp1395 moves1395 = last1395 := by decide +kernel
theorem result1395 : ValidCode last1395 ∧ ∀ i, 1395 ≤ i → i < 1495 → P i := by
  have h := walk_sound moves1395 val1395 (by decide) (by decide) (by rw [checked1395]; rfl)
  rw [checked1395] at h
  exact h
def cp1495 := last1395
theorem val1495 : ValidCode cp1495 := result1395.1
def moves1495 : List Move := [⟨[],[1070,942],[241,139,881]⟩,⟨[483,1100,1338,521,483],[269,1017],[684,942,1194]⟩,⟨[],[940],[333,1279,269]⟩,⟨[],[1171,1209],[1096,1124,876]⟩,⟨[],[30,640],[473,423,353]⟩,⟨[],[1027,863],[442,1030,30]⟩,⟨[],[264,1040,878],[467,695,281,713]⟩,⟨[502,71,355,899,1073,1285,1302,1150,645,1360],[57,367],[392,1158,1036]⟩,⟨[134,713,713,713,1077,1247,918,892,134],[906],[1361,1031,57]⟩,⟨[462,676,1362,1275,544,462],[1301,1217,227],[504,666,1106]⟩,⟨[],[820,122],[105,1321,295]⟩,⟨[854,869,965,947,1267,854],[1375,1447],[1196,816,986]⟩,⟨[],[436,1444],[239,603,809]⟩,⟨[],[355,81],[1348,1286,526]⟩,⟨[],[558,742],[753,1277]⟩,⟨[],[1033,1283],[470,760,848]⟩,⟨[],[474,278,420],[1157,739,1159]⟩,⟨[76,1244,1244,504,504,76],[],[600,1498,194,210]⟩,⟨[609,646,646,1046,1005,761,339,297,567],[1044,568],[535,1175,1475]⟩,⟨[1262,487,58,1189,1189,1189,805,931,61,674,615],[925,561],[532,298,334]⟩,⟨[],[544,668],[1083,1023,1481]⟩,⟨[1465,182,316,634,1030,474,37,500,521,1341],[747],[1390,178,1036]⟩,⟨[],[],[969,699,1269]⟩,⟨[1361,1078,277,277,1078,1361],[499,981],[136,884]⟩,⟨[1324,529,1094,723],[30,840],[1125,107]⟩,⟨[],[73],[212,736,30]⟩,⟨[],[1064,1284],[941,1355]⟩,⟨[],[1355],[662,990,786]⟩,⟨[1051,853,462,498,1289,93,895,164],[1160],[1195,185,121]⟩,⟨[],[953,347],[454,738,774]⟩,⟨[],[1262],[427,1189,1201,855]⟩,⟨[],[1,1335],[150,494,1484,1180]⟩,⟨[],[670,702],[721,503,1]⟩,⟨[1416,160,139,20,926,792,1101,688,205,307,152],[999,1331,793],[320,1146,1124]⟩,⟨[126,126,303,303],[462,324],[1403,389]⟩,⟨[],[197,475],[366,1090]⟩,⟨[],[1264,1366],[471,41,1375]⟩,⟨[342,355,1382,1094,988,140,1329],[891,245],[76,306,1182]⟩,⟨[1148,115,115,1148],[466,476],[437,967,845]⟩,⟨[601,623,1097,1225,545,1209,1265],[407,17],[1262,564,156]⟩,⟨[],[1408,876],[447,1247]⟩,⟨[],[1,859],[586,1002,556]⟩,⟨[],[708,1530,1222],[31,1375,1]⟩,⟨[],[425,697],[1504,950]⟩,⟨[984,1410,1410,984],[910,1284],[1055,675,425]⟩,⟨[],[501,579],[522,424,640]⟩,⟨[344,116,1315,848,176,1375,640],[640],[295,867,609]⟩,⟨[1,69,1102,1102,69,1],[1345,917,737],[14,460,1204]⟩,⟨[],[694,1452,1370],[1355,47,1199]⟩,⟨[],[1453,1455],[710,496,682]⟩,⟨[63,775,908,1315,252,668,781,1270,1039,566,412,63],[528,816],[1321,57,609,1543]⟩,⟨[],[963,491],[698,356,1294]⟩,⟨[],[1342],[161,1497,977]⟩,⟨[],[1035],[4,80,442]⟩,⟨[],[698,874,868],[377,5,989]⟩,⟨[],[475],[1224,212,148,262]⟩,⟨[],[48,658],[1511,933,599,197]⟩,⟨[],[875,1217],[160,1456,48]⟩,⟨[],[214,650,736],[687,1357,1151]⟩,⟨[1447,1434,299,1525,567,312],[649,1407],[1152,214]⟩,⟨[],[540,1026],[481,469,963]⟩,⟨[],[143,209,1361],[904,458,338,474]⟩,⟨[1159,263,263,1159],[348,740,1450],[619,467,209,143]⟩,⟨[],[893,53,981],[664,774,1320]⟩,⟨[],[1312,152],[107,1,777]⟩,⟨[760,1424,1511,706,241,71,142,463,1014,5,359,720],[1489],[1472,778,476]⟩,⟨[],[1360,214],[1171,1141,533]⟩,⟨[271,1233,652,652,1233,271],[959,643],[854,472,414]⟩,⟨[],[414,1414],[703,1103,933,1233]⟩,⟨[1,1551,791,1324,1],[399],[156,532,736]⟩,⟨[27,1468,305,889,410,30,303,250,1310,255,27],[916,550],[463,439,781]⟩,⟨[],[599,677],[408,828,724]⟩,⟨[454,185,185,454],[42,972],[809,815,337]⟩,⟨[],[379,599],[76,1458,42]⟩,⟨[1397,642,884,1425,804,559,559,1190,1120,1489],[1256,1538],[1197,1193,345]⟩,⟨[],[693,903],[876,1242,662]⟩,⟨[444,571,1342,1185,983,353,1001,1092],[1494,1498],[667,975,695]⟩,⟨[],[303,1411],[942,590,352]⟩,⟨[],[194],[1299,995,1159]⟩,⟨[],[1247,587],[696,266,194]⟩,⟨[],[786,518,302],[1009,1309,631,1347]⟩,⟨[],[1131],[414,874,1030]⟩,⟨[1258,891,780,1551,813,9,1163,24,1257],[478,722],[893,523,781]⟩,⟨[],[601,1375],[644,478]⟩,⟨[],[1514,1064],[219,611]⟩,⟨[1007,1243,57,486,1514,490,137,719,570,934],[553,31,397],[98,52,932]⟩,⟨[348,197,197,348],[228,1266,1202],[359,893,1469]⟩,⟨[],[721,1483],[514,970,228]⟩,⟨[],[924,218,1312],[935,1069,965,1247]⟩,⟨[],[971,289],[376,588,1208]⟩,⟨[],[258,516],[1193,1407]⟩,⟨[],[107],[828,980]⟩,⟨[],[894,112],[947,1163,107]⟩,⟨[],[159,975],[66,1490,798]⟩,⟨[680,308,1528,1319,929,1552,1301],[610],[1011,555,431]⟩,⟨[],[497,1209],[852,578,486]⟩,⟨[],[88,36],[857,1283,921]⟩,⟨[],[1147,243],[1092,924]⟩,⟨[],[1376],[155,1505,1061]⟩,⟨[],[1207,453],[562,978,372]⟩]
def last1495 : PathCode := ⟨1595,0xc170d217c3ec371a3083002b08df642f0e1321ac54e69fb6332ba991ee2b57161d5e641d30f1a99327eb8d329ebd29376214f636d02e969cbd0a45eca963a492f0586480c9b901e1860f4b3a01e1d4c65949182f03215ed4499b961561d8e52ffb44a8aa399d3ce3c90f51b95265c26df31e253c3541ab556ea6b16a4af3883bbca4ec43881c0d707199ef5223843886baad72743ac13df564e38198ae21641a4f4c3acc8a83d0869154eadf881c208d2ae28db6f1c9e91d245d85945cae0c4909672d68c6cb4f18f62f64a6180e0a228a20c5aca9b50e4088fa2a891304d984f1e95fd2a86f7caefac249d259d7052324bc9a749b21281ef11ae6c521c44b3861122104e3b153080108308a8e557e1887109a668374a5a6dc16e138fa99cad2a66976d70e174ae0b50965b8c328aceac6b6fcd99e9b112e6758f5a994eede823bb9c16a593d1479f2a5dd4c405f222c4b32bbaab3006b7709425e86a2c32b7ec22ccb11c36eb297f1257fcc8d00020ce46387d4b90d40606dba685a91dd642631ae596eaed13a299512a7645b78910307e5683c1461184efaa59d76964216d42f5e538520948ff4ae3b49da2de51102344db941cb631401815bd53092f02a0250d78993d8956d67ba51ded0a7418ef1a61fcd0f0f1cba32f9eeec4c8aaa3cd9587a123a2d4990462f00f208db66618e1b06b373d4f7a110c12c0a0d505e9272945018c01a6c45080a264ed33bb85c5d9f1a0e604e3e5a8149f965186977adb7dc768f74329aeeca10572a8300cf83326c128171626b796341e444cde5951244f70a9be2d2c7105d40dcac93167fba2c44cfe8293b6923e08c927534d5c754ba3af6e5a38b92567954fe026bf50a413c218501ead3a6b773558a12d738bd557be297f5aafd42f1c207ee95277b2d81701a4a80191eeb07a7a073121153f765407a957f86a24c0314e6275b1b810ff245540685c228daeb877653bd2535a71517e508281f3662e645d1f85d5879ba6accecc714b8b38dd648bb70d02a4bc69701786c1a0dbb82d7178114004424a46c270c25edc0e86c82a9791177033292d04981740b48a81835fef28ff6030e06c4cc6f02210e475589601f0de3a2ccb961a4d889476b9df1bc056625b9e7366f90183d3a8cf1821c50f6d1a7f2ebc2a33d98ac00a01005094339a5f1041086f8da26e034c195609cdab1cc20cde827a65578edaee6064fa59bee2455bd994b77d4a9c6ed6330383dda88c30ad12de4d46e1640d4ce8b507a1943695112c4f02e98a15d1c60744cb6110610434151056ad7b94fe88b2ab55c988cf1e6c0663459e312bf6158e4cdb86339db1131a25be689c07c8394dfbe51c90b1deda42800a44d9a507f116f2205616b995f52bb9c1ca094ee8e7875d3be9a2e5e8951af6c2b7c5299b03d61931a21c460752a53cb7ab90500a463a19dcce2b7fcfad0330a90c34c073f22ce2a8e3abd4a765a7d2ef8955ea57c517317256c1f17676baa5a9e4e55dc8d36a9b40dab75f6a07635ea3bc6fb31f1926f1b4b9dd561a8ec38dd0c48970a05dfa32c2505ea55af9c338e3f546774dfe088b8090a44985107221bc2ad9c6c92155a05c2696c23cc28262b3cb95c78c463e811e225c05a158597d04a2b4bf8491125784a0a48c811ccab51d56c9b1da3545996d835158d521e1b56b6b948dbf5a161397d9892a0ac06a0bc0111f2d693727507d8d28a50d86e6f422c0e0e4ec2ac728bf6499ad9c8c15059b6876d554e3a42d97362e33444b711400243db7f0ca4acafac90b02619b0ae2f4d7b18b4b08a23549f50641e0d5287c128ba037255ca698c79b072a299f0353d9d596587ebe827a55bde0091f4fb02a55048214720602126050776d919b716e77b959c31a60f42fa0f05a2b4d1eb675b389e0155f6856fa9de29c2eeb5226005420e0ec970a42342449687e2e7c30a43482c62c4ddb64b5f1641bc50a7fca559a85416a37e213915c490439b1619971b0e4967d80d8494b76395b1ce3e647402555476b565da296f6efb03423a7c94899012c5c2d911aedb6904080284b810111e1484f38a23427c97b10e2f1461961e605d565278386b4ce08510a8fdda4d4ce9ffd62b2f2497f5a332d16e52a3f134c9d3ed1308c2ea07a822fd30ab3d923fc2984f0433fa5311c408932bddf6cb45b95a260be01d229d6ed0c45b04deb02a8b48de56a8c80a0f1a42a9bf0264d3a59100110fe2cd0f8f158fc71c3f6c9495578da3b092a5f86437a3db15bd77992f0eb97375c869cc371762c62049c152523b1225f82b1b3f336323c1d10a39f706019569d4099752ba8fe705a7c9a05e2c9694677055f839a66016de53c0982f34606c998b42a8c8f32382c3e88bbf9a0e775e3bc96367d5d7d515e7274fa11c7e98d66222034327d22bfb67d14a87ada46c02af3a021449b99b0132fb451f6458ad8cd48644d7ee7ea9f901c70ca58bd8a20f02460124041880e4cc84e35e10c5d165e556c78b11277f9e34db9d369ea90ee0ad7a9ed5262d6c652014470b4710e8879a4dca3ba6d0d83f543a8976e4483f2cb26a4f06a90fa62f3efac346b9234b262c0ca9d1982c1530d67041e15d06709ed5469aa924ac0c7091949fb456983d60db1e3e53c9a943e80cccdd8d4f2845899146e8674b98b4d379c62e0cd48b62ec148611aa6bc5346397e06d26ece717b4d3180b4098dd667a151889302c5e84034e0d64e52b7779f305b2bd4cd2ea6c8f10a55d945b3f3c6381d0712ade16c7458a2fec082394c668f5456c74fbeb911f243860e89b324cd79714577248482fab1b273f57661482b5317c149be0c42403c484b812462583d32a1a0c4faea71312a1f555398d5c467475744a36c2307e1d638d30671a8f21b992f62f60050597153f8ca1de6081be096b13b20a0707a274d9e8c329c48d134bead77e5e5d359e8d4058071b9e9d507b4a5ed539a9c3d8c958200958a733c2d05591cf7f6ea32c6cb37e10bc83b83215e105c68174423006800254dba51383366b88213e8ea5551a88ea7679d3691c95879d9e9160f8a91f7b333dc0c84b6ec2282b82294ee7431801,0x431b9d94e0882b88a6ec12c0ccf7b327dca903e91767879a5691d4da79a9d88f46a5523a13e20a6b8cd138e954d809680c004205dc684155e0c83b8f2210cdf6cacb2ea5fd1cf566d04f0a7256200d608c90f5a9d4e5ecd2907a75b9e1c4583509e94d5e5df9ad72f91312329c30d9e9d37a21c20a4ec6b18241b9821de3293fdc5058016f63d899286e8f1c6306e35d61f8230db04a55d747118d5ce655487f129c4aeb13da0ca83d29624660484af1240310be05257c54c82b851764fdb26ac42fa1272515d7135e24c6cce8e1824247eb93efc75158f519a94c08ec08bf58b1d216ab7712742384f1b3e5155dc298f09b12ed332bc16df35de2b7394d65384037a02c24c18885667b750982d31853417b39e6e9b47e18e5342f1aa7845483b0b635220c98b79d34d8b52e8671b99116228553dd8b3380d0f9a94f23e4c7a0d8f5698d149fc657090324aaa469b5509e99c5d078704359530b05982740cb8b0b248d6b90d2fabcfa6243c6a93c26ab2c3f11276ea25438fd0d89b63bb729a421d0ed1c70a511203192d7499ed5ea0ac3baa95a79d336de35fe1262c6c795565f7450c5784e3320e4e200404906040920f6298bb29c704069f9fa7ef13486335ad9161f65142fa04d9b26e14480af380a46cb6a87c5267cfed22c9f342882626357e8470fa49d5e7545d79f5636f25e39dda0efe48b8fa82cc8c8f2a3b426606cd182f22613c37901699839d7e70519d690b205f269a79c18feae9750269d455a01dc139e4281d48f362fcf1b60a25ec4923d499c0812c65d837073086dd79723ad2f5e6bd6c563d8de86497c928ec8db55d495b2c3f1c58fbc50f8b34fe044100964d3899bf0aa5a403c80aa3256a378b40a9eb41345b4316e8a71d2f8260d685b92d1f6af79330211c14c3fa10c4f0a63fd64ab3cc22fca0a078ba08d44d3eb271348fe52c5b32d68d7f492b2f589ffb3a4d576a8fc420853386b60e52755a0587919651a2f44397a9f2346284f25211e404b80a1080410b68bb5118b6c5c04899252a7d08f033be6f68a65dad54775540211d3e67395b58e4b61240d9f6496c3971866b170e4905713918863785a855668a51ff50a6f16457c64b76ec4b1848290c30b9f7e25a2448d0a425c0ec838543801223adc2f8a69ddbe68557e016275b2d9d1ead35a23c2fa3d0a610c559dee6e6dc519db6077816121807208504815402b3ed1f002bde95427afa87e595d5cf603467ea2c1c79a630a6957372e81289f052983641d4149e8d48a52c18b5eef4ab89b0984b0324afb2b0ca5fc3da091405c444acd22e5cd2d8e914e3558766d905b059c86b649afd728ab0ec039c0f08a6f61b50ca298d41f2744ded6c7c0102f06a2b02a06257d84ea16fd48dae56b66d61e3541580d56d9663547689b55b51d2ad1cb20a4928178449490fe2b49287d01661581625c78a8118f8c571cb92cf2630a23cdb02681715a4856c96702a86f723440982910902e208b7f77551a3f4e39c36bea5417c248c9dfa81971121d08e38ed869d52e71b49bf194c76faef1ea58da077dab70369b4da88d5774e4a7aa5dae7667c56c5c973114657d7a894bbe7d5964a6af4e38aa2cefc8070d390cc29033eb7fd8adcc86763a290502e4b7b4f12a01dc4688531d8603c66c52adf6c26bc9517aa2efa5d3e1d8e73ba09072b9d4ad5f2e6616816f244507e6944d829281691dec2c1c8f94df8e57c87026896f1a244ddb0ceb873358e5852bf8c45998dc06798cf26255caac8b3fab94b5c56d44340411065844ca1d1c65748a0ba4f04b1510da5941e8b513a0d4d906e1352de34430a231dae0f30358c6eaa77d52dd9956f244fba5993e606bb8edd5ea6409cde8831cd6ac9cd58c180d26e3686f84210417c39a50c508400a0b01988cfc2abae7f3460f67158233c3a80f5019be736e7a25959bc17c6b9d1d88893561b2ea2d78df0d805891d50e0886f13306c4386023fef2d7f1822a0b4dd0981412928cc77044697a0a86d039edb092711b24a110400047178b5bb8836c1de17011a64bc0a70c2ed64e378b252cc733b6ac6e9879751f9176e65981f20a250c5f714d69254ef764e1dae8a35c21a1544910fee05b189d4e60c64c1a87f8a5407d953f64571201ca7ac1dee864a80691703607b349ee901f1c30befd56a97ef8957af57384b58a4d5b76e9aad407184f0a415426bf8094f9e52562e5a3db93af2e87535753449c8c8f86924ee82b3fc44e8a7fcc5ac8371d44412c78b69bdc244f44a59337445079632de6265c5281b03333e300aa0572842eca6b4323dc76df7ada5dd86d949f80525ab8f604839f197685ceeed31930a3422c40698c14069449c5e9540a0cb00c0844f7cf5b36c18e1986b66234f23c0462642d48e8a1361cd928f8ab132eebe7a3272f0f3431fc698ef5060a77b6519ee6d62553de260d60942a4bc308f54158063152d941b6e34440a510b79daed0ae3fd9494813857942e5b6425a59d6a94efc61460f05681f9030245b7d912a654629c4eaec5bae58c642775a91a16ba61b4064354b81f463b39021400c8dff1245feb28db11d32c22dfb32a8b286897094ddc06accbaacac4b08b5f3101d4a979f251d3d296c16ee423b7a4eea64f59d62e6c45e9b666fd1aceaa2bc336e0962d4ae05d30e5b5696a98ad2678fb84c169b7a5add2682697106217e3958a80c010c201538ed04c88610ce044c876c46baf120721326da72f2324149d749649cb0aefdf286f4a95fc7a84f36530224a2a23e40d43a9b6b20c228a22382181292f63d8f1b2d8c6b59672420c52b945e1645c749e9472b6ea36ae234c20206dfd3a9142183d22aacd30e4f1062162b819b8e564f7ec150e726ab46b8e2385489ef4667070348190e4ecf283bce24ae5aa6b5bab550683514f1e37cc2699795346d0f0f23ce676a3aa2b44bfce5076156e5899b5115e0c82f24659531a1d007b3a3d186078b90326481612f092563b2a45f429cba5a02edb4f60853774a5ebccab8c9f99346a30f075e6075716ad5ee2642bb8cdfb39ac5486a133c364237eb0c0008268c370fb17c34817003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1495 : walk cp1495 moves1495 = last1495 := by decide +kernel
theorem result1495 : ValidCode last1495 ∧ ∀ i, 1495 ≤ i → i < 1595 → P i := by
  have h := walk_sound moves1495 val1495 (by decide) (by decide) (by rw [checked1495]; rfl)
  rw [checked1495] at h
  exact h
def cp1595 := last1495
theorem val1595 : ValidCode cp1595 := result1495.1
def moves1595 : List Move := [⟨[1537,1504,1359,1359,1121,1425,1391,333,699,1275,1349],[1472],[275,1353,793]⟩,⟨[],[1441,417],[1494,1374,398]⟩,⟨[],[1540,750,1138],[1393,1301,923]⟩,⟨[],[1153,1377,1499],[954,758,1550]⟩,⟨[],[916,1412],[545,273,1181]⟩,⟨[479,1476,1476,479],[671,991],[832,1292,644]⟩,⟨[],[608,304],[1141,1455,1583]⟩,⟨[],[353,1541],[636,1298,508]⟩,⟨[],[1122,1276],[741,131,1381]⟩,⟨[],[1517,791],[972,666,512]⟩,⟨[],[884,8],[1345,1053,247,963]⟩,⟨[],[733,369],[26,552]⟩,⟨[431,431,582,1353,1500,345,1191,457,635],[1102,334],[947,729,647]⟩,⟨[1521,1184,1576,1471,867,1204],[895],[728,260,288]⟩,⟨[],[18,704],[1215,157]⟩,⟨[],[1,1411,445],[1042,626]⟩,⟨[],[1412,1570],[929,407,1]⟩,⟨[],[83,55],[536,1454]⟩,⟨[884,1132,617,653,927,920],[186,1570],[1559,1233]⟩,⟨[],[85,3,1425],[964,1416,104]⟩,⟨[619,161,1067,663,663,66,497,155],[628,138],[1229,1175,607,1563]⟩,⟨[],[641],[222,450,1386]⟩,⟨[],[414,932],[1123,347,611]⟩,⟨[],[1565,1513],[698,694,678]⟩,⟨[519,21,1030,1010,692,724,1253,89,575],[354,714],[1237,393,929]⟩,⟨[],[1027,1277],[78,1344]⟩,⟨[1127,446,1031,566,720,813,1062,1492,1306,1584],[126,770],[1075,723]⟩,⟨[],[1145,585,1357],[712,126]⟩,⟨[],[934,244],[821,697,1267]⟩,⟨[],[311,1423],[100,598]⟩,⟨[1558,1305,1305,195,195,1558],[624,142],[1501,143,1441]⟩,⟨[],[453,1161,1325],[1580,648,684]⟩,⟨[],[356,1032,264],[829,869,761]⟩,⟨[792,1254,1426,1062,332,970,944,1141],[889,785],[1512,1064,546]⟩,⟨[745,499,499,745],[1364],[1515,1255,1099]⟩,⟨[],[1487,799],[1532,1080,1490]⟩,⟨[],[1452,622,586],[867,821,859]⟩,⟨[],[403,1343],[12,1084,730]⟩,⟨[81,1285,1285,419,778,1151,198,48,153,983,1161,186],[1130,140],[945,709,491]⟩,⟨[],[921,157],[340,1122,1500]⟩,⟨[],[1540,302],[317,457,971]⟩,⟨[],[1207],[336,1066,1266]⟩,⟨[],[1102],[255,1203,1565,1127]⟩,⟨[1078,106,386,431,189,1487,708,1538,746,1154],[155,409],[142,60,1038]⟩,⟨[1179,1138,1123,1219,701,1493,1550,1033,868,1524,102,730],[1452,1554],[115,73]⟩,⟨[],[1605],[354,240,1296]⟩,⟨[448,80,1291,624,1080,1172,336,204,202,18,676],[1008,644],[899,475,565]⟩,⟨[1,49,645,647,1],[647,497],[446,562,238]⟩,⟨[],[1212,910],[59,669,883]⟩,⟨[447,1635,1635,447],[191,1101],[1208,1176,1240]⟩,⟨[],[158,712],[623,505,627]⟩,⟨[],[1391,505,1097],[1454,974,158]⟩,⟨[],[772],[563,267,1077]⟩,⟨[561,1134,1042,1183,992,63,1175,383,672,936,1145],[1167,1605],[666,268,1474]⟩,⟨[],[1182,440],[649,625,1295]⟩,⟨[],[307,1243],[36,1420,612]⟩,⟨[],[586,132,58],[293,1507,665]⟩,⟨[],[809,71],[122,550,574]⟩,⟨[],[1232,922],[23,1083,791]⟩,⟨[],[591,761],[662,882,334]⟩,⟨[],[848,194,994],[915,445,1357]⟩,⟨[],[1157,1331],[368,1652,672]⟩,⟨[],[1430,824],[183,73,745]⟩,⟨[],[1655,1035],[1082,518,666]⟩,⟨[],[558,164],[881,791]⟩,⟨[],[1469,1547],[1646,164,650]⟩,⟨[1652,525,82,1656,1447,1447,1447,716,1167],[1466,296],[1635,711,1405]⟩,⟨[],[591,219],[1338,776,828]⟩,⟨[],[828,844,454],[1301,759]⟩,⟨[],[989,81],[994,516,226]⟩,⟨[],[1018,554],[551,815,465]⟩,⟨[],[847,1255],[320,762,1108]⟩,⟨[],[226,230],[175,1087,353]⟩,⟨[],[543],[684,188,832]⟩,⟨[],[572,92],[187,1571,965,1485]⟩,⟨[],[1535,939,1379],[192,158,634]⟩,⟨[473,1413,1452,870,473],[386,104],[435,119,1591]⟩,⟨[],[],[70,1302,670]⟩,⟨[249,1443,1535,669,648,249],[492,1258],[1105,1455,71]⟩,⟨[238,1125,1610,1391,1391,238],[1,923,365],[1486,464,594]⟩,⟨[1124,1231,1208,1506,1182,824,946,1246],[1646,1438],[1243,1315,1]⟩,⟨[],[1545,393],[1642,1144,138]⟩,⟨[1224,648,717,1113,689,1427,1179,869],[],[895,43,291]⟩,⟨[1012,1397,1397,1012],[1407,1055],[98,960,158,1648]⟩,⟨[],[1414,278],[737,571]⟩,⟨[],[585],[580,250,1388]⟩,⟨[],[734,1218],[1489,255]⟩,⟨[156,1271,1084,685,281,593,1363,1511,1370,156],[601,1345,887],[1202,338,1086]⟩,⟨[84,899,1487,1162,1447,1532,84],[500,362],[1437,1511,1211]⟩,⟨[],[431,1579],[590,950,1198]⟩,⟨[],[82],[1443,1001,1351]⟩,⟨[],[1351,533,685],[1674,1554,82]⟩,⟨[1153,1260,934,858,938,213,963,1129,1172,1074,352],[1588,674],[1281,173,229]⟩,⟨[],[607,611],[1360,832]⟩,⟨[],[492,1610],[1561,1677]⟩,⟨[],[1415,349],[774,370,1142]⟩,⟨[],[102,1164],[1081,437,397]⟩,⟨[],[397,945],[1662,1644,102]⟩,⟨[],[1608,1008],[19,409]⟩,⟨[215,595,63,242,76,606,804,761,341,325,1612,865],[1587,537],[330,1276]⟩]
def last1595 : PathCode := ⟨1695,0xd1ea47a9204280191bfe248bfd651b6fb89156fcc5778adce53580e1a60f583751a3f1266bd99a7f2ebc2a33cd136e5072d8c50060279f8b5c39caf969e7df5869971e698cb5a4dc9d41f634ddc25097353a6d033eb7fd8adcc86763a290502e49595f5921604c33608c927534d5c754ba3af6e5a38b9b0e6c947c55899775f3d19891921be4c8393880101241806c4040f8098dd6c58665c637a3db15bd77992f0eb97375c869cc371762c6204c80b0198e938ccf7a911c21c435d56b93c6257cbd2c76548be853974b405f3d47f57591825cc59fee8b1127f1943bcc1037c12d62764140e048078df361b6527e01496ae3d811c715459df900e1a7219855f6a07637225fc3da091405c444acd22e5cd2d8e9342dbb9aa83d3adcf0e273c8503a91f66a1505a10f349b94774da1b1ea82b1ab33d0ae8c0b17a100d8f2aacbee8a18af09c52c1e9950d0627d753898950faaa9cc6ae233a3abb9d242c1ca8a67c0d4f67565961fbaac351d871ba14079055fcd1380f90729bf7cb012e028437a09e9955e3b6bb981d419078354a1f04a2e80dc957d2519dc157e0e699805b7999623b2b57bbd2ae29890f32b7ec9f4b366d43ac164f95546a23a9dcc60b8690becf65b851b5dccebe827df1bc056625d16bc6f86c02c48ea870444412c78b69bdc244e3a453adda188b609bd605516ab55fa85e3840f902d1c2ac3b22ec2ca2e57062484b3abb44e8a6fc4b4489ce07519e3558777b98912fc158d9f9d0d459591feca4a409c2bccb067231f394f23e57deb69773326c1d4c405f2e601489baad02c3c8cb28d17a21e4da2efa52bce2d0443881c0d707306b42dc6c8a36dbc727a474a5fbe255e449dba3a5ad18f4b20b7cc16caf5334ba9b23c4295779147a59d00f0e847b323bd41829ded9467b9b5bce317066a45b1760a4308d535e29a31cbf0368930624e0d08181089ef9eb66d831c34fc50ce697c41042344161920326e40786184d50a0902a80567da3e005a3ea148278430943cb2a2411dbd64a134c9d3ed13ca26608644d7ee7ea9f901c70ca58bd8a20f025f02609b309e3d67f0cb8b0b248d6b8cd6b64587d9450bee6c9f02b1aa39030109302a9c7ea46e92d045cad6cdac3c811566d04f0a7256200d60b330ac2cbe82502f2eab2b12c22f033be2172657bbed9681715a4302525ec7b38e0662b93119e3cc4a8d7b619c7386d7d4a82f849193bf5032e16c1f17676baa5a9e4e55dc8d36a9b40dab71cbcf2ba0ce3bdb485006896f5224c288391d305440c1f99306a1fe694d20b451fca58b665915e19b704b16a5702e9872dab4b54c56933c7dc260b4dbd2d6e934134b883108e59052406ab6cb348bb3c3cd2b48ea6d3cc58893bfcf198f3736e28cedb03b18b4b08a23549e306e84c00a0a25b44dc068114323dd60f4f40e4ad46ec8a37433a5cc5a69abd4a765a499ad9c880008e2f16ab3c98c288f36c09a4703a028637e213915c7300d9a305e420069b114222ce375922edc340a92f1a5c05e1b07939edc0e86c82a97911770332e282c00b42dcb5cb18c84eeb52342d74c3692344d2fab5df97974d67a350542e7e8118f8c571cb9677b921dde52766f68a73c0199ef9b57a550283062d654da8720531a21d005a4b81d966e88a0f2c65bcc4cb8a500433bd2535a71517e50e584925e3389d367ba1e6edb330cbfad1e9da698c05a29501f654fd915c48715efab290ed88d75e240e4264db4e5e4648293ae92c939615dfbe4139d93871fa39efedd4658d966fc21790770642bc11a791e02315be294cd81eb0c6cce8e1824247eb93ef7f57296b8ad0e9272945018c1a64a82b0ca07d24eba7c3b1cea8af329c30ee752b57cb9985c2e2ecf8d070320bc9196537611415df563fc02a815ca10bb29ad0c8f71db2df2125f86597ab98314e6275b1b2e036058e72b6b1c96c249f72a40fa8de491e17d1e8530862acca6e9c0902e208b7f77569e74cdb36c64ed32fb3128e0a62f50a92f1145111c19661bd2ac75158f519a94c08ec08bf58b1d216ab77132ed6aa3baaa0108e9f32ad3a97fda2aaea4ad961f8e2c7de287c59a7f0220804b269db4b283d16a2743b9c16a593d1479f2a5f348d0a4390dc087f922aa2ce3051f7a56d58e61079852014470b4710e9e365ba5f46c03b834e2466045f8e54358257384b58a47c128db08c1f8758e34c19c6a3d76ec4b1848290c8349e9875991507a10ceef37356375a2b4d617c534eedf342abf00b13ad96ce588a154f762cce0343e6a4cfe82e5f10a7b1b6ad397a9f2346284f25211e665308d149fc657090324aaa469b5509ee53122dbec8953c7b80c9b55b51d2ad9f3fb48b27cd0a209898d56587e92565eb13ff6749aaed51f88410a670d6c1ca4dd6a44c00640584a932e135460bdcf81a06e1fd086278531feb2559e6117e50503c5d0461fc69899e5d6080321aa5c0fab300695c7699d6ae234c20206dfd3a9159bceac6b6fcd99e9b112e6758f5a994ee729a307b6124e236494221000209a343d318959e553f809afae14f026326585639336e18ce76c44f3ece7b523a284e5b112ce1844884138ec54c20632de0f0e086b2a63345697f092224af07e847192d7c5906f1429ff295a7cd283f88b791028d4a3b11126ac3382d3e4d02f164b48971e25ce36937e3298edf5de3d4621201e2425cd6099751df54b3aed2c842da85ee91be736e795154733a79c79647cd4768d53af0a37bd2aa74660b0480410b68bb5118b67161d5e618d8c90f5a9d4e5ecd2a7d2ef8955ea57c518a15d1c6515448496660d8870c047fde5aff94a53b9d0c78b8091324a54fa11861d076f69e25403b88e6b5bab550683514f9442de76e0cab04e5444b13c0ba5d46815c0692a06911518f22a105c6817442300b42a8c8f5c6994f5e949bb61c92cfb4ee8241c837855276d26505f0292be2a6415c28bb27ed9356217d093928aeb89879751f9176e65981f20a01e405d178993d89515ed45a05611bec85e1c264358a9cd3f6c66575323dc56b92c4cdf81d91b6de34430a231dae0f30358e30a30782b4004a9b74a27066cd710427ea90ee0ad7a9ed526c7d14a87ada46c02af3a021449b88b2ab55cd0f0f0220dd9d945286c3737a11607072761563945faa9c6eb2382c3e88bbf9a0e775e3bc96367d6a21a0208832c2265859351b85907a22cf4321b992f62f665407a3932a99428b67e78e7383a61e35326d3c52cc733bd1301ead3a62d549decb60cc97710693c690aa418001,0x4182a96904f106ddccc8d81ecd272d4e9aad407d12cecc714bd3cc9a3518783b9ce78d9f28a6532a8e407b952f63d899286f430b37a3641b84d4858996c220c208682a21f5636f25e39dda0efe48b8fa82cc8c6eaa75fae51561d807381e114dec36a19456760dc08b0f34355caac8b26e14480af380a46cb6a87c52c7d499ed5ea0ac3baa909f10535c6689c74aa6c04ad07828c230d6330383dda88c30ad12de46d1d97e04ce4b56af713215dc66fd9cd62a435099e1b211bf585a035115e2553de26d170141e0281f3662e645d1f85d587ae28aee490905f56364e7eaecc29056a62f82937c250349276154378728253b8fb24b61c6ee94bd79957188f2a3b42c004205dc684162a63c151a46a01a45c1a05d42e93c12c544139ab1832768b794453c3541ab556ea6b62303a9529e5bdd0618611d3e4a44c80962e0c6e7653e52aff7947fb0187036266125449455c65748a114657d7a894bbe7d34a5ed539a9c3d8c8635e60757162d911aedb69040802c16609d12adef0a2ebcd51dacd591c791e733b51d5139e7366fae92172db212d2ceb54a77d75026cd7095e2480620f51de37d98f8c9378da5ce788972d21640be4d34f382b0d26c44a3a35102de488a0fcd2e9f2947fd429bc5915f19291c7e8bc224a487f15a7342986b3820f0b7863308054e3b4132218433811396e848e8b5339f3e91376c33ae1ccd639617260984f0b85afe0253e79495cc643c68c20c00221252361386121eda31ca4eea64f59d62e6c45e9b666fd1aceae6f9154eadf881c208d2ae67576857006acc0fa9721a80c609974999a61fc1185d40f5045fa61567b247f85309e0867f46e068cf82f54604d32f2a458190c00911d6a93c1c35a6704288547eed26a674ffeb15979241f965e35988880d0c9f48afed9f4ab51d56c9b603c7a54ec8b6f12394c9ed5469aa924ac0c7091949fb453099951e1484f38a23427c97ab4db69ec10b97e82b3f6a50fa0333376353ca11626ceb6713c02abed0adf53bc5385f4d68a374d5b373bb10c1e91556698727883243482c62c4ddba3c718c1b8d7587e08c36c1291f18a12d73809435b955f981246538b8300f46e9765a78d0ed1c70a5112066110639ad5e951f6c16ce2a89221fdc0e43a4234334a979f251d3d296c16ee6745a83d0ca1b49a74b2200221fc59a1f1e2b1f8e387ed9292aaf6897fcea2ac7cc8e804aaa8ed6acbb712ade16c7458a2fec082394c668f5456c754aa1be591c1445144bc0a8bd4a6238312beed319336d36e74da7774dfe088b8091a70a6ab38634c1e85f41e19268d83e2a47dc24a5bb1cad8e7016036cb9b189d4e60c6b9e5e86497f214b71da3dd0ca6bbb28415caa0c038fdf5057114dd9652460bc0c9073e32ed0b985ae657d4aee70c329cbcea8c73c3ae9e4e9f4ca0ac0a86998c14069449c0e82b56bdca7f4fbeb911f243860e89b3b0c078cd8a55be8c5e01e411aaf0641dc7910866fb65659752fe8e71fae1dd904ebe577d6124e92ceb8291925e4d3a4d90940f788d736290eac9ef9c5c48454fdd9501ea545a630a69a76d1afe30d6ce6ee8767a74f3897849396250c5f714d69254ef042940b8b135bcb1a0f22266e764b8169d0088531c81a87536d64182835417a66d9ee0673c2296f69d9e5077b939dcb95c78c463e8139f542d427a5357977e6b5cbe44c48c36dd342d48eeb21318d72dcb50b00a0b2e28cc77044697a0a86d039ede4eb07785c046992f029c30bb5938de2cd08b101a420179a3036730571391886378a13a11c09a5b08f30a098acf16b8bc08a009c86b649d964a6af669b16a5d0ce3732246f2b40e53d60ef7432045069371b42890a1302e80c149e8d48a52c18a0eedb2336e2dcd8f3c6bfc24c58cf3a6d2392b0f3b3d22cb32db06b49190239310e2134cd06e94b4db82dc271f53395a54cd2edae1c2e95c16a12cb71865159968b72951fad1d21a51fe1a89307e40c151d30e46881305225bc68940b48ef4ce2e8cf272eb70369b4da88d5774e4a7aa5dae7667c56c4b8502efd1961282f52ad7ce19c6d84d792a3cc679310ae066e387b17b2530c15a05c968fb57bc99216efb0308b12ccaeea8bc250fa02cc2bb3358200958a733c2d05598110f0dab5b5cb4129291b7eaa7302c24300e41aa0ac9f19b0bed147d9162b63356b9234b262c0cb9fe3d4279b2981f040920f6298bb29c704069f9fa7ef13486198ca344d3eb27135929bd047a252c9438c278520aa168f0048fa7d8152a82410a1356181e2e40c9920587441084105f0e69434fc70d8359b9ea7bd08860d093806224c368fc31ca685e354f08a907616c6a4419316f39b59ee9477b429d063bccc847c3a00f6747a6455770a63c26c4bb4ccaf05b7cc82f4b4635ac8e9db91255ef8a5f9d27a51cadba8d6c8b72b44c17070348190ed053892bbe9a2f93621c5e28c32c3cc0baac26c14b985f3101d49b03325deb6df73e53cb390c76732c2bca70a41291fed64459435f9e36c144bd895ee876d559e1d4ce1224b43f18a713abb2ce48418a5728bc2c8b83b0abd1c4080f8e185f7eab545a054f5a09a2da18b74538e944f70a9be2d2c71044421c8eab12c03e1bc745a25959bc17c427afacced745196ecf62f86902ecc6a7623d1a95593ec150e66d2cc9f5fb32a43e98ab8bd35ef2b08e996de405a660e75f9c1467d2455cdcba04a27c14a60d90750581aee3b757a9902737aa12e04047ca6fc72be43813455fe41406e8471c76c34eaa1f9657573d80d19fa8b07242e74abae8e231ab9ccaa90fe253895d627b419507a52c271af0862e8b2f2ab63d00de80b1a310accf1aa0adea86c4db1ddb94d210e16a1559a91e0e8851cf0e373d3aa0f9ab6ef42ba42d97362e33444b711400243db7f32258da077d9854861a6039f916715471d8138f96a0527e59461b7cc789200e105276358c120dcc10ef1949ff113a29ff31425e465751ff3d0174b4e5e8522f654b1cbd15fc62e4d568d71c470a913de8cda4d98ac0c80812c65d837073086dd79723ad2f5e6bd6c563d8de5c619ac5b750983e0041b118049010620393321be648891465f3ddd899155479b2b0e2e5a3db93af2e87535753449c8ccd84c25819257d958b90500a463a19dcce2b7fcfad0369b35225c2537763507c9d137b5a631e6e5c8697d5e7e5acaf0e4b5e7e026018c54b6506db8d10cfc2abae7f6666bc49a3f5468363d5a6038359394adddecc55bc913ee1b7594bf892bfe64680010a9291d1e803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1595 : walk cp1595 moves1595 = last1595 := by decide +kernel
theorem result1595 : ValidCode last1595 ∧ ∀ i, 1595 ≤ i → i < 1695 → P i := by
  have h := walk_sound moves1595 val1595 (by decide) (by decide) (by rw [checked1595]; rfl)
  rw [checked1595] at h
  exact h
def cp1695 := last1595
theorem val1695 : ValidCode cp1695 := result1595.1
def moves1695 : List Move := [⟨[],[852,198],[1623,1053,647,1407]⟩,⟨[],[441,689,1295],[1192,900,544,1092]⟩,⟨[],[1440,944],[599,441]⟩,⟨[],[5,1409],[840,570,1608]⟩,⟨[],[708,944],[393,1491,5]⟩,⟨[],[361,447,705],[16,1458,1396]⟩,⟨[],[566,1662],[353,1297,1143]⟩,⟨[229,246,753,1301,152,685,1614,762],[559],[1448,1318,1346]⟩,⟨[],[1358,926],[989,991,559]⟩,⟨[],[803],[828,1542,1016]⟩,⟨[774,1490,961,1232,1374,755,1078,728,1335],[470,42],[1075,1665,535]⟩,⟨[],[549,395],[1068,1100,582]⟩,⟨[],[1448],[475,1407,1637]⟩,⟨[],[451],[1156,1320,1588]⟩,⟨[569,1203,615,194,194,1574,569],[944,1446],[593,927,451]⟩,⟨[],[639,697],[1648,944,940]⟩,⟨[],[1312,80],[713,1041,1479]⟩,⟨[],[1041,337,293],[414,850,870]⟩,⟨[1653,1155,211,504,916,1017,276,622,450,1655,380],[1406],[919,981,1533]⟩,⟨[1533,1708,336,134,1422,1697,1331],[1025,1119,641],[54,1276,774]⟩,⟨[],[692,1364,1520],[345,943,1037]⟩,⟨[],[1185,541],[1710,194,1092]⟩,⟨[],[564,1334],[869,1683,977]⟩,⟨[],[995],[564]⟩,⟨[],[868,1282,2],[477,159,19]⟩,⟨[],[355,1083],[216,1066]⟩,⟨[],[1066,506],[437,81,289]⟩,⟨[1031,1570,686,704,416,46,437,1521,1479],[587],[292,670]⟩,⟨[],[1550,902],[347,699,411]⟩,⟨[1387,96,821,353,1695,633,523,455,689,644],[1,1509],[14,910,1020]⟩,⟨[],[520],[1715,241,229,1]⟩,⟨[477,1082,608,1441,891,645,860,1461,477],[299],[1674,1572,1526]⟩,⟨[],[180,1310],[1113,1411]⟩,⟨[],[713],[1258,1050,180]⟩,⟨[214,611,1394,1039,458,252,214],[1442,932],[685,1697,1503]⟩,⟨[],[657,1419,1263],[1182,22,30]⟩,⟨[],[1324],[835,709,665]⟩,⟨[755,379,379,755],[1705,1081],[538,812,656]⟩,⟨[],[1590,138],[1311,863]⟩,⟨[],[511,601],[430,888,280]⟩,⟨[],[30,472],[209,385,1663]⟩,⟨[],[171,1699],[776,1254,30]⟩,⟨[1414,1490,1490,1414],[792,748],[1299,901,931,1515]⟩,⟨[],[1399,819],[264,1324,820]⟩,⟨[664,930,666,62,1099,1319,71,453],[1002,726],[1255,379,1651]⟩,⟨[],[1505,403,1437],[1280,1400]⟩,⟨[1400,1047,1149,899,1165,1113,627,651],[958,1182],[1085,1327,661]⟩,⟨[],[969,225,883],[456,434,678]⟩,⟨[],[30,894,304],[1041,367]⟩,⟨[496,402,250,1441,1351,688,1604,344],[291,641],[1558,1574,30]⟩,⟨[290,1209,293,1351,290],[1076,1456],[853,503,425]⟩,⟨[],[955,517],[1110,946,1686]⟩,⟨[],[110,590],[1621,1727,1729]⟩,⟨[],[905,1507],[992,774,110]⟩,⟨[1176,473,1066,705,409,504,223,361,361,1628,900,601,468],[1256],[1281,869]⟩,⟨[],[85,1591,1255],[328,1606]⟩,⟨[],[690,1036],[1203,665,85]⟩,⟨[],[1411,321],[1112,162,110]⟩,⟨[110,352,166,1610,372,1264,571,1714,107,1295,49,503],[448,1038],[403,859,519]⟩,⟨[],[645,1571],[1060,1030]⟩,⟨[],[1486,1432],[227,1153,1571]⟩,⟨[],[197],[1722,1402,1488]⟩,⟨[],[524],[977,687,197]⟩,⟨[],[205,1017],[578,984,532]⟩,⟨[],[792,512,408],[1215,859,205]⟩,⟨[],[1,549],[1450,484]⟩,⟨[],[516],[951,1751,1]⟩,⟨[],[1073,1243],[1062,1226,1580]⟩,⟨[1309,112,879,807,1020,943,112,1309],[1038,1460],[973,765,1451]⟩,⟨[1406,1157,548,1222,369,232,660],[1],[338,640,1010]⟩,⟨[1710,360,638,960,689,414],[1636,1304],[1221,1075,1]⟩,⟨[],[1453,1483,81],[1030,1430]⟩,⟨[],[524,394],[293,1379,1479]⟩,⟨[1447,1736,1736,1447],[467],[756,468,424]⟩,⟨[564,1233,856,1629,875,1505,1605,815,1180,1700,340,1544],[1762,86],[697,1261,353]⟩,⟨[],[1,939],[636,1472,1376]⟩,⟨[],[208,154],[391,1]⟩,⟨[1739,1567,683,358,1319,1669,1669,450,73,485,1359],[1119,915],[878,1756,1356]⟩,⟨[1690,755,1519,472,472,1502,1552,1345,810,159,485,186],[792,926],[765,473,1523]⟩,⟨[1054,647,1630,575,122,214,1074],[803,417],[374,122,1346]⟩,⟨[],[966,518,1574],[863,165,1253]⟩,⟨[],[1007,725],[1442,604,1752]⟩,⟨[533,772,1552,1117,1276,149,16,574,1318,400],[84,684],[415,1353,921]⟩,⟨[],[1759,1431],[1738,84]⟩,⟨[],[1130,72],[967,761,1231]⟩,⟨[],[913],[962,810,720]⟩,⟨[1182,411,957,737,1001,92,510,355,1455,928],[432],[851,1339,239]⟩,⟨[764,1382,512,257,1103,852,1600,462,47,1223,1420,94],[1583,965],[1622,1714,970]⟩,⟨[],[440,690,1106],[1081,1133,633]⟩,⟨[],[657],[182,1144,1402]⟩,⟨[],[1726,506,1500],[497,651,1193,877]⟩,⟨[],[429,1191],[718,582,1344]⟩,⟨[],[222,1760,1276],[137,1425,441]⟩,⟨[],[867,79],[1480,1460,1148]⟩,⟨[],[938,202],[1543,1077,263]⟩,⟨[],[399,673],[142,810,658]⟩,⟨[658,1184,1184,658],[1600,878,242],[1391,507,1553]⟩,⟨[],[741,1579,1461],[1414,1470,1606,1198]⟩,⟨[],[1198,1606],[787,967,741]⟩,⟨[1486,813,1280,956,1224,1046,1351,926,411,996,1611],[653,1191,1237],[204,262,1634]⟩]
def last1695 : PathCode := ⟨1795,0xd6b23a76e44957be297ee14a2240cc220c06accd2b6ac736aab2c94d5ee43cdcd58dd4d710427ea90ee0adb8d0eb87d45bddcc86763a29212e6b04cba8efaa59d6095ce12d6283b236dbc688614463b5c1e606b1c61460f061413159e2d717811401390d6c9381d0d90552f2238a37e5b56963d9e9b112e6758f5a99d908e2d8bb05202012ca2bc336e0962d4ae05d30e285378b22be325238fd1783509e94d502640dc85819257da27944745a99cf9f63e094d4ae120649554838288a283b1066a405c968fb57bc992178b96912e3c4b9c6d26fc6531dbebbc7a8c41c087f922aa2ce55d747bb71bac9176e1a05497d9bb31e24804227be7ad9b60c70cc32feb47a769a630168a5407d953f64551a150d3318280d289381d056ad7b94fe9f7d7223e4870c1d1ce73c6cf945328f17323607b349cb53a6ab5b9ae5b96df469db4b283d16a2746112fee474c1510307e64c1a87f9a53483348b9734b63a4d0b6ee6aa0f4eb73c38b132e3b4ce7516bc64069f9fa7ef13486198362300920200b2fa0942d8d1216caf5334bad1c5cbcbbf35ae5f6a61269f65e0545ea530e257589ed07744e94a0b0198e937fb29290270af32c19c8c7ce53c8f911eb8dbad3b3ca8f59fc32e2c2c9b835cd87a12621c42690e10533e0bd518134cbca91604264dcc61bc36df712253e79495be5809701426ddd7961106104341510fab1b7929dce50a70f48aab32de58d07911337a1a4cf5b18e297a799327e8cd269a79c1586936226b505e2c8495ff3234000854948e5e963b2a45e1d5c58b6db402af3a02144c7e38e1fb64a4aabda25ff3a8ab1f323a012aaa3b5ab2edc4ab785b1d1628bfb0208e5319a3d515b1d52a86f9641c26c8f10a55de45dbe5961fbaac351d871ead5690c268374a5a6dc16e138fa49c8c958dd90348190ed0538b77c75136ab95591605d98d4ec47a352ab27d8217c10a2151fbb49a99d3ffac565e4907e5978d662220343a8e973169a7bfad9cddd0ecf4e9e712f09272c4a18bee29ad24a9de084518a18df884e43485f15320ae7b2dc5adaf6669fd7ecca90fa62ae3548e7bfb75196365d88c004205dc684162a63c151a46a05505e99b67bc6a30f0776e6bd04e6f52190693d30f50e83b7b4f2440d12dea47680149f9653564b8502efd1961282f52ad78e2385489ef17b412502d23bd338ba33c9cbadc0da6d36a2355dd3929ea97bd4d64e52b777b3156fda204f3f47b012b4234b80bc360f276d68474f929132025b48e790a15ed45a05611be717127001d289ee11773326c1d4c405f3b2c37676514a1b0db469467b9b5bce31781612180720d536addc41b0cc931b3b0c0781161e6869866c6f9660b07501a45c1a05d42e93c0183424e018848078df3d7c3484b84a6eec6a0fb71466298ff592acf308bf28281e2e8230fe34ceccf88b37a3641b84d48596607ccf8159a374bb2d3c6306e84c00a0a247db05d7f7caefcb15104e6ac60c9da2de515ee876d5575e15d3853559c31a60f42fa0f0c9346c1f1523ee1252dd8e56cf6d328abd1d00b13ad96ce588a154f76257f18b9355a35e1ce57cb4f3efac34cb8f34c65ad26e4e9a52f6c158d9f9af14d18e5f81b4498234f23c0463420c4afbb4c64cdb4db193000209a343c88d76db4dfa51e7ca97cd234290eb0892921fc569cd0a61acc90da8734be2089b8c369be2d2c7104ff94a31f18ae3972cef7243b8cd66701a1f11b7eaa7362c9f48afed9f686437325ec5ecca80f68e4a83d29600ce789d8d6304c201538ef74dc80f0c309aa14120553783a037255f4946770440b73a7a52d82ddc8884a27c358d8f4037a02c68c42b33c6aa744ab7bc28baf35476b356471e479cced47544e79cda561e7bd9672420c52b945c59200766dba8d6c99806c86b72abf30248ca71706018c6d948d8a70c3b9d4ad5f2e66170b8bb3e341d35add5aa8353995521fae233f60a3f94b16ccb07b6124e236494221b6405b7999623b812c249d25a05d56276d26505f0293bec4aa7bc4da2e0283cd50504140681b87f75260d90750581aee3b757a990728253b8fb24b61c6ee94b78459592966380107725ab8fe0223e653d70d453cc54b6506db8d13271340a9eb41345b4316eb6365c06c0b46e6448dc1d48fb350a82d0879a4dca3ba6d0d8f54158068fd51a0d8f5698e6014c18b59536a1c814c6887401692e0b46b98314e6276aa13dca77b429bad489800c86b4a3a35102de488a0fcd2e9fb42a8d131230db74d0b523bac9bb79b9d94f94abfde51ffba99fd05cbe214f636d5a72f53e2946bb99d7d04fbe3780acc4bd5cded14c682781f52e435018c132ebcc31b1921eb53a9d859172131fa2f2eab2b12c22f033be3cc67869c866157da81d8dc897f2b42dcb8a331dc6d85d9851a6a577d345d3c948479994c234527f19715bfe7d681b4dda59085b50bdd237cd4ad704313d418ef33280e8e59052406ab6cb348bb3ca99cd12fd74a9d7eb945594f583bdd0c81141a23daa64fa59b36a1db0d80c381b13309281f1c30befd56a8b4b7c5299b0ed5eef4d102606a77c5b93af2e875357535b1ef53daa4d8fa29107812f81304d984f809afae14f0263265182f210034d88633aaf7733b10ceecaab2fba2862bc27199072710224a2ae32ba4508a32bebd44a5df3e9d3e1d8e7bc5cf92a35ed8671ce1610ce200d60b33a9f794727a474b67e551c95733abb42b87b5b61183f0eb1c698338d88c0ea545783203e2cd3f81106eb232c2da1be648891465f3ddd899155479b29bf085e407919651a2f3e6417a5a31c9d3e9941581d4ce1224b43f18a713abb21a84cf0d908630c24234433cacb9b0bed147d9162b6335de8271d2a9bd8d97a1925fc85b8b5bcad0381205c4116feeead3e2a37f496822e56b66d61e408ab36827853935711b59d1ebb76258c241060aa6fc099c96ad5ee2642bb8cc58cf3a6d239816c2a1eb69b337e8d675737c8aa756fc40e10253b0012280b888976db4e5e4648293ae5c619ac5b750983e2562e46b92376be4d886a84378554383d2ce80787595b67293c1c35a677037ed429cba5a02f9ea3fabac8c12e62cff7458893f8ca1de6081bb12d640c82f246594dd8450577d52dc768f74329aeeca10572a8300e3fdcb7322e8fc2eac3d714577248482fab1b273f4a1c161f493d1a914c4bbfc48b6fb2254f1ee0326d56d474abafc1cd332f3aa2281d0a03c82afe689c07c839615dfe78cc79b984ea16014166b8dc357da15bea778a70be9ad156d81d8c5ce92160e54533e06a7b3ab71c0cc572624ce56ac5317653040f0e0811396f64bc73bb41dfc917765b7b5dd85639336e18ce76c44e6f422c0e0e503de235cd8a43ab27bf929bd047a252c9438c278520aa168f0048fa7d815589601f0eaf62b7aef325e1d72e6eb90d3986e2ec58cadb7de8100e7e459c551c78f36c09a4703a1305c1801,0x5c1cc13a11c09a5b08f271c551677e403a815f7adb632ec1b8398436ebcb91d697af35eb62babdf0d805880567da3e005a3ea148278430943cb2a2411dbd64a7beaca43b6235d78903839c0f08a6f11376c33ae1ccd6396175dede76445dfcd073baf1f64e5b113820f0c10652c5ec515a4ce9885703371ceae7b01a33f5160e485ce83141ddb6d15a6b0be29a776f9a155fdc3ae016005a16139b9b1e78d7fa158e57c870268abfc8280dd08a0aa2bcd33073afd2ad4755b26d80f1e953b22dbc48effc4a4511aa4f1f5058a1cfdb26ac42fa1272515d7130f2ea3f22edccdcb8ff00aa0572842eca6b4323dc76cb77d415c453765949182f032d64c481b9821de3293fe227453fe6284bc8caea3fe7a02e969cbd0a7edc0e670d6c1ca4f6765687401ece8f443815437aa18879376bc8d6b8b92560f8098dd6c58665c6eb8291925e4d3b6da25b88a00126c025384040dbfa7522b379d58d6df9b32daa1fb098148ea6d3cc58e332ba991ee2b5c96266fc2a90609058c589bb747b59c463574e6785a0ab30221e1b56b6b968252537f8aad3bba6ff0445c0480392b75bee2c8497e1965ed8ca6dd289cde8cd6b64587d9450bee6cacacf3441080c218d90bc384c86abb44e8a6fc4b4489ce0751586503e927631e96416f9a2f1461961e5e44219be6c947c55899775f3d19891921be3682c2c8c6e8443f8b343e0c85789500ee2338c60dc6bac3f0461b61ed2b8ed33ad5c1c9957679d27a51cb796a7b3358200b3861138671b6135e4a9cfef18e7875d3cfa5df12abd4af8a3142ba38ca2a893101c99909c6bc218ba2cbcaabbb10ccef776ab633620348402f3463260984f0b85afe0284f365303e081241e2963ea4cf6af56c7534d5c754ba3af6e77c1a9261442f4d7b0ec66c52adf8b55aafd42f1c207c92ccc1b10e180ec3a1ccda5993eaa68f41a0450c8f7583d3d558e517eaa7d744bdcd2a6b3d22cb32db06b4919023980ecc8ef50613c10ed735237d7490b96d9096974da067d6ffb15c6527ed14c26654785213cd177d295da6e145d9b61dc0ccb8ab72b45fcc8963681df66152186999e3ccefb0308b12ccaeea8bc1fa84d17616a9cd4e1ec6431af332eb040190d52e07d2791a114b7bd5d12cacde0be213d7d6676baa513e4bd5a6db4f6085cbf4159feea1ff796bfe5294ee7779a6ebad48d0b5d30da48d132a3b43a7cd283f88b791028d4a3bad0c8600488eb429dedca64f6aa09d4e60c6b9ad12e05a7402214c7206a1d4db5906014b986983d60dd468fc01815bd50d89b63bb729a421c2d42ab3523c1d2376451b80b01b65cd8d6ed0c45b04deb02a134c9cd136e5072d8c514f0d4f5e6508fe02e3e5a9dc0118e296564458de2949bb61c92cfb4ee8241ca9955e3b6bb981d41907837521fd1b81a014141d500f202e8bc4c9ec4aefb2937c25034927755a05c9649cb0b8108e996de405ed9221252361386121eccb45b94a8ff608cfae287d554e68356aadd4d641cf8cbb42e616b995f52bb9c30ca7236d9431a01dc1a71233022fc72a1ac6ce606c8a36db9d920116545cae0c4909676f61e6959cdb9e54551cce9e71e591f351da354ebc28def4aa9d06accf42ba302c5e840363f589f04a2221dce0b52c9eb7390270519f49157372e83781541208509ab0c0f172374e3b15308304b589d99e00ca583d32a28e03dca97b1ec4c9437a199f3fb48b27f62a9c7ea46e1f4066663343bdc9cee5cae3c6231e528ffc412c78b69bb0d9b8820be1cdda9241aca98cd15a5fc248893ac2908d0cd2a5e7c947dfb6d176a2343c68c20c0019336cdb193b4cbecc4d08462f00f208d4986d1f86394d0bc5f9e36c14bd9a513a26f6b4c63cdcb90d2fabcfcb595e1c8d755ae4f1895f76353ca11626ceb6713c02d1c2ad32bdb56d6392d8493ee5481f51bc923c2fa3d0a610c55994dd3985575b558777ba510b79db832ac1395112c6efdf2d7ec147da890a1302e80c13c6cb74be8d1593e07cd98859351b85907a22ccf8bb334c3f8230ba81ea08bf4c2acf648ff0a6466dc60fb1a6ee1284b8d2d7d7cc78920189383420603c0ba5d46815c0693502c1661be66c2616878781101eb0c6cc9343341b7736ab5472060212605316f39b59ee946d1b0da865159d8376cb5f3101d49b03325dee12271d3c03121c51bf585a035115e428e7ed20244c92953e847b5b27583bc2e0234ad00131ef3f013da35bf315de2b7394d66f5a96a7939577234daa6d036adc72f3cae8338ef6d21404125edef52238438ad7d4a82f849193bf5032e3565949f8053682912de3464453cb7ba0f50cc393c419219bd04faf76e41d30f1aa7be6d5e9542a06911518f22a105c6817442300d88d95965d4bfa39f54ab8a6243ccadfb9fd999af16b2dd9ee0ad4c5f0d20e46218de284518219de929ad38a8bf2872c2492f19c4e9b3dd0f376d9efe9a6c5a976a3342882626355961fa49597ac4ffd9d26abb547e2104217d60b27caaa3511d4ee6305c45955aae1371d777ce2d0443881c0ddd85608c9278fb84c169b7a5add268430569ab471c76c34eaa1f965dbf9155dc298f09b01c65986f4ab1d4563d466a53023b022fd62c7485aaddc4cbb5aa8eeaa80423a7ccab4ea5ff68aaba92b6587e38b1f14480af380adb42d9c587545eca96397a48f524085003237fc490b205fad62224d586705a7c9a8cc9f99369e29663b5b133a1acdd1141e58cb7ab322a0f429ce5277792c6cfad4434041106584d79b75425c0808f94959e553e489f70db1bd31a4d9091612a4cb84d5182f73e4140e09a5c4188a1361f5cee02c98b032e7f8f4f293b6ebb8c478f94f2ce431d9ccb0af29c2904a47fba4d98ac04a13a77434189f5d4e214c5ea1525e27d127a9a5f56bbf2f2c5cb474bb4ccaf05bd12b60943e80b2080920c03626608644d7ee7ea9f901bc7458e76d32e2c4c38dcf4ea83e6adbbd0ae90b65cd8b8cd3486947f86a24c1f90305474c3912ff846745a83d0ca1b49a7df4e5ae5ee6ab4e98b55277b2d83323c5328516cfcf1ce67470c12123f5c9f7bfab94b5c568749394a280c60d325411a1153f765407a951698c29a69db46bf8c31c360d66e7a9ef423201e26ccd9b25e05386176b271beed747576ce2a89221fdc0b107a8ef1becc7c649bc6d2e73c44b96962e2172657bbed968172a44193b08a2888e054925606384d4a2523e67d9cf6a474651a275f592160dc9901025359e8d41783f4238c96be2c8378a170e174ae0b50965b8c328ad2c880520ec2d8a38d90a64f59d62e6c45e98f66976d77e6282234bd0543681d24cd6ce4400047178b559e4c6143c1461186b1981c1eed4461856896f2368ec6284b5ce0259d6a94efaea04d9ae128a463a19dccef7d44e1d0eee30ac3baa909f10535cdd356cdd90d5ea53b2daa8735abd2ab3006883cc2900a238597ef895791276e8e96b003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1695 : walk cp1695 moves1695 = last1695 := by decide +kernel
theorem result1695 : ValidCode last1695 ∧ ∀ i, 1695 ≤ i → i < 1795 → P i := by
  have h := walk_sound moves1695 val1695 (by decide) (by decide) (by rw [checked1695]; rfl)
  rw [checked1695] at h
  exact h
def cp1795 := last1695
theorem val1795 : ValidCode cp1795 := result1695.1
def moves1795 : List Move := [⟨[1,638,1616,853,735,1643,856,790,1],[398,1014],[707,673,1213]⟩,⟨[660,660,903,36,488,707,763,1303,1012,1451,1120],[1,347],[1538,734,1278]⟩,⟨[],[836],[1209,385,1]⟩,⟨[],[317,345],[1276,466,1784]⟩,⟨[],[282,1468],[821,805,1487]⟩,⟨[],[1191,1743],[698,1398,282]⟩,⟨[],[1286,1266,592],[1785,1053,1237]⟩,⟨[],[633,1503],[200,1288,1700]⟩,⟨[],[232,1240,184],[1475,83,341]⟩,⟨[],[1713,311],[1362,1598,380]⟩,⟨[],[1528],[507,601,1643]⟩,⟨[844,347,566,813,1584,679,1254,113,1176,1221,989],[953,1535],[1610,784,1784]⟩,⟨[388,188,1341,1539,1804],[1748,28],[931,329,199]⟩,⟨[546,649,212,1007,1520,170,170,676,264,843,214,300],[199],[1184,1716,86]⟩,⟨[],[378,1492],[741,1289,491]⟩,⟨[],[1,317],[1788,1558,694]⟩,⟨[],[694,1558,298],[1347,163,1]⟩,⟨[1365,115,1403,1003,928,439,1689],[1599,339],[1024,332]⟩,⟨[],[1424,236],[1347,405]⟩,⟨[],[1059,575],[1630,1812,1110]⟩,⟨[648,586,586,310,1597,1436,1774],[1580,276],[1123,1407,833]⟩,⟨[833,1623,917,211,1327,154,266,1305],[1407,1301],[1548,1328,1514]⟩,⟨[],[1582,1396],[943,865,1645]⟩,⟨[],[1,1159],[1728,940,266]⟩,⟨[],[200,502],[1537,193,1]⟩,⟨[87,67,1559,17,249,1818,1477,660,994],[131,1379],[372,1658,8]⟩,⟨[],[1748],[1269,1393]⟩,⟨[],[1357,207,1273],[1132,1142,686]⟩,⟨[],[1752,1586],[759,1299,671]⟩,⟨[],[1815],[972,416,1012]⟩,⟨[],[8],[115,1685]⟩,⟨[],[63,781],[1214,492,8]⟩,⟨[],[1266,1816],[273,385,1433]⟩,⟨[],[1687],[540,284,1122]⟩,⟨[],[752,968],[1189,281,827]⟩,⟨[],[163,1529,853],[42,1394,1178]⟩,⟨[],[1372,30],[153,151]⟩,⟨[],[1773,1287],[298,1342,1530]⟩,⟨[],[966,1528],[1319,581,1629]⟩,⟨[],[1823,259],[94,714,1264]⟩,⟨[],[816,450],[1723,1451,523]⟩,⟨[],[587,151],[1332,1632,1746]⟩,⟨[],[1556,648],[265,1069,1595]⟩,⟨[1719,183,1263,586,1515,301],[1409,211],[966,340,1558]⟩,⟨[212,766,766,212],[1518,724],[859,41,1195,1135]⟩,⟨[],[],[470,6,1620]⟩,⟨[1034,1078,1078,789,1439,1811,1337,686,1033],[726,814],[503,1399,779]⟩,⟨[],[159,49],[1488,1374,888]⟩,⟨[],[216,894],[923,991,975]⟩,⟨[],[975,991],[760,502,216]⟩,⟨[874,1617,1617,874],[],[1479,673,1175]⟩,⟨[],[1151],[1290,200,1008]⟩,⟨[418,459,920,1266,820,1281,1278,6,1826,1834,597,1009],[1122],[149,913,1235]⟩,⟨[218,1455,1261,437,166,782,214,1725,1586,1227],[1329,991],[374,12,1508]⟩,⟨[],[854,302],[773,1595,595]⟩,⟨[],[891,1057],[1306,1144,1710]⟩,⟨[],[1246,42],[1817,767,1617]⟩,⟨[],[1617,353],[92,1150,386]⟩,⟨[],[1010,1818],[29,1121,1685]⟩,⟨[],[445,63],[854,90,1454]⟩,⟨[],[1588,188],[1335]⟩,⟨[],[253,347],[930,1006,548]⟩,⟨[1637,1580,587,1400,292,566,1031,1373,1835,1331,918],[1022,228,236],[1007,159,1225,1327]⟩,⟨[],[1437,881],[1042,1456,182]⟩,⟨[],[264,1560],[37,275]⟩,⟨[],[1669,1741],[38,168,632]⟩,⟨[],[106,32],[151,175,643]⟩,⟨[],[901],[1710,694]⟩,⟨[],[562,1218],[545,617,841]⟩,⟨[],[1743,365],[1486,1244,1352]⟩,⟨[1682,1319,1744,1316,1004,1149,1824],[390,1812],[447,23,1345]⟩,⟨[],[193,23,1539],[1184,1188]⟩,⟨[],[6,768],[915,159]⟩,⟨[1726,801,1476,187,1112],[785,45],[166,1058,6]⟩,⟨[681,93,231,863,1022,509,275,1468,354,1637],[1030],[391,595,1657]⟩,⟨[],[153],[1210,788]⟩,⟨[],[90,338],[323,503,581]⟩,⟨[738,1771,1771,1174,1174,918,267,1847,1196,281,485],[725],[476,542,90]⟩,⟨[1789,1067,940,211,532,774,1798,354,749,977,1615,1745,816],[644],[1601,1823,1001]⟩,⟨[1538,50,50,1538],[1653],[74,156,726]⟩,⟨[],[524,234],[1193,669,575]⟩,⟨[],[817,455],[174,1126,1022]⟩,⟨[],[442,1636],[1327,1475,1473]⟩,⟨[669,1187,413,821,686,568,922,1762,1530,1605,1874],[1795,1761,53],[392,1072]⟩,⟨[],[950,1848],[961,87]⟩,⟨[],[937,1355],[1200,1152,1386]⟩,⟨[],[678,1316],[499,103,1179]⟩,⟨[465,1623,395,565,1780,1643,773,1032,799,1777,112,1358],[1223,5],[332,410,310]⟩,⟨[],[900,1350,682],[629,325,929]⟩,⟨[],[1,563,645],[1814,292,1744]⟩,⟨[],[1744],[1431,113,1]⟩,⟨[],[25,1315],[1232,696,450]⟩,⟨[],[924,700],[961,1515,25]⟩,⟨[],[683],[1488,354,710]⟩,⟨[],[234,1276],[1417,1013,1819]⟩,⟨[],[1819,811],[1828,1268,234]⟩,⟨[],[312,894],[7,1217,73]⟩,⟨[],[1359,1389],[1182,400,1850]⟩,⟨[],[1666,1694],[241,31,367]⟩,⟨[1404,1404,1120,1834,458,458,1266,1240,834,1607],[1607,9],[1472,1042,1838]⟩]
def last1795 : PathCode := ⟨1895,0xc1e92c5a9d572258da077d9854861a7c583d22aaccb796341ec16a593d6e7204e0a33e922ae6e5d02513e1ac6c7a01bd1cf112edb69c95b85ab95418071fee5b991747e748ad2fe124449d619d31e953b22180f02e9751a078c3117a63d9a5db5df98a088d2f4150db9775baad4ea4566f3aae13529fc59a1f0647213bea9675afeb47a769a630de8cd6b64587d9450bee6caca36df7122e45bbb55b19250fa02ce38a5959116378a526ed8724b3ed3ba09072a65578ed9e633c5cb3bdc90efc6693bd96c0b83a4d68bf83a02e27d9794209c46c9284436c80b6f332c4770258493a4b40b20b8d02e884601b13a673dbce8085131f8e387ed9292aaf6897fcea2ac7cd6b4ba3af6e77c1a90761579db558766d85db45e96eb82973ebcc97875cb9bae4376e4f53de846403c4d99b364bc0a70ceccd30fedd7718b99d68366257dda63267c679d3691cc0b6150f96ae3f80f0f56b92c4cdf8552ac3281f493b18f4b20b7cd178a34ab51d56c9b60331b971e698cb5a4df86d332bc16d94b175b4d99bf46beccffb15c6527e29612180720d536addc41b0cc9301eb0c6cdf8c5389d5daf74a216f8b69bb0d2696c23c9c7e735e1c41887a22cdc73ab9ec068056da16ce2f82b24afb44f28a509d3ba1a0c4faea710a62f50a8db4f671404ae7096b141d81f52e435019cb431b217870990d74783a61f8d2472f405a158e57c870268abfc8280dd0f588182f7960647bac1e9eaac728bf553eba25ee695359ee267b5b6285378b22be325238fd1783509e83f6ca49554838288a283b1066a46895b02b27c0f9b310b39c10c89afdcfd7679b309f0135f5c29e04c64ca305e420069b11ca4bc1980433bcd136e5072d9f5a06c7d14883e324de369739e225cb4b1710b932bddf6cb45b97159d886a3d76ec4b1848328cf736b79c62c17663e6cd69c545f94396124c9b2122c25499709aa31da15c01b1ddb94d210e16a1559a91e0e80be7a8feaeb2304b98b3fdd16224fe32877a5a72f429fb70399c35b0718206ec4b590320bc9196575fe548dc6c86b72abf30208d3c8f0118db8c328ad2c880520ec2d888f994f5c3514f315c5c1161e6869866c6f9660b07501a4b2a03d4a8b4e6b99016f0c4ab7bc28f3f444cdcc92f219f5c50faaa9cd06ad55ba9ac838658797910866ff611107a65451c1aa813206e42c00c3b02c9c6fbb5d1d5db38aa24887f70240e06eec2b0464506f02a9a556646db79351b859040029212e6b04cba9131230db74d0b523bac9bb79b9d94f94b69012e4eda5941e8b513a30897f723a60a88183f3260d43fcd296b2a6d4349ab0ce0dcf4ea83e6adbbd0ae90b65cd8b9c22d4d50a81a445463c8a9c41c014982078704089cb7b25e39dda0efe48bbb2dbdaeec2b1c99b70c673b6226ff716164dc1cc004c7bcfc04f68d6fcc435e1ce57cb4f3efac349983611c6c85327af5b18e297a799327e8cc3cf7b2ce48418a5728b8b240374dc80f1b051fca58b665a0749335b393ae334d20b46b98314e6276aa13dca77b429badb69bf4a3cf952e5a7400b97977e6b5cbed4c24fab2d397a9f14a35dccebe827df1bc056625eae6f68a63413cca97b1ec4c94e14825219c77b690a0704581785f197685cc2d737432034fe42c1ca8a67c509183f0eb1c6983cccd78b596ecf7c7b030de98cf6d328abd1d00b13ad96ce588a1417e9a9dce53464268bb0b54e6a70f6323e00c2c8c6e844ac166753ef28e4f48e96cfe82d3e4d076af63140e224a2ae32ba4508a32bebd44a5df3e9d3e1d8e7bc5cf92a35ed84b4489ce07530ae9c29aace18ccf42ba302c24c368fc0085003237fc490b205fad6227206121ec24e9bb4b211861354282417a66d9ef1aa1bd2ac7515b872b6b1c96f836936635c0ba61c23a012aaa3b5ab2edc4ab785b1d1628bfb0208e5319a3d41587755213e20a6b9ba6ad9bb21abde0ec8a37492b2f589ffb3a4d55ff9922f654b1f1ca685e2fcf1b60a5ecd289d24a3ee5481f51bc927ec8aa342a1a6630501a51270846886792b75bee2c8497e1946fc42721ee2642bb8cc58edf2cb0fdd561a8ec38f56ab4861341ba52d36fa374bb2d3c65996dc09337d95625800e2c4cb8ed339d45af1be1d5e0d6925d565625845a191ee3b451916556aba7168221d60e86933023ca14e6c593e915fdb3e437a18851cfe62a4f677429fd7ef22abb8531e13625d68e0091f7237ac0a84d3276d53681b56e66701baf63b15308304b589d99e00ca581036ff097120fcb2f1acc444068751d2e62d34f7f5b39bba1d9e9d3ce3ace231aba72080920c0363d3e413c218429d348708299f0b6a17ba46f9a95ae08627a831de66501d1cb20e1332138ae8cf272c3adcb72dbe8d3f599cf9f63e094bfb75196365b36c18e1986e3765b550e6b571faa354ab5e8e8033bb2aacbee8a181f00a5cc34c071965844e19c7d76e3c6231e528ffc412c7b875c02c00b42c2737363cf1aff04288547eed58a2b499d316ffc4a4511aa4f1f5058a1cfdb26ac42fa1272515d7130f2ea271d2a9bd8d978198ae0e75fb99c9e987a8741dbda792206896f523b400a0cde381d056ad7b94fe9f7d7223e4870c1d1ce73c6cf945328f179a1cc371762c656dbef408073f22ce2a9332f3aa3bbe3a89be9c6c947c55899775f3d19890d217c54c82a771bebbc7a8c401ce0784537bb10e2385489ef1324a54fa11ed6c9cdd8450577d52deeca6b5dcc0ea0c83c1ba90fe8dc0d00a388990d694746a205bc91141f9a5d3f6855191e3e53cb390c76732c2bcec7534d5c750a6466efaa168fe1531ded5262355dd3929ee4c5ed04cdb193000209a343c88d76e138fa49f348d0a425c240a63442ce200f633fd64ab3cc22fca0a078ba08dd296fc5aad57ea178e103e4978fe05d592e140bbf465cbfad207bc46b9b1487564f7f2537a08f44a5928763a19dccef7d44e1d0eee320c90cde827d7bd4e76e0cab04e5444b1bbf7cb5fb051f6a240db2e6c6b768622d827b9aad7574da1b20c141d50245b78159f6e98b5737a1361f5c82b7abc9300244e3a331dc6d85d9851a6a577d345d3c948479994c20bc0117a6881305a11a49db499417c1b8c1f634ddc25097ea557da15bea778a70be9ad156d975d59b413c3a827479997582045068c56f5e551c95733a86f54310f26ed791a20f30a40288e165fbe255e449dbd49c36a19456760ddb2d7cc407526c0cc977b8489c74f00c487146fd61680d4457f3abd595a1d007b3a3d10e2ad7278c4afbb1a9e65487d31571aa4738d2d7d7cc7892018938342715df62553de26d170141e7541e17d1e85302c2ebcd51dacd591c791e733b51d5139e736fd48dc3e4a69d9e547acfe197958beb0593e5551a88ea755e5e51ffba99fd05cbe2152a01dc467195f52bb9c30ca7236d9431a01dc1a71233a2f44098dd6c58665c7d1a45bb9e80142605d01830221e1b56b6b968252537f8aad3bba6ff0445c048393882381d0982e0eef15b9ca6b37ad4b1eb3f11ed5327d2cd9b50ed86c061c2082f87376a4906b2a633435c5c92b392a9f3ca4adf2c04b80a136eebcb08830821a0a887d58dbc9cc0d9146db73b384094ec0048a02e2535c5e2d567931850f0518461ac660707bb5118615a2260ec9371b437cc91d4508001,0x508751c90df1b44dcec8981a2185118ed707981ac7185183c18504c5678b5c5f4d6e2280049b0094e103b36dd46b64cc0f258d9f5a886808220cb09af36ea84b81011f292b3caa7f92cac5c8d73342986b32436a1cd2f88221c301d874399b4b327d54d1ecfc1eb52f7a9ac9ca56eef383982742386203921205c4116feeead3e2a37f496822e56b66d61e40818374260050e80ee645f465c619ac5b75099d13a2c8ca71706018c6d948d8a70c3b9d4ad5f1c6c460752a085cbf4159feea1ff7955e29d88f46a5564fb042fb95865cff1e9e52764a70f88dbf5736e795154733a79c79647cd4768d53af2c34c1e85f41e1d501e405d178993d895df7c57424e018848078df3d7c34873ea95714c487995a9eec4afe31726ab50e0f4b3a01e1d656bd5ce857b516815846f9c5c49c0074a27b845dccc9b07531017cecb0dd9d945286c37525db91255ef8a5fb852889033088391bb5f26c435421bf3ad5c1c9956f5b150681158265d7989d3a84f0b4156575db6d15a6b0be29a776f9a155fea425c2537763507db8df0940d249dc695a04c2885e90102f0c26654785213cd177d295da6e145d9b61dc0cce3a913007247aa0af5cd87a13cdcb53a69f6055b7891d505060c06c4dbd5ead6e68268b6862dd6c6cb80da891f6c175fdf2bbf2c544139ab183276f53d7a09cdea4320db8d0eb87d45bddcc86763aa1e5951208edeb253df56521db11aebc481fad72f464efd40cb8d598178f92503e38617dfaad51696ff4a08c2ea07a822fd30ab3d923fdd8e00b3844298e40970a42343349278fb84d76a2343c68c20c0019336d0497be4ca7939577235499ed4c7e15a3ea13be46629875357535b1ebccb067231f394f23e447951da1d3e6941fc45bc88146a51dd68643888280d0370feea4c1b20ea0b035dc9aeeccb77d415c45376c9db5a11d3e4a44c9ef52238438bb14de84581c1cb107a8ef1be9dc82b5317c348891465f3ddd899155479b2e9c26e3aeefaa2bcd330aa2cefc807502bef5b6c65d83707339a3c5328516cfcf1ce67470c12123f5c9f7bfab94b5c56874e383340a6d05225bc68c88a796f741ea198727b99d7e0e62b819e5ed8ca6dd289c2eac3d714577248482fab1b273f4a1c161f493d1a914c4bbfd312672b562aed51f88410aff3c663cdcc2750b00a0b35c6e12c7104ff94a31f18ae3f5d9c738584659070d31cc0291f0862e8b2f2aaeec0323ab5f52aa347eb5639b55596e36618e1b06b36d95965d4bfa2523e67d9cfd64d3efa72d72c3a9cbcf2ba138cc8e12c811cc0766477a8309e0876b9a91beba485cb6e7c8281c1348a7184f0a4174f36230092020a726ae236b3ce274d9ee879bb6cf7f4d362d4bb519a14413131aacb0fdc4b095bf1029600ce789d8d6304c201538efaf4066675b81b4da6d4c9c4d02a7adc8d1f00268e97536478852aef22dfb9fdd0b67293e6273c85686436cf9fda4593fb154e7280224ce86d8321da0a712ae556458518ed1ee8644589665775692035d5ef86f1d1639db4cb8b130e3601627653370256d9663c6cb74be8d36f4b5ba4d0860ad3568e38ed869d543f2cbb7c58e332ba991ee1c8c431be1925fc85b8b5bcad679a208449ca51406306992a08d08a9fbc9346c1f1523ee9289d34a5ed82b1b3f35e29a31cac76548bf9957f4d4ce9ffd62b2f24a37322e0eaf721e6e6ac6ea6b88213f548770563d466a53023b022fd62c7485aaddc4cbb5aa8eeaa80423b870ba570663a4f8325bb1cadb87456c754aa1bc6a9ef9b57a0904284d586484b4ba6c2487b613c82226b505e2c8495ff323400083f03689302c68c42b33e18ab329ba730a9d4ce1224b436135e4a9cfef18e7875d3cfa5df12abd4af8a3142ba38ca2a8900e0c5af61da4d34fe83b3ce93d28e5bcb53d99ac01106eb230c2f823243d6a753b0b22e426d18e5277e9b05ca11626ceb6713c02d1c2ad32bdb98c37b0371ecf65b8b5b5eccc60dc6bac3f04605099fa8b07242d3f203d0d7330b85c5d9f1de1581c10a05a477a672525204e1325ec5ecca84f2342296f7aba25959bc17c427afacced754a27c97ab4fab093d4d2fab5df97962e74016952f3e4a3efdb68eb429dedca64f6aa09d4e60c6b9ad1d20cd3ae4e435b24e071968b72951fec10f1723749008b2a2e57062484b3b7b0f38cc9f99369e29663b5b1eb533b211c0d89990d2fabcfcb595e1c8d7cc55bf68813cfd1ec04f30dc0593163fd226ed8675c399ac72c2ebbdbcec88bbf9a0e775e3ec9cb6227041e1820525c07108a98f054691a81542d4f088b9734b63a4d0b6ee6aa0f4eb73ce0ac349b50ea6dacd28ff0d44983f2060a8e987225ff08ce8b507a194369e4e04b6965294ee7779a6ebad48d0b5d30da48d132ea04d9ae128a4401641b84d4b791b5666952a9bc0501192b1bb2069037021fe48aa8b39575d1eedc6eb27b00302c1b93202041ab472541e9111d866fc217901e465a0e9ad6ead541a9ccaa90fd7119ebc8c9337445cfc28def4abc3016e64e6a2d14a80fb2a693502c1661be66c2616878781171731453c353d799423ed8bb05202012ca2bc336e118bc03c8237022fc72a1ac6ca37e55d7d652460bc0cb5931206e60b070d699dc0dfb50a72e968778ca4ff889d14ff98a12f232ba8ff9e80b83a91f66a1505a10f349b947701a571da28c09a65e548b021326d24e5894317dc535ae6d98c1718b79cdacf74a3482c62c4ddba3c2199ddc55b92d1f6af793242f172d225c789738da4df8c883c52c7c819f5cb6506db8d14ef042660bc729b101a420179a319304c2785c2d7f014279b3d9cfd3f789a4339c42cb303e67c0ac5b1a26a44193b08a2888e0549256ca0fd9e8d41783f4238c96be2c8378a15b61ede276795339a25fae953afd728ab29eb077ba193960bd819d61d0a03c82afe689c07c8396158162f491f8d18783bd1d0d426786c8431f2d0190d52e07d1d8c5096b9c04bc50f636d0a8bd4a61c4aeb13da0ee89d294328d13afac9382b8b16db680501a9eceadc70b37a2621c4578e7271e3cdb0268c369be2d16f28af757689d14df89b3b0c0789343341b7736ab54720602120a527f19715bfeecd1adbf3665b4c5d9485b2bd4cf86937b5a631e6e5c31b80c9b55b51d2aca345e7cc82f4b46393a7d3282b05537e04ce4b56bc3f80b8f96b43f6130291d4da799f13276997d989836758b9dc6dd63f8d33b370d02a4becdd98f12402113df3d76e10dbaf2e475a5ebcdcf8293aee96d145d9b6876d579d8550766a77c5b93af2e96b1f32ad3a97fda2aaea4ad961f8e2c7c51202bcfcf7a66c46002102ee3420b02e4b24e585c08474cb6f202f6c9109291b09c5089789f42e0e8bf95a3a4ae06c0f6693f190ef7273b97233c798edd5ea641ca094ee3ec92d871bba52de116564a598e02cbe8250c6755eeee44489f70dbacb9b0bed147d9162b6335de98c29a69db46bfa75aa53bfc846407c59a7f352b843ab9be4553aaadd6f974364154bc88e28df96d5a58f67a6c478c681750ba4f0060b2254f1ee74d61125243f8ad3d207e45db99b971fe01540ae785a5669db6d12f3cbd0806c7eb13e0945d01b92afa4a33b82205b9d3d296c17079632deacc8a83d7161a7219855f6a07637227555a84b01e803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1795 : walk cp1795 moves1795 = last1795 := by decide +kernel
theorem result1795 : ValidCode last1795 ∧ ∀ i, 1795 ≤ i → i < 1895 → P i := by
  have h := walk_sound moves1795 val1795 (by decide) (by decide) (by rw [checked1795]; rfl)
  rw [checked1795] at h
  exact h
def cp1895 := last1795
theorem val1895 : ValidCode cp1895 := result1795.1
def moves1895 : List Move := [⟨[],[1448],[1539,983,295]⟩,⟨[350,193,1028,861,844,149,290,1309],[865],[156,786,1374]⟩,⟨[],[1190],[1727,1723,1311]⟩,⟨[],[409,227],[582,1790,1472]⟩,⟨[],[1220,1848],[1699,765]⟩,⟨[],[833,379],[888,784,886]⟩,⟨[],[1140],[463,1829,769]⟩,⟨[],[769,399],[202,1082,1028]⟩,⟨[],[1098,16],[1707,1345]⟩,⟨[547,835,32,270,870,35,1724,1137,836,378,369,238,1298],[1357,351],[284,42,314]⟩,⟨[57,129,349,1494,1267,681,789,57],[1596,960],[323,317,1515]⟩,⟨[],[1515,301],[1790,1602,944]⟩,⟨[],[242,964],[1703,329,823]⟩,⟨[],[1,887],[1640,188,968]⟩,⟨[1824,1580,255,1394,1088,1235,1813,241,1506,931,1075],[114,690,1678],[961,1283,1]⟩,⟨[921,789,1604,165,986,602,1258,6,995,1327],[1327,317],[1640,1728,310,1208]⟩,⟨[],[18,248],[1085,981,131]⟩,⟨[1689,1894,1638,26,730,554,1855,1844,1742,1745,77],[99,827],[1826,216,18]⟩,⟨[1544,853,772,280,926,635,1284,1378],[1378,1784],[1279,327,345]⟩,⟨[],[1579,31],[196,378,466]⟩,⟨[1205,456,1444,722,1596,681,1613,1210,900,1359,375,706],[1856,1750],[273,1427,357]⟩,⟨[],[1225,465],[162,826,1796]⟩,⟨[],[1160,428],[1795,1203,1161]⟩,⟨[],[823,369],[1486,1754,1440]⟩,⟨[676,1187,1134,1220,1197,1400,676],[1902,1628],[925,499,1225]⟩,⟨[],[893,579],[500,1456,1860]⟩,⟨[113,62,446,1184,946,794,82,1203,300,177,1495],[1872,1340,740],[641,415,1807]⟩,⟨[],[1025,795],[108,666,1374]⟩,⟨[],[652,768],[1227,339]⟩,⟨[],[995,41],[334,1058,672,1216]⟩,⟨[],[1216],[1353,1139,903]⟩,⟨[],[927,1627],[522,480,1638]⟩,⟨[397,278,1037,220,446,535,6,1035,1007,1641,853],[220,1568,982],[639,1469]⟩,⟨[],[1469,289,1245],[620,1766,220]⟩,⟨[1194,1177,1245,1468,1735,162,828],[1704,480],[179,79,1387]⟩,⟨[97,37,1480,732,1367,1121],[509,1045],[1636,1488,1080]⟩,⟨[1034,1068,1357,887,976,1281,1118,1169,982,201,393],[130,980,1378],[1301,841,1297]⟩,⟨[988,321,765,381,880],[597],[1634,808,130]⟩,⟨[1091,369,347,299,202,972],[1898,1922],[855,1783,1323]⟩,⟨[],[1889,1253],[996,1274,890]⟩,⟨[],[1590,606],[343,389,1337]⟩,⟨[1036,1721,1721,1036],[445,1855],[1066,1828,346,664]⟩,⟨[],[1368,426],[979,1317]⟩,⟨[],[1241,1829],[1018,1532,1036]⟩,⟨[],[130,1926],[363,1537,1453]⟩,⟨[],[223,1291],[1594,1086,130]⟩,⟨[1092,1693,1263,636,1223,219,715,480],[530],[1327,1201,387]⟩,⟨[],[1361,187],[1926,1066,624]⟩,⟨[],[1488,1274],[953,1661,1311]⟩,⟨[],[351,1091],[1354,1496,1390]⟩,⟨[],[1076,56],[1375,989,1263]⟩,⟨[],[1,785],[1680,1918]⟩,⟨[],[1288,504],[1543,1227,1]⟩,⟨[],[1643,481,337],[1042,936,642]⟩,⟨[873,339,1833,704,932,932,155,865],[860,160],[781,835,673]⟩,⟨[],[715,1093],[206,918,458]⟩,⟨[227,850,842,759,17,649,1805,257,1836,850,1452],[778,1454],[897,1895,1133]⟩,⟨[],[343,1829,857],[1844,826,1486]⟩,⟨[1935,1892,444,1035,179,1787,1038,572,1900,1178],[1400,1094],[837,243,745]⟩,⟨[],[1219,801],[1588,1672,1228]⟩,⟨[],[1536,246,904],[621,1231,357]⟩,⟨[],[603,913],[298,978,1216,906]⟩,⟨[736,574,896,1728,1302,1096,1104,192,298,1164],[1446],[1259,333,1373]⟩,⟨[1867,111,935,734,286,861,201],[639,1913],[1786,1894,236]⟩,⟨[],[416,672],[1181,111,741]⟩,⟨[961,724,516,1237,313,1671,64,154,1148,1498],[1501,1723],[898,576,1704]⟩,⟨[],[1834,842],[1057,1525,1449,1395]⟩,⟨[],[135,1033],[1230,474,1110]⟩,⟨[935,1922,1186,178,1338,1205],[474,394],[1697,223,135]⟩,⟨[529,193,768,274,1593,12,1269,1808,77,802,826,448,1189],[1755,1303],[1282,184,478]⟩,⟨[909,426,1199,159,1346,441],[930],[1689,703,1863]⟩,⟨[],[1667],[1378,468,984]⟩,⟨[],[814,1624,530],[1931,893,1121]⟩,⟨[1001,798,1919,1320,621,1065],[1617,53],[1508,1028,1012]⟩,⟨[79,1195,720,513,513,293,1281,79],[826],[445,853,575]⟩,⟨[],[1,1183],[1882,1808,660]⟩,⟨[],[1414,1384],[617,1017,1]⟩,⟨[],[271,1545],[1492,918]⟩,⟨[332,1788,1916,711,199,1249,1382],[232,1026],[1571,1777,883]⟩,⟨[],[1447],[1794,1590,232]⟩,⟨[],[1030],[1833,759]⟩,⟨[102,1638,1057,471,941,1525,1303,102],[785,1207],[206,572,1422]⟩,⟨[1909,1308,1308,1909],[994,924],[1585,731,1627]⟩,⟨[],[659,1897],[1592,1584]⟩,⟨[95,580,512,1889,95],[866,932],[131,1573,1383]⟩,⟨[],[1],[50,564,1250]⟩,⟨[],[1250],[997,1071,1]⟩,⟨[452,99,1808,170,1069,523],[1499,1773],[1294,304,310]⟩,⟨[],[310,492,292],[1565,913,309]⟩,⟨[],[961],[1172,402,1194]⟩,⟨[1937,555,1935,1223,1445,1618,3,30,543,1828,1911,19,22],[1944,924],[1307,123,917]⟩,⟨[],[863,1249],[1878,1636,1090]⟩,⟨[],[1312,322,1790],[1811,837,1379]⟩,⟨[],[785,1633],[506,448,1176]⟩,⟨[287,831,831,287,494,494],[180,406],[465,639,1127]⟩,⟨[],[295,1311],[1254,1052,180]⟩,⟨[],[1760,1150],[667,1229,1827]⟩,⟨[],[1579,1537],[766,924]⟩,⟨[],[1604,1292],[879,1299,809]⟩,⟨[1974,176,1519,796,630,378,1417,1842,195],[1111,19],[864,1834,1436]⟩]
def last1895 : PathCode := ⟨1995,0xe1f463d2c82df305b652c5d6d36603ddc95bb89976b5777c7513652410124301843c49183f0eb1c6c0318cbeed31933e300020d6330383dda88c30a8f332e4c131eb1724ace4aa7cf292beedc4ecf2a67344bf5d2a75fae515677d6f9923a8a10861341ba52d36fa34ae3b4518134cbca9160b509603d10e6e4abe9266501d1cec7af32c19c8c7ce53c8f911e5469b7abd5adcd04fdf4f3a6d239813e2f04c39259f69dd04839532abc76c04c7b4d21c20a67c2daa4e28c50ae8fb65a2dcb8acec4351ebb76258c241947e7513f3ae9fed53a7509e1682acaebb6da2b4d617c534eedf3425fd0ecdb0bb68bd2dd7052e7d7992f7037ed429cbaa9bf026725ab5e1e0a9eb5ee3453bcfab1b793981b228db6fa256c281f50ba33c9cb28a27ea940ff84cdcc926ede6e74b9a4e5851ddb94d2edc4cc08e2fa6b71140024ed89600ce789d8d6304f907a8c4098acf16a1b20c1417100e4982d08d24eda4d58c193b7a9ebd7a77c6f0159897ab9bdbbec0dc7b3dea91cec64943e80b379d011479f2a5cb4e80172f2cec970a42343349278fb84d76a234c2d0fdb74e364a3e2ac4cbbaf9e8cc48690be2a6415c28bb36c3b8199c7522600e492b59e688211272945018c1a64a823422a7ee9f7738bc51a55a8eab64db01f960a77b72993daa827539831ae6b468c7286d1373b22606881f47631425a44c689d3acc8a83d7161a6ec6a799521f4c589971da673a8b5e37c3abc1ad24baa9bf191071ba112b0599d4fbc9072bb8531e13625d68fec96f2c683d50ea6dacd28ff0d44988d09f14a730dc1ea64bc0a70ceccd3013da35bf310d74e5edf2c838010ee7d595589f5d4e214c5eb3d1a82f07e8a755e5e5f69b56ee20d8664985f582c9f104ff94a5ef267d3b52b5d88ce32be4a44c9ef786efd4ccaf586366fc629e3d0a84f3e27400a1302e80c1811f2760129a2efa52bb4d8879376bc8d1079852014470b2fd12f3cbd1ec4a798ae2e08b0f4727a474b67f4169f2685fd81046d8548080143d22b4bf8e0223e653d7f1a753384892d1e6084c9b4939609c46c9284436c80b6f332f836937fb290ce3bdb48503822c0bc2f8dd691c64b5f1641bcc5b4dd86934b611e4e3f39af09c6647096406a77c5b93afe2a23d1a954fde2690ce710b2cc0f9c81b90b0030ec15466c6f9660b07501a4b2a03d4a8b4e6b99016f0c4ab7bf614a216f4e8d51dacd591c791e733b51d5139e736fd48d925539b164fa457f6cf90de8621473f98ca0be0dc60fb1a6ee1284bf52abff16ea5fd1291f3744e99b6327bdf0e8ad8ea95437f342a8b38d90d6e557e604c7915388380ef2ac3281f493b632b6df7a04039f904f5f569ddd37f8222e3c605dc6841605c96d9dd0a7f34627d2cd18bc0b42c012c9e8650da793d8abb547e21042bfcf198f373d6c638a5e9e64c9fa330f3decb3921062b1e804518ed2a7644301e0f0248150da3d3b4d3186f466b5b22c3eca285f736565db775a91a16ba61b491a268356aadd4d6917d19719a1d474b83b57b37d748376cb5f31008c8a0de05534aacc8db6f26a370b2080052425cd6099756da16ce2f82b24afb44f28893d4d2fab5df9f401274dda59d7f1bddba9360943ba53d4a7dc74f9a507f116f237d77982044e5b1bc36df7122e45bbb55b7e8d7d99ff62b8ca4fc52c2484138342715df7e3b05dc6395e5fb6b2398dde957912f1fdd5f7bfab94b5c56874e383340a6d05225bd8adebcaa392ae6750de2ca9fc85838622d8bb08725adaf6663060371995d4c8f7032f2bcdcd58dd4d7105488e118783bd1d0d426786c8431f2d01821162c746eb62c3310381bbb0ac638a5959116378a526ece4848453e6c2750b00a0b0b262c730d32226b505feeab55fa85e386883916a753b0b22e4267b5b6285f48d579d855076058bd247e344a8d7a92aaf6880123ee46db4f671404bdac3f25bb1cad82d42ab34f1f64d080a3cfd116de76445dfcd073bbe130ae9c29aace18ccf42ba302c24c368fc0085003237fc4936e5072d9f5a06c7d149739e225c5da1730b5cdd0c809a343de9b71c814c68859c401ec67fac95679845f94167ef250fdd561a8ec38f56ab43a11c31054434041106584d79b75425c0808f942e27d9792962d99681d24cd6ce4eb80d022b04cbbecd3b10ed05389572ab05d4aee77cbc8b7ec74f00c487146f9faecf36613e02b9ff280f812da594a538fd08f44a5928763a19dccef7d44e1d0e8bcf11844bfcc1707778adce5359bd6a58f59f88f6a98060bc9196575fe548ded961f8e2c7c5107fed436b056367e6bc53463958eca98b4d3dfd6ce6ee8767a30ca723695ca2e2c900dd37203c6c147fe16cfcf1f81f06ec1b8399cd1e29948212455459cabae8f76e37592b6cb30abd1d00b13ad96ce588a1417e9a9ddbd64a7beaca43b6235d78903f5ae5e8c9dffa543f3167fba2c449fc650ef4b522b379d5709a94fe2cd0f832390f683305e394d880d2100bcf8797375dc535ae6d98e16eccf7b20ea0b035dde8a87cb571f1696ff4a08c2e80501a9ecd392b5939fb99f9922ff2bdbe68abfc823e10c5d165f2e96b3bb9ccaab5bee2c8497e1946fc4272264bd8bd9953de6cdcae2361e1b56b6b968252537f8ab7d396b961d5e618dcb8c175fdf2bbf2c544139e16ae550601c7fb95d5b8e166f45104c4c6ab2c9a8af6a2d02b09d8833523b4b906a9837521fd1b81a014711321ad28e8d440beff6535f5c29e2b88cf5e5e7b758fef479b67bc6ac4da2e0283cea83c2fa3d0a60585d7c95b282b27c7b91168647bfaa2ac7cf86937b5a631e694382c3e927a352298977fa624ce569db32e6c608460301d874399b7c31036ff09712eee935619c161138671f5db8f188c78e2ec537a1160753469facce7cfbe4c2b0ee1961e7b8461460f06146686b93a2d477c308f5415eb9b0f4279b96a74d3ec0ab6f123aa0fc8e0a228a12e435f382a348d40aa16a78445cb9a5b1d2685b7735507a75316f39b59ee1d741b2f6c6536e944e17561eb8a2bb9242417d58af34cd0ac72be43802c76f9653c8cb1b2d9b60c70cc371bb2daa8735ab8fd51aa53571d555badf2e86c82a97911c51bf2dab4b1ec26993b6a9b40dab733380dd7b1d8a9b2f589ffb3a4d55fdc0d204e05474c20960ef743272c17b033ac3a1407bf6da1dc7910866ff611107a65451c1ab21186204740944f86b1ce67470c12123f5c8196b26240dcc160e1ad33ae11773327ad4cec847036266434beaf3f2d1ea33529af565687401ece8f4438ab5c9e312bfe86c1d0dd89d339efc7c9346c1f1523ee9289d34a5ec23b8169765a78cef0fb51206f3b28a50d86ea4bb74756bcf0f801880752a085cbf4159feea1fef2a3d67fb834e246745e881300c778a726ae236b3ce3e7e50c5f0d5dfc6281c449455c64b8d598178faa53becc6b8174c384740255547627821c866157da81d8dc89d57d78954f633ae1ccd6396175d82942feb6bb91aa4cf6a63f0ad1f50a413c218429d6ed0c45af12402113df3d76e10df290f6323e00c2e7f78c73c3ae9e7d2ef8955ea57f91530d66486d439a5f104438f328af0cdb85d2ea340f186221cc5703336323c1d017cf51fd5d6460965b969cbdf0713abb7ae9251b99170757b90fab4ea5fed07dc488a796f741ea198727b99d7e4d77665bbea0ae229bb64edad08c5307b613c815254533e34b5f5f31e3ec13c9480e360162765337027e439c1d17f2b47495c0d81ecd27e321dee4e772e4678f3163dc3ae124449d619d2e645d1f8850482f44caf6ef4ab831306ceb78b53dc98bd89665645919a964f5b9c813828ceb4b1710b20c90cde8276bacd348001,0x7483346ba09cdea4320c42f172d28cee08816e74f4a5919916656258bdf2653de2ceb41b312ae2f4bdb4cabd0482141f9176e6674d61125246b8dc258cf319e2e59dee4877e3349decb605c1d26b45fc1d0e73e4409337d95625800e25213cfb01e37cf5f0d233f515527206121ec53423dad939bb08a0aefaa5bdd94d75fb99c9e987a8741dbda79223dc3415ff3abab64357bc1d9146e925ebabb44ef072f56996e0979195d47fcf405c1d48f3620cc57073623c6340ba85d36e30ca2bf330e10417c39bb5248359531e4657d7a894bbe7d3a7c3b1cf78b9f0c2f823243df284376e4f53de846403c445b4316e8a7184f0a41542d1fc2a63bdaa4c46abbfad42e0a75dd85639336e18ce4f6257d7f55c8963681df66152182189e4775540211dc385d2b83313bea978fe05d592e1c651544807062f7f0d517e50f9fce3ace231aba73de00c04ce89d1646538b839fe3d3ca1ffba99fd05cbe2152a01d189e00f0daf474edea4e1b50ca2b3b01b5123ecef1e365ba5f8108e5ecd289d24a3ee5481f51bc93f1f9ef4cd89436c1fa12bf8c5c9aad4383d2ce80787595af54a63347ab2d3cfbeb0d2660d8471b214c9eb3325dee14ce1ad838c1037625ac81957223e4870c1d1ce7ac4f8251740811864841ab472541e9111d866fc21790772da6fd406e87ac40c17bcb0323dd60e8274c1514e1481c0d7f4d4ce9ffd62b2e2a71df5e80ccceb70369b4da99389a1ecd2edaefcc5044697a0a86dcbbadd561d4d5ea55468fd6ac736aab2dc6cc31c360d66db2b2c3c85976f8b1380f9072c2b4ccbcd5885f424e4a2bae261e5d44e3a5537b1b2f5061d67b9b5bce3169d507cd5b77a15d216cb9b173845a9aa1503488a8f390d52e228a22380fcea8122dbc0acfb74c5ab9bd09b0fae415bd5309df2d44e86b99a2143c1461187b80791963b82b793cfb39fac9a753581e114deec4388c7c62b8fd7671ce161070561a4deefc4b095bf103f0d9b50ed86c04600216c6cb9db15a4ce98b7fe252288d5278fa82c50de698cb5a4df869f32adea87ba19117ee67c0acb29255d7961a60f42fa0f0ea80f202e8bc4d1aa7be6df463fb75f9e5e433eb8a785c2d7f657bf40a3528eeb4321c44140681b87f75260d6a8e43b4d48832762b0b406a22bc9aacbc6b311103d1166e39d5ee5c7f805502b9e164e5444b1bbf7cb5fb05cb8635e6075b96e5b7d62a37f496822e56b66d61e08dcafb37de654bd8f62649c8c431be1925fc85b8b5baaa9cceed6b4ba65f7450c0f8c82afe68f6ff2a8bf996679fb64d2b34e9ec068050ba08dd296fc5a71f2d687fa25dcc0ea0c83f7bb3216e63e6cd69c55d7973e1cbc8400d362394978331da3908c80f8b34fe6a570875737c8a4b43bc6527fc44e8a7fcc543fe95dfa32e5fd6903de235cd8a43ab27bf929bd277e9b05ca11626ceb6713c02d1c2acb32db5938df76ba3abb67154491820651e2f343986e2ec7c1f813c6cff8547fb043c5c8dd24022ca8b95c8d8a70c367ba1e6edb3dfd34d8b32a58f8e5342f17e78db050daed41fc5131f8e387ed9237e55d7d652460bc01aa9a3d9f83d6a5ef5359394addde707304bfe11f102f10eb87d45bddcc86763aa1e5951208e3f653e52da40480ffcab9f80a13cd9ece7e86f9c5c49c0074dfbc8bf2ee752b05caad574e2d044393b7b3cbac1022834eb9390d6c9381c65a2dca59789f42e3e5809701426ddd7961106104341513104703a0ad3568e38ed869d543ff259f94117e98559ec91feec70059c2214c720771fa643c68c80f435ccc2e1717625c78973c52c7c819f5cb6506db8495ff323400083f03689302c68c42b33e18ab329ba730af843bb41dfc917765b791173f0a342364bc7b350a82d2b6b1c96c3f76b04bc50f636de468f8015a2aaea48d792ae3491cbd0160761579db55f48a15b61ed4268bb0b54e6a6e46880e185f7eab57ba05fad62234c7318b0b202c00b42c2779b452120e49bba52de116564a598e0ac6ec81a40c3358b6eb1d162884019cb431b217870990d74783a61ce152210535cdd356cddcac32bdc4c85771980d307999af16b872ec2d89888392169f8b20df9d6ae0e4cab7ad8a96f523b400a0cde381d056ad7b94fe9f7f75f1e44957f7a98cc8fb6f9739571b05f8edf7c57424e08410905293f8cb8adff7668d6dfb55eeee44489f70db1bd96c44e08778df6f244507e6974ff714a74f7ba250360ea7ddfc69d76974d849f417e6b5cbed4c24f28d13afac9382b8b16db6975026cd709452200b20dc26a5bc8dab334a954de02808cc405f3b2c375d237d5ec3b52ed4668571f4691735add5aa8348989186dba685a91dd6db75973617da28fb22c56c66bbd318534d3b68d50920f02780305912a63b451a01b1e189212cedec3ce3327e64da78a598ed6cdcd8f3c6bfc10a2151fbb562b93b696507a12cb00b42f0118cb327cd1a7f742d9d25a05905c68177c60b8822dfddd5a75f413df900ea057deb6d8c93a7d3282b0ef2e0388454c798117e3950d6364b38aaf350de9563a8adc3bbd8c99b73a77447c1297f6ea7c5abfd484b84a6eec6a0fb71be1283989cf215a190db3e7f69164fec55384948dbf5736e795154733a79c79647cd4768d553a16f28b615ef4abc3016e64e6a2d14a80fb2a693502c1661be66c551ec00c0b06e4c803e6cc42ce7043226bf795546a23f8a3af6e77c1a9641c2664271af1ce4e3c79b604d186d37c5a6f16457c64a471d6be3bc2b0382140b48ef4ce4a47fba4f834cb6f202f6c9109291b09c65849326c84f982d1227381d4f1af5e6508fe02fe2b4f48142201483610476045fc9a69fd07679d27a51cb0f022e2e628a7fb1bd1cf112cbf70a511206611072376be4d886d352bbe9a2e4a7607c9810306e84c00a1d03e213c0a98f629bf1367618af533efde19ef1324a4af8e3623b5cd4bd3c995ee528ffc41c9f6085f126866836ee6d5f697955e29d7e8bc1a84f45ea530e257589e557d5bb90100e32cfb74e435f3156fda204cd33b370d02a4bfa9dc1cc14a27c8d1260d43fcd296b2a6d4383cb196f7b268e97536478852aed076f2d4f666b00441ba41f1926fbab4901aeaf7c378e8b1ceda65c589d3121e656a7bb11a7c583d22aacc74c6891325ac507607d688983b24dc6d1ca28c2d1ae60c53989daa84f729ded0a7e5b01936ab6a3a559468bddce9f1fb22a8d0a86998c14069449c211a219e4ade498012271d198ee36c2ecc29056a62f86911228cbe7bbb1322aa8f365d3bdb3434c288d76e138fa49f348d0a425c0ecbcb173a00b4a979f251d015e70b2fa0943191cfaa73df1ec0cef9bdeae896566f05f17a7af7a9cedc19561a493b8d2b40980397105060c06c16ab3c98b107a9e4304b589d99e00ca58ed8091405c4a6b8bc08933edd349b9477584938b9b9dde69b8c9337f8503ea909f28a72f3cae8f50a056c689b6ea35b2660792c6cfacef3457b9eb02ae1ead725899bf0aa5cbd0a7edc0d2f5e6e7c149d774b68a2ecdb43b5fcd0adf53bc5385f4d68ab6cbaeacda09e1d413a7b5e9fce913f9d9469058c589bb74784333bb8ab725a3edae914228a932db9f20a0704d31ec049dbabd4c8394129dc7d925b0ef04f898148ea6d3cfdf413dcd56baba6d546478f94f2ce431d9ccb0af3b1d1cc07665a48ab9b910e0f4962d41612a4cb84d518ed0ae68d36f4b5ba4d0860843a8e486f9df5563945faa9f5d12f734a9acf713eec4acf2a9fe4b2b1727ac13193332a3c30a231dae0f30358c20c003e264ed32fb18d00dc6bac3f0463c4e10300490101491371d777ad5976e255bf7203cd996d31765216df320bd2d18e1f003,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1895 : walk cp1895 moves1895 = last1895 := by decide +kernel
theorem result1895 : ValidCode last1895 ∧ ∀ i, 1895 ≤ i → i < 1995 → P i := by
  have h := walk_sound moves1895 val1895 (by decide) (by decide) (by rw [checked1895]; rfl)
  rw [checked1895] at h
  exact h
def cp1995 := last1895
theorem val1995 : ValidCode cp1995 := result1895.1
def moves1995 : List Move := [⟨[],[366,1312],[1771,19,1213]⟩,⟨[1383,1846,1846,1383],[737,1501],[186,40,1026]⟩,⟨[228,1708,1708,228],[266,1270],[1299,601,897]⟩,⟨[],[1407,259],[608,616]⟩,⟨[],[386,1228],[1321,621,999]⟩,⟨[],[753,1179],[106,1046,1326]⟩,⟨[],[1892,526],[969,447,1387,1833]⟩,⟨[],[1833],[982,806,1398]⟩,⟨[],[554,942],[69,249,993]⟩,⟨[],[1365,457],[1636,318,408]⟩,⟨[],[1520,958],[1235,497,1039]⟩,⟨[],[1787,981],[754,704]⟩,⟨[],[686,718],[1225,1695,1181]⟩,⟨[27,1196,1168,548,1149,1312,1312,288,1151,27],[1131],[636,6,848]⟩,⟨[],[1268,590],[1011,807,501]⟩,⟨[],[1915,39],[716,664]⟩,⟨[],[828,1080],[855,645,133]⟩,⟨[],[1205,1775],[310,1394,1400]⟩,⟨[1343,683,683,1343],[1396,1258],[1335,963,1859]⟩,⟨[],[1859,501],[922,1340,1430]⟩,⟨[],[478,1694],[1111,1409,1255]⟩,⟨[135,1643,1643,135],[],[1458,44,1582]⟩,⟨[1580,506,1564,1370,1919,1367,1457,942],[942,748],[1871,1267,947]⟩,⟨[],[1117,1131],[616,1146,1118]⟩,⟨[],[496,116],[1607,97,1007]⟩,⟨[221,11,622,202,829,570,1621,822,1982,1711],[499],[782,262,380]⟩,⟨[],[],[1043,1553,617]⟩,⟨[617,348,371,330,1626,1840,602,698],[1653,1619],[836,1082,1626]⟩,⟨[],[1726,66,402],[141,957]⟩,⟨[],[1487,341,37],[1174,868,2018]⟩,⟨[],[1638,1424],[1489,877]⟩,⟨[],[1103,979],[758,1710]⟩,⟨[1865,1721,499,1404,901,766,977,643],[362,1542],[701,1131,1499]⟩,⟨[],[709,1821],[426,362]⟩,⟨[],[68,1266,1824],[249,1005,269]⟩,⟨[],[691,1911],[978,72,68]⟩,⟨[1864,767,1425,790,1932,1887],[1006,1872,306],[681,401,1369]⟩,⟨[797,793,695,347,1954,471,1445,128,1523,1205,167,298],[1039],[1214,66,1480]⟩]
def last1995 : PathCode := ⟨2033,0x3dc3ae124449d619d20e485a7e2c837e75b961d5e618dfa9ad417fbaad57ea178e1a20e45a9d4ec2c8b9099ed2461b6e9a16a4775b6dd65cd85f68a3ec8b1fa120ca3f3a89f9d74ff6a9d3a84f0b4156575db6d15a6b0b979f0f2e6ebb8a6b5cdb6d2ea04d9ae128a4401641b84d4b79023e4ec025345df4a5769b10f26ed791a20f30a402889f42e04d518ed0ae68d36f4b5ba4d0860843a8e486f9df556654f79b372b88d8786d5adae5a09494dfe2adf4e5be71930a3cfd116de76445dfcd07272a2258ddfbe5afd82e5c2696c23c9c7e735e138cc8e12c80d4ef8b7275fc5447a352a9fbfdad5ef86f1d1639db4cb8b13a6243ccad4f76234f8b07a455598e98d12264b58a0ec0fad11307648dab334a954de02808cc405f3b2c375d237d5ec3b52ed4668571f46766e1a05497f53b83982944f91a24c1a87f9a52d6094bfb753e2d5fea425c250fa49e8d48a625dfe98bb14de84581d4d1a7eb25213cfb01e37cf5f0d233f515527206121ec53423dad939bb08a0aefaa5bdd94d75fb99c9e987a8741dbda79223dc3415ff3abab64357bc1d9146e925ebabb44ef072f56996e0979195d47fcf405c1d48f3620cc570736220e16c628d136dff179fce3ace231aba73de00c04ce89d1646538b839fe3d3ca1ffba99fd05cbe2152a01d189f755994dd39857c21ddfcf8a69ddbe684bfa1d9b6176d17a5bae0a5cfaf325ee06fda853975537e04ce4b56bc3c153d6bdc68a779f5f9f9047c5ec7b1324e46218df0c92fe42dc5ade56b3cd104224e528a031834c950468454fdd3eee7178a34ab51d56c9b603f2c14ef6e5327b5504ea730635cc66f1c0e82b56bdca7f4fbfbaf8f224abfbd537c5a6f1646fcb6ad2c7b09a64edaa6d036adccce0375ec762a6cbd627fece93557f58a2100672d0c6c87ec2513e1ac7399d1c304848fd72065ac9bbb1a83edc6f84a0e6273c85686436cf9fda4593fb154e125ad8cd77a630a69a76d1aa1c01c91b6285f48d579d855076058bd247e344a8d7a9294e3f473ea9ecf36613e02b9ff280f812da594a1f2fbb4ceec0305efccaaa7367e5045fa61567b247fbb1c0167088531c81dc7575d1eedc6eb24085003237fc4936e5072d9f5a06c7d149739e225c5da1730b5cdd0c809a334c04f68d6fcc435d397b7cb379d011479f2a5f6535f5c21a06e1fdd49835aa390ed35220c9d8ac2d01a8a08871e6515e19e17a3a016275b2d9cb114282fd353bb7ac94f7d594876c46baf1207eb5cbd193bff4bf71c4039081111a6398ec337e10a1f98b3fdd16224fe32877a5a9159bceab84d4a7f16687c191c87b41982f1ca6c4069fb7e990f4c6647db7cb9cab8d82fc76fbe2ba12704208482949fc65c56ffbb346b6fdaaf77722245f7805ed922125236138cb09264d909f305a244e703a9e35ebcca11fc05fc569e90284402906c208ec08bf934d3fa0ecf3a4f4a3961e04410aff3c663cdcf5b18e297a799327e8cc3cf7b2ce48418ac7b1206e60b070d699d70bebab95418071fee5756e3859bd14413131aacb26a2be7aedc21be521ec643b8f223e6e89d336c64f7be1d15b1d7d6e5d0d90552f223fbfc943f75586a3b0e3d5aad0e8470c41510d010478bcd0e61b8bb1f07e04f1b3fe151ffeaa746a8ed66ac8e3c8f399da8ea89cf39b7ea46d5339a25fae953afd729f40fa650561de5c07101b259c5579a86f4a95fcd1edfe5517f32ccf3f6c9a5669d3d80d00a17411ba52df8b4e3e5ad0ff44bb981d41907ef76642dcc7b043c5c8dd24022ca8b95c8d8a74f2ce431d9ccb0af3b1d1cc07665a48ab9b910e0f4962d41612a4cbcfa5df12abd4aff22a61acc90da8734be7e5b69bf501ba1eb10305ef2c0c8f7583a090100a75dd85639077a3a1a84cf0cf0f80489c74663b8db0bb30a415a98be1a4448a32f9eeec4c8aaa3cd974ef6cd0d30a235db84e3e927cd2342909703b2f2c5ce802d2d8170749ad17f07439cf91024cdf6558960038fd33e300020d6330383dda88c30a8f332e4c131eb17267d178a35b2660792c6d6b1f32adea87ba19117ee67c0acb29255d7961a60f42fa0f0ea80f202e8bc4d1aa7be6df463fb75f9e5e56bd1d3b7a9386d4328acec06d448fb3bc78d96e97e042397b34a274928fb95207d46f24fc7e7bd336250db07e84afe31726ab50e0f4b3a01e1d656bd5298cd1eacb4f3efac34998361f89b3b0c57a99ff1d3054538520703f8f53093ca344ebeb24e0ae2c5b7eb0b2fa094319fc0483c09e06f332f836937fa90c8310bc5cb4a33b82205b9d3d296466458addde707307f8450ae8fb65a2dcb8acec4351ebb76258c7e17e06d126058d1885667c31f417e6b5cbe656258bdf2653de2ceb41b312ae2f4bdb4cabd0482141f9176e67cdaaf6880123ee46db4f671404bdac3f25bb1cad82d42ab34f1f64d089792962d99681d24cd6ce4eb80d022b04cbbecd3b10ed05389572ab05d4aee77cbc8b7ec74f00c487146f9fa0ef7273b97233c798b1bad7c778560704281691de99c948e810230c9083568e4a83d2221dcfab2ab13eba9c4298bd67a3505e0fd14eabcbcbed36addc41b0cc930beb0593e209ff294bde4cfa76a56bb119c657df4867d714f1463943689b9536a1c1e58cb7bd93474ba9b23c42957683b796a7b33580220dd20f8c937dd5a480d56d966156f6693f197c0185cfef18e7875d3c42a3f76ac57276d2ca3e8d5347b3f07ad4bdea6b272fcc8e8dd6c586620703776158c714b2b222c6f14a4dd9c90908a7cd84ea1601416164c59f908e325af9cd73202de18956f7ec29442dc24847b550691367be3d819df0c6806e35d61f8231e2708180248080a489b8ebbbd6acbb712adfb901e6ccb698bb290b6f9905e968c7276c656dbef408073f209ebead3bba6ff0445c78c0bb8d082c0b92db3ba14fe68c4fa59a31781685802593d0862e8b2f975c5cc514ff63d4e76e0cab0d249dc695a04c0a0c180d82d567931620f53c86096b13b33c0194b1db012280b894d717811267dba693728eeb092717373bbcd3719266ff0a07d5213e514e5e795d1ea14097fc23e22ce2a8923040ca70d26f6b4c63cd28705a45cd6b75f7dc2cbf44bcf2f42011463b4a9d910c0846403c445b4316e8a7184f0a41542d1fc2a63bdaa4c46abbfad42f336e18ce4f6257d7f55c8963681df66152182189e4775540211dc385d2b83313bea978fe05d592e1c651544807062f7f0d517e50828e226435a51d1a8817dfad107f116f237d77982044e5b1bc36df7512964a1d8e867733bdf5138743a99cad3b665cd8c108c0603b0e87336f86206dfe12e25ddd26ac3382c2270ce3ebb71e3118f1c4708c3ebd7a77c6f01599ce948993dea4420a6b9ba6ad9bb958657b8990aee3301a60f3335e2d70e5d85b131157072655bd6c54b7a91da0053ea9ef8a2a4cb6e7c8281c134c7b01276eaf5320e504a771f6496c3bc13e260523a9b4f3f7d04f7355aeae9b55191e3e567b89f762567954ff259588e3642993d6664bbb0dfd9c6340ba85d36e1d4fbbf8d3aed2e9bfdde4c2b0ee1961e7b8461460f06146686b93a2d477c308f5415eb9b0f4279b96a74d3ec0ab6f123aa0fc8e0a228a12e435f382a348d40aa16a78445cb9a5b1d2685b7735507a75316f39b59ee1d741b2f6c6536e944e17561eb8a2bb9242417d58af34cd0ac72be43802c76f9653c8cb1b2d9b60c70cc371bb2daa8735ab8fd51aa53571d555bad9a5d3fdc529d3dee8940d80c1ba130028740f884f02a63d8a7fb45a29501f654d26a0fd2def5744bf0ddf9232caebfca91bdb2c3f1c58f8a20ffda86d60ac6cfcd78a68c72b1d953169a7bfad9cddd0ecf461ac1661be66c551ec00c0b06e4c803e6cc42ce7043226c54c798117e3950d7f66e04047ca832c26bcdbaa10de8276bacd348001,0x1d20cd1ae82737aa136eebcb08831f2c04b81f6435b955f98131e45489a4339c42cb303e7206e42c00c3b05519b1be5982c1186cf743cddb67bfa69b16654b1f1ca685e2fcf1b60a1b5da83f8a263f1c70fdb246fcabafaca48ddfbc344bd5cdeff4ea034965407a95169fb629e3d0a84f3e27400a1302e80c1360943ba53d4a7dc74f9a5eb755875357a9551a3f5ab1cdaaacb71b30c70d8359b6cacb0f2165dbe2c4e03e41cb0ad332f356217d093928aeb8987975138e954dec6cbd418759ee6d6f38c5a7541f356dde857485b2e6c5ce116a6a8540d222a3ce4354b88a2888e03f3aa048b6f02b3edd316ae6f426c3eb9056f54c277cb513a1ae668850f0518461ee01e4658ee0ade4ff769bb4b3afe37bb7536e174ba8d03c63f630d2ee664f5a99d908e25672553e79495f76e27678f911e5469b7abd5adcd04fdf4f3a6d239813e2f04c39259f69dd04839532abc76c04c7b4d21c20a67c2daa4e289effaa053682912dec56f5e551c9570c45b17610e4b5b5eccc60c06e332ba991ee065e579b9ab1ba9ae20a913de26494a73959bc17c5e9ebd30e7087118f8c571faece39c2c20e0ac349bddf89612b7e207e1b36a1db0d808c0042d8d973b62b499d0eb87d45bddcc86763aa1e595127dc36c6f65b113821de37dbc91141fad1f7e8146a51dd686438882894317c3577f18a071125157192e356605e3ea94efb31ae05d30e11d0095551d89e087219855f6a0763722755f5e2553d8ceb873350bfadaee46a933da98fc2b47d42904f08610a75bb43116bc4900844305912a63b451a01bd1cf112cbf70bf7edd4d6917058a1bcd3196b49bf0d32904248aa8b39e230897f503ea1746793965144fd5281ff099b9924ddbcdce97349cb0a3bb729a5db899811c5f4d6e2280049db12c019cf13b1ac609f20f518813159e2d4364182824c168469276d26ac60c9dbd4fd894f315c5e5d32fba2860f4259601685e02319664f9a34fee85b3a4b40b20b8d02ef8c171045bfbbab4ebe827bf201d40afbd6db1927631e96416f982db2962eb69b301eee4addc4cbb5abbbe3a89b29208092180c21e248c1f8758e36018c677d81b8f67b44d06ad50470922de516c2bde9578602dcc9cd6be325239f93161640580168584ef368a4241c93774a5bc22cac94b31c158dd903481866b16dd63a7cc9ca6b37ad4b1eb3f11ed53fa2ca1b4f27b1576a8fc4274f87639ef173e185f0719a4ef64559665b60d6925d54df8c8838dd089582ccea7de48395dc298f09b12eb47f64b796341ea875366e368e514613c57119ff495f1c6c476b9a97a7932bdca51ff88393ec10be24d0cd06ddcdabed2f2abc53afd1783509e8bd4a61c4aeb13caafab772220f4ca8a383564230c408e825219c77b690a0704581785f1bad2c6798cf172cef7243b9fa1be717127001d37ef22fcbb9d4ac172ab55d38b4110e4edecf2eb0408a0d3ae4e435b24e071968b72965e508d92f1ecd42a0b4adac725b0fddac12f143d8db791a3e00568aabfcdb991747e214120bd132bdbbd2ae0c4c1b3ade2d4f7262f625995cbead77e7d043199e857460584986d1f87e1631626edd1e10cceee2adc968fb6ba450fe1305c1dde2b645919a964f5b9c813828ceb4b1710b20c90dfee93e0d32dbc9e0f02483f0319250fa02cfeb16ce2f82b24afb44f28893d4df8dc0d204e05474c7f1a6657ac31b37e236266434beaf3f2d1ea33529af565687401ece8f4438ab5c9e312bfe86c1d0dd89d339efc7c9346c1f1523ee9289d34a5ec23b8169765a78cef0fb51206f3b28a50d86ea4bb74756bd7979edd63fbd1e6d9ef1ab1368b80a0f3aa0f0be8f429816175f256ca0ac9f1ee445a191efea8ab1f35acc6de4e606c8a345e67d5c9eb04c64ccca8f0c288c76b83cc0d63083000f8fd30e360162765337027e439c1d17f2b47495c0d80b4e80172f2cec970a42343349278fb84d76a234c2d0fdb74e364a3e2ac4cbbaf9e8cc48690be2a6415c28bb36c3b8199c75227803c2f0e1321ae8f0758e585d760a40420960ef743272c17b033ac3a1407bf6da7e52f87376a4906b2a63c8cafaf512977cfa32f2a4582d42580f4439b92afa4999407473b1ebccb067231f394f229c8da5728b8b240374dc80f1b0731c2dd99ef641d41606bbbd150f96ae3e2d2dfe941185d00a0353d9a7256b273f733f3245fe57b7cd157f4aa1bf9a15459c6cf10701de5586503e9f41ca2fd54fae897b9a54c46dfab9b73ca8aa399d3ce3cb23e6a3b46aa9d7ea47fe16cfcf1f81f06ec1b8399cd1e2904341513104703a0ad3568e38ed869d543ff25fbc88d2f4150db977d6c7515b8777b19336e74ee88f8f20ee46487be5086edc9ea2bc9aacbc6b311103d1166e39d5ee5c7f805502b9faf70a670d6c1c6081bb12b1e189212cedec3ce3327e64da78a598ed6cdcd8f3c6bfc1081161e8e4f48e96cfe82d3e4d0bfb0208db0a90100287a45697f1c0447cca7afe34ea6709125a3cc1099369272c1388d9250886d9017f7891722dddaadbf46beccffb15c6527e296124209c1a138aefbf1d82ee31caf2fdb591cc643de9bed869b11ca4bc198ed1c846407c59a7f352b843ab9be4525a1de3293fe227453fe62a1f84337fb0b9869911020039711f73d2bbf465cbfad207bc46b9b1487564f7f2537a4efd360b9422c4d9d6ce27805a3b85e19457e661c2086a2d02b09d8833523b4b906a9837521fd1b81a170b5fd94a5e7c94740579f2cfb74e435f3156fda204cd31a3203d0d7330b85c5d8971e25cf14b1f2067d72d941b6e1257fcc8d00020b271beed74757771c814c68859c401ec67fac95679845f94167e9ccaabf305e00ceeed32fb87d94b6901203ff2ae7e0284f367b3ea91ce3f653a9235e4ab8d2472f40581d855e76d57d22856d9c93002a1b47a769a630de8cd6b6125539b164fa457f6cf90de8621473f98ca0be0dc60fb1a6efac81957223e4870c1d1ce7ac4f8251fb0c8431f2d01821162d7f4d4ce9ffd62b2e2a71df5e80ccceb70369b4da99389a1ecd2edaefc5906f316d37ef4abc8978feeafbdfd5ca5ae2b43a71c19b5cc18a7313b5509ee53bda14fcb60326d56d474ab28d17bb9d3e3f64551a150d3318280d289384234433c95badf716424bf0ca37e21391325ec5ec1f1907e79f59de68af73d6055c3d5ae4b1337e154b97a14fdb81a5ebcdcf8293aee96d145d9b6876bf9a15bea778a7f39ddf098574e14d567f746201d4a82172fd0567fba87fbca8f59fee0d38919d17a204c031de29c9ab88dacf38f9ffc56df44e285b00e18887315c0ccd8c8f07405f3d47f5759182596e5a72f7c1c4eaedeba4946e645c1d5ee43ead3a97fb41f712229e5bdd07a8661c9ee675f935dd996efa82b88a6ed93b6b42314c1ed84f20549514cf8d2d7d7cc78fb04f2523ac9a753581e114deec498b7fe252288d5278fa09425fa955ff8b752fe894b59a51fe1a89311a13e294e61b83d4c97814e19d9f465c668751d2e0ed5ecdf5d20ddb2d7cc4023228378154d2ab3236f644c0d103e8ec6284b4898d13a75991507ae2c34dd8d4f32a43e98b132e3b4ce7516bc6f8757fda7ef2aa8d447f1475edcef8352c8384cc84e35e39c9c78f36c09a65c60bafef95df962a209cd077f245dd96de445cfc28993f9ce5b7d62a37f496822e56b66d61e08dcafb37de654559df5be648ea2842184d06e94b4dbe8d2b8ed14604d0b89f4a2240cc220e46ed7c9b10da6a577d345c94ec0f93022de4d46e1641000a484b9ac132eadb5cd9ad38abaf2e7c3979c2fa6b455b65d7566d04f0ea09d3daf4fe7489fceca3483fa22c3eca285f736565db775a91a16ba61b4919ed4268bb0b54e6a6e46880e185f7eab57ba05fad7ea18d7981d6e5e750de2ca9fc858399d358449491ae370803,true⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem checked1995 : walk cp1995 moves1995 = last1995 := by decide +kernel
theorem result1995 : ValidCode last1995 ∧ ∀ i, 1995 ≤ i → i < 2033 → P i := by
  have h := walk_sound moves1995 val1995 (by decide) (by decide) (by rw [checked1995]; rfl)
  rw [checked1995] at h
  exact h
theorem medium (n : ℕ) (lo : 41 ≤ n) (hi : n < 2033) : P n := by
  by_cases h41 : n < 42
  · have he : n=41 := by omega
    exact he ▸ base41
  by_cases h42 : n < 43
  · have he : n=42 := by omega
    exact he ▸ base42
  by_cases h43 : n < 44
  · have he : n=43 := by omega
    exact he ▸ base43
  by_cases h44 : n < 45
  · have he : n=44 := by omega
    exact he ▸ base44
  by_cases h45 : n < 46
  · have he : n=45 := by omega
    exact he ▸ base45
  by_cases h46 : n < 47
  · have he : n=46 := by omega
    exact he ▸ base46
  by_cases h47 : n < 48
  · exact result47.2 n (by omega) h47
  by_cases h48 : n < 49
  · have he : n=48 := by omega
    exact he ▸ base48
  by_cases h49 : n < 50
  · have he : n=49 := by omega
    exact he ▸ base49
  by_cases h50 : n < 51
  · have he : n=50 := by omega
    exact he ▸ base50
  by_cases h51 : n < 52
  · exact result51.2 n (by omega) h51
  by_cases h52 : n < 53
  · have he : n=52 := by omega
    exact he ▸ base52
  by_cases h53 : n < 54
  · have he : n=53 := by omega
    exact he ▸ base53
  by_cases h54 : n < 55
  · have he : n=54 := by omega
    exact he ▸ base54
  by_cases h55 : n < 56
  · have he : n=55 := by omega
    exact he ▸ base55
  by_cases h56 : n < 65
  · exact result56.2 n (by omega) h56
  by_cases h65 : n < 66
  · have he : n=65 := by omega
    exact he ▸ base65
  by_cases h66 : n < 67
  · exact result66.2 n (by omega) h66
  by_cases h67 : n < 68
  · have he : n=67 := by omega
    exact he ▸ base67
  by_cases h68 : n < 73
  · exact result68.2 n (by omega) h68
  by_cases h73 : n < 74
  · have he : n=73 := by omega
    exact he ▸ base73
  by_cases h74 : n < 94
  · exact result74.2 n (by omega) h74
  by_cases h94 : n < 95
  · have he : n=94 := by omega
    exact he ▸ base94
  by_cases h95 : n < 195
  · exact result95.2 n (by omega) h95
  by_cases h195 : n < 295
  · exact result195.2 n (by omega) h195
  by_cases h295 : n < 395
  · exact result295.2 n (by omega) h295
  by_cases h395 : n < 495
  · exact result395.2 n (by omega) h395
  by_cases h495 : n < 595
  · exact result495.2 n (by omega) h495
  by_cases h595 : n < 695
  · exact result595.2 n (by omega) h595
  by_cases h695 : n < 795
  · exact result695.2 n (by omega) h695
  by_cases h795 : n < 895
  · exact result795.2 n (by omega) h795
  by_cases h895 : n < 995
  · exact result895.2 n (by omega) h895
  by_cases h995 : n < 1095
  · exact result995.2 n (by omega) h995
  by_cases h1095 : n < 1195
  · exact result1095.2 n (by omega) h1095
  by_cases h1195 : n < 1295
  · exact result1195.2 n (by omega) h1195
  by_cases h1295 : n < 1395
  · exact result1295.2 n (by omega) h1295
  by_cases h1395 : n < 1495
  · exact result1395.2 n (by omega) h1395
  by_cases h1495 : n < 1595
  · exact result1495.2 n (by omega) h1495
  by_cases h1595 : n < 1695
  · exact result1595.2 n (by omega) h1595
  by_cases h1695 : n < 1795
  · exact result1695.2 n (by omega) h1695
  by_cases h1795 : n < 1895
  · exact result1795.2 n (by omega) h1795
  by_cases h1895 : n < 1995
  · exact result1895.2 n (by omega) h1895
  by_cases h1995 : n < 2033
  · exact result1995.2 n (by omega) h1995
  omega
theorem little (n : ℕ) (lo : 25 ≤ n) (hi : n < 41) : ∃ s, s.Perm (labels n) ∧ Chain s := by
  interval_cases n
  · exact little25
  · exact little26
  · exact little27
  · exact little28
  · exact little29
  · exact little30
  · exact little31
  · exact little32
  · exact little33
  · exact little34
  · exact little35
  · exact little36
  · exact little37
  · exact little38
  · exact little39
  · exact little40

inductive Tile where
  | single (v : Fin 24)
  | block (long rev : Bool) (a : Fin 49)
def flipD (a i : ℕ) := if i%2=0 then a else 48-a
def raised (x d : ℕ) := 49*x-24+d
def liftRow (a : ℕ) (xs : List ℕ) := xs.mapIdx (fun i x => raised x (flipD a i))
def orient (rev : Bool) (xs : List ℕ) := if rev then xs.reverse else xs
def render (s t : List ℕ) : Tile → List ℕ
  | .single v => [v.val+1]
  | .block long rev a => orient rev (liftRow a (if long then t else s))
def coeff : Tile → ℕ
  | .single _ => 0
  | .block .. => 1
def units : Tile → ℕ
  | .single _ => 1
  | .block long _ _ => long.toNat
def sizeAt (m : ℕ) (z : Tile) := coeff z*m+units z
def lastParity (p : ℕ) (long : Bool) := (p+long.toNat+1)%2
def endsAt (p : ℕ) : Tile → ℕ × ℕ
  | .single v => (v.val+1,v.val+1)
  | .block long rev a =>
    let u := raised 1 a
    let v := raised (endVal (p+long.toNat)) (flipD a (lastParity p long))
    if rev then (v,u) else (u,v)

theorem ready_len {n : ℕ} {xs : List ℕ} (h : Ready n xs) : xs.length=n := by
  simpa using h.1.length_eq
theorem ready_pos {n : ℕ} {xs : List ℕ} (h : Ready n xs) (i : ℕ) (hi : i<xs.length) :
    1 ≤ xs[i] := by
  have he := h.1.mem_iff.mp (List.getElem_mem hi)
  obtain ⟨_,_,e⟩ := List.mem_map.mp he
  omega
theorem ready_choose {n : ℕ} {s t : List ℕ} (hp : Paired n s t) (e : Bool) :
    Ready (n+e.toNat) (if e then t else s) := by cases e <;> simp [hp.1,hp.2.1]

theorem len_render {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (z : Tile) :
    (render s t z).length = sizeAt m z := by
  cases z with
  | single v => simp [render,sizeAt,coeff,units]
  | block e rev a =>
    have hl := ready_len (ready_choose hp e)
    cases rev <;> simp [render,orient,liftRow,sizeAt,coeff,units,hl]

theorem lifted_chain {n : ℕ} {xs : List ℕ} (hr : Ready n xs) (a : Fin 49) : Chain (liftRow a xs) := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  have hi' : i+1<xs.length := by simpa [liftRow] using hi
  obtain ⟨k,hk⟩ := List.isChain_iff_getElem.mp hr.2.1 i hi'
  have h1 := ready_pos hr i (by omega)
  have h2 := ready_pos hr (i+1) hi'
  have ha := a.isLt
  have hf : flipD a i + flipD a (i+1) = 48 := by unfold flipD; split_ifs <;> omega
  refine ⟨7*k,?_⟩
  simp only [liftRow,List.getElem_mapIdx,raised]
  have hm : (7*k)*(7*k)=49*(k*k) := by ring
  rw [hm,← hk]
  omega

theorem tile_chain {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (z : Tile) : Chain (render s t z) := by
  cases z with
  | single v => simp [render,Chain]
  | block e rev a =>
    have h := lifted_chain (ready_choose hp e) a
    cases rev
    · exact h
    · apply List.isChain_reverse.mpr
      simpa only [Nat.add_comm] using h

theorem ends_render {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m) (z : Tile) :
    (render s t z).head? = some (endsAt (m%2) z).1 ∧
    (render s t z).getLast? = some (endsAt (m%2) z).2 := by
  cases z with
  | single v => simp [render,endsAt]
  | block e rev a =>
    let xs := if e then t else s
    have h : Ready (m+e.toNat) xs := ready_choose hp e
    have hd : (liftRow a xs).head?=some (raised 1 a) := by
      simp [liftRow,List.head?_mapIdx,h.2.2.1,flipD]
    have hl := ready_len h
    have eq : (xs.length-1)%2 = lastParity (m%2) e := by unfold lastParity; omega
    have ev : endVal (m+e.toNat) = endVal (m%2+e.toNat) := by unfold endVal; rw [Nat.add_mod m, Nat.add_mod (m%2)]; simp
    have tl : (liftRow a xs).getLast? =
        some (raised (endVal (m%2+e.toNat)) (flipD a (lastParity (m%2) e))) := by
      simp [liftRow,List.getLast?_mapIdx,h.2.2.2,ev,flipD,eq,lastParity]
    dsimp only [xs] at hd tl
    cases rev <;> simp [render,orient,endsAt,hd,tl]

def joins (p : ℕ) (a b : Tile) : Prop :=
  let k := (endsAt p a).2+(endsAt p b).1
  k.sqrt^2=k
instance (p : ℕ) (a b : Tile) : Decidable (joins p a b) := by unfold joins; infer_instance
def shape (p r : ℕ) (w : List Tile) : Prop :=
  (w.map coeff).sum=49 ∧ (w.map units).sum=r ∧ w.IsChain (joins p) ∧
  (w.head?.map (fun z => (endsAt p z).1))=some 1 ∧
  (w.getLast?.map (fun z => (endsAt p z).2))=some (endVal (p+r))
instance (p r : ℕ) (w : List Tile) : Decidable (shape p r w) := by unfold shape; infer_instance

theorem word_len {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (w : List Tile) :
    (w.flatMap (render s t)).length = (w.map coeff).sum*m + (w.map units).sum := by
  induction w with
  | nil => simp
  | cons z w ih => simp [ih,len_render hp,sizeAt,Nat.add_mul]; omega

theorem word_ends {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m) (w : List Tile) :
    (w.flatMap (render s t)).head?=w.head?.map (fun z => (endsAt (m%2) z).1) ∧
    (w.flatMap (render s t)).getLast?=w.getLast?.map (fun z => (endsAt (m%2) z).2) := by
  induction w with
  | nil => simp
  | cons z w ih =>
    have h := ends_render hp hm z
    simp only [List.flatMap_cons,List.head?_append,List.getLast?_append,h.1,h.2,ih.2]
    cases w with
    | nil => simp
    | cons v vs => simp [List.getLast?_eq_some_getLast (show v::vs ≠ [] by simp)]

theorem word_chain {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m) (w : List Tile)
    (hc : w.IsChain (joins (m%2))) : Chain (w.flatMap (render s t)) := by
  induction w with
  | nil => simp [Chain]
  | cons z w ih =>
    apply List.IsChain.append (tile_chain hp z) (ih hc.tail)
    intro x hx y hy
    rw [(ends_render hp hm z).2] at hx
    rw [(word_ends hp hm w).1] at hy
    cases w with
    | nil => simp at hy
    | cons v w =>
      simp at hx hy
      subst x; subst y
      have h := hc.rel
      exact ⟨_,by simpa [joins,pow_two] using Eq.symm h⟩

inductive Query where
  | low
  | body (j : Fin 2)
  | top
def supports (m : ℕ) (s t : List ℕ) (x : ℕ) : Query → Prop
  | .low => True
  | .body j => Occ s x j ∧ Occ t x j
  | .top => Occ t x (m%2)
def value (x d : ℕ) : Query → ℕ
  | .low => d+1
  | _ => raised x d
def place (p pos : ℕ) (e rev : Bool) (j : ℕ) :=
  (pos+j+(if rev then lastParity p e else 0))%2
def entry (p pos : ℕ) : Tile → Query → Option (ℕ × ℕ)
  | .single v,.low => some (v.val,pos%2)
  | .block e rev a,.body j => some (flipD a j,place p pos e rev j)
  | .block true rev a,.top => some (flipD a p,place p pos true rev p)
  | _,_ => none

def ShiftOcc (pos : ℕ) (xs : List ℕ) (x j : ℕ) :=
  ∃ i : Fin xs.length, xs[i.val]=x ∧ (pos+i.val)%2=j

theorem render_occ {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    {x j : ℕ} (e rev : Bool) (a : Fin 49) (pos : ℕ)
    (hh : Occ (if e then t else s) x j) :
    ShiftOcc pos (render s t (.block e rev a)) (raised x (flipD a j))
      (place (m%2) pos e rev j) := by
  let xs := if e then t else s
  have hl : xs.length=m+e.toNat := ready_len (ready_choose hp e)
  obtain ⟨⟨i,hi⟩,hx,hj⟩ := hh
  change i<xs.length at hi
  change xs[i]=x at hx
  change i%2=j at hj
  have hd : flipD a i=flipD a j := by unfold flipD; rw [← hj,Nat.mod_mod]
  have ix : (liftRow a xs)[i]'(by simpa [liftRow] using hi) = raised x (flipD a j) := by
    simp [liftRow,hx,hd]
  have hpar : (xs.length-1)%2 = lastParity (m%2) e := by unfold lastParity; omega
  cases rev
  · refine ⟨⟨i,by simpa [render,orient,liftRow,xs] using hi⟩,ix,?_⟩
    change (pos+i)%2 = (pos+j+0)%2
    omega
  · let k := xs.length-1-i
    have hk : k<xs.length := by dsimp [k]; omega
    refine ⟨⟨k,by simpa [render,orient,liftRow,xs] using hk⟩,?_,?_⟩
    · change (liftRow a xs).reverse[k]'(by simpa [liftRow] using hk)=_
      simp only [List.getElem_reverse,liftRow,List.length_mapIdx,List.getElem_mapIdx]
      have he : xs.length-1-k=i := by dsimp [k]; omega
      simpa [he,liftRow] using ix
    · change (pos+k)%2=(pos+j+lastParity (m%2) e)%2
      dsimp [k]
      omega

theorem entry_sound {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    {x d j : ℕ} {q : Query} (hs : supports m s t x q) (pos : ℕ) (z : Tile)
    (hh : entry (m%2) pos z q = some (d,j)) :
    ShiftOcc pos (render s t z) (value x d q) j := by
  cases z with
  | single v =>
    cases q <;> simp [entry] at hh
    obtain ⟨rfl,rfl⟩ := hh
    exact ⟨⟨0,by simp [render]⟩,rfl,by simp⟩
  | block e rev a =>
    cases q with
    | low => simp [entry] at hh
    | body k =>
      simp [entry] at hh
      obtain ⟨rfl,rfl⟩ := hh
      exact render_occ hp hm e rev a pos (by cases e; exact hs.1; exact hs.2)
    | top =>
      cases e <;> simp [entry] at hh
      obtain ⟨rfl,rfl⟩ := hh
      exact render_occ hp hm true rev a pos hs

def entries (p : ℕ) (q : Query) : List Tile → ℕ → List (ℕ × ℕ)
  | [],_ => []
  | z::w,pos => (entry p pos z q).toList ++ entries p q w ((pos+sizeAt p z)%2)

theorem entries_sound {m : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    {x d j : ℕ} {q : Query} (hs : supports m s t x q) (w : List Tile) (pos : ℕ)
    (hh : (d,j) ∈ entries (m%2) q w pos) :
    ShiftOcc pos (w.flatMap (render s t)) (value x d q) j := by
  induction w generalizing pos with
  | nil => simp [entries] at hh
  | cons z w ih =>
    simp only [entries,List.mem_append,Option.mem_toList] at hh
    rcases hh with hh|hh
    · obtain ⟨⟨i,hi⟩,hv,hj⟩ := entry_sound hp hm hs pos z hh
      refine ⟨⟨i,by simp; omega⟩,?_,hj⟩
      simpa [List.getElem_append_left hi] using hv
    · obtain ⟨⟨i,hi⟩,hv,hj⟩ := ih _ hh
      let l := (render s t z).length
      refine ⟨⟨l+i,by simpa only [List.flatMap_cons,List.length_append,l,Nat.add_lt_add_iff_left] using hi⟩,?_,?_⟩
      · simpa [l,List.getElem_append_right] using hv
      · change (pos+(l+i))%2=j
        change (((pos+sizeAt (m%2) z)%2)+i)%2=j at hj
        have he : l%2=sizeAt (m%2) z%2 := by
          dsimp only [l]; rw [len_render hp]
          cases z <;> simp [sizeAt,coeff,units,Nat.add_mod]
        omega

def mask (j : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (k,i)::xs => (if i=j then 2^k else 0) ||| mask j xs
theorem mask_spec (xs : List (ℕ × ℕ)) (j d : ℕ) :
    (mask j xs).testBit d=true ↔ (d,j) ∈ xs := by
  induction xs with
  | nil => simp [mask]
  | cons v xs ih =>
    obtain ⟨k,i⟩ := v
    by_cases h : i=j
    · simp [mask,h,Nat.testBit_two_pow,ih]; tauto
    · simp [mask,h,ih,Ne.symm h]
def cap (r : ℕ) : Query → ℕ
  | .low => 24
  | .body _ => 49
  | .top => r-24
def masksOK (p r : ℕ) (a b : List Tile) (q : Query) : Prop :=
  let s := entries p q a 0
  let t := entries p q b 0
  (mask 0 s ||| mask 1 s)=2^(cap r q)-1 ∧
  (mask 0 s &&& mask 0 t)=mask 0 s ∧ (mask 1 s &&& mask 1 t)=mask 1 s
instance (p r : ℕ) (a b : List Tile) (q : Query) : Decidable (masksOK p r a b q) := by
  unfold masksOK; infer_instance
theorem mask_cover {p r : ℕ} {a b : List Tile} {q : Query} (h : masksOK p r a b q)
    {d : ℕ} (hd : d<cap r q) :
    ∃ j, (d,j) ∈ entries p q a 0 ∧ (d,j) ∈ entries p q b 0 := by
  obtain ⟨hu,he,ho⟩ := h
  let test (n : ℕ) := fun (v : ℕ) => v.testBit n
  have h1 := congrArg (test d) hu
  have h2 := congrArg (test d) he
  have h3 := congrArg (test d) ho
  simp only [test,Nat.testBit_or,Nat.testBit_two_pow_sub_one,decide_eq_true hd,
    Bool.or_eq_true,mask_spec] at h1
  rcases h1 with h|h
  · refine ⟨0,h,?_⟩
    have hh := (mask_spec _ _ _).2 h
    simpa [test,hh,mask_spec] using h2
  · refine ⟨1,h,?_⟩
    have hh := (mask_spec _ _ _).2 h
    simpa [test,hh,mask_spec] using h3

def certified (p r : ℕ) (a b : List Tile) : Prop :=
  shape p r a ∧ shape p (r+1) b ∧ masksOK p r a b .low ∧
  (∀ j : Fin 2, masksOK p r a b (.body j)) ∧ masksOK p r a b .top ∧
  (mask ((p+r)%2) (entries p .top b 0)).testBit (r-24)=true
instance (p r : ℕ) (a b : List Tile) : Decidable (certified p r a b) := by unfold certified; infer_instance
def decodeTile (u : ℕ) : Tile :=
  let tag := u%5
  let a := u/5
  if tag=0 then .single ⟨(a-25)%24,Nat.mod_lt _ (by decide)⟩
  else .block ((tag-1)%2==1) (2<tag) ⟨a%49,Nat.mod_lt _ (by decide)⟩
def decodeWord : ℕ → ℕ → List Tile
  | 0,_ => []
  | n+1,v => decodeTile (v%256)::decodeWord n (v >>> 8)

theorem occ_left {xs : List ℕ} {x j : ℕ} (h : Occ xs x j) (ys : List ℕ) : Occ (xs++ys) x j := by
  obtain ⟨⟨i,hi⟩,hv,hj⟩ := h
  exact ⟨⟨i,by simp; omega⟩,by simpa [List.getElem_append_left hi] using hv,hj⟩
theorem occ_snoc (xs : List ℕ) (x : ℕ) : Occ (xs++[x]) x (xs.length%2) :=
  ⟨⟨xs.length,by simp⟩,by simp,rfl⟩
theorem occ_mem {xs : List ℕ} {x j : ℕ} (h : Occ xs x j) : x ∈ xs := by
  obtain ⟨i,rfl,_⟩ := h
  exact List.getElem_mem _
theorem occ_unique {xs : List ℕ} (h : xs.Nodup) {x a b : ℕ} (ha : Occ xs x a) (hb : Occ xs x b) :
    a=b := by
  obtain ⟨i,hi,rfl⟩ := ha
  obtain ⟨j,hj,rfl⟩ := hb
  have e : i=j := h.injective_get (hi.trans hj.symm)
  rw [e]

theorem common {m : ℕ} {s t : List ℕ} (hp : Paired m s t) {x : ℕ} (hx : 1 ≤ x) (hm : x ≤ m) :
    ∃ j : Fin 2, supports m s t x (.body j) := by
  have hx' : x ∈ s := by
    apply hp.1.1.mem_iff.mpr
    exact List.mem_map.mpr ⟨x-1,List.mem_range.mpr (by omega),by omega⟩
  obtain ⟨i,hi,hv⟩ := List.getElem_of_mem hx'
  let j : Fin 2 := ⟨i%2,Nat.mod_lt _ (by decide)⟩
  have ho : Occ s x j := ⟨⟨i,hi⟩,hv,rfl⟩
  exact ⟨j,ho,hp.2.2 _ _ (occ_left ho _)⟩

theorem topSupport {m : ℕ} {s t : List ℕ} (hp : Paired m s t) :
    supports m s t (m+1) .top := by
  apply hp.2.2
  simpa [ready_len hp.1] using occ_snoc s (m+1)

theorem unshift {xs : List ℕ} {x j : ℕ} (h : ShiftOcc 0 xs x j) : Occ xs x j := by
  simpa only [ShiftOcc,Occ,zero_add] using h
theorem common_output {m r : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    {a b : List Tile} (hc : certified (m%2) r a b) {q : Query} {x d : ℕ}
    (hs : supports m s t x q) (hd : d < cap r q) :
    ∃ j, Occ (a.flatMap (render s t)) (value x d q) j ∧ Occ (b.flatMap (render s t)) (value x d q) j := by
  have hv : masksOK (m%2) r a b q := by
    cases q with
    | low => exact hc.2.2.1
    | body j => exact hc.2.2.2.1 j
    | top => exact hc.2.2.2.2.1
  obtain ⟨j,ha,hb⟩ := mask_cover hv hd
  exact ⟨j,unshift (entries_sound hp hm hs a 0 ha),unshift (entries_sound hp hm hs b 0 hb)⟩

theorem cover_output {m r : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    (hlo : 24 ≤ r) (hhi : r ≤ 72) {a b : List Tile} (hc : certified (m%2) r a b)
    (y : ℕ) (hy : 1 ≤ y) (hN : y ≤ 49*m+r) :
    ∃ j, Occ (a.flatMap (render s t)) y j ∧ Occ (b.flatMap (render s t)) y j := by
  by_cases low : y ≤ 24
  · have h := common_output hp hm hc (q:=.low) (x:=0) (d:=y-1) trivial (by change y-1<24; omega)
    simpa only [value,Nat.sub_add_cancel hy] using h
  let x := (y+24)/49
  let d := (y+24)%49
  have hd : d<49 := Nat.mod_lt _ (by decide)
  have eq : y=raised x d := by dsimp [raised,x,d]; omega
  rw [eq]
  by_cases h : x ≤ m
  · obtain ⟨j,hs⟩ := common hp (x:=x) (by dsimp [x]; omega) h
    exact common_output hp hm hc hs hd
  · have ht : x=m+1 := by dsimp [x] at *; omega
    have hb : d < r-24 := by dsimp [x,d] at *; omega
    rw [ht]
    exact common_output hp hm hc (topSupport hp) hb

theorem extra_output {m r : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    (hr : 24 ≤ r) {a b : List Tile} (hc : certified (m%2) r a b) :
    Occ (b.flatMap (render s t)) (49*m+r+1) ((49*m+r)%2) := by
  have ht := (mask_spec _ _ _).1 hc.2.2.2.2.2
  have h := unshift (entries_sound hp hm (topSupport hp) b 0 ht)
  change Occ _ (raised (m+1) (r-24)) ((m%2+r)%2) at h
  have he : raised (m+1) (r-24) = 49*m+r+1 := by unfold raised; omega
  have he' : (m%2+r)%2 = (49*m+r)%2 := by omega
  rwa [he,he'] at h

theorem shape_output {m r : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    {w : List Tile} (hs : shape (m%2) r w)
    (cov : ∀ y, 1 ≤ y → y ≤ 49*m+r → y ∈ w.flatMap (render s t)) :
    Ready (49*m+r) (w.flatMap (render s t)) := by
  obtain ⟨h1,h2,hc,hd,ht⟩ := hs
  have he : endVal (m%2+r)=endVal (49*m+r) := by
    have he : (m%2+r)%2=(49*m+r)%2 := by omega
    simp only [endVal,he]
  exact ⟨perm_of_cover (by rw [word_len hp,h1,h2]) cov,word_chain hp hm w hc,
    (word_ends hp hm w).1.trans hd,(word_ends hp hm w).2.trans (ht.trans (congrArg some he))⟩

theorem pair_output {m r : ℕ} {s t : List ℕ} (hp : Paired m s t) (hm : 0 < m)
    (hlo : 24 ≤ r) (hhi : r ≤ 72) {a b : List Tile} (hc : certified (m%2) r a b) : P (49*m+r) := by
  let n := 49*m+r
  let S := a.flatMap (render s t)
  let T := b.flatMap (render s t)
  have cov (y : ℕ) (h1 : 1 ≤ y) (h2 : y ≤ n) : ∃ j, Occ S y j ∧ Occ T y j :=
    cover_output hp hm hlo hhi hc y h1 h2
  have extra : Occ T (n+1) (n%2) := extra_output hp hm hlo hc
  have ps : Ready n S := shape_output hp hm hc.1 (by
    intro y h1 h2; obtain ⟨_,h,_⟩ := cov y h1 h2; exact occ_mem h)
  have pt : Ready (n+1) T := shape_output hp hm hc.2.1 (by
    intro y h1 h2
    by_cases h : y ≤ n
    · obtain ⟨_,_,he⟩ := cov y h1 h; exact occ_mem he
    · have e : y=n+1 := by dsimp only [n] at *; omega
      exact e ▸ occ_mem extra)
  have perm : (S++[n+1]).Perm (labels (n+1)) := by
    rw [labels,List.range_succ,List.map_append]; exact ps.1.append_right _
  have nd := perm.nodup_iff.mpr (List.nodup_range.map Nat.succ_injective)
  refine ⟨S,T,ps,pt,?_⟩
  intro y j hj
  have hy := perm.mem_iff.mp (occ_mem hj)
  obtain ⟨k,hk,hky⟩ := List.mem_map.mp hy
  have hk' := List.mem_range.mp hk
  by_cases h : y ≤ n
  · obtain ⟨j',hs,ht⟩ := cov y (by omega) h
    exact occ_unique nd hj (occ_left hs _) ▸ ht
  · have e : y=n+1 := by omega
    rw [e] at hj ⊢
    have hs := occ_snoc S (n+1)
    rw [ready_len ps] at hs
    exact occ_unique nd hj hs ▸ extra

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word24p0 : ∃ a b, certified 0 24 a b :=
  ⟨decodeWord 73 0xa079ee21d32bc935bfd26c88767ebe9708df15e285aa94b9eba84c53a1f0b48c91af8f65d7966fcdc62e1cd8019ec3d024f10de7103aba44b0e15d829ba5c8dcb73d6287e6ad47587d,decodeWord 73 0x8796aa9460dcc8a59b825be112e90bd8b93abaad47b73db48d7183e417dd0699be80748a6ad2c1e6589c0433cb29d51fec7ba0cdc62ec3d024f11ad7678c91af44b04ea6eb53a1f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word24p1 : ∃ a b, certified 1 24 a b :=
  ⟨decodeWord 73 0x875b97678fd26c8ad70ba59b82303fb7d0ba44a05391afb0e18cd31f2bb9eb747ebee658836fcd92aac39c62792649adda01f1e9a1e210ee08dc17c43a35c1c9c81a964ca6ddb4f07d,decodeWord 73 0xa012c92921d5b53d6279c3aa944724cdc615dcc81a964c5391ce30066599ee9ce7f4bfd28d718556a8e2af03e18cb4df829ba5ba38336c8ad70be6addab0425d87b9eb747ebea1f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word25p0 : ∃ a b, certified 0 25 a b :=
  ⟨decodeWord 73 0x87e6bfd26c88b48d7196d7bc38b9da1ae78074f326cec39c0433beaf44b0e15d97678c91dcc8cb29d51fec159ba50de410dd06eb8230c4cda07985aa94603fb549ab53a1f04ea6587d,decodeWord 73 0xa07985aac39c043317ee21d3beaf918cb4b9da1ae780a59b74f326ce995be1b242bc38678d7196d7cdc62e82eb09dcc8cb2987e6bfd26c88df12e20b94603fb549ab53a1f04ea6587d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word25p1 : ∃ a b, certified 1 25 a b :=
  ⟨decodeWord 73 0xa042bc3aaa964ca53d62798571f0a3e70b94f426b5ce30b48a511ae4125d99ee9c56499bc4cdd76708d32bb08c91af33cbbfa8b9eb82bee6876c03e17e74c8dc17dfabd88fd221c37d,decodeWord 73 0x876c03e112d28dda1c5388dfabe6bea1c69b47248cb244a09ec31f91afe4a65817cd92aa3833cbbced97d0b73fa54e965d7e74c8dc62798571f0b42e82ebb929d50665d70be7f4bf7d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word26p0 : ∃ a b, certified 0 26 a b :=
  ⟨decodeWord 73 0xa07985aa94b9da0de417ee21d32bc935bfd29b748a6a02af8f65995b44b08c91dcc8a57ebe82eb0938c62ed024f11ae710ddb43fb549ab53a1f04ea6966fcdd7bce1c39c6287e6587d,decodeWord 73 0x87e6589c046c88767ebe82eb0938b9da0ed7bce15d97d024f11ae710ddb43fb549ab53a1f04ea696aa946091dcc8a59bd2c133cb29d51fec15e2af44b08c678d71837ba0cdc62ec37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word26p1 : ∃ a b, certified 1 26 a b :=
  ⟨decodeWord 73 0x876c6fcdc615dda64c1fed06ebb93a35c1f2e90dce247b609ec3aa961c5391af03e18c56e6ad4992d5b5b2d88f6774c8dc83e4a3be805b97a53d2e829bd210a04229c9bad788b4f07d,decodeWord 73 0xa012d28ddab0e1016a872bcbbcce9942af91514e965d7e74f426be8230abe60dea1cbf3338b9eb08ef21d5b54992aac39c62798571f0b43fa5c8dc17c4cdd788dfa8e2a19b588c677d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word27p0 : ∃ a b, certified 0 27 a b :=
  ⟨decodeWord 73 0x87966f8fb4b9da1ae710dd8aafe417ee21d3be80a5995be1b24209dcb549abe60e3d6292aa837ba0cdd7bc38678c916ad2c133cb29c8769b82eb53a1c62ec3d024f1029e56a84cf07d,decodeWord 73 0xa079856f8fb43f0ca57ebee6ad47b7dc0744b0e15d97d024f102f0a3514ea6589c6292d51fec15e2af88df13d2c133cb29c8769b82ebb9da1ae7aa96876c918c653abad7cdc62ec37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word27p1 : ∃ a b, certified 1 27 a b :=
  ⟨decodeWord 73 0xa0cdd7965d87d88f4c1fd2c1c935afbed58c67082e8260926c8a51a1e28571f003f42610e1b2442bb9a6eb747eea1cc897a50dceb5dc91adddb43f9c56e679efba38c6159b47aac37d,decodeWord 73 0x87d82610e15d7e74f4bf3fa54e96c9ba38c615dcb7aa499bd28d658c91adddb42e8260920dcec31fed9708d3beaf44b2e3a151eba8b929c81ae89c56e6798571f003336c8ad7cda07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word28p0 : ∃ a b, certified 0 28 a b :=
  ⟨decodeWord 73 0xa079c39ccb29d51fec15e2856f30c4cdd7965d82eb0938b992aa49ab53a19bd211ddb4f004e1ba44b08c678dda0ee91cf326ce99be80748aaf916a35bfa84ca5c8dcb73d6287e6587d,decodeWord 73 0x87e6ad47b73dc1336c88767ee91cf326cec39ca079ee21d32bc9c8a599beaf91dc6292aa965d82eb0938b9b4f004e1ba44b08c678dda0ed7cdc62e7183e418df13d29ba3514ea6587d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word28p1 : ∃ a b, certified 1 28 a b :=
  ⟨decodeWord 73 0x87b93abced975b442b0b94cdc61535afbe8260dcb7aac3e17eea1c53a3e5b0d31f4ca6eb74f4bf3f9ca012d26c03d88f67082e718556499ba5c8cb96d788dfabe67926d0918cb4f07d,decodeWord 73 0xa09ec3aa944758837be6bea1f0b4b9daad2ed026b5875b44b2e3af03f4bfa8e012d26c6fcdc6158ad796c9353abced9708678f4c1fd32b0b3fa59b8260dcc81ae880e18c9151eb747d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word29p0 : ∃ a b, certified 0 29 a b :=
  ⟨decodeWord 73 0x8796aa0938c62ec37ba0cd7183b9da0e3dc1e6be82eb53a19b748a6ad2ab918c65d7b0b7dcc82bc935024916e2af8fb4df1342bce15d97d024f11ae780a5ee21d394609e56a84cf07d,decodeWord 73 0xa079c330c43a07aa83e418cd719687b9eb82bee6ad4704f326ce995be1ba4411ddb48daf88769bd26c918c65d7b0b7dcc82bc935bf3f0cd81be780a5ee21d394609e56a84c53a1f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word29p1 : ∃ a b, certified 1 29 a b :=
  ⟨decodeWord 73 0xa0cdd796aa08dc91ce24f2ea1cc82b0be6875b4497a53d2ec43abced12d2c1c935afe5171fe0ab53a3be80e101499b82eb748a6c6f83b9dab0b7d3946279c39c56a84e8d658cb4f07d,decodeWord 73 0x875ba3be35afe517c43aaa08efba4497a53d2e829b47589ec37b60dc9151eba8d9b98571f0b48cd394f426d00be6adde214e8d12d2c11a96c9c82bb0b7e880e1016a887665d7cda07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word30p0 : ∃ a b, certified 0 30 a b :=
  ⟨decodeWord 73 0xa079c39ccb29d51feca57ebe829b748aaf8fb4df135d97678ce1ba44b0b73d6287966fcdd70cd8b992aa83e4184704336c91dcc81be7f326ce30c43a07eba84cf0a351add2c1e6587d,decodeWord 73 0x8796aa94603fb549abe6bfd211ddb48daf88767ebe829ba54ea6ebb9da0ed7678cb242bce15d97d024f1e91d53a1f004336c91dcc82bc99ec330c43a07d320ec7ba0cd7183e418587d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word30p1 : ∃ a b, certified 1 30 a b :=
  ⟨decodeWord 73 0x87b9b48ce1b2e3af333812c929d5214e96d7886a019e3d2ed09151a15d9942bceda5c8dc831cdba65817e0abe60d6279c3aa9447b7e88076eb08678fd2c1a0f426be829bc4cd71f07d,decodeWord 73 0xa09e5883e5b04e96c929d608dcc8a5efbaad2e3d620deab54992aac37be6be82eba8d91ad7678fd2c1f2016a887680e18cb4e01224ce9942af3338b9875ba3539121159bc4cd71f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word31p0 : ∃ a b, certified 0 31 a b :=
  ⟨decodeWord 73 0x87603f0cd8b992aa83e41847b7dcc8a19ba5ee2251eb825b44b04e1be7f326ce30c43a07d32bc935bfa8cd7196d7bce1c37ba09e56e6add211dd8aaf8fb4f0046c918c6599be80747d,decodeWord 73 0xa079c3e1bad7966fcda6c1336c916287b7dcc8a19ba5ee2251eb825b44b08c6599be80742bc99e56e6add211dd8aaf8fb43f0cd8b992d50938c62ed004f3274916e285aae91d4cf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word31p1 : ∃ a b, certified 1 31 a b :=
  ⟨decodeWord 73 0xa04229c8cbbc3aaab5b2d6a151ebb9b4f06fcdc6303fa5ef214e8dafe517e012d29b82be805b9708dc837b60920dea1cdba6589ec3e18c91ce2447abe68796d767748a6c03f4bf337d,decodeWord 73 0x8796d71cc8cbbc3aaa94cda053886a35afe517e012d29b82bee6ad4926d103f4bfc42e3d0deab5b2d6a15d7e742b4497a5ef214e8ddba6589ec3e18c91dc62798571f0b4b9eb08677d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word32p0 : ∃ a b, certified 0 32 a b :=
  ⟨decodeWord 73 0xa079ee2251eba8cdd7b08c653a07d394b9da0e3dc1e6add26c91dcb587609ec3d00433cb29c8a1c62e829b748aafbe80a5995be1ba4411ddb48d7196aa83e418475825f1e91d4cf07d,decodeWord 73 0x87609ec3d00433be80748aaf8fb4df1342bce18c65995ba3c8a59b82eb5320ec7ba0cda65825f1e91d4cb2d796aa94b9da0e3dc1e6add26c91dcb54916e2856f30c43a07d32ccbf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word32p1 : ∃ a b, certified 1 32 a b :=
  ⟨decodeWord 73 0x875b97d19c56e67926be827185dc916294cda042bced06d4b0b7aa499bc4a338336c03f4bfa8d91ae88076ebb929c9c8a53d0dd7964cf0b48ce1c330ab5388e012d22115e3af8f677d,decodeWord 73 0xa0cdd796aa49926091dcc8a5ba38336c03f4bfa8d91ae88076ebb9b4f04e8dafbe827185569bd210de8a51ad2ec4a3e5171fed7be6872b0b3fb7248ce1c3d19ccc975b44b2d608677d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word33p0 : ∃ a b, certified 0 33 a b :=
  ⟨decodeWord 73 0x87e6bfd26c918c653aba82eba8cdd7b0e1c37ba0f327be80748aaf4411dd16e285aae91d4c20ec07d394609e569ba5995b966f8fb43f0cd8b92ac8dcb549ab53a1c62ed00433cbf07d,decodeWord 73 0xa079c3e1b242af918c653aba82ebc42fd00433cbf04e1be7aa83e41820ec07d394609e56a8cdd7966f8fb43f0cd8b92ac8dcb549ab53a15d97a57ebe25f1769bd211dd8a6a87e6bf7d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word33p1 : ∃ a b, certified 1 33 a b :=
  ⟨decodeWord 73 0xa09ecf99cabad7cd92d6082e718556e6addb0d2942afb04e9687b9eb82bea1511ae517c43aaaeab53d6279ef21c3e15d7e74f426499ba5c8dc918c678fd210dea6c135016a88b4f07d,decodeWord 73 0x87e6addb0d2942af0333bfd28d6599c8a54e96a8b9eb82bea19b4758836f30b48c91dc06d4b0e15d7e74f42610de15e31c53886a94c53aaaeab53d6279ef21c3d19ca0cdd7bcccf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word34p0 : ∃ a b, certified 0 34 a b :=
  ⟨decodeWord 73 0xa079c39c6292aa83e41847b73d2f829b74f327beaf88df13d2ab53a1f0c93502ce995b44b0e1bad7cdc6ebb9da0e2ad50938678cb48d7196876c91dcc81be780a5ee224ea6c1e6587d,decodeWord 73 0x872c0cd8b93abaadd26c91dcc81be780a5ee224ea6966f8fb48c6507d3beaf88df13425d97d004e1b2d7cdc6eb53a1f0c936c1e65825f1a079c39c6292aa83e41847b73d2f829b747d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word34p1 : ∃ a b, certified 1 34 a b :=
  ⟨decodeWord 73 0x876c03e17e214e965d12e5b08c56e679efba82bea151ebb93aaac3d19c6294c5cdd788766599ca35a6c1f2a042af91dc836f8fd29ba5c81ae817e0ab47b724db0d29d6082e3db4f07d,decodeWord 73 0xa0cdd767747eeab549adde8a51ebb9b43f3006d42b0bf426103aaac3d19c6294c5a3be35af44975b964ca59bd2c28ddba6588c912115dc836f82bced7be6876c03e1b2e31cc8ccf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word35p0 : ∃ a b, certified 0 35 a b :=
  ⟨decodeWord 73 0x87609ec3d004e1baadd26c91dcc8a19b74f32711dd8aafe41847b73d2f825b96d70cd81be7aa94b9ebc4cda079856f8fb4f0c9363a07d32c44b08c6599be80a5ee22514ea6c1e6587d,decodeWord 73 0xa079856fcdc6eb825b44b08cb4f0c92ad509ee22c39c6287b73d2fd004e1baadd26c91dcc81be70cd88f65d796a84c53a19ba599be8074f32711dd8aafe41847aa94b93b36c1e6587d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word35p1 : ∃ a b, certified 1 35 a b :=
  ⟨decodeWord 73 0xa0cdc7eb748a6c6f30066599ca9ecf24f201f0b48ce17eeab53d6282be35af91dc17e0ab53a3d49447aa38b987965d12e5b04229c81a85569bd2c28ddba64ca5bad70be679ef21c37d,decodeWord 73 0x8796d7bd88e0ab53a3d49447aa38b9dba64ca59b588ce17ebe82600be679ef2115ea1cc82b44b2e385dc91af8fc0d2105b9767082e716a3501cfc39cccf0b43fb724f276ebc5cda07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word36p0 : ∃ a b, certified 0 36 a b :=
  ⟨decodeWord 73 0xa07985aa3934be8271965d97678c91afe418589c6292d509dcb5b2d7cda6ebc4a3c8cbf04e1be780a5ee2251ad4725f102ce31b48dda0e3dc1e687b92a769bd26c88df1342bce1c37d,decodeWord 73 0x87e6bf40b7dc07d394b92a769bd26c88df1342bce1c39c622fd0043439c6eba8cdd7b04e1be70cd88f6599be80a5ee2251ad4725f1a07985aa966f825ba3c8cbf0b48c91afe418587d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word36p1 : ∃ a b, certified 1 36 a b :=
  ⟨decodeWord 73 0x8796aa3833beaf91dcc8a59b4724f276658ce15d7eeab5b2e3a1511a8571f04e8ddb0dd7cd1556a8b9eb8230c792603f9ccc97d1036c8abbadb4e012d2c2e679c31fed06d42b44a07d,decodeWord 73 0xa042bd886a01cfc37be6c0d2103aaa96872bcc976708ef21d6a1511ae8f426499ba5c876805be18c91addeb4b9eb82beafe5b0b8dc836f30c792603f9c56a83317cdd70bd98f4cf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word37p0 : ∃ a b, certified 0 37 a b :=
  ⟨decodeWord 73 0x8796a8cd713ec1e6be8231c6eb5320ec07d394609ec3aa837ba0f327d004346c39b9b48c678dda0ed7b04e1be780742ccbf0a3c8a5995be1ba4411dd8aafe41847b7dc91add29b587d,decodeWord 73 0xa079856fcda696876c88df13d29b8231c6eb5320ec07d394609ec3aa49ab91dcb53ec1e6be3602ce25f1767ee91d4cb2d70cd88f658cb4b93bbce15d97a5c8a1f0c92a43afe418587d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word37p1 : ∃ a b, certified 1 37 a b :=
  ⟨decodeWord 73 0xa042b0e17ebe24f201af8fd29b82bd886a35a64c1fed97a53dc2e6875b10de15e385b6dc91511ae8aa96d7cd92d6082e71f0ca9ecfc37b600bd9ab47588cb4b929c876ebc5a338677d,decodeWord 73 0x875b97a53dc2e6bea19bd28d653aaa96d78876ebc52ed19ca0cd92d608ef214ea8b9b48c5649addb0d2942af336c03f42610de15e385b6dcc8ccf06f82bde1b37eea1c53916279c37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word38p0 : ∃ a b, certified 0 38 a b :=
  ⟨decodeWord 73 0xa079c3e1baadd211ddb48dda0e6287e6bf40b7dc918c6599be80748aaf45b2d7cda6966f31c6eb829ba5c8a15d2ad509ee22514e1be7f327d004346c39b992aa83e41847589ccbf07d,decodeWord 73 0x87e6bf40b7dc918cb4df1325f1e91d53a15d2ac8a59b48aa83e418589ca079c3e1baadd26c39b992d509ee224ea6966f82ebc4cdd7b043af88767ebe97678dda0e622fd00434cbf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word38p1 : ∃ a b, certified 1 38 a b :=
  ⟨decodeWord 73 0x875b10a042082e82be24f201cf99cac8a59bd26c6fcd15e385569c629447aac3e1bb38b9dba6c28d65d7964cf0b48cb37eea1c5388e0abe679ef21d6a1c7eb742b0b3fb8dc91af337d,decodeWord 73 0xa0422976ebc5cd7185b64992600bf426be3501cf99cac8a54e96d7678fc0a8d9b93aaa08dc91afe517e012d26c8a511ae880b18cb4f0a3d41fed7bace6875be1bb829b589e3d2ec37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word39p0 : ∃ a b, certified 0 39 a b :=
  ⟨decodeWord 73 0x8760918ce1ba39c6eba8cd71965d97d00434be829ba351a07985aac33140a5ee2216e2af8f6507d394b9da0ed7b0432ac8dcb54aadd26c88b4df1325f1767ee91d4cf0c99e56e6bf7d,decodeWord 73 0xa079856f8f6507d320eca53eb48aafe418df135d97d004e1ba452c0cd8b992aa968760918cb2d7cda64df0c99ec331c6eb53a19b82be363b6ad2ab48b7dcc81be78074f32756e6bf7d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word39p1 : ∃ a b, certified 1 39 a b :=
  ⟨decodeWord 73 0xa0cdd7bd886a01cf9942afe517588ce1b37ebe35a64ca59b82eb74c82b0bd91ae8f42649aed210deb4b9875b96aa38c79260dc9151a1f0ca9ec33006d41fed7be6c03fb8836f8f677d,decodeWord 73 0x875b4497d1036c8abb829ba54ea974c82b0bd91ae8f42649aed210deb4f0ca35afe517588ce1b37ebea1c79260dc9151ebb93aaa96d7cda09ec33006d41fed7be6c03fb8836f8f677d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word40p0 : ∃ a b, certified 0 40 a b :=
  ⟨decodeWord 73 0xa09ec3d004346c39678cb2d70cd88fb42f3e6292aa9687b9ebc4a3c8dcb54a79856fcda6c1e6be829bd2ab91af88df13e4185825f17643bce15d97a54f7ee91d5320ec07d32ccbf07d,decodeWord 73 0x87b992aa4a79c39ca0f32756e6bfa8cd71964df0c92a43bce1b2d70cd88fb48c653b6a3602ce316040b7dcc8a1c6eb825b11dd8aaf91add29ba599bed509ee2216e285521be780747d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word40p1 : ∃ a b, certified 1 40 a b :=
  ⟨decodeWord 73 0x87e6588c678fc03fa59bd210de15e3a1f0b4b93aaa94cd7185b6b3d7886a019ecfc37bac4724f2a05391dcc876a7ebc52e82600bd91ae880e1bb442bcc975b964c1fed06d4beaf337d,decodeWord 73 0xa0f4264992aa38b9b4f0a46fcdd7b14229c8dc91ae7985b687e6c03fa59bd26c03e1bb82600bd91ae88076a7965d99ca9ecfc330c7eb5388e012e517588c678f4c1fed06d4beaf337d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word41p0 : ∃ a b, certified 0 41 a b :=
  ⟨decodeWord 73 0x872c0cd8b9926c88767ee91d54a3c8dcb5b2d796aa83e418df135d82ebc43b36af8f6507d320ec7b485825f102cec39ccbf04fa8cda043bce18cb4406f316091add29ba599bee6bf7d,decodeWord 73 0xa0cda696872c0cd8b992aa83e418df135d97678daf45748a6ad2ab91622f713eb48c574a79ee22d509dcb5b2d7bce102ce25f1e91d54a3c8a59b82ebc43b36c1e6be804df0c99ec37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word41p1 : ∃ a b, certified 1 41 a b :=
  ⟨decodeWord 73 0xa0f426499ba4c8a54e96aa946279c31fed06d4be8076ebc52ed1036c8a511ae80bd98fd2ac91af3338b985dcb63db4e012e517cda7c2e6872b44975be1bb8271f0ca9e588cb3d7677d,decodeWord 73 0x87b9db0dea1c5391aed28daf33be805be1bb826092d6082e7185dcb63dc2e679c39dccf0b4e012e517cdc7eba9742b44a0f426d1036c8ad7b18c56499ba4c8a599ef214e96aa38677d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word42p0 : ∃ a b, certified 0 42 a b :=
  ⟨decodeWord 73 0xa09ec3d004f3274a7985aa966f31c6eba8cdd7b08c9152add211dd16e2af8f65995be1ba82bee6bf40a59b5988b4b9926c3934cbf0a3c8dcb587600cd81be7804d20ec07d32c45747d,decodeWord 73 0x87b7dcc8a1c6eba8cda09ec3d0043439b9926c9152add211ddb48a579ba54f7ee91dda0e622f3ec1e6be975c4574f3274a7985aa966f82bce18cb2d7678dafe41820ec07d32ccbf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word42p1 : ∃ a b, certified 1 42 a b :=
  ⟨decodeWord 73 0x875b10deb4f0a4c8cc97d103336c6f30c7eb829ba54e96aaea1c538876658c91dc6294cda7589fc37be6c03fb883e5171fed06d42bb93abde17ebeaf44b3d70bd98fd2ac4724f2a07d,decodeWord 73 0xa05388e0125d87e679c3aa964ca59b4724f2ea1cdb0dd7b142afe5171fed06d42bccf0a4c876658cb4b93a3501cf9abe80e1bb82ebc52e3d6294cda7589f6ad2ac91dcb8836f8fc07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word43p0 : ∃ a b, certified 0 43 a b :=
  ⟨decodeWord 73 0x875c11dd8aafe418cda64d20eca57ee91dda0e6292aa39c6eb829b74f327be976734cbf0a3c8dcb54a798552add26c918cb2d7966f8fb4b92ad5092f3ec1e6599ec3d004e1ba45a07d,decodeWord 73 0xa0f327be97a5ee22d5092f826140b7dcc8a1f0c93665d7b08cb48d7196a8cd16e2af88df135e87e6bfd2ab916a94b9ebc43baa4a7985524f7ee91dda0e2a43bce102cec39c579b747d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word43p1 : ∃ a b, certified 1 43 a b :=
  ⟨decodeWord 73 0xa0f426bee6ae79ef214ea9748abb38c7926c9dccf06fcdd796aac3d103e18c6798a5c8a251eb826091dcb6875b44b37eea1cdb0d29d6082e3db4b98556499bd210de15e3af8fc0337d,decodeWord 73 0x875b44a0f426be82bd8876a74ca59bd210de15e3af8f6798d103e18cb37eea1cdb0d29c8a251ebc53a35c2e65883b9b43f3006d41fed7bac47b8dc9162936c9dccf06fcdd796aac37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word44p0 : ∃ a b, certified 0 44 a b :=
  ⟨decodeWord 73 0xa079ee2216e285521be7aa964df0c9c8a1c6eba8cd713ec1e65988df1325f1767ebe97a59bd2ab48b7dc07d394619ec3d0046c39b9875c452c0cd88fb42f82bce1b2d7678c91af347d,decodeWord 73 0x875c45b2d7688fb48c57e6bf3439b985aae91dda0e2ad509dcb54aadd29b82bce102ce31406fcda6964df0c9c8a1c6eb5491afe41820eca599be8074f32711dd8a6a94619ec37ba07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word44p1 : ∃ a b, certified 1 44 a b :=
  ⟨decodeWord 73 0x87e6c0d29b588cb4b9db0dd7b1e1c3303fa54e96a9747ebe985b442bccf0a4c8dc06d41fed7bac47b8836f82ebc53abd88e012e517cda0f426d103336c9d6293aaea1c5391af8f677d,decodeWord 73 0xa0f42649aed29b588c91af90b4f0ca29425d9a653abd88e012e517cdc7eb827185b6b3d70bd9b9876c9d6293aaea1c53a4c8dc06d41fed7be6c033be8076a7964ca53d2ed103e1c37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word45p0 : ∃ a b, certified 0 45 a b :=
  ⟨decodeWord 73 0x872c45a0f32711dd16e2af8fb42fd004343968975c96aae91d5491dcb53e6392d509ee22c39c574a79856fcda64df0c9c8a1c6ebb9da0ed7b08ce1ba82be80a59b748a6ad2abe6bf7d,decodeWord 73 0xa054918ce1baadd211dd16e2af8fb42f829b748a574a79ee22d509dcb53e63926d9ccbf04fa8cd71965e99663b3602cec3aa83b9ebc4a3c8a57ebe25f1e91dda0ed7b0432a87e6bf7d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word45p1 : ∃ a b, certified 1 45 a b :=
  ⟨decodeWord 73 0xa042bd8876a7589fc37b60dc9151aed29b47aa964ca5c8a2f0ca29876c6f90b4e01224f201cf303fb883b993d608ef2115e3af333867985be18cb37eea1cdb0dd7cdc7eb82bee6c07d,decodeWord 73 0x87e6c0a9748b56499ba5c8a2f0ca2942bde15d9a65d7cdc7eb82be353aaa964c1fed06d495b985716ad2ac5391dcb63d2ed103f42610de15e3af90b48cb37eea1cdb0d6279c39da07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word46p0 : ∃ a b, certified 0 46 a b :=
  ⟨decodeWord 73 0xa043af886b9461403107d32cb9da0ee91d5491dcb54a79ee22c39c5716e2856f8fb4df1325f1769ba57ebe82ebc4cda64df0c9c8a15e87e6bfd2abbce18cb2d796aa396897d004347d,decodeWord 73 0x875c11dd8a5716e2af916392d509ee22c33140b7dcc8a59b82ebc4cda64db2d796aa39346d9ccbf0a3708fb4b9da0ee91d54837b4825f102ce99668ce1baadd2c1e6be80742c45a07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word46p1 : ∃ a b, certified 1 46 a b :=
  ⟨decodeWord 73 0x875b96aac31fed06d42b44b3d70bd9b993609f6a01cf9a653abde18c91514ea9cd15e310de8b5649aed2c2e67985dcb63d2e829ba5c81ae88076ebc5a46f90b4f0ca35afbe24f2a07d,decodeWord 73 0xa0f426be82bde1c31feda5c81ae88076a74cf0ca9f6a01cf9a658c91afe517cdc7eb53847b60dcb63db48edb0d29875b44b3d796aa38b993d6082e71a29b475889e012d2ace6c0337d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word47p0 : ∃ a b, certified 0 47 a b :=
  ⟨decodeWord 73 0x8796d7b08c57e6bf3439b92a435e8dda0e63926d8aafe418df13d2ab48aa837ba09ec3d004e1ba829ba37031b440b7dc9152ebc4cda64d20eca5996607d3be25f1767ee91dc8cbf07d,decodeWord 73 0xa07985aa4aadd211dd16e2af886b94619ec320ec07d3be36c1e687964d5491dcb53eb42f72a19b82ebc4cda6598cb2d76897a57e75f327d004e1ba39b92a435e8dda0ee91dc8cbf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word47p1 : ∃ a b, certified 1 47 a b :=
  ⟨decodeWord 73 0xa0cdd7965d87e6c0d29b589fc37bac47b8dc918cb37ebed6086798d103e1bb442b0bd990b4f0ca353aaa84b9936c6f82603f30c7eb53a4c81ae8f42610de8bafe5171feda54ea9747d,decodeWord 73 0x87b9936c6f82603f30c7eb53a4c81ae8f426d103e1bb442b0bd990b4e012d29b589fc37bac47b8dc06d41feda57fbee6c033ccf04ea9748baf918cb3d7965d9a653aaa84e517cda07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word48p0 : ∃ a b, certified 0 48 a b :=
  ⟨decodeWord 73 0xa0cdc6eb82be97a59bd2ab5483708fb4b93bbce15e876d8aafe418df1325f102ce3140b7dcc8a1f0c936c1e6599ec37b48aa96a8752c45b2d70cd81be7804d20ec07d39461918c687d,decodeWord 73 0x876d8aaf45b2d70cd8b9b4df13e418599ec37ce6bfd2ab918c6897a59b4825f102ce3140b7dc6392aa96a875c8a1f0c92ad509ee224f7ee91d5483708f5ce1ba3934be82ebc4cda07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word48p1 : ∃ a b, certified 1 48 a b :=
  ⟨decodeWord 73 0x87e6c0d210deb48eafe51758896a353abde101cf24f276a7ebc5cdd7b14e96aaea1cdb0d6295b929c8a2f0ca9fc3303fa57fbe985b44a053846f829b47b8dc06d41fed7bac918c677d,decodeWord 73 0xa053846fcdd7b1425d87e6c03f30b48e659abe81a54e96aaea1cdb0d6295b929d608dcb6497aef21c39d56a974f426d103336c8bafe517e012d2ac918ce1bb38c7eb829ba4c8ccf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word49p0 : ∃ a b, certified 0 49 a b :=
  ⟨decodeWord 73 0x87b7dc91521be780a599663baa837ce6bf4031c6ebb9b4df135e8dda0e6392d509ee2216e2af886bd2abbce18c574a9ba37082be25f1a0cdd7b0432ac877a6964df0c99ec3d004347d,decodeWord 73 0xa0f327be82ebc42f3ec1e67a85aa4a9ba370cdd7964df0c99ec3d004346d8aafe41820ec07d394610cd88f5c45b27fe91d5491add211ddb4b92a87b7dcc8a599663bbce18c57a8757d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word49p1 : ∃ a b, certified 1 49 a b :=
  ⟨decodeWord 73 0xa09f6a95b93a3501cf24f2ea1cdb0dd7b142af90b48b56e6c0a9cdc7eb5384e517e0125d8796aa497aef21d6082e71a29bd2ac918c67742bccf04e7fbe98a5c8dcb63d6282bde1c37d,decodeWord 73 0x87e6c0a9cda07a86aa964cf0ca9f6ad2ac918c67905b10de15e3af44b3d70bd91ae8f426d1033338c7eb53a46f30b48b56499b82bde1c31fed06d42bb993603fb8dcc8a59abe81757d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word50p0 : ∃ a b, certified 0 50 a b :=
  ⟨decodeWord 73 0xa0432ad5092f3eb4f0c99ec37c610cd8b9926d8a57e6bfa8757fbe97d004f3274aadd211dd16e285aae91dc8dcb587964d20eca59b8272a15e8d663bbce18cb2d7cdc6eb5491af347d,decodeWord 73 0x87b7dcc82c45a0cdc6eb82bce17fe91d54a37084e418df1325f102ce99beaf918cb4f0c99ec37c61403107d320eca59b4859886bd2abe6bf3439688f5c96aa94b9da0ed7b04fa8757d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word50p1 : ∃ a b, certified 1 50 a b :=
  ⟨decodeWord 73 0x876c9dccf04e96d7b18c569bd2ace6c0a9cdc7eb827186aaea1cc8a251a0425d8e6506d42b0bd9b9936091dcb6497aef2115e3af89e01224f2777fbe98a53db42ec3d103e1bb38337d,decodeWord 73 0xa053a4c81ae8814cf0ca9f6a87b8dc916295b9db0d29d6082e82ebc5cda7c2e6aed29ba59a65d7b18ce1bb3833beaf44758b56497aef2115e386aa965d8e723db4e01224f201cfc37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word51p0 : ∃ a b, certified 0 51 a b :=
  ⟨decodeWord 73 0x872c45b2d7cdc6eba8757fe91dda0e6394b9b48c91dcb54aad7a8672a152a0f32711dd16e2af886bd29b82bce15e8d663b3602ce99bed5092f3ec1e6599ec3aa964d20eca5c8cbf07d,decodeWord 73 0xa0432a87b7dc918cb4403107d320ec7cab48aae91dda0e6394b98672a19b82bce1b2d7965e8d663b36afe418df1325f102cec39c57e6bfd26d8b524fa8cdc6eb757fbe97a5c8cbf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word51p1 : ∃ a b, certified 1 51 a b :=
  ⟨decodeWord 73 0xa0cda7c2e6aed29b75f426d1033338c7eb53a4c8a57fbe9867905b10de15e3af918ce1bb8272964cf0ca9f6a872b44b3d70bd91ae8aa84b993603fb8dc06d41fed7c475889b42ec37d,decodeWord 73 0x87b993603fb8dc06d41feda57fbe9867905b10de15e3af9151ebc53a3501cf30b48b6bd2ac4724f2779ba4c82b44b3d70bd91ae8aa847ca0cda7c2e6588ce1bb8272964cf0ca9fc37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word52p0 : ∃ a b, certified 0 52 a b :=
  ⟨decodeWord 73 0xa0f3274aadd211ddb48d72f0c99e6b87b93b36af452c0cd81be7aa964d20ec07d39461dc9152ebc4cdd7bc8977a6c1e67ac3d004e1b27fbe975ca3c8a59b823140b784e418598c687d,decodeWord 73 0x87b7847ce6bf4031b4df13e418cdc6eb5491dc6392aa964df0c99e6b02cec320ec07d32cb93b36af45b2d7bc8977a6598ce17fbe8272a15e99668eda0ee91dc8a59bd2ab4825f1a07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word52p1 : ∃ a b, certified 1 52 a b :=
  ⟨decodeWord 73 0x875b10deb48e653abde101cf30c7eb53a4c81ae8f426497aef21d608dcb63dc2e6588cb3d79670829ba59abe81758b6bd2ac916295b9db0d2942af33ccf04ea9cd15e386aac39da07d,decodeWord 73 0xa042afe517cda74cf0ca9fc3aa847c4724f2ea1cc8a251ebc52ed103e1bb3868336d89b4e0125d8edb0d2987b9936091aed29b827296d7b18c56e6c03fb8dc06d41feda59abe81757d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word53p0 : ∃ a b, certified 0 53 a b :=
  ⟨decodeWord 73 0x876d8bbad796aa3968975c452c0cd81be781b0b7dcc8cbf0b4df13d2ab485984b9926140a59b82be36c1e67aee22d5092fc39ca0f327d004e18c91524f8eafe418cd72a1c6eba8757d,decodeWord 73 0xa0cd16e28672a15e996607d320ec7ce6876d8bd796aa39b9ebc42fc39c574a936140a59b82be3602ce25f177a64d54918ce1baadd211ddb4f0c9c8dcb5b27fe91dda0e2a43af90bf7d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word53p1 : ∃ a b, certified 1 53 a b :=
  ⟨decodeWord 73 0xa07ac39d56a9cd723d2ed103e1bb829b75f42610deb48b6bd2ac47b8dc6295b9db0dd7b14229d608ef2115e386aa38c7eb53918c6833ccf0a4c81ae8814ca59abeaf905b9687e6c07d,decodeWord 73 0x87e6c0d2ac53a4c81ae8814cf0ca2942bde101cf9abe82ebc53a35668cb3d70bd9b9b48b6b956191af905b9670303fb8dc06d41feda59b75f42610de15e386aa497ac39d56a9cda07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word54p0 : ∃ a b, certified 0 54 a b :=
  ⟨decodeWord 73 0xa0435e99be81776607d32c0cd890bf40a5ee224f96aa39b987e6598ce1b2d7bc89b4df13d29ba3c8dcb54aad7ac39c6395c42f82eba8cd16e286726b02ce25f1e91d5491af34cbf07d,decodeWord 73 0x87e6598c91521be7f327d0046d9c638272f0c936afbe81b0e15e9ac8a19bd211ddb48bbad70cd890bf40a5ee224f96aa39b9eba8cd16e286dcb54aad7ac331c693d50968752c45a07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word54p1 : ∃ a b, certified 1 54 a b :=
  ⟨decodeWord 73 0x87e6c0a9cdd7b1b8dcc8a2511ae80bd990b48c91af89e0125d9abe8175f42649aed26d38c7ebb993aa84e5171feda53d632ed103e1bb44a07ac39d569b8272964cf0ca29d60868337d,decodeWord 73 0xa042bde101cf9a5c10de8b6bd2ace6c0a9cdd7b1b8dcc8a2f0ca356606d495b9872b0bd91ae8f426497ac39d632e72964c53918c569b82ebc53aaa84e5171feda53db48eafbe81757d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word55p0 : ∃ a b, certified 0 55 a b :=
  ⟨decodeWord 73 0x875ce18c91add29b48599ec37ce6bf40a5ee2216e211ddb4f04f8eaf452c0cd8b98672a1521be7aa96d7bc896b95c43b3602ce3107d3be25f1a0cda6eb8261dcb5b27f75c8cb98687d,decodeWord 73 0xa043af904d20eca59b48b784e418599f3ec1e67ac3d0043439c6eba8cd72f0b4df135e87b9da0ee91d54a3c8dc63823107d3be25f193aa96d7bc896bd2ab918ce1b27f752ccb98687d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word55p1 : ∃ a b, certified 1 55 a b :=
  ⟨decodeWord 73 0xa0f426be82303f70cda74cf0ca3501cfc39d569ba5c8a2c7ebb93abde18c91dcb687e6c0d2ac53847c47aa96d7b14229d608ef2115e3af90669a5c10deb48b6b95610bd91ae881757d,decodeWord 73 0x87e6c0d2ac53918ce1bb38b9b4e0125e98688eafe517cda74cb3d796aa95610bd91ae881758b6b3501cfc31fed06d42b44a0f426be82ebc5a4c8dcb6497a8670303fa59b599dccf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word56p0 : ∃ a b, certified 0 56 a b :=
  ⟨decodeWord 73 0xa0432a87e6bfd2ab54a37082bce1c37c61dcc877663baa4a9ba5ee224f8eaf918cb27fbe25f1e91dda0ed7965e9ac936026b89df13e418599fce3107d395c4cda6ebb986b53eb4f07d,decodeWord 73 0x87e6ad7ac3e1ba8272f0b440b784b93baa4a9bd2c18eaf918cb27fbed5092fd09d5716e2a252eba8cdc69361dcc8a5ee224f965e9ac936026b89df1325f1e91dda0ed768752c45a07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word56p1 : ∃ a b, certified 1 56 a b :=
  ⟨decodeWord 73 0x87e6c0a9cda053a4c82b5c4475f426d1036d89b48e72964cf0ca356606d495619f579b82303fb8dc91aed210de15e3afbe98a57fea1cdb0dd7b18ce1bb38c7ebb986aa497aef21c37d,decodeWord 73 0xa054a29b82bde1c31fed06d495619f57a9cd72964cf0ca35668cb3d70bd990b48b6b01cf303fb8dc91aed210de15e3afbe98a57fea1cc82b5c4475f426497a86aa38c7ebb987e6c07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word57p0 : ∃ a b, certified 0 57 a b :=
  ⟨decodeWord 73 0x87e6599fcec37cab54a4d395c42f3ec18e668c91af3439b9eb09ee224fa8752ccb98a5c8dcb7847082610cd81be7f327be815c96aa4a9bd26d8bd7b043bce102f0b4df13e418cda07d,decodeWord 73 0xa0cd16e211ddb4f004e1ba829b48aa9687e6bf4031079ac92a435e7fbe25f1e91dc8dcb78470904d20eca50e637ac3d09d57a9d8b9eb54a4d395c43b36af91add26d8bd7b08c68757d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word57p1 : ∃ a b, certified 1 57 a b :=
  ⟨decodeWord 73 0xa07a86aac3303f7090b4e012e517599d6393d60868336d38b9db0dd7b14e96a9cdc7eb541feda59b82beaf89777fea1cc8a25e98d103f42649aed2c2e687b8dc918ce1bb442bccf07d,decodeWord 73 0x87e6c0d2ac4724f201cf9a5c96a9cdc7eb541feda54f1ae88175c8a29b82beaf89e012e517599d6393d60868336d38b9db0dd7b1b8dc918ce1bb442bccf0b48e723d2ec3aa847ca07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word58p0 : ∃ a b, certified 0 58 a b :=
  ⟨decodeWord 73 0xa09fc3e1ba829ba5c82cb9a7964d20ec98d004f327bed5092f3eb48c57e6875ca45491dcb7847c61936d70cdc6eb758bd70cd81be781b043afe418df13d2ab48aa396890bf34cbf07d,decodeWord 73 0x875ce1ba823107d3be25f102afe418df13d2c18e669ac936a7964d20ec7c6140b78470cda09fcec3aa4a9ba5c8dc91521be781b0432a77ebb93ba2c6936d8bd70cd8ace6598cb4f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word58p1 : ∃ a b, certified 1 58 a b :=
  ⟨decodeWord 73 0x87e6c0a9cd7284e517e0125e829b599dccf04f1ae8f42649aed26d89777fbe98a53d2ed103e1bb44a07aef2152ebc5a4c82b0bd990b4b93a35af918c6606d49561dcb6b3d796aac37d,decodeWord 73 0xa07aef2152ae4824f201cfc3aa96d7b1e1bb442b0bd990b43f3006d49561dcb687e6c03338b9ebc5a4c8a54f1ae881758bafbe829bd26d918c669a5c10de15e38670cda7599dccf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word59p0 : ∃ a b, certified 0 59 a b :=
  ⟨decodeWord 73 0x87b9a7ebc43ba252a0f327be815c459868758bbaaeddb48c9163829ba5c82c0cd81be79d574a93d5092fd004e1b2d796aac37ce6bf40b7dc84e418cd726bd211ee224f8eaf34cbf07d,decodeWord 73 0xa054a4e418cd7286dcb54a93d5092f3ec1e67aee224f8e1325f102cec3aa39c6eba9dfacbce1b34598a5c82c0cd81be79d579bd26d8bd7965e87b9b48c68757fbe826191af34cbf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word59p1 : ∃ a b, certified 1 59 a b :=
  ⟨decodeWord 73 0xa07a8670cda796aa4a15e3af44b3d70bd990669a5c10deb43f3006d495619fc3d1033338c7ebb92987b8dc918ce1bb82be81758b6bd2ac541feda59ba4c8ccf04f1ae8f42657e6c07d,decodeWord 73 0x87e6c03fb8dc91aed26d89e0125e82bde18cb343afe517485924f2ea1c54a29b75c8ccf0b4b929d6082ed1033338c7eba94d1feda57fbe98688edb0dd79670cda07a86aa95619fc37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word60p0 : ∃ a b, certified 0 60 a b :=
  ⟨decodeWord 73 0xa0cdd7bc896bd28eda0ee91d5491dcc8a59b82eb757fbea2c693d5092f7286b53e637ac320ec13e418599fce9ac936af452cb1e15e87e6bfa9b93baa964df004f3274aaeddb48c687d,decodeWord 73 0x87e6be8177eb829bd26d8bd7cda0f327d09d574aaedd16dc07d395c4a43934cbf07084e4b1b8aa964da5c82cb9daa7c18eaf04e1ba45985c11ee22c37c6191521be70c4031b48c687d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word60p1 : ∃ a b, certified 1 60 a b :=
  ⟨decodeWord 73 0x876d91aed29b752b5c4510de8bafe5174824f201cf9abe81a54f1ae8aac39dccf0a4c8dcb63db48c688e72847ca0cda796d7b1e1bb8230610bd9b993d608ef2152ebc53a35c2e6597d,decodeWord 73 0xa07a86709066d7bde1b3435e8230619fc3aaea1c4d1fed06d495b9db0d3eb48c91afe517cda79687b8dcc8a57fbe98d103f42610de8b6bd29b752bccf0a452ebc53a35c2e6ae48597d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word61p0 : ∃ a b, certified 0 61 a b :=
  ⟨decodeWord 73 0x87964d20ec07aa39b9daa75984e4b18c91ae2f82eb541dc8a50ed7cd72f0c92ad5a2c69361dc18df135e9a43bce17fe9b63eb48b6d0434beaf906875f3274a9bd2c1e67ac3d09da07d,decodeWord 73 0xa09fe91d54916395cd72f0c92a77668eaf45b3e286dcc8985c11dd1657a9d8b93baa092f82ebc4a4d32081e18cb4acbdec7ce6bfd29b48b840a54f96876d8bd70cf327be3602cec37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word61p1 : ∃ a b, certified 1 61 a b :=
  ⟨decodeWord 73 0xa07aef21524f1ae88175f426d1036d89b4e0124329c8a2f0ca9f579ba59abe353aaa9687e6c0d2acbde15e827284b9db0d3e6393d608688eafe51748b8dc918cb3d7cda7ebc52ec37d,decodeWord 73 0x87b986aac39dccf0a4c82b4510deb48b6b01cf30c7eb541fed7ca0f42657e6c0400bd990669abe353b06d49561dcb64a15e3af918cb3d7cda79670825ce1bbaed29ba54f1ae881757d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word62p0 : ∃ a b, certified 0 62 a b :=
  ⟨decodeWord 73 0xa043afb1e15e7f75f32711dd8bd7cd16e21dc8dc07eba9d8b986726b02cec37ce6bfd28e669ac99f598cb440b8e7aa95c42f82be363bbdeca59b48ac54a4d32091630e2a87964df07d,decodeWord 73 0x87b9daa7eb092f827286dc1820918cb4f04f965e7f75f327113bbdec7ce6be36026bd29b48599fce9ac92ad5a252aedd8bd7cdc693610ca5c81be4b1e1c3aae9b63ec2a043af90687d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word62p1 : ∃ a b, certified 1 62 a b :=
  ⟨decodeWord 73 0x8761916b353bbbd7688eaf89e012d2ace6c0400bd9b993d608dcb6b3435e29c8a29ba59abe24f201cfc3e18cb4f0ca9f574a15e386aa96708230c7eba9cda07aef21524f1ae881757d,decodeWord 73 0xa07aef2152ebc52e827296aa84e51748b8dc06d495b9db0d3ec2346d916387e6aed210deb48ce1c3d103f426be98a59ba4c82b5c45b14f1ae881758baf90663bbbd7cda7599dccf07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word63p0 : ∃ a b, certified 0 63 a b :=
  ⟨decodeWord 73 0x87b9da0e2a77eba934c0d29b48599fce25f1026b89b4df13e41820ec07d395c43baa96d768904da5c81b86dc9152a25e9a43afb18ce17fe9b63e637ac331ace6be82bdcbf070cda07d,decodeWord 73 0xa0cd93d509dcc8a50ed768904d209152a2c716e211ddb48b6d7084b9875c96aa3934c0d29b48599fce9a43afb18ce17fe91ddaa7eb752ccbf004f327b63e637aeebb82bee6ae2fc37d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word63p1 : ∃ a b, certified 1 63 a b :=
  ⟨decodeWord 73 0xa07aef21d60839688edb0d3ec2e6aed26d918cb4b98670cdd79687b8dc6393aaea1c54a2f0ca9f57a94db343bde1c330c7eb829ba5c82b5c10de8bafe5174824f2777fbe98d103347d,decodeWord 73 0x876d918ce1bbaed2c2e6599dccf0b440b64a15e3af89e01224f2779ba4521ae80bd990663b06d41feda57fbe3601cf9a5c45b14fa7eb827284b929c8dc6393aa96d7cdc72fc37ca07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word64p0 : ∃ a b, certified 0 64 a b :=
  ⟨decodeWord 73 0xa0f3c040a5bb45b3e2a29bd211ee22d5092fc53b36af9068757fe9b687e6598ce15e9ac99fc3d0046d70847c6191aeddb48b521bd796aa4a930e2ac8dc18cd27be82ebb9daa74df07d,decodeWord 73 0x87e6599fc3aa96d71d5489b4dfac91af34cc2c45a0f3c040a5bb39c73107d320ec7c61930ee9b64a9bd28e668ce11325cd16dcc877815c98d0046d7084e4b14fa9d8b9eb82bea2f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word64p1 : ∃ a b, certified 1 64 a b :=
  ⟨decodeWord 73 0x876191dcc82b0bd91ae881a54fa75924f2a07aef21d60839688e7296aa84b9936d89779ba452eb82beafe517e012d2c2e6ae48b83eb4f0ca9fc331c5cdd7bde18cb3435e98d103347d,decodeWord 73 0xa07aef21d60839688e7284b993aa965e98d10334be82eb54a2f0b440b64aace6c0d29b75f42610de8b6b876191dcc82cca9fc331c5cd15e3af45b18ce1bbd70bd91ae881a54fa7597d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word65p0 : ∃ a b, certified 0 65 a b :=
  ⟨decodeWord 73 0x87b9da0e2acabbaedda7eb827286dcc898a54f96aa3934c0d29b48b8403107668eafe4b1435e7f75f32711e102f0b48c91521be718c5a4d3bee6599fcec320ec7c61936d8bd7cda07d,decodeWord 73 0xa0cdd78918df132548b8aa39c731acbdcc96872c0cd8b9eb82726b36a74da59a4309ee22c3d191521be7815ca4d3bee67a86dcc877668eafe4b1e1029f3e6395f3c0d29b598cb4f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word65p1 : ∃ a b, certified 1 65 a b :=
  ⟨decodeWord 73 0xa07a867031c5cda7eb541fed06d4be36c0d2ace65924f201cf9a5ca4c8a57fea1c4db3d70bd990663bbb829b752cca9fc3e18c91dcb83e63936d89e01243afe51748aa9687b9b4f07d,decodeWord 73 0x87b9b4e01243af91dcc82cca9f57e6aed2c234bed608ef214f1ae881a59b758b6b956140b6b3d70bd990668ce1c37ca0cda796aa4a15e3867031c53bbb82eb54a25e98d125f201f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word66p0 : ∃ a b, certified 0 66 a b :=
  ⟨decodeWord 73 0xa0cd936d708231acbdec7ce6872c0c6191524f96d789df13ca9f598ce1c3d1b825f102f0b4b9daa7eb757fbea2c7169b48aae91dc040a5c8985c45b3e286dc07d320d28eaf3439687d,decodeWord 73 0x875c45a013ca9fe91dc034be8177eb09dc84e418c52f82619152aedd8b6d70cd93aa964df0b440a5c898d1b825f1024a9ba439b9daa7598ce1c320d28eafb1d42c0ce67aeebbd7687d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word66p1 : ∃ a b, certified 1 66 a b :=
  ⟨decodeWord 73 0x8761916b95b9db0d3eb4e01243af89779b82eba9cdd7b1b8dcc82cca9f57e6be36c0d2acbde18c688e7284e51748aa965e98d125f201f0a4524f1ae881a5ef21d60839c72fc37ca07d,decodeWord 73 0xa07a867090668c91638796aa0839c72fc3e1bb82eba9cdd7b1b8dcc82cca9f57e6beafe5174803f427cf9a5c4510deb4400bd9b993d620eda57fea1c4df0a452aed29b758b6b36c07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word67p0 : ∃ a b, certified 0 67 a b :=
  ⟨decodeWord 73 0x8796ca36afbe817766d71dc8a54f8eda0ecfc37ce6aedda7ebb92ad6b3e211e15e9a4309ee22bb39c731b48b6d04f3c0d29b18cda09f598c274a93aae9b63e63827286dc9152a2f07d,decodeWord 73 0xa0cdd768757fe9b63e0ecf31b48b6d70826191dc84b92ad60745985ce113e4b14f8edbaedda7eb541dc8a5ee22bb39c7169bd2c2f1029f598c274a93aac37ce68796ca36afbea2f07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word67p1 : ∃ a b, certified 1 67 a b :=
  ⟨decodeWord 73 0xa07aef22d49561916bd29ba59a5ce1bb4510de15e3af89b48e729687e6c0400bd91ae8aa84b9eb0839688cb3d7cdc72f82be8175f427cfc39d0334cc2ac8dcb64aac54a2f04fa7597d,decodeWord 73 0x87967090b4f04fa7eb0839688cb3d7cda07aef22d49561916bd29ba59abe81758bafe517e01243bde15e8231c5a452ae48b8dcc82cca36019fc3d125f21be8aa84b9db0d3ec2e6597d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word68p0 : ∃ a b, certified 0 68 a b :=
  ⟨decodeWord 73 0xa09fe9b6cfc320d49548aa9687e6598470cdc79b82bdec0745b3e2af904da50e2acac81bd7896bd2c2f177669a5e7fbea252eba93439b9dbaeb42f3e637a2711dd16dc918ce102f07d,decodeWord 73 0x87965e7f22c39da0f3c0d26d8bd7cd7286579ba5eebb39b9db1dc89868752ccc11e18c9152aede16dc6382eba94f8eafe4b14309d49548aae9b63e0ecf257ce6bea2c731b4f004347d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word68p1 : ∃ a b, certified 1 68 a b :=
  ⟨decodeWord 73 0x87610b40b6b343af91dcc8a57fbe98d125f2ea1dd9906606ebb993aa84e517e0125e8231c53bbbd7cd7296a94d54a2f0b48ce1c39da07aef22d42cca36014aace6c0d26d89779b597d,decodeWord 73 0xa07aef22d495b9db1be8f427cf9a5c10906606aa84e518de8baf45b1b83ec2e6ae480334be81752cca9fc3e18cb4f0a4524fa7eb8231c53bbbd7cd729687610ba5c8dc916bd29b597d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word69p0 : ∃ a b, certified 0 69 a b :=
  ⟨decodeWord 73 0x87b8e718cd274a9bc5a439135e7f75c898a53e0e6382de8bd7961ddb026bd2c2f193aac3e1b3e2afbee67aee22d68c579da043092fd1bbaeb4f04fa934cc2cb9eb5491dc847090687d,decodeWord 73 0xa09fe9b687b9eb548977815ce1c320d42ccc96d70c6191cf3107aa3913d28e668cb34598a53ec2f1936d7082deb4f04fa934beaf04d9acbdec7ce659841dc8dc18cd274a9bc5a4e57d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word69p1 : ∃ a b, certified 1 69 a b :=
  ⟨decodeWord 73 0xa07ac39dcc2a779bd210de8bafe518ef22d495b98670cdc72f825c45b1b8dcc8a57fbe98d125f21be8aa96d7bde1014aac54a2f04fa7eb0839688cb48edb0d3ec2346d916387e6597d,decodeWord 73 0x87e60d3eb48eafe518ef22d49561918c663b06aa847ca0cdc72f7296d7bde1c39dcc2a779bd2c2346d89e013ea1dd9b9eb825c45b1b8dcc8a57fbe98d125f2014aac54a2f04fa7597d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word70p0 : ∃ a b, certified 0 70 a b :=
  ⟨decodeWord 73 0xa0432a87e6599f3e637a27d1bbcac877eb82beafb1b8aac320ec985ce17fe91ddb024a9b18c5cdd70ca54f96a93439b986dc07668e13e5a454896bd2c2f193d68c91aedeb42f72f07d,decodeWord 73 0x875ce17fea0ecf25f193d68c91afbe36c2ca2a77ebb9a7964da5c89809dc6382deb4f070847ce6aedb1d54896b024a9b18599f3e2fc5cdd7bdec13e5a4396890d222c3aab6b345a07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word70p1 : ∃ a b, certified 1 70 a b :=
  ⟨decodeWord 73 0x876140b6dc916bd29ba452eb8231c53b0645b18c669a5c96aa4aacbde113ea1df427cfc39dcc2ac8a5ef22d495b9db0dd7cda07a867090b4e016e3af89777fbe3601f04fa7c2e6597d,decodeWord 73 0xa07a86aa0839c72f82eb54a29bd26d91dcb83e6393d620ed13ea1df427cfc39dcc2ac8a59a5ce1bb45b18c66d7cd729687b9db0ee518deb48eaf89777fbe3601f04fa7c2e6ae48597d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word71p0 : ∃ a b, certified 0 71 a b :=
  ⟨decodeWord 73 0x87b8aa39b9b4f070847c61936d0434c0409dcc2c45a0cdc7168bd70ce8f3274a9bd28eaf91dcc8a5ee22d607eb757fbea2e3115c98d1bb82dea7964d541ddbb1e1c331ace6598c687d,decodeWord 73 0xa0432a875c98eda5c8ccc03439b9a7964df0b42fd1bbaedb1d5489e082eb757fbea2e31190d222d607aac3e102afb18c91dcb8409de8f3274a9b18c5cd726b95637a8657e60ed7687d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word71p1 : ∃ a b, certified 1 71 a b :=
  ⟨decodeWord 73 0xa07a8670cdd796a94d54a2f0b4e013ea1df427cf9a5c45b18ce1c331c53bbb82ebb9936d91ae48aa08688edb0ee518ef22d4be81a5c8dcb83e63872cca9f57e6c0d29b758baf03347d,decodeWord 73 0x876191af0334be81a5ef07aa4aacbd39c72fc3e113ea0cf427cf9a5c45b18c688edb1be518de8b6bd2c2e6599dcc2a22d495b9eb829b75c8dcb83eb4f0a4524fa796d7cd72847ca07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word72p0 : ∃ a b, certified 0 72 a b :=
  ⟨decodeWord 73 0xa0541dc8cc2c0c6193aa39bb82beaf904df0b4b9a7598ce1c33140b8d191aedb024a2711e3a2c716de8bd7cd726b36c2f177eb09dc847ce687965e7fea9feda59bd222d6b34598687d,decodeWord 73 0x8796aa39bbd789e018c5a4e513d26d04d9ac541dc034beaf91cf31b4b9a7eb75c8cc2c0ce89d57e67a86dc07eda59b826140b8d4b18ce1c320815c459868904df070cd274a93f2a07d,by decide +kernel⟩
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem word72p1 : ∃ a b, certified 1 72 a b :=
  ⟨decodeWord 73 0x8761916b3601f0a4524fa7599dcc2ad620eda57fea0cd9b993aa4aace6c0d29b75c8dc18de07eb82beaf89b440b6b343bd3913e31df427cf9a5c96d7cdc72fc3e18c688e72847ca07d,decodeWord 73 0xa07a867090668ce1c331c5cdd7965e98d125f20ee5113bbbae48aa09e0168baf45b14fa7599dcc2ac8dcb83eb4b993d620eda59bd2c2346d916387e6be82eb54a2f004db1be881757d,by decide +kernel⟩
theorem all_certified (p r : ℕ) (hp : p < 2) (hl : 24 ≤ r) (hh : r ≤ 72) :
    ∃ a b, certified p r a b := by
  interval_cases r <;> interval_cases p
  · exact word24p0
  · exact word24p1
  · exact word25p0
  · exact word25p1
  · exact word26p0
  · exact word26p1
  · exact word27p0
  · exact word27p1
  · exact word28p0
  · exact word28p1
  · exact word29p0
  · exact word29p1
  · exact word30p0
  · exact word30p1
  · exact word31p0
  · exact word31p1
  · exact word32p0
  · exact word32p1
  · exact word33p0
  · exact word33p1
  · exact word34p0
  · exact word34p1
  · exact word35p0
  · exact word35p1
  · exact word36p0
  · exact word36p1
  · exact word37p0
  · exact word37p1
  · exact word38p0
  · exact word38p1
  · exact word39p0
  · exact word39p1
  · exact word40p0
  · exact word40p1
  · exact word41p0
  · exact word41p1
  · exact word42p0
  · exact word42p1
  · exact word43p0
  · exact word43p1
  · exact word44p0
  · exact word44p1
  · exact word45p0
  · exact word45p1
  · exact word46p0
  · exact word46p1
  · exact word47p0
  · exact word47p1
  · exact word48p0
  · exact word48p1
  · exact word49p0
  · exact word49p1
  · exact word50p0
  · exact word50p1
  · exact word51p0
  · exact word51p1
  · exact word52p0
  · exact word52p1
  · exact word53p0
  · exact word53p1
  · exact word54p0
  · exact word54p1
  · exact word55p0
  · exact word55p1
  · exact word56p0
  · exact word56p1
  · exact word57p0
  · exact word57p1
  · exact word58p0
  · exact word58p1
  · exact word59p0
  · exact word59p1
  · exact word60p0
  · exact word60p1
  · exact word61p0
  · exact word61p1
  · exact word62p0
  · exact word62p1
  · exact word63p0
  · exact word63p1
  · exact word64p0
  · exact word64p1
  · exact word65p0
  · exact word65p1
  · exact word66p0
  · exact word66p1
  · exact word67p0
  · exact word67p1
  · exact word68p0
  · exact word68p1
  · exact word69p0
  · exact word69p1
  · exact word70p0
  · exact word70p1
  · exact word71p0
  · exact word71p1
  · exact word72p0
  · exact word72p1

theorem mem_labels {n x : ℕ} : x ∈ labels n ↔ 0 < x ∧ x ≤ n := by
  simp only [labels,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨h1,h2⟩; exact ⟨x-1,by omega,by omega⟩

def labelEquiv (n : ℕ) : {x // x ∈ labels n} ≃ Fin n where
  toFun x := ⟨x.val-1,by have ⟨_,_⟩ := mem_labels.mp x.property; omega⟩
  invFun i := ⟨i.val+1,mem_labels.mpr (by have := i.isLt; omega)⟩
  left_inv x := by apply Subtype.ext; have ⟨_,_⟩ := mem_labels.mp x.property; dsimp; omega
  right_inv i := by apply Fin.ext; simp

theorem arrange {n : ℕ} {xs : List ℕ} (hp : xs.Perm (labels n)) (hc : Chain xs) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j : Fin n, j.val=i.val+1 →
      IsSquare ((p i).val+1+((p j).val+1)) := by
  have hl : xs.length=n := by simpa using hp.length_eq
  have nd := hp.nodup_iff.mpr (List.nodup_range.map Nat.succ_injective)
  let pos := finCongr hl.symm
  let transfer : {x // x ∈ xs} ≃ {x // x ∈ labels n} := Equiv.subtypeEquivRight (fun _ => hp.mem_iff)
  let f := ((pos.trans (List.Nodup.getEquiv xs nd)).trans transfer).trans (labelEquiv n)
  have val (i : Fin n) : (f i).val+1 = xs[i.val]'(hl.symm ▸ i.isLt) := by
    change xs[i.val]'(hl.symm ▸ i.isLt) - 1 + 1 = _
    apply Nat.sub_add_cancel
    exact (mem_labels.mp (hp.mem_iff.mp (List.getElem_mem _))).1
  refine ⟨f,fun i j hij => ?_⟩
  rw [val,val]
  have hi : i.val+1<xs.length := by rw [hl,← hij]; exact j.isLt
  simpa only [hij] using List.isChain_iff_getElem.mp hc i.val hi

theorem all_pairs (n : ℕ) (hn : 41 ≤ n) : P n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 2033
    · exact medium n hn small
    let m := (n-24)/49
    let r := 24+(n-24)%49
    have hm : 41 ≤ m := by dsimp [m]; omega
    have hr : 24 ≤ r ∧ r ≤ 72 := by dsimp [r]; omega
    have he : 49*m+r=n := by dsimp [m,r]; omega
    obtain ⟨s,t,hp⟩ := ih m (by omega) hm
    obtain ⟨a,b,hc⟩ := all_certified (m%2) r (by omega) hr.1 hr.2
    exact he ▸ pair_output hp (by omega) hr.1 hr.2 hc

theorem all_paths (n : ℕ) (hn : 25 ≤ n) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j : Fin n, j.val=i.val+1 →
      IsSquare ((p i).val+1+((p j).val+1)) := by
  by_cases h : n < 41
  · obtain ⟨xs,hp,hc⟩ := little n hn h
    exact arrange hp hc
  · obtain ⟨s,t,hp⟩ := all_pairs n (by omega)
    exact arrange hp.1.1 hp.1.2.1

end SquarePaths

theorem OMA.solution : type_of% @OMA.S_mse_2637546.main := SquarePaths.all_paths
