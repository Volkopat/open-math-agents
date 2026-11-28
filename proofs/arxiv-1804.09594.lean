import OMAStatements.S_arxiv_1804_09594

/-!
# The even terms of Kuca's additive sequences
STATUS: NEW
Borys Kuca, Structures in additive sequences, Theorem 3.1 and Conjecture 3.1.
https://arxiv.org/abs/1804.09594
The even terms of V(2,n) for every n=2^k+1 at least 5 are 2, 2n and 2n²+2.
The dyadic companion rows and the reflected recurrence supply at least two
unordered representations of every later even candidate. The original greedy
list is recovered by induction. Two disjoint finite windows give the small cases.
Written proof and reproducible finite checks:
https://github.com/Mapika/open-math-agents/tree/e394e79cf5a2af4160d853b5ae632b3c44abe4bb/research/arxiv-1804.09594
-/

namespace KucaLucas

/-- Parity of a binomial coefficient. -/
def bit (m j : ℕ) : ℕ := m.choose j % 2

theorem bit_cases (m j : ℕ) : bit m j = 0 ∨ bit m j = 1 := by
  unfold bit
  omega

theorem bit_pascal (m j : ℕ) :
    bit (m+1) (j+1) = (bit m j + bit m (j+1)) % 2 := by
  simp only [bit, Nat.choose_succ_succ, Nat.add_mod_mod, Nat.mod_add_mod]

theorem bit_lucas (m j : ℕ) :
    bit m j = bit (m%2) (j%2) * bit (m/2) (j/2) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := m) (k := j) (p := 2)
  change _ % 2 = _ % 2 at h
  unfold bit
  rw [h, Nat.mul_mod]
  obtain h₁ | h₁ := bit_cases (m%2) (j%2) <;>
    obtain h₂ | h₂ := bit_cases (m/2) (j/2) <;>
    unfold bit at * <;> rw [h₁,h₂]

/-- Every entry in the row indexed by one less than a power of two is odd. -/
theorem dyadic_full (k j : ℕ) (hj : j < 2^k) : bit (2^k-1) j = 1 := by
  induction k generalizing j with
  | zero => have : j = 0 := by simpa using hj
            subst j
            decide
  | succ k ih =>
    have hp : 0 < 2^k := by positivity
    rw [pow_succ] at hj ⊢
    have a : (2^k*2-1)%2 = 1 := by omega
    have b : (2^k*2-1)/2 = 2^k-1 := by omega
    rw [bit_lucas, a, b, ih (j/2) (by omega)]
    rcases (show j%2=0 ∨ j%2=1 by omega) with h|h <;> rw [h] <;> decide

/-- Off the left endpoint, the final dyadic row has zero carry-free entries. -/
theorem dyadic_edge (k s : ℕ) (hs : 0 < s) (hs' : s < 2^k) :
    bit (2^k-1+s) (2^k-1) = 0 := by
  induction k generalizing s with
  | zero => simp at hs'; omega
  | succ k ih =>
    have hp : 0 < 2^k := by positivity
    rw [pow_succ] at hs' ⊢
    have a : (2^k*2-1)%2 = 1 := by omega
    have b : (2^k*2-1)/2 = 2^k-1 := by omega
    rw [bit_lucas,a,b]
    rcases (show s%2=0 ∨ s%2=1 by omega) with he|ho
    · rw [show (2^k*2-1+s)/2=2^k-1+s/2 by omega, ih (s/2) (by omega) (by omega), Nat.mul_zero]
    · rw [show (2^k*2-1+s)%2=0 by omega]
      simp [bit]

def carry (h s : ℕ) := bit (h+s) h

theorem carry_symm (h s : ℕ) : carry h s = carry s h := by
  unfold carry bit
  rw [Nat.choose_symm_add, Nat.add_comm]

theorem carry_edge (k h : ℕ) (hp : 0 < h) (hl : h < 2^k) :
    carry h (2^k-1) = 0 := by
  rw [carry_symm]
  exact dyadic_edge k h hp hl

theorem carry_pascal (h s : ℕ) :
    carry (h+1) (s+1) = (carry h (s+1) + carry (h+1) s) % 2 := by
  unfold carry
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using bit_pascal (h+s+1) h

/-- Coefficient with a signed column, extended by zero before the first block. -/
def col (m : ℕ) (j : ℤ) : ℕ := if j < 0 then 0 else bit m j.toNat

theorem col_cases (m : ℕ) (j : ℤ) : col m j = 0 ∨ col m j = 1 := by
  by_cases h : j< 0 <;> simp [col,h,bit_cases]

theorem col_pascal (m : ℕ) (j : ℤ) :
    col (m+1) j = (col m j + col m (j-1)) % 2 := by
  by_cases hn : j< 0
  · simp [col,hn,show j-1< 0 by omega]
  by_cases hz : j=0
  · subst j
    simp [col,bit]
  have ha : ¬j-1< 0 := by omega
  have hb : j.toNat = (j-1).toNat+1 := by omega
  simp only [col, if_neg hn, if_neg ha]
  conv_lhs => rw [hb,bit_pascal]
  rw [← hb, Nat.add_comm]

/-- The two one-dimensional Pascal rules give the exact-one recurrence in the interior. -/
theorem row_step (m s : ℕ) (j : ℤ) :
    col (m+1) j * carry (m+2) (s+1) =
    (if col (m+1) j * carry (m+2) s +
        col m j * carry (m+1) (s+1) + col m (j-1) * carry (m+1) (s+1) = 1
     then 1 else 0) := by
  rw [col_pascal, carry_pascal (m+1) s]
  rcases col_cases m j with h|h <;> rw [h] <;>
    rcases col_cases m (j-1) with h|h <;> rw [h] <;>
    rcases bit_cases (m+1+(s+1)) (m+1) with h|h <;>
    change carry (m+1) (s+1) = _ at h <;> rw [h] <;>
    rcases bit_cases (m+2+s) (m+2) with h|h <;>
    change carry (m+2) s = _ at h <;> rw [h] <;> decide

end KucaLucas

namespace KucaLucas

def coef : ℕ → ℤ → ℕ
  | 0, j => if j < 0 then 0 else 1
  | m+1, j => col m j

theorem coef_cases (h : ℕ) (j : ℤ) : coef h j = 0 ∨ coef h j = 1 := by
  cases h with
  | zero => by_cases H : j< 0 <;> simp [coef,H]
  | succ m => exact col_cases _ _

theorem coef_pascal (h : ℕ) (j : ℤ) :
    coef (h+1) j = (coef h j + coef h (j-1)) % 2 := by
  cases h with
  | succ m => exact col_pascal m j
  | zero =>
    by_cases hn : j < 0
    · simp [coef,col,hn,show j-1< 0 by omega]
    by_cases hz : j=0
    · subst j; decide
    · have hp : 0 < j.toNat := by omega
      simp [coef,col,bit,hn,show ¬j-1< 0 by omega,Nat.choose_eq_zero_of_lt hp]

@[simp] theorem carry_zero_right (h : ℕ) : carry h 0 = 1 := by simp [carry,bit]
@[simp] theorem carry_zero_left (s : ℕ) : carry 0 s = 1 := by simp [carry,bit]

def one (x y z : ℕ) := if x+y+z=1 then 1 else 0
def entry (j : ℤ) (h s : ℕ) := coef h j * carry h s

theorem entry_left (h : ℕ) (j : ℤ) :
    entry j (h+1) 0 = one 0 (entry j h 0) (entry (j-1) h 0) := by
  simp only [entry,carry_zero_right,Nat.mul_one,coef_pascal]
  rcases coef_cases h j with a|a <;> rcases coef_cases h (j-1) with b|b <;> rw [a,b] <;> decide

theorem entry_inside (h s : ℕ) (j : ℤ) :
    entry j (h+1) (s+1) =
    one (entry j (h+1) s) (entry j h (s+1)) (entry (j-1) h (s+1)) := by
  unfold entry
  rw [coef_pascal, carry_pascal h s]
  rcases coef_cases h j with a|a <;> rw [a] <;>
    rcases coef_cases h (j-1) with b|b <;> rw [b] <;>
    rcases bit_cases (h+(s+1)) h with c|c <;> change carry h (s+1) = _ at c <;> rw [c] <;>
    rcases bit_cases (h+1+s) (h+1) with d|d <;> change carry (h+1) s = _ at d <;>
    rw [d] <;> decide

def origin (q : ℕ) (j : ℤ) : ℤ := j*((q:ℤ)*(q+1)+1)
def index (q : ℕ) (j : ℤ) (h s : ℕ) : ℤ := origin q j + (h:ℤ)*(q+1)+1+s
def value (q : ℕ) (j : ℤ) (h s : ℕ) := if s=q then 0 else entry j h s

theorem index_neg {q h s : ℕ} {j : ℤ} (hj : j< 0) (hh : h< q) (hs : s≤ q) :
    index q j h s < 0 := by
  have ht : (h:ℤ)+1 ≤ q := by exact_mod_cast hh
  have hu : (s:ℤ) ≤ q := by exact_mod_cast hs
  have hj' : j ≤ -1 := by omega
  unfold index origin
  have ha := mul_le_mul_of_nonneg_right hj' (show 0≤ (q:ℤ)*(q+1)+1 by positivity)
  have hb := mul_le_mul_of_nonneg_right ht (show 0≤ (q:ℤ)+1 by positivity)
  nlinarith

theorem value_neg {q h s : ℕ} {j : ℤ} (hj : j< 0) : value q j h s = 0 := by
  cases h <;> simp [value,entry,coef,col,hj]

theorem index_pos {q h s : ℕ} {j : ℤ} (hj : 0≤ j) : 0 < index q j h s := by
  unfold index origin
  positivity

theorem front (q : ℕ) (j : ℤ) : index q j 0 0 - 1 = origin q j := by
  simp [index]
theorem prev_h (q h : ℕ) (j : ℤ) : index q j (h+1) 0 - 1 = index q j h q := by
  simp only [index, Nat.cast_add, Nat.cast_one, Nat.cast_zero]; ring
theorem prev_s (q h s : ℕ) (j : ℤ) : index q j h (s+1) - 1 = index q j h s := by
  simp only [index,Nat.cast_add,Nat.cast_one]; ring
theorem prev_n (q h s : ℕ) (j : ℤ) : index q j (h+1) s - (q+1) = index q j h s := by
  simp only [index,Nat.cast_add,Nat.cast_one]; ring
theorem prev_l (q h s : ℕ) (j : ℤ) :
    index q j (h+1) s - ((q+1)^2+1) = index q (j-1) h s := by
  simp only [index,origin,Nat.cast_add,Nat.cast_one]; ring

theorem top_n (q s : ℕ) (hq : 0< q) (j : ℤ) :
    index q j 0 s - (q+1) = index q (j-1) (q-1) (s+1) := by
  have hb : ((q-1:ℕ):ℤ) = q-1 := by omega
  simp only [index,origin,Nat.cast_zero,hb,Nat.cast_add,Nat.cast_one]; ring
theorem top_l (q s : ℕ) (hq : 0< q) (j : ℤ) :
    index q j 0 s - ((q+1)^2+1) = index q (j-2) (q-1) (s+1) := by
  have hb : ((q-1:ℕ):ℤ) = q-1 := by omega
  simp only [index,origin,Nat.cast_zero,hb,Nat.cast_add,Nat.cast_one]; ring
theorem top_end_n (q : ℕ) (j : ℤ) :
    index q j 0 q - (q+1) = origin q j := by simp [index]; omega
theorem orig_h (q : ℕ) (hq : 0< q) (j : ℤ) :
    origin q j - 1 = index q (j-1) (q-1) q := by
  have hb : ((q-1:ℕ):ℤ)=q-1 := by omega
  simp only [index,origin,hb]; ring
theorem orig_n (q : ℕ) (hq : 0< q) (j : ℤ) :
    origin q j - (q+1) = index q (j-1) (q-1) 0 := by
  have hb : ((q-1:ℕ):ℤ)=q-1 := by omega
  simp only [index,origin,hb,Nat.cast_zero]; ring
theorem orig_l (q : ℕ) (hq : 0< q) (j : ℤ) :
    origin q j - ((q+1)^2+1) = index q (j-2) (q-1) 0 := by
  have hb : ((q-1:ℕ):ℤ)=q-1 := by omega
  simp only [index,origin,hb,Nat.cast_zero]; ring

end KucaLucas

namespace KucaLucas

theorem last_zero {q k s : ℕ} (hq : q=2^k) (hs : 0< s) (hl : s≤ q) (j : ℤ) :
    value q j (q-1) s = 0 := by
  by_cases he : s=q
  · simp [value,he]
  · have hd := dyadic_edge k s hs (by omega)
    subst q
    simp [value,he,entry,carry,hd]

theorem last_start {q k : ℕ} (hq : q=2^k) (hlarge : 2≤ q) {j : ℤ}
    (hj : 0< j) (hle : j≤ q) :
    one 0 (value q (j-1) (q-1) 0) (value q (j-2) (q-1) 0) = 1 := by
  have hz : (0:ℕ)≠q := by omega
  simp only [value,if_neg hz,entry,carry_zero_right,Nat.mul_one]
  have hx := coef_cases (q-1) (j-1)
  have hy := coef_cases (q-1) (j-2)
  have hp := coef_pascal (q-1) (j-1)
  rw [show q-1+1=q by omega,show j-1-1=j-2 by omega] at hp
  have hc : coef q (j-1) = 1 := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_one_of_ne_zero (show q ≠ 0 by omega)
    rw [hd,coef,col,if_neg (by omega)]
    have hdm : d=2^k-1 := by omega
    rw [hdm]
    apply dyadic_full
    omega
  rw [hc] at hp
  suffices H : one 0 (coef (q-1) (j-1)) (coef (q-1) (j-2)) = (coef (q-1) (j-1)+coef (q-1) (j-2))%2 from H.trans hp.symm
  rcases hx with a|a <;> rcases hy with b|b <;> rw [a,b] <;> decide

def Block (q : ℕ) (a : ℤ → ℕ) (j : ℤ) : Prop :=
  a (origin q j)=1 ∧ ∀ h s : ℕ, h< q → s≤ q → a (index q j h s)=value q j h s

/-- The whole initial array of a three-even companion, for every dyadic parameter. -/
theorem dyadic_prefix {q k : ℕ} (hq : q=2^k) (hlarge : 2≤ q) (a : ℤ → ℕ)
    (seed : a 0=1) (neg : ∀ i : ℤ, i< 0 → a i=0)
    (step : ∀ i : ℤ, 0 < i → a i = one (a (i-1)) (a (i-(q+1))) (a (i-((q+1)^2+1))))
    (j : ℕ) (hj : j≤ q) : Block q a j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hq' : 0< q := by omega
    have jnon : 0≤ (j:ℤ) := by positivity
    have old (t : ℤ) (ht : t< j) (h s : ℕ) (hh : h< q) (hs : s≤ q) :
        a (index q t h s)=value q t h s := by
      by_cases hneg : t< 0
      · rw [neg _ (index_neg hneg hh hs),value_neg hneg]
      · have ht' : (t.toNat:ℤ)=t := by omega
        have hb := (ih t.toNat (by omega) (by omega)).2 h s hh hs
        rwa [ht'] at hb
    have base : a (origin q j) = 1 := by
      by_cases hz : j=0
      · subst j; simpa [origin] using seed
      have hp : 0 < origin q j := by
        have jpos : (0:ℤ)< j := by exact_mod_cast Nat.pos_of_ne_zero hz
        unfold origin
        positivity
      rw [step _ hp,orig_h q hq',orig_n q hq',orig_l q hq',
          old _ (by omega) _ _ (by omega) (by omega), old _ (by omega) _ _ (by omega) (by omega),
          old _ (by omega) _ _ (by omega) (by omega)]
      simp only [value,ite_true]
      apply last_start hq hlarge (by omega) (by exact_mod_cast hj)
    refine ⟨base,?_⟩
    intro h
    induction h with
    | zero =>
      intro s
      induction s with
      | zero =>
        intro hh hs
        rw [step _ (index_pos jnon),front,base,top_n q _ hq',top_l q _ hq',
          old _ (by omega) _ _ (by omega) (by omega), old _ (by omega) _ _ (by omega) (by omega),
          last_zero hq (by omega) (by omega),last_zero hq (by omega) (by omega)]
        simp [value,show (0:ℕ)≠q by omega,entry,coef,jnon.not_gt,one]
      | succ s prev =>
        intro hh hs
        have hu : s< q := by omega
        have left := prev hh (by omega)
        simp [value,hu.ne,entry,coef,jnon.not_gt] at left
        rw [step _ (index_pos jnon),prev_s,left]
        by_cases he : s+1=q
        · rw [he,top_end_n,base]
          simp [one,value]
          omega
        · rw [top_n q _ hq',top_l q _ hq',old _ (by omega) _ _ (by omega) (by omega),
            old _ (by omega) _ _ (by omega) (by omega),last_zero hq (by omega) (by omega),
            last_zero hq (by omega) (by omega)]
          simp [value,he,entry,coef,jnon.not_gt,one]
    | succ h above =>
      intro s
      induction s with
      | zero =>
        intro hh hs
        rw [step _ (index_pos jnon),prev_h,above q (by omega) (by omega),prev_n,prev_l,
          above 0 (by omega) (by omega),old _ (by omega) _ _ (by omega) (by omega)]
        simpa only [value,ite_true,if_neg (show (0:ℕ)≠q by omega)] using (entry_left h j).symm
      | succ s prev =>
        intro hh hs
        have hu : s< q := by omega
        rw [step _ (index_pos jnon),prev_s,prev hh (by omega),prev_n,prev_l,
          above (s+1) (by omega) (by omega),old _ (by omega) _ _ (by omega) (by omega)]
        by_cases he : s+1=q
        · have hx : s=q-1 := by omega
          have hd := carry_edge k (h+1) (by omega) (by omega)
          rw [← hq,← hx] at hd
          simp [value,he,hu.ne,entry,hd,one]
        · simpa only [value,if_neg hu.ne,if_neg he] using (entry_inside h s j).symm

end KucaLucas

namespace KucaLucas

theorem mask_split (j m : ℕ) :
    j &&& m = j ↔ (j/2 &&& m/2)=j/2 ∧ (j%2=1 → m%2=1) := by
  have hd := Nat.and_div_two (a:=j) (b:=m)
  have hl := Nat.and_mod_two_eq_one (a:=j) (b:=m)
  omega

theorem disjoint_split (h s : ℕ) :
    h &&& s = 0 ↔ (h/2 &&& s/2)=0 ∧ ¬(h%2=1 ∧ s%2=1) := by
  have hd := Nat.and_div_two (a:=h) (b:=s)
  have hl := Nat.and_mod_two_eq_one (a:=h) (b:=s)
  omega

theorem bit_odd_iff (m j : ℕ) : bit m j = 1 ↔ j &&& m = j := by
  induction j using Nat.strong_induction_on generalizing m with
  | h j ih =>
    by_cases hj : j=0
    · subst j; simp [bit]
    have ih' := ih (j/2) (by omega) (m/2)
    rw [mask_split,← ih',bit_lucas]
    rcases (show j%2=0 ∨ j%2=1 by omega) with a|a <;>
      rcases (show m%2=0 ∨ m%2=1 by omega) with b|b <;>
      simp [a,b,bit]

theorem carry_odd_iff (h s : ℕ) : carry h s = 1 ↔ h &&& s = 0 := by
  induction h using Nat.strong_induction_on generalizing s with
  | h h ih =>
    by_cases hh : h=0
    · subst h; simp
    have ih' := ih (h/2) (by omega) (s/2)
    rw [disjoint_split,← ih']
    unfold carry
    rw [bit_lucas]
    rcases (show h%2=0 ∨ h%2=1 by omega) with a|a <;>
      rcases (show s%2=0 ∨ s%2=1 by omega) with b|b
    all_goals first
      | (rw [show (h+s)/2=h/2+s/2 by omega]; rw [Nat.add_mod]; simp [a,b,bit])
      | (rw [Nat.add_mod]; simp [a,b,bit])

theorem block_header {q j : ℕ} {a : ℤ → ℕ} (B : Block q a j) (r : ℕ) (hr : r≤ q) :
    a (origin q j+r) = 1 := by
  cases r with
  | zero => simpa using B.1
  | succ s =>
    have e := B.2 0 s (by omega) (by omega)
    simpa [value,show s≠q by omega,entry,coef,index,(show ¬ (j:ℤ)< 0 by omega),add_comm,add_left_comm,add_assoc] using e

theorem block_row_iff {q j : ℕ} {a : ℤ → ℕ} (B : Block q a j)
    (h s : ℕ) (hp : 0< h) (hh : h< q) (hs : s< q) :
    a (index q j h s)=1 ↔ (j &&& (h-1))=j ∧ (h &&& s)=0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
  rw [B.2 _ _ hh hs.le]
  simp [value,hs.ne,entry,coef,col,bit_odd_iff,carry_odd_iff,(show ¬(j:ℤ)< 0 by omega),mul_eq_one]

end KucaLucas

namespace KucaShift
open KucaLucas

abbrev N (q : ℕ) : ℤ := q+1
abbrev D (q : ℕ) : ℤ := (q:ℤ)*(N q)+1
abbrev L (q : ℕ) : ℤ := (N q)^2+1
def B (q : ℕ) (a : ℤ → ℕ) (j r : ℤ) := a (origin q j+r)

structure Data (q : ℕ) (a : ℤ → ℕ) : Prop where
  qlarge : 4 ≤ q
  dyadic : ∃ k : ℕ, q = 2^k
  seed : a 0 = 1
  neg : ∀ i : ℤ, i < 0 → a i = 0
  step : ∀ i : ℤ, 0 < i → a i = one (a (i-1)) (a (i-N q)) (a (i-L q))

variable {q : ℕ} {a : ℤ → ℕ}
theorem Data.prefixBlock (A : Data q a) (j : ℕ) (hj : j≤ q) : Block q a j := by
  obtain ⟨k,hk⟩ := A.dyadic
  exact dyadic_prefix hk (by linarith [A.qlarge]) a A.seed A.neg A.step j hj

theorem Data.front (A : Data q a) {j r : ℤ} (hj : 0≤ j) (hj' : j≤ q)
    (hr : 0≤ r) (hr' : r< N q) : B q a j r = 1 := by
  have h := A.prefixBlock j.toNat (by omega)
  rcases eq_or_lt_of_le hr with hz|hp
  · simpa [B,←hz,Int.toNat_of_nonneg hj] using h.1
  let s := (r-1).toNat
  have se : (s:ℤ) = r-1 := by dsimp [s]; omega
  have hq := A.qlarge
  have hs : s< q := by dsimp [s]; unfold N at hr'; omega
  have e := h.2 0 s (by omega) hs.le
  have ci : index q j.toNat 0 s = origin q j+r := by
    simp only [index,Int.toNat_of_nonneg hj,Nat.cast_zero,zero_mul,add_zero,se]
    omega
  rw [ci] at e
  simpa [B,value,hs.ne,entry,coef] using e

theorem coords {r : ℤ} (hq : 4≤ q) (hr : 0< r) (hr' : r< D q) :
    ∃ h s : ℕ, h< q ∧ s≤ q ∧ r=(h:ℤ)*N q+1+s := by
  have hn : 0 < N q := by unfold N; positivity
  let h := (r-1)/N q
  let s := (r-1)%N q
  have hnon : 0≤ h := Int.ediv_nonneg (by omega) hn.le
  have snon : 0≤ s := Int.emod_nonneg _ hn.ne'
  have sl : s < N q := Int.emod_lt_of_pos _ hn
  have eh : h < q := by
    change (r-1)/N q < q
    rw [Int.ediv_lt_iff_lt_mul hn]
    unfold D at hr'
    linarith
  have rep := Int.mul_ediv_add_emod (r-1) (N q)
  refine ⟨h.toNat,s.toNat,by omega,?_,?_⟩
  · unfold N at sl; omega
  · rw [Int.toNat_of_nonneg hnon,Int.toNat_of_nonneg snon]
    dsimp only [h,s]
    linarith [mul_comm (N q) ((r-1)/N q)]

theorem Data.bare (A : Data q a) {j r : ℤ} (hj : (q:ℤ)-1≤ j) (hj' : j≤ q)
    (hr : N q≤ r) (hr' : r< D q) : B q a j r = 0 := by
  have hq := A.qlarge
  have hnj : 0≤ j := by omega
  obtain ⟨h,s,hh,hs,he⟩ := coords hq (by unfold N at hr; omega) hr'
  have hp := (A.prefixBlock j.toNat (by omega)).2 h s hh hs
  have ind : index q j.toNat h s = origin q j+r := by
    simp only [index,Int.toNat_of_nonneg hnj,N,he]; ring
  rw [ind] at hp
  change a (origin q j+r) = _
  rw [hp]
  by_cases hz : s=q
  · simp [value,hz]
  cases h with
  | zero => simp only [Nat.cast_zero,zero_mul,zero_add] at he; unfold N at hr; omega
  | succ t =>
    have ltj : t< j.toNat := by omega
    simp [value,hz,entry,coef,col,bit, max_eq_left hnj,Nat.choose_eq_zero_of_lt ltj]

theorem prior (j r : ℤ) : B q a j r = B q a (j-1) (r+D q) := by
  unfold B origin D N
  ring_nf

theorem Data.rule (A : Data q a) (j r : ℤ) (hp : 0< origin q j+r) :
    B q a j r = one (B q a j (r-1)) (B q a j (r-N q)) (B q a (j-1) (r-N q)) := by
  unfold B
  rw [A.step _ hp]
  congr 2 <;> simp only [origin,L,N] <;> ring

theorem Data.npos (A : Data q a) : 0 < N q := by unfold N; positivity
theorem Data.dlarge (A : Data q a) : 3*N q < D q := by
  have hq : 4≤ (q:ℤ) := by exact_mod_cast A.qlarge
  unfold D N; nlinarith
theorem Data.at_pos (A : Data q a) {j r : ℤ} (hj : 0< j) (hr : 0≤ r) : 0 < origin q j+r := by
  unfold origin
  positivity

theorem Data.zero_header (A : Data q a) (t : ℕ) (ht : (t:ℤ)< N q) :
    B q a (N q) t = 0 := by
  have hn := A.npos
  have hd := A.dlarge
  have prev (r : ℤ) (hr : 0≤ r) (hr' : r< N q) :
      B q a (N q) (r-N q)=0 ∧ B q a (N q-1) (r-N q)=0 := by
    constructor <;> rw [prior] <;> apply A.bare <;> first | (unfold N; omega) | omega
  induction t with
  | zero =>
    simp only [Nat.cast_zero] at ht ⊢
    have e := prev 0 (by omega) ht
    rw [A.rule _ _ (A.at_pos hn (by simp)),e.1,e.2,prior (N q) ((0:ℤ)-1),
      A.bare (by unfold N;omega) (by unfold N;omega) (by omega) (by omega)]
    rfl
  | succ t ih =>
    have e := prev (t+1) (by positivity) (by exact_mod_cast ht)
    rw [Nat.cast_succ,A.rule _ _ (A.at_pos hn (by positivity)),e.1,e.2,
      show (t:ℤ)+1-1=t by omega,ih (by omega)]
    rfl

theorem Data.zero_front (A : Data q a) {r : ℤ} (hr : 0≤ r) (hr' : r< N q) :
    B q a (N q) r=0 := by simpa [Int.toNat_of_nonneg hr] using A.zero_header r.toNat (by omega)

theorem Data.zero_before (A : Data q a) {r : ℤ} (hr : r< 0) : B q a 0 r=0 := by
  simpa [B,origin] using A.neg r hr
end KucaShift

namespace KucaShift
open KucaLucas
variable {q : ℕ} {a : ℤ → ℕ}

theorem Data.shift_aux (A : Data q a) (t : ℕ) (ht : N q≤ t) (hl : (t:ℤ)< D q) :
    B q a (N q) t = a ((t:ℤ)-1) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    have hn := A.npos
    have hd := A.dlarge
    have ih' (r : ℤ) (hr : N q ≤ r) (hr' : r< t) :
        B q a (N q) r = a (r-1) := by
      have hnn : 0≤ r := by omega
      simpa [Int.toNat_of_nonneg hnn] using ih r.toNat (by omega) (by omega) (by omega)
    have hbase (r : ℤ) (hr : 0≤ r) (hr' : r< N q) : a r = 1 := by
      simpa [B,origin] using A.front (j:=0) (by omega) (by omega) hr hr'
    have H := A.rule (N q) t (A.at_pos hn (by positivity))
    by_cases he : (t:ℤ)=N q
    · rw [he, A.zero_front (r:=N q-1) (by omega) (by omega), A.zero_front (r:=N q-N q) (by omega) (by omega),
        A.front (j:=N q-1) (r:=N q-N q) (by unfold N; omega) (by unfold N; omega) (by omega) (by omega)] at H
      rw [he,H,hbase _ (by omega) (by omega)]
      rfl
    · have orig := A.step ((t:ℤ)-1) (by omega)
      have lag : (t:ℤ)-1-L q< 0 := by
        have e : L q = D q+N q := by unfold L D N; ring
        omega
      rw [A.neg _ lag] at orig
      rw [H,ih' _ (by omega) (by omega),orig]
      by_cases h2 : (t:ℤ)< 2*N q
      · rw [A.zero_front (by omega) (by omega),
          A.front (by unfold N; omega) (by unfold N; omega) (by omega) (by omega),
          hbase ((t:ℤ)-1-N q) (by omega) (by omega)]
        simp [one]
      · rw [ih' _ (by omega) (by omega),
          A.bare (by unfold N; omega) (by unfold N; omega) (by omega) (by omega)]
        rw [show (t:ℤ)-N q-1=(t:ℤ)-1-N q by omega]

theorem Data.shift (A : Data q a) {r : ℤ} (hr : N q≤ r) (hr' : r< D q) :
    B q a (N q) r = a (r-1) := by
  have hn := A.npos
  have hnn : 0≤ r := by omega
  simpa [Int.toNat_of_nonneg hnn] using A.shift_aux r.toNat (by omega) (by omega)

end KucaShift

namespace KucaShift
open KucaLucas
variable {q : ℕ} {a : ℤ → ℕ}

theorem Data.row_zero (A : Data q a) (h s : ℕ) (hh : h< q) (hs : s≤ q) :
    a ((h:ℤ)*N q+1+s) = value q 0 h s := by
  simpa [index,origin,N] using (A.prefixBlock 0 (Nat.zero_le _)).2 h s hh hs

theorem Data.last (A : Data q a) {r : ℤ} (hr : 0≤ r) (hr' : r< N q) :
    B q a (N q) (D q-N q+r) = if r=1 then 1 else 0 := by
  have hq := A.qlarge
  have hn := A.npos
  have hd := A.dlarge
  rw [A.shift (by omega) (by omega)]
  have c1 : ((q-1:ℕ):ℤ) = q-1 := by omega
  have c2 : ((q-2:ℕ):ℤ) = q-2 := by omega
  by_cases hz : r=0
  · have eq' : D q-N q+r-1=((q-2:ℕ):ℤ)*N q+1+q := by
      rw [hz,c2]; simp only [D,N]; ring
    rw [eq',A.row_zero _ _ (by omega) (by omega),hz]
    simp [value]
  have hs : (r-1).toNat < q := by unfold N at hr'; omega
  have eq' : D q-N q+r-1=((q-1:ℕ):ℤ)*N q+1+(r-1).toNat := by
    rw [c1,Int.toNat_of_nonneg (by omega)]; simp only [D,N]; ring
  rw [eq',A.row_zero _ _ (by omega) hs.le]
  split_ifs with he
  · rw [he]; simp [value,show (0:ℕ)≠q by omega,entry]
    obtain ⟨k,h⟩ := Nat.exists_eq_add_one_of_ne_zero (show q-1 ≠ 0 by omega)
    simp [h,coef,col,bit]
  · obtain ⟨k,hk⟩ := A.dyadic
    exact last_zero hk (by omega) hs.le 0

theorem Data.header2_aux (A : Data q a) (t : ℕ) (ht : (t:ℤ)< N q) :
    B q a (N q+1) t = if t=0 then 0 else 1 := by
  have hn := A.npos
  have hd := A.dlarge
  have hq := A.qlarge
  have edges (r : ℤ) (hr : 0≤ r) (hr' : r< N q) :
      B q a (N q+1) r = one (B q a (N q+1) (r-1)) (if r=1 then 1 else 0) 0 := by
    rw [A.rule _ _ (A.at_pos (by omega) hr),prior (N q+1) (r-N q),
      show N q+1-1=N q by omega,prior (N q) (r-N q),
      show r-N q+D q=D q-N q+r by omega,A.last hr hr',
      A.bare (j:=N q-1) (r:=D q-N q+r) (by unfold N;omega) (by unfold N;omega) (by omega) (by omega)]
  induction t with
  | zero =>
    simp only [Nat.cast_zero,ite_true]
    rw [edges _ (by omega) hn,prior (N q+1) (0-1),show N q+1-1=N q by omega,
      show 0-1+D q=D q-N q+(N q-1) by omega,
      A.last (by omega) (by omega),if_neg (show N q-1≠1 by unfold N;omega)]
    decide
  | succ t ih =>
    rw [Nat.cast_succ,edges _ (by positivity) (by exact_mod_cast ht),show (t:ℤ)+1-1=t by omega,
      ih (by omega)]
    by_cases h : t=0 <;> simp [h,one]

theorem Data.header2 (A : Data q a) {r : ℤ} (hr : 0≤ r) (hr' : r< N q) :
    B q a (N q+1) r = if r=0 then 0 else 1 := by
  have e := A.header2_aux r.toNat (by omega)
  rw [Int.toNat_of_nonneg hr] at e
  by_cases h : r=0
  · simpa [h] using e
  · simpa [h,show r.toNat≠0 by omega] using e

theorem Data.next_mark (A : Data q a) : B q a (N q+1) 1=1 := by
  simpa using A.header2 (r:=1) (by omega) (by unfold N;linarith [A.qlarge])

theorem Data.evenq (A : Data q a) : q%2=0 := by
  obtain ⟨k,hk⟩ := A.dyadic
  cases k with
  | zero => simp at hk; linarith [A.qlarge]
  | succ k => rw [hk,pow_succ]; omega

theorem Data.row1 (A : Data q a) (t : ℕ) (ht : t≤ q) :
    B q a (N q) (N q+t) = 1-t%2 ∧ B q a (N q+1) (N q+t) = 1-t%2 := by
  have hn := A.npos
  have hq := A.qlarge
  have hq' : 4≤ (q:ℤ) := by exact_mod_cast hq
  have stepRow (j : ℤ) (hj : 0< j) (t : ℤ) (ht : 0≤ t) :
      B q a j (N q+t) = one (B q a j (N q+t-1)) (B q a j t) (B q a (j-1) t) := by
    simpa only [add_sub_cancel_left] using A.rule j (N q+t) (A.at_pos hj (by omega))
  induction t with
  | zero =>
    simp only [Nat.cast_zero,Nat.zero_mod,Nat.sub_zero,add_zero]
    have left : B q a (N q) (N q-1)=0 := A.zero_front (by omega) (by omega)
    have right : B q a (N q+1) (N q-1)=1 := by
      rw [A.header2 (by omega) (by omega),if_neg (by unfold N;omega)]
    have e := stepRow (N q) hn 0 (by omega)
    have f := stepRow (N q+1) (by omega) 0 (by omega)
    simp only [add_zero] at e f
    rw [show N q+1-1=N q by omega] at f
    rw [e,f,left,right,A.zero_front (r:=0) (by omega) hn,
      A.front (j:=N q-1) (r:=0) (by unfold N;omega) (by unfold N;omega) (by omega) hn,
      A.header2 (r:=0) (by omega) hn]
    decide
  | succ t ih =>
    rcases ih (by omega) with ⟨hx,hy⟩
    have ht' : (t:ℤ)+1< N q := by unfold N;omega
    rw [Nat.cast_succ,stepRow _ hn _ (by positivity),stepRow (N q+1) (by omega) _ (by positivity),
      show N q+((t:ℤ)+1)-1=N q+t by omega,show N q+1-1=N q by omega,hx,hy,
      A.zero_front (r:=(t:ℤ)+1) (by positivity) ht',
      A.front (j:=N q-1) (r:=(t:ℤ)+1) (by unfold N;omega) (by unfold N;omega) (by positivity) ht',
      A.header2 (r:=(t:ℤ)+1) (by positivity) ht',if_neg (by omega)]
    unfold one
    split_ifs <;> omega

end KucaShift

namespace KucaShift
open KucaLucas
variable {q : ℕ} {a : ℤ → ℕ}
def R (q h s : ℕ) : ℤ := (h:ℤ)*N q+2+s

theorem Data.shift_row (A : Data q a) {h s : ℕ} (hp : 0< h) (hh : h< q) (hs : s≤ q) (hl : R q h s< D q) :
    B q a (N q) (R q h s) = value q 0 h s := by
  have hnn : (1:ℤ) ≤ h := by exact_mod_cast hp
  have hn := A.npos
  have hpos : N q ≤ (h:ℤ)*N q := by nlinarith
  rw [A.shift (by unfold R;omega) hl]
  convert A.row_zero h s hh hs using 2
  unfold R;ring

theorem Data.row2_edges (A : Data q a) :
    B q a (N q+1) (2*N q) = 0 ∧ B q a (N q+1) (2*N q+1)=0 := by
  have hq := A.qlarge
  have hn := A.npos
  have e0 := A.row1 0 (by omega)
  have e1 := A.row1 1 (by omega)
  simp only [Nat.cast_zero,add_zero,Nat.zero_mod,Nat.sub_zero] at e0
  norm_num only at e1
  change B q a (N q) (N q+1)=0 ∧ B q a (N q+1) (N q+1)=0 at e1
  have ea := A.rule (N q+1) (2*N q) (A.at_pos (by omega) (by omega))
  rw [show N q+1-1=N q by omega,show 2*N q-N q=N q by omega,e0.1,e0.2] at ea
  have hb : B q a (N q+1) (2*N q)=0 := by rw [ea];unfold one;split_ifs <;> omega
  have eb := A.rule (N q+1) (2*N q+1) (A.at_pos (by omega) (by omega))
  rw [show N q+1-1=N q by omega,show 2*N q+1-N q=N q+1 by omega,
    show 2*N q+1-1=2*N q by omega,hb,e1.1,e1.2] at eb
  exact ⟨hb,eb⟩

theorem Data.first_shift_row (A : Data q a) {s : ℕ} (hs : s≤ q) :
    B q a (N q+1) (R q 1 s) = B q a (N q) (R q 1 s) := by
  have hq := A.qlarge
  have hn := A.npos
  have hd := A.dlarge
  have he : R q 1 s = N q + (s+2 : ℕ) := by simp [R]; ring
  by_cases hu : s+2≤ q
  · rw [he];exact (A.row1 _ hu).2.trans (A.row1 _ hu).1.symm
  have hr : R q 1 s< D q := by rw [he];push_cast; unfold N at *;omega
  rw [A.shift_row (by omega) (by omega) hs hr]
  by_cases hh : s=q
  · have eq' : R q 1 s = 2*N q+1 := by rw [he];push_cast;unfold N;omega
    rw [eq',A.row2_edges.2,hh];simp [value]
  · have eq' : R q 1 s = 2*N q := by rw [he];push_cast;unfold N;omega
    obtain ⟨k,hk⟩ := A.dyadic
    have e := carry_edge k 1 (by omega) (by omega)
    rw [← hk,show q-1=s by omega] at e
    rw [eq',A.row2_edges.1];simp [value,hh,entry,e]

theorem Data.row_rule (A : Data q a) {h s : ℕ} (hp : 0< h) (hl : R q (h+1) s< D q) :
    B q a (N q+1) (R q (h+1) s) =
      one (B q a (N q+1) (R q (h+1) s-1))
        (B q a (N q+1) (R q h s)) (B q a (N q) (R q h s)) ∧
    B q a (N q) (R q (h+1) s) =
      one (B q a (N q) (R q (h+1) s-1)) (B q a (N q) (R q h s)) 0 := by
  have hn := A.npos
  have en : R q (h+1) s-N q = R q h s := by simp only [R,Nat.cast_add,Nat.cast_one];ring
  have hv : N q≤ R q h s := by
    have h' : 1≤ (h:ℤ) := by exact_mod_cast hp
    unfold R;nlinarith [mul_le_mul_of_nonneg_right h' hn.le,show 0≤ (s:ℤ) by positivity]
  have hy := A.rule (N q+1) (R q (h+1) s) (A.at_pos (by omega) (by omega))
  have hx := A.rule (N q) (R q (h+1) s) (A.at_pos hn (by omega))
  rw [show N q+1-1=N q by omega,en] at hy
  rw [en,A.bare (j:=N q-1) (r:=R q h s) (by unfold N;omega) (by unfold N;omega) hv (by omega)] at hx
  exact ⟨hy,hx⟩

theorem Data.next_rows (A : Data q a) (h s : ℕ) (hp : 0< h) (hh : h< q) (hs : s≤ q)
    (hl : R q h s < D q) : B q a (N q+1) (R q h s) =
      if h%2=1 then B q a (N q) (R q h s) else 0 := by
  induction h generalizing s with
  | zero => omega
  | succ h above =>
    by_cases hb : h=0
    · subst h; simpa using A.first_shift_row hs
    have hh' : 0< h := by omega
    induction s with
    | zero =>
      have eq' : R q (h+1) 0-1 = R q h q := by simp only [R,N,Nat.cast_add,Nat.cast_one,Nat.cast_zero];ring
      have lt : R q h q < D q := by omega
      have vz := A.shift_row hh' (by omega) (by omega : q≤ q) lt
      simp only [value,ite_true] at vz
      have wz := above q hh' (by omega) (by omega) lt
      rw [vz] at wz
      simp only [ite_self] at wz
      have l0 : R q h 0 < D q := by
        have := A.npos
        have e : R q (h+1) 0=R q h 0+N q := by simp only [R,Nat.cast_add,Nat.cast_one];ring
        omega
      have up := above 0 hh' (by omega) (by omega) l0
      have e := A.row_rule (s:=0) hh' hl
      rw [e.1,e.2,eq',wz,vz,up]
      by_cases he : h%2=1
      · simp only [if_pos he, if_neg (show (h+1)%2≠1 by omega)];unfold one;split_ifs <;> omega
      · simp [he,show (h+1)%2=1 by omega,one,Nat.add_comm]
    | succ s left =>
      have eq' : R q (h+1) (s+1)-1 = R q (h+1) s := by simp only [R,Nat.cast_add,Nat.cast_one];ring
      have lcol := left (by omega) (by omega)
      have l0 : R q h (s+1) < D q := by
        have := A.npos
        have e : R q (h+1) (s+1)=R q h (s+1)+N q := by simp only [R,Nat.cast_add,Nat.cast_one];ring
        omega
      have up := above (s+1) hh' (by omega) (by omega) l0
      have e := A.row_rule (s:=s+1) hh' hl
      rw [e.1,e.2,eq',lcol,up]
      by_cases he : h%2=1
      · simp only [if_pos he,if_neg (show (h+1)%2≠1 by omega)];unfold one;split_ifs <;> omega
      · simp [he,show (h+1)%2=1 by omega,one,Nat.add_comm]

end KucaShift

namespace KucaShift
open KucaLucas
variable {q : ℕ} {a : ℤ → ℕ}

theorem Data.last2 (A : Data q a) {r : ℤ} (hr : 0≤ r) (hr' : r< N q) :
    B q a (N q+1) (D q-N q+r) = if r=1 then 1 else 0 := by
  have hq := A.qlarge
  have hn := A.npos
  have hd := A.dlarge
  have eq := A.evenq
  have c1 : ((q-1:ℕ):ℤ) = q-1 := by omega
  have c2 : ((q-2:ℕ):ℤ) = q-2 := by omega
  by_cases hz : r=0
  · have e : D q-N q+r=R q (q-2) q := by
      rw [hz];simp only [R,c2,D,N];ring
    have z := A.next_rows (q-2) q (by omega) (by omega) (by omega) (by omega)
    rw [e,z,if_neg (show (q-2)%2≠1 by omega),if_neg (by omega)]
  · have hu : (r-1).toNat≤ q := by unfold N at hr';omega
    have e : D q-N q+r = R q (q-1) (r-1).toNat := by
      simp only [R,c1,Int.toNat_of_nonneg (by omega : 0≤ r-1),D,N];ring
    have z := A.next_rows (q-1) _ (by omega) (by omega) hu (by omega)
    rw [← e,if_pos (show (q-1)%2=1 by omega)] at z
    exact z.trans (A.last hr hr')

theorem Data.header3_aux (A : Data q a) (t : ℕ) (ht : (t:ℤ)< N q) :
    B q a (N q+2) t = 0 := by
  have hn := A.npos
  have hq := A.qlarge
  have edges (r : ℤ) (hr : 0≤ r) (hr' : r< N q) :
      B q a (N q+2) r = one (B q a (N q+2) (r-1)) (if r=1 then 1 else 0) (if r=1 then 1 else 0) := by
    rw [A.rule _ _ (A.at_pos (by omega) hr),prior (N q+2) (r-N q),
      show N q+2-1=N q+1 by omega,prior (N q+1) (r-N q),show N q+1-1=N q by omega,
      show r-N q+D q=D q-N q+r by omega,A.last2 hr hr',A.last hr hr']
  induction t with
  | zero =>
    simp only [Nat.cast_zero]
    rw [edges _ (by omega) hn,prior (N q+2) (0-1),show N q+2-1=N q+1 by omega,
      show 0-1+D q=D q-N q+(N q-1) by omega,
      A.last2 (by omega) (by omega),if_neg (show N q-1≠1 by unfold N;omega)]
    decide
  | succ t ih =>
    rw [Nat.cast_succ,edges _ (by positivity) (by exact_mod_cast ht),
      show (t:ℤ)+1-1=t by omega,ih (by omega)]
    split_ifs <;> rfl

theorem Data.header3 (A : Data q a) {r : ℤ} (hr : 0≤ r) (hr' : r< N q) :
    B q a (N q+2) r = 0 := by
  simpa [Int.toNat_of_nonneg hr] using A.header3_aux r.toNat (by omega)

theorem Data.third_row1 (A : Data q a) (t : ℕ) (ht : t≤ q) :
    B q a (N q+2) (N q+t) = t%2 := by
  have hn := A.npos
  have hq := A.qlarge
  have recStep (r : ℤ) (hr : 0≤ r) (hr' : r< N q) :
      B q a (N q+2) (N q+r) =
      one (B q a (N q+2) (N q+r-1)) 0 (if r=0 then 0 else 1) := by
    rw [A.rule _ _ (A.at_pos (by omega) (by omega)),show N q+r-N q=r by omega,
      show N q+2-1=N q+1 by omega,A.header3 hr hr',A.header2 hr hr']
  induction t with
  | zero =>
    simp only [Nat.cast_zero,Nat.zero_mod]
    rw [recStep _ (by omega) hn,add_zero,A.header3 (by omega) (by omega)];decide
  | succ t ih =>
    rw [Nat.cast_succ,recStep _ (by positivity) (by unfold N;omega),if_neg (by omega),
      show N q+((t:ℤ)+1)-1=N q+t by omega,ih (by omega)]
    unfold one;split_ifs <;> omega

theorem Data.third_row2 (A : Data q a) (t : ℕ) (ht : t≤ q) :
    B q a (N q+2) (2*N q+t) = 1-t%2 := by
  have hn := A.npos
  have hq := A.qlarge
  have recStep (r : ℕ) (hr : r≤ q) :
      B q a (N q+2) (2*N q+r) =
      one (B q a (N q+2) (2*N q+r-1)) (r%2) (1-r%2) := by
    rw [A.rule _ _ (A.at_pos (by omega) (by positivity)),show 2*N q+(r:ℤ)-N q=N q+r by omega,
      show N q+2-1=N q+1 by omega,A.third_row1 r hr,(A.row1 r hr).2]
  induction t with
  | zero =>
    rw [recStep _ ht,show 2*N q+(0:ℕ)-1=N q+q by unfold N;push_cast;ring,
      A.third_row1 q (by omega),A.evenq];decide
  | succ t ih =>
    rw [recStep _ ht,show 2*N q+(t.succ:ℤ)-1=2*N q+t by push_cast;ring,ih (by omega)]
    unfold one;split_ifs <;> omega

theorem Data.witnesses (A : Data q a) :
    B q a (N q) (N q) = 1 ∧ B q a (N q) (N q+2) = 1 ∧
    B q a (N q) (2*N q-1) = 1 ∧ B q a (N q+2) (3*q) = 1 ∧
    B q a (N q+2) (3*q-2) = 1 := by
  have hq := A.qlarge
  have eq := A.evenq
  have e := (A.row1 q (by omega)).1
  have h := A.third_row2 (q-2) (by omega)
  have h' := A.third_row2 (q-4) (by omega)
  have eq2 : 2*N q+((q-2:ℕ):ℤ) = 3*q := by unfold N;omega
  have eq4 : 2*N q+((q-4:ℕ):ℤ) = 3*q-2 := by unfold N;omega
  rw [eq2,show (q-2)%2=0 by omega] at h
  rw [eq4,show (q-4)%2=0 by omega] at h'
  rw [show N q+(q:ℤ)=2*N q-1 by unfold N;ring,eq] at e
  exact ⟨by simpa using (A.row1 0 (by omega)).1,
    by simpa using (A.row1 2 (by omega)).1,e,h,h'⟩

end KucaShift

namespace KucaInitial
open KucaLucas

def d (q : ℕ) := q*(q+1)+1
def base (q h : ℕ) := h*(q+1)+1

def Covered (A : ℕ → Prop) (s : ℕ) : Prop :=
  ∃ x y u v : ℕ, x+y=s ∧ u+v=s ∧ A x ∧ A y ∧ A u ∧ A v ∧ x≠u ∧ x≠v

def mark (a : ℤ → ℕ) (i : ℕ) := a i = 1

theorem row_partition (q r : ℕ) (hr : 0< r) (hr' : r< d q) :
    ∃ h s, h< q ∧ s≤ q ∧ r = base q h + s := by
  refine ⟨(r-1)/(q+1),(r-1)%(q+1),?_,?_,?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    dsimp [d] at hr'; omega
  · have := Nat.mod_lt (r-1) (show 0< q+1 by omega); omega
  · have := Nat.mod_add_div (r-1) (q+1)
    dsimp [base]; rw [Nat.mul_comm]; omega

theorem header {q j : ℕ} {a} (B : Block q a j) {r : ℕ} (hr : r≤ q) :
    mark a (j*d q+r) := by
  simpa [mark, d, origin] using block_header B r hr

theorem row {q j : ℕ} {a} (B : Block q a j) {h s : ℕ} (hp : 0< h) (hh : h< q) (hs : s< q) :
    mark a (j*d q+base q h+s) ↔ j &&& (h-1)=j ∧ h &&& s=0 := by
  simpa [mark,d,base,index,origin,add_assoc] using block_row_iff B h s hp hh hs

theorem complement {q k h : ℕ} (hq : q=2^k) (hh : h< q) : h &&& (q-1-h)=0 := by
  apply (carry_odd_iff _ _).mp
  unfold carry
  rw [show h+(q-1-h)=q-1 by omega,hq]
  apply dyadic_full
  omega

theorem disjoint_bound {q k h s : ℕ} (hq : q=2^k) (hh : h< q) (hs : s< q)
    (ha : h &&& s=0) : h+s< q := by
  subst q
  induction k generalizing h s with
  | zero => simp_all
  | succ k ih =>
    rw [pow_succ] at hh hs ⊢
    rcases (disjoint_split h s).mp ha with ⟨A,B⟩
    have := ih (h:=h/2) (s:=s/2) A (by omega) (by omega)
    omega

theorem first_row {q : ℕ} {a} (B : Block q a 0) {h s : ℕ} (hh : h< q) (hs : s≤ q) :
    mark a (base q h+s) ↔ s< q ∧ h &&& s=0 := by
  by_cases he : s=q
  · subst s
    have e := B.2 h q hh (by omega)
    simp [index,origin,value] at e
    simp [mark,base,e]
  · have hs' : s< q := by omega
    by_cases hz : h=0
    · subst h
      have hh' := header (q:=q) (j:=0) B (r:=1+s) (by omega)
      simpa [base,hs',hh'] using (show mark a (1+s) ↔ True by simpa using hh')
    · simpa [hs'] using row (q:=q) (j:=0) B (h:=h) (s:=s) (by omega) hh hs'

theorem boundary_unique {q k : ℕ} {a} (hq : q=2^k) (hh : 2≤ q)
    (B : ∀ j : ℕ, j≤ q → Block q a j) :
    mark a 0 ∧ mark a (d q) ∧ ∀ x y, x+y=d q → mark a x → mark a y → x=0 ∨ y=0 := by
  have B₀ := B 0 (by omega)
  have b₁ := header (B 1 (by omega)) (r:=0) (by omega)
  refine ⟨by simpa [mark,origin] using B₀.1, by simpa using b₁,?_⟩
  intro x y hxy hx hy
  by_contra! hn
  obtain ⟨h,s,hl,hs,hxr⟩ := row_partition q x (by omega) (by omega)
  obtain ⟨slt,hd⟩ := (first_row B₀ hl hs).mp (hxr ▸ hx)
  have hbound := disjoint_bound hq hl slt hd
  have hycalc : y = base q (q-1-h)+(q-s) := by
    have hqeq : q=(q-1-h)+(h+1) := by omega
    have e := congrArg (fun t : ℕ => t*(q+1)) hqeq
    simp only [Nat.add_mul,Nat.one_mul] at e
    dsimp [d, base] at *; omega
  obtain ⟨tlt,td⟩ := (first_row B₀ (h:=q-1-h) (s:=q-s) (by omega) (by omega)).mp (hycalc ▸ hy)
  have := disjoint_bound hq (h:=q-1-h) (by omega) tlt td
  omega

/-- Two marked positions in the header's pairing interval. The rightmost
eligible offset in each row provides the second position. -/
theorem two_near {q k : ℕ} {a} (hq : q=2^k) (B : Block q a 0)
    {h s : ℕ} (hp : 0< h) (hh : h+1< q) (hs : s≤ q) :
    ∃ x y, q≤ x ∧ x< y ∧ y≤ base q h+s ∧ base q h+s≤ x+q ∧
      mark a x ∧ mark a y := by
  have anchor : mark a (base q h) := by
    simpa using (first_row B (h:=h) (s:=0) (by omega) (by omega)).mpr ⟨by omega,by simp⟩
  have hbig : q< base q h := by
    dsimp [base]; nlinarith [Nat.mul_le_mul_right (q+1) hp]
  by_cases hi : q-1-h ≤ s
  · refine ⟨base q h,base q h+(q-1-h),by omega,by omega,by omega,by omega,anchor,?_⟩
    apply (first_row B (by omega) (by omega)).mpr
    exact ⟨by omega,complement hq (by omega)⟩
  · obtain ⟨g,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
    have H : base q (g+1)=base q g + (q+1) := by dsimp [base]; ring
    refine ⟨base q g+(q-1-g),base q (g+1),?_,by omega,by omega,by omega,?_,anchor⟩
    · dsimp [base]
      nlinarith [Nat.mul_le_mul_left g (show 1≤ q+1 by omega), (show q-1-g+g+1=q by omega)]
    · exact (first_row B (by omega) (by omega)).mpr ⟨by omega,complement hq (by omega)⟩


end KucaInitial

namespace KucaInitial
open KucaLucas

theorem tag_ne {D i j x y : ℕ} (hx : x< D) (hy : y< D) (hne : i≠j ∨ x≠y) :
    i*D+x ≠ j*D+y := by
  intro H
  have e := congrArg (fun t : ℕ => t%D) H
  simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hy] at e
  have M : i*D=j*D := by omega
  have := Nat.eq_of_mul_eq_mul_right (show 0< D by omega) M
  omega

theorem size {q h : ℕ} (hh : h< q) (s : ℕ) (hs : s≤ q) :
    base q h+s< d q := by
  have := Nat.mul_le_mul_right (q+1) hh
  dsimp [base,d]
  rw [Nat.succ_mul] at this
  omega

theorem near_cover {A : ℕ → Prop} {q i j r x y : ℕ}
    (hxy : x< y) (hl : q< y) (hu : y< d q) (hy : y≤ r) (hx : r≤ x+q)
    (mx : A (i*d q+x)) (my : A (i*d q+y))
    (H : ∀ t : ℕ, t≤ q → A (j*d q+t)) :
    Covered A ((i+j)*d q+r) := by
  have qd : q< d q := by omega
  refine ⟨i*d q+y,j*d q+(r-y),i*d q+x,j*d q+(r-x),?_,?_,my,H _ (by omega),mx,H _ (by omega),?_,?_⟩
  · rw [Nat.add_mul]; omega
  · rw [Nat.add_mul]; omega
  · omega
  · exact tag_ne hu (by omega) (Or.inr (by omega))

theorem front_cover {A : ℕ → Prop} {q j r : ℕ} (hq : 4≤ q)
    (hr : 0< r) (hu : r≤ q+1) (hcase : 0< j ∨ 2≤ r)
    (H : ∀ t : ℕ, t≤ q → A t) (J : ∀ t : ℕ, t≤ q → A (j*d q+t)) :
    Covered A (j*d q+r) := by
  have qd : q< d q := by dsimp [d]; nlinarith
  by_cases h : r≤ q
  · refine ⟨0,j*d q+r,1,j*d q+(r-1),by omega,by omega,H _ (by omega),J _ h,
      H _ (by omega),J _ (by omega),by decide,?_⟩
    rcases hcase with h | h
    · have := Nat.mul_le_mul_right (d q) h
      rw [Nat.one_mul] at this; omega
    · omega
  · refine ⟨1,j*d q+q,2,j*d q+(q-1),by omega,by omega,H _ (by omega),J _ (by omega),
      H _ (by omega),J _ (by omega),by decide,by omega⟩

theorem four_dvd {q k : ℕ} (hq : q=2^k) (hlarge : 4≤ q) : q%4=0 := by
  obtain _|k := k
  · simp_all
  obtain _|k := k
  · simp_all
  simp [hq,pow_succ,Nat.mul_assoc]

/-- The ordinary row argument covers block zero too, with extra witnesses in
rows 1 and q-2 when the interval reaches the final row. -/
theorem low_blocks {q k : ℕ} {a} (hq : q=2^k) (hlarge : 4≤ q)
    (B : ∀ i : ℕ, i≤ q → Block q a i) {j r : ℕ}
    (hj : j≤ q) (hr : r< d q) (hl : 2≤ j*d q+r) (hd : j*d q+r≠d q) :
    Covered (mark a) (j*d q+r) := by
  have H (i t : ℕ) (hi : i≤ q) (ht : t≤ q) := header (B i hi) ht
  have H₀ (t : ℕ) (ht : t≤ q) : mark a t := by simpa using H 0 t (by omega) ht
  have B₀ := B 0 (by omega)
  have dm : 0< d q := by simp [d]
  have qd : q< d q := by dsimp [d]; nlinarith
  by_cases rz : r=0
  · subst r
    simp only [Nat.add_zero] at *
    have jtwo : 2≤ j := by
      by_contra! h
      interval_cases j <;> simp_all
    have S : j*d q=d q+(j-1)*d q := by
      nth_rw 1 [show j=(j-1)+1 by omega,Nat.add_mul]
      omega
    refine ⟨0,j*d q,d q,(j-1)*d q,by omega,by omega,H₀ _ (by omega),?_,?_,?_,by omega,?_⟩
    · simpa using H j 0 hj (by omega)
    · simpa using H 1 0 (by omega) (by omega)
    · simpa using H (j-1) 0 (by omega) (by omega)
    · exact (Nat.mul_pos (show 0< j-1 by omega) dm).ne
  by_cases hf : r≤ q+1
  · apply front_cover (by omega) (by omega) hf _ H₀ (fun t ht => H _ _ hj ht)
    by_cases z : j=0
    · subst j; simp_all
    · omega
  obtain ⟨h,s,hh,hs,er⟩ := row_partition _ _ (by omega) hr
  have hp : 0< h := by
    by_contra! e
    have : h=0 := by omega
    simp [this,base] at er; omega
  by_cases hi : h+1< q
  · obtain ⟨x,y,hx,hxy,hy,hu,mx,my⟩ := two_near hq B₀ hp hi hs
    have C := near_cover (A:=mark a) (i:=0) (j:=j) (r:=r) hxy (by omega) (by omega)
      (by omega) (by omega) (by simpa using mx) (by simpa using my) (fun t ht => H _ _ hj ht)
    simpa using C
  have he : h=q-1 := by omega
  have h4 := four_dvd hq (by omega)
  have anchor (i : ℕ) (hei : i≤ q) (hm : i &&& (h-1)=i) :
      mark a (i*d q+base q h) := by
    simpa using (row (B _ hei) hp hh (s:=0) (by omega)).mpr ⟨hm,by simp⟩
  have A₀ : mark a (base q h) := by simpa using anchor 0 (by omega) (by simp)
  have largeBase : q< base q h := by
    dsimp [base]; nlinarith [Nat.mul_le_mul_right (q+1) hp]
  have baseLt : base q h< d q := by omega
  by_cases largeJ : 2≤ j
  · have m : 2 &&& (h-1) = 2 := by
      rw [mask_split,mask_split]
      norm_num
      omega
    have A₂ := anchor 2 (by omega) m
    have J : j*d q = 2*d q + (j-2)*d q := by
      nth_rw 1 [show j=2+(j-2) by omega,Nat.add_mul]
    refine ⟨base q h,j*d q+s,2*d q+base q h,(j-2)*d q+s,by omega,by omega,
      A₀,H _ _ hj hs,A₂,H _ _ (by omega) hs,by omega,?_⟩
    simpa using tag_ne (D:=d q) (i:=0) (j:=j-2) baseLt (show s< d q by omega)
      (Or.inr (show base q h≠s by omega))
  by_cases sz : s=0
  · subst s
    have last := (first_row B₀ (h:=h-1) (s:=q-h) (by omega) (by omega)).mpr
      ⟨by omega,by rw [show q-h=q-1-(h-1) by omega]; apply complement hq (by omega)⟩
    have bdiff : base q h=base q (h-1)+(q+1) := by
      have E := congrArg (fun t : ℕ => t*(q+1)) (show h=(h-1)+1 by omega)
      simp only [Nat.add_mul,Nat.one_mul] at E
      dsimp [base]; omega
    have C := near_cover (A:=mark a) (i:=0) (j:=j) (r:=r)
      (x:=base q (h-1)+(q-h)) (y:=base q h) (by omega) largeBase baseLt (by omega) (by omega)
      (by simpa using last) (by simpa using A₀) (fun t ht => H _ _ hj ht)
    simpa using C
  let e := (s-1)%2
  let v := (s-1)-e
  have ev : e≤ 1 ∧ v%2=0 ∧ e+v=s-1 := by dsimp [e,v]; omega
  have eMark : mark a (j*d q+base q (q-2)+e) := by
    apply (row (B _ hj) (by omega) (by omega) (by omega)).mpr
    constructor
    · rw [mask_split]
      have zj : j/2=0 := by omega
      simp [zj]
      omega
    · rw [disjoint_split]
      have ze : e/2=0 := by omega
      simp [ze]
      omega
  have vMark : mark a (base q 1+v) := by
    apply (first_row B₀ (by omega) (by omega)).mpr
    refine ⟨by omega,?_⟩
    rw [Nat.and_comm]; simp [ev.2.1]
  have bd : base q h + 1 = base q (q-2)+base q 1 := by
    have E := congrArg (fun t : ℕ => t*(q+1)) (show h=(q-2)+1 by omega)
    simp only [Nat.add_mul,Nat.one_mul] at E
    dsimp [base]; omega
  have g : base q 1+v< base q h := by
    have hi := Nat.mul_le_mul_right (q+1) (show 2≤ h by omega)
    simp only [base,Nat.one_mul]
    omega
  have ne : base q h ≠ j*d q+base q (q-2)+e := by
    rcases (show j=0 ∨ j=1 by omega) with je|je
    · simp [je]; dsimp [base] at bd ⊢; omega
    · rw [je]; simp; omega
  exact ⟨base q h,j*d q+s,j*d q+base q (q-2)+e,base q 1+v,by omega,by omega,A₀,
    H _ _ hj hs,eMark,vMark,ne,by omega⟩

end KucaInitial

namespace KucaInitial
open KucaLucas

theorem layout {A : ℕ → Prop} {D k r i j m n x y u v : ℕ}
    (hj : i+j=k) (hm : m+n=k) (hxy : x+y=r) (huv : u+v=r)
    (mx : A (i*D+x)) (my : A (j*D+y)) (mu : A (m*D+u)) (mv : A (n*D+v))
    (hl : x< D) (hl' : u< D) (hl'' : v< D) (ha : i≠m ∨ x≠u) (hb : i≠n ∨ x≠v) :
    Covered A (k*D+r) := by
  exact ⟨i*D+x,j*D+y,m*D+u,n*D+v,by rw [← hj,Nat.add_mul,← hxy]; omega,
    by rw [← hm,Nat.add_mul,← huv]; omega,mx,my,mu,mv,tag_ne hl hl' ha,tag_ne hl hl'' hb⟩

theorem high_core {q k : ℕ} {a} (hq : q=2^k) (hlarge : 4≤ q)
    (B : ∀ i : ℕ, i≤ q → Block q a i)
    (shift : ∀ x : ℕ, q≤ x → x+1< d q → mark a x → mark a ((q+1)*d q+(x+1)))
    {j r : ℕ} (hj : q< j) (ju : j≤ 2*q-2) (hr : r< d q) :
    Covered (mark a) (j*d q+r) := by
  have HH (i t : ℕ) (hi : i≤ q) (ht : t≤ q) := header (B i hi) ht
  have B₀ := B 0 (by omega)
  have qd : q+1< d q := by dsimp [d]; nlinarith
  by_cases hu : r≤ 2*q
  · let x := r-q
    let y := r-x
    have ex : x+y=r ∧ x≤ q ∧ y≤ q := by dsimp [x,y]; omega
    exact layout (D:=d q) (i:=j-q) (j:=q) (m:=j-q+1) (n:=q-1)
      (x:=x) (y:=y) (u:=x) (v:=y) (by omega) (by omega) ex.1 ex.1
      (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega))
      (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega))
      (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  obtain ⟨h,s,hh,hs,he⟩ := row_partition q (r-1) (by omega) (by omega)
  have hp : 0< h := by
    by_contra! hz
    have : h=0 := by omega
    simp [this,base] at he; omega
  by_cases hm : h+1< q
  · obtain ⟨x,y,hx,hxy,hy,hu,mx,my⟩ := two_near hq B₀ hp hm hs
    have C := near_cover (A:=mark a) (i:=q+1) (j:=j-(q+1)) (r:=r)
      (x:=x+1) (y:=y+1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (shift _ hx (by omega) mx) (shift _ (by omega) (by omega) my) (fun t ht => HH _ _ (by omega) ht)
    rwa [show q+1+(j-(q+1))=j by omega] at C
  have hfin : h=q-1 := by omega
  have hb : q≤ base q h := by
    have mul := Nat.mul_le_mul_right (q+1) hp
    dsimp [base]; rw [Nat.one_mul] at mul; omega
  have e : base q h+q+1=d q := by
    have mul := congrArg (fun t : ℕ => t*(q+1)) (show h+1=q by omega)
    dsimp [base,d]; rw [Nat.add_mul,Nat.one_mul] at mul; omega
  have A₀ : mark a (base q h) := by
    simpa using (first_row B₀ (h:=h) (s:=0) hh (by omega)).mpr ⟨by omega,by simp⟩
  have A₁ := shift _ hb (by omega) A₀
  have A₂ : mark a ((q-2)*d q+base q h) := by
    have sub : (q-2) &&& (h-1)=q-2 := by rw [show h-1=q-2 by omega]; simp
    simpa using (row (B (q-2) (by omega)) hp hh (s:=0) (by omega)).mpr ⟨sub,by simp⟩
  exact layout (D:=d q) (i:=q+1) (j:=j-(q+1)) (m:=q-2) (n:=j-(q-2))
    (x:=base q h+1) (y:=s) (u:=base q h) (v:=s+1)
    (by omega) (by omega) (by omega) (by omega) A₁ (HH _ _ (by omega) hs) A₂
    (HH _ _ (by omega) (by omega)) (by omega) (by omega) (by omega)
    (Or.inl (by omega)) (Or.inl (by omega))

theorem high_end {q : ℕ} {a} (hlarge : 4≤ q)
    (B : ∀ i : ℕ, i≤ q → Block q a i)
    (shift : ∀ x : ℕ, q≤ x → x+1< d q → mark a x → mark a ((q+1)*d q+(x+1)))
    (post : mark a ((q+2)*d q+1))
    {j r : ℕ} (hj : 2*q-1≤ j) (ju : j≤ 2*q) (hr : r≤ 2*q) :
    Covered (mark a) (j*d q+r) := by
  have HH (i t : ℕ) (hi : i≤ q) (ht : t≤ q) := header (B i hi) ht
  have B₀ := B 0 (by omega)
  have qd : 2*q+1< d q := by dsimp [d]; nlinarith
  have ht : j-q+q=j := by omega
  by_cases r0 : r=0
  · subst r
    let z := base q (q-1)
    have ez : z+(q+1)=d q := by
      have mul := congrArg (fun t : ℕ => t*(q+1)) (show (q-1)+1=q by omega)
      rw [Nat.add_mul,Nat.one_mul] at mul
      dsimp [z,base,d]; omega
    have zlarge : q≤ z := by
      have mul := Nat.mul_le_mul_right (q+1) (show 1≤ q-1 by omega)
      dsimp [z,base]; rw [Nat.one_mul] at mul; omega
    have zm : mark a z := by
      simpa [z] using (first_row B₀ (h:=q-1) (s:=0) (by omega) (by omega)).mpr ⟨by omega,by simp⟩
    have A := shift z zlarge (by omega) zm
    have sume : (q+1)*d q + (j-q-2)*d q + d q = j*d q := by
      have he : q+1+(j-q-2)+1=j := by omega
      simpa only [Nat.add_mul,Nat.one_mul] using congrArg (fun t : ℕ => t*d q) he
    refine ⟨(q+1)*d q+(z+1),(j-q-2)*d q+q,(j-q)*d q+0,q*d q+0,
      by omega,by rw [← ht,Nat.add_mul]; simp [Nat.sub_add_cancel (show q≤ j by omega)],
      A,HH _ _ (by omega) (by omega),HH _ _ (by omega) (by omega),HH _ _ (by omega) (by omega),?_,?_⟩
    · exact tag_ne (by omega) (by omega) (Or.inl (by omega))
    · exact tag_ne (by omega) (by omega) (Or.inl (by omega))
  by_cases small : 2≤ r ∧ r≤ 2*q-2
  · let x := r-q
    let y := r-x
    have ex : x+y=r ∧ x+2≤ y ∧ y≤ q := by dsimp [x,y]; omega
    exact layout ht ht ex.1 (show (x+1)+(y-1)=r by omega)
      (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega))
      (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega))
      (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  by_cases r1 : r=1
  · subst r
    by_cases eq : j=2*q
    · exact layout (i:=q+2) (j:=j-(q+2)) (m:=j-q) (n:=q)
        (x:=1) (y:=0) (u:=0) (v:=1) (by omega) ht (by decide) (by decide) post
        (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega))
        (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    · exact layout ht ht (show 0+1=1 by decide) (show 1+0=1 by decide)
        (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega))
        (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) (by omega))
        (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  have qm : mark a q := by simpa using HH 0 q (by omega) (by omega)
  have markN := shift q (by omega) (by omega) qm
  let x := r-q
  have ex : x+q=r ∧ x≤ q := by dsimp [x]; omega
  exact layout (i:=q+1) (j:=j-(q+1)) (m:=j-q) (n:=q)
    (x:=q+1) (y:=r-(q+1)) (u:=x) (v:=q) (by omega) ht (by omega) ex.1 markN
    (HH _ _ (by omega) (by omega)) (HH _ _ (by omega) ex.2) (HH _ _ (by omega) (by omega))
    (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))


end KucaInitial

namespace KucaInitial
open KucaLucas KucaShift

theorem blocks_covered {q : ℕ} {a} (A : Data q a) {j r : ℕ}
    (hj : j≤ 2*q) (hr : r< d q) (hbox : j≤ 2*q-2 ∨ r≤ 2*q)
    (hl : 2≤ j*d q+r) (hd : j*d q+r≠d q) : Covered (mark a) (j*d q+r) := by
  obtain ⟨k,hk⟩ := A.dyadic
  have hlarge := A.qlarge
  have shift (x : ℕ) (hx : q≤ x) (hu : x+1< d q) (hm : mark a x) :
      mark a ((q+1)*d q+(x+1)) := by
    have H := A.shift (r:=(x:ℤ)+1) (by unfold N; omega) (by simpa [D,N,d] using (show (↑(x+1):ℤ)< (d q:ℕ) by exact_mod_cast hu))
    simpa [mark,KucaShift.B,origin,d,N] using H.trans (by simpa [mark] using hm)
  have post : mark a ((q+2)*d q+1) := by
    simpa [mark,KucaShift.B,origin,d,N,add_assoc] using A.next_mark
  by_cases h : j≤ q
  · exact low_blocks hk hlarge A.prefixBlock h hr hl hd
  by_cases h' : j≤ 2*q-2
  · exact high_core hk hlarge A.prefixBlock shift (by omega) h' hr
  · exact high_end hlarge A.prefixBlock shift post (by omega) hj (by omega)

/-- The complete initial cover, including all sums before the third even term. -/
theorem initial_cover {q : ℕ} {a} (A : Data q a) {s : ℕ}
    (hl : 2≤ s) (hd : s≠d q) (hu : s≤ (2*q-1)*d q+2*q) : Covered (mark a) s := by
  let j := s/d q
  let r := s%d q
  have hlarge := A.qlarge
  have qd : 2*q< d q := by dsimp [d]; nlinarith
  have er : s=j*d q+r := by dsimp [j,r]; exact (Nat.div_add_mod' _ _).symm
  have hr : r< d q := Nat.mod_lt _ (by omega)
  have hj : j≤ 2*q-1 := by
    by_contra! h
    have hm := Nat.mul_le_mul_right (d q) h
    rw [Nat.succ_mul] at hm; omega
  have hb : j≤ 2*q-2 ∨ r≤ 2*q := by
    by_cases e : j=2*q-1
    · rw [e] at er; omega
    · omega
  rw [er] at hl hd ⊢
  exact blocks_covered A (by omega) hr hb hl hd

/-- Every sum of two header indices above the third even term has two unordered witnesses. -/
theorem header_sum {q : ℕ} {a} (A : Data q a) {i j u v : ℕ}
    (hi : i≤ q) (hj : j≤ q) (hu : u≤ q) (hv : v≤ q)
    (hs : d q< (i*d q+u)+(j*d q+v)) :
    Covered (mark a) ((i*d q+u)+(j*d q+v)) := by
  have e : (i*d q+u)+(j*d q+v)=(i+j)*d q+(u+v) := by ring
  have hlarge := A.qlarge
  have qd : 2*q< d q := by dsimp [d]; nlinarith
  rw [e] at hs ⊢
  exact blocks_covered A (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega)

end KucaInitial

/-!
STATUS: PARTIAL
The reflected recurrence obstruction used in the proposed proof of Kuca's
Conjecture 3.1 (arXiv:1804.09594). For every integer n ≥ 17 the exceptional
length-L seed has no continuation through position 4L−2, where L = n²+1.
The finite deductions follow the ordinary proof's reverse-seed schedule.
See the research register for the 28 November 2026 prior-art check.
-/

namespace KucaTail

/-- On a reflected edge the left bit is set if precisely one successor is set. -/
def Edge (a b c d : ℕ) : Prop :=
  a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1 ∧ (a = 1 ↔ b + c + d = 1)

private theorem infer101x {a b c d : ℕ} (e : Edge a b c d)
    (ha : a = 1) (hb : b = 0) (hc : c = 1) : d = 0 := by
  unfold Edge at e
  omega

private theorem infer100x {a b c d : ℕ} (e : Edge a b c d)
    (ha : a = 1) (hb : b = 0) (hc : c = 0) : d = 1 := by
  unfold Edge at e
  omega

private theorem infer010x {a b c d : ℕ} (e : Edge a b c d)
    (ha : a = 0) (hb : b = 1) (hc : c = 0) : d = 1 := by
  unfold Edge at e
  omega

private theorem infer001x {a b c d : ℕ} (e : Edge a b c d)
    (ha : a = 0) (hb : b = 0) (hc : c = 1) : d = 1 := by
  unfold Edge at e
  omega

private theorem inferx11x {a b c d : ℕ} (e : Edge a b c d)
    (hb : b = 1) (hc : c = 1) : a = 0 := by
  unfold Edge at e
  omega

private theorem infer000x {a b c d : ℕ} (e : Edge a b c d)
    (ha : a = 0) (hb : b = 0) (hc : c = 0) : d = 0 := by
  unfold Edge at e
  omega

private theorem infer110x {a b c d : ℕ} (e : Edge a b c d)
    (ha : a = 1) (hb : b = 1) (hc : c = 0) : d = 0 := by
  unfold Edge at e
  omega

/-- Finite symbolic obstruction. An edge is required only when its base and
its largest successor both lie in the closed interval [0, 4L−2]. -/
theorem exceptional_seed (b : ℤ → ℕ) (n L : ℤ) (hn : 17 ≤ n) (hL : L = n*n+1)
    (bit : ∀ i, b i ≤ 1)
    (rec : ∀ i : ℤ, 0 ≤ i → i+L ≤ 4*L-2 →
      b i = if b (i+1) + b (i+n) + b (i+L) = 1 then 1 else 0)
    (seed : ∀ i : ℤ, 0 ≤ i → i < L →
      b i = if i = 0 ∨ i = n ∨ i = 2*n-1 then 1 else 0) : False := by
  let D := L-n
  have hspan : 8*n ≤ D := by dsimp [D]; nlinarith [sq_nonneg (n-17)]
  have hrel : L = D+n := by dsimp [D]; omega
  let c (j h t : ℤ) := b (j*D + h*n + t)
  have zeroAt (j h t : ℤ) (h₀ : 0 ≤ j*D+h*n+t) (h₁ : j*D+h*n+t < L)
      (hs : ¬ (j*D+h*n+t = 0 ∨ j*D+h*n+t = n ∨ j*D+h*n+t = 2*n-1)) :
      c j h t = 0 := by
    exact (seed _ h₀ h₁).trans (if_neg hs)
  have oneAt (j h t : ℤ) (h₀ : 0 ≤ j*D+h*n+t) (h₁ : j*D+h*n+t < L)
      (hs : j*D+h*n+t = 0 ∨ j*D+h*n+t = n ∨ j*D+h*n+t = 2*n-1) :
      c j h t = 1 := by
    exact (seed _ h₀ h₁).trans (if_pos hs)
  have edge (j h t : ℤ) (h₀ : 0 ≤ j*D+h*n+t) (h₁ : j*D+h*n+t+L ≤ 4*L-2) :
      Edge (c j h t) (c j h (t+1)) (c j (h+1) t) (c (j+1) (h+1) t) := by
    unfold Edge
    refine ⟨bit _, bit _, bit _, bit _, ?_⟩
    dsimp [c]
    have e := rec _ h₀ h₁
    rw [show j*D+h*n+t+1 = j*D+h*n+(t+1) by ring,
        show j*D+h*n+t+n = j*D+(h+1)*n+t by ring,
        show j*D+h*n+t+L = (j+1)*D+(h+1)*n+t by rw [hrel]; ring] at e
    split at e <;> omega

  -- Bits in the seed window that occur in the deductions below.
  have v0_0_0 : c 0 0 0 = 1 := oneAt 0 0 0 (by omega) (by omega) (by omega)
  have v0_0_1 : c 0 0 1 = 0 := zeroAt 0 0 1 (by omega) (by omega) (by omega)
  have v0_0_2 : c 0 0 2 = 0 := zeroAt 0 0 2 (by omega) (by omega) (by omega)
  have v0_1_m2 : c 0 1 (-2) = 0 := zeroAt 0 1 (-2) (by omega) (by omega) (by omega)
  have v0_1_m1 : c 0 1 (-1) = 0 := zeroAt 0 1 (-1) (by omega) (by omega) (by omega)
  have v0_1_0 : c 0 1 0 = 1 := oneAt 0 1 0 (by omega) (by omega) (by omega)
  have v0_1_1 : c 0 1 1 = 0 := zeroAt 0 1 1 (by omega) (by omega) (by omega)
  have v0_1_2 : c 0 1 2 = 0 := zeroAt 0 1 2 (by omega) (by omega) (by omega)
  have v0_2_m2 : c 0 2 (-2) = 0 := zeroAt 0 2 (-2) (by omega) (by omega) (by omega)
  have v0_2_m1 : c 0 2 (-1) = 1 := oneAt 0 2 (-1) (by omega) (by omega) (by omega)
  have v0_2_0 : c 0 2 0 = 0 := zeroAt 0 2 0 (by omega) (by omega) (by omega)
  have v0_2_1 : c 0 2 1 = 0 := zeroAt 0 2 1 (by omega) (by omega) (by omega)
  have v0_3_m2 : c 0 3 (-2) = 0 := zeroAt 0 3 (-2) (by omega) (by omega) (by omega)
  have v0_3_m1 : c 0 3 (-1) = 0 := zeroAt 0 3 (-1) (by omega) (by omega) (by omega)
  have v0_3_0 : c 0 3 0 = 0 := zeroAt 0 3 0 (by omega) (by omega) (by omega)
  have v0_4_m2 : c 0 4 (-2) = 0 := zeroAt 0 4 (-2) (by omega) (by omega) (by omega)
  have v0_4_m1 : c 0 4 (-1) = 0 := zeroAt 0 4 (-1) (by omega) (by omega) (by omega)
  have v1_1_m2 : c 1 1 (-2) = 0 := zeroAt 1 1 (-2) (by omega) (by omega) (by omega)
  have v1_1_m1 : c 1 1 (-1) = 0 := zeroAt 1 1 (-1) (by omega) (by omega) (by omega)

  -- A zero base with two zero short successors forces a zero long successor.
  have v1_1_1 : c 1 1 1 = 0 :=
    infer000x (edge 0 0 1 (by omega) (by omega)) v0_0_1 v0_0_2 v0_1_1
  have v1_2_m2 : c 1 2 (-2) = 0 :=
    infer000x (edge 0 1 (-2) (by omega) (by omega)) v0_1_m2 v0_1_m1 v0_2_m2
  have v1_2_1 : c 1 2 1 = 0 :=
    infer000x (edge 0 1 1 (by omega) (by omega)) v0_1_1 v0_1_2 v0_2_1
  have v1_3_0 : c 1 3 0 = 0 :=
    infer000x (edge 0 2 0 (by omega) (by omega)) v0_2_0 v0_2_1 v0_3_0
  have v1_4_m2 : c 1 4 (-2) = 0 :=
    infer000x (edge 0 3 (-2) (by omega) (by omega)) v0_3_m2 v0_3_m1 v0_4_m2
  have v1_4_m1 : c 1 4 (-1) = 0 :=
    infer000x (edge 0 3 (-1) (by omega) (by omega)) v0_3_m1 v0_3_0 v0_4_m1
  have v2_2_m2 : c 2 2 (-2) = 0 :=
    infer000x (edge 1 1 (-2) (by omega) (by omega)) v1_1_m2 v1_1_m1 v1_2_m2

  -- Fifteen recurrence deductions give incompatible bits on the final edge.
  have v1_1_0 : c 1 1 0 = 0 :=
    infer101x (edge 0 0 0 (by omega) (by omega)) v0_0_0 v0_0_1 v0_1_0
  have v1_2_0 : c 1 2 0 = 1 :=
    infer100x (edge 0 1 0 (by omega) (by omega)) v0_1_0 v0_1_1 v0_2_0
  have v1_3_m1 : c 1 3 (-1) = 1 :=
    infer100x (edge 0 2 (-1) (by omega) (by omega)) v0_2_m1 v0_2_0 v0_3_m1
  have v1_3_m2 : c 1 3 (-2) = 1 :=
    infer010x (edge 0 2 (-2) (by omega) (by omega)) v0_2_m2 v0_2_m1 v0_3_m2
  have v2_2_0 : c 2 2 0 = 1 :=
    infer001x (edge 1 1 0 (by omega) (by omega)) v1_1_0 v1_1_1 v1_2_0
  have v1_2_m1 : c 1 2 (-1) = 0 :=
    inferx11x (edge 1 2 (-1) (by omega) (by omega)) v1_2_0 v1_3_m1
  have v2_3_m2 : c 2 3 (-2) = 1 :=
    infer001x (edge 1 2 (-2) (by omega) (by omega)) v1_2_m2 v1_2_m1 v1_3_m2
  have v2_2_m1 : c 2 2 (-1) = 0 :=
    infer000x (edge 1 1 (-1) (by omega) (by omega)) v1_1_m1 v1_1_0 v1_2_m1
  have v2_3_0 : c 2 3 0 = 1 :=
    infer100x (edge 1 2 0 (by omega) (by omega)) v1_2_0 v1_2_1 v1_3_0
  have v2_4_m2 : c 2 4 (-2) = 0 :=
    infer110x (edge 1 3 (-2) (by omega) (by omega)) v1_3_m2 v1_3_m1 v1_4_m2
  have v2_4_m1 : c 2 4 (-1) = 1 :=
    infer100x (edge 1 3 (-1) (by omega) (by omega)) v1_3_m1 v1_3_0 v1_4_m1
  have v3_3_m2 : c 3 3 (-2) = 1 :=
    infer001x (edge 2 2 (-2) (by omega) (by omega)) v2_2_m2 v2_2_m1 v2_3_m2
  have v2_3_m1 : c 2 3 (-1) = 0 :=
    inferx11x (edge 2 3 (-1) (by omega) (by omega)) v2_3_0 v2_4_m1
  have v3_4_m2 : c 3 4 (-2) = 1 :=
    infer100x (edge 2 3 (-2) (by omega) (by omega)) v2_3_m2 v2_3_m1 v2_4_m2
  have v3_3_m1 : c 3 3 (-1) = 1 :=
    infer010x (edge 2 2 (-1) (by omega) (by omega)) v2_2_m1 v2_2_0 v2_3_m1
  have hlast : c 3 3 (-2) = 0 := inferx11x (edge 3 3 (-2) (by omega) (by omega)) v3_3_m1 v3_4_m2
  exact (show (1 : ℕ) ≠ 0 by decide) (v3_3_m2.symm.trans hlast)


/-- The four-term reflected edge is valid at every base below the marker S. -/
def Reflected (b : ℤ → ℕ) (n L S : ℤ) : Prop :=
  ∀ i < S, b i = if b (i+1) + b (i+n) + b (i+L) = 1 then 1 else 0

def Vanishes (b : ℤ → ℕ) (lo hi : ℤ) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → b i = 0

/-- Two zero input rows and the right boundary fill the preceding row. -/
theorem fill_row {b : ℤ → ℕ} {n D S p : ℤ}
    (rec : Reflected b n (D+n) S) (hn : 1 ≤ n) (hp : p ≤ S)
    (first : Vanishes b p (p+n-1)) (second : Vanishes b (p+D) (p+D+n-1)) :
    Vanishes b (p-n) p := by
  intro i hlo hhi
  refine Int.leInductionDown (motive := fun x _ => p-n ≤ x → b x = 0) ?_ ?_ i hhi hlo
  · intro _
    exact first _ (by omega) (by omega)
  · intro x hx ih hlow
    have e := rec (x-1) (by omega)
    rw [show x-1+1 = x by omega, ih (by omega), first (x-1+n) (by omega) (by omega),
        second (x-1+(D+n)) (by omega) (by omega)] at e
    simpa using e

/-- A run of h+1 zero headers, spaced D apart, forces a zero interval
from p−hn through the end of its leftmost header. -/
theorem fill_triangle {b : ℤ → ℕ} {n D S : ℤ}
    (rec : Reflected b n (D+n) S) (hn : 1 ≤ n) (hD : 0 ≤ D)
    (h : ℕ) (p : ℤ) (hcap : p+(h:ℤ)*D ≤ S)
    (headers : ∀ j : ℕ, j ≤ h → Vanishes b (p+(j:ℤ)*D) (p+(j:ℤ)*D+n-1)) :
    Vanishes b (p-(h:ℤ)*n) (p+n-1) := by
  induction h generalizing p with
  | zero => simpa using headers 0 (by omega)
  | succ h ih =>
    have hcap' : p + (h:ℤ)*D + D ≤ S := by
      simpa [Nat.cast_succ, add_mul, add_assoc] using hcap
    have left := ih p (by omega) (fun j hj => headers j (by omega))
    have right := ih (p+D) (by omega) (by
      intro j hj
      convert headers (j+1) (by omega) using 1 <;> push_cast <;> ring)
    let base := p-(h:ℤ)*n
    have hhn : 0 ≤ (h:ℤ)*n := mul_nonneg (by positivity) (by omega)
    have hhD : 0 ≤ (h:ℤ)*D := mul_nonneg (by positivity) hD
    have lower := fill_row (p := base) rec hn (by dsimp [base]; omega)
      (by intro i hlo hhi; apply left i <;> dsimp [base] at * <;> omega)
      (by intro i hlo hhi; apply right i <;> dsimp [base] at * <;> omega)
    intro i hlo hhi
    by_cases hi : i ≤ base
    · apply lower i _ hi
      dsimp [base]
      simpa [Nat.cast_succ, add_mul, sub_add_eq_sub_sub] using hlo
    · exact left i (by dsimp [base] at hi; omega) hhi


/-- The three permitted even summands give these three lags in the odd sequence. -/
def Forward (a : ℤ → ℕ) (n L : ℤ) : Prop :=
  ∀ i > 0, a i = if a (i-1) + a (i-n) + a (i-L) = 1 then 1 else 0

theorem reflected_of_forward {a : ℤ → ℕ} {n L : ℤ} (h : Forward a n L)
    (s : ℤ) : Reflected (fun i => a (s-i)) n L s := by
  intro i hi
  simpa only [sub_add_eq_sub_sub] using h (s-i) (by omega)

/-- Every full window has a one. A one lost at the left boundary forces the
new rightmost bit whenever the overlap is entirely zero. -/
theorem forward_window {a : ℤ → ℕ} {n L : ℤ} (rec : Forward a n L)
    (bits : ∀ i, a i ≤ 1) (first : a 0 = 1) (hn : 1 ≤ n) (hL : n < L)
    (x : ℕ) : ∃ i : ℤ, (x:ℤ) ≤ i ∧ i < (x:ℤ)+L ∧ a i = 1 := by
  induction x with
  | zero => exact ⟨0, by simp, by simpa using (by omega : 0 < L), first⟩
  | succ x ih =>
    push_cast
    by_contra! absent
    obtain ⟨i, hlo, hhi, hi⟩ := ih
    have eqleft : i = (x:ℤ) := by
      by_contra h
      exact absent i (by omega) (by omega) hi
    subst i
    let z := (x:ℤ)+L
    have bound : 0 ≤ (x:ℤ) := by positivity
    have overlap (t : ℤ) (h₀ : (x:ℤ)+1 ≤ t) (h₁ : t ≤ z) : a t = 0 := by
      have ha := absent t h₀ (by dsimp [z] at *; omega)
      have hb := bits t
      omega
    have e := rec z (by dsimp [z]; omega)
    rw [overlap (z-1) (by dsimp [z]; omega) (by omega),
        overlap (z-n) (by dsimp [z]; omega) (by omega),
        show z-L = (x:ℤ) by dsimp [z]; omega, hi] at e
    have hzero := overlap z (by dsimp [z]; omega) (by omega)
    simp_all

/-- A full window in a reflection corresponds to a nonnegative forward window
provided the right endpoint of the reflected window does not pass s. -/
theorem reflected_window {a : ℤ → ℕ} {n L : ℤ} (rec : Forward a n L)
    (bits : ∀ i, a i ≤ 1) (first : a 0 = 1) (hn : 1 ≤ n) (hL : n < L)
    (s lo : ℤ) (h : lo+L-1 ≤ s) :
    ∃ i : ℤ, lo ≤ i ∧ i < lo+L ∧ a (s-i) = 1 := by
  let start := s-(lo+L-1)
  have hs : (start.toNat : ℤ) = start := Int.toNat_of_nonneg (by dsimp [start]; omega)
  obtain ⟨j, h₀, h₁, hj⟩ := forward_window rec bits first hn hL start.toNat
  rw [hs] at h₀ h₁
  refine ⟨s-j, ?_, ?_, ?_⟩
  · dsimp [start] at h₀ h₁; omega
  · dsimp [start] at h₀ h₁; omega
  · simpa using hj

/-- When all headers miss, the first reflected window has exactly one set
bit at n. The column at offset n carries this bit through to nD+n. -/
theorem no_header_seed {b : ℤ → ℕ} {n D S : ℤ} (q : ℕ)
    (hnq : n = (q:ℤ)+1) (hn : 3 ≤ n) (hD : D = n*n-n+1)
    (hcap : (q:ℤ)*D+1 < S)
    (rec : Reflected b n (D+n) S) (bits : ∀ i, b i ≤ 1)
    (gap : ∀ lo : ℤ, lo+(D+n)-1 ≤ S → ∃ i : ℤ, lo ≤ i ∧ i < lo+(D+n) ∧ b i = 1)
    (headers : ∀ j : ℕ, j ≤ q → Vanishes b ((j:ℤ)*D) ((j:ℤ)*D+n-1)) :
    (∀ i : ℤ, 0 ≤ i → i < D+n → b i = if i = n then 1 else 0) ∧ b (n*D+n) = 1 := by
  have hDn : n < D := by nlinarith [sq_nonneg (n-2)]
  have hprod : (q:ℤ)*n = D-1 := by rw [show (q:ℤ) = n-1 by omega]; rw [hD]; ring
  have hqD : D ≤ (q:ℤ)*D := by
    nlinarith [mul_nonneg (show 0 ≤ (q:ℤ)-1 by omega) (show 0 ≤ D by omega)]
  have start := fill_triangle rec (by omega) (by omega) q 0 (by omega)
    (by simpa using headers)
  simp only [zero_sub, zero_add] at start
  have hqm : ((q-1:ℕ):ℤ) = (q:ℤ)-1 := by omega
  have next := fill_triangle rec (by omega) (by omega) (q-1) D (by
    rw [hqm, sub_mul]; simp; omega) (by
    intro j hj
    have r := headers (j+1) (by omega)
    convert r using 1 <;> push_cast <;> ring)
  have hstart : D-((q-1:ℕ):ℤ)*n = n+1 := by rw [hqm, sub_mul, hprod]; ring
  rw [hstart] at next
  obtain ⟨u, hu, hv, hub⟩ := gap (-((q:ℤ)*n)) (by omega)
  have hueq : u = n := by
    by_contra h
    have hz := start u hu (by omega)
    omega
  subst u
  refine ⟨?_, ?_⟩
  · intro i hi hi'
    split_ifs with h
    · simpa [h] using hub
    · by_cases hlt : i < n
      · exact start i (by omega) (by omega)
      · exact next i (by omega) (by omega)
  · have propagate (j : ℕ) (hj : j ≤ q+1) : b ((j:ℤ)*D+n) = 1 := by
      induction j with
      | zero => simpa using hub
      | succ j ih =>
        have hj' : j ≤ q := by omega
        have step := rec ((j:ℤ)*D) (by
          have h := mul_le_mul_of_nonneg_right (show (j:ℤ) ≤ (q:ℤ) by exact_mod_cast hj') (show 0 ≤ D by omega)
          omega)
        have h₀ := headers j hj' ((j:ℤ)*D) (by omega) (by omega)
        have h₁ := headers j hj' ((j:ℤ)*D+1) (by omega) (by omega)
        rw [h₀, h₁, ih (by omega)] at step
        have bound := bits ((j:ℤ)*D+(D+n))
        have target : (↑(j+1):ℤ)*D+n = (j:ℤ)*D+(D+n) := by push_cast; ring
        rw [target]
        split at step <;> omega
    convert propagate (q+1) (by omega) using 2
    push_cast
    rw [hnq]


/-- A path of m steps from the seed uses a steps of length L−n and
v steps of length L−1. All remaining steps have length L. -/
def Reach (n L x : ℤ) : Prop :=
  ∃ m u v : ℤ, 0 ≤ u ∧ 0 ≤ v ∧ u+v ≤ m ∧ x = n+m*L-u*n-v

theorem seed_support {b : ℤ → ℕ} {n L S : ℤ} (hn : 1 ≤ n) (hL : n < L)
    (rec : Reflected b n L S) (bits : ∀ i, b i ≤ 1)
    (seed : ∀ i : ℤ, 0 ≤ i → i < L → b i = if i = n then 1 else 0)
    (x : ℤ) (hx : 0 ≤ x) (cap : x ≤ S) (hb : b x = 1) : Reach n L x := by
  induction x using Int.strongRec (m := 0) with
  | lt x h => omega
  | ge x h ih =>
    by_cases hxL : x < L
    · have e := seed x hx hxL
      split at e
      · refine ⟨0, 0, 0, by omega, by omega, by omega, ?_⟩
        simp_all
      · omega
    · have e := rec (x-L) (by omega)
      rw [show x-L+L = x by omega, hb] at e
      have parent : b (x-L) = 1 ∨ b (x-L+1) = 1 ∨ b (x-L+n) = 1 := by
        have ha := bits (x-L)
        have hc := bits (x-L+1)
        have hd := bits (x-L+n)
        split at e <;> omega
      rcases parent with h | h | h
      · obtain ⟨m,u,v,hu,hv,hm,he⟩ := ih (x-L) (by omega) (by omega) (by omega) h
        exact ⟨m+1,u,v,hu,hv,by omega,by linarith only [he]⟩
      · obtain ⟨m,u,v,hu,hv,hm,he⟩ := ih (x-L+1) (by omega) (by omega) (by omega) h
        exact ⟨m+1,u,v+1,hu,by omega,by omega,by linarith only [he]⟩
      · obtain ⟨m,u,v,hu,hv,hm,he⟩ := ih (x-L+n) (by omega) (by omega) (by omega) h
        exact ⟨m+1,u+1,v,by omega,hv,by omega,by linarith only [he]⟩

private theorem path_bounds {m u v n L : ℤ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hm : u+v ≤ m) (hn : 1 ≤ n) :
    m*(L-n) ≤ m*L-u*n-v ∧ m*L-u*n-v ≤ m*L := by
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ m-u-v by omega) (show 0 ≤ n by omega),
               mul_nonneg hv (show 0 ≤ n-1 by omega)]
  · nlinarith [mul_nonneg hu (show 0 ≤ n by omega)]

/-- Above the advancing front the next path-length shell has not started. -/
theorem outside_front {n L j : ℤ} (hn : 3 ≤ n) (hl : L = n*n+1)
    (hj' : j ≤ n-2) : ¬ Reach n L (n+j*L+1) := by
  rintro ⟨m,u,v,hu,hv,hm,he⟩
  obtain ⟨low,high⟩ := path_bounds hu hv hm (by omega : 1 ≤ n) (L := L)
  have hD : 0 ≤ L-n := by nlinarith [sq_nonneg (n-1)]
  have hL : 0 ≤ L := by nlinarith [sq_nonneg n]
  by_cases hmj : m ≤ j
  · nlinarith [mul_nonneg (show 0 ≤ j-m by omega) hL]
  · have shell := mul_le_mul_of_nonneg_right (show j+1 ≤ m by omega) hD
    nlinarith [mul_nonneg (show 0 ≤ n-2-j by omega) (show 0 ≤ n by omega)]

/-- No path reaching one of the final Pascal columns can have arrived
by a last step of length D. Beyond the first n rows the only other
candidate path length would land in a gap between multiples of n−1 and n. -/
theorem outside_wide_parent {n L j d : ℤ} (hn : 5 ≤ n) (hl : L = n*n+1)
    (hj : 1 ≤ j) (hd : 0 ≤ d) (hd' : d ≤ 2)
    (region : j ≤ n-1 ∨ (j = n ∧ 1 ≤ d) ∨ (j = n+1 ∧ d = 2)) :
    ¬ Reach n L (n+j*L-d-(L-n)) := by
  rintro ⟨m,u,v,hu,hv,hm,he⟩
  obtain ⟨low,high⟩ := path_bounds hu hv hm (by omega : 1 ≤ n) (L := L)
  have hD : 2 < L-n := by nlinarith [sq_nonneg (n-1)]
  have hL : 2 < L := by nlinarith [sq_nonneg n]
  have lower : j ≤ m+1 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ j-2-m by omega) (show 0 ≤ L by omega)]
  have unequal : m+1 ≠ j := by
    rintro rfl
    nlinarith [mul_nonneg hu (show 0 ≤ n by omega)]
  have jmax : j ≤ n+1 := by rcases region with h|⟨h,_⟩|⟨h,_⟩ <;> omega
  have upper : m+1 ≤ j+1 := by
    by_contra! h
    have shell := mul_le_mul_of_nonneg_right (show j+1 ≤ m by omega) (show 0 ≤ L-n by omega)
    nlinarith [mul_nonneg (show 0 ≤ n+1-j by omega) (show 0 ≤ n by omega),
               sq_nonneg (n-2)]
  have eq : m = j := by omega
  subst m
  rcases region with reg | ⟨heq,hd1⟩ | ⟨heq,heqd⟩
  · nlinarith [mul_nonneg (show 0 ≤ n-1-j by omega) (show 0 ≤ n by omega)]
  · subst j
    by_cases ha : n-u = 0
    · have : v = 0 := by omega
      nlinarith
    · nlinarith [mul_nonneg (show 0 ≤ n-u-1 by omega) (show 0 ≤ n-1 by omega)]
  · subst j d
    by_cases ha : n+1-u ≤ 1
    · nlinarith [mul_nonneg (show 0 ≤ 1-(n+1-u) by omega) (show 0 ≤ n by omega)]
    · nlinarith [mul_nonneg (show 0 ≤ n+1-u-2 by omega) (show 0 ≤ n-1 by omega)]


/-- The second no-header witness comes from the first three columns
of Pascal's triangle modulo two. Here q = n−1 is a multiple of four. -/
theorem no_header_second {b : ℤ → ℕ} {n L S : ℤ} (q : ℕ)
    (hn : 5 ≤ n) (hL : L = n*n+1) (hnq : n = (q:ℤ)+1) (hq : q%4 = 0)
    (cap : n+(n+1)*L ≤ S) (rec : Reflected b n L S) (bits : ∀ i, b i ≤ 1)
    (seed : ∀ i : ℤ, 0 ≤ i → i < L → b i = if i = n then 1 else 0) :
    b (n+(n+1)*L-2) = 1 := by
  have nL : n < L := by nlinarith [sq_nonneg (n-1)]
  have Lpos : 0 ≤ L := by omega
  let f (j : ℕ) (d : ℤ) := b (n+(j:ℤ)*L-d)
  have outside (i : ℤ) (hi : 0 ≤ i) (hi' : i ≤ S) (h : ¬ Reach n L i) : b i = 0 := by
    have hb : b i ≠ 1 := fun hh => h (seed_support (by omega) nL rec bits seed i hi hi' hh)
    have bound := bits i
    omega
  have above (j : ℕ) (hj : (j:ℤ) ≤ n-2) : f j (-1) = 0 := by
    apply outside
    · nlinarith [mul_nonneg (show 0 ≤ (j:ℤ) by positivity) Lpos]
    · nlinarith [mul_nonneg (show 0 ≤ n-(j:ℤ) by omega) Lpos]
    · simpa only [sub_neg_eq_add] using outside_front (by omega) hL hj
  have step (j : ℕ) (d : ℤ) (hd : 0 ≤ d) (hd' : d ≤ 2)
      (region : (j:ℤ)+1 ≤ n-1 ∨ ((j:ℤ)+1 = n ∧ 1 ≤ d) ∨ ((j:ℤ)+1 = n+1 ∧ d = 2)) :
      f (j+1) d = (f j d + f j (d-1))%2 := by
    let x := n+((j:ℤ)+1)*L-d
    let y := n+(j:ℤ)*L-d
    have jmax : (j:ℤ)+1 ≤ n+1 := by rcases region with h|⟨h,_⟩|⟨h,_⟩ <;> omega
    have jpos : 0 ≤ (j:ℤ) := by positivity
    have xcap : x ≤ S := by dsimp [x]; nlinarith [mul_nonneg (show 0 ≤ n-j by omega) Lpos]
    have hw : b (x-(L-n)) = 0 := outside _
      (by dsimp [x]; nlinarith [mul_nonneg jpos Lpos]) (by omega)
      (outside_wide_parent hn hL (by omega) hd hd' region)
    have hxy : y+L = x := by dsimp [x,y]; ring
    have hwy : y+n = x-(L-n) := by dsimp [x,y]; ring
    have e := rec y (by omega)
    rw [hwy, hw, hxy] at e
    have e₀ := bits y
    have e₁ := bits (y+1)
    have e₂ := bits x
    have eqbit : b x = (b y + b (y+1))%2 := by split at e <;> omega
    change b (n+(↑(j+1):ℤ)*L-d) = (b y + b (n+(j:ℤ)*L-(d-1)))%2
    rw [show (↑(j+1):ℤ) = (j:ℤ)+1 by push_cast; rfl,
        show n+(j:ℤ)*L-(d-1) = y+1 by dsimp [y]; ring]
    exact eqbit
  have rows (j : ℕ) (hj : (j:ℤ) ≤ n-1) :
      f j 0 = 1 ∧ f j 1 = j%2 ∧ f j 2 = (j/2)%2 := by
    induction j with
    | zero =>
      have z : b n = 1 := by simpa using seed n (by omega) nL
      have o : b (n-1) = 0 := by simpa [show n-1 ≠ n by omega] using seed (n-1) (by omega) (by omega)
      have t : b (n-2) = 0 := by simpa [show n-2 ≠ n by omega] using seed (n-2) (by omega) (by omega)
      simpa [f] using And.intro z (And.intro o t)
    | succ j ih =>
      obtain ⟨a,c,e⟩ := ih (by omega)
      have h₀ := step j 0 (by omega) (by omega) (Or.inl (by omega))
      have h₁ := step j 1 (by omega) (by omega) (Or.inl (by omega))
      have h₂ := step j 2 (by omega) (by omega) (Or.inl (by omega))
      norm_num1 at h₀ h₁ h₂
      have z := above j (by omega)
      omega
  obtain ⟨a,c,e⟩ := rows q (by omega)
  have h₁ := step q 1 (by omega) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have h₂ := step q 2 (by omega) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have h₃ := step (q+1) 2 (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, rfl⟩))
  norm_num1 at h₁ h₂ h₃
  have target : f (q+1+1) 2 = 1 := by omega
  simpa [f, hnq, add_assoc] using target


/-- A single set input at column u switches all the preceding outputs on,
when the right boundary of the row is zero. -/
theorem fill_impulse {b : ℤ → ℕ} {n D S p u : ℤ} (rec : Reflected b n (D+n) S)
    (hp : p ≤ S) (_hu : 0 ≤ u) (hu' : u < n) (right : b p = 0)
    (input : ∀ v : ℤ, 0 ≤ v → v < n →
      b (p+v) + b (p+D+v) = if v = u then 1 else 0) :
    ∀ v : ℤ, 0 ≤ v → v < n → b (p-n+v) = if v ≤ u then 1 else 0 := by
  intro v hv hv'
  refine Int.leInductionDown (motive := fun v _ => 0 ≤ v →
    b (p-n+v) = if v ≤ u then 1 else 0) ?_ ?_ v hv'.le hv
  · intro _
    simpa [show ¬ n ≤ u by omega] using right
  · intro t ht ih ht'
    have e := rec (p-n+(t-1)) (by omega)
    rw [show p-n+(t-1)+1 = p-n+t by omega, ih (by omega),
        show p-n+(t-1)+n = p+(t-1) by omega,
        show p-n+(t-1)+(D+n) = p+D+(t-1) by omega,
        Nat.add_assoc, input (t-1) ht' (by omega)] at e
    split_ifs at e ⊢ <;> omega

/-- The reflected headers have a single one, in row j and column u. -/
def OneHit (b : ℤ → ℕ) (D q j u : ℤ) : Prop :=
  ∀ k v : ℤ, 0 ≤ k → k ≤ q → 0 ≤ v → v ≤ q →
    b (k*D+v) = if k = j ∧ v = u then 1 else 0

/-- Two adjacent headers containing the hit at a positive column force a
second hit at the leftmost entry of the preceding row. -/
theorem positive_column {b : ℤ → ℕ} {n D S j u m : ℤ}
    (rec : Reflected b n (D+n) S) (single : OneHit b D (n-1) j u)
    (hu : 0 < u) (hu' : u < n) (hm : 0 ≤ m) (hm' : m < n-1)
    (adj : j=m ∨ j=m+1) (cap : m*D ≤ S) : b (m*D-n) = 1 := by
  have right := single m 0 (by omega) (by omega) (by omega) (by omega)
  simp [show (0:ℤ) ≠ u by omega] at right
  have forced := fill_impulse (p := m*D) (u := u) rec cap hu.le hu' right (by
    intro v hv hv'
    rw [show m*D+D+v = (m+1)*D+v by ring,
        single m v (by omega) (by omega) hv (by omega),
        single (m+1) v (by omega) (by omega) hv (by omega)]
    split_ifs <;> omega) 0 (by omega) (by omega)
  simpa [hu.le] using forced

/-- With a hit in column zero, the leftmost site at every depth d≤ j
is set while the other columns of that row vanish. -/
theorem column_zero_impulse {b : ℤ → ℕ} {n D S j : ℤ}
    (rec : Reflected b n (D+n) S) (single : OneHit b D (n-1) j 0)
    (hn : 1 ≤ n) (hD : 0 ≤ D) (hj : j ≤ n-1) (cap : j*D ≤ S)
    (d : ℕ) (hd : (d:ℤ) ≤ j) :
    ∀ v : ℤ, 0 ≤ v → v < n →
      b ((j-(d:ℤ))*D-(d:ℤ)*n+v) = if v = 0 then 1 else 0 := by
  induction d with
  | zero =>
    intro v hv hv'
    simpa using single j v (by omega) hj hv (by omega)
  | succ d ih =>
    have hd' : (d:ℤ) < j := by omega
    let k := j-(d:ℤ)-1
    let p := k*D-(d:ℤ)*n
    have k0 : 0 ≤ k := by dsimp [k]; omega
    have d0 : 0 ≤ (d:ℤ) := by positivity
    have dpos := mul_nonneg d0 (show 0 ≤ n by omega)
    have kcap : k*D+(d:ℤ)*D ≤ S := by dsimp [k]; nlinarith
    have zeros := fill_triangle rec hn hD d (k*D) kcap (by
      intro i hi z hz hz'
      let v := z-(k*D+(i:ℤ)*D)
      have v0 : 0 ≤ v := by dsimp [v]; omega
      have v1 : v < n := by dsimp [v]; omega
      have e := single (k+i) v (by positivity) (by dsimp [k]; omega) v0 (by omega)
      rw [if_neg (show ¬ (k+(i:ℤ) = j ∧ v = 0) by dsimp [k]; omega)] at e
      convert e using 2
      dsimp [v]; ring)
    have zeroRow (v : ℤ) (hv : 0 ≤ v) (hv' : v < n) : b (p+v)=0 :=
      zeros _ (by dsimp [p]; omega) (by dsimp [p]; omega)
    have pcap : p ≤ S := by dsimp [p]; nlinarith [mul_nonneg d0 hD]
    have ed := fill_impulse (p := p) (u := 0) rec pcap (by omega) (by omega)
      (by simpa using zeroRow 0 (by omega) (by omega)) (by
        intro v hv hv'
        rw [zeroRow v hv hv', zero_add]
        convert ih (by omega) v hv hv' using 2
        dsimp [p,k]; ring)
    intro v hv hv'
    have atv := ed v hv hv'
    simp only [show v ≤ 0 ↔ v = 0 by omega] at atv
    convert atv using 2
    dsimp [p,k]; ring


/-- The short and long vertical successors of header column v in row j are
the same column of the auxiliary array Y, in rows j and j+1. -/
def Columns (H Y : ℤ → ℤ → ℕ) (q : ℤ) : Prop :=
  ∀ j v : ℤ, 0 ≤ j → j ≤ q → 0 ≤ v → v ≤ q →
    Edge (H j v) (if v = q then Y j 0 else H j (v+1)) (Y j v) (Y (j+1) v)

theorem header_columns {b : ℤ → ℕ} {n D S : ℤ} (_hn : 1 ≤ n) (hD : 0 ≤ D)
    (rec : Reflected b n (D+n) S) (bits : ∀ i, b i ≤ 1) (cap : (n-1)*D+n ≤ S) :
    Columns (fun j v => b (j*D+v)) (fun j v => b (j*D+n+v)) (n-1) := by
  intro j v hj hj' hv hv'
  have bd := mul_le_mul_of_nonneg_right hj' hD
  have e := rec (j*D+v) (by omega)
  have hhor : (if v = n-1 then b (j*D+n+0) else b (j*D+(v+1))) = b (j*D+v+1) := by
    split_ifs with ht <;> congr 1 <;> omega
  dsimp only
  rw [hhor, show (j+1)*D+n+v = j*D+v+(D+n) by ring,
      show j*D+n+v = j*D+v+n by ring]
  refine ⟨bits _, bits _, bits _, bits _, ?_⟩
  split at e <;> omega

theorem Edge.equal_vertical {a b c d : ℕ} (e : Edge a b c d)
    (ha : a=0) (hb : b=0) : c=d := by unfold Edge at e; omega

private theorem chain {f : ℤ → ℕ} {lo hi : ℤ} (h : lo ≤ hi)
    (step : ∀ j : ℤ, lo ≤ j → j < hi → f j = f (j+1)) : f lo = f hi := by
  refine Int.leInduction (motive := fun j _ => j ≤ hi → f lo = f j) ?_ ?_ hi h (by omega)
  · simp
  · intro j hj ih hj'
    exact (ih (by omega)).trans (step j hj (by omega))

/-- If the single reflected header hit lies in row zero, a member of an
even post-marker column must be set. -/
theorem first_header_contradiction {H Y : ℤ → ℤ → ℕ} {q u : ℤ}
    (cols : Columns H Y q) (hq : 4 ≤ q) (hqeven : q%2 = 0)
    (hu : 0 ≤ u) (hu' : u ≤ q)
    (hit : ∀ j v : ℤ, 0 ≤ j → j ≤ q → 0 ≤ v → v ≤ q →
      H j v = if j = 0 ∧ v = u then 1 else 0)
    (initial : ∀ v : ℤ, 1 ≤ v → v ≤ q → Y 0 v = 0)
    (late : ∀ v : ℤ, 0 ≤ v → v ≤ q → v%2 = 0 → Y (q+1) v = 0) : False := by
  have empty (j v : ℤ) (hj : 1 ≤ j) (hj' : j ≤ q) (hv : 0 ≤ v) (hv' : v ≤ q) :
      H j v = 0 := by rw [hit j v (by omega) hj' hv hv']; simp [show j ≠ 0 by omega]
  have high (j v : ℤ) (hj : 1 ≤ j) (hj' : j ≤ q+1) (hv : 0 ≤ v) (hv' : v < q) :
      Y j v = Y (q+1) v := by
    apply chain (f := fun k => Y k v) hj'
    intro k hk hk'
    have e := cols k v (by omega) (by omega) hv (by omega)
    rw [if_neg (by omega : v ≠ q)] at e
    exact e.equal_vertical (empty _ _ (by omega) (by omega) hv (by omega))
      (empty _ _ (by omega) (by omega) (by omega) (by omega))
  have firstzero (j : ℤ) (hj : 1 ≤ j) (hj' : j ≤ q+1) : Y j 0 = 0 :=
    (high j 0 hj hj' (by omega) (by omega)).trans (late 0 (by omega) (by omega) rfl)
  have last (j : ℤ) (hj : 1 ≤ j) (hj' : j ≤ q+1) : Y j q = 0 := by
    calc Y j q = Y (q+1) q := by
           apply chain (f := fun k => Y k q) hj'
           intro k hk hk'
           have e := cols k q (by omega) (by omega) (by omega) (by omega)
           simp only at e
           exact e.equal_vertical (empty _ _ (by omega) (by omega) (by omega) (by omega))
             (firstzero _ (by omega) (by omega))
         _ = 0 := late q (by omega) (by omega) hqeven
  have secondzero (v : ℤ) (hv : 0 ≤ v) (hv' : v ≤ q) (he : v%2=0) : Y 1 v=0 := by
    rcases hv'.eq_or_lt with rfl | hv'
    · exact last 1 (by omega) (by omega)
    · exact (high 1 v (by omega) (by omega) hv hv').trans (late v hv hv'.le he)
  have origin := cols 0 0 (by omega) (by omega) (by omega) (by omega)
  simp only [if_neg (show (0:ℤ) ≠ q by omega), zero_add, hit 0 0 (by omega) (by omega) (by omega) (by omega),
      hit 0 1 (by omega) (by omega) (by omega) (by omega), true_and, firstzero 1 (by omega) (by omega)] at origin
  unfold Edge at origin
  by_cases small : u ≤ 1
  · have yn : Y 0 0=1 := by split_ifs at origin <;> simp at origin <;> omega
    have e := cols 0 q (by omega) (by omega) (by omega) (by omega)
    simp only [zero_add, hit 0 q (by omega) (by omega) (by omega) (by omega),
        true_and, if_neg (show q ≠ u by omega), yn, initial q (by omega) (by omega),
        last 1 (by omega) (by omega)] at e
    unfold Edge at e; norm_num at e
  · let v := 2*(u/2)
    have hv : 1 ≤ v := by dsimp [v]; omega
    have hv' : v ≤ q := by dsimp [v]; omega
    have he : v%2 = 0 := by dsimp [v]; omega
    have near : v = u ∨ v+1 = u := by dsimp [v]; omega
    have yn : Y 0 0=0 := by split_ifs at origin <;> simp at origin <;> omega
    have e := cols 0 v (by omega) (by omega) (by omega) hv'
    rw [hit 0 v (by omega) (by omega) (by omega) hv', initial v hv hv'] at e
    simp only [zero_add, secondzero v (by omega) hv' he] at e
    by_cases vend : v = q
    · rw [if_pos vend, yn] at e
      unfold Edge at e; simp only [true_and] at e; split_ifs at e <;> simp at e; omega
    · rw [if_neg vend, hit 0 (v+1) (by omega) (by omega) (by omega) (by omega)] at e
      unfold Edge at e; simp only [true_and] at e; split_ifs at e <;> simp at e <;> omega


/-- Fill the entire left triangle under a zero suffix of the headers. -/
theorem zero_suffix {b : ℤ → ℕ} {n D S q k j u : ℤ}
    (rec : Reflected b n (D+n) S) (hn : 1 ≤ n) (hD : 0 ≤ D) (hq : q = n-1)
    (single : OneHit b D q j u) (hk : 0 ≤ k) (hk' : k ≤ q) (hj : j < k)
    (cap : q*D ≤ S) : Vanishes b (k*D-(q-k)*n) (k*D+n-1) := by
  have hd : (((q-k).toNat):ℤ) = q-k := Int.toNat_of_nonneg (by omega)
  have sub := fill_triangle rec hn hD (q-k).toNat (k*D) (by rw [hd]; nlinarith) (by
    intro t ht x hx hx'
    have ht' : 0 ≤ (t:ℤ) := by positivity
    let v := x-(k*D+(t:ℤ)*D)
    have v0 : 0 ≤ v := by dsimp [v]; omega
    have v1 : v ≤ q := by dsimp [v]; omega
    have e := single (k+t) v (by omega) (by omega) v0 v1
    rw [if_neg (show ¬ (k+(t:ℤ) = j ∧ v=u) by omega)] at e
    convert e using 2
    dsimp [v]; ring)
  rwa [hd] at sub

/-- Row-zero exception in terms of the actual reflected sequence. -/
theorem first_header {b : ℤ → ℕ} {n D S u : ℤ} (hn : 5 ≤ n)
    (hD : D=n*n-n+1) (hqeven : (n-1)%2=0) (hu : 0 ≤ u) (hu' : u < n)
    (rec : Reflected b n (D+n) S) (bits : ∀ i, b i ≤ 1) (cap : (n-1)*D+n ≤ S)
    (single : OneHit b D (n-1) 0 u)
    (late : ∀ v : ℤ, 0 ≤ v → v < n → v%2=0 → b (n*D+n+v)=0) : False := by
  have dpos : 0 ≤ D := by nlinarith [sq_nonneg (n-1)]
  have zeros := zero_suffix rec (by omega) dpos rfl single (k := 1) (by omega) (by omega) (by omega) (by omega)
  apply first_header_contradiction (header_columns (by omega) dpos rec bits cap) (by omega) hqeven hu (by omega) single
  · intro v hv hv'
    apply zeros
    · nlinarith
    · nlinarith [sq_nonneg (n-2)]
  · intro v hv hv' ev
    simpa using late v hv (by omega) ev

/-- A unique header hit at the origin of row one fixes all its neighboring
columns from the absence of the early odd and late even marks. -/
theorem second_header_columns {H Y : ℤ → ℤ → ℕ} {q : ℤ}
    (cols : Columns H Y q) (hq : 4 ≤ q) (hqeven : q%2=0)
    (hit : ∀ j v : ℤ, 0 ≤ j → j ≤ q → 0 ≤ v → v ≤ q →
      H j v = if j = 1 ∧ v = 0 then 1 else 0)
    (early : ∀ v : ℤ, 1 ≤ v → v < q → v%2=1 → Y 0 v=0)
    (late : ∀ v : ℤ, 0 ≤ v → v ≤ q → v%2=0 → Y (q+1) v=0) :
    (∀ j v : ℤ, 0 ≤ j → j ≤ q+1 → 1 ≤ v → v < q → Y j v=0) ∧
      Y 0 0=1 ∧ Y 1 0=1 ∧ Y 1 q=1 := by
  have empty (j v : ℤ) (hj : 0 ≤ j) (hj' : j ≤ q) (hv : 0 ≤ v) (hv' : v ≤ q)
      (h : j ≠ 1 ∨ v ≠ 0) : H j v=0 := by rw [hit j v hj hj' hv hv', if_neg (by omega)]
  have interior (j v : ℤ) (hj : 0 ≤ j) (hj' : j ≤ q) (hv : 1 ≤ v) (hv' : v < q) :
      Y j v = Y (j+1) v := by
    have e := cols j v hj hj' (by omega) (by omega)
    rw [if_neg (by omega : v ≠ q)] at e
    exact e.equal_vertical (empty _ _ hj hj' (by omega) (by omega) (by omega))
      (empty _ _ hj hj' (by omega) (by omega) (by omega))
  constructor
  · intro j v hj hj' hv hv'
    by_cases ev : v%2=0
    · exact (chain (f := fun k => Y k v) hj' (fun k _ _ => interior k v (by omega) (by omega) hv hv')).trans
        (late v (by omega) (by omega) ev)
    · exact (chain (f := fun k => Y k v) hj (fun k _ _ => interior k v (by omega) (by omega) hv hv')).symm.trans
        (early v hv hv' (by omega))
  · have col0 (j : ℤ) (hj : 2 ≤ j) (hj' : j ≤ q+1) : Y j 0=0 := by
      apply Eq.trans (b := Y (q+1) 0) _ (late 0 (by omega) (by omega) rfl)
      apply chain (f := fun k => Y k 0) hj'
      intro k hk hk'
      have e := cols k 0 (by omega) (by omega) (by omega) (by omega)
      rw [if_neg (by omega : (0:ℤ) ≠ q)] at e
      exact e.equal_vertical (empty _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
        (empty _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
    have e₁ := cols 1 0 (by omega) (by omega) (by omega) (by omega)
    have mark := hit 1 0 (by omega) (by omega) (by omega) (by omega)
    simp at mark
    rw [if_neg (by omega : (0:ℤ) ≠ q), mark, empty 1 (0+1) (by omega) (by omega)
        (by omega) (by omega) (by omega), col0 (1+1) (by omega) (by omega)] at e₁
    have y₁ : Y 1 0=1 := by unfold Edge at e₁; simp at e₁; omega
    have e₀ := cols 0 0 (by omega) (by omega) (by omega) (by omega)
    rw [if_neg (by omega : (0:ℤ) ≠ q)] at e₀
    have y₀ := e₀.equal_vertical (empty _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
      (empty _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
    have y₂q : Y 2 q=0 := by
      apply Eq.trans (b := Y (q+1) q) _ (late q (by omega) (by omega) hqeven)
      apply chain (f := fun k => Y k q) (by omega)
      intro k hk hk'
      have e := cols k q (by omega) (by omega) (by omega) (by omega)
      simp only at e
      exact e.equal_vertical (empty _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
        (col0 _ (by omega) (by omega))
    refine ⟨y₀.trans y₁,y₁,?_⟩
    have e := cols 1 q (by omega) (by omega) (by omega) (by omega)
    simp only at e
    rw [empty _ _ (by omega) (by omega) (by omega) (by omega) (by omega), y₁] at e
    rw [show (1:ℤ)+1=2 by decide, y₂q] at e
    unfold Edge at e; simp at e; omega


/-- A zero long successor reduces the reflected recursion below its marked
boundary D to the forward two-lag recursion, read in reverse. -/
theorem reverse_block {a b : ℤ → ℕ} {n D S : ℤ} (hn : 1 ≤ n) (_hD : 2*n < D)
    (cap : D ≤ S) (aRec : Forward a n (D+n)) (first : a 0=1)
    (neg : ∀ z < 0, a z=0) (rec : Reflected b n (D+n) S)
    (header : ∀ v : ℤ, 0 ≤ v → v < n → b (D+v)=if v=0 then 1 else 0)
    (long : ∀ i : ℤ, n+1 ≤ i → i < D → b (i+(D+n))=0)
    (i : ℤ) (hi : n+1 ≤ i) (hi' : i ≤ D) : b i=a (D-i) := by
  have matchWord (z : ℤ) (lower : 1-n ≤ z) (upper : z ≤ D-n-1) : b (D-z)=a z := by
    induction z using Int.strongRec (m := 1) with
    | lt z hz =>
      have e := header (-z) (by omega) (by omega)
      rw [← sub_eq_add_neg] at e
      by_cases h : z=0
      · simpa [h,first] using e
      · rw [neg z (by omega), e, if_neg (by omega)]
    | ge z hz ih =>
      have af := aRec z (by omega)
      rw [neg (z-(D+n)) (by omega)] at af
      have br := rec (D-z) (by omega)
      have h₁ := ih (z-1) (by omega) (by omega) (by omega)
      have h₂ := ih (z-n) (by omega) (by omega) (by omega)
      rw [show D-z+1 = D-(z-1) by omega, h₁, show D-z+n = D-(z-n) by omega, h₂,
          long (D-z) (by omega) (by omega)] at br
      exact br.trans af.symm
  simpa using matchWord (D-i) (by omega) (by omega)

/-- The unique header hit at D is incompatible with the known companion
marks. Its translated length-L word equals the forbidden three-point seed. -/
theorem second_header {a b : ℤ → ℕ} {n D S : ℤ} (hn : 17 ≤ n)
    (hD : D=n*n-n+1) (hqeven : (n-1)%2=0) (rec : Reflected b n (D+n) S)
    (bits : ∀ i, b i ≤ 1) (cap : (n-1)*D+n ≤ S) (bigcap : D+4*(D+n)-2 ≤ S)
    (single : OneHit b D (n-1) 1 0)
    (af : Forward a n (D+n)) (first : a 0=1) (neg : ∀ z < 0, a z=0)
    (mark : a (D-2*n)=1)
    (early : ∀ v : ℤ, 1 ≤ v → v < n-1 → v%2=1 → b (n+v)=0)
    (late : ∀ v : ℤ, 0 ≤ v → v < n → v%2=0 → b (n*D+n+v)=0) : False := by
  have dlarge : 3*n < D := by nlinarith [sq_nonneg (n-3)]
  have cols := header_columns (by omega) (by omega) rec bits cap
  obtain ⟨interior,c₀,c₁,cq⟩ := second_header_columns cols (by omega) hqeven single
    (by intro v hv hv' ho; simpa using early v hv hv' ho)
    (by intro v hv hv' he; simpa using late v hv (by omega) he)
  simp only [zero_mul, zero_add, add_zero, one_mul] at c₀ c₁ cq
  have suffix := zero_suffix rec (by omega) (by omega) rfl single (k := 2)
    (by omega) (by omega) (by omega) (by omega)
  have start : 2*D-(n-1-2)*n = D+2*n+1 := by rw [hD]; ring
  rw [start] at suffix
  have hhead (v : ℤ) (hv : 0 ≤ v) (hv' : v < n) : b (D+v)=if v=0 then 1 else 0 := by
    simpa using single 1 v (by omega) (by omega) hv (by omega)
  have long (i : ℤ) (hi : n+1 ≤ i) (hi' : i < D) : b (i+(D+n))=0 :=
    suffix _ (by omega) (by omega)
  have rev := reverse_block (by omega) (by omega) (by omega) af first neg rec hhead long
    (2*n) (by omega) (by omega)
  have e := rec n (by omega)
  have col1 := interior 0 1 (by omega) (by omega) (by omega) (by omega)
  simp only [zero_mul, zero_add] at col1
  rw [c₀, col1, show n+n=2*n by omega, rev, mark] at e
  have boundary : b (D+2*n)=0 := by
    rw [show D+2*n=n+(D+n) by omega]
    split at e <;> omega
  apply exceptional_seed (fun i => b (D+i)) n (D+n) hn (by rw [hD]; ring) (fun i => bits _)
  · intro i hi hi'
    simpa only [← add_assoc] using rec (D+i) (by omega)
  · intro i hi hi'
    by_cases h : i < n
    · rw [hhead i hi h]
      split_ifs <;> omega
    · by_cases h' : i ≤ 2*n-1
      · let v := i-n
        have hv : 0 ≤ v := by dsimp [v]; omega
        have hv' : v ≤ n-1 := by dsimp [v]; omega
        rcases (show v=0 ∨ v=n-1 ∨ (1≤ v ∧ v< n-1) by omega) with hz|hz|⟨hx,hy⟩
        · have ie : i=n := by dsimp [v] at hz; omega
          subst i
          simpa using c₁
        · have ie : i=2*n-1 := by dsimp [v] at hz; omega
          rw [ie, if_pos (by omega), show D+(2*n-1) = D+n+(n-1) by omega]
          exact cq
        · have hzero := interior 1 v (by omega) (by omega) hx hy
          simp only [one_mul] at hzero
          have ie : D+i = D+n+v := by dsimp [v]; omega
          rw [ie,hzero,if_neg (by dsimp [v] at hx hy; omega)]
      · rw [if_neg (by omega)]
        by_cases h₂ : i=2*n
        · simpa [h₂] using boundary
        · exact suffix _ (by omega) (by omega)

end KucaTail

namespace KucaLate
open KucaInitial KucaLucas KucaShift KucaTail
variable {q : ℕ} {a : ℤ → ℕ} {s : ℕ}

def hit (a : ℤ → ℕ) (s x : ℤ) := a x=1 ∧ a (s-x)=1

theorem two_hits (A : Data q a) {x y : ℤ} (hx : hit a s x) (hy : hit a s y)
    (hne : x≠y) (hpair : x+y≠s) : Covered (mark a) s := by
  have non (i : ℤ) (hi : a i=1) : 0 ≤ i := by
    by_contra! h
    have := A.neg i h
    omega
  obtain ⟨h₁,h₂⟩ := hx
  obtain ⟨h₃,h₄⟩ := hy
  have n₁ := non _ h₁
  have n₂ := non _ h₂
  have n₃ := non _ h₃
  have n₄ := non _ h₄
  refine ⟨x.toNat,((s:ℤ)-x).toNat,y.toNat,((s:ℤ)-y).toNat,by omega,by omega,
    ?_,?_,?_,?_,by omega,by omega⟩ <;> simp only [mark,Int.toNat_of_nonneg n₁,Int.toNat_of_nonneg n₂,Int.toNat_of_nonneg n₃,Int.toNat_of_nonneg n₄] <;> assumption

theorem data_bit (A : Data q a) (i : ℤ) : a i≤ 1 := by
  rcases lt_trichotomy i 0 with h|h|h
  · rw [A.neg i h]; decide
  · rw [h,A.seed]
  · rw [A.step i h]; unfold one; split <;> decide

theorem zero_from_hit (A : Data q a) (lack : ¬Covered (mark a) s) {x y : ℤ}
    (hx : hit a s x) (my : a y=1) (diff : y≠x) (anti : x+y≠s) : a ((s:ℤ)-y)=0 := by
  have bits := data_bit A ((s:ℤ)-y)
  by_contra! nz
  exact lack (two_hits A hx ⟨my,by omega⟩ diff.symm anti)

/-- Equal residues in the header interval force equal block coordinates. -/
theorem decode {d q i j u v : ℤ} (hq : q< d) (hu : 0≤ u) (hu' : u≤ q)
    (hv : 0≤ v) (hv' : v≤ q) (eq : i*d+u=j*d+v) : i=j ∧ u=v := by
  have H (i j u v : ℤ) (hi : i< j) (h : i*d+u=j*d+v) (hl : u< d) (hv : 0≤ v) : False := by
    have upper := mul_le_mul_of_nonneg_right (show i+1≤ j by omega) (show 0≤ d by omega)
    rw [add_mul,one_mul] at upper
    omega
  have hij : i=j := by
    rcases lt_trichotomy i j with h|h|h
    · exact (H _ _ _ _ h eq (by omega) hv).elim
    · exact h
    · exact (H _ _ _ _ h eq.symm (by omega) hu).elim
  subst j; omega

theorem header_mark (A : Data q a) {j u : ℤ}
    (hj : 0≤ j) (hj' : j≤ q) (hu : 0≤ u) (hu' : u≤ q) : a (j*D q+u)=1 := by
  apply A.front hj hj' hu (by unfold N; omega)

theorem header_pair (A : Data q a) {j k u v : ℤ}
    (hj : 0≤ j) (hj' : j≤ q) (hu : 0≤ u) (hu' : u≤ q)
    (hk : 0≤ k) (hk' : k≤ q) (hv : 0≤ v) (hv' : v≤ q)
    (hs : D q < s) (he : (j*D q+u)+(k*D q+v)=s) : Covered (mark a) s := by
  have castD : (d q:ℤ) = D q := by simp [d,D,N]
  have he' : (j.toNat*d q+u.toNat)+(k.toNat*d q+v.toNat)=s := by
    exact_mod_cast (show ((↑(j.toNat*d q+u.toNat+(k.toNat*d q+v.toNat)):ℤ))=(s:ℤ) by
      push_cast; simp only [castD,Int.toNat_of_nonneg hj,Int.toNat_of_nonneg hk,Int.toNat_of_nonneg hu,Int.toNat_of_nonneg hv]; exact he)
  rw [← he']
  apply header_sum A (by omega) (by omega) (by omega) (by omega)
  rw [he']; exact_mod_cast (castD ▸ hs : (d q:ℤ)< s)

theorem unique_headers (A : Data q a) (lack : ¬Covered (mark a) s)
    {j u : ℤ} (hj : 0≤ j) (hj' : j≤ q) (hu : 0≤ u) (hu' : u≤ q)
    (hs : D q< s) (hit₀ : hit a s (j*D q+u)) :
    OneHit (fun i => a ((s:ℤ)-i)) (D q) q j u := by
  have hlarge := A.qlarge
  have qd : (q:ℤ)< D q := by dsimp [D,N]; nlinarith
  intro k v hk hk' hv hv'
  split_ifs with H
  · obtain ⟨rfl,rfl⟩ := H; exact hit₀.2
  · exact zero_from_hit A lack hit₀ (header_mark A hk hk' hv hv')
      (fun e => H (decode qd hv hv' hu hu' e))
      (fun e => lack (header_pair A hj hj' hu hu' hk hk' hv hv' hs e))

abbrev P (q : ℕ) := N q*D q+N q
abbrev T (q : ℕ) := (N q+2)*D q+3*(q:ℤ)
abbrev cap (q : ℕ) := (2*(q:ℤ)-1)*D q+2*q

theorem no_hit_covered (A : Data q a) (hlarge : 16≤ q) (hs : cap q< s)
    (empty : ∀ j u : ℤ, 0≤ j → j≤ q → 0≤ u → u≤ q → a ((s:ℤ)-(j*D q+u))=0) :
    Covered (mark a) s := by
  let b := fun i : ℤ => a ((s:ℤ)-i)
  have dn : D q=N q*N q-N q+1 := by dsimp [D,N]; ring
  have ln : L q=N q*N q+1 := by dsimp [L]; ring
  have dl : D q+N q=L q := by dsimp [D,N,L]; ring
  have hn : 17≤ N q := by unfold N; omega
  have dpos : 0≤ D q := by unfold D N; positivity
  have dq : (q:ℤ)< D q := by dsimp [D,N]; nlinarith only [sq_nonneg (q:ℤ)]
  have recF : Forward a (N q) (L q) := A.step
  have recR := reflected_of_forward recF (s:ℤ)
  have recD : Reflected b (N q) (D q+N q) s := by rw [dl]; exact recR
  have bb (i : ℤ) : b i≤ 1 := data_bit A _
  have startCap : (q:ℤ)*D q+1< s := by
    have H := mul_nonneg (show 0≤ (q:ℤ)-1 by omega) dpos
    dsimp [cap] at hs; nlinarith
  have endCap : N q+(N q+1)*(L q) ≤ (s:ℤ) := by
    have H := mul_nonneg (show 0≤ (q:ℤ)-5 by omega) dpos
    have Dform : (q:ℤ)*(q+1)=D q-1 := by unfold D N; ring
    rw [← dl]
    dsimp only [cap,N] at hs ⊢
    nlinarith only [hs,H,dq,Dform]
  have edges (j : ℕ) (hj : j≤ q) : Vanishes b ((j:ℤ)*D q) ((j:ℤ)*D q+N q-1) := by
    intro t tl tu
    have H := empty j (t-j*D q) (by positivity) (by exact_mod_cast hj) (by omega) (by unfold N at tu; omega)
    simpa [b] using H
  obtain ⟨seed,hP⟩ := no_header_seed (b:=b) q rfl (by omega) dn startCap recD bb
    (by
      intro lo h
      rw [dl] at h ⊢
      exact reflected_window recF (data_bit A) A.seed (by omega)
        (by rw [ln]; nlinarith only [sq_nonneg (N q-1),hn]) s lo h) edges
  rw [dl] at seed
  obtain ⟨k,hk⟩ := A.dyadic
  have hT := no_header_second q (by omega) ln rfl (four_dvd hk (by omega)) endCap recR bb seed
  have tag : N q+(N q+1)*L q-2=T q := by unfold T N L D; ring
  rw [tag] at hT
  obtain ⟨aP,aP₂,_,aT,aT₂⟩ := A.witnesses
  have gap : P q+4< T q := by unfold P T; unfold N; nlinarith only [dq,hn]
  by_cases h : P q+T q=s
  · have hb₂ : a ((s:ℤ)-(P q+2))=1 := by
      rw [show (s:ℤ)-(P q+2)=T q-2 by omega]
      simpa [B,T,origin,D,sub_eq_add_neg,add_assoc] using aT₂
    exact two_hits A (x:=P q) (y:=P q+2) ⟨aP,hP⟩ ⟨by simpa [B,P,D,origin,add_assoc] using aP₂,hb₂⟩ (by omega) (by omega)
  · exact two_hits A (x:=P q) (y:=T q) ⟨aP,hP⟩ ⟨aT,hT⟩ (by omega) h

end KucaLate

namespace KucaLate
open KucaInitial KucaLucas KucaShift KucaTail
variable {q : ℕ} {a : ℤ → ℕ} {s : ℕ}

theorem odd_block {m : ℕ} (A : Data q a) (hm : 0< m) (hu : m< q) (ho : m%2=1) :
    a ((m:ℤ)*D q-N q)=1 := by
  obtain ⟨k,hk⟩ := A.dyadic
  have hq := A.qlarge
  have eq := A.evenq
  have mask : (m-1) &&& (q-1)=m-1 := by
    rw [hk]; apply Nat.and_two_pow_sub_one_of_lt_two_pow; omega
  have slim : (m-1) &&& (q-2)=m-1 := by
    rw [mask_split] at mask ⊢
    rw [show (q-2)/2=(q-1)/2 by omega]
    exact ⟨mask.1,by omega⟩
  have H := (row (A.prefixBlock (m-1) (by omega)) (h:=q-1) (s:=0) (by omega) (by omega)
    (by omega)).mpr ⟨by rwa [show q-1-1=q-2 by omega], by simp⟩
  unfold mark at H
  convert H using 2
  push_cast [d,base]
  rw [show ((m-1:ℕ):ℤ)=(m:ℤ)-1 by omega, show ((q-1:ℕ):ℤ)=(q:ℤ)-1 by omega]
  unfold D N; ring

theorem later_anchor {j : ℕ} (A : Data q a) (hp : 2≤ j) (hj : j≤ q) :
    a (D q-((j-1:ℕ):ℤ)*N q)=1 := by
  have hq := A.qlarge
  have H := (first_row (A.prefixBlock 0 (by omega)) (h:=q-(j-1)) (s:=0) (by omega) (by omega)).mpr
    ⟨by omega,by simp⟩
  unfold mark at H
  convert H using 2
  push_cast [base]
  rw [show ((q-(j-1):ℕ):ℤ)=(q:ℤ)-(j-1:ℕ) by omega]
  unfold D N; ring

theorem ordinary_single (A : Data q a) (hlarge : 16≤ q) (hs : cap q< s)
    {j u : ℕ} (hj : 1≤ j) (hj' : j≤ q) (hu : u≤ q) (nonexc : 2≤ j ∨ 0< u)
    (single : OneHit (fun i => a ((s:ℤ)-i)) (D q) (q:ℤ) j u) :
    Covered (mark a) s := by
  let b := fun i : ℤ => a ((s:ℤ)-i)
  let x := (j:ℤ)*D q+u
  have hx : hit a s x := ⟨header_mark A (by positivity) (by omega) (by positivity) (by omega),
    by simpa [x] using single j u (by positivity) (by omega) (by positivity) (by omega)⟩
  have dl : D q+N q=L q := by unfold D N L; ring
  have recD : Reflected b (N q) (D q+N q) s := by
    rw [dl]; exact reflected_of_forward A.step s
  have sq : N q-1=(q:ℤ) := by unfold N; omega
  rw [← sq] at single
  have dpos : 0≤ D q := by unfold D N; positivity
  have npos : 0< N q := by unfold N; positivity
  have dq : (q:ℤ)< D q := by unfold D N; nlinarith only [sq_nonneg (q:ℤ)]
  have capJ := mul_le_mul_of_nonneg_right (show (j:ℤ)≤ q by omega) dpos
  have jcap : (j:ℤ)*D q≤ s := by
    have H:=mul_nonneg (show 0≤ (q:ℤ)-1 by omega) dpos
    unfold cap at hs; nlinarith
  have finish (y : ℤ) (ma : a y=1) (mb : b y=1) (le : y< x)
      (bound : y≤ ((q:ℤ)-1)*D q) : Covered (mark a) s := by
    apply two_hits A hx ⟨ma,mb⟩ le.ne'
    dsimp [x]; unfold cap at hs; nlinarith only [hs,capJ,bound,(show (u:ℤ)≤ q by omega)]
  by_cases hpos : 0< u
  · let m := if j%2=1 then j else j-1
    have qeven := A.evenq
    have prop : 0< m ∧ m< q ∧ m%2=1 ∧ m≤ j ∧ (j=m ∨ j=m+1) := by
      dsimp [m]; split <;> omega
    obtain ⟨mp,mq,mo,mj,madj⟩ := prop
    have mcap := mul_le_mul_of_nonneg_right (show (m:ℤ)≤ j by omega) dpos
    have mqcap := mul_le_mul_of_nonneg_right (show (m:ℤ)≤ (q:ℤ)-1 by omega) dpos
    have ref := positive_column (m:=(m:ℤ)) recD single (by omega) (by unfold N; omega)
      (by positivity) (by unfold N; omega) (by omega) (by omega)
    exact finish _ (odd_block A mp mq mo) ref (by dsimp [x]; omega) (by omega)
  · have zu : u=0 := by omega
    subst u
    have jtwo : 2≤ j := by omega
    have ref := column_zero_impulse recD single (by omega) dpos (by unfold N; omega) jcap
      (j-1) (by omega) 0 (by omega) (by omega)
    have diff : (j:ℤ)-(j-1:ℕ)=1 := by omega
    simp only [diff,one_mul,add_zero,ite_true] at ref
    have p := mul_nonneg (show (0:ℤ)≤ (j-1:ℕ) by positivity) npos.le
    have bound := mul_le_mul_of_nonneg_right (show (1:ℤ)≤ (q:ℤ)-1 by omega) dpos
    have lt := mul_le_mul_of_nonneg_right (show (2:ℤ)≤ j by omega) dpos
    exact finish _ (later_anchor A jtwo hj') ref
      (by dsimp [x]; nlinarith only [p,lt,dq,(show 0≤ (q:ℤ) by positivity)])
      (by rw [one_mul] at bound; omega)

end KucaLate

namespace KucaLate
open KucaInitial KucaLucas KucaShift KucaTail
variable {q : ℕ} {a : ℤ → ℕ} {s : ℕ}

theorem exceptional_single (A : Data q a) (hlarge : 16≤ q) (hs : cap q< s)
    {j u : ℕ} (hj : j≤ 1) (hu : u≤ q) (spec : j=0 ∨ u=0)
    (single : OneHit (fun i => a ((s:ℤ)-i)) (D q) (q:ℤ) j u) :
    Covered (mark a) s := by
  by_contra lack
  let b := fun i : ℤ => a ((s:ℤ)-i)
  let x := (j:ℤ)*D q+u
  have hx : hit a s x := ⟨header_mark A (by positivity) (by omega) (by positivity) (by omega),
    by simpa [x] using single j u (by positivity) (by omega) (by positivity) (by omega)⟩
  have dl : D q+N q=L q := by unfold D N L; ring
  have dn : D q=N q*N q-N q+1 := by unfold N D; ring
  have hn : 17≤ N q := by unfold N; omega
  have sq : N q-1=(q:ℤ) := by unfold N; omega
  have dpos : 0≤ D q := by unfold D N; positivity
  have dq : 4*(q:ℤ)+4< D q := by
    unfold D N; nlinarith only [sq_nonneg ((q:ℤ)-4),(show 16≤ (q:ℤ) by omega)]
  have xpos : x≤ D q+q := by
    have E := mul_le_mul_of_nonneg_right (show (j:ℤ)≤ 1 by omega) dpos
    dsimp [x]; rw [one_mul] at E; omega
  have gap : D q+q + (N q*D q+2*N q-1) < (s:ℤ) := by
    have e := mul_nonneg (show 0≤ (q:ℤ)-4 by omega) dpos
    unfold N cap at *; nlinarith only [hs,e,dq]
  have startCap : (N q-1)*D q+N q ≤ (s:ℤ) := by
    rw [sq]; unfold N at gap ⊢; nlinarith only [gap,dpos,(show 0≤ (q:ℤ) by omega)]
  have endCap : D q+4*(D q+N q)-2 ≤ (s:ℤ) := by
    have e := mul_nonneg (show 0≤ (q:ℤ)-6 by omega) dpos
    unfold N cap at *; nlinarith only [hs,e,dq]
  have af : Forward a (N q) (D q+N q) := by rw [dl]; exact A.step
  have rf : Reflected b (N q) (D q+N q) s := reflected_of_forward af s
  have bits (i : ℤ) : b i≤ 1 := data_bit A _
  have evenq : (N q-1)%2=0 := by rw [sq]; exact_mod_cast A.evenq
  have largeP : D q+(q:ℤ)< P q := by
    have e := mul_nonneg (show 0≤ (q:ℤ)-1 by omega) dpos
    unfold P N; nlinarith only [e,dq]
  have late (v : ℤ) (hv : 0≤ v) (hv' : v< N q) (he : v%2=0) : b (N q*D q+N q+v)=0 := by
    have vr : v.toNat≤ q := by unfold N at hv'; omega
    have ev := (A.row1 v.toNat vr).1
    have ve : v.toNat%2=0 := by omega
    simp only [ve,Nat.sub_zero,Int.toNat_of_nonneg hv] at ev
    apply zero_from_hit A lack hx (y:=N q*D q+N q+v)
    · simpa [B,D,origin,add_assoc] using ev
    · change D q+q< N q*D q+N q at largeP; omega
    · omega
  rw [← sq] at single
  rcases spec with jz|uz
  · subst j
    exact first_header (by omega) dn evenq (by positivity) (by unfold N; omega)
      rf bits startCap single late
  · subst u
    by_cases jz : j=0
    · subst j
      exact first_header (by omega) dn evenq (by positivity) (by unfold N; omega)
        rf bits startCap single late
    have jone : j=1 := by omega
    subst j
    have xm : x=D q := by simp [x]
    have anchor : a (D q-2*N q)=1 := by
      simpa using later_anchor (j:=3) A (by omega) (by omega)
    have early (v : ℤ) (hv : 1≤ v) (hv' : v< N q-1) (vo : v%2=1) : b (N q+v)=0 := by
      have t := (first_row (A.prefixBlock 0 (by omega)) (h:=1) (s:=(v-1).toNat)
        (by omega) (by omega)).mpr ⟨by omega,by rw [Nat.and_comm]; simp; omega⟩
      apply zero_from_hit A lack hx (y:=N q+v)
      · unfold mark at t
        convert t using 2
        push_cast [base,N]
        omega
      · unfold N at hv' ⊢; omega
      · have := mul_nonneg (show 0≤ N q-1 by omega) dpos
        nlinarith only [gap,hv',xm,this,hn,(show 0≤ (q:ℤ) by omega)]
    exact second_header hn dn evenq rf bits startCap endCap single af A.seed A.neg anchor early late

/-- All later companion sums have two unordered marked representations. -/
theorem late_cover (A : Data q a) (hlarge : 16≤ q) (hs : cap q< s) : Covered (mark a) s := by
  classical
  have dpos : 0≤ D q := by unfold D N; positivity
  have ds : D q< (s:ℤ) := by
    have H := mul_nonneg (show 0≤ (q:ℤ)-2 by omega) dpos
    unfold cap at hs; nlinarith
  by_cases existsHit : ∃ j u : ℕ, j≤ q ∧ u≤ q ∧ a ((s:ℤ)-((j:ℤ)*D q+u))=1
  · obtain ⟨j,u,hj,hu,hb⟩ := existsHit
    by_contra lack
    have h := unique_headers A lack (j:=(j:ℤ)) (u:=(u:ℤ)) (by positivity) (by omega)
      (by positivity) (by omega) ds ⟨header_mark A (by positivity) (by omega) (by positivity) (by omega),hb⟩
    by_cases hej : j=0 ∨ (j=1 ∧ u=0)
    · exact lack (exceptional_single A hlarge hs (by omega) hu (by omega) h)
    · exact lack (ordinary_single A hlarge hs (by omega) hj hu (by omega) h)
  · apply no_hit_covered A hlarge hs
    intro j u hj hj' hu hu'
    have h₁ := data_bit A ((s:ℤ)-(j*D q+u))
    by_contra! hn
    exact existsHit ⟨j.toNat,u.toNat,by omega,by omega,by
      rw [Int.toNat_of_nonneg hj,Int.toNat_of_nonneg hu]; omega⟩

theorem all_cover (A : Data q a) (hlarge : 16≤ q) {s : ℕ}
    (hs : 2≤ s) (hd : s≠d q) : Covered (mark a) s := by
  by_cases h : s≤ (2*q-1)*d q+2*q
  · exact initial_cover A hs hd h
  · apply late_cover A hlarge
    have E : (↑((2*q-1)*d q+2*q):ℤ)=cap q := by
      push_cast [d,cap,D,N,Nat.cast_sub (show 1≤ 2*q by omega)]
      ring
    omega

end KucaLate

namespace KucaSmall
open KucaLucas KucaShift KucaInitial

/-- Numerically test a bounded predicate using only its Boolean values. -/
def check : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | i+1, f => f i && check i f

theorem check_sound {m : ℕ} {f : ℕ → Bool} (hc : check m f) {i : ℕ} (hi : i< m) : f i := by
  induction m with
  | zero => omega
  | succ m ih =>
    change (f m && check m f) = true at hc
    obtain ⟨hm,hr⟩ : f m = true ∧ check m f = true := by simpa using hc
    rcases (show i< m ∨ i=m by omega) with h | rfl
    · exact ih hr h
    · exact hm

def cell (word : ℕ) (i : ℤ) : ℕ := if i< 0 then 0 else (word >>> i.toNat)%2

def prefixOK (q word m : ℕ) :=
  check m fun t => decide (cell word t = if t=0 then 1 else
    one (cell word (t-1 : ℤ)) (cell word ((t:ℤ)-N q)) (cell word ((t:ℤ)-L q)))

theorem prefix_sound {q w m : ℕ} {a : ℤ → ℕ} (A : Data q a) (hc : prefixOK q w m) :
    ∀ i : ℤ, i< m → a i = cell w i := by
  have hi (t : ℕ) (ht : t< m) : a t = cell w t := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      have e := of_decide_eq_true (check_sound hc ht)
      change cell w t = (if t=0 then 1 else _) at e
      by_cases hz : t=0
      · subst t; simpa using A.seed.trans e.symm
      have old (i : ℤ) (h : i< t) : a i = cell w i := by
        by_cases hn : i< 0
        · simp [A.neg i hn,cell,hn]
        have hn' : 0 ≤ i := by omega
        simpa [Int.toNat_of_nonneg hn'] using ih i.toNat (by omega) (by omega)
      rw [if_neg hz] at e
      rw [A.step _ (by omega),old _ (by omega),old ((t:ℤ)-N q) (by linarith [A.npos]),
        old ((t:ℤ)-L q) (by dsimp [L]; nlinarith [A.npos]),e]
  intro i him
  by_cases hn : i< 0
  · simp [A.neg i hn,cell,hn]
  have hz : 0 ≤ i := by omega
  simpa [Int.toNat_of_nonneg hz] using hi i.toNat (by omega)

def packed (width w i : ℕ) := (w >>> (width*i)) % 2^width

def sumsOK (word start count w xcode ucode : ℕ) :=
  check count fun i =>
    let s := start+i
    let x := packed w xcode i
    let u := packed w ucode i
    decide (x< u ∧ 2*u≤ s ∧ cell word x=1 ∧ cell word (s-x : ℕ)=1 ∧
      cell word u=1 ∧ cell word (s-u : ℕ)=1)

theorem sums_sound {q word m start count w xcode ucode : ℕ} {a : ℤ → ℕ}
    (A : Data q a) (hc : prefixOK q word m) (hsum : sumsOK word start count w xcode ucode)
    {s : ℕ} (lo : start≤ s) (hi : s< start+count) (hm : s< m) : Covered (mark a) s := by
  let i := s-start
  have e := of_decide_eq_true (check_sound hsum (i:=i) (by dsimp [i];omega))
  have eq : start+i=s := by dsimp [i];omega
  rw [eq] at e
  obtain ⟨hlt,hs,ax,ay,au,av⟩ := e
  let x := packed w xcode i
  let u := packed w ucode i
  change x< u at hlt
  change 2*u≤ s at hs
  have tr (k : ℕ) (hk : k≤ s) (h : cell word k = 1) : mark a k :=
    (prefix_sound A hc k (by omega)).trans h
  exact ⟨x,s-x,u,s-u,by omega,by omega,tr _ (by omega) ax,tr _ (by omega) ay,
    tr _ (by omega) au,tr _ (by omega) av,by omega,by omega⟩

theorem DataBinary {q : ℕ} {a : ℤ → ℕ} (A : Data q a) (i : ℤ) : a i≤ 1 := by
  rcases lt_trichotomy i 0 with hn|he|hp
  · rw [A.neg i hn];omega
  · rw [he,A.seed]
  · rw [A.step i hp];unfold one;split_ifs <;> omega

/-- No nonnegative companion interval of length L can be entirely zero. -/
theorem gap {q : ℕ} {a : ℤ → ℕ} (A : Data q a) (t : ℕ) :
    ∃ i : ℤ, (t:ℤ) ≤ i ∧ i < (t:ℤ)+L q ∧ a i=1 := by
  have hn := A.npos
  have hL : N q< L q := by unfold L;nlinarith
  induction t with
  | zero => exact ⟨0,by simp,by simpa only [Nat.cast_zero,zero_add] using lt_trans hn hL,A.seed⟩
  | succ t ih =>
    obtain ⟨j,hj,hl,haj⟩ := ih
    by_contra! h
    have zero (z : ℤ) (hz : (t:ℤ)+1≤ z) (hz' : z< (t:ℤ)+1+L q) : a z=0 := by
      have he := h z (by exact_mod_cast hz) (by exact_mod_cast hz')
      have hb := DataBinary A z
      omega
    have eq : j=t := by
      by_contra e
      have := zero j (by omega) (by omega)
      omega
    have pos : 0< (t:ℤ)+L q := by omega
    have e := A.step _ pos
    rw [zero ((t:ℤ)+L q-1) (by omega) (by omega),
      zero ((t:ℤ)+L q-N q) (by omega) (by omega),
      show (t:ℤ)+L q-L q=j by omega,haj] at e
    have := zero ((t:ℤ)+L q) (by omega) (by omega)
    simp [one] at e;omega

def offset (n l d : ℕ) := if d=0 then 0 else if d=1 then 1 else if d=2 then n else l

/-- Three zero vertices in a reflected recurrence edge force its fourth zero. -/
theorem force {q n l : ℕ} {a : ℤ → ℕ} (A : Data q a) (eh : (n:ℤ)=N q) (el : (l:ℤ)=L q)
    {s b : ℕ} (hb : b< s) {d : ℕ} (hd : d< 4)
    (z : ∀ k : ℕ, k< 4 → k≠d → a ((s:ℤ)-(b+offset n l k:ℕ)) = 0) :
    a ((s:ℤ)-(b+offset n l d:ℕ))=0 := by
  have ed := A.step ((s:ℤ)-b) (by omega)
  let g (k : ℕ) := a ((s:ℤ)-(b+offset n l k:ℕ))
  have rel : g 0=one (g 1) (g 2) (g 3) := by
    have e (t : ℤ) : (s:ℤ)-(b+t)=s-b-t := by ring
    simpa [g,offset,eh,el,e] using ed
  change g d=0
  have zb (k : ℕ) (hk : k< 4) (hkd : k≠d) : g k=0 := z k hk hkd
  have bd (k : ℕ) : g k ≤ 1 := DataBinary A _
  interval_cases d
  · rw [zb 1 (by decide) (by decide), zb 2 (by decide) (by decide), zb 3 (by decide) (by decide)] at rel
    exact rel
  · rw [zb 0 (by decide) (by decide), zb 2 (by decide) (by decide), zb 3 (by decide) (by decide)] at rel
    have := bd 1
    unfold one at rel
    split_ifs at rel <;> omega
  · rw [zb 0 (by decide) (by decide), zb 1 (by decide) (by decide), zb 3 (by decide) (by decide)] at rel
    have := bd 2
    unfold one at rel
    split_ifs at rel <;> omega
  · rw [zb 0 (by decide) (by decide), zb 1 (by decide) (by decide), zb 2 (by decide) (by decide)] at rel
    have := bd 3
    unfold one at rel
    split_ifs at rel <;> omega

end KucaSmall

namespace KucaSmall
open KucaLucas KucaShift KucaInitial

structure Window where
  start : ℕ
  width : ℕ
  bits : ℕ
  ranks : ℕ
  sides : ℕ

def rank (w : Window) (i : ℕ) := packed w.bits w.ranks i
def side (w : Window) (i : ℕ) := packed 2 w.sides i

def windowOK (n l word : ℕ) (w : Window) :=
  check w.width fun i =>
    let d := side w i
    let b := i-offset n l d
    decide (rank w i = 0 ∨ cell word (w.start+i : ℕ)=1 ∨
      (d< 4 ∧ offset n l d ≤ i ∧ b+l< w.width ∧
        ∀ e : Fin 4, e.val≠d → 0< rank w (b+offset n l e) ∧ rank w (b+offset n l e)< rank w i))

def runOK (l : ℕ) (w : Window) := check l fun i => decide (0< rank w i)

theorem window_hit {q n l word m : ℕ} {a : ℤ → ℕ} (A : Data q a) (eh : (n:ℤ)=N q)
    (el : (l:ℤ)=L q) (pref : prefixOK q word m) (w : Window) (hw : windowOK n l word w)
    (hl : runOK l w) (hw' : l≤ w.width) (hw'' : w.start+w.width≤ m) {s : ℕ}
    (hS : w.start+w.width≤ s) :
    ∃ x : ℕ, w.start≤ x ∧ x< w.start+w.width ∧ mark a x ∧ mark a (s-x) := by
  have hn := A.npos
  have hn' : N q < L q := by unfold L;nlinarith
  have offle (e : ℕ) : offset n l e ≤ l := by unfold offset;split_ifs <;> omega
  by_contra! none
  have zeros (k : ℕ) (i : ℕ) (hi : i< w.width) (hr : rank w i=k) (hp : 0< k) :
      a ((s:ℤ)-(w.start+i : ℕ))=0 := by
    induction k using Nat.strong_induction_on generalizing i with
    | h k ih =>
      have cond := of_decide_eq_true (check_sound hw hi)
      rcases cond with hnz|hm|⟨hd,ho,hwid,hbelow⟩
      · omega
      · have hma : mark a (w.start+i) := (prefix_sound A pref _ (by omega)).trans hm
        have hz := none (w.start+i) (by omega) (by omega) hma
        have eq : ((s-(w.start+i):ℕ):ℤ) = (s:ℤ)-(w.start+i:ℕ) := by omega
        unfold mark at hz
        rw [eq] at hz
        have := DataBinary A ((s:ℤ)-(w.start+i:ℕ))
        omega
      · let d := side w i
        let b := i-offset n l d
        have hf := @force q n l a A eh el s (w.start+b) (by dsimp [b,d];omega) d hd
        have heq : w.start+b+offset n l d=w.start+i := by dsimp [b,d];omega
        rw [← heq]
        apply hf
        intro t ht ht'
        obtain ⟨hpos,hlt⟩ := hbelow ⟨t,ht⟩ ht'
        have hb : b+offset n l t< w.width := by dsimp [b,d];have := offle t;omega
        have H := ih (rank w (b+offset n l t)) (by simpa [b,d,hr] using hlt) _ hb rfl hpos
        simpa only [Nat.add_assoc] using H
  obtain ⟨j,hj,hj',haj⟩ := gap A (s+1-(w.start+l))
  let i : ℕ := (s:ℤ)-w.start-j |>.toNat
  have hei : (i:ℤ)=(s:ℤ)-w.start-j := by dsimp [i];omega
  have hi : i< l := by omega
  have hr := of_decide_eq_true (check_sound hl hi)
  have h0 := zeros _ i (by omega) rfl hr
  have he : (s:ℤ)-(w.start+i:ℕ)=j := by omega
  rw [he,haj] at h0
  omega

theorem two_windows {q n l word m : ℕ} {a : ℤ → ℕ} (A : Data q a) (eh : (n:ℤ)=N q)
    (el : (l:ℤ)=L q) (pref : prefixOK q word m)
    (w v : Window) (cw : windowOK n l word w) (cv : windowOK n l word v)
    (rw' : runOK l w) (rv' : runOK l v) (hw : l≤ w.width) (hv : l≤ v.width)
    (hsep : w.start+w.width≤ v.start) (hm : v.start+v.width≤ m) {s : ℕ}
    (large : 2*(v.start+v.width)≤ s) : Covered (mark a) s := by
  obtain ⟨x,_,hx,ax,ay⟩ := window_hit A eh el pref w cw rw' hw (by omega) (s:=s) (by omega)
  obtain ⟨u,hu,hu',au,av⟩ := window_hit A eh el pref v cv rv' hv hm (s:=s) (by omega)
  exact ⟨x,s-x,u,s-u,by omega,by omega,ax,ay,au,av,by omega,by omega⟩

end KucaSmall

namespace KucaSmall
open KucaLucas KucaShift KucaInitial

private def win5_0 : Window := ⟨0,111,4,0x1aaaaaaaaa6aaa66aa565211111999959995599454311111543218884488343411111654326541177232511111543216541165121611111,0xffffffffff800fffffffe00154fffff80055d50ffe0015454144800⟩
private def win5_1 : Window := ⟨114,91,4,0x141412121bccc8bcc811c43333121211111abb711b51214121212345987651a6443531212111113456198711981,0xccccffffc3bb88800ff0e1233001563a6a22000005414⟩
private def word5 : ℕ := 0x12008cad844011813080a9d065709f00e0d8474e982a202b4e9955006057c32aa0080af8465400001f0000f84007c0303e1195f
private def left5 : ℕ := 0x10020405482c65440c20400c204000204004004000100010308100308101520b1951030810030810001881030810020400040c20402c63040c20400400400810000010061030810000810010010000040c20400810000000082061840c20400001840c20400010001030810030810000010020400000400810005440c20400400400c20402c63040c204004004000100204000004008100008100100100100101520818610308100018b1030810010010000000040c20400020400400400400405485465440c20402c62c40c204004004000000010308100308100008100100101555555541041030b2cb208186103081000000
private def right5 : ℕ := 0x40cc2d658c30bb082061841030810c40c20c20810820572151ac11930b59830c2ea2081861040c204b5d62061840c308154c2cc2c84084062c40c20c21030c204108818b2040c20431030830820412081861030c20410412d040840610308104620810308108204b2081861040c20410840c30810421030c20465c62c40c20c25c42cc2c83084062040c20c20810840c30810421030c204310308308308308b2d64154153040c204b20c1881030830820410411881030810c40c20c20c20c22d6590590fcc2cc2c83083062040c20c208104106a2081861040c20431030830975965965aabadb2b40c30c2cb2081840c2041041

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem prefix5 : prefixOK 4 word5 410 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem pairs5 : sumsOK word5 85 325 6 left5 right5 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem window5_0 : windowOK 5 26 word5 win5_0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem run5_0 : runOK 26 win5_0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem window5_1 : windowOK 5 26 word5 win5_1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem run5_1 : runOK 26 win5_1 = true := by decide +kernel

theorem small5 {a : ℤ → ℕ} (A : Data 4 a) {s : ℕ} (hs : 4*d 4 < s) :
    Covered (mark a) s := by
  have hstart : 85 ≤ s := by norm_num [d] at hs; omega
  by_cases hcut : s < 410
  · exact sums_sound A prefix5 pairs5 hstart (by omega) hcut
  · exact two_windows A (n:=5) (l:=26) (by decide) (by decide) prefix5 win5_0 win5_1
      window5_0 window5_1 run5_0 run5_1 (by decide) (by decide) (by decide) (by decide)
      (by change 410 ≤ s; omega)

private def win9_0 : Window := ⟨0,667,5,0x6f7bdef7bde97bdef7bde8dbdef7bde8d6def7bde8d6b6f7bde8d6b5b7bde8a6b5aabde8a535aa55e89525a9524410842108421b5ad6b5ad365ad6b5ad3632d6b5ad363196b5ad36318cb5ad34b18c4dad34a58c4a6d34250c4250308421084210a50731483106b5ad6b592d75ad6b592d6bad6b592d6b5d6b59216b5a2b59210b5a11591d0759d0720421084210854941cc520c4a4a0e629021a5294a454a55294a454a52a94a44ea528f4a44e7528e7a44c7328c731421084210842941cc520c4152507314810a928398a1106739ce094a5339ce064a5269ce063252634e0531525314c108421084211316a4a0e62a98b525072956c5a9282148c62d490842194a4f2a1082ca4f295082964f214882148708421084210a507314831054c5a9283908b62d4940c836316a484210b58b5048310631710873909170c8338c8340421084210854941cc520c4a4a0e6290215b16a4a0431318b52421085ac5a84520c4e62c2129021834431184312421084210842941cc520c4152507314810a928398a11058c5a9210842d62d4120c4173161094810bd81104a1105410842108421,0xffffffffffffffffffffffffffffffffffff80000fffffffffffffffffffffffffffffffe000015554fffffffffffffffffffffffffff800005555d5550ffffffffffffffffffffffe000015554555415544ffffffffffffffffff800001555c555f155fc5500fffffffffffffe0000155541557c557f154005454fffffffff800005555d5550155fc550015d5c5050ffffe00001555455541554415400545414140444480000⟩
private def win9_1 : Window := ⟨706,380,5,0xdef509028a8ae108441404214214a0958c1a02a294ac0f7a10f425087a1e84210b02108694a0454ef6d6a0481a56d6a04612d0360844119c21088e108823104e14842458441104812045ce738110443e738e6b161273819cd410ced5acd2118661a85011048c620e141cc25a4a61a0810a8811044318c6108421104411ef7b084210937b0b9ab294d70864a210720d0291844108421104211b126085050854509423088240882208822088649460f739fad4a306b430c4e516318c8be6e52c2b0b9cd4194a399ac394293142b3108320c8328c2208822088210842108423216728c1e186693946010c6b49ca21,0x3f33fc0cc0ff3ff3ff3c330cc0300fcfffccefccf300b00c214cc3ccccc3fcccfd583cf83bf88cc8ce9c5e9b98188bb800883f000f16a20eab32880080a60606321233330055a3d5a095aa26a22aaaaaa2a2a6a6a222200000055425540554⟩
private def word9 : ℕ := 0xcb846ad71436ac998559d51665545c50b1e80f1814fe01d13964d089884070406800608358a2860824042e3069cd2b3ae6941b1414b0e884d72082ea89455f504c4ace19158b445c505a1050dc008a855d11113ba4525945654d79445111121118414d4940dbb445cd08ea965556bd8115d515b744c434a231aa251514161149466141ad1147c40e2875c20826b5ef101414b4e6959550500446055504006507d43e2030297dc332aaaa00008000a0008800aaff80406050784466554000000000000000001ff0000000000000000ff80400000000000007fc0003000000000003fe0101814000000001ff00000000f0000000ff80400000784400007fc00030003c0033003fe01018141e1119955ff
private def left9 : ℕ := 0x20100010000000403020100030201000001000100010000010001000000030201000100040302010000010000010001000100000201000201000002010000040302010001000100010000020100000001000100010003020100010000020100000201000100010001000100030201000100000003020100010004030201000100000302010000000001000706050403020100000000030201000006050403020100010002010000000000000008070605040302010000000100030201000201000000020100010000020100020100000100040302010003020100020100000302010004030201000706050403020100000005040302010007060504030201000001000c0c0a0a080706050403020100000504030201000504030201000001000100000302010001000302010001000403020100000504030201000504030201000201000706050403020100040302010001000000030201000005040302010000010002010000000201000001000201000100010000020100000001000100000002010000010002010001000504030201000001000003020100010005040302010001000201000100000403020100000001000302010004030201000201000001000100000002010005040302010005040302010001000000010001000100030201000201000100030201000100010001000000000001000100050403020100020100000302010002010001000100000201000000040302010000020100030201000100010000030201000100000100030201000302010001000000030201000100050403020100010000010004030201000504030201000100040302010000010000000a1808070605040302010003020100010001000403020100010001000100000001000302010003020100030201000302010002010000000100000001000201000302010001000201000201000100000201000100030201000100010000020100010001000201000001000100000000020100010003020100030201000100030201000302010003020100030201000201000403020100030201000302010000040302010005040302010001000201000001000100020100020100010006050403020100000100000100000001000001000302010003020100010000000201000001000403020100030201000000010001000100020100010000020100010001000100010001000100000100010000000001000006050403020100030201000100010000000100010001000302010001000100000100000100000001000302010002010000030201000403020100000100020100010003020100030201000003020100000100010001000302010002010001000302010001000100030201000100050403020100010000040302010003020100010002010002010001000302010000020100000403020100010005040302010000010001000001000302010003020100010003020100000000000302010006050403020100000003020100010004030201000000010001000000040302010005040302010005040302010002010000010001000001000100000000010000000003020100070605040302010001000504030201000100020100010000010002010000000201000001000201000100010000020100010001000100010005040302010001004908070605040302010003020100030201000006050403020100010001000100010001000504030201000c0a0a0807060504030201000002010001000504030201000000000001000100040302010000000000030201000706050403020100000605040302010001000201000100000000000100000004030201000002010000020100010001000100010001000100010001004910490e490c490a49080706050403020100370e370c370a370807060504030201000100250c250a2508070605040302010003020100130a130807060504030201000100010001000100000000000000000008070605040302010007060504030201000006050403020100010005040302010000000004030201000302010003020100000201000002010001000100010001004949494949494949494040404040404040383737373737373730302e2e2e2e2e2e2827262525252525202020201c1c1c1c181717171413131310100e0e0c0c0a0a08070605040302010000000000000000
private def right9 : ℕ := 0x10304030202010105080706050404030201020302030202010203020201010405040302060505040302010202010203020302020103050403030201030302010506050403020302030202010303020101020302030205040504030202010303020103040302030203020302050405040302020101040504030206050605040302020104040302010101020a080807060504030201010104040302010708070605040302040303020101010101010a0a08070605040302010102050406050403030201010304030202010305040303020102060508070605040605040303020104080706050c0c0a0a08080706050403020101060e0c0c0a0a080807060504030201020e0e13181710180807060504030201060c0a0a0807060605040302010203020201040504030205040504030206050504030201060e0a0c0807060807060504030a0e080c0e0a0c0807060506050403020201010404030201060605040302010204030302010103030201020403040302030202010303020101020302020101030302010204030403020706060504030201020201040504030207060706050403020403040302020105050403020101020504080706050706050403030201020302020101030807060e0a0c0807060706050403020201010203020302050406050403040302050405040302030203020201010101020302070608070605040303020104060504030403020302020103030201010505040302010306050405040302030202010405040302020102050407060504050403020201010405040302070607060504030202010206050a100807060706050403020605050403020102020101130e1c0c140a140807060504050403020302060506050403020302030202010102050407060504070605040706050406050403030201010202010102040306050405040302040305040304030202010304030205040504030203020201030403020302040303020102030202010101030403020504070605040504030205040706050407060504070605040605040307060508070605040706050404030201050a0e0807060706050403020403030201020302040305040304030208070706050403020102020102020101020201020504070605040504030202010103030201020605080706050404030201010203020302040304030202010304030203020302030203020302020102030202010101020201070a0e0807060504050403020302020101020302030205040504030203020201020201020201010205040605040303020104080706050504030201020403040302050407060504040302010404030201020302030205040605040304030205040504030203020504050403020706070605040302020105080706050405040302040305040304030205040403020103030201050605040302070606050403020102030202010205040706050405040302050404030201010101040a0a0807070605040302010104050403020605050403020101020302020101050a130807060e0a0c080706080706050403030201020302020102030202010101020201010104130a13081408070605040302070607060504030204030403020201020403030201010303020102040304030203020201030403020302030203020706070605040302130a4e0c100a0e080706050407060504040302010708070605040302030203020302030207061710100e0e0c170e170c080706050403020103040302070606050403020101010102030206050504030201010101040c0a0a0808070605040302010708070605040302040304030202010101010202010105050403020103030201030403020302030203020302030203020302134a4a204a204a1c4a1cdb1817181714131413103810380e380c380a1708070605040302130e2610260e260c170a170807060504130e130c140c140a10080706050403020302030203020201010101010101019210100e0e0c0c0a0a080807060504030201070807060504030207060605040302010101050807060504070605040403020103030201030403020302030203024b4a4a4a4a4a4a4a4a4a929a99989796959493403838383838383837373030303030302e2827262626262625252525202020201c18181817141414131310100e0e0c0c0a080706050403020101010101010101

set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem prefix9 : prefixOK 8 word9 2172 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem pairs9 : sumsOK word9 585 1587 8 left9 right9 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem window9_0 : windowOK 9 82 word9 win9_0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem run9_0 : runOK 82 win9_0 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem window9_1 : windowOK 9 82 word9 win9_1 = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 20000000 in
private theorem run9_1 : runOK 82 win9_1 = true := by decide +kernel

theorem small9 {a : ℤ → ℕ} (A : Data 8 a) {s : ℕ} (hs : 8*d 8 < s) :
    Covered (mark a) s := by
  have hstart : 585 ≤ s := by norm_num [d] at hs; omega
  by_cases hcut : s < 2172
  · exact sums_sound A prefix9 pairs9 hstart (by omega) hcut
  · exact two_windows A (n:=9) (l:=82) (by decide) (by decide) prefix9 win9_0 win9_1
      window9_0 window9_1 run9_0 run9_1 (by decide) (by decide) (by decide) (by decide)
      (by change 2172 ≤ s; omega)

end KucaSmall

namespace Kuca
open OMA.S_arxiv_1804_09594

def IsPair (P : ℕ → Prop) (x : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ≤ p.2 ∧ p.1 + p.2 = x ∧ p.1 < x ∧ p.2 < x ∧ P p.1 ∧ P p.2

theorem reps_eq_one {P : ℕ → Prop} {x : ℕ} {l : List ℕ}
    (hnd : l.Nodup) (hm : ∀ z, z ∈ l ↔ z < x ∧ P z) :
    reps l x = 1 ↔ ∃! p, IsPair P x p := by
  classical
  let pairs := (l ×ˢ l).filter (fun p => decide (p.1 ≤ p.2 ∧ p.1 + p.2 = x))
  have hmem (p : ℕ × ℕ) : p ∈ pairs.toFinset ↔ IsPair P x p := by
    rcases p with ⟨u,v⟩
    simp only [List.mem_toFinset, pairs, List.mem_filter, List.mem_product,
      decide_eq_true_eq, hm, IsPair]
    tauto
  change pairs.length = 1 ↔ _
  rw [← List.toFinset_card_of_nodup ((hnd.product hnd).filter _), Finset.card_eq_one]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hp, hu⟩ := Finset.eq_singleton_iff_unique_mem.mp hp
    exact ⟨p, (hmem p).mp hp, fun z hz => hu z ((hmem z).mpr hz)⟩
  · rintro ⟨p, hp, hu⟩
    exact ⟨p, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨(hmem p).mpr hp, fun z hz => hu z ((hmem z).mp hz)⟩⟩

theorem scan_eq {P : ℕ → Prop} {a b : ℕ}
    (hr : ∀ x, P x ↔ x = a ∨ x = b ∨ (b < x ∧ ∃! p, IsPair P x p)) :
    ∀ x, InV a b x ↔ P x := by
  let before (x : ℕ) := (List.range x).foldl (step a b) []
  have inv (x : ℕ) : (before x).Nodup ∧ ∀ z, z ∈ before x ↔ z < x ∧ P z := by
    induction x with
    | zero => simp [before]
    | succ x ih =>
      rcases ih with ⟨hnd,hm⟩
      have hstep : before (x+1) = step a b (before x) x := by
        simp [before, List.range_succ, List.foldl_append]
      rw [hstep]
      have htest : (x = a ∨ x = b ∨ b < x ∧ reps (before x) x = 1) ↔ P x := by
        rw [reps_eq_one hnd hm, ← hr]
      unfold step
      split_ifs with he
      · refine ⟨List.nodup_append.mpr ⟨hnd, by simp, ?_⟩, ?_⟩
        · intro z hz w hw
          obtain rfl : w = x := by simpa using hw
          exact ne_of_lt ((hm z).mp hz).1
        · intro z
          simp only [List.mem_append, List.mem_singleton, hm]
          have hPx := htest.mp he
          constructor
          · rintro (⟨hlt, hp⟩ | rfl)
            · exact ⟨by omega, hp⟩
            · exact ⟨by omega, hPx⟩
          · rintro ⟨hlt, hp⟩
            by_cases heq : z = x
            · exact Or.inr heq
            · exact Or.inl ⟨by omega, hp⟩
      · refine ⟨hnd, fun z => ?_⟩
        rw [hm]
        have hn : ¬ P x := fun h => he (htest.mpr h)
        constructor
        · rintro ⟨hlt, hp⟩
          exact ⟨by omega, hp⟩
        · rintro ⟨hlt, hp⟩
          have : z ≠ x := fun h => hn (h ▸ hp)
          exact ⟨by omega, hp⟩
  intro x
  change x ∈ before (x+1) ↔ P x
  simp [(inv (x+1)).2]

end Kuca

namespace Kuca

def lag (n : ℕ) (j : Fin 3) : ℕ := ![1,n,n^2+1] j

def Cand (n : ℕ) (a : ℤ → ℕ) (x : ℕ) : Prop :=
  (∃ j : Fin 3, x = 2 * lag n j) ∨ ∃ i : ℕ, x = n + 2*i ∧ a i = 1

def sorted (u v : ℕ) : ℕ × ℕ := (min u v,max u v)

theorem sorted_mem {P : ℕ → Prop} {x u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (he : u + v = x) (hpu : P u) (hpv : P v) : IsPair P x (sorted u v) := by
  by_cases h : u ≤ v
  · simp [IsPair, sorted, min_eq_left h, max_eq_right h, h, he, hpu, hpv]
    omega
  · have h' : v ≤ u := by omega
    simp [IsPair, sorted, min_eq_right h', max_eq_left h', h', Nat.add_comm v u, he, hpu, hpv]
    omega

theorem sorted_even_inj {e f u v : ℕ} (hu : Odd u) (hv : Odd v)
    (he : sorted (2*e) u = sorted (2*f) v) : e = f := by
  obtain ⟨u',hu⟩ := hu
  obtain ⟨v',hv⟩ := hv
  unfold sorted at he
  simp only [Prod.mk.injEq] at he
  omega

theorem lag_injective {n : ℕ} (hn : 5 ≤ n) : Function.Injective (lag n) := by
  have hn' : n < n^2+1 := by nlinarith [Nat.mul_self_le_mul_self hn]
  intro j k h
  fin_cases j <;> fin_cases k <;> norm_num [lag] at h ⊢ <;> omega

theorem lag_pos {n : ℕ} (hn : 5 ≤ n) (j : Fin 3) : 0 < lag n j := by
  fin_cases j <;> simp [lag] <;> omega

def active (n : ℕ) (a : ℤ → ℕ) (i : ℕ) (j : Fin 3) : Prop :=
  a ((i : ℤ) - (lag n j : ℤ)) = 1

def oddPair (n i : ℕ) (j : Fin 3) :=
  sorted (2*lag n j) (n+2*i-2*lag n j)

theorem active_pair {n i : ℕ} {a : ℤ → ℕ} (hn : 5 ≤ n)
    (neg : ∀ z, z < 0 → a z = 0) {j : Fin 3} (hj : active n a i j) :
    IsPair (Cand n a) (n+2*i) (oddPair n i j) := by
  have hge : lag n j ≤ i := by
    by_contra! h
    have hz := neg ((i : ℤ)-(lag n j : ℤ)) (by omega)
    unfold active at hj
    omega
  have hei : (↑(i-lag n j) : ℤ) = (i : ℤ)-(lag n j : ℤ) := by omega
  have hpos := lag_pos hn j
  refine sorted_mem (by omega) (by omega) (by omega) (Or.inl ⟨j,rfl⟩) ?_
  exact Or.inr ⟨i-lag n j, by omega, by rw [hei]; exact hj⟩

theorem oddPair_active_inj {n i : ℕ} {a : ℤ → ℕ} (hn : 5 ≤ n) (hodd : Odd n)
    (neg : ∀ z, z < 0 → a z = 0) {j k : Fin 3} (hj : active n a i j)
    (hk : active n a i k) (he : oddPair n i j = oddPair n i k) : j = k := by
  obtain ⟨t, ht⟩ := hodd
  apply lag_injective hn
  apply sorted_even_inj (e := lag n j) (f := lag n k) (u := n+2*i-2*lag n j)
    (v := n+2*i-2*lag n k) _ _ he
  all_goals
    first
    | have : lag n j ≤ i := by
        by_contra! h
        have hz := neg ((i : ℤ)-(lag n j : ℤ)) (by omega)
        unfold active at hj
        omega
      exact ⟨t+(i-lag n j), by omega⟩
    | have : lag n k ≤ i := by
        by_contra! h
        have hz := neg ((i : ℤ)-(lag n k : ℤ)) (by omega)
        unfold active at hk
        omega
      exact ⟨t+(i-lag n k), by omega⟩

theorem oddPair_all {n i : ℕ} {a : ℤ → ℕ} (hodd : Odd n) {p : ℕ × ℕ}
    (hp : IsPair (Cand n a) (n+2*i) p) :
    ∃ j, active n a i j ∧ p = oddPair n i j := by
  obtain ⟨u,v⟩ := p
  obtain ⟨hle,hs,_,_,hu,hv⟩ := hp
  change u ≤ v at hle
  change u+v = _ at hs
  rcases hodd with ⟨t, ht⟩
  rcases hu with ⟨j,he⟩ | ⟨b,hb,hab⟩ <;> rcases hv with ⟨k,hf⟩ | ⟨c,hc,hac⟩
  · change u = _ at he
    change v = _ at hf
    omega
  · change u = _ at he
    change v = _ at hc
    have hi : (i:ℤ)-(lag n j:ℤ) = c := by omega
    refine ⟨j, by simpa [active, hi] using hac, ?_⟩
    have hv' : n+2*i-2*lag n j = v := by omega
    unfold oddPair
    rw [hv', ← he]
    simp [sorted, hle]
  · change u = _ at hb
    change v = _ at hf
    have hi : (i:ℤ)-(lag n k:ℤ) = b := by omega
    refine ⟨k, by simpa [active, hi] using hab, ?_⟩
    have hu' : n+2*i-2*lag n k = u := by omega
    unfold oddPair
    rw [hu', ← hf]
    simp [sorted, min_eq_right hle, max_eq_left hle]
  · change u = _ at hb
    change v = _ at hc
    omega

theorem odd_unique {n i : ℕ} {a : ℤ → ℕ} (hn : 5 ≤ n) (hodd : Odd n)
    (neg : ∀ z, z < 0 → a z = 0) :
    (∃! p, IsPair (Cand n a) (n+2*i) p) ↔ ∃! j, active n a i j := by
  constructor
  · rintro ⟨p,hp,hu⟩
    obtain ⟨j,hj,rfl⟩ := oddPair_all hodd hp
    exact ⟨j,hj,fun k hk => oddPair_active_inj hn hodd neg hk hj (hu _ (active_pair hn neg hk))⟩
  · rintro ⟨j,hj,hu⟩
    refine ⟨_,active_pair hn neg hj,fun p hp => ?_⟩
    obtain ⟨k,hk,rfl⟩ := oddPair_all hodd hp
    rw [hu k hk]

end Kuca

namespace Kuca

/-- The companion odd bits, with zero values at negative indices. -/
def raw (n : ℕ) (i : ℕ) : ℕ :=
  if h : i = 0 then 1 else
    KucaLucas.one (raw n (i-1))
      (if 0 < n ∧ n ≤ i then raw n (i-n) else 0)
      (if n^2+1 ≤ i then raw n (i-(n^2+1)) else 0)
termination_by i
decreasing_by all_goals omega

def seq (n : ℕ) (z : ℤ) := if z < 0 then 0 else raw n z.toNat

theorem seq_seed (n : ℕ) : seq n 0 = 1 := by simp [seq, raw]

theorem seq_neg {n : ℕ} {z : ℤ} (hz : z < 0) : seq n z = 0 := by simp [seq,hz]

theorem seq_step {n : ℕ} (hn : 0 < n) {z : ℤ} (hz : 0 < z) :
    seq n z = KucaLucas.one (seq n (z-1)) (seq n (z-(n:ℤ))) (seq n (z-((n:ℤ)^2+1))) := by
  lift z to ℕ using (by omega : 0 ≤ z) with i hi
  have h₁ : ¬(↑i-1:ℤ) < 0 := by omega
  have hi : i ≠ 0 := by omega
  have hL : ((n^2+1 : ℕ):ℤ) = (n:ℤ)^2+1 := by norm_cast
  rw [← hL]
  simp only [seq, Int.natCast_nonneg, not_false_eq_true, Int.toNat_natCast, ite_false]
  rw [raw.eq_def]
  simp only [hi, ↓reduceDIte, h₁, ite_false, hn, true_and]
  have conv (u : ℕ) : ((i : ℤ) - u).toNat = i-u := by omega
  have conv1 : ((i : ℤ)-1).toNat=i-1 := by omega
  rw [conv1,conv n,conv (n^2+1)]
  have nn : ¬ ((i:ℤ)< 0) := by omega
  have cn : ((i:ℤ)-(n:ℤ)< 0) ↔ ¬ (n ≤ i) := by omega
  have cl : ((i:ℤ)-((n^2+1:ℕ):ℤ)< 0) ↔ ¬ (n^2+1 ≤ i) := by omega
  rw [if_neg nn]
  by_cases h : n ≤ i <;> by_cases h' : n^2+1 ≤ i <;> simp only [cn,cl,h,h',not_true_eq_false,not_false_eq_true,ite_true,ite_false]

theorem seq_binary {n : ℕ} (hn : 0< n) (z : ℤ) : seq n z ≤ 1 := by
  rcases lt_trichotomy z 0 with h|h|h
  · simp [seq_neg h]
  · simp [h,seq_seed]
  · rw [seq_step hn h]
    unfold KucaLucas.one
    split <;> omega

theorem unique_fin3 (f : Fin 3 → ℕ) (hb : ∀ j, f j ≤ 1) :
    (∃! j, f j = 1) ↔ f 0+f 1+f 2=1 := by
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  constructor
  · rintro ⟨j,hj,hu⟩
    have hu0 := hu 0
    have hu1 := hu 1
    have hu2 := hu 2
    fin_cases j <;> simp at * <;> omega
  · intro hs
    by_cases h : f 0 = 1
    · refine ⟨0,h,?_⟩
      intro b hb
      fin_cases b <;> simp_all <;> omega
    · by_cases h' : f 1 = 1
      · refine ⟨1,h',?_⟩
        intro b hb
        fin_cases b <;> simp_all <;> omega
      · refine ⟨2, by omega, ?_⟩
        intro b hb
        fin_cases b <;> simp_all

theorem odd_cand_iff {n i : ℕ} {a : ℤ → ℕ} (hn : 5 ≤ n) (hodd : Odd n)
    (hb : ∀ z, a z ≤ 1) (neg : ∀ z, z < 0 → a z = 0) (hi : 0 < i)
    (step : ∀ z : ℤ, 0< z → a z=KucaLucas.one (a (z-1)) (a (z-n)) (a (z-((n:ℤ)^2+1)))) :
    Cand n a (n+2*i) ↔ ∃! p, IsPair (Cand n a) (n+2*i) p := by
  rw [odd_unique hn hodd neg]
  change _ ↔ ∃! j : Fin 3, (fun j => a ((i:ℤ)-(lag n j:ℤ))) j = 1
  rw [unique_fin3 _ (fun j => hb _)]
  have hr := step (i:ℤ) (by omega)
  change Cand n a (n+2*i) ↔ a ((i:ℤ)-(1:ℕ))+a ((i:ℤ)-(n:ℤ))+a ((i:ℤ)-((n^2+1:ℕ):ℤ))=1
  push_cast
  have hbit : a i=1 ↔
      a ((i:ℤ)-1)+a ((i:ℤ)-n)+a ((i:ℤ)-((n:ℤ)^2+1)) = 1 := by
    rw [hr]
    simp [KucaLucas.one]
  rw [← hbit]
  constructor
  · rintro (⟨j,he⟩|⟨b,hb',ha⟩)
    · obtain ⟨t,ht⟩ := hodd
      omega
    · have : i=b := by omega
      simpa [this] using ha
  · intro h
    exact Or.inr ⟨i,rfl,h⟩

end Kuca

namespace Kuca

theorem cand_even {n x : ℕ} {a : ℤ → ℕ} (ho : Odd n) (hv : Even x) :
    Cand n a x ↔ x = 2 ∨ x = 2*n ∨ x = 2*(n^2+1) := by
  rcases ho with ⟨t,ht⟩
  rcases hv with ⟨u,hu⟩
  constructor
  · rintro (⟨j,h⟩|⟨i,h,_⟩)
    · fin_cases j <;> norm_num [lag] at h <;> tauto
    · omega
  · rintro (h|h|h)
    · exact Or.inl ⟨0,by simpa [lag] using h⟩
    · exact Or.inl ⟨1,by simpa [lag] using h⟩
    · exact Or.inl ⟨2,by simpa [lag] using h⟩

theorem even_pair_cases {n x : ℕ} {a : ℤ → ℕ} {p : ℕ×ℕ} (ho : Odd n) (hx : Even x)
    (hp : IsPair (Cand n a) x p) :
    (∃ j k, p.1=2*lag n j ∧ p.2=2*lag n k) ∨
    ∃ i j : ℕ, p.1=n+2*i ∧ p.2=n+2*j ∧ a i=1 ∧ a j=1 := by
  rcases ho with ⟨t,ht⟩
  rcases hx with ⟨y,hy⟩
  rcases hp with ⟨_,hs,_,_,h1,h2⟩
  rcases h1 with ⟨j,hj⟩|⟨i,hi,hai⟩ <;> rcases h2 with ⟨k,hk⟩|⟨k,hk,hak⟩
  · exact Or.inl ⟨_,_,hj,hk⟩
  · omega
  · omega
  · exact Or.inr ⟨_,_,hi,hk,hai,hak⟩

theorem no_even_even {n x : ℕ} (hn : 5≤ n)
    (hx : (n< x ∧ x≤ 2*n) ∨ x=2*(n^2+1)) (j k : Fin 3) :
    2*lag n j+2*lag n k≠x := by
  have hhigh : 2*n< n^2+1 := by nlinarith [Nat.mul_self_le_mul_self hn]
  fin_cases j <;> fin_cases k <;> norm_num [lag] <;> omega

theorem short_even {n x : ℕ} {a : ℤ → ℕ} (hn : 5≤ n) (ho : Odd n) (hx : Even x)
    (hl : n< x) (hu : x< 2*n) : ¬∃ p, IsPair (Cand n a) x p := by
  rintro ⟨p,hp⟩
  have hs := hp.2.1
  rcases even_pair_cases ho hx hp with ⟨j,k,he,hf⟩|⟨i,j,he,hf,_,_⟩
  · exact no_even_even hn (Or.inl ⟨hl,by omega⟩) j k (by omega)
  · omega

theorem odd_sorted_mark {n s i j : ℕ} {a : ℤ → ℕ} (hn : 0< n)
    (he : i+j=s) (hi : a i=1) (hj : a j=1) :
    IsPair (Cand n a) (2*n+2*s) (sorted (n+2*i) (n+2*j)) :=
  sorted_mem (by omega) (by omega) (by omega) (Or.inr ⟨i,rfl,hi⟩) (Or.inr ⟨j,rfl,hj⟩)

theorem covered_nonunique {n s : ℕ} {a : ℤ → ℕ} (hn : 0< n)
    (hc : KucaInitial.Covered (KucaInitial.mark a) s) :
    ¬∃! p, IsPair (Cand n a) (2*n+2*s) p := by
  obtain ⟨i,j,u,v,h1,h2,hi,hj,hu,hv,hne,hne'⟩ := hc
  rintro ⟨p,_,uniq⟩
  have h := (uniq _ (odd_sorted_mark hn h1 hi hj)).trans (uniq _ (odd_sorted_mark hn h2 hu hv)).symm
  unfold sorted at h
  simp only [Prod.mk.injEq] at h
  omega

theorem one_nonunique {n : ℕ} {a : ℤ → ℕ} (hn : 5≤ n) (h0 : a 0=1) (h1 : a 1=1) :
    ¬∃! p, IsPair (Cand n a) (2*n+2*1) p := by
  rintro ⟨p,_,hu⟩
  have hodd := odd_sorted_mark (a:=a) (n:=n) (s:=1) (i:=0) (j:=1) (by omega) rfl h0 h1
  have c2 : Cand n a 2 := Or.inl ⟨0,by simp [lag]⟩
  have c2n : Cand n a (2*n) := Or.inl ⟨1,by simp [lag]⟩
  have he := sorted_mem (x:=2*n+2*1) (by decide : 0< 2) (by omega : 0< 2*n) (by omega) c2 c2n
  have eq := congrArg Prod.fst ((hu _ he).trans (hu _ hodd).symm)
  simp [sorted] at eq
  omega

theorem unique_boundary {n s : ℕ} {a : ℤ → ℕ} (hn : 5≤ n) (ho : Odd n)
    (he : s=0 ∨ 2*n+2*s=2*(n^2+1)) (h0 : a 0=1) (hm : a (s:ℤ)=1)
    (hb : ∀ i j : ℕ, i+j=s → a i=1 → a j=1 → i=0 ∨ j=0) :
    ∃! p, IsPair (Cand n a) (2*n+2*s) p := by
  have hep : IsPair (Cand n a) (2*n+2*s) (sorted (n+2*0) (n+2*s)) :=
    odd_sorted_mark (by omega) (by omega) h0 hm
  refine ⟨_,hep,?_⟩
  rintro ⟨u,v⟩ hp
  have hle : u≤ v := hp.1
  have hs : u+v=2*n+2*s := hp.2.1
  rcases even_pair_cases ho (show Even (2*n+2*s) from ⟨n+s,by omega⟩) hp with
    ⟨j,k,hu,hv⟩|⟨i,j,hu,hv,hi,hj⟩
  · change u = _ at hu
    change v = _ at hv
    exact (no_even_even hn (x:=2*n+2*s) (by rcases he with he|he <;> omega) j k (by omega)).elim
  · change u = _ at hu
    change v = _ at hv
    have hsum : i+j=s := by omega
    have hzero := hb i j hsum hi hj
    simp [sorted,show n≤ n+2*s by omega]
    omega

end Kuca

namespace Kuca
open OMA.S_arxiv_1804_09594

theorem greedy_of_cover {q n : ℕ} (hnq : n=q+1) (ho : Odd n) {a : ℤ → ℕ}
    (A : KucaShift.Data q a) (hb : ∀ z, a z ≤ 1)
    (cover : ∀ s, 2 ≤ s → s ≠ KucaInitial.d q → KucaInitial.Covered (KucaInitial.mark a) s) :
    {x : ℕ | InV 2 n x ∧ Even x} = {2, 2*n, 2*n^2+2} := by
  have hq := A.qlarge
  have hn : 5 ≤ n := by omega
  have hL : n+KucaInitial.d q=n^2+1 := by simp [KucaInitial.d,hnq]; ring
  have hD : 0< KucaInitial.d q := by simp [KucaInitial.d]
  have npos : 0< n := by omega
  have hLgt : n< n^2+1 := by omega
  obtain ⟨k,hk⟩ := A.dyadic
  obtain ⟨h0,hmarkD,uniqD⟩ := KucaInitial.boundary_unique hk (by omega) A.prefixBlock
  have hmark1 : a 1 = 1 := by
    have t := KucaInitial.header (A.prefixBlock 0 (by omega)) (r:=1) (by omega)
    simpa [KucaInitial.mark] using t
  have c2 : Cand n a 2 := Or.inl ⟨0,by simp [lag]⟩
  have cn : Cand n a n := Or.inr ⟨0,by omega,by simpa using A.seed⟩
  have neg := A.neg
  have step (z : ℤ) (hz : 0< z) :
      a z=KucaLucas.one (a (z-1)) (a (z-n)) (a (z-((n:ℤ)^2+1))) := by
    simpa [hnq,KucaShift.N,KucaShift.L] using A.step z hz
  have hrec (x : ℕ) : Cand n a x ↔ x=2 ∨ x=n ∨ (n< x ∧ ∃! p, IsPair (Cand n a) x p) := by
    by_cases hsmall : x≤ n
    · have hnlt : ¬n< x := by omega
      simp only [hnlt,false_and,or_false]
      constructor
      · rintro (⟨j,he⟩|⟨i,hi,_⟩)
        · fin_cases j <;> norm_num [lag] at he <;> omega
        · omega
      · rintro (rfl|rfl)
        · exact c2
        · exact cn
    · have hnx : n< x := by omega
      have hne : x≠2 := by omega
      have hnn : x≠n := by omega
      simp only [hne,hnn,hnx,false_or,true_and]
      rcases Nat.even_or_odd x with heven | hodd
      · rw [cand_even ho heven]
        by_cases h2 : x< 2*n
        · have hnone := short_even (a:=a) hn ho heven hnx h2
          constructor
          · omega
          · rintro ⟨p,hp,_⟩
            exact (hnone ⟨p,hp⟩).elim
        · rcases heven with ⟨z,hz⟩
          let s:=z-n
          have hxs : x=2*n+2*s := by dsimp [s]; omega
          rw [hxs]
          by_cases hzero : s=0
          · subst s
            have ez : z-n=0 := hzero
            have eu : ∃! p, IsPair (Cand n a) (2*n+2*(z-n)) p :=
              unique_boundary hn ho (Or.inl ez) A.seed (by simpa [ez] using A.seed)
                (fun i j hij _ _ => by omega)
            exact ⟨fun _ => eu,fun _ => by omega⟩
          · by_cases hd : s=KucaInitial.d q
            · have heq : 2*n+2*s=2*(n^2+1) := by omega
              have eu := unique_boundary hn ho (Or.inr heq) A.seed (hd ▸ hmarkD)
                (fun i j hij hi hj => uniqD i j (hij.trans hd) hi hj)
              exact ⟨fun _ => eu,fun _ => Or.inr (Or.inr heq)⟩
            · have hnone : ¬∃! p, IsPair (Cand n a) (2*n+2*s) p := by
                by_cases h1 : s=1
                · rw [h1]
                  exact one_nonunique hn A.seed hmark1
                · exact covered_nonunique npos (cover s (by omega) hd)
              constructor
              · omega
              · intro h
                exact (hnone h).elim
      · obtain ⟨u,hu⟩ := hodd
        obtain ⟨v,hv⟩ := ho
        let i:=u-v
        have hi : 0 < i := by dsimp [i]; omega
        have hx : x=n+2*i := by dsimp [i]; omega
        rw [hx]
        exact odd_cand_iff hn ⟨v,hv⟩ hb neg hi step
  ext x
  change (InV 2 n x ∧ Even x) ↔ x∈({2,2*n,2*n^2+2}:Set ℕ)
  rw [scan_eq hrec]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hm,he⟩
    have h := (cand_even ho he).mp hm
    omega
  · intro h
    have he : Even x := by
      rcases h with h|h|h
      · exact ⟨1,by omega⟩
      · exact ⟨n,by omega⟩
      · exact ⟨n^2+1,by omega⟩
    exact ⟨(cand_even ho he).mpr (by omega),he⟩

theorem greedy_from_signed_bits {q n : ℕ} (hnq : n=q+1) (ho : Odd n)
    (hq : 4≤ q) (hpow : ∃ k : ℕ, q=2^k)
    (allCover : ∀ a : ℤ → ℕ, KucaShift.Data q a → ∀ s, 2 ≤ s → s ≠ KucaInitial.d q →
        KucaInitial.Covered (KucaInitial.mark a) s) :
    {x : ℕ | InV 2 n x ∧ Even x} = {2,2*n,2*n^2+2} := by
  have hn : 0< n := by omega
  have A : KucaShift.Data q (seq n) :=
    ⟨hq,hpow,seq_seed n,fun _ h => seq_neg h,fun z hz => by
      simpa [hnq,KucaShift.N,KucaShift.L] using seq_step (n:=n) hn hz⟩
  exact greedy_of_cover hnq ho A (seq_binary hn) (allCover _ A)

end Kuca

theorem OMA.solution : type_of% @OMA.S_arxiv_1804_09594.main := by
  intro n ho hn hk
  let q := n-1
  have hq : 4≤ q := by dsimp [q]; omega
  apply Kuca.greedy_from_signed_bits (q:=q) (by dsimp [q]; omega) ho hq hk
  intro a A s hs hd
  by_cases hl : 16≤ q
  · exact KucaLate.all_cover A hl hs hd
  · obtain ⟨k,hk'⟩ := hk
    change q=2^k at hk'
    have hkl : k< 4 := by
      by_contra! h
      have hm : 2^4≤ (2:ℕ)^k := Nat.pow_le_pow_right (by decide) h
      omega
    interval_cases k <;> norm_num at hk' <;> first | omega | skip
    all_goals
      first
      | have eq : q=4 := by omega
        revert A hs hd
        rw [eq]
        intro A hs hd
        by_cases hf : 4*KucaInitial.d 4< s
        · exact KucaSmall.small5 A hf
        · apply KucaInitial.initial_cover A hs hd
          simp [KucaInitial.d] at * <;> omega
      | have eq : q=8 := by omega
        revert A hs hd
        rw [eq]
        intro A hs hd
        by_cases hf : 8*KucaInitial.d 8< s
        · exact KucaSmall.small9 A hf
        · apply KucaInitial.initial_cover A hs hd
          simp [KucaInitial.d] at * <;> omega
