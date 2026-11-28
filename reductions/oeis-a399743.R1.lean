import OMAStatements.S_oeis_a399743

/-!
# Signed representations of Fibonacci numbers in a row of Pascal's triangle

The modulus-five representation of Dresden and Li has exactly ceil(2n/5)
entries. For every fixed period, each matching signed pattern on any sufficiently large
row uses at least floor((2*n+4)/5) slots. The modulus-five pattern attains
that count exactly. The chosen pattern may vary between rows.
The proof uses the positive semidefinite centered Pascal operator on a finite cycle.
The minimum number of occupied positions is unbounded as n varies.

All rows from 0 to 146 satisfy Huber's bound by explicit certificates.
The remaining hypotheses are exact integer-relation problems on even half-rows.
H1 changes the even reference vector by a zero-weight vector. H2 changes the
odd reference vector by a vector whose adjacent sums have zero even-row weight.
The inverse implication proves necessity. An exact order-independent search
with gcd and magnitude pruning is also certified.

Sources: https://oeis.org/A399743 and
https://cs.uwaterloo.ca/journals/JIS/VOL26/Dresden/dresden26.html
-/
namespace Fib743

open Finset

theorem fold_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (n+1), f i =
      ∑ k ∈ range (n/2+1), (f k + if 2*k=n then 0 else f (n-k)) := by
  induction n using Nat.twoStepInduction generalizing f with
  | zero => simp
  | one => simp [sum_range_succ]
  | more n ih _ =>
    have hdiv : (n+2)/2 = n/2+1 := by omega
    rw [hdiv, sum_range_succ f (n+2), sum_range_succ' f (n+1),
      sum_range_succ' (fun k => f k + if 2*k=n+2 then 0 else f (n+2-k)) (n/2+1),
      ih (fun k => f (k+1))]
    simp only [Nat.mul_zero, Nat.zero_ne_add_one, ↓reduceIte, Nat.sub_zero]
    have eq : (∑ k ∈ range (n/2+1), (f (k+1) + if 2*k=n then 0 else f (n-k+1))) =
        ∑ k ∈ range (n/2+1), (f (k+1) + if 2*(k+1)=n+2 then 0 else f (n+2-(k+1))) := by
      apply sum_congr rfl
      intro k hk
      have h := mem_range.mp hk
      simp only [show 2*(k+1)=n+2 ↔ 2*k=n by omega, show n+2-(k+1) = n-k+1 by omega]
    rw [eq]
    ac_rfl

private theorem full_sets {I : Type*} [Fintype I] [DecidableEq I] (c : I → ℤ)
    (T : ℤ) (B : ℕ) :
    (∃ g : I → ℤ, (∀ i, (g i).natAbs ≤ 1) ∧ (∑ i, g i*c i)=T ∧
      (∑ i, (g i).natAbs) ≤ B) ↔
    ∃ p m : Finset I, Disjoint p m ∧ (∑ i ∈ p, c i)-(∑ i ∈ m, c i)=T ∧ p.card+m.card≤B := by
  classical
  constructor
  · rintro ⟨g,hg,ht,hb⟩
    let p := univ.filter (fun i => g i=1)
    let m := univ.filter (fun i => g i= -1)
    refine ⟨p,m,disjoint_left.mpr (fun i hi hm => ?_), ?_, ?_⟩
    · simp [p,m] at hi hm
      omega
    · rw [← ht]
      simp only [p,m,sum_filter,← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      have h := hg i
      have : g i = -1 ∨ g i=0 ∨ g i=1 := by omega
      rcases this with h'|h'|h' <;> simp [h']
    · refine le_trans ?_ hb
      simp only [p,m,card_eq_sum_ones,sum_filter,← sum_add_distrib]
      refine sum_le_sum fun i _ => ?_
      have h := hg i
      have : g i = -1 ∨ g i=0 ∨ g i=1 := by omega
      rcases this with h'|h'|h' <;> simp [h']
  · rintro ⟨p,m,hd,ht,hb⟩
    let g := fun i => if i ∈ p then (1:ℤ) else if i ∈ m then -1 else 0
    have hdis := disjoint_left.mp hd
    refine ⟨g, fun i => ?_, ?_, ?_⟩
    · by_cases h : i ∈ p
      · simp [g,h]
      · by_cases h' : i ∈ m <;> simp [g,h,h']
    · rw [← ht, ← univ_inter p, ← univ_inter m, ← filter_mem_eq_inter, ← filter_mem_eq_inter]
      simp only [sum_filter, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      by_cases hp : i∈p
      · simp [g,hp,hdis hp]
      · by_cases hm : i∈m <;> simp [g,hp,hm]
    · refine le_trans ?_ hb
      rw [← univ_inter p, ← univ_inter m, ← filter_mem_eq_inter, ← filter_mem_eq_inter]
      simp only [card_eq_sum_ones, sum_filter, ← sum_add_distrib]
      refine sum_le_sum fun i _ => ?_
      by_cases hp : i∈p
      · simp [g,hp,hdis hp]
      · by_cases hm : i∈m <;> simp [g,hp,hm]

private theorem full_nat_sets (n : ℕ) (T : ℤ) (B : ℕ) :
    (∃ g : ℕ → ℤ, (∀ i ≤ n, (g i).natAbs ≤ 1) ∧
      (∑ i ∈ range (n+1), g i*(n.choose i:ℤ))=T ∧ (∑ i ∈ range (n+1), (g i).natAbs) ≤ B) ↔
    ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
      (∑ i ∈ p, (n.choose i.val:ℤ))-(∑ i ∈ m, (n.choose i.val:ℤ))=T ∧ p.card+m.card≤B := by
  rw [← full_sets]
  constructor
  · rintro ⟨g,hg,ht,hb⟩
    exact ⟨fun i => g i.val, fun i => hg _ (by omega),
      (Fin.sum_univ_eq_sum_range _ _).trans ht, (Fin.sum_univ_eq_sum_range _ _).trans_le hb⟩
  · rintro ⟨g,hg,ht,hb⟩
    let gn := fun i => if h:i<n+1 then g ⟨i,h⟩ else 0
    refine ⟨gn,fun i hi => ?_, ?_, ?_⟩
    · simpa only [gn, dif_pos (show i<n+1 by omega)] using hg ⟨i,by omega⟩
    · rw [← Fin.sum_univ_eq_sum_range]
      simpa only [gn, dif_pos (Fin.isLt _), Fin.eta] using ht
    · rw [← Fin.sum_univ_eq_sum_range]
      simpa only [gn, dif_pos (Fin.isLt _), Fin.eta] using hb

theorem folded_iff (n : ℕ) (T : ℤ) (B : ℕ) :
    (∃ w : ℕ → ℤ, (∀ k ≤ n/2, (w k).natAbs ≤ if 2*k=n then 1 else 2) ∧
      (∑ k ∈ range (n/2+1), w k*(n.choose k:ℤ)) = T ∧
      (∑ k ∈ range (n/2+1), (w k).natAbs) ≤ B) ↔
    ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
      (∑ i ∈ p, (n.choose i.val:ℤ))-(∑ i ∈ m, (n.choose i.val:ℤ))=T ∧ p.card+m.card≤B := by
  rw [← full_nat_sets]
  constructor
  · rintro ⟨w,hw,ht,hb⟩
    let f (z : ℤ) := if z< -1 then (-1:ℤ) else if 1<z then 1 else z
    let g (i : ℕ) := if i≤n/2 then f (w i) else w (n-i) - f (w (n-i))
    have vals (k : ℕ) (hk : k ≤ n/2) :
        w k = -2 ∨ w k = -1 ∨ w k = 0 ∨ w k = 1 ∨ w k = 2 := by
      have hk' := hw k hk
      split at hk' <;> omega
    have piece (k : ℕ) (hk : k≤n/2) :
        (g k + if 2*k=n then 0 else g (n-k)) = w k ∧
        ((g k).natAbs + if 2*k=n then 0 else (g (n-k)).natAbs) = (w k).natAbs := by
      by_cases hc : 2*k=n
      · have h1 := hw k hk
        rw [if_pos hc] at h1
        have hw1 : w k = -1 ∨ w k=0 ∨ w k=1 := by omega
        rcases hw1 with h|h|h <;> simp [g,hk,hc,h,f]
      · have hmirror : ¬ n-k≤n/2 := by omega
        have hinv : n-(n-k)=k := by omega
        rcases vals k hk with h|h|h|h|h <;> simp [g,hk,hc,hmirror,hinv,h,f]
    refine ⟨g,?_,?_,?_⟩
    · intro i hi
      by_cases h : i≤n/2
      · rcases vals i h with h'|h'|h'|h'|h' <;> simp [g,h,h',f]
      · rcases vals (n-i) (by omega) with h'|h'|h'|h'|h' <;> simp [g,h,h',f]
    · rw [fold_range, ← ht]
      apply sum_congr rfl
      intro k hk
      have hl := mem_range.mp hk
      have h := (piece k (by omega)).1
      by_cases hc : 2*k=n
      · simpa [hc] using congrArg (fun z : ℤ => z*(n.choose k:ℤ)) h
      · simpa [hc,add_mul,Nat.choose_symm (show k≤n by omega)] using
            congrArg (fun z : ℤ => z*(n.choose k:ℤ)) h
    · rw [fold_range]
      apply le_trans (le_of_eq ?_) hb
      exact sum_congr rfl fun k hk => (piece k (Nat.le_of_lt_succ (mem_range.mp hk))).2
  · rintro ⟨g,hg,ht,hb⟩
    let w (k : ℕ) := g k + if 2*k=n then 0 else g (n-k)
    refine ⟨w,?_,?_,?_⟩
    · intro k hk
      have hk0 := hg k (by omega)
      have hk1 := hg (n-k) (by omega)
      by_cases hc : 2*k=n
      · simpa [w,hc] using hk0
      · simp only [w, if_neg hc]
        exact (Int.natAbs_add_le _ _).trans (by omega)
    · rw [← ht,fold_range n]
      apply sum_congr rfl
      intro k hk
      have hl := mem_range.mp hk
      by_cases hc : 2*k=n <;> simp [w,hc,add_mul,Nat.choose_symm (show k≤n by omega)]
    · rw [fold_range] at hb
      refine le_trans (sum_le_sum (fun k hk => ?_)) hb
      by_cases hc : 2*k=n
      · simp [w,hc]
      · simpa [w,hc] using Int.natAbs_add_le (g k) (g (n-k))

end Fib743

namespace Fib743

private theorem prunes_valid (cs : List (ℕ × ℕ)) (t : ℤ) (b : ℕ) (h : (fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (go : ℤ → ℕ → Prop) t b => ∃ z : ℤ, z.natAbs ≤ cw.1 ∧ z.natAbs ≤ b ∧
        go (t-z*(cw.2:ℤ)) (b-z.natAbs))
      (fun (t : ℤ) (_ : ℕ) => t = 0)) cs t b) :
    let head := ((fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (rest : List (ℕ × ℕ × ℕ × ℕ)) =>
        let h := rest.headD (0,0,0,0)
        (cw.1, cw.2, cw.2.gcd h.2.2.1, cw.1*cw.2+h.2.2.2) :: rest) []) cs).headD (0,0,0,0)
    ((head.2.2.1:ℤ) ∣ t) ∧ t.natAbs ≤ head.2.2.2 := by
  induction cs generalizing t b with
  | nil => change t=0 at h; simp [h]
  | cons c cs ih =>
    obtain ⟨c,w⟩ := c
    obtain ⟨z,hz,_,hr⟩ := h
    obtain ⟨hg,hm⟩ := ih _ _ hr
    let head := ((fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (rest : List (ℕ × ℕ × ℕ × ℕ)) =>
        let h := rest.headD (0,0,0,0)
        (cw.1, cw.2, cw.2.gcd h.2.2.1, cw.1*cw.2+h.2.2.2) :: rest) []) cs).headD (0,0,0,0)
    let g := w.gcd head.2.2.1
    change (↑g ∣ t) ∧ t.natAbs ≤ c*w+head.2.2.2
    have hd1 : (g:ℤ) ∣ (w:ℤ) := by exact_mod_cast Nat.gcd_dvd_left w head.2.2.1
    have hd2 : (g:ℤ) ∣ (head.2.2.1:ℤ) := by exact_mod_cast Nat.gcd_dvd_right w head.2.2.1
    have eq : t = z*(w:ℤ)+(t-z*(w:ℤ)) := by ring
    constructor
    · exact eq ▸ dvd_add (dvd_mul_of_dvd_right hd1 _) (hd2.trans hg)
    · calc
        _ = (z*(w:ℤ)+(t-z*(w:ℤ))).natAbs := congrArg Int.natAbs eq
        _ ≤ (z*(w:ℤ)).natAbs + (t-z*(w:ℤ)).natAbs := Int.natAbs_add_le _ _
        _ ≤ _ := by rw [Int.natAbs_mul]; exact Nat.add_le_add (Nat.mul_le_mul_right w hz) hm

theorem search_spec (cs : List (ℕ × ℕ)) (T : ℤ) (B : ℕ) (hc : ∀ x ∈ cs, x.1≤2) :
    (fun (columns : List (ℕ × ℕ)) => (fun (ps : List (ℕ × ℕ × ℕ × ℕ)) => ps.foldr
      (fun cwgm (go : ℤ → ℕ → Bool) t b =>
        decide ((cwgm.2.2.1:ℤ) ∣ t) && decide (t.natAbs ≤ cwgm.2.2.2) &&
        ([0,1,-1,2,-2] : List ℤ).any (fun z =>
          decide (z.natAbs≤cwgm.1) && decide (z.natAbs≤b) &&
            go (t-z*(cwgm.2.1:ℤ)) (b-z.natAbs)))
      (fun (t : ℤ) (_ : ℕ) => decide (t=0))) ((fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (rest : List (ℕ × ℕ × ℕ × ℕ)) =>
        let h := rest.headD (0,0,0,0)
        (cw.1, cw.2, cw.2.gcd h.2.2.1, cw.1*cw.2+h.2.2.2) :: rest) []) columns)) cs T B = true ↔ (fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (go : ℤ → ℕ → Prop) t b => ∃ z : ℤ, z.natAbs ≤ cw.1 ∧ z.natAbs ≤ b ∧
        go (t-z*(cw.2:ℤ)) (b-z.natAbs))
      (fun (t : ℤ) (_ : ℕ) => t = 0)) cs T B := by
  induction cs generalizing T B with
  | nil => simp
  | cons c cs ih =>
    obtain ⟨c,w⟩ := c
    have hc' := hc (c,w) (by simp)
    have htail := fun x (hx : x∈cs) => hc x (List.mem_cons_of_mem _ hx)
    change (_ && _ && ([0,1,-1,2,-2] : List ℤ).any (fun z =>
        decide (z.natAbs≤c) && decide (z.natAbs≤B) &&
          (fun (columns : List (ℕ × ℕ)) => (fun (ps : List (ℕ × ℕ × ℕ × ℕ)) => ps.foldr
      (fun cwgm (go : ℤ → ℕ → Bool) t b =>
        decide ((cwgm.2.2.1:ℤ) ∣ t) && decide (t.natAbs ≤ cwgm.2.2.2) &&
        ([0,1,-1,2,-2] : List ℤ).any (fun z =>
          decide (z.natAbs≤cwgm.1) && decide (z.natAbs≤b) &&
            go (t-z*(cwgm.2.1:ℤ)) (b-z.natAbs)))
      (fun (t : ℤ) (_ : ℕ) => decide (t=0))) ((fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (rest : List (ℕ × ℕ × ℕ × ℕ)) =>
        let h := rest.headD (0,0,0,0)
        (cw.1, cw.2, cw.2.gcd h.2.2.1, cw.1*cw.2+h.2.2.2) :: rest) []) columns)) cs (T-z*(w:ℤ)) (B-z.natAbs))) = true ↔ _
    simp only [Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true,ih _ _ htail]
    constructor
    · rintro ⟨⟨_,_⟩,z,_,⟨h1,h2⟩,hr⟩
      exact ⟨z,h1,h2,hr⟩
    · intro h
      have hg := prunes_valid _ _ _ h
      obtain ⟨z,h1,h2,hr⟩ := h
      refine ⟨hg, z, ?_, ⟨h1,h2⟩, hr⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      change c≤2 at hc'
      omega

theorem reaches_perm {cs ds : List (ℕ × ℕ)} (h : cs.Perm ds) (T : ℤ) (B : ℕ) :
    (fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (go : ℤ → ℕ → Prop) t b => ∃ z : ℤ, z.natAbs ≤ cw.1 ∧ z.natAbs ≤ b ∧
        go (t-z*(cw.2:ℤ)) (b-z.natAbs))
      (fun (t : ℤ) (_ : ℕ) => t = 0)) cs T B ↔ (fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (go : ℤ → ℕ → Prop) t b => ∃ z : ℤ, z.natAbs ≤ cw.1 ∧ z.natAbs ≤ b ∧
        go (t-z*(cw.2:ℤ)) (b-z.natAbs))
      (fun (t : ℤ) (_ : ℕ) => t = 0)) ds T B := by
  induction h generalizing T B with
  | nil => rfl
  | cons v _ ih =>
    rcases v with ⟨c,w⟩
    simp only [List.foldr_cons, ih]
  | swap a b cs =>
    rcases a with ⟨c,w⟩
    rcases b with ⟨d,v⟩
    constructor <;> rintro ⟨x,hx1,hx2,y,hy1,hy2,hr⟩ <;>
      refine ⟨y,hy1,by omega,x,hx1,by omega,?_⟩ <;>
      convert hr using 1 <;> omega
  | trans _ _ ih1 ih2 => exact (ih1 T B).trans (ih2 T B)

private theorem reaches_map {α : Type*} [DecidableEq α] (f : α → ℕ × ℕ)
    (l : List α) (hl : l.Nodup) (T : ℤ) (B : ℕ) :
    (fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (go : ℤ → ℕ → Prop) t b => ∃ z : ℤ, z.natAbs ≤ cw.1 ∧ z.natAbs ≤ b ∧
        go (t-z*(cw.2:ℤ)) (b-z.natAbs))
      (fun (t : ℤ) (_ : ℕ) => t = 0)) (l.map f) T B ↔ ∃ w : α → ℤ,
      (∀ k ∈ l, (w k).natAbs ≤ (f k).1) ∧
      (l.map (fun k => w k*((f k).2:ℤ))).sum = T ∧
      (l.map (fun k => (w k).natAbs)).sum ≤ B := by
  induction l generalizing T B with
  | nil => simp [eq_comm]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    change (∃ z : ℤ, z.natAbs ≤ (f a).1 ∧ z.natAbs≤B ∧
      (fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (go : ℤ → ℕ → Prop) t b => ∃ z : ℤ, z.natAbs ≤ cw.1 ∧ z.natAbs ≤ b ∧
        go (t-z*(cw.2:ℤ)) (b-z.natAbs))
      (fun (t : ℤ) (_ : ℕ) => t = 0)) (l.map f) (T-z*((f a).2:ℤ)) (B-z.natAbs)) ↔ _
    constructor
    · rintro ⟨z,hz,hb,hr⟩
      obtain ⟨w,hw,hs,hn⟩ := (ih hl _ _).mp hr
      let v := fun k => if k=a then z else w k
      have va : v a = z := by simp [v]
      have ve (k) (hk : k∈l) : v k = w k := by
        have : k≠a := fun h => ha (h ▸ hk)
        simp [v,this]
      refine ⟨v, ?_, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl|hm
        · simpa [va] using hz
        · simpa [ve k hm] using hw k hm
      · have heq := List.map_congr_left (l := l) (f := fun k => v k*((f k).2:ℤ))
            (g := fun k => w k*((f k).2:ℤ)) (fun k hk => by rw [ve k hk])
        simp only [List.map_cons, List.sum_cons, va, heq]
        omega
      · have heq := List.map_congr_left (l := l) (f := fun k => (v k).natAbs)
            (g := fun k => (w k).natAbs) (fun k hk => by rw [ve k hk])
        simp only [List.map_cons, List.sum_cons, va, heq]
        omega
    · rintro ⟨w,hw,hs,hn⟩
      simp only [List.map_cons, List.sum_cons] at hs hn
      refine ⟨w a,hw a (by simp),by omega, (ih hl _ _).mpr ?_⟩
      exact ⟨w,fun k hk => hw k (List.mem_cons_of_mem _ hk),by omega,by omega⟩

theorem search_row_perm_iff (n : ℕ) (T : ℤ) (B : ℕ) (cols : List (ℕ×ℕ))
    (h : cols.Perm ((List.range (n/2+1)).map (fun k => (if 2*k=n then 1 else 2, n.choose k)))) :
    (fun (columns : List (ℕ × ℕ)) => (fun (ps : List (ℕ × ℕ × ℕ × ℕ)) => ps.foldr
      (fun cwgm (go : ℤ → ℕ → Bool) t b =>
        decide ((cwgm.2.2.1:ℤ) ∣ t) && decide (t.natAbs ≤ cwgm.2.2.2) &&
        ([0,1,-1,2,-2] : List ℤ).any (fun z =>
          decide (z.natAbs≤cwgm.1) && decide (z.natAbs≤b) &&
            go (t-z*(cwgm.2.1:ℤ)) (b-z.natAbs)))
      (fun (t : ℤ) (_ : ℕ) => decide (t=0))) ((fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (rest : List (ℕ × ℕ × ℕ × ℕ)) =>
        let h := rest.headD (0,0,0,0)
        (cw.1, cw.2, cw.2.gcd h.2.2.1, cw.1*cw.2+h.2.2.2) :: rest) []) columns)) cols T B = true ↔
    ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
      (∑ i ∈ p, (n.choose i.val:ℤ))-(∑ i ∈ m, (n.choose i.val:ℤ))=T ∧ p.card+m.card≤B := by
  rw [search_spec, reaches_perm h, reaches_map _ _ List.nodup_range, ← folded_iff]
  · simp only [List.mem_range, Nat.lt_succ_iff]
    rfl
  · intro x hx
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp (h.mem_iff.mp hx)
    split <;> norm_num

theorem search_row_iff (n : ℕ) (T : ℤ) (B : ℕ) :
    (fun (columns : List (ℕ × ℕ)) => (fun (ps : List (ℕ × ℕ × ℕ × ℕ)) => ps.foldr
      (fun cwgm (go : ℤ → ℕ → Bool) t b =>
        decide ((cwgm.2.2.1:ℤ) ∣ t) && decide (t.natAbs ≤ cwgm.2.2.2) &&
        ([0,1,-1,2,-2] : List ℤ).any (fun z =>
          decide (z.natAbs≤cwgm.1) && decide (z.natAbs≤b) &&
            go (t-z*(cwgm.2.1:ℤ)) (b-z.natAbs)))
      (fun (t : ℤ) (_ : ℕ) => decide (t=0))) ((fun (cs : List (ℕ × ℕ)) => cs.foldr
      (fun cw (rest : List (ℕ × ℕ × ℕ × ℕ)) =>
        let h := rest.headD (0,0,0,0)
        (cw.1, cw.2, cw.2.gcd h.2.2.1, cw.1*cw.2+h.2.2.2) :: rest) []) columns)) ((List.range (n/2+1)).map (fun k => (if 2*k=n then 1 else 2, n.choose k))) T B = true ↔
    ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
      (∑ i ∈ p, (n.choose i.val:ℤ))-(∑ i ∈ m, (n.choose i.val:ℤ))=T ∧ p.card+m.card≤B :=
  search_row_perm_iff n T B _ (List.Perm.refl _)

end Fib743

namespace Fib743
open Finset Filter Topology Matrix

/-- A finite sum of nonnegative real exponentials that vanishes at arbitrarily
large integer times vanishes at every positive integer time. -/
theorem positive_moments (S : Finset ℝ) (c : ℝ → ℝ) (hp : ∀ x ∈ S, 0 ≤ x)
    (hz : ∃ᶠ n : ℕ in atTop, ∑ x ∈ S, c x*x^n = 0) :
    ∀ m : ℕ, 0 < m → ∑ x ∈ S, c x*x^m = 0 := by
  classical
  let T := S.filter fun x => 0<x ∧ c x ≠ 0
  have eqT (n : ℕ) (hn : 0<n) :
      ∑ x ∈ T, c x*x^n = ∑ x ∈ S, c x*x^n := by
    apply sum_subset_zero_on_sdiff (filter_subset ..)
    · intro x hout
      obtain ⟨hS,hx⟩ := mem_sdiff.mp hout
      have : ¬ (0<x ∧ c x ≠ 0) := by simpa [T,hS] using hx
      by_cases hc : c x=0
      · simp [hc]
      · have ha := hp x hS
        have e : x=0 := by by_contra h; exact this ⟨lt_of_le_of_ne ha (Ne.symm h),hc⟩
        simp [e,hn.ne']
    · intro x hx
      rfl
  have empty : T = ∅ := by
    by_contra h
    let M := T.max' (Finset.nonempty_iff_ne_empty.mpr h)
    have mem : M ∈ T := Finset.max'_mem _ _
    have mm := Finset.mem_filter.mp mem
    have hM : 0<M := mm.2.1
    have tend : Tendsto (fun n : ℕ => ∑ x ∈ T, c x*(x/M)^n) atTop (𝓝 (c M)) := by
      have each (x : ℝ) (hx : x ∈ T) :
          Tendsto (fun n : ℕ => c x*(x/M)^n) atTop (𝓝 (if x=M then c M else 0)) := by
        by_cases e : x=M
        · subst x
          simp [hM.ne']
        · have hlt : x<M := lt_of_le_of_ne (Finset.le_max' T x hx) e
          have xp := (Finset.mem_filter.mp hx).2.1
          simpa only [if_neg e, mul_zero] using
            (tendsto_const_nhds (x := c x)).mul
              (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg xp.le hM.le)
                ((div_lt_one hM).mpr hlt))
      simpa [mem] using tendsto_finsetSum T each
    have zero : ∃ᶠ n : ℕ in atTop, (∑ x ∈ T, c x*(x/M)^n)=0 := by
      refine (hz.and_eventually (eventually_gt_atTop 0)).mono ?_
      rintro n ⟨e,hn⟩
      simp_rw [div_pow,mul_div_assoc']
      rw [← Finset.sum_div, eqT n hn, e,zero_div]
    exact mm.2.2 (tendsto_nhds_unique_of_frequently_eq tend tendsto_const_nhds zero)
  intro m hm
  rw [← eqT m hm, empty, Finset.sum_empty]

theorem psd_moments {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ)
    (hB : B.PosSemidef) (v : ι → ℝ) (i : ι)
    (hz : ∃ᶠ n : ℕ in atTop, ((B^n).mulVec v) i = 0) :
    ∀ m : ℕ, 0 < m → ((B^m).mulVec v) i = 0 := by
  classical
  let a := hB.1.eigenvalues
  let U := hB.1.eigenvectorUnitary
  let w := (star U : Matrix ι ι ℝ).mulVec v
  let c := fun j : ι => (U : Matrix ι ι ℝ) i j * w j
  have expn (n : ℕ) : ((B^n).mulVec v) i = ∑ j, c j*(a j)^n := by
    have rep : B^n = ((U : Matrix ι ι ℝ) * diagonal (a^n)) * (star U : Matrix ι ι ℝ) := by
      conv_lhs => rw [hB.1.spectral_theorem, ← map_pow, Matrix.diagonal_pow,
        Unitary.conjStarAlgAut_apply]
      rfl
    rw [rep, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (∑ j, (U : Matrix ι ι ℝ) i j * (diagonal (a^n) *ᵥ w) j) = _
    simp only [Matrix.mulVec_diagonal, Pi.pow_apply, c]
    apply Finset.sum_congr rfl
    intro j _
    ring
  let S := univ.image a
  let C := fun x : ℝ => ∑ j ∈ univ.filter (fun j : ι => a j=x), c j
  have grouped (n : ℕ) : (B^n *ᵥ v) i = ∑ x ∈ S, C x*x^n := by
    rw [expn]
    refine (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_image_of_mem a (mem_univ j))
      (fun j => c j * (a j)^n)).symm.trans ?_
    apply Finset.sum_congr rfl
    intro x hx
    rw [show C x*x^n=∑ j ∈ univ.filter (fun j : ι => a j=x), c j*x^n by
      unfold C; rw [Finset.sum_mul]]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(mem_filter.mp hj).2]
  have nonneg : ∀ x ∈ S, 0 ≤ x := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact hB.eigenvalues_nonneg j
  simp_rw [grouped] at hz ⊢
  exact positive_moments S C nonneg hz

private theorem periodic_aux (ι : Type*) [Finite ι] :
  (∀ n : ℕ,
    let p := (univ : Finset (Fin (n+1))).filter fun k => k.val%5=(n/2 + if n%2=0 then 1 else 0)%5
    let m := (univ : Finset (Fin (n+1))).filter fun k => k.val%5=(n/2+2)%5
    Disjoint p m ∧ (∑ k ∈ p, (n.choose k.val:ℤ)) - (∑ k ∈ m, (n.choose k.val:ℤ)) =
      (Nat.fib n:ℤ) ∧ p.card+m.card=(2*n+4)/5) ∧
  (∀ (q : ℕ), 0 < q → ∀ (c : ι → ℤ → ℝ), (∀ i, Function.Periodic (c i) ((10*q:ℕ):ℤ)) →
    ∀ᶠ j : ℕ in atTop, ∀ i : ι,
      (∑ k ∈ range (2*(10*q*j)+1), ((2*(10*q*j)).choose k:ℝ)*c i k) =
        (Nat.fib (2*(10*q*j)):ℝ) → 4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c i k|) ∧
  (∀ (q : ℕ), 0<q → ∀ (c : ℤ→ℝ),
    Function.Periodic c ((10*q:ℕ):ℤ) →
    (∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1),
      ((2*m).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m):ℝ)) →
    4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c k|) ∧
  (∀ (q : ℕ), 0<q → ∀ (c : ℤ→ℝ),
    Function.Periodic c ((10*q:ℕ):ℤ) →
    (∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1+1),
      ((2*m+1).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m+1):ℝ)) →
    4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c k|) ∧
  (∀ (p : ℕ) [NeZero p],
    ∀ᶠ n : ℕ in atTop, ∀ pat : ZMod p → Fin 3,
      let w := fun k : ℕ => ((pat (k:ZMod p)).val:ℤ)-1
      (∑ k ∈ range (n+1), (n.choose k:ℤ)*w k) = (Nat.fib n:ℤ) →
        (2*n+4)/5 ≤ ((range (n+1)).filter fun k => w k≠0).card) := by

  let walk (x : ℤ → ℝ) (k : ℤ) := x (k-1) + 2*x k + x (k+1)

  have walk_eq (x : ℤ → ℝ) (k : ℤ) : walk x k = x (k-1)+2*x k+x (k+1) := rfl

  let foldAt (x : ℤ → ℝ) (k : ℤ) := x k + x (-k)

  have walk_fold (x : ℤ → ℝ) (k : ℤ) :
      foldAt (walk x) k = foldAt x (k-1) + 2*foldAt x k + foldAt x (k+1) := by
    simp only [foldAt,walk_eq,neg_sub,neg_add_rev]
    rw [show (1:ℤ)-k = -k+1 by ring,show -(1:ℤ) + -k = -k-1 by ring]
    ring

  have folded_vanish {x : ℤ → ℝ} (h : ∀ m : ℕ, (walk^[m] x) 0 = 0) :
      ∀ k m : ℕ, foldAt (walk^[m] x) k = 0 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
      intro m
      simp [foldAt, h m]
    | one =>
      intro m
      have h1 := h (m+1)
      rw [Function.iterate_succ_apply'] at h1
      simp only [walk_eq,zero_sub,zero_add,h m,mul_zero,add_zero] at h1
      simpa only [foldAt,Nat.cast_one,add_comm] using h1
    | more k hk hk1 =>
      intro m
      have h2 := hk1 (m+1)
      rw [Function.iterate_succ_apply',walk_fold] at h2
      push_cast at h2 ⊢
      rw [add_sub_cancel_right, hk, show (k:ℤ)+1=((k+1:ℕ):ℤ) by simp,hk1] at h2
      simpa only [zero_add,mul_zero,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℤ)+1=2 by decide] using h2


  have folded_of_positive_moments {x : ℤ → ℝ}
      (h : ∀ m : ℕ, (walk^[m+1] x) 0 = 0) (k : ℕ) :
      x k + x (-(k:ℤ)) = (-1:ℝ)^k * (2*x 0) := by
    have h' : ∀ m : ℕ, (walk^[m] (walk x)) 0 = 0 := by
      intro m
      simpa only [Function.iterate_succ_apply] using h m
    have eq (j : ℕ) := folded_vanish h' j 0
    change foldAt x k = _
    induction k using Nat.twoStepInduction with
    | zero => simp [foldAt]; ring
    | one =>
      have h0 := h 0
      simp [walk_eq] at h0
      simp [foldAt]
      linarith
    | more k hk hk1 =>
      have hrec := eq (k+1)
      simp only [Function.iterate_zero, id_eq,walk_fold,Nat.cast_add,Nat.cast_one,
        add_sub_cancel_right] at hrec
      change foldAt x k + 2*foldAt x ((k+1:ℕ):ℤ) + foldAt x ((k+2:ℕ):ℤ) = 0 at hrec
      rw [hk,hk1] at hrec
      rw [pow_succ] at hrec
      rw [pow_succ,pow_succ]
      linarith

  let fiveFilter (k : ℤ) : ℝ := if k % 5 = 1 then 1 else if k % 5 = 2 then -1 else 0

  let row (n : ℕ) (r : ℤ) : ℤ :=
    ∑ k ∈ range (n+1), (n.choose k : ℤ)*(if ((k:ℤ)-r)%5=0 then 1 else 0)

  have period {n : ℕ} {r s : ℤ} (e : r%5=s%5) : row n r = row n s := by
    unfold row
    apply Finset.sum_congr rfl
    intro k hk
    simp only [show ((k:ℤ)-r)%5=0 ↔ ((k:ℤ)-s)%5=0 by omega]

  have reflect (n : ℕ) (r : ℤ) : row n r = row n (n-r) := by
    unfold row
    rw [← Finset.sum_range_reflect (fun k => (n.choose k:ℤ)*(if ((k:ℤ)-r)%5=0 then 1 else 0))]
    apply Finset.sum_congr rfl
    intro k hk
    have h : k≤n := by simpa using hk
    simp only [Nat.add_sub_cancel, Nat.choose_symm h, Nat.cast_sub h]
    simp only [show ((n:ℤ)-k-r)%5=0 ↔ ((k:ℤ)-(n-r))%5=0 by omega]

  have next (n : ℕ) (r : ℤ) : row (n+1) r = row n r + row n (r-1) := by
    unfold row
    rw [Finset.sum_choose_succ_mul (fun i _ => if ((i:ℤ)-r)%5=0 then (1:ℤ) else 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_add,Nat.cast_one,show (k:ℤ)+1-r = k-(r-1) by ring]

  have two_steps (n : ℕ) (r : ℤ) :
      row (n+2) (r+1) = row n (r+1) + 2*row n r + row n (r-1) := by
    rw [next,add_sub_cancel_right,next,next]
    rw [add_sub_cancel_right]
    ring

  have reference_even_rows (m : ℕ) :
      row (2*m) (m+1) - row (2*m) (m+2) = (Nat.fib (2*m) : ℤ) ∧
      row (2*m) m - row (2*m) (m+2) = (Nat.fib (2*m+1) : ℤ) := by
    induction m with
    | zero => decide
    | succ m ih =>
      have s₁ : row (2*m) ((m:ℤ)-1) = row (2*m) (m+1) := by
        rw [reflect (2*m) ((m:ℤ)-1)]
        apply period
        push_cast
        omega
      have s₃ : row (2*m) ((m:ℤ)+2+1) = row (2*m) (m+2) := by
        rw [reflect (2*m) ((m:ℤ)+2+1)]
        apply period
        push_cast
        omega
      rw [show 2*(m+1)=2*m+2 by omega]
      push_cast
      rw [show (m:ℤ)+1+2=(m+2)+1 by ring,two_steps,two_steps,two_steps]
      rw [show (m:ℤ)+1-1=m by ring,show (m:ℤ)+2-1=m+1 by ring,
        show (m:ℤ)+2=m+1+1 by ring] at *
      rw [s₁,s₃]
      rw [Nat.fib_add_two (n := 2*m+1), Nat.fib_add_two (n := 2*m)]
      push_cast
      constructor <;> linarith

  have odd_row (m : ℕ) :
      row (2*m+1) m - row (2*m+1) (m+2) = (Nat.fib (2*m+1) : ℤ) := by
    have s : row (2*m) ((m:ℤ)-1) = row (2*m) (m+1) := by
      rw [reflect (2*m) ((m:ℤ)-1)]
      apply period
      push_cast
      omega
    rw [next,next,s,show (m:ℤ)+2-1=m+1 by ring]
    linarith only [(reference_even_rows m).2]

  let positions (n r : ℕ) : Finset (Fin (n+1)) :=
    univ.filter fun k => k.val%5=r%5

  let posRef (n : ℕ) := positions n (n/2 + if n%2=0 then 1 else 0)
  let negRef (n : ℕ) := positions n (n/2+2)

  have row_positions (n r : ℕ) :
      (∑ k ∈ positions n r, (n.choose k.val : ℤ)) = row n r := by
    unfold positions
    rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun k =>
      if k%5=r%5 then (n.choose k:ℤ) else 0)]
    unfold row
    apply Finset.sum_congr rfl
    intro k hk
    by_cases h : k%5=r%5
    · simp [h,show ((k:ℤ)-r)%5=0 by omega]
    · simp [h,show ((k:ℤ)-r)%5≠0 by omega]

  have count_aux (n r : ℕ) (hr : r<5) :
      (∑ k ∈ range n, if k%5=r then (1:ℕ) else 0) = (n+4-r)/5 := by
    induction n with
    | zero => simp; omega
    | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      split <;> omega

  have positions_card (n r : ℕ) :
      (positions n r).card = (n+5-r%5)/5 := by
    unfold positions
    rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_eq_sum_range (fun k =>
      if k%5=r%5 then (1:ℕ) else 0)]
    exact count_aux (n+1) _ (Nat.mod_lt _ (by decide))

  have reference (n : ℕ) :
      Disjoint (posRef n) (negRef n) ∧
      (∑ k ∈ posRef n, (n.choose k.val:ℤ)) -
        (∑ k ∈ negRef n, (n.choose k.val:ℤ)) = (Nat.fib n:ℤ) ∧
      (posRef n).card + (negRef n).card = (2*n+4)/5 := by
    unfold posRef negRef
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro k hp hn
      simp only [positions,mem_filter,mem_univ,true_and] at hp hn
      split at hp <;> omega
    · rw [row_positions,row_positions]
      obtain ⟨m, h | h⟩ : ∃ m : ℕ, n=2*m ∨ n=2*m+1 := ⟨n/2, by omega⟩
      · subst n
        simpa using (reference_even_rows m).1
      · subst n
        simpa [show (2*m+1)/2=m by omega] using odd_row m
    · rw [positions_card,positions_card]
      obtain ⟨q,t,ht,rfl⟩ : ∃ q t : ℕ, t<10 ∧ n=q*10+t :=
        ⟨n/10,n%10,Nat.mod_lt _ (by decide),by omega⟩
      interval_cases t <;> split <;> omega

  let cyclicIncidence (L : ℕ) [NeZero L] : Matrix (ZMod L) (ZMod L) ℝ :=
    Matrix.of (fun i j => (if j=i then 1 else 0) + if j=i+1 then 1 else 0)

  let cycleMatrix (L : ℕ) [NeZero L] : Matrix (ZMod L) (ZMod L) ℝ :=
    (cyclicIncidence L).transpose * cyclicIncidence L

  have cycleMatrix_psd (L : ℕ) [NeZero L] : (cycleMatrix L).PosSemidef := by
    simpa [cycleMatrix] using Matrix.posSemidef_conjTranspose_mul_self (cyclicIncidence L)

  have incidence_act (L : ℕ) [NeZero L] (v : ZMod L → ℝ) (i : ZMod L) :
      (cyclicIncidence L).mulVec v i = v i + v (i+1) := by
    simp [Matrix.mulVec, dotProduct, cyclicIncidence, add_mul, ite_mul, sum_add_distrib]

  have incidence_transpose_act (L : ℕ) [NeZero L] (v : ZMod L → ℝ) (i : ZMod L) :
      (cyclicIncidence L).transpose.mulVec v i = v i + v (i-1) := by
    have he (j : ZMod L) : i = j+1 ↔ j = i-1 := by
      rw [eq_sub_iff_add_eq,eq_comm]
    simp [Matrix.mulVec, dotProduct, cyclicIncidence, he, add_mul, ite_mul, sum_add_distrib]

  have cycleMatrix_act (L : ℕ) [NeZero L] (v : ZMod L → ℝ) (i : ZMod L) :
      (cycleMatrix L).mulVec v i = v (i-1)+2*v i+v (i+1) := by
    unfold cycleMatrix
    rw [← Matrix.mulVec_mulVec, incidence_transpose_act,
      incidence_act, incidence_act, sub_add_cancel]
    ring

  have cycle_walk (L : ℕ) [NeZero L] (m : ℕ) (v : ZMod L → ℝ) (k : ℤ) :
      (cycleMatrix L ^ m).mulVec v (k : ZMod L) =
        (walk^[m] (fun z : ℤ => v (z : ZMod L))) k := by
    induction m generalizing k with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, cycleMatrix_act,
        Function.iterate_succ_apply', walk_eq, ← ih (k-1), ← ih k, ← ih (k+1)]
      push_cast
      rfl

  have pascal_shift (n : ℕ) (f : ℕ → ℝ) :
      (∑ j ∈ range (n+1+1), ((n+1).choose j : ℝ)*f j) =
        (∑ j ∈ range (n+1), (n.choose j : ℝ)*f j) +
        ∑ j ∈ range (n+1), (n.choose j : ℝ)*f (j+1) := by
    have h : (∑ j ∈ range (n+1), (n.choose (j+1) : ℝ)*f (j+1))+f 0 =
        ∑ j ∈ range (n+1), (n.choose j : ℝ)*f j := by
      have a := sum_range_succ' (fun j => (n.choose j : ℝ)*f j) (n+1)
      have b := sum_range_succ (fun j => (n.choose j : ℝ)*f j) (n+1)
      simpa [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)] using a.symm.trans b
    rw [sum_range_succ' (fun j => ((n+1).choose j : ℝ)*f j) (n+1)]
    simp only [Nat.choose_succ_succ',Nat.cast_add,add_mul,sum_add_distrib,
      Nat.choose_zero_right,Nat.cast_one,one_mul]
    linarith

  have walk_binomial (m : ℕ) (x : ℤ → ℝ) (k : ℤ) :
      (walk^[m] x) k =
        ∑ j ∈ range (2*m+1), ((2*m).choose j : ℝ)*x (k+(j:ℤ)-m) := by
    induction m generalizing k with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', walk_eq, ih (k-1), ih k, ih (k+1)]
      rw [show 2*(m+1) = 2*m+1+1 by omega]
      rw [pascal_shift, pascal_shift, pascal_shift]
      push_cast
      simp only [show ∀ j : ℕ, k+(j:ℤ)-((m:ℤ)+1) = k-1+j-m by intro j; ring,
        show ∀ j : ℕ, k+((j:ℤ)+1)-((m:ℤ)+1) = k+j-m by intro j; ring,
        show ∀ j : ℕ, k+((j:ℤ)+1+1)-((m:ℤ)+1) = k+1+j-m by intro j; ring]
      ring

  have five_binomial (m : ℕ) :
      (∑ j ∈ Finset.range (2*m+1), ((2*m).choose j : ℝ)*fiveFilter ((j:ℤ)-m)) =
      (Nat.fib (2*m) : ℝ) := by
    calc
      _ = ((row (2*m) ((m:ℤ)+1) - row (2*m) ((m:ℤ)+2) : ℤ) : ℝ) := by
        simp only [row, Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have h1 : ((j:ℤ)-(m+1))%5=0 ↔ ((j:ℤ)-m)%5=1 := by omega
        have h2 : ((j:ℤ)-(m+2))%5=0 ↔ ((j:ℤ)-m)%5=2 := by omega
        by_cases c : ((j:ℤ)-m)%5=1
        · simp [fiveFilter,c,h1,h2]
        · by_cases d : ((j:ℤ)-m)%5=2 <;> simp [fiveFilter,c,d,h1,h2]
      _ = _ := by exact_mod_cast (reference_even_rows m).1

  have five_moment (m : ℕ) :
      (walk^[m] fiveFilter) 0 = (Nat.fib (2*m) : ℝ) := by
    simpa [walk_binomial] using five_binomial m

  have five_add (k : ℤ) : fiveFilter (k+5) = fiveFilter k := by
    simp [fiveFilter]

  have block_mass (j : ℕ) :
      (∑ i ∈ range 5, 2*|fiveFilter (10*(j:ℤ)+i)+fiveFilter (-(10*(j:ℤ)+i))|) = 8 := by
    have hd : (5:ℤ) ∣ 10*(j:ℤ) := ⟨2*(j:ℤ),by ring⟩
    norm_num [Finset.sum_range_succ, fiveFilter, Int.add_emod, Int.mul_emod, Int.neg_emod, hd]

  have sum_cycle_neg (c : ℤ → ℝ) (L : ℕ) (hp : Function.Periodic c (L:ℤ)) :
      (∑ k ∈ range L, |c (-(k:ℤ))|) = ∑ k ∈ range L, |c k| := by
    have h : (∑ k ∈ range (L+1), |c (-(k:ℤ))|) = ∑ k ∈ range (L+1), |c k| := by
      rw [← Finset.sum_range_reflect (fun k : ℕ => |c (k:ℤ)|) (L+1)]
      apply sum_congr rfl
      intro k hk
      have hk' : k ≤ L := by simpa using hk
      rw [Nat.add_sub_cancel,Nat.cast_sub hk',← hp (-(k:ℤ))]
      ring_nf
    rw [sum_range_succ,sum_range_succ] at h
    have u := hp (-(L:ℤ))
    have v := hp 0
    simp only [neg_add_cancel,zero_add] at u v
    rw [← u, v] at h
    linarith


  have period_support (c : ℤ → ℝ) (q : ℕ)
      (hp : Function.Periodic c ((10*q:ℕ):ℤ))
      (h : ∀ m : ℕ, (walk^[m+1] (fun k => c k - fiveFilter k)) 0 = 0) :
      4*(q:ℝ) ≤ ∑ i ∈ range (10*q), |c i| := by
    let mass (k : ℕ) := |c k| + |c (-(k:ℤ))|
    have pair (k : ℕ) : 2*|fiveFilter k + fiveFilter (-(k:ℤ))| ≤ mass k + mass (k+5) := by
      have x := folded_of_positive_moments h k
      have y := folded_of_positive_moments h (k+5)
      push_cast at y
      rw [five_add, show -((k:ℤ)+5)=(-(k:ℤ)-5)+0 by ring] at y
      simp only [add_zero] at y
      rw [← five_add (-(k:ℤ)-5),sub_add_cancel,pow_add] at y
      norm_num at y
      have eq : (c k+c (-(k:ℤ))) + (c ((k:ℤ)+5) + c (-((k:ℤ)+5))) =
          2*(fiveFilter k + fiveFilter (-(k:ℤ))) := by
        rw [show -((k:ℤ)+5)= -(k:ℤ)-5 by ring]
        linarith
      calc
        _ = |(c k+c (-(k:ℤ))) + (c ((k:ℤ)+5) + c (-((k:ℤ)+5)))| := by rw [eq,abs_mul]; norm_num
        _ ≤ (|c k| + |c (-(k:ℤ))|) + (|c ((k:ℤ)+5)| + |c (-((k:ℤ)+5))|) :=
          (abs_add_le ..).trans (add_le_add (abs_add_le ..) (abs_add_le ..))
        _ = _ := by simp [mass]
    have blocks (j : ℕ) : 8*(j:ℝ) ≤ ∑ i ∈ range (10*j), mass i := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Nat.mul_succ,sum_range_add]
        have hs := sum_le_sum (s := range 5) (fun i _ => pair (10*j+i))
        simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,block_mass,sum_add_distrib] at hs
        have split : (∑ i ∈ range 10, mass (10*j+i)) =
            (∑ i ∈ range 5, mass (10*j+i)) + ∑ i ∈ range 5, mass (10*j+i+5) := by
          rw [show 10=5+5 by decide,sum_range_add]
          simp only [add_assoc,add_comm 5 _]
        rw [split]
        push_cast
        linarith
    have hsum := blocks q
    simp only [mass,sum_add_distrib,sum_cycle_neg c _ hp] at hsum
    linarith

  have periodic_moments (L : ℕ) (hL : 0 < L) (v : ℤ → ℝ)
      (per : Function.Periodic v (L : ℤ))
      (hz : ∃ᶠ n : ℕ in atTop, (walk^[n] v) 0 = 0) :
      ∀ m : ℕ, (walk^[m+1] v) 0 = 0 := by
    let : NeZero L := ⟨hL.ne'⟩
    let w : ZMod L → ℝ := fun x => v x.val
    have lift : (fun k : ℤ => w (k : ZMod L)) = v := by
      funext k
      dsimp only [w]
      rw [ZMod.val_intCast,Int.emod_def,mul_comm]
      exact per.sub_int_mul_eq _
    have moments (n : ℕ) : ((cycleMatrix L)^n).mulVec w 0 = (walk^[n] v) 0 := by
      simpa only [Int.cast_zero,lift] using cycle_walk L n w 0
    have h := psd_moments (cycleMatrix L) (cycleMatrix_psd L) w 0
      (hz.mono fun n hn => (moments n).trans hn)
    intro m
    rw [← moments]
    exact h _ (by omega)


  have agreement_moments (q : ℕ) (hq : 0<q) (c : ℤ → ℝ)
      (hc : Function.Periodic c ((10*q : ℕ):ℤ))
      (many : ∃ᶠ j : ℕ in atTop, (∑ k ∈ range (2*(10*q*j)+1),
        ((2*(10*q*j)).choose k:ℝ)*c k) = (Nat.fib (2*(10*q*j)):ℝ)) :
      ∀ m : ℕ, (walk^[m+1] (fun z => c z-fiveFilter z)) 0 = 0 := by
    let L := 10*q
    have hL : 0 < L := by dsimp [L]; omega
    have p5 : Function.Periodic fiveFilter (L:ℤ) := by
      intro z
      simp [fiveFilter, L, Int.add_emod, Int.mul_emod]
    apply periodic_moments L hL _ (fun z => by rw [hc z,p5 z])
    rw [frequently_atTop] at many ⊢
    intro K
    obtain ⟨j,hj,e⟩ := many K
    refine ⟨L*j,le_trans hj (Nat.le_mul_of_pos_left j hL),?_⟩
    have e' := five_moment (L*j)
    rw [walk_binomial] at e' ⊢
    simp only [zero_add, mul_sub, sum_sub_distrib]
    have centre (k : ℕ) : c ((k:ℤ)-(L*j:ℕ)) = c k := by
      rw [Nat.cast_mul,mul_comm (L:ℤ)]
      exact hc.sub_int_mul_eq _
    simp_rw [centre]
    rw [sub_eq_zero]
    exact e.trans (by simpa only [zero_add] using e'.symm)



  have adaptive_period_mass (q : ℕ) (hq : 0 < q)
      (c : ι → ℤ → ℝ) (per : ∀ i, Function.Periodic (c i) ((10*q:ℕ):ℤ)) :
      ∀ᶠ j : ℕ in atTop, ∀ i : ι,
        (∑ k ∈ range (2*(10*q*j)+1), ((2*(10*q*j)).choose k:ℝ)*c i k) =
          (Nat.fib (2*(10*q*j)):ℝ) → 4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c i k| := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases periodMass : 4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c i k|
    · exact Filter.Eventually.of_forall fun _ _ => periodMass
    · have no : ∀ᶠ j : ℕ in atTop, ¬ (∑ k ∈ range (2*(10*q*j)+1),
            ((2*(10*q*j)).choose k:ℝ)*c i k) = (Nat.fib (2*(10*q*j)):ℝ) := by
        by_contra h
        exact periodMass (period_support (c i) q (per i) (agreement_moments q hq _ (per i) h))
      exact no.mono fun _ h e => (h e).elim
  have even_center_fold (q : ℕ) (hq : 0<q) (c : ℤ→ℝ)
      (per : Function.Periodic c ((10*q:ℕ):ℤ))
      (many : ∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1),
        ((2*m).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m):ℝ)) :
      ∀ m : ℕ, (walk^[m+1] (fun z => c z-fiveFilter z)) 0=0 := by
    apply periodic_moments (10*q) (by omega)
    · intro z
      dsimp only
      rw [per z]
      simp [fiveFilter,Int.add_emod,Int.mul_emod]
    · apply many.mono
      intro m h
      rw [walk_binomial]
      simp only [zero_add,mul_sub,sum_sub_distrib,h,five_binomial,sub_self]

  have even_center_mass (q : ℕ) (hq : 0<q) (c : ℤ→ℝ)
      (per : Function.Periodic c ((10*q:ℕ):ℤ))
      (many : ∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1),
        ((2*m).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m):ℝ)) :
      4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c k| := by
    exact period_support c q per (even_center_fold q hq c per many)

  let oddFilter (k : ℤ) : ℝ := if k%5=0 then 1 else if k%5=2 then -1 else 0

  have odd_ref (m : ℕ) :
      (∑ j ∈ range (2*m+1+1), ((2*m+1).choose j:ℝ)*oddFilter ((j:ℤ)-m)) =
        (Nat.fib (2*m+1):ℝ) := by
    have v := (reference (2*m+1)).2.1
    unfold posRef negRef at v
    rw [row_positions,row_positions] at v
    have v' : row (2*m+1) m - row (2*m+1) ((m:ℤ)+2) = (Nat.fib (2*m+1):ℤ) := by
      simpa [show (2*m+1)/2=m by omega] using v
    calc
      _ = ((row (2*m+1) m - row (2*m+1) ((m:ℤ)+2):ℤ):ℝ) := by
        simp only [row,Int.cast_sub,Int.cast_sum,Int.cast_mul,Int.cast_natCast,
          ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have h2 : ((j:ℤ)-(m+2))%5=0 ↔ ((j:ℤ)-m)%5=2 := by omega
        by_cases h : ((j:ℤ)-m)%5=0
        · simp only [oddFilter,h2,h,if_true]
          norm_num
        · by_cases t : ((j:ℤ)-m)%5=2 <;> (simp only [oddFilter,h2,h,t,if_false,if_true]; norm_num)
      _ = _ := by exact_mod_cast v'

  have odd_walk (m : ℕ) (g : ℤ→ℝ) :
      (walk^[m] (fun z => g z+g (z+1))) 0 =
        ∑ j ∈ range (2*m+1+1), ((2*m+1).choose j:ℝ)*g ((j:ℤ)-m) := by
    rw [walk_binomial,pascal_shift]
    simp only [zero_add,mul_add,sum_add_distrib,Nat.cast_add,Nat.cast_one]
    congr 1
    apply sum_congr rfl
    intro j _
    rw [show (j:ℤ)-m+1=j+1-m by ring]


  have odd_pairs (g : ℤ→ℝ) (q : ℕ) (hq : 0<q)
      (per : Function.Periodic g ((10*q:ℕ):ℤ))
      (h : ∀ m : ℕ, (walk^[m+1] (fun z => g z+g (z+1))) 0=0) :
      ∀ k : ℕ, g k+g (1-(k:ℤ))=0 := by
    let d (k : ℕ) := g k+g (1-(k:ℤ))
    let b := g 0+g 1
    have recurrence (k : ℕ) : d k+d (k+1)=(-1:ℝ)^k*(2*b) := by
      have e := folded_of_positive_moments h k
      dsimp [d,b]
      simp only [zero_add] at e ⊢
      rw [show 1-((k:ℤ)+1)= -(k:ℤ) by ring,show 1-(k:ℤ)= -(k:ℤ)+1 by ring]
      linarith only [e]
    have sol (k : ℕ) : d k=(-1:ℝ)^k*(1-2*(k:ℝ))*b := by
      induction k with
      | zero => simp [d,b]
      | succ k ih =>
        have e := recurrence k
        rw [pow_succ,Nat.cast_succ]
        linear_combination e - ih
    have endp : d (10*q)=b := by
      dsimp [d,b]
      have u := per 0
      have v := per.sub_eq (1:ℤ)
      simpa only [zero_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg₂ (·+·) u v
    have last := sol (10*q)
    rw [endp,pow_mul] at last
    norm_num at last
    have hpos : 0<(q:ℝ) := by exact_mod_cast hq
    have bz : b=0 := by
      by_contra ne
      rcases lt_or_gt_of_ne ne with hi|hi
      · nlinarith [mul_neg_of_pos_of_neg hpos hi]
      · nlinarith [mul_pos hpos hi]
    intro k
    simpa [bz,d] using sol k

  have cycle_mass_shift (c : ℤ→ℝ) (L s : ℕ) (hp : Function.Periodic c (L:ℤ)) :
      ∑ k ∈ range L, |c ((k:ℤ)+s)| = ∑ k ∈ range L, |c k| := by
    induction s with
    | zero => simp
    | succ s ih =>
      have u := sum_range_succ' (fun k : ℕ => |c ((k:ℤ)+s)|) L
      have v := sum_range_succ (fun k : ℕ => |c ((k:ℤ)+s)|) L
      rw [add_comm (L:ℤ),hp] at v
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add] at u
      simp only [Nat.cast_succ,show ∀ k : ℕ, (k:ℤ)+(s+1)=k+1+s by intro k; ring]
      linarith only [u,v,ih]

  have mass_flip (c : ℤ→ℝ) (L : ℕ) (hp : Function.Periodic c (L:ℤ)) :
      ∑ k ∈ range L, |c (1-(k:ℤ))| = ∑ k ∈ range L, |c k| := by
    rw [← cycle_mass_shift c L 2 hp]
    norm_num only [Nat.cast_ofNat]
    rw [← sum_range_reflect (fun k : ℕ => |c ((k:ℤ)+2)|) L]
    apply sum_congr rfl
    intro k hk
    have hk' : k<L := mem_range.mp hk
    rw [Nat.cast_sub (show k≤L-1 by omega),Nat.cast_sub (show 1≤L by omega),Nat.cast_one,
      ← hp (1-(k:ℤ))]
    ring_nf

  have odd_ref_mass (q : ℕ) :
      ∑ k ∈ range (10*q), |oddFilter k+oddFilter (1-(k:ℤ))| = 8*(q:ℝ) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ,sum_range_add,ih]
      have b : ∑ i ∈ range 10, |oddFilter ((10*q+i:ℕ):ℤ)+oddFilter (1-((10*q+i:ℕ):ℤ))| = 8 := by
        have op (u v : ℤ) (e : u%5 = v%5) : oddFilter u=oddFilter v := by simp only [oddFilter,e]
        have op1 (i : ℕ) : oddFilter ((10*q+i:ℕ):ℤ)=oddFilter i := by
          apply op
          push_cast
          omega
        have op2 (i : ℕ) : oddFilter (1-((10*q+i:ℕ):ℤ))=oddFilter (1-(i:ℤ)) := by
          apply op
          push_cast
          omega
        simp_rw [op1,op2]
        norm_num [sum_range_succ,oddFilter]
      rw [b,Nat.cast_succ]
      ring

  have odd_center_fold (q : ℕ) (hq : 0<q) (c : ℤ→ℝ)
      (per : Function.Periodic c ((10*q:ℕ):ℤ))
      (many : ∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1+1),
        ((2*m+1).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m+1):ℝ)) :
      ∀ k : ℕ, c k+c (1-(k:ℤ))=oddFilter k+oddFilter (1-(k:ℤ)) := by
    let g := fun z => c z-oddFilter z
    have pg : Function.Periodic g ((10*q:ℕ):ℤ) := by
      intro z
      dsimp only [g]
      rw [per z]
      have x : (z+((10*q:ℕ):ℤ))%5=z%5 := by push_cast; omega
      simp only [oddFilter,x]
    have ps : Function.Periodic (fun z => g z+g (z+1)) ((10*q:ℕ):ℤ) := by
      intro z
      dsimp only
      rw [pg z,show z+(↑(10*q):ℤ)+1=(z+1)+(↑(10*q):ℤ) by ring,pg]
    have wh := periodic_moments (10*q) (by omega) _ ps (many.mono fun m h => by
      rw [odd_walk]
      simp only [g,mul_sub,sum_sub_distrib,h,odd_ref,sub_self])
    have pairs := odd_pairs g q hq pg wh
    intro k
    have e := pairs k
    dsimp [g] at e
    linarith only [e]

  have odd_center_mass (q : ℕ) (hq : 0<q) (c : ℤ→ℝ)
      (per : Function.Periodic c ((10*q:ℕ):ℤ))
      (many : ∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1+1),
        ((2*m+1).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m+1):ℝ)) :
      4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c k| := by
    have pairs := odd_center_fold q hq c per many
    have le (k : ℕ) : |oddFilter k+oddFilter (1-(k:ℤ))| ≤ |c k|+|c (1-(k:ℤ))| := by
      have e := pairs k
      rw [← e]
      exact abs_add_le .. 
    have h := sum_le_sum (s:=range (10*q)) (fun k _ => le k)
    rw [odd_ref_mass,sum_add_distrib,mass_flip c _ per] at h
    linarith
  have residue_count (n r : ℕ) (hr : r<5) :
      (∑ k ∈ range n, if k%5=r then 1 else 0) = (n+4-r)/5 := by
    induction n with
    | zero => simp; omega
    | succ n ih => rw [sum_range_succ,ih]; split <;> omega

  have paired_count (n : ℕ) (live : ℕ→Bool)
      (covers : ∀ j ≤ n, j%5 ≠ (n/2+if n%2=0 then 0 else 3)%5 →
        live j=true ∨ live (n-j)=true) :
      (2*n+4)/5 ≤ ((range (n+1)).filter (fun j => live j=true)).card := by
    let r := (n/2+if n%2=0 then 0 else 3)%5
    let v (k : ℕ) := if live k=true then 1 else 0
    have pair (j : ℕ) (hj : j ∈ range (n+1)) :
        1 ≤ (if j%5=r then 1 else 0)+v j+v (n-j) := by
      by_cases e : j%5=r
      · simp [e]; omega
      · rcases covers j (by simpa using hj) e with h|h <;> simp [e,v,h]
    have h := sum_le_sum (s:=range (n+1)) (fun j hj => pair j hj)
    have flip : (∑ j ∈ range (n+1), v (n-j)) = ∑ j ∈ range (n+1), v j := by
      simpa using sum_range_reflect v (n+1)
    have card : (∑ j ∈ range (n+1), v j) = ((range (n+1)).filter fun j => live j=true).card := by
      simp [v]
    rw [sum_add_distrib,sum_add_distrib,flip,card,residue_count _ _ (Nat.mod_lt _ (by decide))] at h
    simp only [sum_const,card_range,nsmul_eq_mul,mul_one] at h
    have ar : 2*((2*n+4)/5)+(n+1+4-r)/5=n+1 := by
      obtain ⟨k,t,ht,he⟩ : ∃ k t:ℕ,t<10 ∧ n=10*k+t := ⟨n/10,n%10,Nat.mod_lt _ (by decide),by omega⟩
      dsimp [r]
      rw [he]
      interval_cases t <;> split <;> omega
    simp only [Nat.cast_id,r] at ar h
    omega

  have ternary_even_fold (c : ℤ→ℝ) (codes : ∀ z, ∃ i : Fin 3, c z=(i.val:ℝ)-1)
      (h : ∀ m : ℕ, (walk^[m+1] (fun z => c z-fiveFilter z)) 0=0) :
      ∀ z:ℤ, c z+c (-z)=fiveFilter z+fiveFilter (-z) := by
    have bound (z : ℤ) : c z≤1 := by
      obtain ⟨i,e⟩ := codes z
      rw [e]
      have eq : i.val≤2 := by omega
      exact_mod_cast (show ((i.val:ℤ)-1)≤1 by omega)
    have h1 := folded_of_positive_moments h 1
    have h4 := folded_of_positive_moments h 4
    norm_num [fiveFilter] at h1 h4
    have zero : c 0=0 := by
      obtain ⟨i,e⟩ := codes 0
      fin_cases i <;> norm_num at e <;> linarith only [e,h1,h4,bound 1,bound (-1),bound 4,bound (-4)]
    have pn (k : ℕ) : c k+c (-(k:ℤ))=fiveFilter k+fiveFilter (-(k:ℤ)) := by
      have he := folded_of_positive_moments h k
      simp only [zero,show fiveFilter 0=0 by norm_num [fiveFilter],sub_self,mul_zero] at he
      linarith only [he]
    intro z
    by_cases hz : 0≤z
    · simpa [Int.toNat_of_nonneg hz] using pn z.toNat
    · have hz' : 0≤-z := by omega
      simpa [Int.toNat_of_nonneg hz',add_comm] using pn (-z).toNat

  have ternary_odd_fold (c : ℤ→ℝ)
      (h : ∀ k : ℕ, c k+c (1-(k:ℤ))=oddFilter k+oddFilter (1-(k:ℤ))) :
      ∀ z : ℤ, c z+c (1-z)=oddFilter z+oddFilter (1-z) := by
    intro z
    by_cases hz : 0≤z
    · simpa [Int.toNat_of_nonneg hz] using h z.toNat
    · have hz' : 0≤1-z := by omega
      simpa [Int.toNat_of_nonneg hz',add_comm] using h (1-z).toNat

  have reflected_support (o : Bool) (c : ℤ→ℝ)
      (h : ∀ z, c z+c ((if o then 1 else 0)-z) =
        (if o then oddFilter else fiveFilter) z+(if o then oddFilter else fiveFilter) ((if o then 1 else 0)-z))
      (z : ℤ) (hz : z%5 ≠ if o then 3 else 0) :
      c z≠0 ∨ c ((if o then 1 else 0)-z)≠0 := by
    by_contra! no
    have eq := h z
    rw [no.1,no.2,zero_add] at eq
    have hl : 0≤z%5 := Int.emod_nonneg _ (by decide)
    have hu : z%5<5 := Int.emod_lt_of_pos _ (by decide)
    cases o <;> simp only [Bool.false_eq_true,if_false,if_true] at eq hz <;>
      simp only [oddFilter,fiveFilter] at eq <;>
      simp only [show (0-z)%5=(5-z%5)%5 by omega,show (1-z)%5=(6-z%5)%5 by omega] at eq <;>
      interval_cases z%5 <;> first | (norm_num at eq; done) | norm_num at hz

  have frequent_rigidity {P : ℕ→Prop} {Q : Prop}
      (h : (∃ᶠ m : ℕ in atTop,P m) → Q) : ∀ᶠ m : ℕ in atTop, P m → Q := by
    by_cases e : Q
    · exact .of_forall fun _ _ => e
    · have no : ∀ᶠ m : ℕ in atTop, ¬ P m := by by_contra he; exact e (h he)
      exact no.mono fun _ hn hp => (hn hp).elim

  have periodic_reference_optimal (p : ℕ) [NeZero p] :
      ∀ᶠ n : ℕ in atTop, ∀ pat : ZMod p → Fin 3,
        let w := fun k : ℕ => ((pat (k:ZMod p)).val:ℤ)-1
        (∑ k ∈ range (n+1), (n.choose k:ℤ)*w k) = (Nat.fib n:ℤ) →
          (2*n+4)/5 ≤ ((range (n+1)).filter fun k => w k≠0).card := by
    let c := fun (P : ZMod p → Fin 3) (z : ℤ) => ((P (z:ZMod p)).val:ℝ)-1
    have hp (P : ZMod p→Fin 3) : Function.Periodic (c P) ((10*p:ℕ):ℤ) := by intro z; simp [c]
    have ev : ∀ᶠ m:ℕ in atTop, ∀ P : ZMod p→Fin 3,
        (∑ j ∈ range (2*m+1),((2*m).choose j:ℝ)*c P ((j:ℤ)-m))=(Nat.fib (2*m):ℝ) →
        ∀ z:ℤ, c P z+c P (-z)=fiveFilter z+fiveFilter (-z) := by
      apply Filter.eventually_all.mpr
      intro P
      apply frequent_rigidity
      intro many
      exact ternary_even_fold _ (fun z => ⟨P _,rfl⟩) (even_center_fold p (NeZero.pos _) (c P) (hp P) many)
    have od : ∀ᶠ m:ℕ in atTop, ∀ P : ZMod p→Fin 3,
        (∑ j ∈ range (2*m+1+1),((2*m+1).choose j:ℝ)*c P ((j:ℤ)-m))=(Nat.fib (2*m+1):ℝ) →
        ∀ z:ℤ, c P z+c P (1-z)=oddFilter z+oddFilter (1-z) := by
      apply Filter.eventually_all.mpr
      intro P
      apply frequent_rigidity
      intro many
      exact ternary_odd_fold _ (odd_center_fold p (NeZero.pos _) (c P) (hp P) many)
    obtain ⟨M,hM⟩ := eventually_atTop.mp (ev.and od)
    filter_upwards [eventually_ge_atTop (2*M)] with n hn
    intro pat w h
    let m := n/2
    let P (z:ZMod p) := pat (z+(m:ZMod p))
    have unshift (k : ℕ) : c P ((k:ℤ)-m)=(w k:ℝ) := by simp [c,P,w]
    have hn' : m≥M := by dsimp [m]; omega
    have rr : n=2*m ∨ n=2*m+1 := by dsimp [m]; omega
    have he : (∑ k ∈ range (n+1), (n.choose k:ℝ)*c P ((k:ℤ)-m))=(Nat.fib n:ℝ) := by
      simpa only [unshift,Int.cast_sum,Int.cast_mul,Int.cast_natCast] using congrArg ((↑):ℤ→ℝ) h
    have final := paired_count n (fun k => decide (w k≠0))
    simp only [decide_eq_true_eq] at final
    apply final
    intro j hj residue
    let z : ℤ := (j:ℤ)-m
    have us : c P z = (w j:ℝ) := unshift j
    rcases rr with e|e
    · have folded := (hM m hn').1 P (by rwa [←e])
      have zz : ((n-j:ℕ):ℤ)-m= -z := by rw [Nat.cast_sub hj]; dsimp [z]; omega
      have pair := reflected_support false (c P) (by simpa using folded) z (by
        simp only [Bool.false_eq_true,if_false]
        dsimp [z,m]
        dsimp [m] at e
        simp only [if_pos (show n%2=0 by omega),Nat.add_zero] at residue
        omega)
      simp only [Bool.false_eq_true,if_false,zero_sub,us,←zz,unshift,Int.cast_ne_zero] at pair
      exact pair
    · have folded := (hM m hn').2 P (by rwa [←e])
      have zz : ((n-j:ℕ):ℤ)-m=1-z := by rw [Nat.cast_sub hj]; dsimp [z]; omega
      have pair := reflected_support true (c P) (by simpa using folded) z (by
        simp only [if_true]
        dsimp [z,m]
        dsimp [m] at e
        simp only [if_neg (show n%2≠0 by omega)] at residue
        omega)
      simp only [if_true,us,←zz,unshift,Int.cast_ne_zero] at pair
      exact pair
  exact ⟨reference, adaptive_period_mass, even_center_mass, odd_center_mass, periodic_reference_optimal⟩

theorem reference_explicit :
    ∀ n : ℕ,
    let p := (univ : Finset (Fin (n+1))).filter fun k => k.val%5=(n/2 + if n%2=0 then 1 else 0)%5
    let m := (univ : Finset (Fin (n+1))).filter fun k => k.val%5=(n/2+2)%5
    Disjoint p m ∧ (∑ k ∈ p, (n.choose k.val:ℤ)) - (∑ k ∈ m, (n.choose k.val:ℤ)) =
      (Nat.fib n:ℤ) ∧ p.card+m.card=(2*n+4)/5 := (periodic_aux Unit).1

theorem adaptive_period_mass {ι : Type*} [Finite ι] :
    ∀ (q : ℕ), 0 < q → ∀ (c : ι → ℤ → ℝ), (∀ i, Function.Periodic (c i) ((10*q:ℕ):ℤ)) →
    ∀ᶠ j : ℕ in atTop, ∀ i : ι,
      (∑ k ∈ range (2*(10*q*j)+1), ((2*(10*q*j)).choose k:ℝ)*c i k) =
        (Nat.fib (2*(10*q*j)):ℝ) → 4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c i k| := (periodic_aux ι).2.1

private theorem absolute_blocks (L s : ℕ) (c : ℤ → ℝ) (per : Function.Periodic c (L:ℤ)) :
    ∑ k ∈ range (L*s), |c k| = (s:ℝ)*∑ k ∈ range L, |c k| := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ,Finset.sum_range_add,ih,Nat.cast_succ,add_mul,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_add,Nat.cast_mul,add_comm,mul_comm (L:ℤ),per.nat_mul s]

theorem adaptive_period_obstruction {ι : Type*} [Finite ι] (q : ℕ) (hq : 0 < q)
    (c : ι → ℤ → ℝ) (per : ∀ i, Function.Periodic (c i) ((10*q:ℕ):ℤ)) :
    ∀ᶠ j : ℕ in atTop, ∀ i : ι, let n := 2*(10*q*j)
      (∑ k ∈ range (n+1), (n.choose k:ℝ)*c i k) = (Nat.fib n:ℝ) →
        (((n+2)/3+2 : ℕ):ℝ) < ∑ k ∈ range (n+1), |c i k| := by
  filter_upwards [adaptive_period_mass q hq c per, eventually_ge_atTop 4] with j hm hj
  intro i n h
  have lb := mul_le_mul_of_nonneg_left (hm i h) (show 0≤((2*j:ℕ):ℝ) by positivity)
  have eq : n = (10*q)*(2*j) := by dsimp [n]; ring
  rw [Finset.sum_range_succ,eq,absolute_blocks _ _ _ (per i)]
  have qj : 4 ≤ q*j := le_trans hj (Nat.le_mul_of_pos_left _ hq)
  have intb : (n+2)/3+2 < 8*(q*j) := by
    change (2*(10*q*j)+2)/3+2 < 8*(q*j)
    rw [show 2*(10*q*j)=20*(q*j) by ring]
    omega
  have realb : (((n+2)/3+2 : ℕ):ℝ) < ((2*j:ℕ):ℝ)*(4*q) := by
    exact_mod_cast (show (n+2)/3+2 < (2*j)*(4*q) by nlinarith only [intb])
  rw [eq] at realb
  linarith only [realb,lb,abs_nonneg (c i (((10*q)*(2*j):ℕ):ℤ))]

/-- For any bounded period, all its ternary templates fail Huber's size
bound on every sufficiently large row in an explicit arithmetic progression.
The template, including its signs and phase, may be chosen anew on each row. -/
theorem periodic_signed_obstruction (p : ℕ) [NeZero p] :
    ∀ᶠ j : ℕ in atTop, ∀ pat : ZMod p → Fin 3,
      let n := 2*(10*p*j)
      let w := fun k : ℕ => ((pat (k:ZMod p)).val:ℤ)-1
      (∑ k ∈ range (n+1), (n.choose k:ℤ)*w k) = (Nat.fib n:ℤ) →
        (n+2)/3+2 < ((range (n+1)).filter fun k => w k ≠ 0).card := by
  let c := fun (pat : ZMod p → Fin 3) (k : ℤ) => ((pat (k:ZMod p)).val:ℝ)-1
  have per (pat : ZMod p → Fin 3) : Function.Periodic (c pat) ((10*p:ℕ):ℤ) := by
    intro k
    simp [c]
  have weight (i : Fin 3) : |(i.val:ℝ)-1| =
      (if (i.val:ℤ)-1 ≠ 0 then (1:ℝ) else 0) := by fin_cases i <;> norm_num
  filter_upwards [adaptive_period_obstruction p (NeZero.pos _) c per] with j hj
  intro pat n w h
  have he : (∑ k ∈ range (n+1), (n.choose k:ℝ)*c pat k) = (Nat.fib n:ℝ) := by
    simpa only [Int.cast_sum,Int.cast_mul,Int.cast_sub,Int.cast_one,Int.cast_natCast,
      c, w] using congrArg ((↑) : ℤ → ℝ) h
  have t := hj pat he
  change (((n+2)/3+2:ℕ):ℝ) < ∑ k ∈ range (n+1), |c pat k| at t
  simp only [c,Int.cast_natCast,weight] at t
  rw [Finset.sum_boole] at t
  exact_mod_cast t

theorem even_center_mass (q : ℕ) (hq : 0<q) (c : ℤ→ℝ)
    (per : Function.Periodic c ((10*q:ℕ):ℤ))
    (many : ∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1),
      ((2*m).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m):ℝ)) :
    4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c k| := (periodic_aux Unit).2.2.1 q hq c per many

theorem odd_center_mass (q : ℕ) (hq : 0<q) (c : ℤ→ℝ)
    (per : Function.Periodic c ((10*q:ℕ):ℤ))
    (many : ∃ᶠ m : ℕ in atTop, (∑ j ∈ range (2*m+1+1),
      ((2*m+1).choose j:ℝ)*c ((j:ℤ)-m)) = (Nat.fib (2*m+1):ℝ)) :
    4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c k| := (periodic_aux Unit).2.2.2.1 q hq c per many

theorem cycle_mass_shift (c : ℤ→ℝ) (L s : ℕ) (hp : Function.Periodic c (L:ℤ)) :
    ∑ k ∈ range L, |c ((k:ℤ)+s)| = ∑ k ∈ range L, |c k| := by
  induction s with
  | zero => simp
  | succ s ih =>
    have u := sum_range_succ' (fun k : ℕ => |c ((k:ℤ)+s)|) L
    have v := sum_range_succ (fun k : ℕ => |c ((k:ℤ)+s)|) L
    rw [add_comm (L:ℤ),hp] at v
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add] at u
    simp only [Nat.cast_succ,show ∀ k : ℕ, (k:ℤ)+(s+1)=k+1+s by intro k; ring]
    linarith only [u,v,ih]


theorem all_rows_cost (q n : ℕ) (hq : 0<q) (hn : 100*q ≤ n) (c : ℤ → ℝ)
    (per : Function.Periodic c ((10*q:ℕ):ℤ)) (hm : 4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c k|) :
    (((n+2)/3+2:ℕ):ℝ) < ∑ k ∈ range (n+1), |c k| := by
  let s := (n+1)/(10*q)
  have hL : 0 < 10*q := by omega
  have full : 10*q*s ≤ n+1 := Nat.mul_div_le _ _
  have nxt : n+1 < 10*q*(s+1) := by
    have h := Nat.mod_lt (n+1) hL
    have h' := Nat.mod_add_div (n+1) (10*q)
    change (n+1) < 10*q*((n+1)/(10*q)+1)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have steps : 10 ≤ s := (Nat.le_div_iff_mul_le hL).mpr (by omega)
  have lb := Nat.mul_le_mul_left q steps
  have num : (n+2)/3+2 < s*(4*q) := by
    have div := Nat.mod_add_div (n+2) 3
    nlinarith only [nxt,lb,hq,div,Nat.zero_le ((n+2)%3)]
  have hv := mul_le_mul_of_nonneg_left hm (show 0≤(s:ℝ) by positivity)
  calc
    _ < (s:ℝ) * (4*(q:ℝ)) := by exact_mod_cast num
    _ ≤ _ := hv
    _ = ∑ k ∈ range (10*q*s), |c k| := (absolute_blocks _ _ c per).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono full)
      (fun k _ _ => abs_nonneg _)


private theorem center_eventually {ι : Type*} [Finite ι] (q : ℕ) (hq : 0<q)
    (c : ι→ℤ→ℝ) (per : ∀ i, Function.Periodic (c i) ((10*q:ℕ):ℤ)) :
    ∀ᶠ m : ℕ in atTop, ∀ i : ι,
      ((∑ k ∈ range (2*m+1), ((2*m).choose k:ℝ)*c i ((k:ℤ)-m)) = (Nat.fib (2*m):ℝ) ∨
        (∑ k ∈ range (2*m+1+1), ((2*m+1).choose k:ℝ)*c i ((k:ℤ)-m)) = (Nat.fib (2*m+1):ℝ)) →
      4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c i k| := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases h : 4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c i k|
  · exact .of_forall fun _ _ => h
  · have en : ∀ᶠ m:ℕ in atTop, ¬ (∑ k ∈ range (2*m+1), ((2*m).choose k:ℝ)*c i ((k:ℤ)-m)) =
        (Nat.fib (2*m):ℝ) := by
      by_contra h'
      exact h (even_center_mass q hq (c i) (per i) h')
    have od : ∀ᶠ m:ℕ in atTop, ¬ (∑ k ∈ range (2*m+1+1), ((2*m+1).choose k:ℝ)*c i ((k:ℤ)-m)) =
        (Nat.fib (2*m+1):ℝ) := by
      by_contra h'
      exact h (odd_center_mass q hq (c i) (per i) h')
    filter_upwards [en,od] with m h₁ h₂
    exact fun e => (e.elim h₁ h₂).elim

/-- Beyond a common finite threshold, every matching template of a finite
periodic family has mean absolute coefficient at least two fifths. -/
theorem all_period_mass {ι : Type*} [Finite ι] (q : ℕ) (hq : 0<q)
    (c : ι→ℤ→ℝ) (per : ∀ i, Function.Periodic (c i) ((10*q:ℕ):ℤ)) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ι,
      (∑ k ∈ range (n+1), (n.choose k:ℝ)*c i k) = (Nat.fib n:ℝ) →
      4*(q:ℝ) ≤ ∑ k ∈ range (10*q), |c i k| := by
  let L := 10*q
  have hL : 0<L := by dsimp [L]; omega
  let shifted (i : ι × Fin L) (z : ℤ) := c i.1 (z+i.2.val)
  have ps (i : ι × Fin L) : Function.Periodic (shifted i) (L:ℤ) := by
    intro z
    dsimp [shifted]
    rw [add_right_comm,per]
  obtain ⟨m₀, hm⟩ := eventually_atTop.mp (center_eventually q hq shifted ps)
  filter_upwards [eventually_ge_atTop (2*m₀)] with n hn
  intro i e
  let m := n/2
  let s : Fin L := ⟨m%L,Nat.mod_lt _ hL⟩
  have eq (k : ℕ) : shifted (i,s) ((k:ℤ)-m) = c i k := by
    change c i ((k:ℤ)-m+(m%L:ℕ))=c i k
    have md : ((m%L:ℕ):ℤ)+(L:ℤ)*(m/L:ℕ)=m := by exact_mod_cast Nat.mod_add_div m L
    rw [show (k:ℤ)-m+(m%L:ℕ)=k-(m/L:ℕ)*(L:ℤ) by linarith only [md]]
    exact (per i).sub_int_mul_eq _
  have mlarge : m₀ ≤ m := by dsimp [m]; omega
  have centered := hm m mlarge (i,s)
  have rr : n=2*m ∨ n=2*m+1 := by dsimp [m]; omega
  have mass : 4*(q:ℝ) ≤ ∑ k ∈ range L, |shifted (i,s) k| := by
    apply centered
    simp_rw [eq]
    rcases rr with v|v
    · exact Or.inl (by rwa [←v])
    · exact Or.inr (by rwa [←v])
  change 4*(q:ℝ) ≤ ∑ k ∈ range L, |c i ((k:ℤ)+s.val)| at mass
  rwa [cycle_mass_shift _ _ _ (per i)] at mass

/-- No bounded-period strategy, even with a row-dependent template, can realize
the conjectured support bound for any sufficiently large row. -/
theorem all_periodic_signed_obstruction (p : ℕ) [NeZero p] :
    ∀ᶠ n : ℕ in atTop, ∀ pat : ZMod p → Fin 3,
      let w := fun k : ℕ => ((pat (k:ZMod p)).val:ℤ)-1
      (∑ k ∈ range (n+1), (n.choose k:ℤ)*w k) = (Nat.fib n:ℤ) →
        (n+2)/3+2 < ((range (n+1)).filter fun k => w k≠0).card := by
  let c := fun (pat : ZMod p → Fin 3) (k : ℤ) => ((pat (k:ZMod p)).val:ℝ)-1
  have per (pat : ZMod p → Fin 3) : Function.Periodic (c pat) ((10*p:ℕ):ℤ) := by
    intro k
    simp [c]
  have weight (i : Fin 3) : |(i.val:ℝ)-1| =
      (if (i.val:ℤ)-1 ≠ 0 then (1:ℝ) else 0) := by fin_cases i <;> norm_num
  filter_upwards [all_period_mass p (NeZero.pos _) c per,eventually_ge_atTop (100*p)] with n hm hn
  intro pat w h
  have he : (∑ k ∈ range (n+1), (n.choose k:ℝ)*c pat k) = (Nat.fib n:ℝ) := by
    simpa only [Int.cast_sum,Int.cast_mul,Int.cast_sub,Int.cast_one,Int.cast_natCast,c,w]
      using congrArg ((↑) : ℤ → ℝ) h
  have bound := all_rows_cost p n (NeZero.pos _) hn (c pat) (per pat) (hm pat he)
  simp only [c,Int.cast_natCast,weight] at bound
  rw [Finset.sum_boole] at bound
  exact_mod_cast bound

theorem periodic_reference_optimal (p : ℕ) [NeZero p] :
    ∀ᶠ n : ℕ in atTop, ∀ pat : ZMod p → Fin 3,
      let w := fun k : ℕ => ((pat (k:ZMod p)).val:ℤ)-1
      (∑ k ∈ range (n+1), (n.choose k:ℤ)*w k) = (Nat.fib n:ℤ) →
        (2*n+4)/5 ≤ ((range (n+1)).filter fun k => w k≠0).card := (periodic_aux Unit).2.2.2.2 p

end Fib743

open Finset
namespace Fib743

/-- Sum a full signed row by folding symmetric positions. -/
theorem folded_value (n : ℕ) (v : ℕ → ℤ) :
    (∑ k ∈ range (n/2+1), (v k + if 2*k=n then 0 else v (n-k)) * (n.choose k:ℤ)) =
      ∑ i ∈ range (n+1), v i*(n.choose i:ℤ) := by
  rw [fold_range n (fun i => v i*(n.choose i:ℤ))]
  apply sum_congr rfl
  intro k hk
  have h : k ≤ n := by have := mem_range.mp hk; omega
  rw [Nat.choose_symm h]
  split <;> ring

/-- An exchange in an odd half-row has zero value precisely when its neighboring
coefficient sums are orthogonal to the preceding even half-row. -/
theorem adjacent_exchange (m : ℕ) (z : ℕ → ℤ) (edge : z (m+1) = 0) :
    ∑ k ∈ range (m+1), z k*((2*m+1).choose k : ℤ) =
      ∑ k ∈ range (m+1), (z k+z (k+1))*((2*m).choose k : ℤ) := by
  simp_rw [add_mul]
  rw [sum_add_distrib]
  have h (k : ℕ) :
      z (k+1)*((2*m+1).choose (k+1) : ℤ) =
        z (k+1)*((2*m).choose (k+1):ℤ) + z (k+1)*((2*m).choose k:ℤ) := by
    rw [Nat.choose_succ_succ,Nat.cast_add]
    ring
  rw [sum_range_succ' (fun k => z k*((2*m+1).choose k:ℤ)),
    sum_range_succ' (fun k => z k*((2*m).choose k:ℤ)),
    sum_range_succ (fun k => z (k+1)*((2*m).choose k:ℤ))]
  simp_rw [h]
  rw [sum_add_distrib,edge]
  simp only [zero_mul,add_zero,Nat.choose_zero_right,Nat.cast_one,mul_one]
  ring

theorem explicit_to_sum (n a b : ℕ) :
    let v := fun k : ℕ => (if k%5=a%5 then (1:ℤ) else 0) -
      (if k%5=b%5 then (1:ℤ) else 0)
    (∑ i : Fin (n+1) with i.val%5=a%5, (n.choose i.val:ℤ)) -
      (∑ i : Fin (n+1) with i.val%5=b%5, (n.choose i.val:ℤ)) =
      ∑ i ∈ range (n+1), v i*(n.choose i:ℤ) := by
  dsimp only
  rw [sum_filter,sum_filter,Fin.sum_univ_eq_sum_range
    (fun k => if k%5=a%5 then (n.choose k:ℤ) else 0),
    Fin.sum_univ_eq_sum_range (fun k => if k%5=b%5 then (n.choose k:ℤ) else 0),
    ←sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  split <;> split <;> simp_all

end Fib743

namespace Fib743

/-- Arbitrarily large primes split the Fibonacci characteristic polynomial.
A prime divisor of M(M+1)-1 works when M is divisible by all small primes. -/
theorem exists_split_prime (b : ℕ) : ∃ p : ℕ, p.Prime ∧ b<p ∧
    ∃ x y : ZMod p, x≠0 ∧ y≠0 ∧ x≠y ∧ x*x=x+1 ∧ y*y=y+1 := by
  let M := 6 * (b+5).factorial
  have hM : 6 ≤ M := by
    have := Nat.factorial_pos (b+5)
    dsimp [M]
    omega
  let N := M*(M+1)-1
  have eN : N+1=M*(M+1) := by
    have : 1 ≤ M*(M+1) := Nat.mul_pos (by omega) (by omega)
    dsimp [N]
    omega
  have hn : N ≠ 1 := by nlinarith
  obtain ⟨p,hp,hpN⟩ := Nat.exists_prime_and_dvd hn
  let : Fact p.Prime := ⟨hp⟩
  have hz : (N:ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).mpr hpN
  have he : (M:ZMod p) * ((M:ZMod p)+1) = 1 := by
    have h := congrArg (fun t : ℕ => (t:ZMod p)) eN.symm
    simpa [hz] using h
  have large : b+5<p := by
    by_contra! hs
    have hdiv : p ∣ M := dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hs) 6
    rw [(ZMod.natCast_eq_zero_iff M p).mpr hdiv] at he
    simp at he
  have h5 : (5 : ZMod p) ≠ 0 := by
    change ((5:ℕ):ZMod p) ≠ 0
    intro z
    have hd := (ZMod.natCast_eq_zero_iff 5 p).mp z
    exact (by omega : ¬p≤5) (Nat.le_of_dvd (by decide) hd)
  refine ⟨p,hp,by omega, (M:ZMod p)+1, -(M:ZMod p), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h,mul_zero] at he
    exact zero_ne_one he
  · intro h
    have z : (M:ZMod p)=0 := neg_eq_zero.mp h
    simp [z] at he
  · intro h
    apply h5
    linear_combination -(4:ZMod p)*he + (2*(M:ZMod p)+1)*h
  · linear_combination he
  · linear_combination he

end Fib743

namespace Fib743
open Finset

private theorem repunit_choose {p : ℕ} [Fact p.Prime] (r : ℕ → ℕ) (h0 : r 0 = 0)
    (hs : ∀ d, r (d+1) = 1+p*r d) (d k : ℕ) :
    ((r d).choose k : ZMod p) = 0 ∨ ((r d).choose k : ZMod p) = 1 := by
  induction d generalizing k with
  | zero =>
    rw [h0]
    cases k <;> simp
  | succ d ih =>
    have hp : 1<p := (Fact.out : p.Prime).one_lt
    have hmod : r (d+1)%p=1 := by rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp]
    have hdiv : r (d+1)/p=r d := by rw [hs, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hp, Nat.zero_add]
    have hl := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (r (d+1)) k p _
    rw [hmod,hdiv] at hl
    have hh := (ZMod.natCast_eq_natCast_iff _ _ _).2 hl
    rw [Nat.cast_mul] at hh
    rw [hh]
    have hsmall : (1:ℕ).choose (k%p) = 0 ∨ (1:ℕ).choose (k%p) = 1 := by
      by_cases h : k%p≤1
      · have : k%p=0 ∨ k%p=1 := by omega
        rcases this with h|h <;> simp [h]
      · exact Or.inl (Nat.choose_eq_zero_of_lt (by omega))
    rcases hsmall with h|h <;> rcases ih (k/p) with v|v <;> simp [h,v]

private theorem binet_difference {p : ℕ} (x y : ZMod p) (hx : x*x=x+1) (hy : y*y=y+1) (n : ℕ) :
    (x-y)*(Nat.fib n : ZMod p) = x^n-y^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more i h₀ h₁ =>
    rw [Nat.fib_add_two, Nat.cast_add, mul_add,h₀,h₁]
    calc
      _ = x^i*(x+1) - y^i*(y+1) := by ring
      _ = _ := by rw [← hx, ← hy]; ring

private theorem repunit_fib {p : ℕ} [Fact p.Prime] (r : ℕ → ℕ) (h0 : r 0 = 0)
    (hs : ∀ d, r (d+1) = 1+p*r d) (x y : ZMod p) (hxy : x≠y)
    (hx : x*x=x+1) (hy : y*y=y+1) (d : ℕ) :
    (Nat.fib (r d) : ZMod p) = Nat.fib d := by
  have powers (z : ZMod p) : z^(r d)=z^d := by
    induction d with
    | zero => simp [h0]
    | succ t ih =>
      have hpow : z^p=z := ZMod.pow_card z
      rw [hs, pow_add, pow_mul, hpow, ih, pow_one, pow_succ, mul_comm]
  apply mul_left_cancel₀ (sub_ne_zero.mpr hxy)
  rw [binet_difference x y hx hy,binet_difference x y hx hy,powers x,powers y]

/-- A row with binomial residues zero and one requires at least the smaller
absolute residue of the target many signed positions, even allowing overlap. -/
theorem cost_residue {p n f : ℕ} [Fact p.Prime] (small : 2*f≤p)
    (hc : ∀ k : ℕ, (n.choose k : ZMod p)=0 ∨ (n.choose k : ZMod p)=1)
    (hf : (Nat.fib n : ZMod p) = f) (a b : Finset (Fin (n+1)))
    (sum : (∑ k ∈ a, (n.choose k.val : ℤ)) - (∑ k ∈ b, (n.choose k.val : ℤ)) = Nat.fib n) :
    f ≤ a.card+b.card := by
  classical
  let c (t : Finset (Fin (n+1))) := (t.filter fun k => (n.choose k.val : ZMod p)=1).card
  have le (t : Finset (Fin (n+1))) : c t ≤ t.card := card_filter_le _ _
  have red (t : Finset (Fin (n+1))) : (∑ k ∈ t, (n.choose k.val : ZMod p)) = c t := by
    calc
      _ = ∑ k ∈ t, (if (n.choose k.val : ZMod p)=1 then (1:ZMod p) else 0) := by
        apply sum_congr rfl; intro k _
        rcases hc k.val with h|h <;> simp [h]
      _ = _ := by simp [c]
  have hs : ((c a : ℕ) : ZMod p) - (c b : ℕ) = Nat.fib n := by
    rw [← red, ←red]
    exact_mod_cast congrArg (fun v : ℤ => (v : ZMod p)) sum
  rw [hf, sub_eq_iff_eq_add] at hs
  have hh : ((c a : ℕ) : ZMod p) = ((f+c b : ℕ) : ZMod p) := by simpa using hs
  by_contra! h
  have ha := le a
  have hb := le b
  have hp := (Fact.out : p.Prime).pos
  have hv := congrArg ZMod.val hh
  rw [ZMod.val_natCast_of_lt (show c a<p by omega),
    ZMod.val_natCast_of_lt (show f+c b<p by omega)] at hv
  omega

theorem repunit_cost {p : ℕ} (hp : p.Prime) (r : ℕ → ℕ) (h0 : r 0 = 0)
    (hs : ∀ d, r (d+1) = 1+p*r d) (x y : ZMod p) (hxy : x≠y)
    (hx : x*x=x+1) (hy : y*y=y+1) (d : ℕ) (small : 2*Nat.fib d≤p)
    (a b : Finset (Fin (r d+1)))
    (sum : (∑ k ∈ a, ((r d).choose k.val : ℤ)) - (∑ k ∈ b, ((r d).choose k.val : ℤ)) = Nat.fib (r d)) :
    Nat.fib d ≤ a.card+b.card := by
  let : Fact p.Prime := ⟨hp⟩
  exact cost_residue small (repunit_choose r h0 hs d) (repunit_fib r h0 hs x y hxy hx hy d) a b sum

end Fib743

namespace Fib743
open Finset

/-- The minimum number of signed entries is unbounded, even if the positive and
negative families are permitted to overlap. The constructed row can exceed
any independently prescribed threshold. -/
theorem cost_unbounded (B T : ℕ) : ∃ n : ℕ, T<n ∧ ∀ a b : Finset (Fin (n+1)),
    (∑ k ∈ a, (n.choose k.val : ℤ)) - (∑ k ∈ b, (n.choose k.val : ℤ)) = Nat.fib n →
      B < a.card + b.card := by
  let d := max B T + 2
  have hBd : B < Nat.fib d := by
    have hh := Nat.le_fib_add_one d
    have := Nat.le_max_left B T
    dsimp [d] at hh ⊢
    omega
  obtain ⟨p,hp,hbig,x,y,_,_,hxy,hx,hy⟩ := exists_split_prime (2*Nat.fib d)
  let r : ℕ → ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun _ z : ℕ => 1+p*z)
  have h0 : r 0 = 0 := rfl
  have hs (i : ℕ) : r (i+1) = 1+p*r i := rfl
  have hrow (i : ℕ) : i≤r i := by
    induction i with
    | zero => omega
    | succ i ih => rw [hs]; have ph := hp.one_lt; nlinarith
  refine ⟨r d, ?_, ?_⟩
  · have hh := hrow d
    have hmax := Nat.le_max_right B T
    dsimp [d] at hh ⊢
    omega
  · intro a b h
    exact hBd.trans_le (repunit_cost hp r h0 hs x y hxy hx hy d hbig.le a b h)

end Fib743

namespace Fib743
open Finset

/-- Explicit signed representations, encoded in base five and checked in Lean. -/
theorem initial_and_selected_checked : ∀ n : ℕ, (n < 147 ∨ n ∈ ([148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 172, 173, 174, 175, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 201, 202, 203, 204, 205] : List ℕ)) →
    ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
    (∑ k ∈ p, (n.choose k.val : ℤ)) - (∑ k ∈ m, (n.choose k.val : ℤ)) = (Nat.fib n : ℤ) ∧
    p.card + m.card ≤ (n+2)/3+2 := by
  let quickChoose (n k : ℕ) : ℕ :=
    Nat.rec 1 (fun j prev => prev * (n-j) / (j+1)) k

  have quickChoose_eq (n k : ℕ) : quickChoose n k = n.choose k := by
    induction k with
    | zero => simp [quickChoose]
    | succ k ih =>
      change quickChoose n k * (n-k) / (k+1) = _
      rw [ih, ← Nat.choose_succ_right_eq]
      exact Nat.mul_div_cancel _ (Nat.succ_pos _)


  let weightAt (code k : ℕ) : ℤ := ((code / 5^k % 5 : ℕ) : ℤ) - 2

  let rowCheck (n code : ℕ) : Bool := decide (
    (∀ i : Fin (n/2+1), (weightAt code i).natAbs ≤ (if 2*i.val=n then 1 else 2)) ∧
    (∑ i ∈ range (n/2+1), weightAt code i * (Int.ofNat (quickChoose n i))) = (Nat.fastFib n : ℤ) ∧
    (∑ i ∈ range (n/2+1), (weightAt code i).natAbs) ≤ (n+2)/3+2)

  let represented (n : ℕ) : Prop := ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
    (∑ i ∈ p, (n.choose i.val : ℤ)) - (∑ i ∈ m, (n.choose i.val : ℤ)) = (Nat.fib n : ℤ) ∧
    p.card + m.card ≤ (n+2)/3+2

  have rowCheck_sound (n code : ℕ) (hc : rowCheck n code = true) : represented n := by
    obtain ⟨hcap,ht,hcost⟩ := of_decide_eq_true hc
    apply (folded_iff n _ _).mp
    refine ⟨weightAt code, fun k hk => hcap ⟨k,by omega⟩, ?_, hcost⟩
    simpa only [Int.ofNat_eq_natCast,quickChoose_eq,Nat.fastFib_eq] using ht

  let codes0 : List ℕ := [2, 3, 13, 16, 66, 82, 331, 411, 1658, 2058]
  have checked0 : ∀ i : Fin 10, represented (0+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (0+i) (codes0[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes0]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes10 : List ℕ := [8292, 10293, 41463, 51466, 207316, 257332, 1036581, 1286661, 5182908, 6433308]
  have checked10 : ∀ i : Fin 10, represented (10+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (10+i) (codes10[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes10]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes20 : List ℕ := [25914542, 32166543, 129572713, 160832716, 647863566, 804163582, 3239317831, 4020817911, 16196589158, 20104089558]
  have checked20 : ∀ i : Fin 10, represented (20+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (20+i) (codes20[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes20]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes30 : List ℕ := [80982945792, 100520447793, 404914728963, 526784113966, 2024573644816, 2513011194832, 11885180189187, 12565055974161, 66714467629191, 61635141273433]
  have checked30 : ∀ i : Fin 10, represented (30+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (30+i) (codes30[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes30]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes40 : List ℕ := [253071705602042, 329220922976038, 1271286017075317, 1632266479342216, 5139548620020337, 8245718383401082, 28047256541990311, 40879433204094686, 151281368776404062, 197075213010749263]
  have checked40 : ∀ i : Fin 10, represented (40+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (40+i) (codes40[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes40]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes50 : List ℕ := [792728810230992667, 983475861164979043, 3689031447160964763, 6061792532010334186, 25504272842429566562, 14132413832705820287, 93368691700714648312, 65949605727915047811, 650423783704223141466, 709731345017199804683]
  have checked50 : ∀ i : Fin 10, represented (50+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (50+i) (codes50[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes50]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes60 : List ℕ := [3037650064500414782792, 2506551122672680038963, 16073816925271606053821, 15219002393881002930112, 61932901541365323222941, 63742107625810082974067, 291151613130598677053485, 171240504427781352836561, 1879315825721625120122912, 2144921554284859997132808]
  have checked60 : ∀ i : Fin 10, represented (60+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (60+i) (codes60[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes60]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes70 : List ℕ := [8314566809347153228710792, 7271672283525778552072588, 35225956350545827114262817, 22409964281128286747407216, 184577608841752963356413566, 254071786254453865350538582, 981094784705037979374802206, 1198187040465589102280271036, 4605644098645543249828747812, 2512541102672910885570899033]
  have checked70 : ∀ i : Fin 10, represented (70+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (70+i) (codes70[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes70]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes80 : List ℕ := [31817631300823927742797301663, 24552306654361966825327067793, 112231651705339192434770413963, 159088757347190980912055804591, 615578891244214732009878019816, 831809296553522061404425555912, 3096546692276746034701332925936, 3933206607303160562503236510311, 8353839709887650819774104976444, 9481552115286078210831186844213]
  have checked80 : ∀ i : Fin 10, represented (80+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (80+i) (codes80[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes80]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes90 : List ℕ := [72145652178170350339858482597692, 49435313822012394784621649336567, 378088290158117849093245530554568, 328946588735673580922317163319814, 1775309124577250464681428834941591, 1922956375836846678992842336464067, 7443922273221138269681778011148447, 10153940004495617598089218088945666, 44414514029914533404111830297948558, 59170017831746730178583756909570287]
  have checked90 : ∀ i : Fin 10, represented (90+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (90+i) (codes90[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes90]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes100 : List ℕ := [137352248645818697313585232786242062, 204346702415177162820192368063008313, 1021981529823749978130555349749200317, 1550758384574257117073285275211547841, 3266259612245805018933821028676660962, 7682652153956269239217066567749744832, 25655080098768148843113164865061584061, 38768982513814311045035505318002224161, 138859618963142800426691750717436560312, 183204277284917526189535890914242761433]
  have checked100 : ∀ i : Fin 10, represented (100+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (100+i) (codes100[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes100]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes110 : List ℕ := [704902110442817246999887155551639489163, 914158320331017871147782545094856385293, 4064051996124365657884329652034163137817, 1860086123638225866016132764840929141186, 18954836268185542717102979421586194611162, 22631984457452878889351626141119653772957, 94507280372522691910843937639844508849081, 118826067902655799721833335293838727885311, 605809758458804026638398603301750854095916, 612678493112775867057454616803659594895312]
  have checked110 : ∀ i : Fin 10, represented (110+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (110+i) (codes110[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes110]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes120 : List ℕ := [2995522613287611416366415832658164879085936, 2863627743068374539434408707379377909340313, 15171847090793734280576463501214802620500796, 14338957532443756607763977967019982297457716, 56985930489547296959062563592092477625892316, 58690903717818504411574763507257430543570942, 288544209640164913267771469868612297868945435, 73153311339170314568548875066132925373475911, 882570046939845603432308192996340410962713941, 796706446290018543142748531549685262231274683]
  have checked120 : ∀ i : Fin 10, represented (120+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (120+i) (codes120[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes120]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes130 : List ℕ := [7227318535503414402302872851165171623170898292, 6668551405342194108575944311626653665381788418, 44614995481379794799625233520357851183764654567, 34230878494718846540305241671591421402213485942, 183395246624274713826619846086652047502076001086, 153191289778158236370105919874163885877807711567, 847011994802455474987702617886865949843080799687, 901238735350071844428128782938858934256002524061, 4224322194069207817672540947874693327705573211562, 5319283642094925091381262356879213480021413144808]
  have checked130 : ∀ i : Fin 10, represented (130+i.val) := by
    have h : (List.range 10).all (fun i => rowCheck (130+i) (codes130[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes130]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  let codes140 : List ℕ := [22910612348239608113194805745888796572556965898292, 19482304227545602279013660351280135393874213885293, 96067197132650976766244119988997191212903237307088, 112601085995490679053435906688397377275319206438564, 522358686429832230772704214053656668901468149476470, 692023444019002051061102443782300625855442515101082, 2856022958425824133649374743702281009470781860054286]
  have checked140 : ∀ i : Fin 7, represented (140+i.val) := by
    have h : (List.range 7).all (fun i => rowCheck (140+i) (codes140[i]?.getD 0)) = true := by
      dsimp only [rowCheck,quickChoose,weightAt,codes140]
      decide +kernel
    intro i
    exact rowCheck_sound _ _ (List.all_eq_true.mp h _ (List.mem_range.mpr i.isLt))

  have verified_initial (n : ℕ) (hn : n < 147) : represented n := by
    by_cases h10 : n < 10
    · have e : 0+(n-0)=n := by omega
      exact e ▸ checked0 ⟨n-0,by omega⟩
    by_cases h20 : n < 20
    · have e : 10+(n-10)=n := by omega
      exact e ▸ checked10 ⟨n-10,by omega⟩
    by_cases h30 : n < 30
    · have e : 20+(n-20)=n := by omega
      exact e ▸ checked20 ⟨n-20,by omega⟩
    by_cases h40 : n < 40
    · have e : 30+(n-30)=n := by omega
      exact e ▸ checked30 ⟨n-30,by omega⟩
    by_cases h50 : n < 50
    · have e : 40+(n-40)=n := by omega
      exact e ▸ checked40 ⟨n-40,by omega⟩
    by_cases h60 : n < 60
    · have e : 50+(n-50)=n := by omega
      exact e ▸ checked50 ⟨n-50,by omega⟩
    by_cases h70 : n < 70
    · have e : 60+(n-60)=n := by omega
      exact e ▸ checked60 ⟨n-60,by omega⟩
    by_cases h80 : n < 80
    · have e : 70+(n-70)=n := by omega
      exact e ▸ checked70 ⟨n-70,by omega⟩
    by_cases h90 : n < 90
    · have e : 80+(n-80)=n := by omega
      exact e ▸ checked80 ⟨n-80,by omega⟩
    by_cases h100 : n < 100
    · have e : 90+(n-90)=n := by omega
      exact e ▸ checked90 ⟨n-90,by omega⟩
    by_cases h110 : n < 110
    · have e : 100+(n-100)=n := by omega
      exact e ▸ checked100 ⟨n-100,by omega⟩
    by_cases h120 : n < 120
    · have e : 110+(n-110)=n := by omega
      exact e ▸ checked110 ⟨n-110,by omega⟩
    by_cases h130 : n < 130
    · have e : 120+(n-120)=n := by omega
      exact e ▸ checked120 ⟨n-120,by omega⟩
    by_cases h140 : n < 140
    · have e : 130+(n-130)=n := by omega
      exact e ▸ checked130 ⟨n-130,by omega⟩
    have e : 140+(n-140)=n := by omega
    exact e ▸ checked140 ⟨n-140,by omega⟩
  let more : List (ℕ × ℕ) := [
    (148, 9008398014997282080051479239819142462035476703310966),
    (149, 17431411269708734346650157859841265529843984947839558),
    (150, 87349676917485715272788068363849919059988357514088938),
    (151, 56013359895047823971137191071628876760764248608401713),
    (152, 329782612189159137877007046518119323392713761110335942),
    (153, 463212666756185059787250688795754937131567117310049067),
    (154, 1126192338961800672559092510172921877592782089040017212),
    (155, 1633159460581515972642920712484971014103154336606136447),
    (156, 7615599481602908588007418147860298250421648026737851585),
    (157, 5705094634951472581945020816540632692142724990446586561),
    (158, 38711035212034725944151221593660593271729149972485651658),
    (159, 61184037866859973380814706922122102812677488291881433308),
    (160, 223337859085675095177704202483686787549337150368040192563),
    (161, 289421962235706039386824912414410567377413504410152850936),
    (162, 1100279286914455447362441006386327961939722280502309510213),
    (163, 1361544964925833339092223112052072819004553536422712238966),
    (164, 5500332495205218411777687977676799184176653608340514617191),
    (165, 6813673317194744121534028138854242588887950220083625551436),
    (166, 27917292733983016962266648092268405422640278955606059871581),
    (167, 36189272238146089812528006585014113068159366750138297879061),
    (168, 129167435424167502314314900878002082172679215678634652466562),
    (169, 178970324789027928497483945687596968237587064318434692380888),
    (170, 689658525069531073749682127172030371439259144239578453648917),
    (172, 3270469165109412305133344434616380701715934654569442756682693),
    (173, 3179397527057265922682398880043023861071371349184769007167681),
    (174, 17485565389946777638142310705588102242594867271562484499360962),
    (175, 16941708818604568600688541522240827752331512743249890749101058),
    (177, 42512356953022459548261354800970932663480992170572347984977081),
    (178, 410141983710564116616673492458537027176994506495679854164728558),
    (179, 429530462940243994636534824882326239276153486224412157899761418),
    (180, 2013073350329241388643655083464364264855107022387170553586944696),
    (181, 2051527253036428232632722839897850790111633952661751172473616713),
    (182, 7674034749403640245435013396901194198460864213854549789489148442),
    (183, 10905359561938975545131636918340589742798135902756455636601020216),
    (184, 53781549352249710175371838633965223321014575236514233621272845337),
    (185, 52070358780453878741735095431133217184184784483246083443910647957),
    (186, 212080668631702050256199435419432208503210923960238321150463536581),
    (201, 20935635555154999891277671092390113350268656526051593879938157649354043),
    (202, 99932871234276593668333453515213367234386091392544527503255087287775838),
    (203, 129910094541538760815451342986709822782395814465558106142241293617863966),
    (204, 523315381828972866659728960189426049285786682063050334841488425940832316),
    (205, 652311875077486705260055458895486974535705644469952691062806773265101082)]
  have checkedMore : more.all (fun p => rowCheck p.1 p.2) = true := by
    dsimp only [more,rowCheck,quickChoose,weightAt]
    decide +kernel
  intro n hn
  rcases hn with h | h
  · exact verified_initial n h
  · have mem : n ∈ more.map Prod.fst := by exact h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
    exact rowCheck_sound _ _ (List.all_eq_true.mp checkedMore p hp)

theorem initial_checked : ∀ n < 147, ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
    (∑ k ∈ p, (n.choose k.val : ℤ)) - (∑ k ∈ m, (n.choose k.val : ℤ)) = (Nat.fib n : ℤ) ∧
    p.card + m.card ≤ (n+2)/3+2 := by
  intro n hn
  exact initial_and_selected_checked n (Or.inl hn)

end Fib743

open Finset
namespace Fib743

theorem baseline (n : ℕ) :
    let a := n/2 + if n%2=0 then 1 else 0
    let b := n/2+2
    let v := fun k : ℕ => (if k%5=a%5 then (1:ℤ) else 0) - (if k%5=b%5 then (1:ℤ) else 0)
    ∑ k ∈ range (n/2+1), (v k + if 2*k=n then 0 else v (n-k))*(n.choose k:ℤ) = (Nat.fib n:ℤ) := by
  dsimp only
  rw [folded_value,←explicit_to_sum]
  exact (reference_explicit n).2.1

end Fib743
namespace OMA.R_oeis_a399743_R1
open Fib743

/-- In an even row, alter the reflected residue-class coefficients by a vector
orthogonal to the half-row of binomial coefficients. The center has capacity one. -/
def H1 : Prop := ∀ m : ℕ, 147 ≤ 2*m →
  let v := fun k : ℕ => (if k%5=(m+1)%5 then (1:ℤ) else 0) - (if k%5=(m+2)%5 then (1:ℤ) else 0)
  let r := fun k : ℕ => v k + if k=m then 0 else v (2*m-k)
  ∃ z : ℕ → ℤ, (∑ k ∈ range (m+1), z k*((2*m).choose k:ℤ)) = 0 ∧
    (∀ k ≤ m, (r k+z k).natAbs ≤ if k=m then 1 else 2) ∧
    (∑ k ∈ range (m+1), (r k+z k).natAbs) ≤ (2*m+2)/3+2

/-- An odd-row exchange uses the same even binomial weights, this time
multiplying the sum of neighboring changes. Every folded position has capacity two. -/
def H2 : Prop := ∀ m : ℕ, 147 ≤ 2*m+1 →
  let v := fun k : ℕ => (if k%5=m%5 then (1:ℤ) else 0) - (if k%5=(m+2)%5 then (1:ℤ) else 0)
  let r := fun k : ℕ => v k + v (2*m+1-k)
  ∃ z : ℕ → ℤ, z (m+1)=0 ∧ (∑ k ∈ range (m+1), (z k+z (k+1))*((2*m).choose k:ℤ)) = 0 ∧
    (∀ k ≤ m, (r k+z k).natAbs ≤ 2) ∧
    (∑ k ∈ range (m+1), (r k+z k).natAbs) ≤ (2*m+3)/3+2

theorem large_rows (h1 : H1) (h2 : H2) (n : ℕ) (hn : 147≤n) :
    ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
      (∑ i ∈ p, (n.choose i.val:ℤ))-(∑ i ∈ m, (n.choose i.val:ℤ))=(Nat.fib n:ℤ) ∧
      p.card+m.card≤(n+2)/3+2 := by
  apply (folded_iff n _ _).mp
  obtain ⟨m, rfl | rfl⟩ : ∃ m : ℕ, n=2*m ∨ n=2*m+1 := ⟨n/2,by omega⟩
  · let v := fun k : ℕ => (if k%5=(m+1)%5 then (1:ℤ) else 0) - (if k%5=(m+2)%5 then (1:ℤ) else 0)
    let r := fun k : ℕ => v k + if k=m then 0 else v (2*m-k)
    obtain ⟨z,hz,hcap,hcost⟩ := h1 m hn
    have bv : ∑ k ∈ range (m+1), r k*((2*m).choose k:ℤ) = Nat.fib (2*m) := by
      simpa only [r,v,Nat.mul_div_cancel_left _ (by decide : 0<2),Nat.mul_mod_right,
        ↓reduceIte,show ∀ k : ℕ, 2*k=2*m ↔ k=m by intro k; omega] using baseline (2*m)
    refine ⟨fun k => r k+z k, ?_, ?_, ?_⟩
    · intro k hk
      simpa only [show 2*k=2*m ↔ k=m by omega] using hcap k (by omega)
    · rw [show 2*m/2=m by omega]
      simp_rw [add_mul,sum_add_distrib,bv,hz,add_zero]
    · simpa only [show 2*m/2=m by omega] using hcost
  · let v := fun k : ℕ => (if k%5=m%5 then (1:ℤ) else 0) - (if k%5=(m+2)%5 then (1:ℤ) else 0)
    let r := fun k : ℕ => v k + v (2*m+1-k)
    obtain ⟨z,edge,hz,hcap,hcost⟩ := h2 m hn
    have bv : ∑ k ∈ range (m+1), r k*((2*m+1).choose k:ℤ) = Nat.fib (2*m+1) := by
      simpa only [r,v,show (2*m+1)/2=m by omega,show (2*m+1)%2=1 by omega,one_ne_zero,
        ↓reduceIte,add_zero,show ∀ k : ℕ, ¬ 2*k=2*m+1 by intro k; omega] using baseline (2*m+1)
    have zero := (adjacent_exchange m z edge).trans hz
    refine ⟨fun k => r k+z k, ?_, ?_, ?_⟩
    · intro k hk
      simpa only [show ¬ 2*k=2*m+1 by omega,↓reduceIte] using hcap k (by omega)
    · rw [show (2*m+1)/2=m by omega]
      simp_rw [add_mul,sum_add_distrib,bv,zero,add_zero]
    · simpa only [show (2*m+1)/2=m by omega,show 2*m+1+2=2*m+3 by omega] using hcost

end OMA.R_oeis_a399743_R1

open Finset
namespace Fib743

/-- Any admissible folded representation differs from a given equal-value
reference by an integer relation; the exchange can be zero-padded beyond the center. -/
theorem exchange_of_witness (n : ℕ) (r : ℕ → ℤ)
    (hr : ∑ k ∈ range (n/2+1), r k*(n.choose k:ℤ) = Nat.fib n)
    (h : ∃ p m : Finset (Fin (n+1)), Disjoint p m ∧
      (∑ i ∈ p, (n.choose i.val:ℤ))-(∑ i ∈ m, (n.choose i.val:ℤ))=(Nat.fib n:ℤ) ∧
      p.card+m.card≤(n+2)/3+2) :
    ∃ z : ℕ → ℤ, z (n/2+1) = 0 ∧
      (∑ k ∈ range (n/2+1), z k*(n.choose k:ℤ)) = 0 ∧
      (∀ k ≤ n/2, (r k+z k).natAbs ≤ if 2*k=n then 1 else 2) ∧
      (∑ k ∈ range (n/2+1), (r k+z k).natAbs) ≤ (n+2)/3+2 := by
  obtain ⟨w,hc,hv,hb⟩ := (folded_iff _ _ _).mpr h
  let z (k : ℕ) := if k≤n/2 then w k-r k else 0
  have hinner (k : ℕ) (hk : k ∈ range (n/2+1)) : z k = w k-r k := by
    simp [z,Nat.lt_succ_iff.mp (mem_range.mp hk)]
  refine ⟨z,by simp [z],?_,?_,?_⟩
  · calc
      _ = ∑ k ∈ range (n/2+1), (w k-r k)*(n.choose k:ℤ) :=
        sum_congr rfl fun k hk => by rw [hinner k hk]
      _ = 0 := by simp_rw [sub_mul,sum_sub_distrib,hv,hr,sub_self]
  · intro k hk
    simpa [z,hk] using hc k hk
  · convert hb using 1
    apply sum_congr rfl
    intro k hk
    simp [hinner k hk]

end Fib743

namespace OMA.R_oeis_a399743_R1
open Fib743

theorem exchanges_necessary (all_rows : type_of% @OMA.S_oeis_a399743.main) : H1 ∧ H2 := by
  constructor
  · intro m _
    let v := fun k : ℕ => (if k%5=(m+1)%5 then (1:ℤ) else 0) - (if k%5=(m+2)%5 then (1:ℤ) else 0)
    let r := fun k : ℕ => v k + if k=m then 0 else v (2*m-k)
    have bv : ∑ k ∈ range ((2*m)/2+1), r k*((2*m).choose k:ℤ) = Nat.fib (2*m) := by
      simpa only [r,v,Nat.mul_div_cancel_left _ (by decide : 0<2),Nat.mul_mod_right,
        ↓reduceIte,show ∀ k : ℕ, 2*k=2*m ↔ k=m by intro k; omega] using baseline (2*m)
    obtain ⟨z,_,zero,cap,cost⟩ := exchange_of_witness _ r bv (all_rows _)
    refine ⟨z,?_,?_,?_⟩
    · simpa only [show 2*m/2=m by omega] using zero
    · intro k hk
      simpa only [show 2*k=2*m ↔ k=m by omega] using cap k (by omega)
    · simpa only [show 2*m/2=m by omega] using cost
  · intro m _
    let v := fun k : ℕ => (if k%5=m%5 then (1:ℤ) else 0) - (if k%5=(m+2)%5 then (1:ℤ) else 0)
    let r := fun k : ℕ => v k + v (2*m+1-k)
    have bv : ∑ k ∈ range ((2*m+1)/2+1), r k*((2*m+1).choose k:ℤ) = Nat.fib (2*m+1) := by
      simpa only [r,v,show (2*m+1)/2=m by omega,show (2*m+1)%2=1 by omega,one_ne_zero,
        ↓reduceIte,add_zero,show ∀ k : ℕ, ¬ 2*k=2*m+1 by intro k; omega] using baseline (2*m+1)
    obtain ⟨z,edge,zero,cap,cost⟩ := exchange_of_witness _ r bv (all_rows _)
    simp only [show (2*m+1)/2=m by omega] at edge zero cap cost
    refine ⟨z,edge,(adjacent_exchange m z edge).symm.trans zero,?_,?_⟩
    · intro k hk
      simpa only [show ¬ 2*k=2*m+1 by omega,↓reduceIte] using cap k hk
    · simpa only [show 2*m+1+2=2*m+3 by omega] using cost

end OMA.R_oeis_a399743_R1

namespace OMA.R_oeis_a399743_R1
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a399743.main := by
  intro h1 h2 n
  by_cases hn : n < 147
  · exact Fib743.initial_checked n hn
  · exact large_rows h1 h2 n (by omega)
end OMA.R_oeis_a399743_R1
