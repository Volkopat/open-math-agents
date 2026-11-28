import OMAStatements.S_mo_338415
import Mathlib

/-!
# Strict and horizontal obstructions in Grahl's forest-fire sequence

This is a reduction of Charles Greathouse's recurrence question for the sequence
of Jack Grahl. The defining MathOverflow discussion is
https://mathoverflow.net/questions/338415 and the original sequence is
https://oeis.org/A229037. All positions here are indexed from zero.

A strictly descending blocker of one is an earlier pair i<j satisfying
n+i=2j and a(i)+1=2a(j), with a(j)>1. Among endpoints escaping all such pairs,
the native greedy selection of ones only has to exclude horizontal progressions.
If a prefix contains r ones, it has at most r+binomial(r,2) escaping endpoints.
We split strict blockers at lag two. Every logarithmic window has an endpoint
escaping these two lags. Lag three already suffices for permanent coverage in
a sublinear progression-free comparison sequence. Every finite native prefix
also admits a progression-free extension with permanent coverage at lag at
most three. These extensions impose only the listed avoidance conditions.

Additional results bound the cost of blocking at fixed origins using Roth's
theorem, and construct long sample progressions whose blockers must reach
outside the sample. The two residual assertions remain open.
-/

namespace Forest338
open OMA.S_mo_338415

private theorem admissible_bounded (n : ℕ) : ∃ m : ℕ, m≤n/2+1 ∧
    0 < m ∧ ∀ k : Fin (n/2), (m:ℤ)-a (n-(k+1)) ≠ (a (n-(k+1)):ℤ)-a (n-2*(k+1)) := by
  classical
  let f (k : Fin (n/2)) : ℤ := 2*(a (n-(k+1)):ℤ)-a (n-2*(k+1))
  let E := Finset.univ.image f
  have hc : E.card ≤ n/2 := by simpa [E] using (Finset.card_image_le (f:=f) (s:=Finset.univ))
  let I := Finset.Icc (1:ℤ) ((n/2:ℕ)+1)
  have hI : I.card=n/2+1 := by simp [I]; omega
  have hlt : E.card < I.card := by omega
  obtain ⟨v,hv,hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨h1,h2⟩ := Finset.mem_Icc.mp hv
  refine ⟨v.toNat,by omega,by omega,?_⟩
  intro k hk
  apply hx
  apply Finset.mem_image.mpr
  refine ⟨k,Finset.mem_univ _,?_⟩
  dsimp [f]
  omega

private theorem greedy_spec (n : ℕ) :
    0 < a n ∧ ∀ k : Fin (n/2), (a n:ℤ)-a (n-(k+1)) ≠ (a (n-(k+1)):ℤ)-a (n-2*(k+1)) := by
  obtain ⟨m,_,hm⟩ := admissible_bounded n
  have h := Nat.sInf_mem (s:={v : ℕ | 0 < v ∧ ∀ k : Fin (n/2),
    (v:ℤ)-a (n-(k+1)) ≠ (a (n-(k+1)):ℤ)-a (n-2*(k+1))}) ⟨m,hm⟩
  simpa only [Set.mem_ofPred_eq, ← a.eq_1 n] using h

theorem positive (n : ℕ) : 0 < a n := (greedy_spec n).1

theorem upper (n : ℕ) : a n≤n/2+1 := by
  obtain ⟨m,hm,hs⟩ := admissible_bounded n
  rw [a.eq_1]
  exact le_trans (Nat.sInf_le hs) hm

theorem avoids (n k : ℕ) (hk : 0 < k) (hb : 2*k≤n) :
    (a n:ℤ)-a (n-k) ≠ (a (n-k):ℤ)-a (n-2*k) := by
  let i : Fin (n/2) := ⟨k-1,by omega⟩
  simpa only [i,show k-1+1=k by omega] using (greedy_spec n).2 i

theorem blocked {n m : ℕ} (hm : 0 < m) (h : m < a n) :
    ∃ k : ℕ, 0 < k ∧ 2*k≤n ∧ (m:ℤ)-a (n-k)=(a (n-k):ℤ)-a (n-2*k) := by
  by_contra! bad
  have hs : 0 < m ∧ ∀ i : Fin (n/2), (m:ℤ)-a (n-(i+1)) ≠ (a (n-(i+1)):ℤ)-a (n-2*(i+1)) := by
    refine ⟨hm,fun i => bad (i+1) (by omega) (by omega)⟩
  have le : a n ≤ m := by
    rw [a.eq_1]
    exact Nat.sInf_le hs
  omega

end Forest338

namespace Forest338
open OMA.S_mo_338415
open Finset
open scoped Classical

/-- At an eligible site only a horizontal pair of previous ones can stop the greedy
rule. Eligibility here excludes all strictly descending extrapolations to one. -/
theorem one_iff_no_pair (n : ℕ) :
    a n=1 ↔ ¬ ∃ i j : ℕ, i < j ∧ n+i=2*j ∧ a i+1=2*a j := by
  constructor
  · rintro ha ⟨i,j,hij,hh,hv⟩
    have hg := avoids n (j-i) (by omega) (by omega)
    rw [show n-(j-i)=j by omega,show n-2*(j-i)=i by omega,ha] at hg
    omega
  · intro h
    have ha := positive n
    by_contra hh
    obtain ⟨k,hk,hb,hv⟩ := blocked (m:=1) (by decide) (show 1 < a n by omega)
    apply h
    exact ⟨n-2*k,n-k,by omega,by omega,by omega⟩

theorem eligible_site (n : ℕ)
    (e : ¬∃ i j : ℕ, i < j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j) :
    a n=1 ∨ ∃ i j : ℕ, i < j ∧ n+i=2*j ∧ a i=1 ∧ a j=1 := by
  by_cases h : a n=1
  · exact Or.inl h
  · obtain ⟨i,j,hij,hi,hv⟩ := Classical.not_not.mp (mt (one_iff_no_pair n).mpr h)
    have hj : a j=1 := by
      have := positive j
      by_contra hn
      exact e ⟨i,j,hij,hi,by omega,hv⟩
    exact Or.inr ⟨i,j,hij,hi,by omega,hj⟩

/-- With r ones in the first N terms, at most r + binomial(r,2) sites are
uncovered by strictly descending pairs. This quantitative estimate includes
the greedy rejections caused by two earlier ones. -/
theorem eligible_count (N : ℕ) :
    let W := (range N).filter fun i => a i=1
    ((range N).filter fun n => ¬∃ i j : ℕ, i < j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j).card
      ≤ W.card+W.card.choose 2 := by
  classical
  dsimp only
  let W := (range N).filter fun i => a i=1
  let B := (W ×ˢ W).filter fun p => p.1 < p.2
  let E := B.image fun p => 2*p.2-p.1
  calc
    _ ≤ (W∪E).card := card_le_card (by
      intro n hn
      obtain ⟨hN,he⟩ := mem_filter.mp hn
      have hn' := mem_range.mp hN
      rcases eligible_site n he with hw|⟨i,j,hij,hi,wi,wj⟩
      · exact mem_union_left _ (mem_filter.mpr ⟨hN,hw⟩)
      · apply mem_union_right
        apply mem_image.mpr
        refine ⟨(i,j),mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,hij⟩,by dsimp; omega⟩
        · exact mem_filter.mpr ⟨mem_range.mpr (by omega),wi⟩
        · exact mem_filter.mpr ⟨mem_range.mpr (by omega),wj⟩)
    _ ≤ W.card+E.card := card_union_le _ _
    _ ≤ W.card+B.card := Nat.add_le_add_left card_image_le _
    _ = _ := by rw [show B.card=W.card.choose 2 from card_product_filter_lt]

/-- The original infinitude question is precisely the failure of cofinite
coverage by strictly descending pairs. Horizontal obstructions cost at most
twice the last position of a one when the set of ones is finite. -/
theorem infinite_sites_iff :
    {n : ℕ | a n=1}.Infinite ↔
      ∀ N : ℕ, ∃ n : ℕ, N≤n ∧ ¬∃ i j : ℕ, i < j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j := by
  constructor
  · intro h N
    obtain ⟨n,hn,hle⟩ := h.exists_gt N
    refine ⟨n,hle.le,?_⟩
    rintro ⟨i,j,hij,hi,_,hv⟩
    exact (one_iff_no_pair n).mp hn ⟨i,j,hij,hi,hv⟩
  · intro h hf
    obtain ⟨M,hM⟩ := hf.bddAbove
    obtain ⟨n,hn,he⟩ := h (2*M+1)
    rcases eligible_site n he with hw|⟨i,j,_,hij,_,hj⟩
    · have := hM (show n∈{t : ℕ | a t=1} from hw); omega
    · have := hM (show j∈{t : ℕ | a t=1} from hj); omega

end Forest338

namespace Forest338
open OMA.S_mo_338415
open Finset
open scoped Classical

/-- A softer counting route: the surplus of long-lag-free sites over those
that have a short strict blocker is bounded by a triangular number in the
number of actual ones. No hypothesis of eventual short-lag redundancy is needed. -/
theorem long_free_count (N : ℕ) :
    let W := (range N).filter fun i => a i=1
    let L := (range N).filter fun n => ¬∃ i j : ℕ,
      i+3 ≤ j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j
    let S := L.filter fun n => ∃ i j : ℕ,
      i < j ∧ j ≤ i+2 ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j
    L.card-S.card  ≤  W.card+W.card.choose 2 := by
  dsimp only
  let long := fun n : ℕ => ∃ i j : ℕ, i+3 ≤ j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j
  let near := fun n : ℕ => ∃ i j : ℕ, i < j ∧ j ≤ i+2 ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j
  let L := (range N).filter fun n => ¬long n
  have eq : (L.filter fun n => ¬near n) =
      (range N).filter fun n => ¬∃ i j : ℕ, i < j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j := by
    ext n
    simp only [L,mem_filter]
    constructor
    · rintro ⟨⟨hn,hl⟩,hs⟩
      refine ⟨hn,?_⟩
      rintro ⟨i,j,hi,hr,hj,hv⟩
      by_cases h : i+3 ≤ j
      · exact hl ⟨i,j,h,hr,hj,hv⟩
      · exact hs ⟨i,j,hi,by omega,hr,hj,hv⟩
    · rintro ⟨hn,h⟩
      refine ⟨⟨hn,?_⟩,?_⟩
      · rintro ⟨i,j,hi,hr,hj,hv⟩
        exact h ⟨i,j,by omega,hr,hj,hv⟩
      · rintro ⟨i,j,hi,_,hr,hj,hv⟩
        exact h ⟨i,j,hi,hr,hj,hv⟩
  have count := Finset.card_filter_add_card_filter_not (s:=L) near
  have bound := eligible_count N
  change L.card-(L.filter near).card  ≤  _
  rw [eq] at count
  omega

end Forest338

namespace Forest338

/-- Two successive forward halvings force another if one of the two latest lags
always blocks. Since each step strictly decreases a positive integer, the
forced chain cannot continue longer than its first entry. -/
lemma no_two_halvings (x : ℕ → ℕ) (t L : ℕ) (bound : x t < 2^L)
    (pos : ∀ i ≤ L+2, 0 < x (t+i))
    (step : ∀ i < L, x (t+i+2) = 2*x (t+i+3) ∨ x (t+i) = 2*x (t+i+2))
    (h0 : x t = 2*x (t+1)) (h1 : x (t+1) = 2*x (t+2)) : False := by
  have chain (i : ℕ) (hi : i < L) : x (t+i) = 2*x (t+i+1) := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      cases i with
      | zero => simpa using h0
      | succ i =>
        cases i with
        | zero => simpa [Nat.add_assoc, Nat.reduceAdd] using h1
        | succ i =>
          have a := ih i (by omega) (by omega)
          have b := ih (i+1) (by omega) (by omega)
          have p := pos (i+2) (by omega)
          rcases step i (by omega) with h | h <;> simp only [Nat.add_assoc, Nat.reduceAdd] at * <;> omega
  have down (i : ℕ) (hi : i ≤ L) : 2^i * x (t+i) = x t := by
    induction i with
    | zero => simp
    | succ i ih =>
      have a := ih (by omega)
      have b := chain i (by omega)
      rw [b] at a
      simpa [pow_succ, Nat.mul_assoc, Nat.add_assoc] using a
  have h := down L (by omega)
  have p := pos L (by omega)
  have le := Nat.le_mul_of_pos_right (2^L) p
  omega

/-- An abstract obstruction to covering a whole interval by the two shortest
lags, expressed in terms of the shifted values starting at its left endpoint. -/
lemma short_lag_contradiction (x : ℕ → ℕ) (s : ℕ)
    (ub : ∀ t ≤ 4*s+6, x t < 2^s)
    (pos : ∀ t ≤ 4*s+6, 0<x t)
    (step : ∀ t ≤ 4*s+2, x (t+2) = 2*x (t+3) ∨ x t = 2*x (t+2)) : False := by
  have noFF (t : ℕ) (ht : t ≤ 3*s)
      (a : x t = 2*x (t+1)) (b : x (t+1) = 2*x (t+2)) : False := by
    apply no_two_halvings x t s (ub _ (by omega)) _ _ a b
    · intro i hi
      exact pos _ (by omega)
    · intro i hi
      exact step _ (by omega)
  have jump (t : ℕ) (ht : t+3 ≤ 3*s) :
      x (t+1) = 2*x (t+3) ∨ x t = 2*x (t+3) := by
    rcases step (t+1) (by omega) with h | h
    · have F : x (t+3)=2*x (t+4) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using h
      rcases step (t+2) (by omega) with h' | h'
      · exact (noFF (t+3) (by omega) F (by simpa [Nat.add_assoc, Nat.reduceAdd] using h')).elim
      · rcases step t (by omega) with h'' | h''
        all_goals
          have p := pos (t+4) (by omega)
          simp only [Nat.add_assoc, Nat.reduceAdd] at *
          omega
    · left
      simpa only [Nat.add_assoc, Nat.reduceAdd] using h
  have height (t : ℕ) (ht : t ≤ 3*s) : 2^(t/3)*x t < 2^s := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      match t with
      | 0 => simpa using ub 0 (by omega)
      | 1 => simpa using ub 1 (by omega)
      | 2 => simpa using ub 2 (by omega)
      | t+3 =>
        have climb (u : ℕ) (hu : t ≤ u) (hut : u < t+3) (hx : x u = 2*x (t+3)) :
            2^((t+3)/3)*x (t+3) < 2^s := by
          calc
            _ = 2^(t/3)*x u := by rw [hx, show (t+3)/3=t/3+1 by omega,pow_succ]; ring
            _ ≤ 2^(u/3)*x u := by gcongr; omega
            _ < _ := ih _ hut (by omega)
        rcases jump t ht with h | h
        · exact climb (t+1) (by omega) (by omega) h
        · exact climb t (by omega) (by omega) h
  have h := height (3*s) (by omega)
  rw [show 3*s/3=s by omega] at h
  exact (Nat.not_lt_of_ge (Nat.le_mul_of_pos_right _ (pos (3*s) (by omega)))) h

end Forest338

namespace Forest338
open OMA.S_mo_338415

/-- Every window with length logarithmic in its height contains an index where neither of the two
shortest progressions forbids the candidate 1. -/
theorem two_lag_window (N s : ℕ) (hbnd : (N+4*s+6)/2 < 2^s) : ∃ n, N ≤ n ∧ n ≤ N+4*s+6 ∧
    ∀ k : ℕ, 0 < k → k ≤ 2 → 2*k ≤ n →
      (1:ℤ)-a (n-k) ≠ (a (n-k):ℤ)-a (n-2*k) := by
  by_contra! bad
  let x (t : ℕ) := a (N+t)-1
  apply short_lag_contradiction x s
  · intro t ht
    have := upper (N+t)
    dsimp [x]
    omega
  · intro t ht
    obtain ⟨k,hk,_,hb,he⟩ := bad (N+t) (by omega) (by omega)
    have ha := avoids (N+t) k hk hb
    have hp := positive (N+t)
    dsimp [x]
    omega
  · intro t ht
    obtain ⟨k,hk,h2,_,he⟩ := bad (N+t+4) (by omega) (by omega)
    have p0 := positive (N+t)
    have p2 := positive (N+(t+2))
    have p3 := positive (N+(t+3))
    dsimp [x]
    rcases (show k=1 ∨ k=2 by omega) with h | h <;> subst k
    · left
      rw [show N+t+4-1=N+(t+3) by omega, show N+t+4-2*1=N+(t+2) by omega] at he
      omega
    · right
      rw [show N+t+4-2=N+(t+2) by omega, show N+t+4-2*2=N+t by omega] at he
      omega

/-- An explicit window requiring no auxiliary height hypothesis. -/
theorem two_lag_log_window (N : ℕ) : ∃ n, N ≤ n ∧
    n ≤ N + 4 * Nat.log 2 (N+1) + 22 ∧
    ∀ k : ℕ, 0 < k → k ≤ 2 → 2*k ≤ n →
      (1:ℤ)-a (n-k) ≠ (a (n-k):ℤ)-a (n-2*k) := by
  let l := Nat.log 2 (N+1)
  have hb : (N+4*(l+4)+6)/2 < 2^(l+4) := by
    have ha : N+1 < 2^(l+1) := Nat.lt_pow_succ_log_self (by decide) _
    have hl : l ≤ N+1 := Nat.log_le_self _ _
    rw [show l+4=(l+1)+3 by omega, pow_add]
    norm_num
    omega
  obtain ⟨n, hn, hhi, h⟩ := two_lag_window N (l+4) hb
  exact ⟨n,hn,by dsimp [l] at *; omega,h⟩

end Forest338

namespace Forest338

/-- Reading the upper bit of each quaternary digit as a ternary digit gives
a sublinear-height graph containing no three-term arithmetic progression. -/
theorem quaternary_coloring :
    ∃ f : ℕ → ℕ, f 0 = 0 ∧
      (∀ n, f n = (n%4)/2 + 3*f (n/4)) ∧
      (∀ x y z, x+z=2*y → f x+f z=2*f y → x=y ∧ y=z) ∧
      ∀ m n, n<4^m → f n<3^m := by
  let f (n : ℕ) := Nat.ofDigits 3 ((Nat.digits 4 n).map fun d => d/2)
  have fz : f 0 = 0 := by simp [f]
  have fr (n : ℕ) : f n = (n%4)/2+3*f (n/4) := by
    by_cases hn : n=0
    · subst n
      change f 0=0+3*f 0
      rw [fz]
    · change Nat.ofDigits 3 ((Nat.digits 4 n).map _) = _
      rw [Nat.digits_def' (by decide) (by omega),List.map_cons,Nat.ofDigits_cons]
  refine ⟨f,fz,fr,?_,?_⟩
  · intro x y
    induction y using Nat.strong_induction_on generalizing x with
    | h y ih =>
      intro z hi hf
      by_cases hy : y=0
      · omega
      have hx := fr x
      have hy' := fr y
      have hz := fr z
      have hb (v : ℕ) : (v%4)/2=0 ∨ (v%4)/2=1 := by omega
      have hbits : (x%4)/2=(y%4)/2 ∧ (y%4)/2=(z%4)/2 := by
        rcases hb x with h | h <;> rcases hb y with k | k <;> rcases hb z with l | l <;> omega
      have hres : x%4=y%4 ∧ y%4=z%4 := by omega
      obtain ⟨hxy,hyz⟩ := ih (y/4) (by omega) (x/4) (z/4) (by omega) (by omega)
      omega
  · intro m
    induction m with
    | zero =>
      intro n hn
      have h : n=0 := by simpa only [pow_zero,Nat.lt_one_iff] using hn
      rw [h,fz,pow_zero]
      decide
    | succ m ih =>
      intro n hn
      rw [pow_succ] at hn ⊢
      have h := ih (n/4) (by omega)
      have := fr n
      omega

/-- A positive progression-free graph with a missing level which is locally
excluded at every index from 3 onward, using displacements at most three.
Its height on base-four windows grows at most as a power of three. -/
theorem lag_three_model :
    ∃ b : ℕ → ℕ, (∀ n, 0<b n) ∧
      (∀ x y z, x+z=2*y → b x+b z=2*b y → x=y ∧ y=z) ∧
      (∀ n ≥ 3, ∃ d : ℕ, 1≤d ∧ d≤3 ∧ 2*d≤n ∧ b (n-2*d)=2*b (n-d)) ∧
      ∀ m n, n<4^(m+1) → b n≤6*3^m := by
  obtain ⟨f,fz,_,free,fbound⟩ := quaternary_coloring
  let t (q : ℕ) := 1+3*f q
  let b (i : ℕ) := if (i%4)/2=0 then 2*t (i/4) else t (i/4)
  refine ⟨b,?_,?_,?_,?_⟩
  · intro n
    dsimp only [b,t]
    split <;> omega
  · intro x y z hp hv
    have htype : (x%4)/2=(y%4)/2 ∧ (y%4)/2=(z%4)/2 := by
      simp only [b,t] at hv
      split_ifs at hv <;> omega
    have hres : x%4=y%4 ∧ y%4=z%4 := by omega
    have hf : f (x/4)+f (z/4)=2*f (y/4) := by
      simp only [b,t,htype.1,htype.2] at hv
      split at hv <;> omega
    obtain ⟨hxy,hyz⟩ := free (x/4) (y/4) (z/4) (by omega) hf
    omega
  · intro n hn
    let q := (n-3)/4
    let r := (n-3)%4
    have e : n=4*q+3+r := by dsimp [q,r]; omega
    have h : r<4 := Nat.mod_lt _ (by decide)
    interval_cases r
    · refine ⟨1,by decide,by decide,by omega,?_⟩
      have a : n-2*1=4*q+1 := by omega
      have c : n-1=4*q+2 := by omega
      simp [b,a,c,Nat.add_mod]
      congr 1
      omega
    · refine ⟨2,by decide,by decide,by omega,?_⟩
      have a : n-2*2=4*q := by omega
      have c : n-2=4*q+2 := by omega
      simp [b,a,c,Nat.add_mod]
      congr 1
      omega
    · refine ⟨2,by decide,by decide,by omega,?_⟩
      have a : n-2*2=4*q+1 := by omega
      have c : n-2=4*q+3 := by omega
      simp [b,a,c,Nat.add_mod]
      congr 1
      omega
    · refine ⟨3,by decide,by decide,by omega,?_⟩
      have a : n-2*3=4*q := by omega
      have c : n-3=4*q+3 := by omega
      simp [b,a,c,Nat.add_mod]
      congr 1
      omega
  · intro m n hn
    rw [pow_succ] at hn
    have := fbound m (n/4) (by omega)
    dsimp only [b,t]
    split <;> omega

/-- The quaternary window estimate implies a sublinear-height countermodel for
the bounded-displacement condition. The displaced sequence is written with
its missing height equal to one, just as in the original question. -/
theorem sublinear_lag_three_model :
    ∃ g : ℕ → ℕ, (∀ n, 1<g n) ∧
      (∀ x y z, x+z=2*y → g x+g z=2*g y → x=y ∧ y=z) ∧
      (∀ n ≥ 3, ∃ d : ℕ, 1≤d ∧ d≤3 ∧ 2*d≤n ∧ g (n-2*d)+1=2*g (n-d)) ∧
      ∀ h : ℕ, ∃ N : ℕ, ∀ n ≥ N, h*g n ≤ n := by
  obtain ⟨b,pos,free,step,bd⟩ := lag_three_model
  refine ⟨fun n => b n+1,fun n => by dsimp only; have := pos n; omega,?_,?_,?_⟩
  · intro x y z hi hv
    dsimp only at hv
    exact free x y z hi (by omega)
  · intro n hn
    obtain ⟨d,h₁,h₂,h₃,h₄⟩ := step n hn
    exact ⟨d,h₁,h₂,h₃,by dsimp only; omega⟩
  · have ratio (m : ℕ) : (m+3)*3^m ≤ 3*4^m := by
      induction m with
      | zero => decide
      | succ m ih =>
        calc
          (m+1+3)*3^(m+1) = (3*(m+4))*3^m := by ring
          _ ≤ (4*(m+3))*3^m := Nat.mul_le_mul_right _ (by omega)
          _ = 4*((m+3)*3^m) := by ring
          _ ≤ 4*(3*4^m) := Nat.mul_le_mul_left _ ih
          _ = 3*4^(m+1) := by ring
    intro h
    refine ⟨4^(21*h),fun n hn => ?_⟩
    let m := Nat.log 4 n
    have hm : 21*h ≤ m := Nat.le_log_of_pow_le (by decide) hn
    have hp : 0<4^(21*h) := by positivity
    have lo : 4^m≤n := Nat.pow_log_le_self _ (by omega)
    have h₁ := bd m n (Nat.lt_pow_succ_log_self (by decide) n)
    have h₂ : 0<3^m := by positivity
    have h₃ := Nat.mul_le_mul_right (3^m) (show 21*h ≤ m+3 by omega)
    have h₄ := h₃.trans (ratio m)
    calc
      h*(b n+1) ≤ h*(7*3^m) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 4^m := by nlinarith only [h₄]
      _ ≤ n := lo

end Forest338

namespace Forest338

theorem four_block_lags {g t : ℕ → ℕ} {L : ℕ}
    (blocks : ∀ q, g (L+4*q)=1+2*t q ∧ g (L+4*q+1)=1+2*t q ∧
      g (L+4*q+2)=1+t q ∧ g (L+4*q+3)=1+t q)
    (n : ℕ) (hn : L+3≤n) :
    ∃ d : ℕ, 1≤d ∧ d≤3 ∧ L+2*d≤n ∧ g (n-2*d)+1=2*g (n-d) := by
  let q := (n-L-3)/4
  let r := (n-L-3)%4
  have e : n=L+4*q+3+r := by dsimp [q,r]; omega
  have h : r<4 := Nat.mod_lt _ (by decide)
  obtain ⟨h₀,h₁,h₂,h₃⟩ := blocks q
  interval_cases r
  · refine ⟨1,by decide,by decide,by omega,?_⟩
    rw [show n-2*1=L+4*q+1 by omega,show n-1=L+4*q+2 by omega,h₁,h₂]
    omega
  · refine ⟨2,by decide,by decide,by omega,?_⟩
    rw [show n-2*2=L+4*q by omega,show n-2=L+4*q+2 by omega,h₀,h₂]
    omega
  · refine ⟨2,by decide,by decide,by omega,?_⟩
    rw [show n-2*2=L+4*q+1 by omega,show n-2=L+4*q+3 by omega,h₁,h₃]
    omega
  · refine ⟨3,by decide,by decide,by omega,?_⟩
    rw [show n-2*3=L+4*q by omega,show n-3=L+4*q+3 by omega,h₀,h₃]
    omega

theorem two_powers_progression {i j k : ℕ} (h : 2^i+2^k=2*2^j) : i=j ∧ j=k := by
  have sep (a b c : ℕ) (hab : a<b) : 2^a+2^b ≠ 2*2^c := by
    intro he
    have h₁ := Nat.pow_lt_pow_right (by decide : 1<2) hab
    rcases lt_or_ge c b with hcb | hbc
    · have h₂ := Nat.pow_le_pow_right (by decide : 0<2) (show c+1≤b by omega)
      rw [pow_succ] at h₂
      have : 0<2^a := by positivity
      omega
    · have h₂ := Nat.pow_le_pow_right (by decide : 0<2) hbc
      omega
  have hik : i=k := by
    rcases lt_trichotomy i k with h₁|h₁|h₁
    · exact False.elim (sep i k j h₁ h)
    · exact h₁
    · exact False.elim (sep k i j h₁ (by omega))
  subst k
  have he : 2^i=2^j := by omega
  exact ⟨Nat.pow_right_injective (by decide : 2≤2) he,
    (Nat.pow_right_injective (by decide : 2≤2) he).symm⟩

/-- Every valid finite prefix extends to an infinite progression-free graph
in which one never appears again and is blocked at displacements at most
three throughout the tail. -/
theorem prefix_lag_three_extension (f : ℕ → ℕ) (L : ℕ)
    (free : ∀ i d, 0<d → i+2*d<L → f i+f (i+2*d)≠2*f (i+d)) :
    ∃ g : ℕ → ℕ, (∀ i<L, g i=f i) ∧ (∀ i≥L, 1<g i) ∧
      (∀ i d, 0<d → g i+g (i+2*d)≠2*g (i+d)) ∧
      ∀ n≥L+3, ∃ d : ℕ, 1≤d ∧ d≤3 ∧ L+2*d≤n ∧ g (n-2*d)+1=2*g (n-d) := by
  let M := 2+2*∑ i ∈ Finset.range L, f i
  have mpos : 0<M := by dsimp [M]; omega
  have mone : 1<M := by dsimp [M]; omega
  have small (i : ℕ) (hi : i<L) : 2*f i<M := by
    have h := Finset.single_le_sum (f:=f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
    dsimp [M]
    omega
  let e (u : ℕ) := 3*(u/4)+(if (u%4)/2=0 then 1 else 0)
  have narrow (u v : ℕ) (h : e u=e v) : u≤v+1 ∧ v≤u+1 := by
    dsimp only [e] at h
    split_ifs at h <;> omega
  have noDouble (u v : ℕ) (h : u<v) : e v ≠ e u+1 := by
    dsimp only [e]
    split_ifs <;> omega
  let g (i : ℕ) := if i<L then f i else 1+M*2^e (i-L)
  have before (i : ℕ) (hi : i<L) : g i=f i := if_pos hi
  have after (i : ℕ) (hi : L ≤ i) : g i=1+M*2^e (i-L) := if_neg (by omega)
  refine ⟨g,before,fun i hi => ?_,?_,?_⟩
  · rw [after i hi]
    have : 0<M*2^e (i-L) := by positivity
    omega
  · intro i d hd ht
    by_cases hz : i+2*d<L
    · rw [before _ hz,before _ (by omega),before _ (by omega)] at ht
      exact free i d hd hz ht
    by_cases hy : i+d<L
    · rw [before _ (by omega),before _ hy,after _ (by omega)] at ht
      have hsm := small _ hy
      have hpow : 0<2^e (i+2*d-L) := by positivity
      have := Nat.mul_le_mul_left M hpow
      omega
    by_cases hx : i<L
    · rw [before _ hx,after _ (by omega),after _ (by omega)] at ht
      have hscale : f i + M*2^e (i+2*d-L) = 1+M*(2*2^e (i+d-L)) := by
        nlinarith only [ht]
      have hrem := congrArg (· % M) hscale
      simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (show f i<M by have := small i hx; omega),
        Nat.mod_eq_of_lt mone] at hrem
      have hpow : 2^e (i+2*d-L) = 2^(e (i+d-L)+1) := by
        apply Nat.eq_of_mul_eq_mul_left mpos
        rw [pow_succ]
        nlinarith only [hscale,hrem]
      exact noDouble (i+d-L) (i+2*d-L) (by omega)
        (Nat.pow_right_injective (by decide : 2≤2) hpow)
    · rw [after _ (by omega),after _ (by omega),after _ (by omega)] at ht
      have poweq : 2^e (i-L)+2^e (i+2*d-L)=2*2^e (i+d-L) := by
        apply Nat.eq_of_mul_eq_mul_left mpos
        nlinarith only [ht]
      obtain ⟨hxy,hyz⟩ := two_powers_progression poweq
      have := narrow _ _ (hxy.trans hyz)
      omega
  · apply four_block_lags (t:=fun q => M*2^(3*q))
    intro q
    have form (r : ℕ) (hr : r<4) :
        g (L+4*q+r) = 1+M*2^(3*q+(if r<2 then 1 else 0)) := by
      rw [after _ (by omega)]
      have e₁ : (L+4*q+r-L)/4=q := by omega
      have e₂ : (L+4*q+r-L)%4=r := by omega
      simp only [e,e₁,e₂]
      by_cases h : r<2
      · rw [if_pos h,if_pos (by omega)]
      · rw [if_neg h,if_neg (by omega)]
    have e₀ := form 0 (by decide)
    have e₁ := form 1 (by decide)
    have e₂ := form 2 (by decide)
    have e₃ := form 3 (by decide)
    norm_num [pow_succ] at e₀ e₁ e₂ e₃
    exact ⟨by nlinarith only [e₀],by nlinarith only [e₁],e₂,e₃⟩

end Forest338

namespace Forest338
open OMA.S_mo_338415

theorem native_prefix_lag_three_extension (L : ℕ) :
    ∃ g : ℕ → ℕ, (∀ i<L, g i=a i) ∧ (∀ i≥L, 1<g i) ∧
      (∀ i d, 0<d → g i+g (i+2*d)≠2*g (i+d)) ∧
      ∀ n≥L+3, ∃ d : ℕ, 1≤d ∧ d≤3 ∧ L+2*d≤n ∧ g (n-2*d)+1=2*g (n-d) := by
  apply prefix_lag_three_extension
  intro i d hd _ he
  have h := avoids (i+2*d) d hd (by omega)
  rw [show i+2*d-d=i+d by omega,show i+2*d-2*d=i by omega] at h
  omega

end Forest338

namespace Forest338
open Finset
open scoped Classical

/-- A rational affine section of a graph avoiding all three-term progressions is
progression-free on every positively stepped sampling progression. -/
theorem affine_section_bound (f : ℕ → ℕ)
    (graph : ∀ x y z : ℕ, x + z = 2 * y →
      (f x : ℤ) + f z = 2 * f y → x = z)
    (L b d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (t α β : ℤ) (ht : t ≠ 0) :
    ((range L).filter fun x => ∃ j : ℕ,
      q*j = b+d*x ∧ t*f j = α*x+β).card ≤ rothNumberNat L := by
  let S := (range L).filter fun x => ∃ j : ℕ,
    q*j = b+d*x ∧ t*f j = α*x+β
  change S.card ≤ _
  apply ThreeAPFree.le_rothNumberNat S _ (fun x hx => mem_range.mp (mem_filter.mp hx).1) rfl
  apply threeAPFree_iff_eq_right.mpr
  intro x hx y hy z hz H
  obtain ⟨i, hi, vi⟩ := (mem_filter.mp hx).2
  obtain ⟨j, hj, vj⟩ := (mem_filter.mp hy).2
  obtain ⟨k, hk, vk⟩ := (mem_filter.mp hz).2
  have idx : i+k=2*j := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith [congrArg (d * ·) H]
  have vals : (f i : ℤ)+f k=2*f j := by
    apply mul_left_cancel₀ ht
    have H' : (x:ℤ)+z=y+y := by exact_mod_cast H
    linarith only [show t*((f i : ℤ)+f k) = α*((x : ℤ)+z)+2*β by linarith only [vi,vk],
      show t*(2*(f j : ℤ)) = α*((y : ℤ)+y)+2*β by linarith only [vj],
      congrArg (fun w : ℤ => α*w+2*β) H']
  have hik := graph i j k idx vals
  apply Nat.eq_of_mul_eq_mul_left hd
  subst k
  omega

/-- Simultaneously remove the first `K` levels and every endpoint that can be
blocked for one of these values by an origin in the finite history `I`. -/
theorem sparse_history_bound (f : ℕ → ℕ) (pos : ∀ n, 0 < f n)
    (graph : ∀ x y z : ℕ, x + z = 2 * y →
      (f x : ℤ) + f z = 2 * f y → x = z)
    (L u d K : ℕ) (hd : 0 < d) (I : Finset ℕ) :
    ((range L).filter fun x => f (u+d*x) ≤ K ∨
      ∃ m ∈ Icc 1 K, ∃ i ∈ I, ∃ j : ℕ,
        2*j = (u+i)+d*x ∧ 2*f j = f i+m).card ≤
      K * (I.card+1) * rothNumberNat L := by
  let level (m : ℕ) := (range L).filter fun x => f (u+d*x) = m
  let origin (m i : ℕ) := (range L).filter fun x => ∃ j : ℕ,
    2*j=(u+i)+d*x ∧ 2*f j = f i+m
  let B (m : ℕ) := level m ∪ I.biUnion (origin m)
  have hl (m : ℕ) : (level m).card ≤ rothNumberNat L := by
    apply le_trans _ (affine_section_bound f graph L u d 1 hd (by decide) 1 0 m (by decide))
    apply card_le_card
    intro x hx
    obtain ⟨xL, hx⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨xL, u+d*x, by simp, by simpa using congrArg (fun z : ℕ => (z:ℤ)) hx⟩
  have ho (m i : ℕ) : (origin m i).card ≤ rothNumberNat L := by
    apply le_trans _ (affine_section_bound f graph L (u+i) d 2 hd (by decide)
        2 0 ((f i : ℤ)+m) (by decide))
    apply card_le_card
    intro x hx
    obtain ⟨xL, j, hj, hj'⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨xL, j, hj, by simpa using congrArg (fun z : ℕ => (z:ℤ)) hj'⟩
  have hb (m : ℕ) : (B m).card ≤ (I.card+1)*rothNumberNat L := by
    exact (card_union_le ..).trans ((Nat.add_le_add (hl m)
      (card_biUnion_le_card_mul I (origin m) _ (fun i _ => ho m i))).trans_eq (by ring))
  apply le_trans _ ((card_biUnion_le_card_mul (Icc 1 K) B _ (fun m _ => hb m)).trans_eq ?_)
  · apply card_le_card
    intro x hx
    simp only [mem_filter] at hx
    obtain ⟨xL, h|h⟩ := hx
    · exact mem_biUnion.mpr ⟨f (u+d*x), mem_Icc.mpr ⟨pos _,h⟩,
        mem_union_left _ (mem_filter.mpr ⟨xL,rfl⟩)⟩
    · obtain ⟨m,hm,i,hi,j,hj,hj'⟩ := h
      exact mem_biUnion.mpr ⟨m,hm,mem_union_right _
        (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨xL,j,hj,hj'⟩⟩)⟩
  · simp [Nat.mul_assoc]

end Forest338

namespace Forest338
open Finset OMA.S_mo_338415
open scoped Classical

theorem graph_three_free (x y z : ℕ) (hxz : x+z=2*y)
    (hv : (a x : ℤ)+a z=2*a y) : x=z := by
  have ord (s t : ℕ) (hst : s<t) (hi : s+t=2*y)
      (he : (a s:ℤ)+a t=2*a y) : False := by
    have h := avoids t (y-s) (by omega) (by omega)
    rw [show t-(y-s)=y by omega, show t-2*(y-s)=s by omega] at h
    exact h (by linarith)
  rcases lt_trichotomy x z with h|h|h
  · exact (ord x z h hxz hv).elim
  · exact h
  · exact (ord z x h (by omega) (by linarith)).elim

/-- Delete any fixed finite history, and test all positive values up to `K`.
Uniformly in the starting point and stride, outside a density-zero exceptional set,
each tested value is blocked, and all its witnesses avoid the deleted history. -/
theorem uniform_fresh_history (K : ℕ) (I : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ u d : ℕ, 0 < d →
      ∃ E ⊆ range L, (E.card : ℝ) ≤ ε*L ∧
        ∀ x < L, x ∉ E → K < a (u+d*x) ∧
          ∀ m ∈ Icc 1 K,
            (∃ k : ℕ, 0 < k ∧ 2*k ≤ u+d*x ∧
              (m : ℤ)-a (u+d*x-k)=(a (u+d*x-k):ℤ)-a (u+d*x-2*k)) ∧
            (∀ k : ℕ, 0 < k → 2*k ≤ u+d*x →
              (m : ℤ)-a (u+d*x-k)=(a (u+d*x-k):ℤ)-a (u+d*x-2*k) →
              u+d*x-2*k ∉ I) := by
  obtain ⟨L₀,hL₀⟩ := Filter.eventually_atTop.mp
    (rothNumberNat_isLittleO_id.bound (by positivity : 0 < ε / ((K*(I.card+1):ℕ)+1:ℝ)))
  refine ⟨L₀,fun L hL u d hd => ?_⟩
  let E := (range L).filter fun x => a (u+d*x) ≤ K ∨
    ∃ m ∈ Icc 1 K, ∃ i ∈ I, ∃ j : ℕ, 2*j=(u+i)+d*x ∧ 2*a j=a i+m
  have hcard : E.card ≤ K*(I.card+1)*rothNumberNat L :=
    sparse_history_bound a positive graph_three_free L u d K hd I
  refine ⟨E,?_,?_,?_⟩
  · intro x hx
    simp only [E,mem_filter] at hx
    exact hx.1
  · have hR := hL₀ L hL
    simp only [Real.norm_natCast] at hR
    have hR' : (rothNumberNat L : ℝ) * ((K*(I.card+1):ℕ)+1:ℝ) ≤ ε * (L:ℝ) := by
      rwa [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hR
    exact (Nat.cast_le.mpr hcard).trans (by
      push_cast at hR' ⊢
      nlinarith only [hR', Nat.cast_nonneg (rothNumberNat L) (α:=ℝ)])
  · intro x hx hgood
    have hb : ¬ (a (u+d*x) ≤ K ∨ ∃ m ∈ Icc 1 K, ∃ i ∈ I, ∃ j : ℕ,
        2*j=(u+i)+d*x ∧ 2*a j=a i+m) := by
      simpa only [E,mem_filter,mem_range,hx,true_and] using hgood
    have hK : K<a (u+d*x) := by
      exact lt_of_not_ge (fun h => hb (Or.inl h))
    refine ⟨hK,fun m hm => ⟨blocked (mem_Icc.mp hm).1 (lt_of_le_of_lt (mem_Icc.mp hm).2 hK),?_⟩⟩
    intro k _ h2 he hI
    exact hb (Or.inr ⟨m,hm,u+d*x-2*k,hI,u+d*x-k,by omega,by omega⟩)

end Forest338

namespace Forest338
open Finset OMA.S_mo_338415
open scoped Classical

/-- On arbitrarily late progressions of any prescribed length, every term exceeds
`K`. Each smaller candidate needs an external witness: no two points anywhere
in the progression have the required values, and no origin belongs to `I`. -/
theorem external_blocker_progression (K T N : ℕ) (I : Finset ℕ) :
    ∃ u ≥ N, ∃ d > 0,
      (∀ x < T, K < a (u+d*x) ∧
        ∀ m ∈ Icc 1 K, ∀ k : ℕ, 0 < k → 2*k ≤ u+d*x →
          (m : ℤ)-a (u+d*x-k)=(a (u+d*x-k):ℤ)-a (u+d*x-2*k) →
          u+d*x-2*k ∉ I) ∧
      ∀ x < T, ∀ y < T, ∀ m ∈ Icc 1 K, a (u+d*x)+m ≠ 2*a (u+d*y) := by
  classical
  let good (n : ℕ) := K < a n ∧ ∀ m ∈ Icc 1 K, ∀ k : ℕ, 0 < k → 2*k ≤ n →
    (m : ℤ)-a (n-k)=(a (n-k):ℤ)-a (n-2*k) → n-2*k ∉ I
  let color (n : ℕ) : Bool × (Fin (K+1) → Fin 2) :=
    (decide (good n), fun m => ⟨padicValNat 2 (a n-m.val) % 2, Nat.mod_lt _ (by decide)⟩)
  obtain ⟨L₀, H⟩ := uniform_fresh_history K I (by norm_num : 0 < (1/2:ℝ))
  let L := L₀+T+1
  obtain ⟨d,hd,b,c,hc⟩ := Combinatorics.exists_mono_homothetic_copy
    (range L) (fun n => color (n+N))
  let u := b+N
  have hC (x : ℕ) (hx : x < L) : color (u+d*x)=c := by
    simpa only [u,nsmul_eq_mul,Nat.cast_id,add_assoc,add_comm,add_left_comm] using hc x (mem_range.mpr hx)
  obtain ⟨E,hE,hcard,hgood⟩ := H L (by dsimp [L]; omega) u d hd
  have hlt : E.card < (range L).card := by
    rw [card_range]
    have hpos : 0 < (L:ℝ) := by exact_mod_cast (show 0<L by dsimp [L]; omega)
    exact_mod_cast (show (E.card:ℝ) < L by linarith)
  obtain ⟨x₀,hx₀,hxE⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hx := mem_range.mp hx₀
  have hg₀ := hgood x₀ hx hxE
  have hg : good (u+d*x₀) := ⟨hg₀.1,fun m hm => (hg₀.2 m hm).2⟩
  have allgood (x : ℕ) (hx' : x<L) : good (u+d*x) := by
    have h := congrArg Prod.fst ((hC x hx').trans (hC x₀ hx).symm)
    change decide (good (u+d*x)) = decide (good (u+d*x₀)) at h
    simpa [hg] using h
  have hTL : T ≤ L := by dsimp [L]; omega
  refine ⟨u,by dsimp [u]; omega,d,hd,fun x hx' => allgood x (lt_of_lt_of_le hx' hTL),?_⟩
  intro x hx' y hy m hm he
  have hmx := (allgood x (lt_of_lt_of_le hx' hTL)).1
  have hmy := (allgood y (lt_of_lt_of_le hy hTL)).1
  have hmK := (mem_Icc.mp hm).2
  let i : Fin (K+1) := ⟨m, by omega⟩
  have h := congrArg (fun z : Bool × (Fin (K+1) → Fin 2) => (z.2 i).val)
    ((hC x (lt_of_lt_of_le hx' hTL)).trans (hC y (lt_of_lt_of_le hy hTL)).symm)
  change padicValNat 2 (a (u+d*x)-m)%2 = padicValNat 2 (a (u+d*y)-m)%2 at h
  have hv : a (u+d*x)-m = 2*(a (u+d*y)-m) := by omega
  rw [hv,padicValNat.mul (by decide) (by omega),padicValNat_self] at h
  omega

end Forest338

namespace Forest338
open Finset OMA.S_mo_338415
open scoped Classical

/-- A fixed midpoint forces the value of the origin. Reversing the sampled
offsets preserves the midpoint equation and hence the Roth bound. -/
theorem fixed_midpoint_bound (L u d j m : ℕ) (hd : 0 < d) :
    ((range L).filter fun x => ∃ i : ℕ, i+(u+d*x)=2*j ∧ a i+m=2*a j).card
      ≤ rothNumberNat L := by
  let S := (range L).filter fun x => ∃ i : ℕ, i+(u+d*x)=2*j ∧ a i+m=2*a j
  change S.card ≤ _
  apply ThreeAPFree.le_rothNumberNat S _ (fun x hx => mem_range.mp (mem_filter.mp hx).1) rfl
  apply threeAPFree_iff_eq_right.mpr
  intro x hx y hy z hz H
  obtain ⟨i, hi, vi⟩ := (mem_filter.mp hx).2
  obtain ⟨k, hk, vk⟩ := (mem_filter.mp hy).2
  obtain ⟨l, hl, vl⟩ := (mem_filter.mp hz).2
  have ix : i+l=2*k := by nlinarith [congrArg (d*·) H]
  have ih := graph_three_free i k l ix (by omega)
  apply Nat.eq_of_mul_eq_mul_left hd
  omega

/-- Any finite support meeting one endpoint of a full set of blocking pairs for
one candidate must grow with the length of the arithmetic progression it covers. -/
theorem blocking_support_cost (L u d m : ℕ) (hd : 0 < d) (S : Finset ℕ)
    (cover : ∀ x < L, ∃ i j : ℕ, i+(u+d*x)=2*j ∧ a i+m=2*a j ∧
      (i ∈ S ∨ j ∈ S)) : L ≤ 2*S.card*rothNumberNat L := by
  let orig (i : ℕ) := (range L).filter fun x => ∃ j : ℕ,
    2*j=(u+i)+d*x ∧ 2*a j=a i+m
  let mid (j : ℕ) := (range L).filter fun x => ∃ i : ℕ,
    i+(u+d*x)=2*j ∧ a i+m=2*a j
  have h₁ (i : ℕ) : (orig i).card ≤ rothNumberNat L := by
    apply le_trans _ (affine_section_bound a graph_three_free L (u+i) d 2 hd (by decide)
        2 0 ((a i : ℤ)+m) (by decide))
    apply card_le_card
    intro x hx
    obtain ⟨xL, j, hj, hv⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨xL,j,hj,by simpa using congrArg (fun z : ℕ => (z:ℤ)) hv⟩
  have sub : range L ⊆ S.biUnion fun v => orig v ∪ mid v := by
    intro x hx
    obtain ⟨i,j,hij,ha,h|h⟩ := cover x (mem_range.mp hx)
    · exact mem_biUnion.mpr ⟨i,h,mem_union_left _ (mem_filter.mpr ⟨hx,j,by omega,by omega⟩)⟩
    · exact mem_biUnion.mpr ⟨j,h,mem_union_right _ (mem_filter.mpr ⟨hx,i,hij,ha⟩)⟩
  have hb := card_biUnion_le_card_mul S (fun v => orig v ∪ mid v) (2*rothNumberNat L)
    (fun v _ => (card_union_le ..).trans ((Nat.add_le_add (h₁ v)
      (fixed_midpoint_bound L u d v m hd)).trans_eq (by ring)))
  simpa only [card_range,mul_assoc,mul_left_comm,mul_comm] using (card_le_card sub).trans hb

end Forest338

namespace Forest338
open OMA.S_mo_338415

theorem mask_allows (l : List ℕ) (f : ℕ → ℕ) (m : ℕ) :
    ((l.foldr (fun i bits => bits ||| 2^(f i)) 0).testBit m = true) ↔ ∃ i ∈ l, f i = m := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons]
    by_cases h : f i = m
    · subst m
      simp
    · simp [h]

/-- Verify a table by marking the forbidden values in each row. The mask is
computed once per row, irrespective of how large the selected term is. -/
theorem certified_prefix (v : ℕ → ℕ) (N : ℕ) (h : ∀ n < N,
    (
      let f := fun i => 2*v (n-(i+1)) - v (n-2*(i+1))
      let b := (List.range (n/2)).foldr (fun i bits => bits ||| 2^(f i)) 0
      0 < (v n) && !b.testBit (v n) &&
      (List.range ((v n)-1)).all (fun j => b.testBit (j+1))) = true) :
    ∀ n < N, a n = (v n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have step := h n hn
    rw [Bool.and_eq_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at step
    obtain ⟨⟨hp,hout⟩,hins⟩ := step
    let f := fun i => 2*v (n-(i+1)) - v (n-2*(i+1))
    have conv (i : ℕ) (hi : i < n/2) (m : ℕ) (hm : 0 < m) :
        f i=m ↔ (m:ℤ)-a (n-(i+1)) = (a (n-(i+1)):ℤ)-a (n-2*(i+1)) := by
      rw [ih (n-(i+1)) (by omega) (by omega), ih (n-2*(i+1)) (by omega) (by omega)]
      dsimp [f]
      omega
    by_contra hn'
    rcases lt_or_gt_of_ne hn' with hl | hl
    · have hp' := positive n
      have hbit := List.all_eq_true.mp hins (a n-1) (List.mem_range.mpr (by omega))
      rw [show a n-1+1 = a n by omega] at hbit
      obtain ⟨i,hi,hh⟩ := (mask_allows _ f _).mp hbit
      have hb := List.mem_range.mp hi
      exact avoids n (i+1) (by omega) (by omega) ((conv i hb _ hp').mp hh)
    · obtain ⟨k,hk,hb,he⟩ := blocked hp hl
      have heq : k-1+1=k := by omega
      have valid : k-1 < n/2 := by omega
      have hf := (conv (k-1) valid _ hp).mpr (by simpa only [heq] using he)
      have hbit := (mask_allows (List.range (n/2)) f _).mpr ⟨k-1,List.mem_range.mpr valid,hf⟩
      exact Bool.false_ne_true (hout.symm.trans hbit)

end Forest338

namespace Forest338
open OMA.S_mo_338415

theorem strict_mask_iff (v : ℕ → ℕ) (n lo hi : ℕ) (h : ∀ i ≤ n, a i=v i)
    (hlo : 0 < lo) :
    ((List.range (n/2)).any fun i => decide (
      lo ≤ i+1 ∧ i+1 ≤ hi ∧ 1 < v (n-(i+1)) ∧ v (n-2*(i+1))+1=2*v (n-(i+1)))) = true ↔
    ∃ i j : ℕ, i+lo ≤ j ∧ j ≤ i+hi ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j := by
  rw [List.any_eq_true]
  simp only [List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨k,hk,hl,hu,hy,he⟩
    refine ⟨n-2*(k+1),n-(k+1),by omega,by omega,by omega,?_,?_⟩
    · simpa only [h _ (by omega : n-(k+1) ≤ n)] using hy
    · simpa only [h _ (by omega : n-(k+1) ≤ n), h _ (by omega : n-2*(k+1) ≤ n)] using he
  · rintro ⟨i,j,hl,hu,he,hj,hv⟩
    refine ⟨j-i-1,by omega,by omega,by omega,?_,?_⟩
    · simpa only [show n-(j-i-1+1)=j by omega,←h j (by omega)] using hj
    · simpa only [show n-(j-i-1+1)=j by omega,show n-2*(j-i-1+1)=i by omega,
        ←h j (by omega),←h i (by omega)] using hv

end Forest338

namespace Forest338
open OMA.S_mo_338415

/-- Exactly these endpoints of the verified prefix have strictly descending
blockers at short lags only. All indices start at zero. -/
theorem short_only_256 (n : ℕ) (hn : n < 256) :
    ((∃ i j : ℕ, i < j ∧ j ≤ i+2 ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j) ∧
      ¬∃ i j : ℕ, i+3 ≤ j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j) ↔ n ∈ [98, 107, 231] := by
  let v : ℕ → ℕ := fun i => (1770879161342639447000281122256139461893664454331549619231580402823730163181408833037217693366084243869996329937101182005427559167243453863508721690630676519947405014116475258282358424800911582858460050159806883433210803780706171425143521282634526648996694895414411096082898650010880475235296419688095445577719938667271378386628949265719231310772181069189228929535263789661022632052769 >>> (5*i)) % 32
  let hit (t lo hi : ℕ) := (List.range (t/2)).any fun i => decide (
    lo ≤ i+1 ∧ i+1 ≤ hi ∧ 1 < v (t-(i+1)) ∧ v (t-2*(i+1))+1=2*v (t-(i+1)))
  let check (t : ℕ) : Bool :=
    let f := fun i => 2*v (t-(i+1)) - v (t-2*(i+1))
    let b := (List.range (t/2)).foldr (fun i bits => bits ||| 2^(f i)) 0
    (0 < v t && !b.testBit (v t) && (List.range (v t-1)).all (fun j => b.testBit (j+1))) &&
      ((hit t 1 2 && !hit t 3 t) == decide (t ∈ [98, 107, 231]))
  have ok (t : ℕ) (ht : t < 256) : check t = true := by
    by_cases h128 : t < 128
    · by_cases h64 : t < 64
      · by_cases h32 : t < 32
        · by_cases h16 : t < 16
          · by_cases h8 : t < 8
            · apply List.all_eq_true.mp (show (List.range' 0 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 8 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h24 : t < 24
            · apply List.all_eq_true.mp (show (List.range' 16 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 24 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
        · by_cases h48 : t < 48
          · by_cases h40 : t < 40
            · apply List.all_eq_true.mp (show (List.range' 32 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 40 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h56 : t < 56
            · apply List.all_eq_true.mp (show (List.range' 48 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 56 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
      · by_cases h96 : t < 96
        · by_cases h80 : t < 80
          · by_cases h72 : t < 72
            · apply List.all_eq_true.mp (show (List.range' 64 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 72 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h88 : t < 88
            · apply List.all_eq_true.mp (show (List.range' 80 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 88 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
        · by_cases h112 : t < 112
          · by_cases h104 : t < 104
            · apply List.all_eq_true.mp (show (List.range' 96 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 104 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h120 : t < 120
            · apply List.all_eq_true.mp (show (List.range' 112 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 120 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
    · by_cases h192 : t < 192
      · by_cases h160 : t < 160
        · by_cases h144 : t < 144
          · by_cases h136 : t < 136
            · apply List.all_eq_true.mp (show (List.range' 128 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 136 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h152 : t < 152
            · apply List.all_eq_true.mp (show (List.range' 144 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 152 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
        · by_cases h176 : t < 176
          · by_cases h168 : t < 168
            · apply List.all_eq_true.mp (show (List.range' 160 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 168 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h184 : t < 184
            · apply List.all_eq_true.mp (show (List.range' 176 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 184 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
      · by_cases h224 : t < 224
        · by_cases h208 : t < 208
          · by_cases h200 : t < 200
            · apply List.all_eq_true.mp (show (List.range' 192 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 200 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h216 : t < 216
            · apply List.all_eq_true.mp (show (List.range' 208 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 216 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
        · by_cases h240 : t < 240
          · by_cases h232 : t < 232
            · apply List.all_eq_true.mp (show (List.range' 224 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 232 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
          · by_cases h248 : t < 248
            · apply List.all_eq_true.mp (show (List.range' 240 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
            · apply List.all_eq_true.mp (show (List.range' 248 8).all check = true by decide +kernel) t
              simp only [List.mem_range'_1]; omega
  have hv := certified_prefix v 256 (fun t ht => (Bool.and_eq_true_iff.mp (ok t ht)).1)
  have localv (i : ℕ) (hi : i ≤ n) := hv i (by omega)
  have hs : hit n 1 2 = true ↔
      (∃ i j : ℕ, i < j ∧ j ≤ i+2 ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j) :=
    strict_mask_iff v n 1 2 localv (by decide)
  have hl : hit n 3 n = true ↔ ∃ i j : ℕ, i+3 ≤ j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j := by
    rw [strict_mask_iff v n 3 n localv (by decide)]
    constructor
    · rintro ⟨i,j,g,_,e,x,y⟩; exact ⟨i,j,g,e,x,y⟩
    · rintro ⟨i,j,g,e,x,y⟩; exact ⟨i,j,g,by omega,e,x,y⟩
  have hcheck := (Bool.and_eq_true_iff.mp (ok n hn)).2
  change ((hit n 1 2 && !hit n 3 n) == decide (n ∈ [98, 107, 231])) = true at hcheck
  rw [beq_iff_eq] at hcheck
  rw [←hs,←hl,←decide_eq_true_eq (p := n ∈ [98, 107, 231]),←hcheck]
  cases hit n 1 2 <;> cases hit n 3 n <;> decide

end Forest338

namespace OMA.R_mo_338415_R1
open OMA.S_mo_338415
open Forest338

/-- Infinitely many endpoints escape all strictly descending extrapolations
to height one with lag at least three. -/
def H1 : Prop := ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    ¬∃ i j : ℕ, i + 3 ≤ j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j

/-- Eventual redundancy of the two nearest lags. Whenever a strict
extrapolation to one has lag one or two, a longer one also exists. -/
def H2 : Prop := ∃ M : ℕ, ∀ n : ℕ, M ≤ n →
    (∃ i j : ℕ, i < j ∧ j ≤ i + 2 ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j) →
    ∃ i j : ℕ, i + 3 ≤ j ∧ n+i=2*j ∧ 1 < a j ∧ a i+1=2*a j

theorem main : H1 → H2 → type_of% @OMA.S_mo_338415.main := by
  rintro h₁ ⟨M,h₂⟩
  apply infinite_sites_iff.mpr
  intro N
  obtain ⟨n,hn,he⟩ := h₁ (N+M)
  refine ⟨n,by omega,?_⟩
  rintro ⟨i,j,hi,hh,hj,hv⟩
  apply he
  by_cases h : i+3 ≤ j
  · exact ⟨i,j,h,hh,hj,hv⟩
  · exact h₂ n (by omega) ⟨i,j,hi,by omega,hh,hj,hv⟩

end OMA.R_mo_338415_R1
