import OMAStatements.S_oeis_a228410
import Mathlib

/-! A least-unused walk visits every decimal parity class. Representatives
with two ones permit a nonzero leading digit in each palindrome. -/
namespace GreedyPaths
noncomputable section
open Finset

def Legal (b : ℕ) (C : ℕ → ℕ → Prop) (a : ℕ → ℕ) : Prop :=
  a 0 = b ∧ ∀ n, IsLeast {m : ℕ | b ≤ m ∧ (∀ i ≤ n, a i ≠ m) ∧ C (a n) m} (a (n+1))

lemma existence {b : ℕ} {C : ℕ → ℕ → Prop} (many : ∀ x B, ∃ y, B < y ∧ C x y) :
    ∃ a, Legal b C a := by
  classical
  let ok (s : ℕ × Finset ℕ) (y : ℕ) := b ≤ y ∧ y ∉ s.2 ∧ C s.1 y
  have ex (s : ℕ × Finset ℕ) : ∃ y, ok s y := by
    obtain ⟨y,hy,hc⟩ := many s.1 (max b (s.2.sup id))
    refine ⟨y,by dsimp [ok]; refine ⟨by omega,?_,hc⟩; intro h; have := Finset.le_sup (f:=id) h; simp at this; omega⟩
  let step (s : ℕ × Finset ℕ) := (Nat.find (ex s), insert (Nat.find (ex s)) s.2)
  let states (n : ℕ) := step^[n] (b,{b})
  let a (n : ℕ) := (states n).1
  have st (n : ℕ) : states (n+1) = step (states n) := Function.iterate_succ_apply' _ _ _
  have an (n : ℕ) : a (n+1) = Nat.find (ex (states n)) := by
    change (states (n+1)).1 = _
    rw [st]
  have mems (n y : ℕ) : y ∈ (states n).2 ↔ ∃ i ≤ n, a i = y := by
    induction n with
    | zero => simp [states,a,eq_comm]
    | succ n ih =>
      rw [st]
      change y ∈ insert (Nat.find (ex (states n))) (states n).2 ↔ _
      rw [← an]
      rw [Finset.mem_insert,ih]
      constructor
      · rintro (h|⟨i,hi,h⟩)
        · exact ⟨_,le_rfl,h.symm⟩
        · exact ⟨i,by omega,h⟩
      · rintro ⟨i,hi,h⟩
        by_cases e : i=n+1
        · exact Or.inl (e ▸ h.symm)
        · exact Or.inr ⟨i,by omega,h⟩
  refine ⟨a,rfl,?_⟩
  intro n
  have h := Nat.find_spec (ex (states n))
  change b ≤ Nat.find (ex (states n)) ∧ Nat.find (ex (states n)) ∉ (states n).2 ∧ C (a n) (Nat.find (ex (states n))) at h
  rw [← an] at h
  refine ⟨⟨h.1,?_,h.2.2⟩,?_⟩
  · intro i hi eqn; exact h.2.1 ((mems _ _).mpr ⟨i,hi,eqn⟩)
  · rintro y ⟨hy,hn,hc⟩
    rw [an]
    apply Nat.find_min' (ex (states n))
    refine ⟨hy,?_,hc⟩
    intro mem
    obtain ⟨i,hi,eqn⟩ := (mems _ _).mp mem
    exact hn _ hi eqn

lemma injective {b C a} (h : Legal b C a) : Function.Injective a := by
  have diff {i j : ℕ} (lt : i<j) : a i ≠ a j := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    exact (h.2 k).1.2.1 i (by omega)
  intro i j eqn
  rcases lt_trichotomy i j with lt|eq|gt
  · exact (diff lt eqn).elim
  · exact eq
  · exact (diff gt eqn.symm).elim

/-- Infinitely many chances to use y force it into a least-unused injective walk. -/
lemma forced {b C a} (h : Legal b C a) {y : ℕ} (hy : b ≤ y)
    (chances : ∀ N, ∃ i, N ≤ i ∧ C (a i) y) : y ∈ Set.range a := by
  classical
  by_contra missing
  let small := (Set.Iic y).preimage a
  have fin : small.Finite := (Set.finite_Iic y).preimage (injective h).injOn
  obtain ⟨B,hB⟩ := fin.bddAbove
  obtain ⟨i,hi,hc⟩ := chances B
  have leq : a (i+1) ≤ y := (h.2 i).2 ⟨hy,fun j _ eqn => missing ⟨j,eqn⟩,hc⟩
  have := hB (show i+1 ∈ small from leq)
  omega
end
end GreedyPaths

namespace ParityWords
open List
def bag (f : ℕ → ℕ) := (List.range 10).flatMap (fun d => List.replicate (f d) d)

lemma count_bag (f : ℕ → ℕ) (d : ℕ) : (bag f).count d = if d < 10 then f d else 0 := by
  have aux (l : List ℕ) (hl : l.Nodup) :
      (l.flatMap (fun v => List.replicate (f v) v)).count d = if d ∈ l then f d else 0 := by
    induction l with
    | nil => simp
    | cons v l ih =>
      have ⟨hn,ht⟩ := List.nodup_cons.mp hl
      by_cases e : d=v
      · subst d; simp [ih ht,hn]
      · simp [ih ht,e,Ne.symm e,List.count_replicate]
  simpa [bag] using aux (List.range 10) List.nodup_range

lemma small_bag (f : ℕ → ℕ) (d : ℕ) (hd : d ∈ bag f) : d < 10 := by
  by_contra! bad
  have h := List.count_pos_iff.mpr hd
  rw [count_bag,if_neg (by omega)] at h
  omega

abbrev Mask := Finset (Fin 10)
def mask (l : List ℕ) : Mask := Finset.univ.filter (fun d => l.count d.val % 2 = 1)
def Rich (l : List ℕ) : Prop := 2 ≤ l.count 1
def Near (s t : Mask) : Prop := ∃ j : Fin 10, ∀ i ≠ j, (i ∈ s ↔ i ∈ t)

lemma near_same (s : Mask) : Near s s := ⟨0,by simp⟩
lemma near_insert (s : Mask) (v : Fin 10) : Near s (insert v s) :=
  ⟨v,fun i h => by simp [h]⟩
lemma near_symm {s t : Mask} (h : Near s t) : Near t s :=
  ⟨h.choose,fun i ne => (h.choose_spec i ne).symm⟩

lemma palindrome {l u : List ℕ} (small : ∀ d ∈ l++u, d < 10)
    (near : Near (mask l) (mask u)) (rich : Rich l ∨ Rich u) :
    ∃ w : List ℕ, w.Perm (l++u) ∧ w.reverse = w ∧ ∃ d : ℕ, w.head? = some d ∧ 0<d := by
  classical
  obtain ⟨j,hj⟩ := near
  let c (d : ℕ) := (l++u).count d
  let h := bag (fun d => (c d - (if d=1 then 2 else 0))/2)
  let mid := if c j.val % 2 = 1 then [j.val] else []
  have midrev : mid.reverse = mid := by dsimp [mid]; split <;> simp
  let w := [1] ++ h ++ mid ++ h.reverse ++ [1]
  refine ⟨w,List.perm_iff_count.mpr ?_,by simp [w,midrev,List.append_assoc],1,by simp [w],by decide⟩
  intro d
  have pair : 2 ≤ c 1 := by
    dsimp [c]; rw [List.count_append]; rcases rich with hr|hr <;> unfold Rich at hr <;> omega
  have even (hd : d < 10) (dif : d ≠ j.val) : c d % 2 = 0 := by
    have eqn := hj ⟨d,hd⟩ (by intro he; exact dif (congrArg Fin.val he))
    simp only [mask,Finset.mem_filter,Finset.mem_univ,true_and] at eqn
    dsimp [c]; rw [List.count_append]; omega
  have outside (hd : ¬d < 10) : c d = 0 := List.count_eq_zero.mpr (fun mem => hd (small d mem))
  have hc : h.count d = (c d - (if d=1 then 2 else 0))/2 := by
    rw [show h.count d = _ from count_bag _ d]
    split
    · rfl
    · rename_i hn; simp [outside hn]
  have mc : mid.count d = c d % 2 := by
    by_cases e : d = j.val
    · subst d
      by_cases odd : c j.val % 2 = 1
      · simp [mid,odd]
      · have hzero : c j.val % 2 = 0 := by omega
        simp [mid,hzero]
    · have hzero : c d % 2 = 0 := by
        by_cases hd : d < 10
        · exact even hd e
        · simp [outside hd]
      rw [hzero]
      dsimp [mid]; split <;> simp [List.count_singleton,e,Ne.symm e]
  change w.count d = c d
  simp only [w,List.count_append,List.count_reverse,hc,mc,List.count_singleton]
  by_cases e : d = 1
  · subst d; simp; omega
  · simp [e,Ne.symm e]; omega

end ParityWords

namespace ParityWords
open List
lemma representatives (s : Mask) (B : ℕ) :
    ∃ y, B < y ∧ mask (Nat.digits 10 y) = s ∧ Rich (Nat.digits 10 y) := by
  classical
  let f (d : ℕ) := if h : d<10 then if (⟨d,h⟩:Fin 10) ∈ s then 1 else 0 else 0
  let k := (Nat.digits 10 B).length
  let w := bag f ++ List.replicate (2*k) 1 ++ [1,1]
  let y := Nat.ofDigits 10 w
  have word : Nat.digits 10 y = w := by
    apply Nat.digits_ofDigits _ (by decide)
    · intro d hd
      rcases List.mem_append.mp hd with hl|hr
      · rcases List.mem_append.mp hl with hb|ho
        · exact small_bag _ _ hb
        · have := (List.mem_replicate.mp ho).2
          omega
      · simp at hr; omega
    · intro h; simp [w]
  refine ⟨y,?_,?_,?_⟩
  · by_contra! bad
    have cmp := Nat.le_length_digits_le 10 y B bad
    rw [word] at cmp
    simp [w] at cmp
    change _ ≤ k at cmp
    omega
  · rw [word]
    ext i
    simp only [mask,Finset.mem_filter,Finset.mem_univ,true_and]
    have parity : w.count i.val % 2 = f i.val % 2 := by
      simp only [w,List.count_append,count_bag,if_pos i.isLt]
      by_cases hi : i.val = 1
      · rw [hi]; simp
      · simp [List.count_replicate,List.count_cons,List.count_singleton,hi,Ne.symm hi]
    rw [parity]
    dsimp [f]
    rw [dif_pos i.isLt]
    by_cases hs : i ∈ s <;> simp [hs]
  · rw [word]; simp [Rich,w,List.count_append]; omega
end ParityWords

open ParityWords
namespace GreedyPaths
noncomputable section

lemma coverage {b : ℕ} {C : ℕ → ℕ → Prop} (tag : ℕ → Mask) (good : ℕ → Prop)
    (supply : ∀ s B, ∃ y, B < y ∧ tag y = s ∧ good y)
    (compatible : ∀ x y, Near (tag x) (tag y) → (good x ∨ good y) → C x y) :
    ∃ a, Legal b C a ∧ Function.Injective a ∧ Set.range a = {y : ℕ | b ≤ y} := by
  classical
  have many (x B : ℕ) : ∃ y, B < y ∧ C x y := by
    obtain ⟨y,hy,ht,hg⟩ := supply (tag x) B
    exact ⟨y,hy,compatible _ _ (ht ▸ near_same _) (Or.inr hg)⟩
  obtain ⟨a,ha⟩ := existence (b:=b) many
  let frequent (s : Mask) := ∀ N : ℕ, ∃ i, N ≤ i ∧ tag (a i) = s
  let recurrent (s : Mask) := ∀ N : ℕ, ∃ i, N ≤ i ∧ tag (a i) = s ∧ good (a i)
  have freq {s} (h : recurrent s) : frequent s := by
    intro N; obtain ⟨i,hi,ht,_⟩ := h N; exact ⟨i,hi,ht⟩
  have spread {s t} (hs : frequent s) (hnear : Near s t) : recurrent t := by
    intro N
    let bound := (Finset.range N).sup a
    obtain ⟨y,hy,ht,hg⟩ := supply t (max b bound)
    have mem : y ∈ Set.range a := forced ha (by omega) (by
      intro M
      obtain ⟨i,hi,hs'⟩ := hs M
      exact ⟨i,hi,compatible _ _ (by simpa [hs',ht] using hnear) (Or.inr hg)⟩)
    obtain ⟨i,ei⟩ := mem
    refine ⟨i,?_,ei ▸ ht,ei ▸ hg⟩
    by_contra! low
    have lim : a i ≤ bound := Finset.le_sup (f:=a) (Finset.mem_range.mpr low)
    omega
  obtain ⟨s,inf⟩ := Finite.exists_infinite_fiber (fun n => tag (a n))
  have recur : recurrent s := spread (s:=s) (by
    intro N
    have inf' : {i : ℕ | tag (a i) = s}.Infinite := Set.infinite_coe_iff.mp inf
    obtain ⟨i,hi,hN⟩ := inf'.exists_gt N
    exact ⟨i,hN.le,hi⟩) (near_same s)
  have down (t : Mask) : recurrent t → recurrent ∅ := by
    induction t using Finset.induction_on with
    | empty => exact id
    | @insert i t _ ih => exact fun h => ih (spread (freq h) (near_symm (near_insert t i)))
  have allm (t : Mask) : recurrent t := by
    induction t using Finset.induction_on with
    | empty => exact down _ recur
    | @insert i t _ ih => exact spread (freq ih) (near_insert t i)
  refine ⟨a,ha,injective ha,Set.ext fun y => ⟨?_,?_⟩⟩
  · rintro ⟨i,rfl⟩
    cases i with
    | zero => exact ha.1.ge
    | succ i => exact (ha.2 i).1.1
  · intro hy
    apply forced ha hy
    intro N
    obtain ⟨i,hi,ht,hg⟩ := allm (tag y) N
    exact ⟨i,hi,compatible _ _ (by rw [ht]; exact near_same _) (Or.inl hg)⟩
end
end GreedyPaths

open ParityWords OMA.S_oeis_a228410
theorem OMA.solution : type_of% @OMA.S_oeis_a228410.main := by
  let tag (x : ℕ) := mask (digitWord x)
  let good (x : ℕ) := Rich (digitWord x)
  have comp (x y : ℕ) (hn : Near (tag x) (tag y)) (hg : good x ∨ good y) : Compatible x y := by
    apply palindrome _ hn hg
    intro d hd
    rcases List.mem_append.mp hd with h|h <;> exact Nat.digits_lt_base (by decide : 1 < 10) h
  obtain ⟨a,ha,inj,ran⟩ := GreedyPaths.coverage (b:=1) tag good representatives comp
  refine ⟨a,⟨ha.1,?_⟩,inj,?_⟩
  · exact ha.2
  · exact ran
