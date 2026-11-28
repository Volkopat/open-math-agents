import OMAStatements.S_oeis_a250355
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Counting six shifted entries with no triple repetition

This proves Colin Barker's conjectured generating function and recurrence
for R. H. Hardin's OEIS A250355 (https://oeis.org/A250355). For a fixed
assignment the inclusion-exclusion terms are its uniform subsets of sizes
3, 4, 5 and its partitions into two uniform triples. A uniform subset has
n+1 minus its span possible common labels, truncated below at zero. This
gives a closed count for every positive n and an explicit degree-six
polynomial for n ≥ 4. The seventh finite difference vanishes from n=11,
and multiplying the series by (1−X)^7 leaves the asserted numerator.
-/

namespace Windows250

def sets (k : ℕ) : Finset (Finset (Fin 6)) := Finset.univ.powersetCard k

def dualsets : Finset (Finset (Fin 6)) := (sets 3).filter (fun s => (0 : Fin 6) ∈ s)

abbrev same {α : Type*} (f : Fin 6 → α) (s : Finset (Fin 6)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, f i=f j

def lo (s : Finset (Fin 6)) : ℕ := if h : s.Nonempty then (s.min' h).val else 0

def hi (s : Finset (Fin 6)) : ℕ := if h : s.Nonempty then (s.max' h).val else 0

def span (s : Finset (Fin 6)) : ℕ := hi s-lo s

def width (n : ℕ) (s : Finset (Fin 6)) : ℕ := n+1-span s

end Windows250

namespace Windows250

private def indicatorOK {α : Type*} [DecidableEq α] (f : Fin 6 → α) : Prop :=
  (if (∃ s ∈ sets 3, same f s) then (0 : ℤ) else 1) =
    1 - (∑ s ∈ sets 3, if same f s then (1 : ℤ) else 0) +
      3 * (∑ s ∈ sets 4, if same f s then (1 : ℤ) else 0) -
      6 * (∑ s ∈ sets 5, if same f s then (1 : ℤ) else 0) +
      (∑ s ∈ dualsets, if same f s ∧ same f sᶜ then (1 : ℤ) else 0)

private instance {α : Type*} [DecidableEq α] (f : Fin 6 → α) : Decidable (indicatorOK f) := by
  unfold indicatorOK
  infer_instance

private theorem indicator_congr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : Fin 6 → α) (g : Fin 6 → β) (h : ∀ i j, f i = f j ↔ g i = g j) :
    indicatorOK g → indicatorOK f := by
  have hs (s : Finset (Fin 6)) : same f s ↔ same g s := by
    simp only [same,h]
  simp only [indicatorOK, hs, imp_self]

private theorem representative {α : Type*} [DecidableEq α] (f : Fin 6 → α) :
    ∃ g : Fin 6 → ℕ, (∀ i, g i ≤ i.val) ∧ (∀ i j, f i = f j ↔ g i = g j) := by
  let fiber (i : Fin 6) := Finset.univ.filter (fun j => f j = f i)
  have mem (i : Fin 6) : i ∈ fiber i := by simp [fiber]
  let pick (i : Fin 6) := (fiber i).min' ⟨i,mem i⟩
  have self (i : Fin 6) : f (pick i) = f i := (Finset.mem_filter.mp
    ((fiber i).min'_mem ⟨i,mem i⟩)).2
  refine ⟨fun i => (pick i).val, fun i => (fiber i).min'_le i (mem i), ?_⟩
  intro i j
  constructor
  · intro h
    have he : fiber i = fiber j := by simp [fiber,h]
    simp only [pick,he]
  · intro h
    have he : pick i = pick j := Fin.ext h
    rw [← self i, he, self j]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem initial_code :
    ∀ (b : Fin 2) (c : Fin 3) (d : Fin 4) (e : Fin 5) (v : Fin 6),
    indicatorOK (![0,b.val,c.val,d.val,e.val,v.val] : Fin 6 → ℕ) := by
  intro b c d e
  fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> decide +kernel

theorem indicator_identity {α : Type*} [DecidableEq α] (f : Fin 6 → α) :
    (if (∃ s ∈ sets 3, same f s) then (0 : ℤ) else 1) =
      1 - (∑ s ∈ sets 3, if same f s then (1 : ℤ) else 0) +
        3 * (∑ s ∈ sets 4, if same f s then (1 : ℤ) else 0) -
        6 * (∑ s ∈ sets 5, if same f s then (1 : ℤ) else 0) +
        (∑ s ∈ dualsets, if same f s ∧ same f sᶜ then (1 : ℤ) else 0) := by
  obtain ⟨g,bound,rel⟩ := representative f
  apply indicator_congr f g rel
  have zero : g 0 = 0 := Nat.eq_zero_of_le_zero (bound 0)
  have hg : g = ![0,g 1,g 2,g 3,g 4,g 5] := by
    funext i
    fin_cases i <;> first | exact zero | rfl
  rw [hg]
  apply initial_code ⟨g 1,Nat.lt_succ_of_le (bound 1)⟩ ⟨g 2,Nat.lt_succ_of_le (bound 2)⟩
    ⟨g 3,Nat.lt_succ_of_le (bound 3)⟩ ⟨g 4,Nat.lt_succ_of_le (bound 4)⟩
    ⟨g 5,Nat.lt_succ_of_le (bound 5)⟩

end Windows250

namespace Windows250

open OMA.S_oeis_a250355
open scoped Classical

private abbrev commonOn {n : ℕ} {s : Finset (Fin 6)} (f : s → Fin (n+1)) : Prop :=
  ∀ i j : s, (f i).val + i.val.val = (f j).val + j.val.val

private theorem restrict_common {n : ℕ} (w : ArrayChoice n) (s : Finset (Fin 6)) :
    same (value w) s ↔ commonOn (fun i : s => w i.val) :=
  ⟨fun h i j => h i.val i.property j.val j.property,
   fun h i hi j hj => h ⟨i,hi⟩ ⟨j,hj⟩⟩

private def commonOffset (n : ℕ) (s : Finset (Fin 6)) (hs : s.Nonempty) :
    {f : s → Fin (n+1) // commonOn f} ≃ Fin (width n s) := by
  let l : s := ⟨s.min' hs, s.min'_mem hs⟩
  let u : s := ⟨s.max' hs, s.max'_mem hs⟩
  have hl (i : s) : l.val.val ≤ i.val.val := s.min'_le _ i.property
  have hu (i : s) : i.val.val ≤ u.val.val := s.le_max' _ i.property
  have hwidth : width n s = n+1-(u.val.val-l.val.val) := by
    simp [width, span, hi, lo, hs, l, u]
  let offset (t : Fin (width n s)) (i : s) : Fin (n+1) :=
    ⟨t.val + (u.val.val-i.val.val), by
      have := t.isLt
      have := hl i
      have := hu i
      omega⟩
  refine
    { toFun := fun f => ⟨(f.val u).val, ?_⟩
      invFun := fun t => ⟨offset t, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have e := f.property u l
    have bl := (f.val l).isLt
    rw [hwidth]
    have := hl u
    omega
  · intro i j
    dsimp [offset]
    have := hu i
    have := hu j
    omega
  · intro f
    apply Subtype.ext
    funext i
    apply Fin.ext
    dsimp [offset]
    have := f.property u i
    have := hu i
    omega
  · intro t
    apply Fin.ext
    simp [offset]

private def splitWindow (n : ℕ) (s : Finset (Fin 6))
    (P : (↥(sᶜ : Finset (Fin 6)) → Fin (n+1)) → Prop) :
    {w : ArrayChoice n // same (value w) s ∧ P (fun i : ↥(sᶜ : Finset (Fin 6)) => w i.val)} ≃
    {f : s → Fin (n+1) // commonOn f} × {g : ↥(sᶜ : Finset (Fin 6)) → Fin (n+1) // P g} := by
  let glue (f : s → Fin (n+1)) (g : ↥(sᶜ : Finset (Fin 6)) → Fin (n+1)) (i : Fin 6) :=
    if h : i ∈ s then f ⟨i,h⟩ else g ⟨i,Finset.mem_compl.mpr h⟩
  have left (f : s → Fin (n+1)) (g : ↥(sᶜ : Finset (Fin 6)) → Fin (n+1)) :
      (fun i : s => glue f g i.val) = f := by
    funext i
    simp [glue,i.property]
  have right (f : s → Fin (n+1)) (g : ↥(sᶜ : Finset (Fin 6)) → Fin (n+1)) :
      (fun i : ↥(sᶜ : Finset (Fin 6)) => glue f g i.val) = g := by
    funext i
    simp [glue, Finset.mem_compl.mp i.property]
  refine
    { toFun := fun w => (⟨fun i => w.val i.val, (restrict_common _ _).mp w.property.1⟩,
                          ⟨fun i => w.val i.val, w.property.2⟩)
      invFun := fun t => ⟨glue t.1.val t.2.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact ⟨(restrict_common _ _).mpr ((left _ _).symm ▸ t.1.property),
            (right _ _).symm ▸ t.2.property⟩
  · intro w
    apply Subtype.ext
    funext i
    dsimp [glue]
    split <;> rfl
  · intro t
    exact Prod.ext (Subtype.ext (left _ _)) (Subtype.ext (right _ _))

private theorem indicator_count {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∑ w : α, if P w then (1:ℤ) else 0) = (Fintype.card {w // P w} : ℤ) := by
  classical
  rw [Fintype.card_subtype, ← Finset.sum_filter]
  simp

theorem sum_same (n : ℕ) (s : Finset (Fin 6)) (hs : s.Nonempty) :
    (∑ w : ArrayChoice n, if same (value w) s then (1 : ℤ) else 0) =
    (width n s : ℤ) * (n+1 : ℤ)^(6-s.card) := by
  have h := Fintype.card_congr (splitWindow n s (fun _ => True))
  have hc := Fintype.card_congr (commonOffset n s hs)
  rw [Fintype.card_prod, hc, Fintype.card_fin] at h
  simp at h
  rw [indicator_count (fun w : ArrayChoice n => same (value w) s)]
  exact_mod_cast h

theorem sum_same_compl (n : ℕ) (s : Finset (Fin 6)) (hs : s.Nonempty)
    (hc : sᶜ.Nonempty) :
    (∑ w : ArrayChoice n, if same (value w) s ∧ same (value w) sᶜ then (1 : ℤ) else 0) =
    (width n s : ℤ) * (width n sᶜ : ℤ) := by
  have h := Fintype.card_congr (splitWindow n s (fun g => commonOn g))
  have h₁ := Fintype.card_congr (commonOffset n s hs)
  have h₂ := Fintype.card_congr (commonOffset n sᶜ hc)
  rw [indicator_count (fun w : ArrayChoice n => same (value w) s ∧ same (value w) sᶜ)]
  rw [Fintype.card_prod, h₁, h₂] at h
  simp only [← restrict_common, Fintype.card_fin] at h
  exact_mod_cast h

end Windows250

namespace Windows250
open Finset

def raw (n : ℕ) : ℤ :=
  let x := (n:ℤ)+1
  x^6 - (∑ s ∈ sets 3, (width n s:ℤ))*x^3
    + 3*((∑ s ∈ sets 4, (width n s:ℤ))*x^2)
    - 6*((∑ s ∈ sets 5, (width n s:ℤ))*x)
    + ∑ s ∈ dualsets, (width n s:ℤ)*(width n sᶜ:ℤ)

theorem cast_width {n : ℕ} (hn : 4≤n) (s : Finset (Fin 6)) :
    (width n s:ℤ)=(n:ℤ)+1-(span s:ℤ) := by
  have hh : hi s≤5 := by
    unfold hi
    split_ifs with h
    · exact Nat.le_of_lt_succ (s.max' h).isLt
    · decide
  have hs : span s≤n+1 := by dsimp [span]; omega
  simp only [width,Nat.cast_sub hs,Nat.cast_add,Nat.cast_one]

theorem sum_width {n : ℕ} (hn : 4≤n) (S : Finset (Finset (Fin 6))) :
    (∑ s ∈ S, (width n s:ℤ))=S.card*((n:ℤ)+1) - ∑ s ∈ S, (span s:ℤ) := by
  simp only [cast_width hn,sum_sub_distrib,sum_const,nsmul_eq_mul]

theorem sum_width_product {n : ℕ} (hn : 4≤n) :
    (∑ s ∈ dualsets, (width n s:ℤ)*(width n sᶜ:ℤ)) =
      10*((n:ℤ)+1)^2-70*((n:ℤ)+1)+119 := by
  let x := (n:ℤ)+1
  have expand (s : Finset (Fin 6)) : (width n s:ℤ)*(width n sᶜ:ℤ) =
      x^2-x*((span s:ℤ)+(span sᶜ:ℤ))+(span s:ℤ)*(span sᶜ:ℤ) := by
    rw [cast_width hn,cast_width hn]; dsimp [x]; ring
  have h0 : dualsets.card=10 := by decide +kernel
  have h1 : (∑ s ∈ dualsets, ((span s:ℤ)+(span sᶜ:ℤ)))=70 := by decide +kernel
  have h2 : (∑ s ∈ dualsets, (span s:ℤ)*(span sᶜ:ℤ))=119 := by decide +kernel
  simp only [expand,sum_add_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,←mul_sum,h0,h1,h2]
  dsimp [x]
  ring

def polynomial (n : ℤ) : ℤ := n^6+6*n^5-5*n^4+55*n^3+25*n^2-61*n+98

theorem raw_polynomial {n : ℕ} (hn : 4≤n) : raw n=polynomial n := by
  have h3 : (sets 3).card=20 := by decide +kernel
  have h4 : (sets 4).card=15 := by decide +kernel
  have h5 : (sets 5).card=6 := by decide +kernel
  have s3 : (∑ s ∈ sets 3,(span s:ℤ))=70 := by decide +kernel
  have s4 : (∑ s ∈ sets 4,(span s:ℤ))=63 := by decide +kernel
  have s5 : (∑ s ∈ sets 5,(span s:ℤ))=28 := by decide +kernel
  simp only [raw, sum_width hn, sum_width_product hn,h3,h4,h5,s3,s4,s5,polynomial]
  norm_num
  ring

theorem raw_recurrence (n : ℕ) (hn : 10<n) :
    raw n=7*raw (n-1)-21*raw (n-2)+35*raw (n-3)-35*raw (n-4)+21*raw (n-5)
      -7*raw (n-6)+raw (n-7) := by
  simp (disch := omega) only [raw_polynomial,Nat.cast_sub,polynomial]
  push_cast
  ring

theorem raw_initial : raw 1=64 ∧ raw 2=622 ∧ raw 3=3349 ∧ raw 4=12734 ∧
    raw 5=38543 ∧ raw 6=99344 ∧ raw 7=226247 ∧ raw 8=467642 ∧ raw 9=894599 ∧ raw 10=1606988 := by
  decide +kernel

end Windows250

namespace Windows250
open Finset OMA.S_oeis_a250355

theorem mem_sets {s : Finset (Fin 6)} {k : ℕ} : s ∈ sets k ↔ s.card=k := by
  simp [sets]

theorem bad_iff_subset {n : ℕ} (w : ArrayChoice n) :
    bad w ↔ ∃ s ∈ sets 3, same (value w) s := by
  constructor
  · rintro ⟨⟨s,hs⟩,h⟩
    exact ⟨s,mem_sets.mpr hs,h⟩
  · rintro ⟨s,hs,h⟩
    exact ⟨⟨s,mem_sets.mp hs⟩,h⟩

theorem count_with (n : ℕ) (hn : n≠0)
    (indicator : ∀ w : ArrayChoice n,
      (if ∃ s ∈ sets 3, same (value w) s then (0:ℤ) else 1) =
        1 - (∑ s ∈ sets 3, if same (value w) s then (1:ℤ) else 0) +
        3*(∑ s ∈ sets 4, if same (value w) s then (1:ℤ) else 0) -
        6*(∑ s ∈ sets 5, if same (value w) s then (1:ℤ) else 0) +
        (∑ s ∈ dualsets, if same (value w) s ∧ same (value w) sᶜ then (1:ℤ) else 0))
    (single : ∀ s : Finset (Fin 6), s.Nonempty →
      (∑ w : ArrayChoice n,if same (value w) s then (1:ℤ) else 0) =
        (width n s:ℤ)*((n:ℤ)+1)^(6-s.card))
    (dual : ∀ s : Finset (Fin 6), s.Nonempty → sᶜ.Nonempty →
      (∑ w : ArrayChoice n,if same (value w) s ∧ same (value w) sᶜ then (1:ℤ) else 0) =
        (width n s:ℤ)*(width n sᶜ:ℤ)) :
    (a n:ℤ)=raw n := by
  classical
  have base : (a n:ℤ)=∑ w : ArrayChoice n,if ∃ s ∈ sets 3, same (value w) s then (0:ℤ) else 1 := by
    rw [a,if_neg hn,Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter,Nat.cast_sum]
    apply sum_congr rfl
    intro w _
    by_cases h : bad w
    · simp [h,(bad_iff_subset w).mp h]
    · have hh := mt (bad_iff_subset w).mpr h
      simp [h,hh]
  have sum_k (k : ℕ) (hk : 0<k) :
      (∑ w : ArrayChoice n,∑ s ∈ sets k,if same (value w) s then (1:ℤ) else 0) =
        (∑ s ∈ sets k,(width n s:ℤ))*((n:ℤ)+1)^(6-k) := by
    rw [sum_comm,Finset.sum_mul]
    apply sum_congr rfl
    intro s hs
    have hcard := mem_sets.mp hs
    rw [single s (card_pos.mp (by omega)),hcard]
  have sum_d : (∑ w : ArrayChoice n,∑ s ∈ dualsets,
      if same (value w) s ∧ same (value w) sᶜ then (1:ℤ) else 0) =
        ∑ s ∈ dualsets,(width n s:ℤ)*(width n sᶜ:ℤ) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro s hs
    have hs3 : s.card=3 := mem_sets.mp (mem_filter.mp hs).1
    have hc3 : sᶜ.card=3 := by simp [card_compl,hs3]
    exact dual _ (card_pos.mp (by omega)) (card_pos.mp (by omega))
  rw [base]
  simp only [indicator, sum_add_distrib,sum_sub_distrib,←mul_sum,sum_k _ (by decide : 0<3),
    sum_k _ (by decide : 0<4),sum_k _ (by decide : 0<5),sum_d]
  simp [raw,Fintype.card_pi]

end Windows250

namespace Window250
open PowerSeries

theorem series_finish (a : ℕ → ℕ) (h0 : a 0=0) (h1 : a 1=64)
    (h2 : a 2=622) (h3 : a 3=3349) (h4 : a 4=12734) (h5 : a 5=38543)
    (h6 : a 6=99344) (h7 : a 7=226247) (h8 : a 8=467642)
    (h9 : a 9=894599) (h10 : a 10=1606988)
    (rec : ∀ n : ℕ, 10<n →
      (a n : ℤ) = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+
        21*a (n-5)-7*a (n-6)+a (n-7)) :
    ((1 - X)^7 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (64+174*X+339*X^2+113*X^3+204*X^4+168*X^5-
        847*X^6+783*X^7-336*X^8+58*X^9)) ∧
    (∀ n : ℕ, 10<n →
      (a n : ℤ) = 7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+
        21*a (n-5)-7*a (n-6)+a (n-7)) := by
  refine ⟨?_,rec⟩
  let S : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have vals (n : ℕ) : coeff n S = (a n:ℤ) := coeff_mk _ _
  have left : (1-X)^7*S =
      S-C (7:ℤ)*(S*X^1)+C (21:ℤ)*(S*X^2)-C (35:ℤ)*(S*X^3)+C (35:ℤ)*(S*X^4)-
      C (21:ℤ)*(S*X^5)+C (7:ℤ)*(S*X^6)-S*X^7 := by
    simp only [map_ofNat]; ring
  have right : X*(64+174*X+339*X^2+113*X^3+204*X^4+168*X^5-
        847*X^6+783*X^7-336*X^8+58*X^9 : PowerSeries ℤ) =
      C (64:ℤ)*X^1+C (174:ℤ)*X^2+C (339:ℤ)*X^3+C (113:ℤ)*X^4+
      C (204:ℤ)*X^5+C (168:ℤ)*X^6-C (847:ℤ)*X^7+C (783:ℤ)*X^8-
      C (336:ℤ)*X^9+C (58:ℤ)*X^10 := by
    simp only [map_ofNat]; ring
  change _*S = _
  rw [left,right]
  ext n
  simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_C,vals]
  by_cases h : n≤10
  · interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
  · simp (disch := omega) only [if_pos,if_neg]
    linarith [rec n (by omega)]

end Window250

namespace Windows250
open OMA.S_oeis_a250355

theorem count_formula (n : ℕ) (hn : n≠0) : (a n:ℤ)=raw n :=
  count_with n hn (fun w => indicator_identity (value w)) (sum_same n) (sum_same_compl n)

theorem eventual_polynomial (n : ℕ) (hn : 4≤n) :
    (a n:ℤ)=(n:ℤ)^6+6*(n:ℤ)^5-5*(n:ℤ)^4+55*(n:ℤ)^3+25*(n:ℤ)^2-61*(n:ℤ)+98 :=
  (count_formula n (by omega)).trans (raw_polynomial hn)

theorem recurrence (n : ℕ) (hn : 10<n) :
    (a n:ℤ)=7*a (n-1)-21*a (n-2)+35*a (n-3)-35*a (n-4)+21*a (n-5)
      -7*a (n-6)+a (n-7) := by
  simpa (disch := omega) only [count_formula] using raw_recurrence n hn

end Windows250

open OMA.S_oeis_a250355 Windows250

theorem OMA.solution : type_of% @OMA.S_oeis_a250355.main := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := raw_initial
  apply Window250.series_finish OMA.S_oeis_a250355.a
  · simp [OMA.S_oeis_a250355.a]
  all_goals first | exact Windows250.recurrence | (
    apply Int.ofNat_inj.mp
    rw [Windows250.count_formula _ (by decide)]
    assumption)
