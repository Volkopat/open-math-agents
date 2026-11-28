import OMAStatements.S_oeis_a249964
import Mathlib

/-!
# Nine-letter arrays with four six-letter window constraints

This proves Barker's formulas for Hardin's A249964, https://oeis.org/A249964.
The native comparison of a pair maximum to the infimum over the other four
positions is equivalent to a tied split into two lower and four upper entries.
We adapt the six-entry criterion from A249963 and the ranked-transfer argument
from A250392 (#32394). The four window masks on nine positions are checked
independently, and the generating function begins with a(1).
-/

namespace Six964
def zCount (n : ℕ) : ℤ := OMA.S_oeis_a249964.a n
end Six964

/-! Six-entry threshold criterion from the proof of OEIS A249963. -/

namespace Six964
open Finset

/-! ### The window condition -/

/-- The condition of the statement on 6 values (without the bound on `v`). -/
def Cy (y : Fin 6 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 6)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 6 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
  obtain ⟨S, hS, v, h1, ⟨s, hs, hsv⟩, h3, ⟨t0, ht0, ht0v⟩⟩ := h
  have hc : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
  by_cases hw : w < v
  · have hsub : univ.filter (fun t => y t ≤ w) ⊆ S.erase s := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have htS : t ∈ S := by
        by_contra hn
        have := h3 t hn
        omega
      refine Finset.mem_erase.2 ⟨?_, htS⟩
      rintro rfl
      omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hs, hc] at h1'
    omega
  · have hsub : insert t0 S ⊆ univ.filter (fun t => y t ≤ w) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · have := h1 t ht'
        omega
    have h1' := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ht0, hc] at h1'
    omega

theorem cy_of (y : Fin 6 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 6)) y Finset.univ_nonempty
    refine ⟨m, ?_⟩
    rw [hU, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : univ.filter (fun t => y t ≤ y m) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      exact hm t (Finset.mem_univ t)
    rw [this]
    simp
  obtain ⟨s, hsU, hmin⟩ := Finset.exists_min_image U y hUne
  have hs2 : 2 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    rw [hU, Finset.mem_filter] at hsU
    exact hsU.2
  have hs3 : 3 ≤ (univ.filter (fun t => y t ≤ y s)).card := by
    have := h (y s)
    omega
  set L := univ.filter (fun t => y t < y s) with hL
  set E := univ.filter (fun t => y t = y s) with hE
  have hLc : L.card ≤ 1 := by
    by_cases hLne : L.Nonempty
    · obtain ⟨l, hl, hlmax⟩ := Finset.exists_max_image L y hLne
      have hyl : y l < y s := by
        rw [hL, Finset.mem_filter] at hl
        exact hl.2
      have hlU : l ∉ U := by
        intro hlU
        have := hmin l hlU
        omega
      have hcl : (univ.filter (fun t => y t ≤ y l)).card ≤ 1 := by
        rw [hU, Finset.mem_filter] at hlU
        have : ¬ 2 ≤ (univ.filter (fun t => y t ≤ y l)).card :=
          fun h2 => hlU ⟨Finset.mem_univ _, h2⟩
        omega
      have hsub : L ⊆ univ.filter (fun t => y t ≤ y l) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlmax t ht
      exact le_trans (Finset.card_le_card hsub) hcl
    · rw [Finset.not_nonempty_iff_eq_empty.mp hLne]
      simp
  have hsplit : (univ.filter (fun t => y t ≤ y s)) ⊆ L ∪ E := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [Finset.mem_union, hL, hE, Finset.mem_filter, Finset.mem_filter]
    rcases Nat.lt_or_ge (y t) (y s) with h' | h'
    · exact Or.inl ⟨Finset.mem_univ _, h'⟩
    · exact Or.inr ⟨Finset.mem_univ _, by omega⟩
  have hcard := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le L E)
  have hsE : s ∈ E := by
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hnotL : ∀ t, ¬ y t < y s → t ∉ L := by
    intro t ht htL
    rw [hL, Finset.mem_filter] at htL
    exact ht htL.2
  rcases Nat.lt_or_ge 0 L.card with hpos | hzero
  · -- one value below `y s`
    obtain ⟨l, hLl⟩ := Finset.card_eq_one.1 (by omega : L.card = 1)
    have hlL : l ∈ L := by rw [hLl]; exact Finset.mem_singleton_self l
    have hyl : y l < y s := by
      rw [hL, Finset.mem_filter] at hlL
      exact hlL.2
    have hE1 : 1 ≤ (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < (E.erase s).card)
    have hes : e ≠ s := (Finset.mem_erase.1 he).1
    have hye : y e = y s := by
      have := (Finset.mem_erase.1 he).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hls : l ≠ s := by
      rintro rfl
      omega
    refine ⟨{l, s}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e, ?_, hye⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair hls⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · omega
      · rw [Finset.mem_singleton.1 ht']
    · intro t ht
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLl, Finset.mem_singleton] at htL
      apply ht
      rw [htL]
      exact Finset.mem_insert_self l {s}
    · intro he'
      rcases Finset.mem_insert.1 he' with rfl | he''
      · omega
      · exact hes (Finset.mem_singleton.1 he'')
  · -- no value below `y s`
    have hL0 : L.card = 0 := by omega
    have hE3 : 3 ≤ E.card := by omega
    have hE2 : 1 < (E.erase s).card := by
      rw [Finset.card_erase_of_mem hsE]
      omega
    obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.1 hE2
    have he1s : e1 ≠ s := (Finset.mem_erase.1 he1).1
    have he2s : e2 ≠ s := (Finset.mem_erase.1 he2).1
    have hye1 : y e1 = y s := by
      have := (Finset.mem_erase.1 he1).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hye2 : y e2 = y s := by
      have := (Finset.mem_erase.1 he2).2
      rw [hE, Finset.mem_filter] at this
      exact this.2
    have hLempty : L = ∅ := Finset.card_eq_zero.1 hL0
    refine ⟨{s, e1}, ?_, y s, ?_, ⟨s, by simp, rfl⟩, ?_, ⟨e2, ?_, hye2⟩⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, Finset.card_pair he1s.symm⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · exact le_rfl
      · rw [Finset.mem_singleton.1 ht', hye1]
    · intro t _
      by_contra hlt
      rw [not_le] at hlt
      have htL : t ∈ L := by
        rw [hL, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hlt⟩
      rw [hLempty] at htL
      exact Finset.notMem_empty t htL
    · intro he'
      rcases Finset.mem_insert.1 he' with h' | h'
      · exact he2s h'
      · exact he12 (Finset.mem_singleton.1 h').symm

theorem window_iff (y : Fin 6 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 6 → ℕ) :
    ¬ Cy y ↔ ∀ v : ℕ, ¬ ((univ.filter (fun t => y t < v)).card ≤ 1 ∧
      3 ≤ (univ.filter (fun t => y t < v + 1)).card) := by
  rw [window_iff, not_forall]
  simp only [ne_eq, not_not]
  constructor
  · rintro ⟨w, hw⟩ v ⟨h1, h3⟩
    rcases Nat.lt_or_ge w v with h | h
    · have hsub : univ.filter (fun t => y t ≤ w) ⊆ univ.filter (fun t => y t < v) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
    · have hsub : univ.filter (fun t => y t < v + 1) ⊆ univ.filter (fun t => y t ≤ w) := by
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        omega
      have := Finset.card_le_card hsub
      omega
  · intro h
    by_contra hne
    simp only [not_exists] at hne
    have key : ∀ v, (univ.filter (fun t => y t < v)).card ≤ 1 := by
      intro v
      induction v with
      | zero => simp
      | succ v ih =>
        have h1 := h v
        have h2 := hne v
        have e : univ.filter (fun t => y t < v + 1) = univ.filter (fun t => y t ≤ v) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [e] at h1 ⊢
        by_contra hc
        exact h1 ⟨ih, by omega⟩
    have hall : univ.filter (fun t => y t < univ.sup y + 1) = univ := by
      apply Finset.filter_true_of_mem
      intro t _
      have := Finset.le_sup (f := y) (Finset.mem_univ t)
      omega
    have := key (univ.sup y + 1)
    rw [hall] at this
    simp at this

end Six964

namespace Six964
open Finset OMA.S_oeis_a249964

/-- An attained minimum on the complement of a pair is equivalent to the subset formulation. -/
theorem maxPair_iff_cy (w : Fin 6 → ℕ) : MaxPairEqMinRest w ↔ Cy w := by
  classical
  constructor
  · rintro ⟨i, j, hij, h⟩
    let v := max (w i) (w j)
    change (v : WithTop ℕ) = _ at h
    have lower (t : Fin 6) (ht : t ∉ ({i,j} : Finset (Fin 6))) : v ≤ w t := by
      have h' : (v : WithTop ℕ) ≤ (w t : WithTop ℕ) := h.le.trans <|
        Finset.inf_le (f := fun k => (w k : WithTop ℕ)) (mem_compl.mpr ht)
      exact_mod_cast h'
    refine ⟨{i,j}, mem_powersetCard.mpr ⟨subset_univ _,card_pair hij⟩, v, ?_, ?_, lower, ?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact le_max_left _ _
      · exact (mem_singleton.mp ht) ▸ le_max_right _ _
    · rcases le_total (w i) (w j) with hij' | hji'
      · exact ⟨j, by simp, (max_eq_right hij').symm⟩
      · exact ⟨i, by simp, (max_eq_left hji').symm⟩
    · by_contra! hn
      have hplus : ((v+1 : ℕ) : WithTop ℕ) ≤ v := by
        rw [h]
        apply Finset.le_inf
        intro t ht
        have ht' := mem_compl.mp ht
        have hlow := lower t ht'
        have hne := hn t ht'
        exact_mod_cast (show v+1 ≤ w t by omega)
      have : v+1 ≤ v := by exact_mod_cast hplus
      omega
  · rintro ⟨S,hS,v,hlo,⟨t,ht,het⟩,hhi,⟨k,hk,hek⟩⟩
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (mem_powersetCard.mp hS).2
    have hv : max (w i) (w j) = v := by
      have h₁ := hlo i (by simp)
      have h₂ := hlo j (by simp)
      rcases mem_insert.mp ht with rfl | ht
      · omega
      · rw [mem_singleton.mp ht] at het
        omega
    refine ⟨i,j,hij,?_⟩
    rw [hv]
    refine le_antisymm (Finset.le_inf fun t ht => WithTop.coe_le_coe.mpr (hhi t (mem_compl.mp ht))) ?_
    rw [← hek]
    exact Finset.inf_le (f := fun t => (w t : WithTop ℕ)) (mem_compl.mpr hk)

end Six964

/-!
The nine-position threshold-chain recursion is adapted from A250062 (PR #32716)
and A250392 (PR #32394), following the A250391 and A250064 proofs.
-/

namespace Six964
open OMA.S_oeis_a249964 Finset

/-! ### Strict threshold sets -/

/-- Entry `k` of a set of positions (`false` past the end). -/
def fget (f : Fin 9 → Bool) (k : ℕ) : Bool := if h : k < 9 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 9 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 6 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 9 → Bool) : Prop := ∀ i < (4 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 9 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 9 → Fin (n + 1)) (v : ℕ) : Fin 9 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem cnt_univ : ∀ i < (4 : ℕ), cntW (fun _ => true) i = 6 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 9 → Fin (n + 1)) :
    (∀ i : Fin 4, ¬ MaxPairEqMinRest (window x i)) ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step2 (i : Fin 4) (v : ℕ) :
      (univ.filter (fun t : Fin 6 => window x i t < v)).card = cntW (Lt x v) i.val := by
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i.val+t.val < 9 := by have := i.isLt; have := t.isLt; omega
    unfold window fget Lt
    rw [dif_pos ht,decide_eq_true_iff]
  have hfull : ∀ w, n < w → Lt x w = fun _ => true := by
    intro w hw
    funext p
    unfold Lt
    have := (x p).isLt
    simp only [decide_eq_true_iff]
    omega
  constructor
  · intro h v _ i hi
    let j : Fin 4 := ⟨i,hi⟩
    have hcy : ¬ Cy (window x j) := fun hc => h j ((maxPair_iff_cy _).2 hc)
    simpa only [step2 j v, step2 j (v+1)] using (not_cy_iff _).1 hcy v
  · intro h i hm
    have hn : ¬ Cy (window x i) := by
      apply (not_cy_iff _).2
      intro v
      rw [step2 i v,step2 i (v+1)]
      by_cases hv : v ≤ n
      · exact h v hv i i.isLt
      · rw [hfull v (by omega),cnt_univ i i.isLt]
        omega
    exact hn ((maxPair_iff_cy _).1 hm)

/-! ### Chains of strict threshold sets -/

/-- Arrays with entries in `0..n` whose consecutive strict threshold sets are compatible, with
`Lt x n ⊆ T` and `Lt x n` compatible with `T`. -/
noncomputable def M (n : ℕ) (T : Fin 9 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 9 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 9 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
  classical
  unfold M
  split_ifs with h
  · rw [Finset.filter_true_of_mem]
    · simp
    · intro x _
      refine ⟨fun p hp => ?_, fun v hv => absurd hv (Nat.not_lt_zero _), ?_⟩
      · rw [Lt_zero] at hp
        exact absurd hp (by simp)
      · rw [Lt_zero]
        exact h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply h
    rw [← Lt_zero x]
    exact hx.2.2

/-- Restriction of an array with entries in `0..n+1` to entries in `0..n`. -/
def lower {n : ℕ} (x : Fin 9 → Fin (n + 2)) : Fin 9 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 9 → Bool) (x : Fin 9 → Fin (n + 1)) : Fin 9 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 9 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 9 → Bool) (x : Fin 9 → Fin (n + 1)) (p : Fin 9) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 9 → Bool) :
    M (n + 1) T = ∑ S : Fin 9 → Bool,
      if Comp S T ∧ (∀ p, S p = true → T p = true) then M n S else 0 := by
  classical
  unfold M
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => Lt x (n + 1)) (t := univ)
    (fun x _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hS
  · apply Finset.card_bij' (fun x _ => lower x) (fun x _ => raise S x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨⟨_, h2, _⟩, h3⟩ := hx
      refine ⟨fun p hp => ?_, fun v hv => ?_, ?_⟩
      · rw [Lt_lower x n le_rfl] at hp
        rw [← h3]
        have hp' : (x p : ℕ) < n := of_decide_eq_true hp
        exact decide_eq_true (by omega)
      · rw [Lt_lower x v (by omega), Lt_lower x (v + 1) (by omega)]
        exact h2 v (by omega)
      · rw [Lt_lower x n le_rfl, ← h3]
        exact h2 n (by omega)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2, h3⟩ := hx
      have hTS : Lt (raise S x) (n + 1) = S := by
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < n + 1) = S p
        rw [raise_val]
        by_cases hp : S p = true
        · rw [if_pos hp, hp]
          have := (x p).isLt
          exact decide_eq_true (by omega)
        · rw [if_neg hp]
          simp only [Bool.not_eq_true] at hp
          rw [hp]
          exact decide_eq_false (by omega)
      have hlow : ∀ v ≤ n, Lt (raise S x) v = Lt x v := by
        intro v hv
        funext p
        show decide (((raise S x p : Fin (n + 2)) : ℕ) < v) = decide ((x p : ℕ) < v)
        rw [raise_val]
        split_ifs with hp
        · rfl
        · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
          rw [decide_eq_decide]
          omega
      refine ⟨⟨?_, fun v hv => ?_, ?_⟩, hTS⟩
      · rw [hTS]
        exact hS.2
      · rcases Nat.lt_or_ge v n with hv' | hv'
        · rw [hlow v (by omega), hlow (v + 1) (by omega)]
          exact h2 v hv'
        · obtain rfl : v = n := by omega
          rw [hlow v le_rfl, hTS]
          exact h3
      · rw [hTS]
        exact hS.1
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨_, h3⟩ := hx
      funext p
      apply Fin.ext
      rw [raise_val]
      have hiff : S p = true ↔ (x p : ℕ) < n + 1 := by
        rw [← h3]
        exact decide_eq_true_iff
      split_ifs with hp
      · show min (x p : ℕ) n = x p
        have := hiff.1 hp
        omega
      · have : ¬ (x p : ℕ) < n + 1 := fun h => hp (hiff.2 h)
        have := (x p).isLt
        omega
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨h1, _⟩ := hx
      funext p
      apply Fin.ext
      show min ((raise S x p : Fin (n + 2)) : ℕ) n = x p
      rw [raise_val]
      split_ifs with hp
      · have := (x p).isLt
        omega
      · have hxp : ¬ (x p : ℕ) < n := fun h => hp (h1 p (decide_eq_true h))
        have := (x p).isLt
        omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    rintro ⟨⟨h1, _, h3⟩, h4⟩
    apply hS
    rw [← h4]
    exact ⟨h3, h1⟩

/-! ### Codes -/

/-- The set of positions with code `u`: position `p` is in it iff bit `p` of `u` is set. -/
def row (u : Fin 512) : Fin 9 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 9 → Bool) : ℕ := ∑ p : Fin 9, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 512, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 9 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2 + m / 256 % 2

theorem cnt_row : ∀ u : Fin 512, cntW (row u) 0 = pcb (u.val &&& 63) ∧
    cntW (row u) 1 = pcb (u.val &&& 126) ∧
    cntW (row u) 2 = pcb (u.val &&& 252) ∧
    cntW (row u) 3 = pcb (u.val &&& 504) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 63) ≤ 1 ∧ 3 ≤ pcb (t &&& 63)) ∧
    ¬ (pcb (s &&& 126) ≤ 1 ∧ 3 ≤ pcb (t &&& 126)) ∧
    ¬ (pcb (s &&& 252) ≤ 1 ∧ 3 ≤ pcb (t &&& 252)) ∧
    ¬ (pcb (s &&& 504) ≤ 1 ∧ 3 ≤ pcb (t &&& 504)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (4 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩
  · rintro ⟨h0, h1, h2, h3⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 512) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0,a1,a2,a3⟩ := cnt_row s
  obtain ⟨b0,b1,b2,b3⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff,a0,a1,a2,a3,b0,b1,b2,b3]

theorem sub_iff (w u : Fin 512) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 9
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (512 : ℕ) ≤ 2 ^ i := by
          calc (512 : ℕ) = 2 ^ 9 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := w.isLt
        omega
      simp [hw]
  · intro h p hp
    unfold row at hp ⊢
    rw [← h, Nat.testBit_land] at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.2

/-- The codes of the subsets of the set with code `u`. -/
def subs (u : Fin 512) : Finset (Fin 512) :=
  univ.filter (fun w : Fin 512 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 512 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 512, M n (row u) = G n u := by
  induction n with
  | zero =>
    intro u
    rw [M_zero, ← row_zero, G]
    exact if_congr (compc_iff 0 u) rfl rfl
  | succ n ih =>
    intro u
    rw [M_succ, ← row_bijective.sum_comp]
    simp only [G, subs]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih w]
    by_cases h1 : (w.val &&& u.val == w.val) = true
    · rw [if_pos h1]
      exact if_congr ((and_iff_left ((sub_iff w u).2 h1)).trans (compc_iff w u)) rfl rfl
    · rw [if_neg h1, if_neg (fun h => h1 ((sub_iff w u).1 h.2))]

theorem row_full : ∀ p, row 511 p = true := by
  decide

theorem a_eq_G (n : ℕ) : zCount n = (G n 511 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 9 → Fin (n + 1) => ∀ i : Fin 4, ¬ MaxPairEqMinRest (window x i))) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 511 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 511)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 511 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 511 := by
      rw [hr]
      funext p
      unfold Lt
      have := (x p).isLt
      simp only [decide_eq_true_iff]
      omega
    constructor
    · intro h
      refine ⟨fun p _ => row_full p, fun v hv => h v (by omega), ?_⟩
      rw [← hn]
      exact h n le_rfl
    · rintro ⟨_, h2, h3⟩ v hv
      rcases Nat.lt_or_ge v n with h | h
      · exact h2 v h
      · obtain rfl : v = n := by omega
        rw [hn]
        exact h3
  unfold zCount a
  rw [h1, ← M_eq_G]
  unfold M
  congr 2

/-! ### The recurrence -/

theorem G_succ (n : ℕ) (u : Fin 512) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl

end Six964

namespace Six964
open Finset

/-- Repeated strict transitions produce the coefficients of the binomial
expansion. A chain arriving at a state cannot have more steps than its rank. -/
theorem binomial_transfer {ι : Type*} (pred : ι → Finset ι) (rank : ι → ℕ)
    (d : ℕ) (hr : ∀ x, ∀ y ∈ pred x, rank y < rank x)
    (M : ℕ → ι → ℕ)
    (step : ∀ n x, M (n+1) x = M n x + ∑ y ∈ pred x, M n y)
    (x : ι) (hx : rank x ≤ d) :
    ∃ c : Fin (d+1) → ℤ, ∀ n : ℕ, (M n x : ℤ) = ∑ j, c j * (n.choose j.val : ℤ) := by
  classical
  let C : ℕ → ι → ℕ := Nat.rec (M 0) (fun _ prev z => ∑ y ∈ pred z, prev y)
  have cstep (k : ℕ) (z : ι) : C (k+1) z = ∑ y ∈ pred z, C k y := rfl
  have vanish (k : ℕ) (z : ι) (hk : rank z < k) : C k z = 0 := by
    induction k generalizing z with
    | zero => omega
    | succ k ih =>
      rw [cstep]
      exact sum_eq_zero (fun y hy => ih y (by have := hr z y hy; omega))
  have expand (n : ℕ) (z : ι) :
      M n z = ∑ j ∈ range (n+1), C j z * n.choose j := by
    induction n generalizing z with
    | zero => simp [C]
    | succ n ih =>
      have shift : (∑ j ∈ range (n+1), C (j+1) z * n.choose (j+1)) + C 0 z =
          ∑ j ∈ range (n+1), C j z * n.choose j := by
        calc
          _ = ∑ j ∈ range (n+1+1), C j z * n.choose j := by
            rw [sum_range_succ' (fun j => C j z * n.choose j)]; simp
          _ = _ := by rw [sum_range_succ]; simp
      rw [step,ih,sum_range_succ' (fun j => C j z * (n+1).choose j)]
      simp only [Nat.choose_succ_succ,Nat.choose_zero_right,mul_one,mul_add,sum_add_distrib]
      have sub (k : ℕ) : (∑ y ∈ pred z, C k y * n.choose k) = C (k+1) z * n.choose k := by
        rw [cstep,sum_mul]
      calc
        _ = (∑ j ∈ range (n+1), C j z * n.choose j) +
            ∑ k ∈ range (n+1), C (k+1) z * n.choose k := by
              simp_rw [ih]
              rw [sum_comm (s := pred z),show (∑ k ∈ range (n+1), ∑ y ∈ pred z, C k y * n.choose k) =
                  ∑ k ∈ range (n+1), C (k+1) z * n.choose k from sum_congr rfl (fun k _ => sub k)]
        _ = _ := by rw [← shift]; ac_rfl
  refine ⟨fun j => Int.ofNat (C j.val x),?_⟩
  intro n
  rw [Fin.sum_univ_eq_sum_range (fun j => Int.ofNat (C j x) * (n.choose j : ℤ))]
  suffices h : M n x = ∑ j ∈ range (d+1), C j x * n.choose j by
    rw [h,Nat.cast_sum]
    simp only [Nat.cast_mul]
    rfl
  rw [expand]
  rcases le_total n d with hn | hd
  · apply sum_subset (range_mono (by omega))
    intro j hj hnj
    simp only [mem_range] at hnj
    simp [Nat.choose_eq_zero_of_lt (show n < j by omega)]
  · symm
    apply sum_subset (range_mono (by omega))
    intro j hj hdj
    simp only [mem_range] at hdj
    simp [vanish j x (by omega)]

end Six964

namespace Six964
open Finset
open scoped Classical

/-- Transfers between increasing threshold sets have degree at most the number of positions. -/
theorem threshold_polynomial {d : ℕ}
    (edge : (Fin d → Bool) → (Fin d → Bool) → Prop) [DecidableRel edge]
    (refl : ∀ T, edge T T)
    (incl : ∀ {S T}, edge S T → ∀ p, S p = true → T p = true)
    (A : ℕ → (Fin d → Bool) → ℕ)
    (advance : ∀ n T, A (n+1) T = ∑ S, if edge S T then A n S else 0)
    (T : Fin d → Bool) :
    ∃ c : Fin (d+1) → ℤ, ∀ n : ℕ, (A n T : ℤ) = ∑ j, c j * (n.choose j.val : ℤ) := by
  let members (U : Fin d → Bool) := univ.filter (fun p => U p = true)
  let allowed (U : Fin d → Bool) := univ.filter (fun V => edge V U)
  let pred (U : Fin d → Bool) := (allowed U).erase U
  have ident : Function.Injective members := by
    intro U V huv
    funext p
    have e : p ∈ members U ↔ p ∈ members V := by rw [huv]
    apply Bool.eq_iff_iff.mpr
    simpa only [members,mem_filter,mem_univ,true_and] using e
  refine binomial_transfer pred (fun U => (members U).card) d ?_ A ?_ T ?_
  · intro U V hv
    obtain ⟨hne, he⟩ : V ≠ U ∧ edge V U := by
      simpa only [pred,allowed,mem_erase,mem_filter,mem_univ,true_and] using hv
    apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun e => hne (ident e)⟩)
    intro p hp
    simpa only [members,mem_filter,mem_univ,true_and] using incl he p
      (by simpa only [members,mem_filter,mem_univ,true_and] using hp)
  · intro n U
    have hu : U ∈ allowed U := by simp [allowed,refl]
    have h := Finset.add_sum_erase (allowed U) (A n) hu
    rw [advance]
    simpa only [pred,allowed,sum_filter] using h.symm
  · simpa [members] using (Finset.card_filter_le (s:=univ) (fun p => T p=true))

end Six964

namespace Six964
open OMA.S_oeis_a249964
open scoped Classical

theorem count_shape : ∃ c : Fin 10 → ℤ, ∀ n : ℕ,
    zCount (n+1) = ∑ j, c j * (n.choose j.val : ℤ) := by
  let edge (S T : Fin 9 → Bool) := Comp S T ∧ ∀ p, S p = true → T p = true
  let : DecidableRel edge := fun S T => inferInstanceAs
    (Decidable (Comp S T ∧ ∀ p, S p = true → T p = true))
  have refl (T : Fin 9 → Bool) : edge T T := by
    refine ⟨?_, fun p hp => hp⟩
    intro i hi bad
    omega
  have next (n : ℕ) (T : Fin 9 → Bool) :
      M (n+1+1) T = ∑ S, if edge S T then M (n+1) S else 0 := by
    exact M_succ (n+1) T
  obtain ⟨c,hc⟩ := threshold_polynomial (d := 9) edge refl (fun h => h.2)
    (fun n => M (n+1)) next (row 511)
  refine ⟨c,fun n => ?_⟩
  rw [a_eq_G,←M_eq_G]
  exact hc n
end Six964

namespace Six964

open OMA.S_oeis_a249964 Finset

/- The packed certificate follows the method used for A249849, which credits
@Salofe's A250064 threshold-chain proof in project PR #23285. Each word stores
512 entries, indexed by the nine-bit subset mask, in radix 2^32. -/
def tb (T w : ℕ) : ℕ := (T >>> (32 * w)) % 2 ^ 32

def tabT : ℕ → ℕ
  | 0 => 0x1000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000100000001000000010000000000000000000000000000000100000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000001000000000000000000000000000000000000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000100000001000000000000000000000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000100000001000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000001000000010000000100000000000000000000000000000001000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001
  | 1 => 0xF0000000A0000000A000000060000000A0000000600000006000000030000000A000000060000000600000003000000060000000300000003000000030000000A0000000600000006000000030000000600000003000000030000000300000006000000030000000300000003000000030000000300000006000000030000000A0000000600000006000000030000000600000003000000030000000300000006000000030000000300000003000000030000000300000006000000030000000600000003000000030000000300000003000000030000000600000003000000030000000300000006000000030000000C0000000600000006000000030000000A0000000A0000000600000006000000060000000600000003000000030000000600000006000000030000000300000003000000030000000300000003000000060000000600000003000000030000000300000003000000030000000300000003000000030000000300000003000000050000000600000006000000030000000600000006000000030000000300000003000000030000000300000003000000030000000300000003000000030000000500000006000000060000000300000003000000030000000300000003000000050000000600000006000000030000000C000000100000001000000008000000100000000800000008000000040000000A000000060000000A00000006000000060000000300000006000000030000000600000003000000060000000300000003000000010000000300000003000000060000000300000006000000030000000300000001000000030000000300000003000000010000000300000003000000030000000300000006000000030000000600000003000000060000000300000003000000010000000300000003000000030000000100000003000000030000000300000003000000060000000300000003000000010000000300000003000000030000000300000006000000030000000600000006000000100000000800000010000000080000000800000004000000060000000600000006000000060000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000060000000600000006000000080000000600000008000000080000000400000003000000030000000300000003000000030000000300000003000000030000000600000006000000060000000800000006000000080000000800000004000000060000000600000006000000080000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000A0000000600000006000000030000000A0000000600000006000000030000000600000003000000030000000100000006000000030000000300000003000000060000000300000003000000010000000600000003000000030000000300000003000000010000000100000001000000030000000300000006000000030000000600000003000000030000000100000006000000030000000300000003000000030000000100000001000000010000000300000003000000060000000300000003000000010000000100000001000000030000000300000006000000030000000300000003000000060000000300000010000000080000000800000004000000060000000600000003000000030000000600000006000000030000000300000003000000030000000100000001000000030000000300000003000000030000000300000003000000010000000100000003000000030000000300000003000000030000000300000003000000030000000600000008000000080000000400000003000000030000000100000001000000030000000300000003000000030000000300000003000000030000000300000006000000080000000800000004000000030000000300000003000000030000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000600000003000000060000000300000006000000030000000600000003000000030000000100000003000000010000000300000001000000030000000300000003000000010000000300000001000000030000000100000003000000030000000300000001000000030000000300000003000000030000000800000004000000030000000100000003000000010000000300000001000000030000000300000003000000010000000300000003000000030000000300000008000000040000000300000001000000030000000300000003000000030000000800000004000000030000000300000008000000040000000800000004000000040000000200000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000004000000030000000300000003000000030000000300000003000000030000000400000003000000030000000300000004000000030000000400000004000000020000000300000003000000030000000300000003000000030000000300000004000000030000000300000003000000040000000300000004000000040000000200000003000000030000000300000004000000030000000400000004000000020000000300000004000000040000000200000004000000020000000200000001
  | 2 => 0x6390000028B000002A300000105000002B8000001110000011D000000630000028D000000FF0000010B0000005B000001150000006100000065000000330000028D000000FF0000010B0000005B00000115000000610000006500000033000001120000006000000064000000330000006700000035000000510000001B0000028D000000FF0000010B0000005B00000115000000610000006500000033000001120000006000000064000000330000006700000035000000510000001B000001120000006000000064000000330000006700000035000000510000001B0000006C00000038000000570000001D000000870000002D0000002D0000000F000002B800000167000001110000008D0000011A000000930000006300000033000001150000009200000061000000330000006300000035000000350000001B000001150000009200000061000000330000006300000035000000350000001B0000006700000038000000380000001D0000004D0000002D0000002D0000000F000001150000009200000061000000330000006300000035000000350000001B0000006700000038000000380000001D0000004D0000002D0000002D0000000F0000006700000038000000380000001D0000004D0000002D0000002D0000000F0000008700000051000000510000001B000000510000001B0000001B00000009000002A300000111000001670000008D000001110000006900000093000000330000010B0000006700000092000000330000006100000021000000350000001B0000010B0000006700000092000000330000006100000021000000350000001B0000006400000022000000380000001D000000380000001D0000002D0000000F0000010B0000006700000092000000330000006100000021000000350000001B0000006400000022000000380000001D000000380000001D0000002D0000000F0000006400000022000000380000001D000000380000001D0000002D0000000F000000570000002D000000510000001B000000510000001B0000001B000000090000011D00000093000000930000004E0000006300000033000000330000001B0000006500000035000000350000001D000000350000001D0000001D0000000F0000006500000035000000350000001D000000350000001D0000001D0000000F000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000006500000035000000350000001D000000350000001D0000001D0000000F000000510000002D0000002D0000001B0000002D0000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B0000000900000009000000030000028B000001020000011100000066000001670000008D0000009300000033000000FF0000005E00000067000000210000009200000033000000350000001B000000FF0000005E00000067000000210000009200000033000000350000001B000000600000001D0000002200000011000000380000001D0000002D0000000F000000FF0000005E00000067000000210000009200000033000000350000001B000000600000001D0000002200000011000000380000001D0000002D0000000F000000600000001D0000002200000011000000380000001D0000002D0000000F000000380000001D0000002D0000000F000000510000001B0000001B00000009000001110000008D0000006900000036000000930000004E000000330000001B00000061000000330000002100000011000000350000001D0000001D0000000F00000061000000330000002100000011000000350000001D0000001D0000000F000000350000001D0000001D0000000F0000002D0000001B0000001B0000000900000061000000330000002100000011000000350000001D0000001D0000000F000000350000001D0000001D0000000F0000002D0000001B0000001B00000009000000350000001D0000001D0000000F0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B00000009000000090000000300000105000000660000008D000000360000008D000000360000004E0000001B0000005B00000021000000330000001100000033000000110000001D0000000F0000005B00000021000000330000001100000033000000110000001D0000000F00000033000000110000001D0000000F0000001D0000000F0000001B000000090000005B00000021000000330000001100000033000000110000001D0000000F00000033000000110000001D0000000F0000001D0000000F0000001B0000000900000033000000110000001D0000000F0000001D0000000F0000001B000000090000001D0000000F0000001B000000090000001B0000000900000009000000030000006300000033000000330000001B000000330000001B0000001B0000000F000000330000001B0000001B0000000F0000001B0000000F0000000F00000009000000330000001B0000001B0000000F0000001B0000000F0000000F000000090000001B0000000F0000000F000000090000000F000000090000000900000003000000330000001B0000001B0000000F0000001B0000000F0000000F000000090000001B0000000F0000000F000000090000000F0000000900000009000000030000001B0000000F0000000F000000090000000F0000000900000009000000030000000F00000009000000090000000300000009000000030000000300000001
  | 3 => 0x92D000002B3800002C8D00000C9900002DA400000D1400000D8F0000038A00002B2C00000C5900000CE60000035800000D570000038A000003B00000013E00002B2C00000C5900000CE60000035800000D570000038A000003B00000013E00000D3800000382000003AF00000140000003D200000150000001C80000007200002B2C00000C5900000CE60000035800000D570000038A000003B00000013E00000D3800000382000003AF00000140000003D200000150000001C80000007200000D3800000382000003AF00000140000003D200000150000001C8000000720000040200000162000001E80000007A000002A0000000A8000000A80000002A00002DA400000FE000000D290000048F00000D86000004BF0000039C0000013E00000D57000004B80000039400000140000003AA00000150000001500000007200000D57000004B80000039400000140000003AA000001500000015000000072000003D200000162000001620000007A000001BE000000A8000000A80000002A00000D57000004B80000039400000140000003AA000001500000015000000072000003D200000162000001620000007A000001BE000000A8000000A80000002A000003D200000162000001620000007A000001BE000000A8000000A80000002A000002A00000010000000100000000400000010000000040000000400000001000002C8D00000D2C00000FE00000048F00000D29000003C9000004BF0000013E00000CE6000003BB000004B80000014000000394000000F8000001500000007200000CE6000003BB000004B80000014000000394000000F80000015000000072000003AF00000100000001620000007A000001620000007A000000A80000002A00000CE6000003BB000004B80000014000000394000000F80000015000000072000003AF00000100000001620000007A000001620000007A000000A80000002A000003AF00000100000001620000007A000001620000007A000000A80000002A000001E8000000A800000100000000400000010000000040000000400000001000000D8F000004BF000004BF000001B00000039C000001440000014400000072000003B000000150000001500000007A000001500000007A0000007A0000002A000003B000000150000001500000007A000001500000007A0000007A0000002A000001C8000000A8000000A800000040000000A8000000400000004000000010000003B000000150000001500000007A000001500000007A0000007A0000002A000001C8000000A8000000A800000040000000A8000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400002B3800000C8C00000D2C000003AE00000FE00000048F000004BF0000013E00000C5900000370000003BB000000F2000004B800000140000001500000007200000C5900000370000003BB000000F2000004B800000140000001500000007200000382000000DE0000010000000056000001620000007A000000A80000002A00000C5900000370000003BB000000F2000004B800000140000001500000007200000382000000DE0000010000000056000001620000007A000000A80000002A00000382000000DE0000010000000056000001620000007A000000A80000002A000001620000007A000000A80000002A0000010000000040000000400000001000000D140000048F000003C900000150000004BF000001B000000144000000720000038A00000140000000F800000056000001500000007A0000007A0000002A0000038A00000140000000F800000056000001500000007A0000007A0000002A000001500000007A0000007A0000002A000000A80000004000000040000000100000038A00000140000000F800000056000001500000007A0000007A0000002A000001500000007A0000007A0000002A000000A8000000400000004000000010000001500000007A0000007A0000002A000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400000C99000003AE0000048F000001500000048F00000150000001B00000007200000358000000F2000001400000005600000140000000560000007A0000002A00000358000000F2000001400000005600000140000000560000007A0000002A00000140000000560000007A0000002A0000007A0000002A000000400000001000000358000000F2000001400000005600000140000000560000007A0000002A00000140000000560000007A0000002A0000007A0000002A000000400000001000000140000000560000007A0000002A0000007A0000002A00000040000000100000007A0000002A0000004000000010000000400000001000000010000000040000038A0000013E0000013E000000720000013E00000072000000720000002A0000013E00000072000000720000002A000000720000002A0000002A000000100000013E00000072000000720000002A000000720000002A0000002A00000010000000720000002A0000002A000000100000002A0000001000000010000000040000013E00000072000000720000002A000000720000002A0000002A00000010000000720000002A0000002A000000100000002A000000100000001000000004000000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001
  | 4 => 0x6225A0001683A00017185000051F9000178DC0000549F0000572D0000122A0001681E000050D2000053F50000117800005667000012540000130A000004CE0001681E000050D2000053F50000117800005667000012540000130A000004CE000055BE0000123200001315000004D8000013C400000514000006720000014A0001681E000050D2000053F50000117800005667000012540000130A000004CE000055BE0000123200001315000004D8000013C400000514000006720000014A000055BE0000123200001315000004D8000013C400000514000006720000014A000014A000000550000006D60000015E000008CA000001C2000001C20000005A000178DC000062760000556E000016290000575A000016F5000012AE000004CE00005667000016D80000129C000004D80000130A00000514000005140000014A00005667000016D80000129C000004D80000130A00000514000005140000014A000013C400000550000005500000015E0000065E000001C2000001C20000005A00005667000016D80000129C000004D80000130A00000514000005140000014A000013C400000550000005500000015E0000065E000001C2000001C20000005A000013C400000550000005500000015E0000065E000001C2000001C20000005A000008CA00000271000002710000007D000002710000007D0000007D00000019000171850000558000006276000016290000556E0000135F000016F5000004CE000053F500001325000016D8000004D80000129C00000410000005140000014A000053F500001325000016D8000004D80000129C00000410000005140000014A000013150000042E000005500000015E000005500000015E000001C20000005A000053F500001325000016D8000004D80000129C00000410000005140000014A000013150000042E000005500000015E000005500000015E000001C20000005A000013150000042E000005500000015E000005500000015E000001C20000005A000006D6000001C2000002710000007D000002710000007D0000007D000000190000572D000016F5000016F500000618000012AE000004EC000004EC0000014A0000130A00000514000005140000015E000005140000015E0000015E0000005A0000130A00000514000005140000015E000005140000015E0000015E0000005A00000672000001C2000001C20000007D000001C20000007D0000007D000000190000130A00000514000005140000015E000005140000015E0000015E0000005A00000672000001C2000001C20000007D000001C20000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D0000001900000019000000050001683A0000520600005580000012E40000627600001629000016F5000004CE000050D2000011DE00001325000003F2000016D8000004D8000005140000014A000050D2000011DE00001325000003F2000016D8000004D8000005140000014A00001232000003B60000042E0000010E000005500000015E000001C20000005A000050D2000011DE00001325000003F2000016D8000004D8000005140000014A00001232000003B60000042E0000010E000005500000015E000001C20000005A00001232000003B60000042E0000010E000005500000015E000001C20000005A000005500000015E000001C20000005A000002710000007D0000007D000000190000549F000016290000135F0000050A000016F500000618000004EC0000014A00001254000004D8000004100000010E000005140000015E0000015E0000005A00001254000004D8000004100000010E000005140000015E0000015E0000005A000005140000015E0000015E0000005A000001C20000007D0000007D0000001900001254000004D8000004100000010E000005140000015E0000015E0000005A000005140000015E0000015E0000005A000001C20000007D0000007D00000019000005140000015E0000015E0000005A000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D000000190000001900000005000051F9000012E4000016290000050A000016290000050A000006180000014A00001178000003F2000004D80000010E000004D80000010E0000015E0000005A00001178000003F2000004D80000010E000004D80000010E0000015E0000005A000004D80000010E0000015E0000005A0000015E0000005A0000007D0000001900001178000003F2000004D80000010E000004D80000010E0000015E0000005A000004D80000010E0000015E0000005A0000015E0000005A0000007D00000019000004D80000010E0000015E0000005A0000015E0000005A0000007D000000190000015E0000005A0000007D000000190000007D0000001900000019000000050000122A000004CE000004CE0000014A000004CE0000014A0000014A0000005A000004CE0000014A0000014A0000005A0000014A0000005A0000005A00000019000004CE0000014A0000014A0000005A0000014A0000005A0000005A000000190000014A0000005A0000005A000000190000005A000000190000001900000005000004CE0000014A0000014A0000005A0000014A0000005A0000005A000000190000014A0000005A0000005A000000190000005A0000001900000019000000050000014A0000005A0000005A000000190000005A0000001900000019000000050000005A00000019000000190000000500000019000000050000000500000001
  | 5 => 0x289E9700079E5A0007C98F00016B2D0007EAF80001755000017ECB0000424500079FC60001678B000173A60000406700017CE7000043190000457300000E0100079FC60001678B000173A60000406700017CE7000043190000457300000E0100017A62000042B1000045B000000E1F000047F900000EBF000011EE000002FD00079FC60001678B000173A60000406700017CE7000043190000457300000E0100017A62000042B1000045B000000E1F000047F900000EBF000011EE000002FD00017A62000042B1000045B000000E1F000047F900000EBF000011EE000002FD00004AB500000F55000012DE0000032500001734000003DE000003DE000000A50007EAF80001A6DA0001795B00004E0F0001806C0000507F0000444F00000E0100017CE7000050260000443300000E1F000045A500000EBF00000EBF000002FD00017CE7000050260000443300000E1F000045A500000EBF00000EBF000002FD000047F900000F5500000F5500000325000011CB000003DE000003DE000000A500017CE7000050260000443300000E1F000045A500000EBF00000EBF000002FD000047F900000F5500000F5500000325000011CB000003DE000003DE000000A5000047F900000F5500000F5500000325000011CB000003DE000003DE000000A5000017340000051000000510000000D800000510000000D8000000D8000000240007C98F0001799A0001A6DA00004E0F0001795B0000464A0000507F00000E01000173A6000045980000502600000E1F0000443300000C5D00000EBF000002FD000173A6000045980000502600000E1F0000443300000C5D00000EBF000002FD000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000173A6000045980000502600000E1F0000443300000C5D00000EBF000002FD000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000012DE000003DE00000510000000D800000510000000D8000000D80000002400017ECB0000507F0000507F000010FE0000444F00000E5B00000E5B000002FD0000457300000EBF00000EBF0000032500000EBF0000032500000325000000A50000457300000EBF00000EBF0000032500000EBF0000032500000325000000A5000011EE000003DE000003DE000000D8000003DE000000D8000000D8000000240000457300000EBF00000EBF0000032500000EBF0000032500000325000000A5000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D800000024000000240000000600079E5A00016C4A0001799A000044C10001A6DA00004E0F0000507F00000E010001678B0000419F0000459800000C030000502600000E1F00000EBF000002FD0001678B0000419F0000459800000C030000502600000E1F00000EBF000002FD000042B100000B7700000CAD0000028F00000F5500000325000003DE000000A50001678B0000419F0000459800000C030000502600000E1F00000EBF000002FD000042B100000B7700000CAD0000028F00000F5500000325000003DE000000A5000042B100000B7700000CAD0000028F00000F5500000325000003DE000000A500000F5500000325000003DE000000A500000510000000D8000000D8000000240001755000004E0F0000464A00000E970000507F000010FE00000E5B000002FD0000431900000E1F00000C5D0000028F00000EBF0000032500000325000000A50000431900000E1F00000C5D0000028F00000EBF0000032500000325000000A500000EBF0000032500000325000000A5000003DE000000D8000000D8000000240000431900000E1F00000C5D0000028F00000EBF0000032500000325000000A500000EBF0000032500000325000000A5000003DE000000D8000000D80000002400000EBF0000032500000325000000A5000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D800000024000000240000000600016B2D000044C100004E0F00000E9700004E0F00000E97000010FE000002FD0000406700000C0300000E1F0000028F00000E1F0000028F00000325000000A50000406700000C0300000E1F0000028F00000E1F0000028F00000325000000A500000E1F0000028F00000325000000A500000325000000A5000000D8000000240000406700000C0300000E1F0000028F00000E1F0000028F00000325000000A500000E1F0000028F00000325000000A500000325000000A5000000D80000002400000E1F0000028F00000325000000A500000325000000A5000000D80000002400000325000000A5000000D800000024000000D80000002400000024000000060000424500000E0100000E01000002FD00000E01000002FD000002FD000000A500000E01000002FD000002FD000000A5000002FD000000A5000000A50000002400000E01000002FD000002FD000000A5000002FD000000A5000000A500000024000002FD000000A5000000A500000024000000A500000024000000240000000600000E01000002FD000002FD000000A5000002FD000000A5000000A500000024000002FD000000A5000000A500000024000000A5000000240000002400000006000002FD000000A5000000A500000024000000A5000000240000002400000006000000A500000024000000240000000600000024000000060000000600000001
  | 6 => 0xC32D97001EED45001F86D00004DE38001FFBE20004FCBC000518A00000C105001EF8730004D50F0004F9900000BCCF000515120000C3A50000C9D3000021E1001EF8730004D50F0004F9900000BCCF000515120000C3A50000C9D3000021E100050D780000C2A20000CA97000022270000D09B00002385000029EB000005FD001EF8730004D50F0004F9900000BCCF000515120000C3A50000C9D3000021E100050D780000C2A20000CA97000022270000D09B00002385000029EB000005FD00050D780000C2A20000CA97000022270000D09B00002385000029EB000005FD0000D794000024C000002BD50000064300003441000007770000077700000111001FFBE200058B5500050AED0000DDD000051F840000E3E20000C6ED000021E1000515120000E3020000C6D1000022270000CAA50000238500002385000005FD000515120000E3020000C6D1000022270000CAA50000238500002385000005FD0000D09B000024C0000024C000000643000029B3000007770000077700000111000515120000E3020000C6D1000022270000CAA50000238500002385000005FD0000D09B000024C0000024C000000643000029B30000077700000777000001110000D09B000024C0000024C000000643000029B30000077700000777000001110000344100000961000009610000015700000961000001570000015700000031001F86D000050B9500058B550000DDD000050AED0000CB9A0000E3E2000021E10004F9900000C9DA0000E302000022270000C6D100001EB500002385000005FD0004F9900000C9DA0000E302000022270000C6D100001EB500002385000005FD0000CA9700001F64000024C000000643000024C00000064300000777000001110004F9900000C9DA0000E302000022270000C6D100001EB500002385000005FD0000CA9700001F64000024C000000643000024C00000064300000777000001110000CA9700001F64000024C000000643000024C000000643000007770000011100002BD500000777000009610000015700000961000001570000015700000031000518A00000E3E20000E3E2000027DE0000C6ED000022B3000022B3000005FD0000C9D3000023850000238500000643000023850000064300000643000001110000C9D300002385000023850000064300002385000006430000064300000111000029EB000007770000077700000157000007770000015700000157000000310000C9D300002385000023850000064300002385000006430000064300000111000029EB00000777000007770000015700000777000001570000015700000031000029EB000007770000077700000157000007770000015700000157000000310000077700000157000001570000003100000157000000310000003100000007001EED450004E39400050B950000C7AA00058B550000DDD00000E3E2000021E10004D50F0000BFD80000C9DA00001DE30000E3020000222700002385000005FD0004D50F0000BFD80000C9DA00001DE30000E3020000222700002385000005FD0000C2A200001CCB00001F6400000547000024C00000064300000777000001110004D50F0000BFD80000C9DA00001DE30000E3020000222700002385000005FD0000C2A200001CCB00001F6400000547000024C00000064300000777000001110000C2A200001CCB00001F6400000547000024C0000006430000077700000111000024C0000006430000077700000111000009610000015700000157000000310004FCBC0000DDD00000CB9A0000231C0000E3E2000027DE000022B3000005FD0000C3A50000222700001EB500000547000023850000064300000643000001110000C3A50000222700001EB5000005470000238500000643000006430000011100002385000006430000064300000111000007770000015700000157000000310000C3A50000222700001EB500000547000023850000064300000643000001110000238500000643000006430000011100000777000001570000015700000031000023850000064300000643000001110000077700000157000001570000003100000777000001570000015700000031000001570000003100000031000000070004DE380000C7AA0000DDD00000231C0000DDD00000231C000027DE000005FD0000BCCF00001DE30000222700000547000022270000054700000643000001110000BCCF00001DE300002227000005470000222700000547000006430000011100002227000005470000064300000111000006430000011100000157000000310000BCCF00001DE30000222700000547000022270000054700000643000001110000222700000547000006430000011100000643000001110000015700000031000022270000054700000643000001110000064300000111000001570000003100000643000001110000015700000031000001570000003100000031000000070000C105000021E1000021E1000005FD000021E1000005FD000005FD00000111000021E1000005FD000005FD00000111000005FD000001110000011100000031000021E1000005FD000005FD00000111000005FD000001110000011100000031000005FD00000111000001110000003100000111000000310000003100000007000021E1000005FD000005FD00000111000005FD000001110000011100000031000005FD00000111000001110000003100000111000000310000003100000007000005FD000001110000011100000031000001110000003100000031000000070000011100000031000000310000000700000031000000070000000700000001
  | 7 => 0x2E9E2B800663E8000680176000DEDE6006955E0000E3B80000E813A0001DF6400666DB8000DD9FE000E36CC0001D6F8000E7BFA0001E5F40001F3D8000047DC00666DB8000DD9FE000E36CC0001D6F8000E7BFA0001E5F40001F3D8000047DC000E68900001E3C40001F5C2000048680002034400004B08000056A000000AD400666DB8000DD9FE000E36CC0001D6F8000E7BFA0001E5F40001F3D8000047DC000E68900001E3C40001F5C2000048680002034400004B08000056A000000AD4000E68900001E3C40001F5C2000048680002034400004B08000056A000000AD40002129400004D5400005A2000000B440000690000000D2000000D20000001A4006955E0000F9AD0000E635E00021CEA000E966400022A0A0001ED80000047DC000E7BFA000228200001ED80000048680001F62400004B0800004B0800000AD4000E7BFA000228200001ED80000048680001F62400004B0800004B0800000AD40002034400004D5400004D5400000B440000564C00000D2000000D20000001A4000E7BFA000228200001ED80000048680001F62400004B0800004B0800000AD40002034400004D5400004D5400000B440000564C00000D2000000D20000001A40002034400004D5400004D5400000B440000564C00000D2000000D20000001A4000069000000100000001000000002000000100000000200000002000000004000680176000E64D8000F9AD000021CEA000E635E0001F72E00022A0A000047DC000E36CC0001F35A00022820000048680001ED800000424800004B0800000AD4000E36CC0001F35A00022820000048680001ED800000424800004B0800000AD40001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A4000E36CC0001F35A00022820000048680001ED800000424800004B0800000AD40001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A40001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A400005A2000000D20000010000000020000001000000002000000020000000040000E813A00022A0A00022A0A000052B00001ED80000049800000498000000AD40001F3D800004B0800004B0800000B4400004B0800000B4400000B44000001A40001F3D800004B0800004B0800000B4400004B0800000B4400000B44000001A4000056A000000D2000000D200000020000000D200000020000000200000000400001F3D800004B0800004B0800000B4400004B0800000B4400000B44000001A4000056A000000D2000000D200000020000000D20000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D200000020000000200000000400000020000000040000000400000000800663E80000DFF58000E64D80001EE7C000F9AD000021CEA00022A0A000047DC000DD9FE0001DD880001F35A000040A4000228200000486800004B0800000AD4000DD9FE0001DD880001F35A000040A4000228200000486800004B0800000AD40001E3C400003EAC00004398000009BC00004D5400000B4400000D20000001A4000DD9FE0001DD880001F35A000040A4000228200000486800004B0800000AD40001E3C400003EAC00004398000009BC00004D5400000B4400000D20000001A40001E3C400003EAC00004398000009BC00004D5400000B4400000D20000001A400004D5400000B4400000D20000001A400001000000002000000020000000040000E3B8000021CEA0001F72E00004A2800022A0A000052B00000498000000AD40001E5F40000486800004248000009BC00004B0800000B4400000B44000001A40001E5F40000486800004248000009BC00004B0800000B4400000B44000001A400004B0800000B4400000B44000001A400000D200000020000000200000000400001E5F40000486800004248000009BC00004B0800000B4400000B44000001A400004B0800000B4400000B44000001A400000D2000000200000002000000004000004B0800000B4400000B44000001A400000D2000000200000002000000004000000D2000000200000002000000004000000200000000400000004000000008000DEDE60001EE7C00021CEA00004A2800021CEA00004A28000052B000000AD40001D6F8000040A400004868000009BC00004868000009BC00000B44000001A40001D6F8000040A400004868000009BC00004868000009BC00000B44000001A400004868000009BC00000B44000001A400000B44000001A400000200000000400001D6F8000040A400004868000009BC00004868000009BC00000B44000001A400004868000009BC00000B44000001A400000B44000001A4000002000000004000004868000009BC00000B44000001A400000B44000001A4000002000000004000000B44000001A40000020000000040000002000000004000000040000000080001DF64000047DC000047DC00000AD4000047DC00000AD400000AD4000001A4000047DC00000AD400000AD4000001A400000AD4000001A4000001A400000040000047DC00000AD400000AD4000001A400000AD4000001A4000001A40000004000000AD4000001A4000001A400000040000001A4000000400000004000000008000047DC00000AD400000AD4000001A400000AD4000001A4000001A40000004000000AD4000001A4000001A400000040000001A400000040000000400000000800000AD4000001A4000001A400000040000001A4000000400000004000000008000001A400000040000000400000000800000040000000080000000800000001
  | 8 => 0x96173C40121EF2401266CAE0022CDEE0129C9F000237C2A002416B6000421A40122844C0022A70C0023773E000412380024112200042FC000044BA400008A3C0122844C0022A70C0023773E000412380024112200042FC000044BA400008A3C0023E55400042B7C00044FBE00008B3800046AD000008FD00000A344000012240122844C0022A70C0023773E000412380024112200042FC000044BA400008A3C0023E55400042B7C00044FBE00008B3800046AD000008FD00000A344000012240023E55400042B7C00044FBE00008B3800046AD000008FD00000A3440000122400048900000093C00000A92C000012CC0000C1A40000158400001584000002640129C9F000267EAC0023DC24000498AE00244C5C0004B24600043F2C00008A3C002411220004AE8000043F8000008B38000450E400008FD000008FD000001224002411220004AE8000043F8000008B38000450E400008FD000008FD00000122400046AD0000093C0000093C0000012CC0000A2CC000015840000158400000264002411220004AE8000043F8000008B38000450E400008FD000008FD00000122400046AD0000093C0000093C0000012CC0000A2CC00001584000015840000026400046AD0000093C0000093C0000012CC0000A2CC0000158400001584000002640000C1A4000019A1000019A1000002D9000019A1000002D9000002D90000005101266CAE0023DF1800267EAC000498AE0023DC24000451620004B24600008A3C0023773E000449D60004AE8000008B3800043F800000811800008FD0000012240023773E000449D60004AE8000008B3800043F800000811800008FD00000122400044FBE00008364000093C0000012CC000093C0000012CC00001584000002640023773E000449D60004AE8000008B3800043F800000811800008FD00000122400044FBE00008364000093C0000012CC000093C0000012CC000015840000026400044FBE00008364000093C0000012CC000093C0000012CC00001584000002640000A92C00001584000019A1000002D9000019A1000002D9000002D900000051002416B60004B2460004B24600009C6000043F2C00008D3000008D300000122400044BA400008FD000008FD0000012CC00008FD0000012CC000012CC0000026400044BA400008FD000008FD0000012CC00008FD0000012CC000012CC000002640000A3440000158400001584000002D900001584000002D9000002D90000005100044BA400008FD000008FD0000012CC00008FD0000012CC000012CC000002640000A3440000158400001584000002D900001584000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D90000005100000051000000090121EF240022FBB40023DF180004402800267EAC000498AE0004B24600008A3C0022A70C00041F04000449D600007E240004AE8000008B3800008FD0000012240022A70C00041F04000449D600007E240004AE8000008B3800008FD00000122400042B7C00007ADC000083640000108C000093C0000012CC00001584000002640022A70C00041F04000449D600007E240004AE8000008B3800008FD00000122400042B7C00007ADC000083640000108C000093C0000012CC000015840000026400042B7C00007ADC000083640000108C000093C0000012CC0000158400000264000093C0000012CC0000158400000264000019A1000002D9000002D90000005100237C2A000498AE0004516200008E2C0004B24600009C6000008D300000122400042FC000008B38000081180000108C00008FD0000012CC000012CC0000026400042FC000008B38000081180000108C00008FD0000012CC000012CC0000026400008FD0000012CC000012CC0000026400001584000002D9000002D90000005100042FC000008B38000081180000108C00008FD0000012CC000012CC0000026400008FD0000012CC000012CC0000026400001584000002D9000002D90000005100008FD0000012CC000012CC0000026400001584000002D9000002D90000005100001584000002D9000002D900000051000002D90000005100000051000000090022CDEE00044028000498AE00008E2C000498AE00008E2C00009C60000012240004123800007E2400008B380000108C00008B380000108C000012CC000002640004123800007E2400008B380000108C00008B380000108C000012CC0000026400008B380000108C000012CC00000264000012CC00000264000002D9000000510004123800007E2400008B380000108C00008B380000108C000012CC0000026400008B380000108C000012CC00000264000012CC00000264000002D90000005100008B380000108C000012CC00000264000012CC00000264000002D900000051000012CC00000264000002D900000051000002D9000000510000005100000009000421A400008A3C00008A3C0000122400008A3C00001224000012240000026400008A3C0000122400001224000002640000122400000264000002640000005100008A3C00001224000012240000026400001224000002640000026400000051000012240000026400000264000000510000026400000051000000510000000900008A3C00001224000012240000026400001224000002640000026400000051000012240000026400000264000000510000026400000051000000510000000900001224000002640000026400000051000002640000005100000051000000090000026400000051000000510000000900000051000000090000000900000001
  | 9 => 0x1A713C4702DA01FA02E44528004E4E1802EBEA06004FB1AA0050E9EC0008519702DB8AE2004E0804004FB07E000837330050E82400086CDF0008A04B0000F69F02DB8AE2004E0804004FB07E000837330050E82400086CDF0008A04B0000F69F00508E4E0008652F0008A8310000F8430008D9FF0000FFC300011E8600001CA702DB8AE2004E0804004FB07E000837330050E82400086CDF0008A04B0000F69F00508E4E0008652F0008A8310000F8430008D9FF0000FFC300011E8600001CA700508E4E0008652F0008A8310000F8430008D9FF0000FFC300011E8600001CA7000910D700010617000127E600001D9700014DFC00002166000021660000035702EBEA060055BA1A00507FE4000926F40051611A00095514000889B30000F69F0050E82400094E3600088ABB0000F8430008AAD70000FFC30000FFC300001CA70050E82400094E3600088ABB0000F8430008AAD70000FFC30000FFC300001CA70008D9FF000106170001061700001D9700011DE10000216600002166000003570050E82400094E3600088ABB0000F8430008AAD70000FFC30000FFC300001CA70008D9FF000106170001061700001D9700011DE10000216600002166000003570008D9FF000106170001061700001D9700011DE100002166000021660000035700014DFC0000271000002710000003E800002710000003E8000003E80000006402E445280050854E0055BA1A000926F400507FE40008A98D000955140000F69F004FB07E00089BD100094E360000F84300088ABB0000E8710000FFC300001CA7004FB07E00089BD100094E360000F84300088ABB0000E8710000FFC300001CA70008A8310000EC310001061700001D970001061700001D970000216600000357004FB07E00089BD100094E360000F84300088ABB0000E8710000FFC300001CA70008A8310000EC310001061700001D970001061700001D9700002166000003570008A8310000EC310001061700001D970001061700001D970000216600000357000127E60000216600002710000003E800002710000003E8000003E8000000640050E9EC000955140009551400011346000889B30000FB8B0000FB8B00001CA70008A04B0000FFC30000FFC300001D970000FFC300001D9700001D97000003570008A04B0000FFC30000FFC300001D970000FFC300001D9700001D970000035700011E860000216600002166000003E800002166000003E8000003E8000000640008A04B0000FFC30000FFC300001D970000FFC300001D9700001D970000035700011E860000216600002166000003E800002166000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A02DA01FA004EB62E0050854E00088A1F0055BA1A000926F4000955140000F69F004E080400084E4300089BD10000E38500094E360000F8430000FFC300001CA7004E080400084E4300089BD10000E38500094E360000F8430000FFC300001CA70008652F0000DE5D0000EC3100001A6D0001061700001D970000216600000357004E080400084E4300089BD10000E38500094E360000F8430000FFC300001CA70008652F0000DE5D0000EC3100001A6D0001061700001D9700002166000003570008652F0000DE5D0000EC3100001A6D0001061700001D9700002166000003570001061700001D97000021660000035700002710000003E8000003E800000064004FB1AA000926F40008A98D0000FCF300095514000113460000FB8B00001CA700086CDF0000F8430000E87100001A6D0000FFC300001D9700001D970000035700086CDF0000F8430000E87100001A6D0000FFC300001D9700001D97000003570000FFC300001D9700001D970000035700002166000003E8000003E80000006400086CDF0000F8430000E87100001A6D0000FFC300001D9700001D97000003570000FFC300001D9700001D970000035700002166000003E8000003E8000000640000FFC300001D9700001D970000035700002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A004E4E1800088A1F000926F40000FCF3000926F40000FCF30001134600001CA7000837330000E3850000F84300001A6D0000F84300001A6D00001D9700000357000837330000E3850000F84300001A6D0000F84300001A6D00001D97000003570000F84300001A6D00001D970000035700001D9700000357000003E800000064000837330000E3850000F84300001A6D0000F84300001A6D00001D97000003570000F84300001A6D00001D970000035700001D9700000357000003E8000000640000F84300001A6D00001D970000035700001D9700000357000003E80000006400001D9700000357000003E800000064000003E800000064000000640000000A000851970000F69F0000F69F00001CA70000F69F00001CA700001CA7000003570000F69F00001CA700001CA70000035700001CA70000035700000357000000640000F69F00001CA700001CA70000035700001CA700000357000003570000006400001CA70000035700000357000000640000035700000064000000640000000A0000F69F00001CA700001CA70000035700001CA700000357000003570000006400001CA70000035700000357000000640000035700000064000000640000000A00001CA70000035700000357000000640000035700000064000000640000000A0000035700000064000000640000000A000000640000000A0000000A00000001
  | 10 => 0x43098A950687E50F069D672900A2101706AD593C00A4B0FB00A6FB3F000F93B7068B73E900A1997F00A4BC11000F68EB00A70613000FC47100101D2100019E6F068B73E900A1997F00A4BC11000F68EB00A70613000FC47100101D2100019E6F00A65B46000FB76C00102B2E0001A103001080E70001AC9D0001DB0500002B2F068B73E900A1997F00A4BC11000F68EB00A70613000FC47100101D2100019E6F00A65B46000FB76C00102B2E0001A103001080E70001AC9D0001DB0500002B2F00A65B46000FB76C00102B2E0001A103001080E70001AC9D0001DB0500002B2F0010DE5C0001B6480001E93300002C79000221EB000031A1000031A10000048306AD593C00AFF2A300A647090010FB9F00A7EB66001149BD000FF6B700019E6F00A7061300113E02000FF9090001A103001030770001AC9D0001AC9D00002B2F00A7061300113E02000FF9090001A103001030770001AC9D0001AC9D00002B2F001080E70001B6480001B64800002C790001DA29000031A1000031A10000048300A7061300113E02000FF9090001A103001030770001AC9D0001AC9D00002B2F001080E70001B6480001B64800002C790001DA29000031A1000031A100000483001080E70001B6480001B64800002C790001DA29000031A1000031A100000483000221EB00003931000039310000053300003931000005330000053300000079069D672900A6505100AFF2A30010FB9F00A6470900102B4F001149BD00019E6F00A4BC11001013D900113E020001A103000FF909000189610001AC9D00002B2F00A4BC11001013D900113E020001A103000FF909000189610001AC9D00002B2F00102B2E00018F2E0001B64800002C790001B64800002C79000031A10000048300A4BC11001013D900113E020001A103000FF909000189610001AC9D00002B2F00102B2E00018F2E0001B64800002C790001B64800002C79000031A10000048300102B2E00018F2E0001B64800002C790001B64800002C79000031A1000004830001E933000031A100003931000005330000393100000533000005330000007900A6FB3F001149BD001149BD0001C99E000FF6B70001A62B0001A62B00002B2F00101D210001AC9D0001AC9D00002C790001AC9D00002C7900002C790000048300101D210001AC9D0001AC9D00002C790001AC9D00002C7900002C79000004830001DB05000031A1000031A100000533000031A100000533000005330000007900101D210001AC9D0001AC9D00002C790001AC9D00002C7900002C79000004830001DB05000031A1000031A100000533000031A10000053300000533000000790001DB05000031A1000031A100000533000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B0687E50F00A2E56E00A65051000FF58E00AFF2A30010FB9F001149BD00019E6F00A1997F000F8FFA001013D9000181A500113E020001A1030001AC9D00002B2F00A1997F000F8FFA001013D9000181A500113E020001A1030001AC9D00002B2F000FB76C000179E900018F2E0000282D0001B64800002C79000031A10000048300A1997F000F8FFA001013D9000181A500113E020001A1030001AC9D00002B2F000FB76C000179E900018F2E0000282D0001B64800002C79000031A100000483000FB76C000179E900018F2E0000282D0001B64800002C79000031A1000004830001B64800002C79000031A1000004830000393100000533000005330000007900A4B0FB0010FB9F00102B4F0001A81A001149BD0001C99E0001A62B00002B2F000FC4710001A103000189610000282D0001AC9D00002C7900002C7900000483000FC4710001A103000189610000282D0001AC9D00002C7900002C79000004830001AC9D00002C7900002C7900000483000031A1000005330000053300000079000FC4710001A103000189610000282D0001AC9D00002C7900002C79000004830001AC9D00002C7900002C7900000483000031A10000053300000533000000790001AC9D00002C7900002C7900000483000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B00A21017000FF58E0010FB9F0001A81A0010FB9F0001A81A0001C99E00002B2F000F68EB000181A50001A1030000282D0001A1030000282D00002C7900000483000F68EB000181A50001A1030000282D0001A1030000282D00002C79000004830001A1030000282D00002C790000048300002C79000004830000053300000079000F68EB000181A50001A1030000282D0001A1030000282D00002C79000004830001A1030000282D00002C790000048300002C790000048300000533000000790001A1030000282D00002C790000048300002C7900000483000005330000007900002C790000048300000533000000790000053300000079000000790000000B000F93B700019E6F00019E6F00002B2F00019E6F00002B2F00002B2F0000048300019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900002B2F0000048300000483000000790000048300000079000000790000000B00019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900002B2F0000048300000483000000790000048300000079000000790000000B00002B2F0000048300000483000000790000048300000079000000790000000B0000048300000079000000790000000B000000790000000B0000000B00000001
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem base_T : ∀ u : Fin 512, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_0 : ∀ u : Fin 512, u.val / 16 = 0 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_1 : ∀ u : Fin 512, u.val / 16 = 1 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_2 : ∀ u : Fin 512, u.val / 16 = 2 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_3 : ∀ u : Fin 512, u.val / 16 = 3 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_4 : ∀ u : Fin 512, u.val / 16 = 4 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_5 : ∀ u : Fin 512, u.val / 16 = 5 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_6 : ∀ u : Fin 512, u.val / 16 = 6 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_7 : ∀ u : Fin 512, u.val / 16 = 7 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_8 : ∀ u : Fin 512, u.val / 16 = 8 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_9 : ∀ u : Fin 512, u.val / 16 = 9 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_10 : ∀ u : Fin 512, u.val / 16 = 10 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_11 : ∀ u : Fin 512, u.val / 16 = 11 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_12 : ∀ u : Fin 512, u.val / 16 = 12 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_13 : ∀ u : Fin 512, u.val / 16 = 13 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_14 : ∀ u : Fin 512, u.val / 16 = 14 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_15 : ∀ u : Fin 512, u.val / 16 = 15 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_16 : ∀ u : Fin 512, u.val / 16 = 16 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_17 : ∀ u : Fin 512, u.val / 16 = 17 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_18 : ∀ u : Fin 512, u.val / 16 = 18 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_19 : ∀ u : Fin 512, u.val / 16 = 19 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_20 : ∀ u : Fin 512, u.val / 16 = 20 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_21 : ∀ u : Fin 512, u.val / 16 = 21 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_22 : ∀ u : Fin 512, u.val / 16 = 22 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_23 : ∀ u : Fin 512, u.val / 16 = 23 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_24 : ∀ u : Fin 512, u.val / 16 = 24 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_25 : ∀ u : Fin 512, u.val / 16 = 25 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_26 : ∀ u : Fin 512, u.val / 16 = 26 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_27 : ∀ u : Fin 512, u.val / 16 = 27 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_28 : ∀ u : Fin 512, u.val / 16 = 28 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_29 : ∀ u : Fin 512, u.val / 16 = 29 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_30 : ∀ u : Fin 512, u.val / 16 = 30 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem chunk_31 : ∀ u : Fin 512, u.val / 16 = 31 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 10) (u : Fin 512) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 16 = c := ⟨_, rfl⟩
  have hc2 : c < 32 := by omega
  interval_cases c
  · exact chunk_0 u hc n hn
  · exact chunk_1 u hc n hn
  · exact chunk_2 u hc n hn
  · exact chunk_3 u hc n hn
  · exact chunk_4 u hc n hn
  · exact chunk_5 u hc n hn
  · exact chunk_6 u hc n hn
  · exact chunk_7 u hc n hn
  · exact chunk_8 u hc n hn
  · exact chunk_9 u hc n hn
  · exact chunk_10 u hc n hn
  · exact chunk_11 u hc n hn
  · exact chunk_12 u hc n hn
  · exact chunk_13 u hc n hn
  · exact chunk_14 u hc n hn
  · exact chunk_15 u hc n hn
  · exact chunk_16 u hc n hn
  · exact chunk_17 u hc n hn
  · exact chunk_18 u hc n hn
  · exact chunk_19 u hc n hn
  · exact chunk_20 u hc n hn
  · exact chunk_21 u hc n hn
  · exact chunk_22 u hc n hn
  · exact chunk_23 u hc n hn
  · exact chunk_24 u hc n hn
  · exact chunk_25 u hc n hn
  · exact chunk_26 u hc n hn
  · exact chunk_27 u hc n hn
  · exact chunk_28 u hc n hn
  · exact chunk_29 u hc n hn
  · exact chunk_30 u hc n hn
  · exact chunk_31 u hc n hn

theorem G_eq_T (n : ℕ) (hn : n ≤ 10) : ∀ u : Fin 512, G n u = tb (tabT n) u.val := by
  induction n with
  | zero => exact base_T
  | succ n ih =>
    intro u
    rw [G_succ]
    have ih' := ih (by omega)
    simp only [ih']
    exact step_all n (by omega) u

/-- The full-mask counts after one through ten levels. -/
def samples : Fin 10 → ℤ := ![15, 1593, 37584, 402010, 2662039, 12791191, 48882360, 157381572, 443628615, 1124698773]

theorem samples_valid (n : Fin 10) : zCount (n.val + 1) = samples n := by
  rw [a_eq_G, G_eq_T (n.val + 1) (by omega)]
  have check : ∀ i : Fin 10, (tb (tabT (i.val + 1)) 511 : ℤ) = samples i := by
    decide +kernel
  exact check n

end Six964

namespace Six964
open PowerSeries
open OMA.S_oeis_a249964

def observations : Fin 10 → ℤ := ![15, 1593, 37584, 402010, 2662039, 12791191, 48882360, 157381572, 443628615, 1124698773]
def weights : Fin 10 → ℤ := ![15, 1578, 34413, 294022, 1273146, 3133206, 4579816, 3940920, 1845216, 362880]

/-- The square matrix of binomial coefficients is unit lower triangular. -/
theorem binomial_unique {D : ℕ} {c t : Fin D → ℤ}
    (h : ∀ n : Fin D, ∑ d, c d * ((n.val.choose d.val : ℕ):ℤ) =
      ∑ d, t d * ((n.val.choose d.val : ℕ):ℤ)) : c=t := by
  funext i
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h k ih =>
    have hz : ∑ d : Fin D, (c d-t d) * ((i.val.choose d.val : ℕ):ℤ) = 0 := by
      simp only [sub_mul,Finset.sum_sub_distrib,h i,sub_self]
    rw [Finset.sum_eq_single i] at hz
    · simpa using sub_eq_zero.mp (by simpa using hz : c i-t i=0)
    · intro d _ hdi
      by_cases lt : d.val < i.val
      · have e := ih d.val (by omega) d rfl
        simp [e]
      · have hn : i.val < d.val := by
          have ne : d.val≠i.val := fun h => hdi (Fin.ext h)
          omega
        simp [Nat.choose_eq_zero_of_lt hn]
    · simp

theorem weights_observations (n : Fin 10) :
    ∑ d : Fin 10, weights d * ((n.val.choose d.val : ℕ):ℤ) = observations n := by
  revert n
  decide +kernel

/-- The explicit binomial-basis polynomial valid at every positive parameter. -/
theorem explicit_counts
    (shape : ∃ c : Fin 10 → ℤ, ∀ n : ℕ, zCount (n+1) = ∑ d, c d * ((n.choose d.val : ℕ):ℤ))
    (data : ∀ n : Fin 10, zCount (n.val+1)=observations n) (n : ℕ) :
    zCount (n+1)= ∑ d : Fin 10, weights d * ((n.choose d.val : ℕ):ℤ) := by
  obtain ⟨c,hc⟩ := shape
  have ht : c=weights := binomial_unique (fun i => by rw [← hc,data,weights_observations])
  simpa [ht] using hc n

noncomputable def binSeries (d : ℕ) : PowerSeries ℚ := mk fun n => (n.choose d : ℚ)

theorem binSeries_one_sub (d : ℕ) : binSeries d * (1-X)^(d+1) = X^d := by
  induction d with
  | zero =>
    ext n
    cases n with
    | zero => simp [binSeries]
    | succ n => simp [binSeries,mul_sub,coeff_succ_mul_X,coeff_one]
  | succ d ih =>
    have step : binSeries (d+1)*(1-X)=X*binSeries d := by
      ext n
      cases n with
      | zero => simp [binSeries,mul_sub]
      | succ n =>
        simp [binSeries,mul_sub,coeff_succ_mul_X,coeff_succ_X_mul,Nat.choose_succ_succ]
    calc
      _ = (binSeries (d+1)*(1-X))*(1-X)^(d+1) := by ring
      _ = X*(binSeries d*(1-X)^(d+1)) := by rw [step]; ring
      _ = X^(d+1) := by rw [ih,pow_succ]; ring

noncomputable def series : PowerSeries ℚ := mk fun n => if n < 1 then 0 else (zCount n:ℚ)

theorem rational_binomial_series {D : ℕ} (v : Fin (D+1) → ℤ) (b : ℕ → ℤ)
    (h : ∀ n : ℕ, b (n+1)= ∑ d : Fin (D+1), v d * ((n.choose d.val : ℕ):ℤ)) :
    mk (fun n => if n<1 then 0 else (b n : ℚ)) * (1-X)^(D+1) =
      X*∑ d : Fin (D+1), C ((v d:ℤ):ℚ)*(X^d.val*(1-X)^(D-d.val)) := by
  have rep : mk (fun n => if n<1 then 0 else (b n : ℚ)) =
      X * ∑ d : Fin (D+1), C ((v d:ℤ):ℚ)*binSeries d.val := by
    ext n
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul]
      simp only [coeff_mk,if_neg (by omega : ¬n+1<1),map_sum,coeff_C_mul,binSeries]
      exact_mod_cast h n
  have reduce (d : Fin (D+1)) : binSeries d.val*(1-X)^(D+1) = X^d.val*(1-X)^(D-d.val) := by
    have add : D+1=d.val+1+(D-d.val) := by omega
    have ep := congrArg (fun e : ℕ => (1-X : PowerSeries ℚ)^e) add
    rw [pow_add _ (d.val+1) (D-d.val)] at ep
    rw [ep,← mul_assoc,binSeries_one_sub]
  rw [rep,mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,reduce]

theorem gf_of_explicit
    (h : ∀ n : ℕ, zCount (n+1)= ∑ d : Fin 10, weights d * ((n.choose d.val : ℕ):ℤ)) :
    series * (1-X)^10 = X*(15+1443*X+22329*X^2+96055*X^3+145209*X^4+81921*X^5+15359*X^6+549*X^7) := by
  have hf := rational_binomial_series (D:=9) weights zCount h
  change series*(1-X)^10 = _ at hf
  rw [hf]
  norm_num [weights,Fin.sum_univ_succ]
  ring

end Six964

namespace Six964
open PowerSeries
open OMA.S_oeis_a249964

/-- Read the tenth finite difference off the numerator. -/
theorem recurrence_of_gf
    (h : series * (1-X)^10 = X*(15+1443*X+22329*X^2+96055*X^3+145209*X^4+81921*X^5+15359*X^6+549*X^7))
    (n : ℕ) (hn : 11≤n) :
    (zCount n : ℚ) = 10*zCount (n-1) - 45*zCount (n-2) + 120*zCount (n-3) - 210*zCount (n-4) +
      252*zCount (n-5) - 210*zCount (n-6) + 120*zCount (n-7) - 45*zCount (n-8) + 10*zCount (n-9) - zCount (n-10) := by
  have eqn : series - C 10*(series*X^1) + C 45*(series*X^2) - C 120*(series*X^3) +
      C 210*(series*X^4) - C 252*(series*X^5) + C 210*(series*X^6) - C 120*(series*X^7) +
      C 45*(series*X^8) - C 10*(series*X^9) + series*X^10 =
      C 15*X^1+C 1443*X^2+C 22329*X^3+C 96055*X^4+C 145209*X^5+
      C 81921*X^6+C 15359*X^7+C 549*X^8 := by
    simp only [map_ofNat]
    linear_combination h
  have atn := congrArg (coeff n) eqn
  simp only [map_sub,map_add,coeff_C_mul,coeff_mul_X_pow',coeff_C,series,coeff_mk] at atn
  simp (disch := omega) only [if_pos, if_neg, add_zero] at atn
  linarith only [atn]

end Six964

namespace Six964
open PowerSeries OMA.S_oeis_a249964

theorem shift_native : X * PowerSeries.mk (fun k => (a (k+1) : ℚ)) = series := by
  ext k
  cases k with
  | zero => simp [series]
  | succ k => simp [coeff_succ_X_mul,series,zCount]

theorem finish (shape : ∃ c : Fin 10 → ℤ, ∀ n : ℕ, zCount (n+1) =
    ∑ j, c j * (n.choose j.val : ℤ)) (data : ∀ n : Fin 10, zCount (n.val+1)=observations n) :
    type_of% @OMA.S_oeis_a249964.main := by
  have gf := gf_of_explicit (explicit_counts shape data)
  constructor
  · rw [←shift_native,mul_assoc] at gf
    exact mul_left_cancel₀ (PowerSeries.X_ne_zero (R:=ℚ)) gf
  · intro n hn
    have h := recurrence_of_gf gf n (by omega)
    push_cast [zCount] at h
    exact_mod_cast h

end Six964

open Six964 in
theorem OMA.solution : type_of% @OMA.S_oeis_a249964.main :=
  finish count_shape samples_valid
