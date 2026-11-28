import OMAStatements.S_oeis_a250062
import Mathlib

/-!
# Nine-letter arrays with three seven-letter window constraints

The conjectures of Colin Barker for R. H. Hardin's A250062 ask for its
generating function and tenth-order recurrence (https://oeis.org/A250062).
For each seven-letter window, a split into two lower and five upper entries
is forbidden if the maximum of the pair equals the minimum of the five.

We adapt @Salofe's seven-letter threshold-set argument for A250064 (#23285)
and the general ranked-transfer proof for A250392 (#32394). Three distinct
window masks on the nine positions give the transfer in this problem.
Ten kernel-checked counts determine its binomial polynomial and numerator.
-/

/-!
The seven-entry window equivalence is from @Salofe's A250064 proof (PR #23285).
The nine-position threshold chain and mask encoding are adapted from A250392
(PR #32394), based on @rodolfoquint's A250391 proof (PR #26543).
-/

namespace Seven062

open OMA.S_oeis_a250062 Finset

/-! ### The window condition -/

/-- The condition of the statement on 7 values (without the bound on `v`). -/
def Cy (y : Fin 7 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 7)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 7 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
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

theorem cy_of (y : Fin 7 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 7)) y Finset.univ_nonempty
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

theorem window_iff (y : Fin 7 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 7 → ℕ) :
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

/-! ### Strict threshold sets -/

/-- Entry `k` of a set of positions (`false` past the end). -/
def fget (f : Fin 9 → Bool) (k : ℕ) : Bool := if h : k < 9 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 9 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 7 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 9 → Bool) : Prop := ∀ i < (3 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 9 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 9 → Fin (n + 1)) (v : ℕ) : Fin 9 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250062.get x k ≤ n := by
  unfold OMA.S_oeis_a250062.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (3 : ℕ), cntW (fun _ => true) i = 7 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 9 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (3 : ℕ), ¬ Cy (fun t : Fin 7 => OMA.S_oeis_a250062.get x (i + t)) := by
    unfold good
    rw [decide_eq_true_iff]
    refine forall_congr' fun i => imp_congr_right fun _ => not_congr ?_
    constructor
    · rintro ⟨S, hS, v, _, h1, h2, h3, h4⟩
      exact ⟨S, hS, v, h1, h2, h3, h4⟩
    · rintro ⟨S, hS, v, h1, ⟨t, ht, htv⟩, h3, h4⟩
      refine ⟨S, hS, v, ?_, h1, ⟨t, ht, htv⟩, h3, h4⟩
      rw [← htv]
      exact Nat.lt_succ_of_le (get_le x _)
  have step2 : ∀ i < (3 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 7 => OMA.S_oeis_a250062.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 9 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250062.get fget Lt
    rw [dif_pos ht, dif_pos ht, decide_eq_true_iff]
  have hfull : ∀ w, n < w → Lt x w = fun _ => true := by
    intro w hw
    funext p
    unfold Lt
    have := (x p).isLt
    simp only [decide_eq_true_iff]
    omega
  rw [step1]
  constructor
  · intro h v _ i hi
    have := (not_cy_iff _).1 (h i hi) v
    simp only [step2 i hi v, step2 i hi (v + 1)] at this
    exact this
  · intro h i hi
    rw [not_cy_iff]
    intro v
    simp only [step2 i hi v, step2 i hi (v + 1)]
    by_cases hv : v ≤ n
    · exact h v hv i hi
    · rw [hfull v (by omega), cnt_univ i hi]
      omega

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

theorem cnt_row : ∀ u : Fin 512, cntW (row u) 0 = pcb (u.val &&& 127) ∧
    cntW (row u) 1 = pcb (u.val &&& 254) ∧
    cntW (row u) 2 = pcb (u.val &&& 508) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 127) ≤ 1 ∧ 3 ≤ pcb (t &&& 127)) ∧
    ¬ (pcb (s &&& 254) ≤ 1 ∧ 3 ≤ pcb (t &&& 254)) ∧
    ¬ (pcb (s &&& 508) ≤ 1 ∧ 3 ≤ pcb (t &&& 508)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (3 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide)⟩
  · rintro ⟨h0, h1, h2⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 512) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2⟩ := cnt_row s
  obtain ⟨b0, b1, b2⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, b0, b1, b2]

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

theorem a_eq_G (n : ℕ) : a n = (G n 511 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 9 → Fin (n + 1) => good x)) =
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
  unfold a
  rw [h1, ← M_eq_G]
  unfold M
  congr 2

/-! ### The recurrence -/

theorem G_succ (n : ℕ) (u : Fin 512) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl

end Seven062

namespace Seven062
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

end Seven062

namespace Seven062
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

end Seven062

namespace Seven062
open OMA.S_oeis_a250062
open scoped Classical

theorem count_shape : ∃ c : Fin 10 → ℤ, ∀ n : ℕ,
    a (n+1) = ∑ j, c j * (n.choose j.val : ℤ) := by
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
end Seven062

namespace Seven062

open OMA.S_oeis_a250062 Finset

/- The packed certificate follows the method used for A249849, which credits
@Salofe's A250064 threshold-chain proof in project PR #23285. Each word stores
512 entries, indexed by the nine-bit subset mask, in radix 2^32. -/
def tb (T w : ℕ) : ℕ := (T >>> (32 * w)) % 2 ^ 32

def tabT : ℕ → ℕ
  | 0 => 0x1000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000010000000000000000000000000000000000000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000000000000000000000000000000000000000000000000000010000000100000000000000000000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000100000001000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000001000000010000000100000000000000000000000000000001000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001
  | 1 => 0x150000000F0000000F0000000A0000000F0000000A0000000A000000060000000F0000000A0000000A000000060000000A0000000600000006000000030000000F0000000A0000000A000000060000000A0000000600000006000000030000000A000000060000000600000003000000060000000300000003000000030000000F0000000A0000000A000000060000000A0000000600000006000000030000000A000000060000000600000003000000060000000300000003000000030000000A0000000600000006000000030000000600000003000000030000000300000006000000030000000300000003000000030000000300000006000000030000000F0000000A0000000A000000060000000A0000000600000006000000030000000A000000060000000600000003000000060000000300000003000000030000000A0000000600000006000000030000000600000003000000030000000300000006000000030000000300000003000000030000000300000006000000030000000A000000060000000600000003000000060000000300000003000000030000000600000003000000030000000300000003000000030000000600000003000000060000000300000003000000030000000300000003000000060000000300000003000000030000000600000003000000100000000800000008000000040000000F0000000F0000000A0000000A0000000A0000000A00000006000000060000000A0000000A0000000600000006000000060000000600000003000000030000000A0000000A00000006000000060000000600000006000000030000000300000006000000060000000300000003000000030000000300000003000000030000000A0000000A0000000600000006000000060000000600000003000000030000000600000006000000030000000300000003000000030000000300000003000000060000000600000003000000030000000300000003000000030000000300000003000000030000000300000003000000060000000800000008000000040000000A0000000A00000006000000060000000600000006000000030000000300000006000000060000000300000003000000030000000300000003000000030000000600000006000000030000000300000003000000030000000300000003000000030000000300000003000000030000000600000008000000080000000400000006000000060000000300000003000000030000000300000003000000030000000300000003000000030000000300000006000000080000000800000004000000030000000300000003000000030000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000F0000000A0000000F0000000A0000000A000000060000000A000000060000000A000000060000000A00000006000000060000000300000006000000030000000A000000060000000A000000060000000600000003000000060000000300000006000000030000000600000003000000030000000100000003000000030000000A000000060000000A00000006000000060000000300000006000000030000000600000003000000060000000300000003000000010000000300000003000000060000000300000006000000030000000300000001000000030000000300000003000000010000000300000003000000030000000300000008000000040000000A000000060000000A000000060000000600000003000000060000000300000006000000030000000600000003000000030000000100000003000000030000000600000003000000060000000300000003000000010000000300000003000000030000000100000003000000030000000300000003000000080000000400000006000000030000000600000003000000030000000100000003000000030000000300000001000000030000000300000003000000030000000800000004000000030000000100000003000000030000000300000003000000080000000400000003000000030000000800000004000000080000000400000004000000020000000A0000000A0000000A0000000A00000006000000060000000600000006000000060000000600000006000000060000000300000003000000030000000300000006000000060000000600000006000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000004000000060000000600000006000000060000000300000003000000030000000300000003000000030000000300000003000000030000000300000003000000040000000300000003000000030000000300000003000000030000000300000004000000030000000300000003000000040000000300000004000000040000000200000006000000060000000600000006000000030000000300000003000000030000000300000003000000030000000300000003000000030000000300000004000000030000000300000003000000030000000300000003000000030000000400000003000000030000000300000004000000030000000400000004000000020000000300000003000000030000000300000003000000030000000300000004000000030000000300000003000000040000000300000004000000040000000200000003000000030000000300000004000000030000000400000004000000020000000300000004000000040000000200000004000000020000000200000001
  | 2 => 0x8F4000003CA000003DE0000019A00000381000001720000017E0000009600000381000001720000017E00000096000001670000008D000000930000003300000381000001720000017E00000096000001670000008D0000009300000033000001670000008D00000093000000330000009200000033000000350000001B00000381000001720000017E00000096000001670000008D0000009300000033000001670000008D00000093000000330000009200000033000000350000001B000001670000008D00000093000000330000009200000033000000350000001B0000009200000033000000350000001B000000380000001D0000002D0000000F00000381000001720000017E00000096000001670000008D0000009300000033000001670000008D00000093000000330000009200000033000000350000001B000001670000008D00000093000000330000009200000033000000350000001B0000009200000033000000350000001B000000380000001D0000002D0000000F000001670000008D00000093000000330000009200000033000000350000001B0000009200000033000000350000001B000000380000001D0000002D0000000F0000009200000033000000350000001B000000380000001D0000002D0000000F000000380000001D0000002D0000000F000000510000001B0000001B00000009000003DE000001F90000019A000000D20000017E000000C6000000960000004E0000017E000000C6000000960000004E000000930000004E000000330000001B0000017E000000C6000000960000004E000000930000004E000000330000001B000000930000004E000000330000001B000000350000001D0000001D0000000F0000017E000000C6000000960000004E000000930000004E000000330000001B000000930000004E000000330000001B000000350000001D0000001D0000000F000000930000004E000000330000001B000000350000001D0000001D0000000F000000350000001D0000001D0000000F0000002D0000001B0000001B000000090000017E000000C6000000960000004E000000930000004E000000330000001B000000930000004E000000330000001B000000350000001D0000001D0000000F000000930000004E000000330000001B000000350000001D0000001D0000000F000000350000001D0000001D0000000F0000002D0000001B0000001B00000009000000930000004E000000330000001B000000350000001D0000001D0000000F000000350000001D0000001D0000000F0000002D0000001B0000001B00000009000000350000001D0000001D0000000F0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000003CA00000195000001F9000000D20000017200000096000000C60000004E0000017200000096000000C60000004E0000008D000000360000004E0000001B0000017200000096000000C60000004E0000008D000000360000004E0000001B0000008D000000360000004E0000001B00000033000000110000001D0000000F0000017200000096000000C60000004E0000008D000000360000004E0000001B0000008D000000360000004E0000001B00000033000000110000001D0000000F0000008D000000360000004E0000001B00000033000000110000001D0000000F00000033000000110000001D0000000F0000001D0000000F0000001B000000090000017200000096000000C60000004E0000008D000000360000004E0000001B0000008D000000360000004E0000001B00000033000000110000001D0000000F0000008D000000360000004E0000001B00000033000000110000001D0000000F00000033000000110000001D0000000F0000001D0000000F0000001B000000090000008D000000360000004E0000001B00000033000000110000001D0000000F00000033000000110000001D0000000F0000001D0000000F0000001B0000000900000033000000110000001D0000000F0000001D0000000F0000001B000000090000001D0000000F0000001B000000090000001B0000000900000009000000030000019A000000D2000000D20000006E000000960000004E0000004E0000002A000000960000004E0000004E0000002A000000330000001B0000001B0000000F000000960000004E0000004E0000002A000000330000001B0000001B0000000F000000330000001B0000001B0000000F0000001B0000000F0000000F00000009000000960000004E0000004E0000002A000000330000001B0000001B0000000F000000330000001B0000001B0000000F0000001B0000000F0000000F00000009000000330000001B0000001B0000000F0000001B0000000F0000000F000000090000001B0000000F0000000F000000090000000F000000090000000900000003000000960000004E0000004E0000002A000000330000001B0000001B0000000F000000330000001B0000001B0000000F0000001B0000000F0000000F00000009000000330000001B0000001B0000000F0000001B0000000F0000000F000000090000001B0000000F0000000F000000090000000F000000090000000900000003000000330000001B0000001B0000000F0000001B0000000F0000000F000000090000001B0000000F0000000F000000090000000F0000000900000009000000030000001B0000000F0000000F000000090000000F0000000900000009000000030000000F00000009000000090000000300000009000000030000000300000001
  | 3 => 0xC36C00003AED00003BF1000011BC0000370E00001050000010C0000004C80000370E00001050000010C0000004C800000FE00000048F000004BF0000013E0000370E00001050000010C0000004C800000FE00000048F000004BF0000013E00000FE00000048F000004BF0000013E000004B80000014000000150000000720000370E00001050000010C0000004C800000FE00000048F000004BF0000013E00000FE00000048F000004BF0000013E000004B800000140000001500000007200000FE00000048F000004BF0000013E000004B8000001400000015000000072000004B8000001400000015000000072000001620000007A000000A80000002A0000370E00001050000010C0000004C800000FE00000048F000004BF0000013E00000FE00000048F000004BF0000013E000004B800000140000001500000007200000FE00000048F000004BF0000013E000004B8000001400000015000000072000004B8000001400000015000000072000001620000007A000000A80000002A00000FE00000048F000004BF0000013E000004B8000001400000015000000072000004B8000001400000015000000072000001620000007A000000A80000002A000004B8000001400000015000000072000001620000007A000000A80000002A000001620000007A000000A80000002A0000010000000040000000400000001000003BF1000014B4000011D00000062C000010C0000005DC000004D4000001B0000010C0000005DC000004D4000001B0000004BF000001B00000014400000072000010C0000005DC000004D4000001B0000004BF000001B00000014400000072000004BF000001B00000014400000072000001500000007A0000007A0000002A000010C0000005DC000004D4000001B0000004BF000001B00000014400000072000004BF000001B00000014400000072000001500000007A0000007A0000002A000004BF000001B00000014400000072000001500000007A0000007A0000002A000001500000007A0000007A0000002A000000A8000000400000004000000010000010C0000005DC000004D4000001B0000004BF000001B00000014400000072000004BF000001B00000014400000072000001500000007A0000007A0000002A000004BF000001B00000014400000072000001500000007A0000007A0000002A000001500000007A0000007A0000002A000000A8000000400000004000000010000004BF000001B00000014400000072000001500000007A0000007A0000002A000001500000007A0000007A0000002A000000A8000000400000004000000010000001500000007A0000007A0000002A000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400003AED000011BC000014B40000062C00001050000004D4000005DC000001B000001050000004D4000005DC000001B00000048F00000150000001B00000007200001050000004D4000005DC000001B00000048F00000150000001B0000000720000048F00000150000001B00000007200000140000000560000007A0000002A00001050000004D4000005DC000001B00000048F00000150000001B0000000720000048F00000150000001B00000007200000140000000560000007A0000002A0000048F00000150000001B00000007200000140000000560000007A0000002A00000140000000560000007A0000002A0000007A0000002A000000400000001000001050000004D4000005DC000001B00000048F00000150000001B0000000720000048F00000150000001B00000007200000140000000560000007A0000002A0000048F00000150000001B00000007200000140000000560000007A0000002A00000140000000560000007A0000002A0000007A0000002A00000040000000100000048F00000150000001B00000007200000140000000560000007A0000002A00000140000000560000007A0000002A0000007A0000002A000000400000001000000140000000560000007A0000002A0000007A0000002A00000040000000100000007A0000002A000000400000001000000040000000100000001000000004000011BC0000062C0000062C00000230000004C8000001B0000001B00000009C000004C8000001B0000001B00000009C0000013E00000072000000720000002A000004C8000001B0000001B00000009C0000013E00000072000000720000002A0000013E00000072000000720000002A000000720000002A0000002A00000010000004C8000001B0000001B00000009C0000013E00000072000000720000002A0000013E00000072000000720000002A000000720000002A0000002A000000100000013E00000072000000720000002A000000720000002A0000002A00000010000000720000002A0000002A000000100000002A000000100000001000000004000004C8000001B0000001B00000009C0000013E00000072000000720000002A0000013E00000072000000720000002A000000720000002A0000002A000000100000013E00000072000000720000002A000000720000002A0000002A00000010000000720000002A0000002A000000100000002A0000001000000010000000040000013E00000072000000720000002A000000720000002A0000002A00000010000000720000002A0000002A000000100000002A000000100000001000000004000000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001
  | 4 => 0x7B5420001CD270001D3F300006B6C0001B48200006498000066E0000016F80001B48200006498000066E0000016F80000627600001629000016F5000004CE0001B48200006498000066E0000016F80000627600001629000016F5000004CE0000627600001629000016F5000004CE000016D8000004D8000005140000014A0001B48200006498000066E0000016F80000627600001629000016F5000004CE0000627600001629000016F5000004CE000016D8000004D8000005140000014A0000627600001629000016F5000004CE000016D8000004D8000005140000014A000016D8000004D8000005140000014A000005500000015E000001C20000005A0001B48200006498000066E0000016F80000627600001629000016F5000004CE0000627600001629000016F5000004CE000016D8000004D8000005140000014A0000627600001629000016F5000004CE000016D8000004D8000005140000014A000016D8000004D8000005140000014A000005500000015E000001C20000005A0000627600001629000016F5000004CE000016D8000004D8000005140000014A000016D8000004D8000005140000014A000005500000015E000001C20000005A000016D8000004D8000005140000014A000005500000015E000001C20000005A000005500000015E000001C20000005A000002710000007D0000007D000000190001D3F3000079CC00006C4800001C34000066E000001B040000174C00000618000066E000001B040000174C00000618000016F500000618000004EC0000014A000066E000001B040000174C00000618000016F500000618000004EC0000014A000016F500000618000004EC0000014A000005140000015E0000015E0000005A000066E000001B040000174C00000618000016F500000618000004EC0000014A000016F500000618000004EC0000014A000005140000015E0000015E0000005A000016F500000618000004EC0000014A000005140000015E0000015E0000005A000005140000015E0000015E0000005A000001C20000007D0000007D00000019000066E000001B040000174C00000618000016F500000618000004EC0000014A000016F500000618000004EC0000014A000005140000015E0000015E0000005A000016F500000618000004EC0000014A000005140000015E0000015E0000005A000005140000015E0000015E0000005A000001C20000007D0000007D00000019000016F500000618000004EC0000014A000005140000015E0000015E0000005A000005140000015E0000015E0000005A000001C20000007D0000007D00000019000005140000015E0000015E0000005A000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D0000001900000019000000050001CD2700006C16000079CC00001C34000064980000174C00001B0400000618000064980000174C00001B0400000618000016290000050A000006180000014A000064980000174C00001B0400000618000016290000050A000006180000014A000016290000050A000006180000014A000004D80000010E0000015E0000005A000064980000174C00001B0400000618000016290000050A000006180000014A000016290000050A000006180000014A000004D80000010E0000015E0000005A000016290000050A000006180000014A000004D80000010E0000015E0000005A000004D80000010E0000015E0000005A0000015E0000005A0000007D00000019000064980000174C00001B0400000618000016290000050A000006180000014A000016290000050A000006180000014A000004D80000010E0000015E0000005A000016290000050A000006180000014A000004D80000010E0000015E0000005A000004D80000010E0000015E0000005A0000015E0000005A0000007D00000019000016290000050A000006180000014A000004D80000010E0000015E0000005A000004D80000010E0000015E0000005A0000015E0000005A0000007D00000019000004D80000010E0000015E0000005A0000015E0000005A0000007D000000190000015E0000005A0000007D000000190000007D00000019000000190000000500006B6C00001C3400001C3400000780000016F80000061800000618000001A4000016F80000061800000618000001A4000004CE0000014A0000014A0000005A000016F80000061800000618000001A4000004CE0000014A0000014A0000005A000004CE0000014A0000014A0000005A0000014A0000005A0000005A00000019000016F80000061800000618000001A4000004CE0000014A0000014A0000005A000004CE0000014A0000014A0000005A0000014A0000005A0000005A00000019000004CE0000014A0000014A0000005A0000014A0000005A0000005A000000190000014A0000005A0000005A000000190000005A000000190000001900000005000016F80000061800000618000001A4000004CE0000014A0000014A0000005A000004CE0000014A0000014A0000005A0000014A0000005A0000005A00000019000004CE0000014A0000014A0000005A0000014A0000005A0000005A000000190000014A0000005A0000005A000000190000005A000000190000001900000005000004CE0000014A0000014A0000005A0000014A0000005A0000005A000000190000014A0000005A0000005A000000190000005A0000001900000019000000050000014A0000005A0000005A000000190000005A0000001900000019000000050000005A00000019000000190000000500000019000000050000000500000001
  | 5 => 0x310875000956D2000975AE0001C58E0008ED6D0001AE220001B692000050460008ED6D0001AE220001B692000050460001A6DA00004E0F0000507F00000E010008ED6D0001AE220001B692000050460001A6DA00004E0F0000507F00000E010001A6DA00004E0F0000507F00000E010000502600000E1F00000EBF000002FD0008ED6D0001AE220001B692000050460001A6DA00004E0F0000507F00000E010001A6DA00004E0F0000507F00000E010000502600000E1F00000EBF000002FD0001A6DA00004E0F0000507F00000E010000502600000E1F00000EBF000002FD0000502600000E1F00000EBF000002FD00000F5500000325000003DE000000A50008ED6D0001AE220001B692000050460001A6DA00004E0F0000507F00000E010001A6DA00004E0F0000507F00000E010000502600000E1F00000EBF000002FD0001A6DA00004E0F0000507F00000E010000502600000E1F00000EBF000002FD0000502600000E1F00000EBF000002FD00000F5500000325000003DE000000A50001A6DA00004E0F0000507F00000E010000502600000E1F00000EBF000002FD0000502600000E1F00000EBF000002FD00000F5500000325000003DE000000A50000502600000E1F00000EBF000002FD00000F5500000325000003DE000000A500000F5500000325000003DE000000A500000510000000D8000000D800000024000975AE0001F8470001CA0200005F460001B69200005BE60000518A000010FE0001B69200005BE60000518A000010FE0000507F000010FE00000E5B000002FD0001B69200005BE60000518A000010FE0000507F000010FE00000E5B000002FD0000507F000010FE00000E5B000002FD00000EBF0000032500000325000000A50001B69200005BE60000518A000010FE0000507F000010FE00000E5B000002FD0000507F000010FE00000E5B000002FD00000EBF0000032500000325000000A50000507F000010FE00000E5B000002FD00000EBF0000032500000325000000A500000EBF0000032500000325000000A5000003DE000000D8000000D8000000240001B69200005BE60000518A000010FE0000507F000010FE00000E5B000002FD0000507F000010FE00000E5B000002FD00000EBF0000032500000325000000A50000507F000010FE00000E5B000002FD00000EBF0000032500000325000000A500000EBF0000032500000325000000A5000003DE000000D8000000D8000000240000507F000010FE00000E5B000002FD00000EBF0000032500000325000000A500000EBF0000032500000325000000A5000003DE000000D8000000D80000002400000EBF0000032500000325000000A5000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D8000000240000002400000006000956D20001C99E0001F84700005F460001AE220000518A00005BE6000010FE0001AE220000518A00005BE6000010FE00004E0F00000E97000010FE000002FD0001AE220000518A00005BE6000010FE00004E0F00000E97000010FE000002FD00004E0F00000E97000010FE000002FD00000E1F0000028F00000325000000A50001AE220000518A00005BE6000010FE00004E0F00000E97000010FE000002FD00004E0F00000E97000010FE000002FD00000E1F0000028F00000325000000A500004E0F00000E97000010FE000002FD00000E1F0000028F00000325000000A500000E1F0000028F00000325000000A500000325000000A5000000D8000000240001AE220000518A00005BE6000010FE00004E0F00000E97000010FE000002FD00004E0F00000E97000010FE000002FD00000E1F0000028F00000325000000A500004E0F00000E97000010FE000002FD00000E1F0000028F00000325000000A500000E1F0000028F00000325000000A500000325000000A5000000D80000002400004E0F00000E97000010FE000002FD00000E1F0000028F00000325000000A500000E1F0000028F00000325000000A500000325000000A5000000D80000002400000E1F0000028F00000325000000A500000325000000A5000000D80000002400000325000000A5000000D800000024000000D80000002400000024000000060001C58E00005F4600005F460000143200005046000010FE000010FE000003A200005046000010FE000010FE000003A200000E01000002FD000002FD000000A500005046000010FE000010FE000003A200000E01000002FD000002FD000000A500000E01000002FD000002FD000000A5000002FD000000A5000000A50000002400005046000010FE000010FE000003A200000E01000002FD000002FD000000A500000E01000002FD000002FD000000A5000002FD000000A5000000A50000002400000E01000002FD000002FD000000A5000002FD000000A5000000A500000024000002FD000000A5000000A500000024000000A500000024000000240000000600005046000010FE000010FE000003A200000E01000002FD000002FD000000A500000E01000002FD000002FD000000A5000002FD000000A5000000A50000002400000E01000002FD000002FD000000A5000002FD000000A5000000A500000024000002FD000000A5000000A500000024000000A500000024000000240000000600000E01000002FD000002FD000000A5000002FD000000A5000000A500000024000002FD000000A5000000A500000024000000A5000000240000002400000006000002FD000000A5000000A500000024000000A5000000240000002400000006000000A500000024000000240000000600000024000000060000000600000001
  | 6 => 0xE4EB7A0024C11F00252D170005E02E0023631300059F520005B8260000E2E60023631300059F520005B8260000E2E600058B550000DDD00000E3E2000021E10023631300059F520005B8260000E2E600058B550000DDD00000E3E2000021E100058B550000DDD00000E3E2000021E10000E3020000222700002385000005FD0023631300059F520005B8260000E2E600058B550000DDD00000E3E2000021E100058B550000DDD00000E3E2000021E10000E3020000222700002385000005FD00058B550000DDD00000E3E2000021E10000E3020000222700002385000005FD0000E3020000222700002385000005FD000024C00000064300000777000001110023631300059F520005B8260000E2E600058B550000DDD00000E3E2000021E100058B550000DDD00000E3E2000021E10000E3020000222700002385000005FD00058B550000DDD00000E3E2000021E10000E3020000222700002385000005FD0000E3020000222700002385000005FD000024C000000643000007770000011100058B550000DDD00000E3E2000021E10000E3020000222700002385000005FD0000E3020000222700002385000005FD000024C00000064300000777000001110000E3020000222700002385000005FD000024C0000006430000077700000111000024C00000064300000777000001110000096100000157000001570000003100252D17000670B10005F00A000106C60005B8260000FECA0000E682000027DE0005B8260000FECA0000E682000027DE0000E3E2000027DE000022B3000005FD0005B8260000FECA0000E682000027DE0000E3E2000027DE000022B3000005FD0000E3E2000027DE000022B3000005FD000023850000064300000643000001110005B8260000FECA0000E682000027DE0000E3E2000027DE000022B3000005FD0000E3E2000027DE000022B3000005FD000023850000064300000643000001110000E3E2000027DE000022B3000005FD0000238500000643000006430000011100002385000006430000064300000111000007770000015700000157000000310005B8260000FECA0000E682000027DE0000E3E2000027DE000022B3000005FD0000E3E2000027DE000022B3000005FD000023850000064300000643000001110000E3E2000027DE000022B3000005FD0000238500000643000006430000011100002385000006430000064300000111000007770000015700000157000000310000E3E2000027DE000022B3000005FD000023850000064300000643000001110000238500000643000006430000011100000777000001570000015700000031000023850000064300000643000001110000077700000157000001570000003100000777000001570000015700000031000001570000003100000031000000070024C11F0005EF5B000670B1000106C600059F520000E6820000FECA000027DE00059F520000E6820000FECA000027DE0000DDD00000231C000027DE000005FD00059F520000E6820000FECA000027DE0000DDD00000231C000027DE000005FD0000DDD00000231C000027DE000005FD0000222700000547000006430000011100059F520000E6820000FECA000027DE0000DDD00000231C000027DE000005FD0000DDD00000231C000027DE000005FD000022270000054700000643000001110000DDD00000231C000027DE000005FD00002227000005470000064300000111000022270000054700000643000001110000064300000111000001570000003100059F520000E6820000FECA000027DE0000DDD00000231C000027DE000005FD0000DDD00000231C000027DE000005FD000022270000054700000643000001110000DDD00000231C000027DE000005FD0000222700000547000006430000011100002227000005470000064300000111000006430000011100000157000000310000DDD00000231C000027DE000005FD000022270000054700000643000001110000222700000547000006430000011100000643000001110000015700000031000022270000054700000643000001110000064300000111000001570000003100000643000001110000015700000031000001570000003100000031000000070005E02E000106C6000106C600002E360000E2E6000027DE000027DE0000070E0000E2E6000027DE000027DE0000070E000021E1000005FD000005FD000001110000E2E6000027DE000027DE0000070E000021E1000005FD000005FD00000111000021E1000005FD000005FD00000111000005FD0000011100000111000000310000E2E6000027DE000027DE0000070E000021E1000005FD000005FD00000111000021E1000005FD000005FD00000111000005FD000001110000011100000031000021E1000005FD000005FD00000111000005FD000001110000011100000031000005FD000001110000011100000031000001110000003100000031000000070000E2E6000027DE000027DE0000070E000021E1000005FD000005FD00000111000021E1000005FD000005FD00000111000005FD000001110000011100000031000021E1000005FD000005FD00000111000005FD000001110000011100000031000005FD00000111000001110000003100000111000000310000003100000007000021E1000005FD000005FD00000111000005FD000001110000011100000031000005FD00000111000001110000003100000111000000310000003100000007000005FD000001110000011100000031000001110000003100000031000000070000011100000031000000310000000700000031000000070000000700000001
  | 7 => 0x3584B000076BDC60077F75E001064B80072EF5C000FCA1000100830000227400072EF5C000FCA100010083000022740000F9AD000021CEA00022A0A000047DC0072EF5C000FCA100010083000022740000F9AD000021CEA00022A0A000047DC000F9AD000021CEA00022A0A000047DC000228200000486800004B0800000AD40072EF5C000FCA100010083000022740000F9AD000021CEA00022A0A000047DC000F9AD000021CEA00022A0A000047DC000228200000486800004B0800000AD4000F9AD000021CEA00022A0A000047DC000228200000486800004B0800000AD4000228200000486800004B0800000AD400004D5400000B4400000D20000001A40072EF5C000FCA100010083000022740000F9AD000021CEA00022A0A000047DC000F9AD000021CEA00022A0A000047DC000228200000486800004B0800000AD4000F9AD000021CEA00022A0A000047DC000228200000486800004B0800000AD4000228200000486800004B0800000AD400004D5400000B4400000D20000001A4000F9AD000021CEA00022A0A000047DC000228200000486800004B0800000AD4000228200000486800004B0800000AD400004D5400000B4400000D20000001A4000228200000486800004B0800000AD400004D5400000B4400000D20000001A400004D5400000B4400000D20000001A4000010000000020000000200000000400077F75E0011C60000109190000272B8001008300002621800022FC8000052B0001008300002621800022FC8000052B000022A0A000052B00000498000000AD4001008300002621800022FC8000052B000022A0A000052B00000498000000AD400022A0A000052B00000498000000AD400004B0800000B4400000B44000001A4001008300002621800022FC8000052B000022A0A000052B00000498000000AD400022A0A000052B00000498000000AD400004B0800000B4400000B44000001A400022A0A000052B00000498000000AD400004B0800000B4400000B44000001A400004B0800000B4400000B44000001A400000D20000002000000020000000040001008300002621800022FC8000052B000022A0A000052B00000498000000AD400022A0A000052B00000498000000AD400004B0800000B4400000B44000001A400022A0A000052B00000498000000AD400004B0800000B4400000B44000001A400004B0800000B4400000B44000001A400000D2000000200000002000000004000022A0A000052B00000498000000AD400004B0800000B4400000B44000001A400004B0800000B4400000B44000001A400000D2000000200000002000000004000004B0800000B4400000B44000001A400000D2000000200000002000000004000000D20000002000000020000000040000002000000004000000040000000080076BDC6001090780011C600000272B8000FCA1000022FC800026218000052B0000FCA1000022FC800026218000052B000021CEA00004A28000052B000000AD4000FCA1000022FC800026218000052B000021CEA00004A28000052B000000AD400021CEA00004A28000052B000000AD400004868000009BC00000B44000001A4000FCA1000022FC800026218000052B000021CEA00004A28000052B000000AD400021CEA00004A28000052B000000AD400004868000009BC00000B44000001A400021CEA00004A28000052B000000AD400004868000009BC00000B44000001A400004868000009BC00000B44000001A400000B44000001A40000020000000040000FCA1000022FC800026218000052B000021CEA00004A28000052B000000AD400021CEA00004A28000052B000000AD400004868000009BC00000B44000001A400021CEA00004A28000052B000000AD400004868000009BC00000B44000001A400004868000009BC00000B44000001A400000B44000001A4000002000000004000021CEA00004A28000052B000000AD400004868000009BC00000B44000001A400004868000009BC00000B44000001A400000B44000001A4000002000000004000004868000009BC00000B44000001A400000B44000001A4000002000000004000000B44000001A4000002000000004000000200000000400000004000000008001064B8000272B8000272B800005E1000022740000052B0000052B000000C7800022740000052B0000052B000000C78000047DC00000AD400000AD4000001A400022740000052B0000052B000000C78000047DC00000AD400000AD4000001A4000047DC00000AD400000AD4000001A400000AD4000001A4000001A40000004000022740000052B0000052B000000C78000047DC00000AD400000AD4000001A4000047DC00000AD400000AD4000001A400000AD4000001A4000001A400000040000047DC00000AD400000AD4000001A400000AD4000001A4000001A40000004000000AD4000001A4000001A400000040000001A400000040000000400000000800022740000052B0000052B000000C78000047DC00000AD400000AD4000001A4000047DC00000AD400000AD4000001A400000AD4000001A4000001A400000040000047DC00000AD400000AD4000001A400000AD4000001A4000001A40000004000000AD4000001A4000001A400000040000001A4000000400000004000000008000047DC00000AD400000AD4000001A400000AD4000001A4000001A40000004000000AD4000001A4000001A400000040000001A400000040000000400000000800000AD4000001A4000001A400000040000001A4000000400000004000000008000001A400000040000000400000000800000040000000080000000800000001
  | 8 => 0xA97E14C014ACBCA014DE47200282CD8014180040026E2C000276C900004ABE0014180040026E2C000276C900004ABE000267EAC000498AE0004B24600008A3C014180040026E2C000276C900004ABE000267EAC000498AE0004B24600008A3C00267EAC000498AE0004B24600008A3C0004AE8000008B3800008FD000001224014180040026E2C000276C900004ABE000267EAC000498AE0004B24600008A3C00267EAC000498AE0004B24600008A3C0004AE8000008B3800008FD00000122400267EAC000498AE0004B24600008A3C0004AE8000008B3800008FD0000012240004AE8000008B3800008FD000001224000093C0000012CC0000158400000264014180040026E2C000276C900004ABE000267EAC000498AE0004B24600008A3C00267EAC000498AE0004B24600008A3C0004AE8000008B3800008FD00000122400267EAC000498AE0004B24600008A3C0004AE8000008B3800008FD0000012240004AE8000008B3800008FD000001224000093C0000012CC000015840000026400267EAC000498AE0004B24600008A3C0004AE8000008B3800008FD0000012240004AE8000008B3800008FD000001224000093C0000012CC00001584000002640004AE8000008B3800008FD000001224000093C0000012CC0000158400000264000093C0000012CC0000158400000264000019A1000002D9000002D900000051014DE472002B2F000028992000053C2800276C9000051CA80004BD9800009C6000276C9000051CA80004BD9800009C600004B24600009C6000008D300000122400276C9000051CA80004BD9800009C600004B24600009C6000008D30000012240004B24600009C6000008D300000122400008FD0000012CC000012CC0000026400276C9000051CA80004BD9800009C600004B24600009C6000008D30000012240004B24600009C6000008D300000122400008FD0000012CC000012CC000002640004B24600009C6000008D300000122400008FD0000012CC000012CC0000026400008FD0000012CC000012CC0000026400001584000002D9000002D90000005100276C9000051CA80004BD9800009C600004B24600009C6000008D30000012240004B24600009C6000008D300000122400008FD0000012CC000012CC000002640004B24600009C6000008D300000122400008FD0000012CC000012CC0000026400008FD0000012CC000012CC0000026400001584000002D9000002D9000000510004B24600009C6000008D300000122400008FD0000012CC000012CC0000026400008FD0000012CC000012CC0000026400001584000002D9000002D90000005100008FD0000012CC000012CC0000026400001584000002D9000002D90000005100001584000002D9000002D900000051000002D9000000510000005100000009014ACBCA0028977C002B2F0000053C280026E2C00004BD9800051CA800009C600026E2C00004BD9800051CA800009C60000498AE00008E2C00009C60000012240026E2C00004BD9800051CA800009C60000498AE00008E2C00009C6000001224000498AE00008E2C00009C600000122400008B380000108C000012CC000002640026E2C00004BD9800051CA800009C60000498AE00008E2C00009C6000001224000498AE00008E2C00009C600000122400008B380000108C000012CC00000264000498AE00008E2C00009C600000122400008B380000108C000012CC0000026400008B380000108C000012CC00000264000012CC00000264000002D9000000510026E2C00004BD9800051CA800009C60000498AE00008E2C00009C6000001224000498AE00008E2C00009C600000122400008B380000108C000012CC00000264000498AE00008E2C00009C600000122400008B380000108C000012CC0000026400008B380000108C000012CC00000264000012CC00000264000002D900000051000498AE00008E2C00009C600000122400008B380000108C000012CC0000026400008B380000108C000012CC00000264000012CC00000264000002D90000005100008B380000108C000012CC00000264000012CC00000264000002D900000051000012CC00000264000002D900000051000002D900000051000000510000000900282CD800053C2800053C280000AF500004ABE000009C6000009C60000014880004ABE000009C6000009C600000148800008A3C0000122400001224000002640004ABE000009C6000009C600000148800008A3C00001224000012240000026400008A3C000012240000122400000264000012240000026400000264000000510004ABE000009C6000009C600000148800008A3C00001224000012240000026400008A3C0000122400001224000002640000122400000264000002640000005100008A3C0000122400001224000002640000122400000264000002640000005100001224000002640000026400000051000002640000005100000051000000090004ABE000009C6000009C600000148800008A3C00001224000012240000026400008A3C0000122400001224000002640000122400000264000002640000005100008A3C00001224000012240000026400001224000002640000026400000051000012240000026400000264000000510000026400000051000000510000000900008A3C00001224000012240000026400001224000002640000026400000051000012240000026400000264000000510000026400000051000000510000000900001224000002640000026400000051000002640000005100000051000000090000026400000051000000510000000900000051000000090000000900000001
  | 9 => 0x1D795C3D03354861033C4FE9005903B20320C2CB00567CEA0057938A000948360320C2CB00567CEA0057938A000948360055BA1A000926F4000955140000F69F0320C2CB00567CEA0057938A000948360055BA1A000926F4000955140000F69F0055BA1A000926F4000955140000F69F00094E360000F8430000FFC300001CA70320C2CB00567CEA0057938A000948360055BA1A000926F4000955140000F69F0055BA1A000926F4000955140000F69F00094E360000F8430000FFC300001CA70055BA1A000926F4000955140000F69F00094E360000F8430000FFC300001CA700094E360000F8430000FFC300001CA70001061700001D9700002166000003570320C2CB00567CEA0057938A000948360055BA1A000926F4000955140000F69F0055BA1A000926F4000955140000F69F00094E360000F8430000FFC300001CA70055BA1A000926F4000955140000F69F00094E360000F8430000FFC300001CA700094E360000F8430000FFC300001CA70001061700001D9700002166000003570055BA1A000926F4000955140000F69F00094E360000F8430000FFC300001CA700094E360000F8430000FFC300001CA70001061700001D97000021660000035700094E360000F8430000FFC300001CA70001061700001D9700002166000003570001061700001D97000021660000035700002710000003E8000003E800000064033C4FE9005F03F70059ECAA000A48620057938A000A10E2000969AE000113460057938A000A10E2000969AE0001134600095514000113460000FB8B00001CA70057938A000A10E2000969AE0001134600095514000113460000FB8B00001CA700095514000113460000FB8B00001CA70000FFC300001D9700001D97000003570057938A000A10E2000969AE0001134600095514000113460000FB8B00001CA700095514000113460000FB8B00001CA70000FFC300001D9700001D970000035700095514000113460000FB8B00001CA70000FFC300001D9700001D97000003570000FFC300001D9700001D970000035700002166000003E8000003E8000000640057938A000A10E2000969AE0001134600095514000113460000FB8B00001CA700095514000113460000FB8B00001CA70000FFC300001D9700001D970000035700095514000113460000FB8B00001CA70000FFC300001D9700001D97000003570000FFC300001D9700001D970000035700002166000003E8000003E80000006400095514000113460000FB8B00001CA70000FFC300001D9700001D97000003570000FFC300001D9700001D970000035700002166000003E8000003E8000000640000FFC300001D9700001D970000035700002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A033548610059EA52005F03F7000A486200567CEA000969AE000A10E20001134600567CEA000969AE000A10E200011346000926F40000FCF30001134600001CA700567CEA000969AE000A10E200011346000926F40000FCF30001134600001CA7000926F40000FCF30001134600001CA70000F84300001A6D00001D970000035700567CEA000969AE000A10E200011346000926F40000FCF30001134600001CA7000926F40000FCF30001134600001CA70000F84300001A6D00001D9700000357000926F40000FCF30001134600001CA70000F84300001A6D00001D97000003570000F84300001A6D00001D970000035700001D9700000357000003E80000006400567CEA000969AE000A10E200011346000926F40000FCF30001134600001CA7000926F40000FCF30001134600001CA70000F84300001A6D00001D9700000357000926F40000FCF30001134600001CA70000F84300001A6D00001D97000003570000F84300001A6D00001D970000035700001D9700000357000003E800000064000926F40000FCF30001134600001CA70000F84300001A6D00001D97000003570000F84300001A6D00001D970000035700001D9700000357000003E8000000640000F84300001A6D00001D970000035700001D9700000357000003E80000006400001D9700000357000003E800000064000003E800000064000000640000000A005903B2000A4862000A48620001310A00094836000113460001134600001FFE00094836000113460001134600001FFE0000F69F00001CA700001CA70000035700094836000113460001134600001FFE0000F69F00001CA700001CA7000003570000F69F00001CA700001CA70000035700001CA700000357000003570000006400094836000113460001134600001FFE0000F69F00001CA700001CA7000003570000F69F00001CA700001CA70000035700001CA70000035700000357000000640000F69F00001CA700001CA70000035700001CA700000357000003570000006400001CA70000035700000357000000640000035700000064000000640000000A00094836000113460001134600001FFE0000F69F00001CA700001CA7000003570000F69F00001CA700001CA70000035700001CA70000035700000357000000640000F69F00001CA700001CA70000035700001CA700000357000003570000006400001CA70000035700000357000000640000035700000064000000640000000A0000F69F00001CA700001CA70000035700001CA700000357000003570000006400001CA70000035700000357000000640000035700000064000000640000000A00001CA70000035700000357000000640000035700000064000000640000000A0000035700000064000000640000000A000000640000000A0000000A00000001
  | 10 => 0x49F0A9880743AC90075253BC00B5F5220719DEE500B1554200B3609E001132260719DEE500B1554200B3609E0011322600AFF2A30010FB9F001149BD00019E6F0719DEE500B1554200B3609E0011322600AFF2A30010FB9F001149BD00019E6F00AFF2A30010FB9F001149BD00019E6F00113E020001A1030001AC9D00002B2F0719DEE500B1554200B3609E0011322600AFF2A30010FB9F001149BD00019E6F00AFF2A30010FB9F001149BD00019E6F00113E020001A1030001AC9D00002B2F00AFF2A30010FB9F001149BD00019E6F00113E020001A1030001AC9D00002B2F00113E020001A1030001AC9D00002B2F0001B64800002C79000031A1000004830719DEE500B1554200B3609E0011322600AFF2A30010FB9F001149BD00019E6F00AFF2A30010FB9F001149BD00019E6F00113E020001A1030001AC9D00002B2F00AFF2A30010FB9F001149BD00019E6F00113E020001A1030001AC9D00002B2F00113E020001A1030001AC9D00002B2F0001B64800002C79000031A10000048300AFF2A30010FB9F001149BD00019E6F00113E020001A1030001AC9D00002B2F00113E020001A1030001AC9D00002B2F0001B64800002C79000031A10000048300113E020001A1030001AC9D00002B2F0001B64800002C79000031A1000004830001B64800002C79000031A10000048300003931000005330000053300000079075253BC00C11C3100B7C00A0012DEFA00B3609E001282AE00116CEE0001C99E00B3609E001282AE00116CEE0001C99E001149BD0001C99E0001A62B00002B2F00B3609E001282AE00116CEE0001C99E001149BD0001C99E0001A62B00002B2F001149BD0001C99E0001A62B00002B2F0001AC9D00002C7900002C790000048300B3609E001282AE00116CEE0001C99E001149BD0001C99E0001A62B00002B2F001149BD0001C99E0001A62B00002B2F0001AC9D00002C7900002C7900000483001149BD0001C99E0001A62B00002B2F0001AC9D00002C7900002C79000004830001AC9D00002C7900002C7900000483000031A100000533000005330000007900B3609E001282AE00116CEE0001C99E001149BD0001C99E0001A62B00002B2F001149BD0001C99E0001A62B00002B2F0001AC9D00002C7900002C7900000483001149BD0001C99E0001A62B00002B2F0001AC9D00002C7900002C79000004830001AC9D00002C7900002C7900000483000031A1000005330000053300000079001149BD0001C99E0001A62B00002B2F0001AC9D00002C7900002C79000004830001AC9D00002C7900002C7900000483000031A10000053300000533000000790001AC9D00002C7900002C7900000483000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B0743AC9000B7BCD100C11C310012DEFA00B1554200116CEE001282AE0001C99E00B1554200116CEE001282AE0001C99E0010FB9F0001A81A0001C99E00002B2F00B1554200116CEE001282AE0001C99E0010FB9F0001A81A0001C99E00002B2F0010FB9F0001A81A0001C99E00002B2F0001A1030000282D00002C790000048300B1554200116CEE001282AE0001C99E0010FB9F0001A81A0001C99E00002B2F0010FB9F0001A81A0001C99E00002B2F0001A1030000282D00002C79000004830010FB9F0001A81A0001C99E00002B2F0001A1030000282D00002C79000004830001A1030000282D00002C790000048300002C7900000483000005330000007900B1554200116CEE001282AE0001C99E0010FB9F0001A81A0001C99E00002B2F0010FB9F0001A81A0001C99E00002B2F0001A1030000282D00002C79000004830010FB9F0001A81A0001C99E00002B2F0001A1030000282D00002C79000004830001A1030000282D00002C790000048300002C790000048300000533000000790010FB9F0001A81A0001C99E00002B2F0001A1030000282D00002C79000004830001A1030000282D00002C790000048300002C790000048300000533000000790001A1030000282D00002C790000048300002C7900000483000005330000007900002C790000048300000533000000790000053300000079000000790000000B00B5F5220012DEFA0012DEFA0001F64E001132260001C99E0001C99E00002FB2001132260001C99E0001C99E00002FB200019E6F00002B2F00002B2F00000483001132260001C99E0001C99E00002FB200019E6F00002B2F00002B2F0000048300019E6F00002B2F00002B2F0000048300002B2F000004830000048300000079001132260001C99E0001C99E00002FB200019E6F00002B2F00002B2F0000048300019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900002B2F0000048300000483000000790000048300000079000000790000000B001132260001C99E0001C99E00002FB200019E6F00002B2F00002B2F0000048300019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900002B2F0000048300000483000000790000048300000079000000790000000B00019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900002B2F0000048300000483000000790000048300000079000000790000000B00002B2F0000048300000483000000790000048300000079000000790000000B0000048300000079000000790000000B000000790000000B0000000B00000001
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
def samples : Fin 10 → ℤ := ![21, 2292, 50028, 505154, 3213429, 15002490, 56118016, 177725772, 494492733, 1240508808]

theorem samples_valid (n : Fin 10) : a (n.val + 1) = samples n := by
  rw [a_eq_G, G_eq_T (n.val + 1) (by omega)]
  have check : ∀ i : Fin 10, (tb (tabT (i.val + 1)) 511 : ℤ) = samples i := by
    decide +kernel
  exact check n

end Seven062

namespace Seven062
open PowerSeries
open OMA.S_oeis_a250062

def observations : Fin 10 → ℤ := ![21, 2292, 50028, 505154, 3213429, 15002490, 56118016, 177725772, 494492733, 1240508808]
def weights : Fin 10 → ℤ := ![21, 2271, 45465, 361925, 1483834, 3498044, 4938120, 4127760, 1885440, 362880]

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
    (shape : ∃ c : Fin 10 → ℤ, ∀ n : ℕ, a (n+1) = ∑ d, c d * ((n.choose d.val : ℕ):ℤ))
    (data : ∀ n : Fin 10, a (n.val+1)=observations n) (n : ℕ) :
    a (n+1)= ∑ d : Fin 10, weights d * ((n.choose d.val : ℕ):ℤ) := by
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

noncomputable def series : PowerSeries ℚ := mk fun n => if n < 1 then 0 else (a n:ℚ)

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
    (h : ∀ n : ℕ, a (n+1)= ∑ d : Fin 10, weights d * ((n.choose d.val : ℕ):ℤ)) :
    series * (1-X)^10 = X*(21+2082*X+28053*X^2+105494*X^3+142519*X^4+72798*X^5+11647*X^6+266*X^7) := by
  have hf := rational_binomial_series (D:=9) weights a h
  change series*(1-X)^10 = _ at hf
  rw [hf]
  norm_num [weights,Fin.sum_univ_succ]
  ring

end Seven062

namespace Seven062
open PowerSeries
open OMA.S_oeis_a250062

/-- Read the tenth finite difference off the numerator. -/
theorem recurrence_of_gf
    (h : series * (1-X)^10 = X*(21+2082*X+28053*X^2+105494*X^3+142519*X^4+72798*X^5+11647*X^6+266*X^7))
    (n : ℕ) (hn : 11≤n) :
    (a n : ℚ) = 10*a (n-1) - 45*a (n-2) + 120*a (n-3) - 210*a (n-4) +
      252*a (n-5) - 210*a (n-6) + 120*a (n-7) - 45*a (n-8) + 10*a (n-9) - a (n-10) := by
  have eqn : series - C 10*(series*X^1) + C 45*(series*X^2) - C 120*(series*X^3) +
      C 210*(series*X^4) - C 252*(series*X^5) + C 210*(series*X^6) - C 120*(series*X^7) +
      C 45*(series*X^8) - C 10*(series*X^9) + series*X^10 =
      C 21*X^1+C 2082*X^2+C 28053*X^3+C 105494*X^4+C 142519*X^5+
      C 72798*X^6+C 11647*X^7+C 266*X^8 := by
    simp only [map_ofNat]
    linear_combination h
  have atn := congrArg (coeff n) eqn
  simp only [map_sub,map_add,coeff_C_mul,coeff_mul_X_pow',coeff_C,series,coeff_mk] at atn
  simp (disch := omega) only [if_pos, if_neg, add_zero] at atn
  linarith only [atn]

end Seven062

open Seven062 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250062.main := by
  have data (n : Fin 10) : OMA.S_oeis_a250062.a (n.val+1) = observations n := samples_valid n
  have gf := gf_of_explicit (explicit_counts count_shape data)
  exact ⟨gf, recurrence_of_gf gf⟩
