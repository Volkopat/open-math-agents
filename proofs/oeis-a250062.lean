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
-- Each table row stores its field width followed by its packed coefficients.
def tb (T : ℕ × ℕ) (w : ℕ) : ℕ := (T.2 >>> (T.1 * w)) % 2 ^ T.1

def tabT : ℕ → ℕ × ℕ
  | 0 => (1, 0xf0000000000000007000000070007077f0000000000000003000000030003033f0000000100010117000101170117177f)
  | 1 => (5, 0xabdea7a9467a946518c37a946518c3518c330c637a946518c3518c330c63518c330c6330c6318cc37a946518c3518c330c63518c330c6330c6318cc3518c330c6330c6318cc330c6318cc318cc3821047bd4a528c6528c631863528c6318633186318c63528c6318633186318c633186318c6318c6332104528c6318633186318c633186318c6318c63321043186318c6318c633210418c633210432104410827a9ea519465194630cc35194630cc330cc3184635194630cc330cc31846330cc3184631846318d045194630cc330cc31846330cc3184631846318d0430cc3184631846318d041846318d0418d04410825294a318c6318c618c63318c618c6318c6318c64318c618c6318c6318c6418c6318c6418c6419082318c618c6318c6318c6418c6318c6418c641908218c6318c6418c641908218c64190821908220841)
  | 2 => (12, 0x8f43ca3de19a38117217e09638117217e09616708d09303338117217e09616708d09303316708d09303309203303501b38117217e09616708d09303316708d09303309203303501b16708d09303309203303501b09203303501b03801d02d00f38117217e09616708d09303316708d09303309203303501b16708d09303309203303501b09203303501b03801d02d00f16708d09303309203303501b09203303501b03801d02d00f09203303501b03801d02d00f03801d02d00f05101b01b0093de1f919a0d217e0c609604e17e0c609604e09304e03301b17e0c609604e09304e03301b09304e03301b03501d01d00f17e0c609604e09304e03301b09304e03301b03501d01d00f09304e03301b03501d01d00f03501d01d00f02d01b01b00917e0c609604e09304e03301b09304e03301b03501d01d00f09304e03301b03501d01d00f03501d01d00f02d01b01b00909304e03301b03501d01d00f03501d01d00f02d01b01b00903501d01d00f02d01b01b00902d01b01b00901b0090090033ca1951f90d21720960c604e1720960c604e08d03604e01b1720960c604e08d03604e01b08d03604e01b03301101d00f1720960c604e08d03604e01b08d03604e01b03301101d00f08d03604e01b03301101d00f03301101d00f01d00f01b0091720960c604e08d03604e01b08d03604e01b03301101d00f08d03604e01b03301101d00f03301101d00f01d00f01b00908d03604e01b03301101d00f03301101d00f01d00f01b00903301101d00f01d00f01b00901d00f01b00901b00900900319a0d20d206e09604e04e02a09604e04e02a03301b01b00f09604e04e02a03301b01b00f03301b01b00f01b00f00f00909604e04e02a03301b01b00f03301b01b00f01b00f00f00903301b01b00f01b00f00f00901b00f00f00900f00900900309604e04e02a03301b01b00f03301b01b00f01b00f00f00903301b01b00f01b00f00f00901b00f00f00900f00900900303301b01b00f01b00f00f00901b00f00f00900f00900900301b00f00f00900f00900900300f009009003009003003001)
  | 3 => (16, 0xc36c3aed3bf111bc370e105010c004c8370e105010c004c80fe0048f04bf013e370e105010c004c80fe0048f04bf013e0fe0048f04bf013e04b8014001500072370e105010c004c80fe0048f04bf013e0fe0048f04bf013e04b80140015000720fe0048f04bf013e04b801400150007204b80140015000720162007a00a8002a370e105010c004c80fe0048f04bf013e0fe0048f04bf013e04b80140015000720fe0048f04bf013e04b801400150007204b80140015000720162007a00a8002a0fe0048f04bf013e04b801400150007204b80140015000720162007a00a8002a04b80140015000720162007a00a8002a0162007a00a8002a01000040004000103bf114b411d0062c10c005dc04d401b010c005dc04d401b004bf01b00144007210c005dc04d401b004bf01b00144007204bf01b0014400720150007a007a002a10c005dc04d401b004bf01b00144007204bf01b0014400720150007a007a002a04bf01b0014400720150007a007a002a0150007a007a002a00a800400040001010c005dc04d401b004bf01b00144007204bf01b0014400720150007a007a002a04bf01b0014400720150007a007a002a0150007a007a002a00a800400040001004bf01b0014400720150007a007a002a0150007a007a002a00a80040004000100150007a007a002a00a800400040001000a800400040001000400010001000043aed11bc14b4062c105004d405dc01b0105004d405dc01b0048f015001b00072105004d405dc01b0048f015001b00072048f015001b0007201400056007a002a105004d405dc01b0048f015001b00072048f015001b0007201400056007a002a048f015001b0007201400056007a002a01400056007a002a007a002a00400010105004d405dc01b0048f015001b00072048f015001b0007201400056007a002a048f015001b0007201400056007a002a01400056007a002a007a002a00400010048f015001b0007201400056007a002a01400056007a002a007a002a0040001001400056007a002a007a002a00400010007a002a00400010004000100010000411bc062c062c023004c801b001b0009c04c801b001b0009c013e00720072002a04c801b001b0009c013e00720072002a013e00720072002a0072002a002a001004c801b001b0009c013e00720072002a013e00720072002a0072002a002a0010013e00720072002a0072002a002a00100072002a002a0010002a00100010000404c801b001b0009c013e00720072002a013e00720072002a0072002a002a0010013e00720072002a0072002a002a00100072002a002a0010002a001000100004013e00720072002a0072002a002a00100072002a002a0010002a0010001000040072002a002a0010002a001000100004002a0010001000040010000400040001)
  | 4 => (19, 0xf6a847349ce9f986b6c36904192603370016f836904192603370016f80c4ec058a40b7a804ce36904192603370016f80c4ec058a40b7a804ce0c4ec058a40b7a804ce02db001360028a0014a36904192603370016f80c4ec058a40b7a804ce0c4ec058a40b7a804ce02db001360028a0014a0c4ec058a40b7a804ce02db001360028a0014a02db001360028a0014a00aa00057800e10005a36904192603370016f80c4ec058a40b7a804ce0c4ec058a40b7a804ce02db001360028a0014a0c4ec058a40b7a804ce02db001360028a0014a02db001360028a0014a00aa00057800e10005a0c4ec058a40b7a804ce02db001360028a0014a02db001360028a0014a00aa00057800e10005a02db001360028a0014a00aa00057800e10005a00aa00057800e10005a004e2001f4003e800193a7e61e730362401c340cdc006c100ba6006180cdc006c100ba60061802dea0186002760014a0cdc006c100ba60061802dea0186002760014a02dea0186002760014a00a280057800af0005a0cdc006c100ba60061802dea0186002760014a02dea0186002760014a00a280057800af0005a02dea0186002760014a00a280057800af0005a00a280057800af0005a00384001f4003e800190cdc006c100ba60061802dea0186002760014a02dea0186002760014a00a280057800af0005a02dea0186002760014a00a280057800af0005a00a280057800af0005a00384001f4003e8001902dea0186002760014a00a280057800af0005a00a280057800af0005a00384001f4003e8001900a280057800af0005a00384001f4003e8001900384001f4003e80019000fa00064000c8000539a4e1b0583ce601c340c93005d300d82006180c93005d300d820061802c5201428030c0014a0c93005d300d820061802c5201428030c0014a02c5201428030c0014a009b00043800af0005a0c93005d300d820061802c5201428030c0014a02c5201428030c0014a009b00043800af0005a02c5201428030c0014a009b00043800af0005a009b00043800af0005a002bc00168003e800190c93005d300d820061802c5201428030c0014a02c5201428030c0014a009b00043800af0005a02c5201428030c0014a009b00043800af0005a009b00043800af0005a002bc00168003e8001902c5201428030c0014a009b00043800af0005a009b00043800af0005a002bc00168003e80019009b00043800af0005a002bc00168003e80019002bc00168003e80019000fa00064000c800050d6d8070d00e1a0078002df001860030c001a402df001860030c001a40099c0052800a50005a02df001860030c001a40099c0052800a50005a0099c0052800a50005a0029400168002d0001902df001860030c001a40099c0052800a50005a0099c0052800a50005a0029400168002d000190099c0052800a50005a0029400168002d000190029400168002d00019000b400064000c8000502df001860030c001a40099c0052800a50005a0099c0052800a50005a0029400168002d000190099c0052800a50005a0029400168002d000190029400168002d00019000b400064000c800050099c0052800a50005a0029400168002d000190029400168002d00019000b400064000c800050029400168002d00019000b400064000c80005000b400064000c800050003200014000280001)
  | 5 => (22, 0xc421d4956d225d6b81c58e23b5b41ae2206da480504623b5b41ae2206da4805046069b6804e0f0141fc00e0123b5b41ae2206da4805046069b6804e0f0141fc00e01069b6804e0f0141fc00e0101409800e1f003afc002fd23b5b41ae2206da4805046069b6804e0f0141fc00e01069b6804e0f0141fc00e0101409800e1f003afc002fd069b6804e0f0141fc00e0101409800e1f003afc002fd01409800e1f003afc002fd003d5400325000f78000a523b5b41ae2206da4805046069b6804e0f0141fc00e01069b6804e0f0141fc00e0101409800e1f003afc002fd069b6804e0f0141fc00e0101409800e1f003afc002fd01409800e1f003afc002fd003d5400325000f78000a5069b6804e0f0141fc00e0101409800e1f003afc002fd01409800e1f003afc002fd003d5400325000f78000a501409800e1f003afc002fd003d5400325000f78000a5003d5400325000f78000a5001440000d80003600002425d6b81f84707280805f4606da4805be6014628010fe06da4805be6014628010fe0141fc010fe00396c002fd06da4805be6014628010fe0141fc010fe00396c002fd0141fc010fe00396c002fd003afc00325000c94000a506da4805be6014628010fe0141fc010fe00396c002fd0141fc010fe00396c002fd003afc00325000c94000a50141fc010fe00396c002fd003afc00325000c94000a5003afc00325000c94000a5000f78000d80003600002406da4805be6014628010fe0141fc010fe00396c002fd0141fc010fe00396c002fd003afc00325000c94000a50141fc010fe00396c002fd003afc00325000c94000a5003afc00325000c94000a5000f78000d8000360000240141fc010fe00396c002fd003afc00325000c94000a5003afc00325000c94000a5000f78000d800036000024003afc00325000c94000a5000f78000d800036000024000f78000d8000360000240003600002400009000006255b481c99e07e11c05f4606b8880518a016f98010fe06b8880518a016f98010fe01383c00e970043f8002fd06b8880518a016f98010fe01383c00e970043f8002fd01383c00e970043f8002fd00387c0028f000c94000a506b8880518a016f98010fe01383c00e970043f8002fd01383c00e970043f8002fd00387c0028f000c94000a501383c00e970043f8002fd00387c0028f000c94000a500387c0028f000c94000a5000c94000a50003600002406b8880518a016f98010fe01383c00e970043f8002fd01383c00e970043f8002fd00387c0028f000c94000a501383c00e970043f8002fd00387c0028f000c94000a500387c0028f000c94000a5000c94000a50003600002401383c00e970043f8002fd00387c0028f000c94000a500387c0028f000c94000a5000c94000a50003600002400387c0028f000c94000a5000c94000a500036000024000c94000a500036000024000360000240000900000607163805f46017d1801432014118010fe0043f8003a2014118010fe0043f8003a2003804002fd000bf4000a5014118010fe0043f8003a2003804002fd000bf4000a5003804002fd000bf4000a5000bf4000a500029400024014118010fe0043f8003a2003804002fd000bf4000a5003804002fd000bf4000a5000bf4000a500029400024003804002fd000bf4000a5000bf4000a500029400024000bf4000a5000294000240002940002400009000006014118010fe0043f8003a2003804002fd000bf4000a5003804002fd000bf4000a5000bf4000a500029400024003804002fd000bf4000a5000bf4000a500029400024000bf4000a5000294000240002940002400009000006003804002fd000bf4000a5000bf4000a500029400024000bf4000a5000294000240002940002400009000006000bf4000a500029400024000294000240000900000600029400024000090000060000900000600001800001)
  | 6 => (24, 0xe4eb7a24c11f252d1705e02e236313059f5205b82600e2e6236313059f5205b82600e2e6058b5500ddd000e3e20021e1236313059f5205b82600e2e6058b5500ddd000e3e20021e1058b5500ddd000e3e20021e100e3020022270023850005fd236313059f5205b82600e2e6058b5500ddd000e3e20021e1058b5500ddd000e3e20021e100e3020022270023850005fd058b5500ddd000e3e20021e100e3020022270023850005fd00e3020022270023850005fd0024c0000643000777000111236313059f5205b82600e2e6058b5500ddd000e3e20021e1058b5500ddd000e3e20021e100e3020022270023850005fd058b5500ddd000e3e20021e100e3020022270023850005fd00e3020022270023850005fd0024c0000643000777000111058b5500ddd000e3e20021e100e3020022270023850005fd00e3020022270023850005fd0024c000064300077700011100e3020022270023850005fd0024c00006430007770001110024c0000643000777000111000961000157000157000031252d170670b105f00a0106c605b82600feca00e6820027de05b82600feca00e6820027de00e3e20027de0022b30005fd05b82600feca00e6820027de00e3e20027de0022b30005fd00e3e20027de0022b30005fd00238500064300064300011105b82600feca00e6820027de00e3e20027de0022b30005fd00e3e20027de0022b30005fd00238500064300064300011100e3e20027de0022b30005fd00238500064300064300011100238500064300064300011100077700015700015700003105b82600feca00e6820027de00e3e20027de0022b30005fd00e3e20027de0022b30005fd00238500064300064300011100e3e20027de0022b30005fd00238500064300064300011100238500064300064300011100077700015700015700003100e3e20027de0022b30005fd00238500064300064300011100238500064300064300011100077700015700015700003100238500064300064300011100077700015700015700003100077700015700015700003100015700003100003100000724c11f05ef5b0670b10106c6059f5200e68200feca0027de059f5200e68200feca0027de00ddd000231c0027de0005fd059f5200e68200feca0027de00ddd000231c0027de0005fd00ddd000231c0027de0005fd002227000547000643000111059f5200e68200feca0027de00ddd000231c0027de0005fd00ddd000231c0027de0005fd00222700054700064300011100ddd000231c0027de0005fd002227000547000643000111002227000547000643000111000643000111000157000031059f5200e68200feca0027de00ddd000231c0027de0005fd00ddd000231c0027de0005fd00222700054700064300011100ddd000231c0027de0005fd00222700054700064300011100222700054700064300011100064300011100015700003100ddd000231c0027de0005fd00222700054700064300011100222700054700064300011100064300011100015700003100222700054700064300011100064300011100015700003100064300011100015700003100015700003100003100000705e02e0106c60106c6002e3600e2e60027de0027de00070e00e2e60027de0027de00070e0021e10005fd0005fd00011100e2e60027de0027de00070e0021e10005fd0005fd0001110021e10005fd0005fd0001110005fd00011100011100003100e2e60027de0027de00070e0021e10005fd0005fd0001110021e10005fd0005fd0001110005fd0001110001110000310021e10005fd0005fd0001110005fd0001110001110000310005fd00011100011100003100011100003100003100000700e2e60027de0027de00070e0021e10005fd0005fd0001110021e10005fd0005fd0001110005fd0001110001110000310021e10005fd0005fd0001110005fd0001110001110000310005fd0001110001110000310001110000310000310000070021e10005fd0005fd0001110005fd0001110001110000310005fd0001110001110000310001110000310000310000070005fd000111000111000031000111000031000031000007000111000031000031000007000031000007000007000001)
  | 7 => (26, 0xd612c0076bdc61dfdd781064b81cbbd700fca1004020c00227401cbbd700fca1004020c002274003e6b40021cea008a8280047dc1cbbd700fca1004020c002274003e6b40021cea008a8280047dc03e6b40021cea008a8280047dc008a0800048680012c20000ad41cbbd700fca1004020c002274003e6b40021cea008a8280047dc03e6b40021cea008a8280047dc008a0800048680012c20000ad403e6b40021cea008a8280047dc008a0800048680012c20000ad4008a0800048680012c20000ad40013550000b4400034800001a41cbbd700fca1004020c002274003e6b40021cea008a8280047dc03e6b40021cea008a8280047dc008a0800048680012c20000ad403e6b40021cea008a8280047dc008a0800048680012c20000ad4008a0800048680012c20000ad40013550000b4400034800001a403e6b40021cea008a8280047dc008a0800048680012c20000ad4008a0800048680012c20000ad40013550000b4400034800001a4008a0800048680012c20000ad40013550000b4400034800001a40013550000b4400034800001a4000400000020000008000000401dfdd7811c60004246400272b804020c0026218008bf200052b004020c0026218008bf200052b0008a8280052b00012600000ad404020c0026218008bf200052b0008a8280052b00012600000ad4008a8280052b00012600000ad40012c20000b440002d100001a404020c0026218008bf200052b0008a8280052b00012600000ad4008a8280052b00012600000ad40012c20000b440002d100001a4008a8280052b00012600000ad40012c20000b440002d100001a40012c20000b440002d100001a40003480000200000080000004004020c0026218008bf200052b0008a8280052b00012600000ad4008a8280052b00012600000ad40012c20000b440002d100001a4008a8280052b00012600000ad40012c20000b440002d100001a40012c20000b440002d100001a400034800002000000800000040008a8280052b00012600000ad40012c20000b440002d100001a40012c20000b440002d100001a4000348000020000008000000400012c20000b440002d100001a40003480000200000080000004000034800002000000800000040000080000004000001000000081daf71810907804718000272b803f2840022fc800988600052b003f2840022fc800988600052b000873a8004a280014ac0000ad403f2840022fc800988600052b000873a8004a280014ac0000ad400873a8004a280014ac0000ad400121a00009bc0002d100001a403f2840022fc800988600052b000873a8004a280014ac0000ad400873a8004a280014ac0000ad400121a00009bc0002d100001a400873a8004a280014ac0000ad400121a00009bc0002d100001a400121a00009bc0002d100001a40002d100001a4000080000004003f2840022fc800988600052b000873a8004a280014ac0000ad400873a8004a280014ac0000ad400121a00009bc0002d100001a400873a8004a280014ac0000ad400121a00009bc0002d100001a400121a00009bc0002d100001a40002d100001a4000080000004000873a8004a280014ac0000ad400121a00009bc0002d100001a400121a00009bc0002d100001a40002d100001a4000080000004000121a00009bc0002d100001a40002d100001a400008000000400002d100001a400008000000400000800000040000010000000804192e00272b8009cae0005e100089d000052b00014ac0000c780089d000052b00014ac0000c780011f70000ad40002b500001a40089d000052b00014ac0000c780011f70000ad40002b500001a40011f70000ad40002b500001a40002b500001a400006900000400089d000052b00014ac0000c780011f70000ad40002b500001a40011f70000ad40002b500001a40002b500001a400006900000400011f70000ad40002b500001a40002b500001a400006900000400002b500001a40000690000040000069000004000001000000080089d000052b00014ac0000c780011f70000ad40002b500001a40011f70000ad40002b500001a40002b500001a400006900000400011f70000ad40002b500001a40002b500001a400006900000400002b500001a40000690000040000069000004000001000000080011f70000ad40002b500001a40002b500001a400006900000400002b500001a40000690000040000069000004000001000000080002b500001a40000690000040000069000004000001000000080000690000040000010000000800001000000080000020000001)
  | 8 => (28, 0xa97e14c14acbca14de4720282cd81418004026e2c00276c90004abe01418004026e2c00276c90004abe00267eac00498ae004b2460008a3c1418004026e2c00276c90004abe00267eac00498ae004b2460008a3c0267eac00498ae004b2460008a3c004ae800008b380008fd000012241418004026e2c00276c90004abe00267eac00498ae004b2460008a3c0267eac00498ae004b2460008a3c004ae800008b380008fd000012240267eac00498ae004b2460008a3c004ae800008b380008fd00001224004ae800008b380008fd0000122400093c000012cc000158400002641418004026e2c00276c90004abe00267eac00498ae004b2460008a3c0267eac00498ae004b2460008a3c004ae800008b380008fd000012240267eac00498ae004b2460008a3c004ae800008b380008fd00001224004ae800008b380008fd0000122400093c000012cc000158400002640267eac00498ae004b2460008a3c004ae800008b380008fd00001224004ae800008b380008fd0000122400093c000012cc00015840000264004ae800008b380008fd0000122400093c000012cc0001584000026400093c000012cc0001584000026400019a100002d900002d9000005114de47202b2f0002899200053c280276c900051ca8004bd980009c600276c900051ca8004bd980009c60004b2460009c600008d3000012240276c900051ca8004bd980009c60004b2460009c600008d300001224004b2460009c600008d3000012240008fd000012cc00012cc00002640276c900051ca8004bd980009c60004b2460009c600008d300001224004b2460009c600008d3000012240008fd000012cc00012cc0000264004b2460009c600008d3000012240008fd000012cc00012cc00002640008fd000012cc00012cc0000264000158400002d900002d900000510276c900051ca8004bd980009c60004b2460009c600008d300001224004b2460009c600008d3000012240008fd000012cc00012cc0000264004b2460009c600008d3000012240008fd000012cc00012cc00002640008fd000012cc00012cc0000264000158400002d900002d90000051004b2460009c600008d3000012240008fd000012cc00012cc00002640008fd000012cc00012cc0000264000158400002d900002d900000510008fd000012cc00012cc0000264000158400002d900002d90000051000158400002d900002d9000005100002d900000510000051000000914acbca028977c02b2f000053c28026e2c0004bd980051ca80009c60026e2c0004bd980051ca80009c6000498ae0008e2c0009c600001224026e2c0004bd980051ca80009c6000498ae0008e2c0009c60000122400498ae0008e2c0009c6000012240008b38000108c00012cc0000264026e2c0004bd980051ca80009c6000498ae0008e2c0009c60000122400498ae0008e2c0009c6000012240008b38000108c00012cc000026400498ae0008e2c0009c6000012240008b38000108c00012cc00002640008b38000108c00012cc000026400012cc000026400002d90000051026e2c0004bd980051ca80009c6000498ae0008e2c0009c60000122400498ae0008e2c0009c6000012240008b38000108c00012cc000026400498ae0008e2c0009c6000012240008b38000108c00012cc00002640008b38000108c00012cc000026400012cc000026400002d9000005100498ae0008e2c0009c6000012240008b38000108c00012cc00002640008b38000108c00012cc000026400012cc000026400002d900000510008b38000108c00012cc000026400012cc000026400002d9000005100012cc000026400002d9000005100002d90000051000005100000090282cd80053c280053c28000af50004abe00009c600009c600001488004abe00009c600009c6000014880008a3c000122400012240000264004abe00009c600009c6000014880008a3c0001224000122400002640008a3c0001224000122400002640001224000026400002640000051004abe00009c600009c6000014880008a3c0001224000122400002640008a3c00012240001224000026400012240000264000026400000510008a3c000122400012240000264000122400002640000264000005100012240000264000026400000510000264000005100000510000009004abe00009c600009c6000014880008a3c0001224000122400002640008a3c00012240001224000026400012240000264000026400000510008a3c0001224000122400002640001224000026400002640000051000122400002640000264000005100002640000051000005100000090008a3c0001224000122400002640001224000026400002640000051000122400002640000264000005100002640000051000005100000090001224000026400002640000051000026400000510000051000000900002640000051000005100000090000051000000900000090000001)
  | 9 => (29, 0xebcae1e8cd521846789fd205903b219061658159f3a80af2714009483619061658159f3a80af2714009483602add0d00249bd0012aa28000f69f19061658159f3a80af2714009483602add0d00249bd0012aa28000f69f02add0d00249bd0012aa28000f69f004a71b0003e10c001ff860001ca719061658159f3a80af2714009483602add0d00249bd0012aa28000f69f02add0d00249bd0012aa28000f69f004a71b0003e10c001ff860001ca702add0d00249bd0012aa28000f69f004a71b0003e10c001ff860001ca7004a71b0003e10c001ff860001ca7000830b8000765c00042cc000035719061658159f3a80af2714009483602add0d00249bd0012aa28000f69f02add0d00249bd0012aa28000f69f004a71b0003e10c001ff860001ca702add0d00249bd0012aa28000f69f004a71b0003e10c001ff860001ca7004a71b0003e10c001ff860001ca7000830b8000765c00042cc000035702add0d00249bd0012aa28000f69f004a71b0003e10c001ff860001ca7004a71b0003e10c001ff860001ca7000830b8000765c00042cc0000357004a71b0003e10c001ff860001ca7000830b8000765c00042cc0000357000830b8000765c00042cc0000357000138800000fa000007d0000006419e27f4817c0fdc0b3d95400a486202bc9c500284388012d35c001134602bc9c500284388012d35c0011346004aa8a00044d18001f7160001ca702bc9c500284388012d35c0011346004aa8a00044d18001f7160001ca7004aa8a00044d18001f7160001ca70007fe18000765c0003b2e000035702bc9c500284388012d35c0011346004aa8a00044d18001f7160001ca7004aa8a00044d18001f7160001ca70007fe18000765c0003b2e0000357004aa8a00044d18001f7160001ca70007fe18000765c0003b2e00003570007fe18000765c0003b2e000035700010b300000fa000007d0000006402bc9c500284388012d35c0011346004aa8a00044d18001f7160001ca7004aa8a00044d18001f7160001ca70007fe18000765c0003b2e0000357004aa8a00044d18001f7160001ca70007fe18000765c0003b2e00003570007fe18000765c0003b2e000035700010b300000fa000007d00000064004aa8a00044d18001f7160001ca70007fe18000765c0003b2e00003570007fe18000765c0003b2e000035700010b300000fa000007d000000640007fe18000765c0003b2e000035700010b300000fa000007d0000006400010b300000fa000007d0000006400001f40000019000000c8000000a19aa4308167a9480be07ee00a486202b3e750025a6b801421c4001134602b3e750025a6b801421c40011346004937a0003f3cc002268c0001ca702b3e750025a6b801421c40011346004937a0003f3cc002268c0001ca7004937a0003f3cc002268c0001ca70007c21800069b40003b2e000035702b3e750025a6b801421c40011346004937a0003f3cc002268c0001ca7004937a0003f3cc002268c0001ca70007c21800069b40003b2e0000357004937a0003f3cc002268c0001ca70007c21800069b40003b2e00003570007c21800069b40003b2e00003570000ecb80000d5c00007d0000006402b3e750025a6b801421c40011346004937a0003f3cc002268c0001ca7004937a0003f3cc002268c0001ca70007c21800069b40003b2e0000357004937a0003f3cc002268c0001ca70007c21800069b40003b2e00003570007c21800069b40003b2e00003570000ecb80000d5c00007d00000064004937a0003f3cc002268c0001ca70007c21800069b40003b2e00003570007c21800069b40003b2e00003570000ecb80000d5c00007d000000640007c21800069b40003b2e00003570000ecb80000d5c00007d000000640000ecb80000d5c00007d0000006400001f40000019000000c8000000a02c81d90029218801490c4001310a004a41b00044d18002268c0001ffe004a41b00044d18002268c0001ffe0007b4f8000729c000394e0000357004a41b00044d18002268c0001ffe0007b4f8000729c000394e00003570007b4f8000729c000394e00003570000e5380000d5c00006ae0000064004a41b00044d18002268c0001ffe0007b4f8000729c000394e00003570007b4f8000729c000394e00003570000e5380000d5c00006ae00000640007b4f8000729c000394e00003570000e5380000d5c00006ae00000640000e5380000d5c00006ae000006400001ab8000019000000c8000000a004a41b00044d18002268c0001ffe0007b4f8000729c000394e00003570007b4f8000729c000394e00003570000e5380000d5c00006ae00000640007b4f8000729c000394e00003570000e5380000d5c00006ae00000640000e5380000d5c00006ae000006400001ab8000019000000c8000000a0007b4f8000729c000394e00003570000e5380000d5c00006ae00000640000e5380000d5c00006ae000006400001ab8000019000000c8000000a0000e5380000d5c00006ae000006400001ab8000019000000c8000000a00001ab8000019000000c8000000a00000320000002800000140000001)
  | 10 => (31, 0x93e153101d0eb2403a929de00b5f5220e33bdca02c55508059b04f001132260e33bdca02c55508059b04f00113226015fe5460043ee7c008a4de80019e6f0e33bdca02c55508059b04f00113226015fe5460043ee7c008a4de80019e6f015fe5460043ee7c008a4de80019e6f00227c040006840c000d64e80002b2f0e33bdca02c55508059b04f00113226015fe5460043ee7c008a4de80019e6f015fe5460043ee7c008a4de80019e6f00227c040006840c000d64e80002b2f015fe5460043ee7c008a4de80019e6f00227c040006840c000d64e80002b2f00227c040006840c000d64e80002b2f00036c900000b1e400018d0800004830e33bdca02c55508059b04f00113226015fe5460043ee7c008a4de80019e6f015fe5460043ee7c008a4de80019e6f00227c040006840c000d64e80002b2f015fe5460043ee7c008a4de80019e6f00227c040006840c000d64e80002b2f00227c040006840c000d64e80002b2f00036c900000b1e400018d080000483015fe5460043ee7c008a4de80019e6f00227c040006840c000d64e80002b2f00227c040006840c000d64e80002b2f00036c900000b1e400018d08000048300227c040006840c000d64e80002b2f00036c900000b1e400018d08000048300036c900000b1e400018d08000048300007262000014cc0000299800000790ea4a778030470c405be0050012defa0166c13c004a0ab8008b6770001c99e0166c13c004a0ab8008b6770001c99e0022937a00072678000d31580002b2f0166c13c004a0ab8008b6770001c99e0022937a00072678000d31580002b2f0022937a00072678000d31580002b2f0003593a0000b1e4000163c800004830166c13c004a0ab8008b6770001c99e0022937a00072678000d31580002b2f0022937a00072678000d31580002b2f0003593a0000b1e4000163c800004830022937a00072678000d31580002b2f0003593a0000b1e4000163c800004830003593a0000b1e4000163c8000048300006342000014cc0000299800000790166c13c004a0ab8008b6770001c99e0022937a00072678000d31580002b2f0022937a00072678000d31580002b2f0003593a0000b1e4000163c800004830022937a00072678000d31580002b2f0003593a0000b1e4000163c800004830003593a0000b1e4000163c8000048300006342000014cc0000299800000790022937a00072678000d31580002b2f0003593a0000b1e4000163c800004830003593a0000b1e4000163c8000048300006342000014cc0000299800000790003593a0000b1e4000163c8000048300006342000014cc00002998000007900006342000014cc00002998000007900000a66000001e4000003c8000000b0e87592002def3440608e188012defa0162aa840045b3b800941570001c99e0162aa840045b3b800941570001c99e0021f73e0006a068000e4cf00002b2f0162aa840045b3b800941570001c99e0021f73e0006a068000e4cf00002b2f0021f73e0006a068000e4cf00002b2f000342060000a0b4000163c800004830162aa840045b3b800941570001c99e0021f73e0006a068000e4cf00002b2f0021f73e0006a068000e4cf00002b2f000342060000a0b4000163c800004830021f73e0006a068000e4cf00002b2f000342060000a0b4000163c80000483000342060000a0b4000163c80000483000058f20000120c0000299800000790162aa840045b3b800941570001c99e0021f73e0006a068000e4cf00002b2f0021f73e0006a068000e4cf00002b2f000342060000a0b4000163c800004830021f73e0006a068000e4cf00002b2f000342060000a0b4000163c80000483000342060000a0b4000163c80000483000058f20000120c0000299800000790021f73e0006a068000e4cf00002b2f000342060000a0b4000163c80000483000342060000a0b4000163c80000483000058f20000120c000029980000079000342060000a0b4000163c80000483000058f20000120c000029980000079000058f20000120c00002998000007900000a66000001e4000003c8000000b016bea44004b7be80096f7d0001f64e0022644c00072678000e4cf00002fb20022644c00072678000e4cf00002fb200033cde0000acbc0001597800004830022644c00072678000e4cf00002fb200033cde0000acbc00015978000048300033cde0000acbc0001597800004830000565e0000120c0000241800000790022644c00072678000e4cf00002fb200033cde0000acbc00015978000048300033cde0000acbc0001597800004830000565e0000120c00002418000007900033cde0000acbc0001597800004830000565e0000120c0000241800000790000565e0000120c00002418000007900000906000001e4000003c8000000b0022644c00072678000e4cf00002fb200033cde0000acbc00015978000048300033cde0000acbc0001597800004830000565e0000120c00002418000007900033cde0000acbc0001597800004830000565e0000120c0000241800000790000565e0000120c00002418000007900000906000001e4000003c8000000b00033cde0000acbc0001597800004830000565e0000120c0000241800000790000565e0000120c00002418000007900000906000001e4000003c8000000b0000565e0000120c00002418000007900000906000001e4000003c8000000b00000906000001e4000003c8000000b000000f20000002c000000580000001)
  | _ => (1, 0)

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
