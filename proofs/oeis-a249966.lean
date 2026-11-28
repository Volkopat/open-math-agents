import OMAStatements.S_oeis_a249966

/-!
A249966: the generating function and recurrence for eleven-position arrays with
strict second/third order-statistic gaps in every length-six window.

Adapted with credit from @Salofe's A250064 threshold-chain proof, PR23285,
https://github.com/lefttosolve2/open-math-agents/pull/23285
(head bd4969a8ddc52c3bd7f8d30008570b9868fd00b6).
The exact six windows, 2048 subset states and all packed tables are regenerated
and kernel checked here. A state-vector finite-difference identity propagates by
linearity to every index, yielding the universal recurrence and generating function.
The conjectures are Colin Barker's; the formal statement is @clementtrecourt's.
-/

namespace OMA.Helpers

open OMA.S_oeis_a249966 Finset

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

/-! ### Strict threshold sets -/

/-- Entry `k` of a set of positions (`false` past the end). -/
def fget (f : Fin 11 → Bool) (k : ℕ) : Bool := if h : k < 11 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 11 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 6 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 11 → Bool) : Prop := ∀ i < (6 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 11 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 11 → Fin (n + 1)) (v : ℕ) : Fin 11 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 11 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a249966.get x k ≤ n := by
  unfold OMA.S_oeis_a249966.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (6 : ℕ), cntW (fun _ => true) i = 6 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 11 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (6 : ℕ), ¬ Cy (fun t : Fin 6 => OMA.S_oeis_a249966.get x (i + t)) := by
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
  have step2 : ∀ i < (6 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 6 => OMA.S_oeis_a249966.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 11 := by have := t.isLt; omega
    unfold OMA.S_oeis_a249966.get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 11 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 11 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 11 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 11 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 11 → Fin (n + 2)) : Fin 11 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 11 → Bool) (x : Fin 11 → Fin (n + 1)) : Fin 11 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 11 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 11 → Bool) (x : Fin 11 → Fin (n + 1)) (p : Fin 11) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 11 → Bool) :
    M (n + 1) T = ∑ S : Fin 11 → Bool,
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
def row (u : Fin 2048) : Fin 11 → Bool := fun p => Nat.testBit u.val p.val

def idIndex (k : Fin 64) (i : Fin 32) : Fin 2048 := ⟨32 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 11
  · exact congrFun h ⟨i, hi⟩
  · have hp : 2048 ≤ 2 ^ i := by
      change 2 ^ 11 ≤ 2 ^ i
      exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hp)]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 11 bits. -/
def pcb (m : ℕ) : ℕ :=
  m / 1 % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2 + m / 256 % 2 + m / 512 % 2 + m / 1024 % 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_0 : ∀ i : Fin 32, cntW (row (idIndex 0 i)) 0 = pcb ((idIndex 0 i).val &&& 63) ∧ cntW (row (idIndex 0 i)) 1 = pcb ((idIndex 0 i).val &&& 126) ∧ cntW (row (idIndex 0 i)) 2 = pcb ((idIndex 0 i).val &&& 252) ∧ cntW (row (idIndex 0 i)) 3 = pcb ((idIndex 0 i).val &&& 504) ∧ cntW (row (idIndex 0 i)) 4 = pcb ((idIndex 0 i).val &&& 1008) ∧ cntW (row (idIndex 0 i)) 5 = pcb ((idIndex 0 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_1 : ∀ i : Fin 32, cntW (row (idIndex 1 i)) 0 = pcb ((idIndex 1 i).val &&& 63) ∧ cntW (row (idIndex 1 i)) 1 = pcb ((idIndex 1 i).val &&& 126) ∧ cntW (row (idIndex 1 i)) 2 = pcb ((idIndex 1 i).val &&& 252) ∧ cntW (row (idIndex 1 i)) 3 = pcb ((idIndex 1 i).val &&& 504) ∧ cntW (row (idIndex 1 i)) 4 = pcb ((idIndex 1 i).val &&& 1008) ∧ cntW (row (idIndex 1 i)) 5 = pcb ((idIndex 1 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_2 : ∀ i : Fin 32, cntW (row (idIndex 2 i)) 0 = pcb ((idIndex 2 i).val &&& 63) ∧ cntW (row (idIndex 2 i)) 1 = pcb ((idIndex 2 i).val &&& 126) ∧ cntW (row (idIndex 2 i)) 2 = pcb ((idIndex 2 i).val &&& 252) ∧ cntW (row (idIndex 2 i)) 3 = pcb ((idIndex 2 i).val &&& 504) ∧ cntW (row (idIndex 2 i)) 4 = pcb ((idIndex 2 i).val &&& 1008) ∧ cntW (row (idIndex 2 i)) 5 = pcb ((idIndex 2 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_3 : ∀ i : Fin 32, cntW (row (idIndex 3 i)) 0 = pcb ((idIndex 3 i).val &&& 63) ∧ cntW (row (idIndex 3 i)) 1 = pcb ((idIndex 3 i).val &&& 126) ∧ cntW (row (idIndex 3 i)) 2 = pcb ((idIndex 3 i).val &&& 252) ∧ cntW (row (idIndex 3 i)) 3 = pcb ((idIndex 3 i).val &&& 504) ∧ cntW (row (idIndex 3 i)) 4 = pcb ((idIndex 3 i).val &&& 1008) ∧ cntW (row (idIndex 3 i)) 5 = pcb ((idIndex 3 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_4 : ∀ i : Fin 32, cntW (row (idIndex 4 i)) 0 = pcb ((idIndex 4 i).val &&& 63) ∧ cntW (row (idIndex 4 i)) 1 = pcb ((idIndex 4 i).val &&& 126) ∧ cntW (row (idIndex 4 i)) 2 = pcb ((idIndex 4 i).val &&& 252) ∧ cntW (row (idIndex 4 i)) 3 = pcb ((idIndex 4 i).val &&& 504) ∧ cntW (row (idIndex 4 i)) 4 = pcb ((idIndex 4 i).val &&& 1008) ∧ cntW (row (idIndex 4 i)) 5 = pcb ((idIndex 4 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_5 : ∀ i : Fin 32, cntW (row (idIndex 5 i)) 0 = pcb ((idIndex 5 i).val &&& 63) ∧ cntW (row (idIndex 5 i)) 1 = pcb ((idIndex 5 i).val &&& 126) ∧ cntW (row (idIndex 5 i)) 2 = pcb ((idIndex 5 i).val &&& 252) ∧ cntW (row (idIndex 5 i)) 3 = pcb ((idIndex 5 i).val &&& 504) ∧ cntW (row (idIndex 5 i)) 4 = pcb ((idIndex 5 i).val &&& 1008) ∧ cntW (row (idIndex 5 i)) 5 = pcb ((idIndex 5 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_6 : ∀ i : Fin 32, cntW (row (idIndex 6 i)) 0 = pcb ((idIndex 6 i).val &&& 63) ∧ cntW (row (idIndex 6 i)) 1 = pcb ((idIndex 6 i).val &&& 126) ∧ cntW (row (idIndex 6 i)) 2 = pcb ((idIndex 6 i).val &&& 252) ∧ cntW (row (idIndex 6 i)) 3 = pcb ((idIndex 6 i).val &&& 504) ∧ cntW (row (idIndex 6 i)) 4 = pcb ((idIndex 6 i).val &&& 1008) ∧ cntW (row (idIndex 6 i)) 5 = pcb ((idIndex 6 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_7 : ∀ i : Fin 32, cntW (row (idIndex 7 i)) 0 = pcb ((idIndex 7 i).val &&& 63) ∧ cntW (row (idIndex 7 i)) 1 = pcb ((idIndex 7 i).val &&& 126) ∧ cntW (row (idIndex 7 i)) 2 = pcb ((idIndex 7 i).val &&& 252) ∧ cntW (row (idIndex 7 i)) 3 = pcb ((idIndex 7 i).val &&& 504) ∧ cntW (row (idIndex 7 i)) 4 = pcb ((idIndex 7 i).val &&& 1008) ∧ cntW (row (idIndex 7 i)) 5 = pcb ((idIndex 7 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_8 : ∀ i : Fin 32, cntW (row (idIndex 8 i)) 0 = pcb ((idIndex 8 i).val &&& 63) ∧ cntW (row (idIndex 8 i)) 1 = pcb ((idIndex 8 i).val &&& 126) ∧ cntW (row (idIndex 8 i)) 2 = pcb ((idIndex 8 i).val &&& 252) ∧ cntW (row (idIndex 8 i)) 3 = pcb ((idIndex 8 i).val &&& 504) ∧ cntW (row (idIndex 8 i)) 4 = pcb ((idIndex 8 i).val &&& 1008) ∧ cntW (row (idIndex 8 i)) 5 = pcb ((idIndex 8 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_9 : ∀ i : Fin 32, cntW (row (idIndex 9 i)) 0 = pcb ((idIndex 9 i).val &&& 63) ∧ cntW (row (idIndex 9 i)) 1 = pcb ((idIndex 9 i).val &&& 126) ∧ cntW (row (idIndex 9 i)) 2 = pcb ((idIndex 9 i).val &&& 252) ∧ cntW (row (idIndex 9 i)) 3 = pcb ((idIndex 9 i).val &&& 504) ∧ cntW (row (idIndex 9 i)) 4 = pcb ((idIndex 9 i).val &&& 1008) ∧ cntW (row (idIndex 9 i)) 5 = pcb ((idIndex 9 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_10 : ∀ i : Fin 32, cntW (row (idIndex 10 i)) 0 = pcb ((idIndex 10 i).val &&& 63) ∧ cntW (row (idIndex 10 i)) 1 = pcb ((idIndex 10 i).val &&& 126) ∧ cntW (row (idIndex 10 i)) 2 = pcb ((idIndex 10 i).val &&& 252) ∧ cntW (row (idIndex 10 i)) 3 = pcb ((idIndex 10 i).val &&& 504) ∧ cntW (row (idIndex 10 i)) 4 = pcb ((idIndex 10 i).val &&& 1008) ∧ cntW (row (idIndex 10 i)) 5 = pcb ((idIndex 10 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_11 : ∀ i : Fin 32, cntW (row (idIndex 11 i)) 0 = pcb ((idIndex 11 i).val &&& 63) ∧ cntW (row (idIndex 11 i)) 1 = pcb ((idIndex 11 i).val &&& 126) ∧ cntW (row (idIndex 11 i)) 2 = pcb ((idIndex 11 i).val &&& 252) ∧ cntW (row (idIndex 11 i)) 3 = pcb ((idIndex 11 i).val &&& 504) ∧ cntW (row (idIndex 11 i)) 4 = pcb ((idIndex 11 i).val &&& 1008) ∧ cntW (row (idIndex 11 i)) 5 = pcb ((idIndex 11 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_12 : ∀ i : Fin 32, cntW (row (idIndex 12 i)) 0 = pcb ((idIndex 12 i).val &&& 63) ∧ cntW (row (idIndex 12 i)) 1 = pcb ((idIndex 12 i).val &&& 126) ∧ cntW (row (idIndex 12 i)) 2 = pcb ((idIndex 12 i).val &&& 252) ∧ cntW (row (idIndex 12 i)) 3 = pcb ((idIndex 12 i).val &&& 504) ∧ cntW (row (idIndex 12 i)) 4 = pcb ((idIndex 12 i).val &&& 1008) ∧ cntW (row (idIndex 12 i)) 5 = pcb ((idIndex 12 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_13 : ∀ i : Fin 32, cntW (row (idIndex 13 i)) 0 = pcb ((idIndex 13 i).val &&& 63) ∧ cntW (row (idIndex 13 i)) 1 = pcb ((idIndex 13 i).val &&& 126) ∧ cntW (row (idIndex 13 i)) 2 = pcb ((idIndex 13 i).val &&& 252) ∧ cntW (row (idIndex 13 i)) 3 = pcb ((idIndex 13 i).val &&& 504) ∧ cntW (row (idIndex 13 i)) 4 = pcb ((idIndex 13 i).val &&& 1008) ∧ cntW (row (idIndex 13 i)) 5 = pcb ((idIndex 13 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_14 : ∀ i : Fin 32, cntW (row (idIndex 14 i)) 0 = pcb ((idIndex 14 i).val &&& 63) ∧ cntW (row (idIndex 14 i)) 1 = pcb ((idIndex 14 i).val &&& 126) ∧ cntW (row (idIndex 14 i)) 2 = pcb ((idIndex 14 i).val &&& 252) ∧ cntW (row (idIndex 14 i)) 3 = pcb ((idIndex 14 i).val &&& 504) ∧ cntW (row (idIndex 14 i)) 4 = pcb ((idIndex 14 i).val &&& 1008) ∧ cntW (row (idIndex 14 i)) 5 = pcb ((idIndex 14 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_15 : ∀ i : Fin 32, cntW (row (idIndex 15 i)) 0 = pcb ((idIndex 15 i).val &&& 63) ∧ cntW (row (idIndex 15 i)) 1 = pcb ((idIndex 15 i).val &&& 126) ∧ cntW (row (idIndex 15 i)) 2 = pcb ((idIndex 15 i).val &&& 252) ∧ cntW (row (idIndex 15 i)) 3 = pcb ((idIndex 15 i).val &&& 504) ∧ cntW (row (idIndex 15 i)) 4 = pcb ((idIndex 15 i).val &&& 1008) ∧ cntW (row (idIndex 15 i)) 5 = pcb ((idIndex 15 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_16 : ∀ i : Fin 32, cntW (row (idIndex 16 i)) 0 = pcb ((idIndex 16 i).val &&& 63) ∧ cntW (row (idIndex 16 i)) 1 = pcb ((idIndex 16 i).val &&& 126) ∧ cntW (row (idIndex 16 i)) 2 = pcb ((idIndex 16 i).val &&& 252) ∧ cntW (row (idIndex 16 i)) 3 = pcb ((idIndex 16 i).val &&& 504) ∧ cntW (row (idIndex 16 i)) 4 = pcb ((idIndex 16 i).val &&& 1008) ∧ cntW (row (idIndex 16 i)) 5 = pcb ((idIndex 16 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_17 : ∀ i : Fin 32, cntW (row (idIndex 17 i)) 0 = pcb ((idIndex 17 i).val &&& 63) ∧ cntW (row (idIndex 17 i)) 1 = pcb ((idIndex 17 i).val &&& 126) ∧ cntW (row (idIndex 17 i)) 2 = pcb ((idIndex 17 i).val &&& 252) ∧ cntW (row (idIndex 17 i)) 3 = pcb ((idIndex 17 i).val &&& 504) ∧ cntW (row (idIndex 17 i)) 4 = pcb ((idIndex 17 i).val &&& 1008) ∧ cntW (row (idIndex 17 i)) 5 = pcb ((idIndex 17 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_18 : ∀ i : Fin 32, cntW (row (idIndex 18 i)) 0 = pcb ((idIndex 18 i).val &&& 63) ∧ cntW (row (idIndex 18 i)) 1 = pcb ((idIndex 18 i).val &&& 126) ∧ cntW (row (idIndex 18 i)) 2 = pcb ((idIndex 18 i).val &&& 252) ∧ cntW (row (idIndex 18 i)) 3 = pcb ((idIndex 18 i).val &&& 504) ∧ cntW (row (idIndex 18 i)) 4 = pcb ((idIndex 18 i).val &&& 1008) ∧ cntW (row (idIndex 18 i)) 5 = pcb ((idIndex 18 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_19 : ∀ i : Fin 32, cntW (row (idIndex 19 i)) 0 = pcb ((idIndex 19 i).val &&& 63) ∧ cntW (row (idIndex 19 i)) 1 = pcb ((idIndex 19 i).val &&& 126) ∧ cntW (row (idIndex 19 i)) 2 = pcb ((idIndex 19 i).val &&& 252) ∧ cntW (row (idIndex 19 i)) 3 = pcb ((idIndex 19 i).val &&& 504) ∧ cntW (row (idIndex 19 i)) 4 = pcb ((idIndex 19 i).val &&& 1008) ∧ cntW (row (idIndex 19 i)) 5 = pcb ((idIndex 19 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_20 : ∀ i : Fin 32, cntW (row (idIndex 20 i)) 0 = pcb ((idIndex 20 i).val &&& 63) ∧ cntW (row (idIndex 20 i)) 1 = pcb ((idIndex 20 i).val &&& 126) ∧ cntW (row (idIndex 20 i)) 2 = pcb ((idIndex 20 i).val &&& 252) ∧ cntW (row (idIndex 20 i)) 3 = pcb ((idIndex 20 i).val &&& 504) ∧ cntW (row (idIndex 20 i)) 4 = pcb ((idIndex 20 i).val &&& 1008) ∧ cntW (row (idIndex 20 i)) 5 = pcb ((idIndex 20 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_21 : ∀ i : Fin 32, cntW (row (idIndex 21 i)) 0 = pcb ((idIndex 21 i).val &&& 63) ∧ cntW (row (idIndex 21 i)) 1 = pcb ((idIndex 21 i).val &&& 126) ∧ cntW (row (idIndex 21 i)) 2 = pcb ((idIndex 21 i).val &&& 252) ∧ cntW (row (idIndex 21 i)) 3 = pcb ((idIndex 21 i).val &&& 504) ∧ cntW (row (idIndex 21 i)) 4 = pcb ((idIndex 21 i).val &&& 1008) ∧ cntW (row (idIndex 21 i)) 5 = pcb ((idIndex 21 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_22 : ∀ i : Fin 32, cntW (row (idIndex 22 i)) 0 = pcb ((idIndex 22 i).val &&& 63) ∧ cntW (row (idIndex 22 i)) 1 = pcb ((idIndex 22 i).val &&& 126) ∧ cntW (row (idIndex 22 i)) 2 = pcb ((idIndex 22 i).val &&& 252) ∧ cntW (row (idIndex 22 i)) 3 = pcb ((idIndex 22 i).val &&& 504) ∧ cntW (row (idIndex 22 i)) 4 = pcb ((idIndex 22 i).val &&& 1008) ∧ cntW (row (idIndex 22 i)) 5 = pcb ((idIndex 22 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_23 : ∀ i : Fin 32, cntW (row (idIndex 23 i)) 0 = pcb ((idIndex 23 i).val &&& 63) ∧ cntW (row (idIndex 23 i)) 1 = pcb ((idIndex 23 i).val &&& 126) ∧ cntW (row (idIndex 23 i)) 2 = pcb ((idIndex 23 i).val &&& 252) ∧ cntW (row (idIndex 23 i)) 3 = pcb ((idIndex 23 i).val &&& 504) ∧ cntW (row (idIndex 23 i)) 4 = pcb ((idIndex 23 i).val &&& 1008) ∧ cntW (row (idIndex 23 i)) 5 = pcb ((idIndex 23 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_24 : ∀ i : Fin 32, cntW (row (idIndex 24 i)) 0 = pcb ((idIndex 24 i).val &&& 63) ∧ cntW (row (idIndex 24 i)) 1 = pcb ((idIndex 24 i).val &&& 126) ∧ cntW (row (idIndex 24 i)) 2 = pcb ((idIndex 24 i).val &&& 252) ∧ cntW (row (idIndex 24 i)) 3 = pcb ((idIndex 24 i).val &&& 504) ∧ cntW (row (idIndex 24 i)) 4 = pcb ((idIndex 24 i).val &&& 1008) ∧ cntW (row (idIndex 24 i)) 5 = pcb ((idIndex 24 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_25 : ∀ i : Fin 32, cntW (row (idIndex 25 i)) 0 = pcb ((idIndex 25 i).val &&& 63) ∧ cntW (row (idIndex 25 i)) 1 = pcb ((idIndex 25 i).val &&& 126) ∧ cntW (row (idIndex 25 i)) 2 = pcb ((idIndex 25 i).val &&& 252) ∧ cntW (row (idIndex 25 i)) 3 = pcb ((idIndex 25 i).val &&& 504) ∧ cntW (row (idIndex 25 i)) 4 = pcb ((idIndex 25 i).val &&& 1008) ∧ cntW (row (idIndex 25 i)) 5 = pcb ((idIndex 25 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_26 : ∀ i : Fin 32, cntW (row (idIndex 26 i)) 0 = pcb ((idIndex 26 i).val &&& 63) ∧ cntW (row (idIndex 26 i)) 1 = pcb ((idIndex 26 i).val &&& 126) ∧ cntW (row (idIndex 26 i)) 2 = pcb ((idIndex 26 i).val &&& 252) ∧ cntW (row (idIndex 26 i)) 3 = pcb ((idIndex 26 i).val &&& 504) ∧ cntW (row (idIndex 26 i)) 4 = pcb ((idIndex 26 i).val &&& 1008) ∧ cntW (row (idIndex 26 i)) 5 = pcb ((idIndex 26 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_27 : ∀ i : Fin 32, cntW (row (idIndex 27 i)) 0 = pcb ((idIndex 27 i).val &&& 63) ∧ cntW (row (idIndex 27 i)) 1 = pcb ((idIndex 27 i).val &&& 126) ∧ cntW (row (idIndex 27 i)) 2 = pcb ((idIndex 27 i).val &&& 252) ∧ cntW (row (idIndex 27 i)) 3 = pcb ((idIndex 27 i).val &&& 504) ∧ cntW (row (idIndex 27 i)) 4 = pcb ((idIndex 27 i).val &&& 1008) ∧ cntW (row (idIndex 27 i)) 5 = pcb ((idIndex 27 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_28 : ∀ i : Fin 32, cntW (row (idIndex 28 i)) 0 = pcb ((idIndex 28 i).val &&& 63) ∧ cntW (row (idIndex 28 i)) 1 = pcb ((idIndex 28 i).val &&& 126) ∧ cntW (row (idIndex 28 i)) 2 = pcb ((idIndex 28 i).val &&& 252) ∧ cntW (row (idIndex 28 i)) 3 = pcb ((idIndex 28 i).val &&& 504) ∧ cntW (row (idIndex 28 i)) 4 = pcb ((idIndex 28 i).val &&& 1008) ∧ cntW (row (idIndex 28 i)) 5 = pcb ((idIndex 28 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_29 : ∀ i : Fin 32, cntW (row (idIndex 29 i)) 0 = pcb ((idIndex 29 i).val &&& 63) ∧ cntW (row (idIndex 29 i)) 1 = pcb ((idIndex 29 i).val &&& 126) ∧ cntW (row (idIndex 29 i)) 2 = pcb ((idIndex 29 i).val &&& 252) ∧ cntW (row (idIndex 29 i)) 3 = pcb ((idIndex 29 i).val &&& 504) ∧ cntW (row (idIndex 29 i)) 4 = pcb ((idIndex 29 i).val &&& 1008) ∧ cntW (row (idIndex 29 i)) 5 = pcb ((idIndex 29 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_30 : ∀ i : Fin 32, cntW (row (idIndex 30 i)) 0 = pcb ((idIndex 30 i).val &&& 63) ∧ cntW (row (idIndex 30 i)) 1 = pcb ((idIndex 30 i).val &&& 126) ∧ cntW (row (idIndex 30 i)) 2 = pcb ((idIndex 30 i).val &&& 252) ∧ cntW (row (idIndex 30 i)) 3 = pcb ((idIndex 30 i).val &&& 504) ∧ cntW (row (idIndex 30 i)) 4 = pcb ((idIndex 30 i).val &&& 1008) ∧ cntW (row (idIndex 30 i)) 5 = pcb ((idIndex 30 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_31 : ∀ i : Fin 32, cntW (row (idIndex 31 i)) 0 = pcb ((idIndex 31 i).val &&& 63) ∧ cntW (row (idIndex 31 i)) 1 = pcb ((idIndex 31 i).val &&& 126) ∧ cntW (row (idIndex 31 i)) 2 = pcb ((idIndex 31 i).val &&& 252) ∧ cntW (row (idIndex 31 i)) 3 = pcb ((idIndex 31 i).val &&& 504) ∧ cntW (row (idIndex 31 i)) 4 = pcb ((idIndex 31 i).val &&& 1008) ∧ cntW (row (idIndex 31 i)) 5 = pcb ((idIndex 31 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_32 : ∀ i : Fin 32, cntW (row (idIndex 32 i)) 0 = pcb ((idIndex 32 i).val &&& 63) ∧ cntW (row (idIndex 32 i)) 1 = pcb ((idIndex 32 i).val &&& 126) ∧ cntW (row (idIndex 32 i)) 2 = pcb ((idIndex 32 i).val &&& 252) ∧ cntW (row (idIndex 32 i)) 3 = pcb ((idIndex 32 i).val &&& 504) ∧ cntW (row (idIndex 32 i)) 4 = pcb ((idIndex 32 i).val &&& 1008) ∧ cntW (row (idIndex 32 i)) 5 = pcb ((idIndex 32 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_33 : ∀ i : Fin 32, cntW (row (idIndex 33 i)) 0 = pcb ((idIndex 33 i).val &&& 63) ∧ cntW (row (idIndex 33 i)) 1 = pcb ((idIndex 33 i).val &&& 126) ∧ cntW (row (idIndex 33 i)) 2 = pcb ((idIndex 33 i).val &&& 252) ∧ cntW (row (idIndex 33 i)) 3 = pcb ((idIndex 33 i).val &&& 504) ∧ cntW (row (idIndex 33 i)) 4 = pcb ((idIndex 33 i).val &&& 1008) ∧ cntW (row (idIndex 33 i)) 5 = pcb ((idIndex 33 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_34 : ∀ i : Fin 32, cntW (row (idIndex 34 i)) 0 = pcb ((idIndex 34 i).val &&& 63) ∧ cntW (row (idIndex 34 i)) 1 = pcb ((idIndex 34 i).val &&& 126) ∧ cntW (row (idIndex 34 i)) 2 = pcb ((idIndex 34 i).val &&& 252) ∧ cntW (row (idIndex 34 i)) 3 = pcb ((idIndex 34 i).val &&& 504) ∧ cntW (row (idIndex 34 i)) 4 = pcb ((idIndex 34 i).val &&& 1008) ∧ cntW (row (idIndex 34 i)) 5 = pcb ((idIndex 34 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_35 : ∀ i : Fin 32, cntW (row (idIndex 35 i)) 0 = pcb ((idIndex 35 i).val &&& 63) ∧ cntW (row (idIndex 35 i)) 1 = pcb ((idIndex 35 i).val &&& 126) ∧ cntW (row (idIndex 35 i)) 2 = pcb ((idIndex 35 i).val &&& 252) ∧ cntW (row (idIndex 35 i)) 3 = pcb ((idIndex 35 i).val &&& 504) ∧ cntW (row (idIndex 35 i)) 4 = pcb ((idIndex 35 i).val &&& 1008) ∧ cntW (row (idIndex 35 i)) 5 = pcb ((idIndex 35 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_36 : ∀ i : Fin 32, cntW (row (idIndex 36 i)) 0 = pcb ((idIndex 36 i).val &&& 63) ∧ cntW (row (idIndex 36 i)) 1 = pcb ((idIndex 36 i).val &&& 126) ∧ cntW (row (idIndex 36 i)) 2 = pcb ((idIndex 36 i).val &&& 252) ∧ cntW (row (idIndex 36 i)) 3 = pcb ((idIndex 36 i).val &&& 504) ∧ cntW (row (idIndex 36 i)) 4 = pcb ((idIndex 36 i).val &&& 1008) ∧ cntW (row (idIndex 36 i)) 5 = pcb ((idIndex 36 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_37 : ∀ i : Fin 32, cntW (row (idIndex 37 i)) 0 = pcb ((idIndex 37 i).val &&& 63) ∧ cntW (row (idIndex 37 i)) 1 = pcb ((idIndex 37 i).val &&& 126) ∧ cntW (row (idIndex 37 i)) 2 = pcb ((idIndex 37 i).val &&& 252) ∧ cntW (row (idIndex 37 i)) 3 = pcb ((idIndex 37 i).val &&& 504) ∧ cntW (row (idIndex 37 i)) 4 = pcb ((idIndex 37 i).val &&& 1008) ∧ cntW (row (idIndex 37 i)) 5 = pcb ((idIndex 37 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_38 : ∀ i : Fin 32, cntW (row (idIndex 38 i)) 0 = pcb ((idIndex 38 i).val &&& 63) ∧ cntW (row (idIndex 38 i)) 1 = pcb ((idIndex 38 i).val &&& 126) ∧ cntW (row (idIndex 38 i)) 2 = pcb ((idIndex 38 i).val &&& 252) ∧ cntW (row (idIndex 38 i)) 3 = pcb ((idIndex 38 i).val &&& 504) ∧ cntW (row (idIndex 38 i)) 4 = pcb ((idIndex 38 i).val &&& 1008) ∧ cntW (row (idIndex 38 i)) 5 = pcb ((idIndex 38 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_39 : ∀ i : Fin 32, cntW (row (idIndex 39 i)) 0 = pcb ((idIndex 39 i).val &&& 63) ∧ cntW (row (idIndex 39 i)) 1 = pcb ((idIndex 39 i).val &&& 126) ∧ cntW (row (idIndex 39 i)) 2 = pcb ((idIndex 39 i).val &&& 252) ∧ cntW (row (idIndex 39 i)) 3 = pcb ((idIndex 39 i).val &&& 504) ∧ cntW (row (idIndex 39 i)) 4 = pcb ((idIndex 39 i).val &&& 1008) ∧ cntW (row (idIndex 39 i)) 5 = pcb ((idIndex 39 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_40 : ∀ i : Fin 32, cntW (row (idIndex 40 i)) 0 = pcb ((idIndex 40 i).val &&& 63) ∧ cntW (row (idIndex 40 i)) 1 = pcb ((idIndex 40 i).val &&& 126) ∧ cntW (row (idIndex 40 i)) 2 = pcb ((idIndex 40 i).val &&& 252) ∧ cntW (row (idIndex 40 i)) 3 = pcb ((idIndex 40 i).val &&& 504) ∧ cntW (row (idIndex 40 i)) 4 = pcb ((idIndex 40 i).val &&& 1008) ∧ cntW (row (idIndex 40 i)) 5 = pcb ((idIndex 40 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_41 : ∀ i : Fin 32, cntW (row (idIndex 41 i)) 0 = pcb ((idIndex 41 i).val &&& 63) ∧ cntW (row (idIndex 41 i)) 1 = pcb ((idIndex 41 i).val &&& 126) ∧ cntW (row (idIndex 41 i)) 2 = pcb ((idIndex 41 i).val &&& 252) ∧ cntW (row (idIndex 41 i)) 3 = pcb ((idIndex 41 i).val &&& 504) ∧ cntW (row (idIndex 41 i)) 4 = pcb ((idIndex 41 i).val &&& 1008) ∧ cntW (row (idIndex 41 i)) 5 = pcb ((idIndex 41 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_42 : ∀ i : Fin 32, cntW (row (idIndex 42 i)) 0 = pcb ((idIndex 42 i).val &&& 63) ∧ cntW (row (idIndex 42 i)) 1 = pcb ((idIndex 42 i).val &&& 126) ∧ cntW (row (idIndex 42 i)) 2 = pcb ((idIndex 42 i).val &&& 252) ∧ cntW (row (idIndex 42 i)) 3 = pcb ((idIndex 42 i).val &&& 504) ∧ cntW (row (idIndex 42 i)) 4 = pcb ((idIndex 42 i).val &&& 1008) ∧ cntW (row (idIndex 42 i)) 5 = pcb ((idIndex 42 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_43 : ∀ i : Fin 32, cntW (row (idIndex 43 i)) 0 = pcb ((idIndex 43 i).val &&& 63) ∧ cntW (row (idIndex 43 i)) 1 = pcb ((idIndex 43 i).val &&& 126) ∧ cntW (row (idIndex 43 i)) 2 = pcb ((idIndex 43 i).val &&& 252) ∧ cntW (row (idIndex 43 i)) 3 = pcb ((idIndex 43 i).val &&& 504) ∧ cntW (row (idIndex 43 i)) 4 = pcb ((idIndex 43 i).val &&& 1008) ∧ cntW (row (idIndex 43 i)) 5 = pcb ((idIndex 43 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_44 : ∀ i : Fin 32, cntW (row (idIndex 44 i)) 0 = pcb ((idIndex 44 i).val &&& 63) ∧ cntW (row (idIndex 44 i)) 1 = pcb ((idIndex 44 i).val &&& 126) ∧ cntW (row (idIndex 44 i)) 2 = pcb ((idIndex 44 i).val &&& 252) ∧ cntW (row (idIndex 44 i)) 3 = pcb ((idIndex 44 i).val &&& 504) ∧ cntW (row (idIndex 44 i)) 4 = pcb ((idIndex 44 i).val &&& 1008) ∧ cntW (row (idIndex 44 i)) 5 = pcb ((idIndex 44 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_45 : ∀ i : Fin 32, cntW (row (idIndex 45 i)) 0 = pcb ((idIndex 45 i).val &&& 63) ∧ cntW (row (idIndex 45 i)) 1 = pcb ((idIndex 45 i).val &&& 126) ∧ cntW (row (idIndex 45 i)) 2 = pcb ((idIndex 45 i).val &&& 252) ∧ cntW (row (idIndex 45 i)) 3 = pcb ((idIndex 45 i).val &&& 504) ∧ cntW (row (idIndex 45 i)) 4 = pcb ((idIndex 45 i).val &&& 1008) ∧ cntW (row (idIndex 45 i)) 5 = pcb ((idIndex 45 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_46 : ∀ i : Fin 32, cntW (row (idIndex 46 i)) 0 = pcb ((idIndex 46 i).val &&& 63) ∧ cntW (row (idIndex 46 i)) 1 = pcb ((idIndex 46 i).val &&& 126) ∧ cntW (row (idIndex 46 i)) 2 = pcb ((idIndex 46 i).val &&& 252) ∧ cntW (row (idIndex 46 i)) 3 = pcb ((idIndex 46 i).val &&& 504) ∧ cntW (row (idIndex 46 i)) 4 = pcb ((idIndex 46 i).val &&& 1008) ∧ cntW (row (idIndex 46 i)) 5 = pcb ((idIndex 46 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_47 : ∀ i : Fin 32, cntW (row (idIndex 47 i)) 0 = pcb ((idIndex 47 i).val &&& 63) ∧ cntW (row (idIndex 47 i)) 1 = pcb ((idIndex 47 i).val &&& 126) ∧ cntW (row (idIndex 47 i)) 2 = pcb ((idIndex 47 i).val &&& 252) ∧ cntW (row (idIndex 47 i)) 3 = pcb ((idIndex 47 i).val &&& 504) ∧ cntW (row (idIndex 47 i)) 4 = pcb ((idIndex 47 i).val &&& 1008) ∧ cntW (row (idIndex 47 i)) 5 = pcb ((idIndex 47 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_48 : ∀ i : Fin 32, cntW (row (idIndex 48 i)) 0 = pcb ((idIndex 48 i).val &&& 63) ∧ cntW (row (idIndex 48 i)) 1 = pcb ((idIndex 48 i).val &&& 126) ∧ cntW (row (idIndex 48 i)) 2 = pcb ((idIndex 48 i).val &&& 252) ∧ cntW (row (idIndex 48 i)) 3 = pcb ((idIndex 48 i).val &&& 504) ∧ cntW (row (idIndex 48 i)) 4 = pcb ((idIndex 48 i).val &&& 1008) ∧ cntW (row (idIndex 48 i)) 5 = pcb ((idIndex 48 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_49 : ∀ i : Fin 32, cntW (row (idIndex 49 i)) 0 = pcb ((idIndex 49 i).val &&& 63) ∧ cntW (row (idIndex 49 i)) 1 = pcb ((idIndex 49 i).val &&& 126) ∧ cntW (row (idIndex 49 i)) 2 = pcb ((idIndex 49 i).val &&& 252) ∧ cntW (row (idIndex 49 i)) 3 = pcb ((idIndex 49 i).val &&& 504) ∧ cntW (row (idIndex 49 i)) 4 = pcb ((idIndex 49 i).val &&& 1008) ∧ cntW (row (idIndex 49 i)) 5 = pcb ((idIndex 49 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_50 : ∀ i : Fin 32, cntW (row (idIndex 50 i)) 0 = pcb ((idIndex 50 i).val &&& 63) ∧ cntW (row (idIndex 50 i)) 1 = pcb ((idIndex 50 i).val &&& 126) ∧ cntW (row (idIndex 50 i)) 2 = pcb ((idIndex 50 i).val &&& 252) ∧ cntW (row (idIndex 50 i)) 3 = pcb ((idIndex 50 i).val &&& 504) ∧ cntW (row (idIndex 50 i)) 4 = pcb ((idIndex 50 i).val &&& 1008) ∧ cntW (row (idIndex 50 i)) 5 = pcb ((idIndex 50 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_51 : ∀ i : Fin 32, cntW (row (idIndex 51 i)) 0 = pcb ((idIndex 51 i).val &&& 63) ∧ cntW (row (idIndex 51 i)) 1 = pcb ((idIndex 51 i).val &&& 126) ∧ cntW (row (idIndex 51 i)) 2 = pcb ((idIndex 51 i).val &&& 252) ∧ cntW (row (idIndex 51 i)) 3 = pcb ((idIndex 51 i).val &&& 504) ∧ cntW (row (idIndex 51 i)) 4 = pcb ((idIndex 51 i).val &&& 1008) ∧ cntW (row (idIndex 51 i)) 5 = pcb ((idIndex 51 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_52 : ∀ i : Fin 32, cntW (row (idIndex 52 i)) 0 = pcb ((idIndex 52 i).val &&& 63) ∧ cntW (row (idIndex 52 i)) 1 = pcb ((idIndex 52 i).val &&& 126) ∧ cntW (row (idIndex 52 i)) 2 = pcb ((idIndex 52 i).val &&& 252) ∧ cntW (row (idIndex 52 i)) 3 = pcb ((idIndex 52 i).val &&& 504) ∧ cntW (row (idIndex 52 i)) 4 = pcb ((idIndex 52 i).val &&& 1008) ∧ cntW (row (idIndex 52 i)) 5 = pcb ((idIndex 52 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_53 : ∀ i : Fin 32, cntW (row (idIndex 53 i)) 0 = pcb ((idIndex 53 i).val &&& 63) ∧ cntW (row (idIndex 53 i)) 1 = pcb ((idIndex 53 i).val &&& 126) ∧ cntW (row (idIndex 53 i)) 2 = pcb ((idIndex 53 i).val &&& 252) ∧ cntW (row (idIndex 53 i)) 3 = pcb ((idIndex 53 i).val &&& 504) ∧ cntW (row (idIndex 53 i)) 4 = pcb ((idIndex 53 i).val &&& 1008) ∧ cntW (row (idIndex 53 i)) 5 = pcb ((idIndex 53 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_54 : ∀ i : Fin 32, cntW (row (idIndex 54 i)) 0 = pcb ((idIndex 54 i).val &&& 63) ∧ cntW (row (idIndex 54 i)) 1 = pcb ((idIndex 54 i).val &&& 126) ∧ cntW (row (idIndex 54 i)) 2 = pcb ((idIndex 54 i).val &&& 252) ∧ cntW (row (idIndex 54 i)) 3 = pcb ((idIndex 54 i).val &&& 504) ∧ cntW (row (idIndex 54 i)) 4 = pcb ((idIndex 54 i).val &&& 1008) ∧ cntW (row (idIndex 54 i)) 5 = pcb ((idIndex 54 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_55 : ∀ i : Fin 32, cntW (row (idIndex 55 i)) 0 = pcb ((idIndex 55 i).val &&& 63) ∧ cntW (row (idIndex 55 i)) 1 = pcb ((idIndex 55 i).val &&& 126) ∧ cntW (row (idIndex 55 i)) 2 = pcb ((idIndex 55 i).val &&& 252) ∧ cntW (row (idIndex 55 i)) 3 = pcb ((idIndex 55 i).val &&& 504) ∧ cntW (row (idIndex 55 i)) 4 = pcb ((idIndex 55 i).val &&& 1008) ∧ cntW (row (idIndex 55 i)) 5 = pcb ((idIndex 55 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_56 : ∀ i : Fin 32, cntW (row (idIndex 56 i)) 0 = pcb ((idIndex 56 i).val &&& 63) ∧ cntW (row (idIndex 56 i)) 1 = pcb ((idIndex 56 i).val &&& 126) ∧ cntW (row (idIndex 56 i)) 2 = pcb ((idIndex 56 i).val &&& 252) ∧ cntW (row (idIndex 56 i)) 3 = pcb ((idIndex 56 i).val &&& 504) ∧ cntW (row (idIndex 56 i)) 4 = pcb ((idIndex 56 i).val &&& 1008) ∧ cntW (row (idIndex 56 i)) 5 = pcb ((idIndex 56 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_57 : ∀ i : Fin 32, cntW (row (idIndex 57 i)) 0 = pcb ((idIndex 57 i).val &&& 63) ∧ cntW (row (idIndex 57 i)) 1 = pcb ((idIndex 57 i).val &&& 126) ∧ cntW (row (idIndex 57 i)) 2 = pcb ((idIndex 57 i).val &&& 252) ∧ cntW (row (idIndex 57 i)) 3 = pcb ((idIndex 57 i).val &&& 504) ∧ cntW (row (idIndex 57 i)) 4 = pcb ((idIndex 57 i).val &&& 1008) ∧ cntW (row (idIndex 57 i)) 5 = pcb ((idIndex 57 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_58 : ∀ i : Fin 32, cntW (row (idIndex 58 i)) 0 = pcb ((idIndex 58 i).val &&& 63) ∧ cntW (row (idIndex 58 i)) 1 = pcb ((idIndex 58 i).val &&& 126) ∧ cntW (row (idIndex 58 i)) 2 = pcb ((idIndex 58 i).val &&& 252) ∧ cntW (row (idIndex 58 i)) 3 = pcb ((idIndex 58 i).val &&& 504) ∧ cntW (row (idIndex 58 i)) 4 = pcb ((idIndex 58 i).val &&& 1008) ∧ cntW (row (idIndex 58 i)) 5 = pcb ((idIndex 58 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_59 : ∀ i : Fin 32, cntW (row (idIndex 59 i)) 0 = pcb ((idIndex 59 i).val &&& 63) ∧ cntW (row (idIndex 59 i)) 1 = pcb ((idIndex 59 i).val &&& 126) ∧ cntW (row (idIndex 59 i)) 2 = pcb ((idIndex 59 i).val &&& 252) ∧ cntW (row (idIndex 59 i)) 3 = pcb ((idIndex 59 i).val &&& 504) ∧ cntW (row (idIndex 59 i)) 4 = pcb ((idIndex 59 i).val &&& 1008) ∧ cntW (row (idIndex 59 i)) 5 = pcb ((idIndex 59 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_60 : ∀ i : Fin 32, cntW (row (idIndex 60 i)) 0 = pcb ((idIndex 60 i).val &&& 63) ∧ cntW (row (idIndex 60 i)) 1 = pcb ((idIndex 60 i).val &&& 126) ∧ cntW (row (idIndex 60 i)) 2 = pcb ((idIndex 60 i).val &&& 252) ∧ cntW (row (idIndex 60 i)) 3 = pcb ((idIndex 60 i).val &&& 504) ∧ cntW (row (idIndex 60 i)) 4 = pcb ((idIndex 60 i).val &&& 1008) ∧ cntW (row (idIndex 60 i)) 5 = pcb ((idIndex 60 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_61 : ∀ i : Fin 32, cntW (row (idIndex 61 i)) 0 = pcb ((idIndex 61 i).val &&& 63) ∧ cntW (row (idIndex 61 i)) 1 = pcb ((idIndex 61 i).val &&& 126) ∧ cntW (row (idIndex 61 i)) 2 = pcb ((idIndex 61 i).val &&& 252) ∧ cntW (row (idIndex 61 i)) 3 = pcb ((idIndex 61 i).val &&& 504) ∧ cntW (row (idIndex 61 i)) 4 = pcb ((idIndex 61 i).val &&& 1008) ∧ cntW (row (idIndex 61 i)) 5 = pcb ((idIndex 61 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_62 : ∀ i : Fin 32, cntW (row (idIndex 62 i)) 0 = pcb ((idIndex 62 i).val &&& 63) ∧ cntW (row (idIndex 62 i)) 1 = pcb ((idIndex 62 i).val &&& 126) ∧ cntW (row (idIndex 62 i)) 2 = pcb ((idIndex 62 i).val &&& 252) ∧ cntW (row (idIndex 62 i)) 3 = pcb ((idIndex 62 i).val &&& 504) ∧ cntW (row (idIndex 62 i)) 4 = pcb ((idIndex 62 i).val &&& 1008) ∧ cntW (row (idIndex 62 i)) 5 = pcb ((idIndex 62 i).val &&& 2016) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev cnt_row_chunk_63 : ∀ i : Fin 32, cntW (row (idIndex 63 i)) 0 = pcb ((idIndex 63 i).val &&& 63) ∧ cntW (row (idIndex 63 i)) 1 = pcb ((idIndex 63 i).val &&& 126) ∧ cntW (row (idIndex 63 i)) 2 = pcb ((idIndex 63 i).val &&& 252) ∧ cntW (row (idIndex 63 i)) 3 = pcb ((idIndex 63 i).val &&& 504) ∧ cntW (row (idIndex 63 i)) 4 = pcb ((idIndex 63 i).val &&& 1008) ∧ cntW (row (idIndex 63 i)) 5 = pcb ((idIndex 63 i).val &&& 2016) := by
  decide +kernel

theorem cnt_row (u : Fin 2048) : cntW (row u) 0 = pcb (u.val &&& 63) ∧ cntW (row u) 1 = pcb (u.val &&& 126) ∧ cntW (row u) 2 = pcb (u.val &&& 252) ∧ cntW (row u) 3 = pcb (u.val &&& 504) ∧ cntW (row u) 4 = pcb (u.val &&& 1008) ∧ cntW (row u) 5 = pcb (u.val &&& 2016) := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, cntW (row (idIndex k i)) 0 = pcb ((idIndex k i).val &&& 63) ∧ cntW (row (idIndex k i)) 1 = pcb ((idIndex k i).val &&& 126) ∧ cntW (row (idIndex k i)) 2 = pcb ((idIndex k i).val &&& 252) ∧ cntW (row (idIndex k i)) 3 = pcb ((idIndex k i).val &&& 504) ∧ cntW (row (idIndex k i)) 4 = pcb ((idIndex k i).val &&& 1008) ∧ cntW (row (idIndex k i)) 5 = pcb ((idIndex k i).val &&& 2016) := by
    intro k
    fin_cases k
    · exact cnt_row_chunk_0
    · exact cnt_row_chunk_1
    · exact cnt_row_chunk_2
    · exact cnt_row_chunk_3
    · exact cnt_row_chunk_4
    · exact cnt_row_chunk_5
    · exact cnt_row_chunk_6
    · exact cnt_row_chunk_7
    · exact cnt_row_chunk_8
    · exact cnt_row_chunk_9
    · exact cnt_row_chunk_10
    · exact cnt_row_chunk_11
    · exact cnt_row_chunk_12
    · exact cnt_row_chunk_13
    · exact cnt_row_chunk_14
    · exact cnt_row_chunk_15
    · exact cnt_row_chunk_16
    · exact cnt_row_chunk_17
    · exact cnt_row_chunk_18
    · exact cnt_row_chunk_19
    · exact cnt_row_chunk_20
    · exact cnt_row_chunk_21
    · exact cnt_row_chunk_22
    · exact cnt_row_chunk_23
    · exact cnt_row_chunk_24
    · exact cnt_row_chunk_25
    · exact cnt_row_chunk_26
    · exact cnt_row_chunk_27
    · exact cnt_row_chunk_28
    · exact cnt_row_chunk_29
    · exact cnt_row_chunk_30
    · exact cnt_row_chunk_31
    · exact cnt_row_chunk_32
    · exact cnt_row_chunk_33
    · exact cnt_row_chunk_34
    · exact cnt_row_chunk_35
    · exact cnt_row_chunk_36
    · exact cnt_row_chunk_37
    · exact cnt_row_chunk_38
    · exact cnt_row_chunk_39
    · exact cnt_row_chunk_40
    · exact cnt_row_chunk_41
    · exact cnt_row_chunk_42
    · exact cnt_row_chunk_43
    · exact cnt_row_chunk_44
    · exact cnt_row_chunk_45
    · exact cnt_row_chunk_46
    · exact cnt_row_chunk_47
    · exact cnt_row_chunk_48
    · exact cnt_row_chunk_49
    · exact cnt_row_chunk_50
    · exact cnt_row_chunk_51
    · exact cnt_row_chunk_52
    · exact cnt_row_chunk_53
    · exact cnt_row_chunk_54
    · exact cnt_row_chunk_55
    · exact cnt_row_chunk_56
    · exact cnt_row_chunk_57
    · exact cnt_row_chunk_58
    · exact cnt_row_chunk_59
    · exact cnt_row_chunk_60
    · exact cnt_row_chunk_61
    · exact cnt_row_chunk_62
    · exact cnt_row_chunk_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

/-- Compatibility on bit codes, enforcing all six windows. -/
def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 63) ≤ 1 ∧ 3 ≤ pcb (t &&& 63)) ∧
    ¬ (pcb (s &&& 126) ≤ 1 ∧ 3 ≤ pcb (t &&& 126)) ∧
    ¬ (pcb (s &&& 252) ≤ 1 ∧ 3 ≤ pcb (t &&& 252)) ∧
    ¬ (pcb (s &&& 504) ≤ 1 ∧ 3 ≤ pcb (t &&& 504)) ∧
    ¬ (pcb (s &&& 1008) ≤ 1 ∧ 3 ≤ pcb (t &&& 1008)) ∧
    ¬ (pcb (s &&& 2016) ≤ 1 ∧ 3 ≤ pcb (t &&& 2016)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (6 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num), h 5 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 2048) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5]

theorem sub_iff (w u : Fin 2048) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 11
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (2048 : ℕ) ≤ 2 ^ i := by
          calc (2048 : ℕ) = 2 ^ 11 := by norm_num
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
def subs (u : Fin 2048) : Finset (Fin 2048) :=
  univ.filter (fun w : Fin 2048 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 2048 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 2048, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 2047 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 2047 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 11 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 2047 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 2047)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 2047 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 2047 := by
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

theorem G_succ (n : ℕ) (u : Fin 2048) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 := rfl

/-- Packed state vectors, certified by the chain recursion, with the per-table entry width in the low six bits. -/
def tb (T w : ℕ) : ℕ := (T >>> (6 + (T % 64) * w)) % 2 ^ (T % 64)

def tabT : ℕ → ℕ
  | 0 => 0x45C5DFC00000000000000000000000000000000000000000000000000000000005C5DFC000000000000000000000000001C1DFC00000000000C0CFC0004045C045C5DFC0000000000000000000000000000000000000000000000000000000000005DFC00000000000000000000000000001DFC0000000000000CFC0000045C045C5DFC000000000000000000000000000001FC00000000000000FC0000005C005C5DFC000000000000003C0000001C001C1DFC0000000C000C0CFC0004045C045C5DFC1
  | 1 => 0x1EA5194630D4630CC318D4630CC318CC318C6330D4630CC318CC318C6330CC318C6330C6330D8630D4A318C618CC618C6318CC618C6318C6318CA630CC618C6318C6318CA630C6318CA630D2C6198630D46518C330CC330C6118CC330C6118C6118C6330CC330C6118C6118C6330C6118C6330CA56198630CC63186318C6318C6318C6318C6318CA5298A630C6318C6318CA5298A630D294B12C6192C6198630D4630D4630CC3184C318CC3184C318C610846330CC3184C318C610846330C610846330C6330D8630CC618CC618C630846318C630846318C6318CA630C630846318C6318CA630CA52952C6192C6198630CC330CC330C611846118C611846118C6118C6330C611846118C6118C6330CA1294A5618A56198630C6318C6318C6318C6318CA5294A5298A5298A630D8C6318C6418C641908218C6419082190822084114630CC31854630CC318CC318461084C318C6330CC318461084C318C6330C61084211046330D8630CC618C63084C618C6318C63084210846318CA630C63084210846318CA630C6318CA630D2C6198630CC330C61184C330C6118C61184200846118C6330C61184200846118C6330C6118C6330CA56198630C6318C210846318C6318C6318C6318CA5298A630CC6318C63198C641908218C641908219082208410C3184C3184C3184C318C6108061084610846330C6108061084610846330C610846330C6330D8630C6308463084630846318C630846318C6318CA630CC6108C6318C631990820C63199082190822084106118461184611846118C611846118C6118C6330CC2308C2318C2318C6820C2318C6820C682208410C6318C6318C6318C6320C6318C6320C6320C8410C6318C6320C6320C8410C6320C8410C8411042094630CC3184C3184610854630CC318CC318C6330CC3184610846108421104C318C6330C6330D8630CC618C630846308421084C618C6318C6318CA630C630842108421084221046318CA630D2C6198630CC330C611846118420084C330C6118C6118C6330C611842008420084211046118C6330CA56198630C6318C2108421084210846318C6318CA5298A630C6318C6318CA5298A630D8C641908219082208410C3184C31846108061084C3184C318C610846330C61080610842000021104610846330C6330D8630C63084630842100021084630846318C6318CA630C630846318C6318CA630CC631990821908220841061184611842008020084611846118C6118C6330C611846118C6118C6330CC2318C6820C6822084106318C6318C6318C6318CC6318C6320C6320C8410C6318C6320C6320C8410C6320C8410C841104208C318461080C318461084C318461084C318C6330C6108020000610842110461084211046330D8630C6308421000630842108463084210846318CA630C63084210846318CA630C6318CA630D90822084106118420080611842008461184200846118C6330C61184200846118C6330C6118C6330CC6822084106318C210846318C6318C6318C6318CC6320C84106318C6318CC6320C8410C6320C8410C841104208610806108061080610846108061084610846330C6108061084610846330C610846330C6330E084106308463084630846318C630846318C6318CC8410630846318C6318CC84106318CC8410C8411042086118461184611846118C611846118C6118C63410611846118C6118C634106118C6341063411042086318C6318C6318C631906318C6319063190642086318C631906319064208631906420864208821045
  | 2 => 0x270E7D74150C490F033F1B0046D1843611C604BC7581430A6029D20837D1D584EC7AA1540AF82C47EE1620BA82F43020C5094818D0E63451B6849872213C0A1028C76614A0AC02BC2BC0B4088816C7A21550B282D82E60BF09181842FA0C5097819439609904C80CD2084A51C087387421E409E828C7861F80A882BC2A60B405A016C7C42090AE82D82CE0BF05F81842DE0C5062819421409904C80CC7A22020AC82D42BE0BC05E01802CE0C2061019021009904C80CC2DE0C7063819C22409F04F80D432A0F307981441E6051028806D184384252873871615A0F2028C74E1680FC02BC2A607305A016C78617310482D82CA07A05F81842D207C062819418A06504C80CC76616F10102D42BA07805E01802C207A061019018406404C80CC2CE07B063819C18E06704F80D422208C07981441E6051028806C7EE20910484482CA0B705B81802D20BB05D819017606403200CC2DE0BF05F819C17E06703380D420208C0460144118051028806C2FA0C706381B018E06C03600E022209604B015C12C05702B807432A0E1070821C1C208704380B41C208704380B410E02D016803D0F03531C6853C94A1CE0F2028C71614E0B781D43F00AF05A016C7421560BD81E44120B605F81842CA06E041010418A06504C80CC7221520BA81E04040B505E01802BA06C03F00FC18406404C80CC2BE06B040010018E06704F80D418E06704F80D41E6051028806C7AA1F80BE830C41211205B81802CA0B903E00FC17606403200CC2CE0BB03E810017E06703380D417E06703380D4118051028806C2E60C2041010C18E06C03600E018E06C03600E012C05702B807422409604B01341C208704380B41C208704380B410E02D016803C7581710FC030C3F00C308901802A607D05C80FC17203F03200CC2A607C05D810017604003380D417604003380D40CE035028806C2BC081061010C18404303600E018404303600E00D803802B807421005404B013412C04D04380B412C04D04380B410E02D016803C3020C5062819C18A06703380E018A06703380E00CE03801C007421408C046013411804D02680B411804D02680B409A02D016803C3960F3079821C1E608704381441E6087043814410E051028806C1E6087043814410E051028806C10E051028806C0A201B00D802505432F1AB84C871A1500B181B494A1CE0F2028C3F00AF05A016C7021480AE81A02FA07A04101044120B605F818418A06504C80CC6DA1420AA81982EA07803F00FC4040B505E018018406404C80CC2B206903800E0104042031808418E06704F80D41E6051028806C7561E40AE82CC2F60C503E00FC41211205B818017606403200CC2BA0B703680E00FA042021008417E06703380D4118051028806C2CA0BC03800E8100044022008818E06C03600E012C05702B807418E06C03600E012C05702B80741C208704380B410E02D016803C71815F0F202CC2DE08706280FC3F00C3089018017203F03200CC2A207805B80E00F8028021008417604003380D40CE035028806C2B007B05E00E80FC028022008818404303600E00D803802B807418404303600E00D803802B807412C04D04380B410E02D016803C2EA0BF05F8190104042021008818A06703380E00CE03801C007418A06703380E00CE03801C007411804D02680B409A02D016803C25E09F04F815C13E05702B80B41E6087043814410E051028806C1E6087043814410E051028806C10E051028806C0A201B00D80246C01430B181EC3C80B306280FC3C80B306280FC22406003200CC27A06803E008816E038021008416E03802100840CE035028806C28406A03F008817803A022008817803A02200880D803802B807417803A02200880D803802B80740D803802B807410E02D016803C2BE0B4041010817E064021008817E06402100880CE03801C007417E06402100880CE03801C00740CE03801C007409A02D016803C24609903180CC13E05702B80B413E05702B80B410E051028806C13E05702B80B410E051028806C10E051028806C0A201B00D802429807A05A0108168042032008816804203200880C802201C007416804203200880C802201C00740C802201C007407001D016803C22206304C80CC13203302B80B413203302B80B40AE02D028806C13203302B80B40AE02D028806C0AE02D028806C0A201B00D802425209904C814413205102880B413205102880B40A202D016806C13205102880B40A202D016806C0A202D016806C05A01B00D802413205102880B40A202D016806C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800CFAE30C19784846A61360A1817870814D0AF81AC2E207603D00F494A1CE0F2028C3F00AF05A016C4120B605F818418A06504C80CC68A1330A1017C2A406903500D42DE07603D80F810204203180844040B505E018018406404C80CC18E06704F80D41E6051028806C6FA1CE0A402A42AC0B303400D42E60C303C00F80F8042021008441211205B818017606403200CC17E06703380D4118051028806C2AA0B503480DC0D603A01D00740F604302180880A8033019804418E06C03600E012C05702B80741C208704380B410E02D016803C6C214D0E702A429C07705980D42D008406180F80FA02802100843F00C3089018017203F03200CC17604003380D40CE035028806C29407605A80DC0D801F01D00740F40260218088086022019804418404303600E00D803802B807412C04D04380B410E02D016803C2C40B605B01800DC03801C00740F80400200088080022011004418A06703380E00CE03801C007411804D02680B409A02D016803C18A06703380E00CE03801C007411804D02680B409A02D016803C1E6087043814410E051028806C10E051028806C0A201B00D802467E1360A801C839C0A905980D42B4077043809C18603E02100843C80B306280FC22406003200CC16E03802100840CE035028806C27806903C007C16A03701D00740F001F0140050086022019804417803A02200880D803802B80740D803802B807410E02D016803C2A80AF03D00F816C06001C00740F403F0140050080022011004417E06402100880CE03801C00740CE03801C007409A02D016803C17E06402100880CE03801C00740CE03801C007409A02D016803C13E05702B80B410E051028806C10E051028806C0A201B00D802428607605780F815E03E03000740E602801F805007E014011004416804203200880C802201C00740C802201C007407001D016803C16804203200880C802201C00740C802201C007407001D016803C13203302B80B40AE02D028806C0AE02D028806C0A201B00D802418A06503280D40CA03501A80740CA03501A807406A01D00E803C13205102880B40A202D016806C0A202D016806C05A01B00D802413205102880B40A202D016806C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800C624121099018829E07203D808039C0A905980D418603E021008439C0A905980D418603E021008422406003200CC0CE035028806C24C05F03300540F001F011004416A03701D0074086022019804416A03701D007408602201980440D803802B807410E02D016803C2760A303400D40F203F011004416C06001C0074080022011004416C06001C007408002201100440CE03801C007409A02D016803C16C06001C007408002201100440CE03801C007409A02D016803C0CE03801C007409A02D016803C10E051028806C0A201B00D802425E06B05180D40EA02701F804415E03E030007407E014011004415E03E030007407E01401100440C802201C007407001D016803C15E03E030007407E01401100440C802201C007407001D016803C0C802201C007407001D016803C0AE02D028806C0A201B00D802417A06103080CC08202101080440CA03501A807406A01D00E803C0CA03501A807406A01D00E803C0A202D016806C05A01B00D80240CA03501A807406A01D00E803C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800C23605E036808014603501F804414603501F80440C001D011004414603501F80440C001D01100440C001D011004407001D016803C14603501F80440C001D01100440C001D011004407001D016803C0C001D011004407001D016803C07001D016803C0A201B00D802416205B02080840C203301080440C2033010804406A01D00E803C0C2033010804406A01D00E803C06A01D00E803C05A01B00D80240C2033010804406A01D00E803C06A01D00E803C05A01B00D802406A01D00E803C05A01B00D802405A01B00D8024036009004800C14E03D02D80840B602101980440B6021019804406601100E803C0B6021019804406601100E803C06601100E803C03A00F00D80240B6021019804406601100E803C06601100E803C03A00F00D802406601100E803C03A00F00D802403A00F00D8024036009004800C0C6033019806C06601B00D803C06601B00D803C03600F007802406601B00D803C03600F007802403600F007802401E009004800C06601B00D803C03600F007802403600F007802401E009004800C03600F007802401E009004800C01E009004800C0120030018004D
  | 3 => 0x2097E12F3C272C815BECA16C85B240BCBC05F60A5C785E1C0C49A064C4329681A90036E2024D0A9550604A0C99A067A8344F01B9E039480268835B581C7A03C04028980F6900A8C01C5000E289FCC05ABD0BDC406110313E019E6035740240032EE01AF503896026580E79009EE01AC000D60346C81BCF03A8E027B80F3580A7301C5000E280F9F00AC201D8000EC009F0004F8009F0004F8A955075800C20E085E43202822FE034940240033A38244F0375A026580DF9009EE013DC00D6035220256E0391E027B80EA880A73014E600E280EFA00AC20158400EC006A7804F8009F0004F8346C825080387C027680E7080A55014AA00E080EDC80AB70156E00EBC06AC8050000A00005000F5800B160162C00F4807008054000A8000540095A0072000E40007200390001C800390001C8A5C78617C0EB00085E4310601C0D045FC02400325101D070489E026580DE20077F013DC00D6033A381DD504ADC027B80E7A007DA014E600E280E9D807F30158400EC00561003B0009F0004F832EE01D8204A10027680E3D007BD014AA00E080E7B007E90156E00EBC055B803AF00A00005000EDC808190162C00F48058B003D200A800054006F1004C100E40007200390001C800390001C835B58256E04ADC034E00E6B00A0E0141C00E080E9D80A4D0149A00EBC0526803AF0075E005000EFA00A9A0153400F48054D003D2007A4005400685004C100982007200260801C800390001C80F9F00B160162C01008058B00402008040058806F10051500A2A007A0028A801E8003D0001E8095A006E400DC800A800372002A000540002A00372002A000540002A00150000A800150000A8A16C85D120C4B806CF83AC002179045FC02400310601B4803B1601DEC122780996013DC00D60320281BD803CB201EC812B7009EE014E600E280E6B007380109000B200561003B0009F0004F8313E01B7903BD801E641284009DA014AA00E080E3D007250105600AFC055B803AF00A00005000E7080733010B200B34058B003D200A8000540058B003D200A80005400390001C800390001C8344F0244F03CEA02A0C12B700D380141C00E080E7A00A2200FFE00AFC0526803AF0075E005000EA880A4D0103600B34054D003D2007A400540054D003D2007A4005400260801C800390001C80F3580AB7010E400BB8058B004020080400588058B004020080400588028A801E8003D0001E807008051500A2A006F80372002A000540002A00372002A000540002A00150000A800150000A8329681DA50489E02A0C122780A8301A7000E080DE2007E90144400AFC0511002BF0075E005000DF9007EE0149A00B340526802CD007A4005400526802CD007A40054001E90015000390001C80E79008410156E00BB8055B802EE0080400588055B802EE0080400588020100162003D0001E806AC8038700A2A006F8028A801BE00540002A0028A801BE00540002A00150000A800150000A80F6900AC20158400F480561003D2007A4005880561003D2007A40058801E900162002C4001E806A7804C100982006F80260801BE0037C002A00260801BE0037C002A000DF000A800150000A809F00072000E4000A800390002A000540004000390002A0005400040001500010000200001000390002A000540004000150001000020000100015000100002000010000800004000080000409CB2059CE0BAD806570312E01B5C0396601C583AC002179045FC02400122780996013DC00D60308381ADE038B001BB40F3A807C80106E00B0012B7009EE014E600E280561003B0009F0004F82F7101A480376801B000EF6007A50101400AC41284009DA014AA00E08055B803AF00A00005000E1F0070A00EF400A080439002E2007C0003E0058B003D200A80005400390001C800390001C83266822FE038B0027080F2C80A9E00FCA00AC412B700D380141C00E080526803AF0075E005000E4780A0E00E8C00A08040D802E2005C4003E0054D003D2007A4005400260801C800390001C80EA380A5500EF400A58042C802FA005F400400058B004020080400588028A801E8003D0001E8058B004020080400588028A801E8003D0001E80372002A000540002A00150000A800150000A8312681C76045FC027080EC58085D0153C00AC4122780A8301A7000E080511002BF0075E005000DD6807BC0141C00A0803FF80221005C4003E00526802CD007A40054001E90015000390001C80E25807EC014AA00A5804158022A005F400400055B802EE0080400588020100162003D0001E8055B802EE0080400588020100162003D0001E8028A801BE00540002A00150000A800150000A80F0100A73014E600EBC0424002E2005C4004000561003D2007A40058801E900162002C4001E80561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A807600054000A80007A002A0001E8003D0002A00390002A0005400040001500010000200001000390002A000540004000150001000020000100015000100002000010000800004000080000402F2F01AA20396601F08117F009C20153C00AC4117F009C20153C00AC4069C003820075E005000D25006F800FCA00780050700282005C4003E0050700282005C4003E001E90015000390001C80D5D007170101400798052A80296005F400400052A80296005F400400020100162003D0001E8052A80296005F400400020100162003D0001E8020100162003D0001E80150000A800150000A80E52009EE0106E00B4C0539803AF005C4004000539803AF005C40040001E900162002C4001E80539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A8071400500007C00056002A0001E8003D0002A002A0001E8003D0002A0015000100002000010002A0001E8003D0002A00150001000020000100015000100002000010000800004000080000400DB8807D6013DC00B4C04F7002D30075E0040004F7002D30075E0040001D780100002C4001E804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A806B0003C800A0000560028000158003D0002A0028000158003D0002A000F4000A80020000100028000158003D0002A000F4000A8002000010000F4000A8002000010000800004000080000400714004F8009F000720027C001C800390002A0027C001C800390002A000E4000A80015000100027C001C800390002A000E4000A8001500010000E4000A800150001000054000400008000040027C001C800390002A000E4000A8001500010000E4000A80015000100005400040000800004000E4000A80015000100005400040000800004000540004000080000400020000100002000010979E056A80B39C060E42E89019A503544019A030BE01B24038EC01C180ED28078E00FAC00A783AC002179045FC02400122780996013DC00D6012B7009EE014E600E280561003B0009F0004F82D5E8191003490019640DBC806E200E2E0097C0EC10078A00FD800AB00420802D300790003C81284009DA014AA00E08055B803AF00A0000500058B003D200A80005400390001C800390001C8302502179035BC025080DEC009C200DF00097C0EEA80A8300F7800AB003F7002D3005A6003C812B700D380141C00E080526803AF0075E00500054D003D2007A4005400260801C800390001C80DE7809DA00E14009C80399802960052C00378040C802EE005DC0040001C380158002B000158058B004020080400588028A801E8003D0001E80372002A000540002A00150000A800150000A82F0E01B24042F2025080DA400798013840097C0E83808380150600AB003F480218005A6003C8122780A8301A7000E080511002BF0075E005000526802CD007A40054001E90015000390001C80D7A8078A013B4009C80392801D30052C0037803F480216005DC00400017700100002B000158055B802EE0080400588020100162003D0001E8028A801BE00540002A00150000A800150000A80E3D009EE013DC00E08039C00282005040037803F9802CD0059A0040001668010000200001580561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A80561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A80390002A000540004000150001000020000100015000100002000010000800004000080000402D92019A5036B801D4010BC80942013840097C0E0680798010BA008240541802AC005A6003C8117F009C20153C00AC4069C003820075E00500050700282005C4003E001E90015000390001C80CF3006E200F4A0072004ED002720052C0037803DE801D300454002E8017700100002B000158052A80296005F400400020100162003D0001E8020100162003D0001E80150000A800150000A80DCF0099600F9000AB004F700382005040037803ED002BF00442002E801668010000200001580539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A80539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A802A0001E8003D0002A00150001000020000100015000100002000010000800004000080000400D480078E0132C00AB004CB002AC007040037803BF802180057E002E8015F800BA002000015804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A8028000158003D0002A000F4000A8002000010000F4000A8002000010000800004000080000400546003B0007600054001D800150002A0001E801D800150002A0001E800A80007A000F4000A8027C001C800390002A000E4000A8001500010000E4000A800150001000054000400008000040027C001C800390002A000E4000A8001500010000E4000A80015000100005400040000800004000E4000A800150001000054000400008000040005400040000800004000200001000020000102B7D81839032B801A480D9F0075000F840073010BC80942013840097C0541802AC005A6003C810BC80942013840097C0541802AC005A6003C8069C003820075E0050001E90015000390001C80C220065900D80005D003CC801C8003CC0028804ED002720052C00378017700100002B00015804ED002720052C00378017700100002B000158020100162003D0001E80150000A800150000A80CF50090000DDA0097C03D9002B1003C00028804F7003820050400378016680100002000015804F7003820050400378016680100002000015801E900162002C4001E800DF000A800150000A804F7003820050400378016680100002000015801E900162002C4001E800DF000A800150000A801E900162002C4001E800DF000A800150000A8015000100002000010000800004000080000400C9880706012000097C03BD80209005620028804CB002AC0070400378015F800BA002000015804CB002AC0070400378015F800BA002000015801D780100002C4001E800B10007A00150000A804CB002AC0070400378015F800BA002000015801D780100002C4001E800B10007A00150000A801D780100002C4001E800B10007A00150000A800F4000A80020000100008000040000800004005130038A00714005000164000F8001F00015801D800150002A0001E800A80007A000F4000A801D800150002A0001E800A80007A000F4000A800E4000A80015000100005400040000800004001D800150002A0001E800A80007A000F4000A800E4000A80015000100005400040000800004000E4000A800150001000054000400008000040005400040000800004000200001000020000100BEC0066800E2C0073004800025F005620028804800025F005620028801C1000DE002000015804800025F005620028801C1000DE002000015801C1000DE002000015800B10007A00150000A804800025F005620028801C1000DE002000015801C1000DE002000015800B10007A00150000A801C1000DE002000015800B10007A00150000A800B10007A00150000A8008000040000800004004D10035800580003C801C500140001F00015801C500140001F00015800A80007A000F4000A801C500140001F00015800A80007A000F4000A800A80007A000F4000A8005400040000800004001C500140001F00015800A80007A000F4000A800A80007A000F4000A8005400040000800004000A80007A000F4000A8005400040000800004000540004000080000400020000100002000010049A0029E006B0003C801AC000F2002800015801AC000F2002800015800A000056000F4000A801AC000F2002800015800A000056000F4000A800A000056000F4000A8003D0002A000800004001AC000F2002800015800A000056000F4000A800A000056000F4000A8003D0002A000800004000A000056000F4000A8003D0002A0008000040003D0002A0008000040002000010000200001001C50013E0027C001C8009F00072000E4000A8009F00072000E4000A800390002A0005400040009F00072000E4000A800390002A000540004000390002A00054000400015000100002000010009F00072000E4000A800390002A000540004000390002A0005400040001500010000200001000390002A00054000400015000100002000010001500010000200001000080000400008000053
  | 4 => 0x27BA2C1212CD25228210466098220843A8808B494038EC89B6668456AE09008A03B86C24D8C00F8810200860101B09E044846AAE092EFE03CDB025DF90100670212D8010BA026A9A0106920226C001171808CDD00483400B5A40048A896ACC04348808BDF4039AC02418000F39001F74800FDD02525800FBF0020F9A010B9C086EF00454200AEB00045E0261620102B1021F3C0113AC08CAB00484600B7480049500903A804A3500BE64004C2803C0F00180600300C0013389E0448525F408EA78049BDC2490001328901EFD400FDD0258F0013C5802051E010B9C082A1004542008A840045E0267B20144A70213040113AC087EE00484600908C00495008AAF004A3500946A004C2802BBC80180600300C001338261620141DE020E0E011194086828047AB008F560048C808A77004A3F00947E004C5402C0480183800307000136008F0A004CCB009996004F1002E208019640032C800145003A0200203A0040740019C80101D000672000CE40005289B666847A250A4BE8049BDC23FBF01042502651200FDD024BFF010B960278B0010B9C0819400386D008A840045E0258F00111D502894E0113AC08614003A9700908C0049500873B003B4200946A004C280251A80130A00300C00133825258010F3B0283BC0111940846D8039E9008F560048C8086C8003B3900947E004C540251F80131500307000136008A77003CC9009996004F10026658013C40032C800145002DB000176B0040740019C80101D000672000CE400052826A9A0144A702894E0156F8085648045F7008BEE0048C80873B0047A2008F44004C54023D100131500262A00136008AAF0049BA009374004F10024DD0013C400278800145002B3100176B002ED60019C800BB5800672000CE40005280903A804CCB009996005280026658014A000294000154002DB00018D30031A6001B5800C698006D6000DAC00057803A02001FA4003F4800232800FD20008CA00119400070800FD20008CA001194000708004650001C200038400016898220844F440905D603F6C4292FA0126F702651200FDD023FBF00FE7D021F6400DFC809E2C0042E7008A840045E0249000102B6022B6600E5180A2538044EB00908C004950085648036D7007AAC003DE80251A80130A00300C0013382418000FF9A0224E400E2640A0EF004465008F560048C80846D8036840079DC003D8C0251F8013150030700013600868280372E007C8C003ECC026658013C40032C8001450026658013C40032C80014500101D000672000CE400052825DF9013C58022CFC0120A80A2538055BE008BEE0048C808614004670007764003D8C023D100131500262A001360087EE0047A200792C003ECC024DD0013C4002788001450024DD0013C400278800145000BB5800672000CE400052808CAB004A3F007DBA004150026658014A0002940001540026658014A000294000154000C698006D6000DAC00057802E208018D30031A600197800FD20008CA00119400070800FD20008CA001194000708004650001C200038400016824D8C0110360278B00120A809E2C00482A00AB7C0048C808194003AC1008CE0003D8C02338000F6300262A001360082A1003B21008F44003ECC023D1000FB3002788001450023D1000FB3002788001450009E2000514000CE4000528086EF003D4500947E0041500251F8010540029400015400251F80105400294000154000A50000550000DAC00057802C048013010031A600197800C6980065E00119400070800C6980065E001194000708004650001C200038400016808CDD004A3500946A004F100251A8013C40027880015400251A8013C4002788001540009E2000550000AA000057802BBC80176B002ED600197800BB580065E000CBC00070800BB580065E000CBC0007080032F0001C200038400016803C0F00203A0040740023280101D0008CA0011940009C40101D0008CA0011940009C4004650002710004E20001F40101D0008CA0011940009C4004650002710004E20001F4004650002710004E20001F40013880007D0000FA000064948A0842FE708A60803BE342417580FEC902122200D648292FA0126F702651200FDD009E2C0042E7008A840045E023A9E00FB47020D6600D3A008B3F0039E1007958003D000A2538044EB00908C0049500251A80130A00300C00133822F7D00F63D02030800CED4089390038FD007766003C040A0EF004465008F560048C80251F801315003070001360083838035F00071E000396801F6E8010180028A0001040026658013C40032C80014500101D000672000CE400052824BBF813289020D66010F5008AD98048CC00756A003C040A2538055BE008BEE0048C8023D100131500262A001360084C10045F7006F2400396801E4B001018002030001040024DD0013C400278800145000BB5800672000CE4000528087CF0047AB0071E0003AE801F230010900021200010B8026658014A000294000154000C698006D6000DAC000578026658014A000294000154000C698006D6000DAC00057800FD20008CA001194000708004650001C200038400016824022810768026512010F50087D9003D20009198003C0409E2C00482A00AB7C0048C802338000F6300262A001360081478039DD008BEE00396801DD9000CED002030001040023D1000FB3002788001450009E2000514000CE4000528083E6803B18008F56003AE801E77000D2A0021200010B80251F80105400294000154000A50000550000DAC0005780251F80105400294000154000A50000550000DAC00057800C6980065E001194000708004650001C2000384000168089B000484600908C004C5401EAB0010180020300010B80251A8013C4002788001540009E2000550000AA00005780251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C200038400016802F990019640032C8001B5800CB20006D6000DAC0007080101D0008CA0011940009C4004650002710004E20001F40101D0008CA0011940009C4004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006422D2500F98B02122200E600099448043D4009198003C04099448043D4009198003C0402ADF00123200262A00136007BF500356100756A002EC0022FB800E5A002030001040022FB800E5A002030001040009E2000514000CE400052807DD2003630007766002F68023D5800EBA0021200010B8023D5800EBA0021200010B800A50000550000DAC000578023D5800EBA0021200010B800A50000550000DAC00057800A50000550000DAC000578004650001C2000384000168084B6004542007958003ECC024230013150020300010B8024230013150020300010B8009E2000550000AA0000578024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C200038400016802DD20018380028A000151800CB20006D6000DAC00070800CB20006D6000DAC000708004650002710004E20001F400CB20006D6000DAC000708004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006408021803A6C008A84003ECC022A1000FB300262A0010B8022A1000FB300262A0010B80098A80042E000AA0000578022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E00038400016802BAC0013BA00307000151800C1C000546000DAC00070800C1C000546000DAC0007080036B0001C20004E20001F400C1C000546000DAC0007080036B0001C20004E20001F40036B0001C20004E20001F40013880007D0000FA00006402D6900180600300C0019C800C03000672000CE400070800C03000672000CE4000708003390001C20003840001F400C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA00006400C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E8000190000320000149096684114A085FCE039BC0227A200F1D601F31600C68823D1280FD1E020ED000D5400881B0038720074D8003A98292FA0126F702651200FDD009E2C0042E7008A840045E00A2538044EB00908C0049500251A80130A00300C00133821A4400EC6001EC7A00C4B007FCD003474006C6000366C0879D80385C007630003BC801EA2800FB3002774000FC80A0EF004465008F560048C80251F801315003070001360026658013C40032C80014500101D000672000CE4000528235570126F701F68E0103700815B0043D4006AC200366C088EA80482A0073BA003BC801D90800FB3001F66000FC80A2538055BE008BEE0048C8023D100131500262A001360024DD0013C400278800145000BB5800672000CE400052808158804465006BE00037E801B97000EBA001D74000ED801E648010540020A80010B800980800546000A8C000438026658014A000294000154000C698006D6000DAC00057800FD20008CA001194000708004650001C200038400016822B5700FD1E024DEE01037007F3E8038A20087A800366C085CB003C48009054003BC801D60800CAA001F66000FC809E2C00482A00AB7C0048C802338000F6300262A001360023D1000FB3002788001450009E2000514000CE400052807DF800385C0088CA0037E801B42000B8F001D74000ED801D9C800CCA0020A80010B80082A00042E000A8C0004380251F80105400294000154000A50000550000DAC00057800C6980065E001194000708004650001C2000384000168083490044EB0089D60048C801B6B800E5A001CB4000ED801DA1000FB3001F660010B8007D980042E00085C0004380251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C20003840001680251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C20003840001680101D0008CA0011940009C4004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006421D4400F1D601FD9200DB640937B8040DC0087A800366C082128038A2007A4000314402415000EF2001F66000FC8099448043D4009198003C0402ADF00123200262A001360022FB800E5A002030001040009E2000514000CE4000528079C80034740071FA002CF002232800DFA001D74000ED801CF4800B8F001A54000D480082A00042E000A8C000438023D5800EBA0021200010B800A50000550000DAC00057800A50000550000DAC000578004650001C2000384000168080338042E70073C2003BC802275801232001CB4000ED801D4B800F630019DA000D48007D980042E00085C000438024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C2000384000168024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C200038400016800CB20006D6000DAC000708004650002710004E20001F4004650002710004E20001F40013880007D0000FA00006407C408038720085CE003BC802173800EF2002464000ED801C36800CAA001EC6000D48007B180035200085C000438022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E000384000168022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E00038400016800C1C000546000DAC0007080036B0001C20004E20001F40036B0001C20004E20001F40013880007D0000FA0000640241A00130A00261400145000985000514000A2800057800985000514000A280005780028A00015E0002BC00016800C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA00006400C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E800019000032000014208CC00E6F001DF1A00CA0807ED88036D9007300002CF00937B8040DC0087A800366C02415000EF2001F66000FC80937B8040DC0087A800366C02415000EF2001F66000FC802ADF00123200262A001360009E2000514000CE40005280735800312C00676A00271801C4C800B3C0017B4000BE002232800DFA001D74000ED80082A00042E000A8C00043802232800DFA001D74000ED80082A00042E000A8C00043800A50000550000DAC000578004650001C2000384000168079B6003F740069D000366C01CA3000F01001760000BE002275801232001CB4000ED8007D980042E00085C00043802275801232001CB4000ED8007D980042E00085C000438009E2000550000AA00005780032F0001C200038400016802275801232001CB4000ED8007D980042E00085C000438009E2000550000AA00005780032F0001C2000384000168009E2000550000AA00005780032F0001C2000384000168004650002710004E20001F40013880007D0000FA0000640770D803550007EE800366C01BF9000C51001E02000BE002173800EF2002464000ED8007B180035200085C00043802173800EF2002464000ED8007B180035200085C0004380098A80042E000AA0000578002A800015E00038400016802173800EF2002464000ED8007B180035200085C0004380098A80042E000AA0000578002A800015E0003840001680098A80042E000AA0000578002A800015E0003840001680036B0001C20004E20001F40013880007D0000FA000064022E30012540024A8001360007BD00041000082000043800985000514000A280005780028A00015E0002BC00016800985000514000A280005780028A00015E0002BC000168003390001C20003840001F4000E100007D0000FA00006400985000514000A280005780028A00015E0002BC000168003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E800019000032000014071D90031A2006B24002CF001FBA000D9B001E02000BE001FBA000D9B001E02000BE0009190003B600085C00043801FBA000D9B001E02000BE0009190003B600085C000438009190003B600085C000438002A800015E00038400016801FBA000D9B001E02000BE0009190003B600085C000438009190003B600085C000438002A800015E000384000168009190003B600085C000438002A800015E000384000168002A800015E0003840001680013880007D0000FA00006402174001178001E80000FC80092A0004D80008200004380092A0004D80008200004380028A00015E0002BC0001680092A0004D80008200004380028A00015E0002BC0001680028A00015E0002BC000168000E100007D0000FA0000640092A0004D80008200004380028A00015E0002BC0001680028A00015E0002BC000168000E100007D0000FA0000640028A00015E0002BC000168000E100007D0000FA000064000E100007D0000FA0000640003E80001900003200001402036000EA60022F0000FC8008BC0003F20009B0000438008BC0003F20009B00004380026C00010E0002BC000168008BC0003F20009B00004380026C00010E0002BC0001680026C00010E0002BC000168000AF00005A0000FA000064008BC0003F20009B00004380026C00010E0002BC0001680026C00010E0002BC000168000AF00005A0000FA0000640026C00010E0002BC000168000AF00005A0000FA000064000AF00005A0000FA0000640003E800019000032000014009150004CE00099C0005280026700014A0002940001680026700014A000294000168000A500005A0000B40000640026700014A000294000168000A500005A0000B4000064000A500005A0000B40000640002D0000190000320000140026700014A000294000168000A500005A0000B4000064000A500005A0000B40000640002D000019000032000014000A500005A0000B40000640002D0000190000320000140002D0000190000320000140000C80000500000A0000057
  | 5 => 0x34A26152740EC8A0A1D40740E5CA3DD73077E6D81EB772014FFCCA6C8D707A7E981F9957015CD202033F301696F405CEEA004AB6CA91D4807C50E8202153016344C20F6DD01730B405FBEF004D2A421856E017A45C062B0D004FE84064AD5005260C018D9E0010914A28E7207756BC1ED9300153EDC1FB1E50163DC405BC310049F4C207C30016E37005F7D0004D5AC0618C1004FE2401826A001019C21318A0176908061E78004F54C0651160052D380192960010C6406766B0054D0C01A0B200115CC01F82400150180054060003804A91D4808CD5681F62AF019E45C200B6B01AC4C005A9070049F4C20C88601B805C05DCEC004D5AC05EC3B004FE24013F89001019C21788A01C1E4805FF30004F54C06202C0052D38014B4E0010C64063D3D0054D0C01534300115CC0183E20015018005406000380421318A01BEA5805F305004EC8C0613C8005246801491A0010AC4063EDA005503001540C00116C00186C000152E80054BA000387C0670670057B6C015EDB0011FE40197F000161E800587A0003AFC01ED11001AE50006B9400047B8006B9400047B80011EE0000BF4A6C8D707E01D023355A019E45C1FA0D401780B806B1300049F4C202EEE01810C806E017004D5AC05DFCD0043FE8013F89001019C20C8860188AE8070792004F54C060B7900462C4014B4E0010C6406178A0046EB001534300115CC01534300115CC0054060003804207C3001856DC06FA96004EC8C05FC5F004581001491A0010AC40616710046FF001540C00116C001540C00116C00054BA000387C063EDA0048CF0015EDB0011FE4015EDB0011FE400587A0003AFC01942B0014AA0006B9400047B8006B9400047B80011EE0000BF421856E01C1E48070792005E988060369005091C0142470010AC406178A00525B001496C00116C001496C00116C00045B0000387C063D3D00549940152650011FE40152650011FE40047F90003AFC0180AF0014AA00052A800047B80052A800047B80011EE0000BF406766B0057B6C015EDB0012AD4015EDB0012AD4004AB50003D5401942B0015BD00056F40004B780056F40004B780012DE0000C9401ED11001A964006A590005CD0006A590005CD00017340000F78006A590005CD00017340000F780017340000F780003DE0000294A3DD7307A04781FB5A0016FF9C23355A019E45C06B1300049F4C1FA0D401715840618C0004347006E017004D5AC013F89001019C200B6B017667C06356C00449FC070792004F54C014B4E0010C64060369004282C012425000EBE401534300115CC00540600038041FB1E501726F80625910043E9006FA96004EC8C01491A0010AC405FC5F0042438012324000EB3801540C00116C00054BA000387C0613C80043210012922000EFC0015EDB0011FE400587A0003AFC015EDB0011FE400587A0003AFC006B9400047B80011EE0000BF420F6DD01B805C0639400052698070792005E9880142470010AC4060B7900510F4011DC8000EB3801496C00116C00045B0000387C06202C00525B00121F0000EFC00152650011FE40047F90003AFC0152650011FE40047F90003AFC0052A800047B80011EE0000BF40651160055030012B81000F80C015EDB0012AD4004AB50003D54015EDB0012AD4004AB50003D540056F40004B780012DE0000C940197F00015BD00056F4000472C006A590005CD00017340000F78006A590005CD00017340000F780017340000F780003DE00002942033F3018698806E017005269806E0170052698017A620010AC405DFCD004642001443D000EB3801443D000EB380045B0000387C05EC3B0046CC401496C000EFC001496C000EFC00047F90003AFC01496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF40618C1004908001540C000F80C01540C000F80C004AB50003D5401540C000F80C004AB50003D54004AB50003D540012DE0000C940186C000119B80056F4000472C0056F4000472C0017340000F780056F4000472C0017340000F780017340000F780003DE0000294064AD50054D0C0153430011FE40153430011FE40047F90003D540153430011FE40047F90003D540047F90003D54000F550000C940183E20014AA00052A8000472C0052A8000472C0011CB0000F780052A8000472C0011CB0000F780011CB0000F780003DE000029401F824001AE50006B940005CD0006B940005CD00017340001440006B940005CD0001734000144000173400014400005100000360006B940005CD00017340001440001734000144000051000003600017340001440000510000036000051000003600000D80000090A0A1D40771D501E9922015EE8C1FB5A0017172C05F7E80040E5C23355A019E45C06B1300049F4C06E017004D5AC013F89001019C1F62AF016D69C05EDA300406A8063940004546C0120D4000E854070792004F54C014B4E0010C6401534300115CC00540600038041ED9300166E6405D39B003F27C06259100445B0011D21000E55006FA96004EC8C01491A0010AC401540C00116C00054BA000387C05F3050041B2C0113C3000DE7C012B81000F4EC004A2E0003174015EDB0011FE400587A0003AFC006B9400047B80011EE0000BF420215301AC4C005EDA3004E36406356C00530A40118E8000E550070792005E9880142470010AC401496C00116C00045B0000387C05FF30005091C010DFF000DE7C0121F0000F4EC003D3B00031740152650011FE40047F90003AFC0052A800047B80011EE0000BF4061E7800524680113C3000E36C012922000FB2C003ECB00032B4015EDB0012AD4004AB50003D540056F40004B780012DE0000C94015EDB0012AD4004AB50003D540056F40004B780012DE0000C94006A590005CD00017340000F780017340000F780003DE00002941F9957017C13406B130004E3640618C000485B8014C29000E55006E0170052698017A620010AC401443D000EB380045B0000387C05DCEC004572C014247000DE7C011DC8000CE3C003D3B000317401496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF405F7D00046BB401491A000E36C012324000D1D8003ECB00032B401540C000F80C004AB50003D54004AB50003D540012DE0000C9401540C000F80C004AB50003D54004AB50003D540012DE0000C940056F4000472C0017340000F780017340000F780003DE0000294062B0D0052D38014B4E00116C0012425000F4EC003D3B00032B40153430011FE40047F90003D540047F90003D54000F550000C940153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE000029401A0B200161E800587A0004B7800587A0004B780012DE0000F78006B940005CD0001734000144000173400014400005100000360006B940005CD00017340001440001734000144000051000003600017340001440000510000036000051000003600000D800000901EB772016B3B405F7E80044C1C06B130004E364014C29000E55006B130004E364014C29000E550017A620010AC40045B0000387C05A90700410BC0118E8000BDE0014247000DE7C003D3B0003174014247000DE7C003D3B00031740047F90003AFC0011EE0000BF405BC310041E70011D21000C06801491A000E36C003ECB00032B401491A000E36C003ECB00032B4004AB50003D540012DE0000C9401491A000E36C003ECB00032B4004AB50003D540012DE0000C94004AB50003D540012DE0000C940017340000F780003DE000029405FBEF004FE240120D4000EEF8014B4E00116C0003D3B00032B4014B4E00116C0003D3B00032B40047F90003D54000F550000C94014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE000029401929600152E8004A2E0003D6800587A0004B780012DE0000F7800587A0004B780012DE0000F780017340001440000510000036000587A0004B780012DE0000F78001734000144000051000003600017340001440000510000036000051000003600000D8000009005CEEA0045F7C013F89000EEF8013F89000EEF80045B000032B4013F89000EEF80045B000032B40045B000032B4000F550000C94013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE000029401826A00120480054BA0003D680054BA0003D680012DE0000F780054BA0003D680012DE0000F780012DE0000F7800051000003600054BA0003D680012DE0000F780012DE0000F7800051000003600012DE0000F78000510000036000051000003600000D80000090018D9E001501800540600047B800540600047B80011EE0000F7800540600047B80011EE0000F780011EE0000F780003DE000036000540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D8000009000540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D8000009000002400000189D03B20743FB81DC75401546401E811E0161C0005ACED003D0941F8074016F6EC05F04D0040B4C061A620043CDC0117DF000E09C23355A019E45C06B1300049F4C06E017004D5AC013F89001019C070792004F54C014B4E0010C6401534300115CC00540600038041DD5AF015A88C059B99003C8F805C9BE003FDEC01079C000D3D80615B70043BBC011AED000E4C4012420000EEF8004812000300C06FA96004EC8C01491A0010AC401540C00116C00054BA000387C015EDB0011FE400587A0003AFC006B9400047B80011EE0000BF41F143A019E45C05B5A7004B46405D99F004E36401042F000D3D80622BA00526980115CB000E4C4011B31000EEF8003BBE000300C070792005E9880142470010AC401496C00116C00045B0000387C0152650011FE40047F90003AFC0052A800047B80011EE0000BF405DA42004EC8C0106CB000D8EC010C84000E36C0038DB0002DDC01233C000F80C003E0300032B400466E0003D68000F5A0000A3C015EDB0012AD4004AB50003D540056F40004B780012DE0000C94006A590005CD00017340000F780017340000F780003DE00002941E9FA6016F6EC067917004B46405C5610043F540138D9000D3D806043200478740149A6000E4C4011908000CA10003BBE000300C06E0170052698017A620010AC401443D000EB380045B0000387C01496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF405B8DC0043BBC013B23000D8EC01090E000BCE40038DB0002DDC011BFC000CCE8003E0300032B4003E0300032B4000F5A0000A3C01540C000F80C004AB50003D54004AB50003D540012DE0000C940056F4000472C0017340000F780017340000F780003DE000029405E917004F54C013D530010AC4010A0B000DE7C00379F0002DDC011BAC000EFC0003BF000032B4003BF000032B4000CAD0000A3C0153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE00002940153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE0000294006B940005CD00017340001440001734000144000051000003600017340001440000510000036000051000003600000D800000901DF9B60161C0005C5CB00421EC067917004B4640138D9000D3D805E02E0043F5401216E000C4EC0149A6000E4C4003BBE000300C06B130004E364014C29000E550017A620010AC40045B0000387C014247000DE7C003D3B00031740047F90003AFC0011EE0000BF4058F71003FDEC01116C000B7B0013B23000D8EC0038DB0002DDC011604000BCE40034760002A58003E0300032B4000F5A0000A3C01491A000E36C003ECB00032B4004AB50003D540012DE0000C94004AB50003D540012DE0000C940017340000F780003DE000029405CC2D004D5AC01151B000E4C4013D530010AC400379F0002DDC0118B1000EB3800338F0002A58003BF000032B4000CAD0000A3C014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE0000294014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE000029400587A0004B780012DE0000F78001734000144000051000003600017340001440000510000036000051000003600000D8000009005A5BD0043CDC01356B000E4C401356B000E4C40042B10002DDC010FFA000CA10003ACE0002A58003ACE0002A58000CAD0000A3C013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE0000294013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE00002940054BA0003D680012DE0000F780012DE0000F7800051000003600012DE0000F78000510000036000051000003600000D8000009001498300115CC0045730003AFC0045730003AFC000EBF0000C940045730003AFC000EBF0000C94000EBF0000C94000325000029400540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D8000009000540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D8000009000002400000181D03970154640057BA3003DD8C05BFE700421EC011307000B710067917004B4640138D9000D3D80149A6000E4C4003BBE000300C067917004B4640138D9000D3D80149A6000E4C4003BBE000300C017A620010AC40045B0000387C0047F90003AFC0011EE0000BF4054FB7003C8F800FC9F000A530010FA4000B7B000301A0002698013B23000D8EC0038DB0002DDC003E0300032B4000F5A0000A3C013B23000D8EC0038DB0002DDC003E0300032B4000F5A0000A3C004AB50003D540012DE0000C940017340000F780003DE0000294058D130049F4C0101AA000D3D801127F000E550002F780002698013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C0047F90003D54000F550000C940011CB0000F780003DE0000294013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C0047F90003D54000F550000C940011CB0000F780003DE00002940047F90003D54000F550000C940011CB0000F780003DE00002940017340001440000510000036000051000003600000D800000900573480040B4C0127D3000D3D8010D1C000C4EC003954000269801356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C01356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C0045B000032B4000F550000C94000F550000C940003DE000029401356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C0045B000032B4000F550000C94000F550000C940003DE00002940045B000032B4000F550000C94000F550000C940003DE00002940012DE0000F78000510000036000051000003600000D80000090013FA10010C64004319000387C003AF90003174000C5D0000A3C0045730003AFC000EBF0000C94000EBF0000C9400032500002940045730003AFC000EBF0000C94000EBF0000C9400032500002940011EE0000F780003DE00003600003DE00003600000D800000900045730003AFC000EBF0000C94000EBF0000C9400032500002940011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D800000900000240000018053FF3003D094010397000B7100127D3000D3D800395400026980127D3000D3D800395400026980042B10002DDC000CAD0000A3C0127D3000D3D800395400026980042B10002DDC000CAD0000A3C0042B10002DDC000CAD0000A3C000F550000C940003DE00002940127D3000D3D800395400026980042B10002DDC000CAD0000A3C0042B10002DDC000CAD0000A3C000F550000C940003DE00002940042B10002DDC000CAD0000A3C000F550000C940003DE0000294000F550000C940003DE000029400051000003600000D800000900134A9001019C003A15000300C004319000387C000C5D0000A3C004319000387C000C5D0000A3C000EBF0000C940003250000294004319000387C000C5D0000A3C000EBF0000C940003250000294000EBF0000C9400032500002940003DE00003600000D80000090004319000387C000C5D0000A3C000EBF0000C940003250000294000EBF0000C9400032500002940003DE00003600000D80000090000EBF0000C9400032500002940003DE00003600000D800000900003DE00003600000D800000900000D800000900000240000018012ADB000E09C004067000300C004067000300C000E1F0000A3C004067000300C000E1F0000A3C000E1F0000A3C0003250000294004067000300C000E1F0000A3C000E1F0000A3C0003250000294000E1F0000A3C000325000029400032500002940000D80000090004067000300C000E1F0000A3C000E1F0000A3C0003250000294000E1F0000A3C000325000029400032500002940000D80000090000E1F0000A3C000325000029400032500002940000D8000009000032500002940000D800000900000D8000009000002400000180042450003804000E010000BF4000E010000BF40002FD0000294000E010000BF40002FD00002940002FD00002940000A50000090000E010000BF40002FD00002940002FD00002940000A500000900002FD00002940000A500000900000A500000900000240000018000E010000BF40002FD00002940002FD00002940000A500000900002FD00002940000A500000900000A5000009000002400000180002FD00002940000A500000900000A5000009000002400000180000A50000090000024000001800002400000180000060000005A
  | 6 => 0x2E76D5123AA3E7E1DE7735824B582079AD6EE09707F704D1FBC005A75647B87FB2099D3FB04F0915805D6AD8141405001812C800C59168010895C7D029F209BC8FF0502D9F005EE5E4147D8580189FA900CABF7801101E414C7C2401906AA00D006E801185CC034EF660048075002A3918003041478E065E09677D304D76D6805B71B813D3810017C77C00C3C4100106B9C144144E0185FF400CA973801111F8033A770004653200294D48002F33C14A3D5C018DAD600CF07D80117254035444600488EF002ACC180030E940366204004A202002C2628003274C00CF822000ED270007693800087847D029F20AD11DD04EA826806BDB2414042D601BC2E300C182C80106B9C1469F6001C6BD800C76E8001111F803256D6004653200232990002F33C14C8F1C01CF94400CB5CF80117254033D32200488EF002447780030E94034B306004A20200251010003274C00A5F92000ED2700076938000878414A3D5C01CCAE400C9F83001156A80337F300048289002414480030A88034D002004A59700252CB80032A5C00A735E000EF1100077888000889C03650AE004C81200264090003426C00ADE02000F8A30007C5180008E1400CC59A001256D00092B68000A7AC0024ADA00029EB00014F5800017F47B87FB209DD08505688EE806BDB2413CC0B6018EDC100DE17180106B9C14174FE019707C00E35EC001111F8031F13A003D94E00232990002F33C1469F60019DFFE00E7CA2001172540332F66003F459002447780030E940338C7A003FE5400251010003274C0094404000C9D3000769380008784144144E019AF9200E6572001156A8032C578003EC33002414480030A88033937A004002900252CB80032A5C0094B2E000CA9700077888000889C034D002004188600264090003426C0099024000D09B0007C5180008E1400AC5F2000EA7900092B68000A7AC0024ADA00029EB00014F5800017F414C7C2401CF94400E7CA2001435E0032EDF00046D8200236C100030A880338C7A004848F002424780032A5C009091E000CA97000654B8000889C034B306004A16100250B08003426C00942C2000D09B000684D80008E1400A5026000EA79000753C8000A7AC001D4F200029EB00014F5800017F40366204004C812002640900035E500099024000D7940006BCA0000930000AC5F2000F5230007A918000AF54001EA460002BD500015EA8000190C00CC59A001232100091908000D104002464200034410001A2080001DDC002464200034410001A2080001DDC0006882000077700003BB8000044479AD6EE0997F1304F5CCA0061D74015A23BA01AF6C900DE17180106B9C13CC0B60188DDB00CDE78800F3A04038D7B0004447E00232990002F33C14042D6018D6EC00D1207000F7D2C039F2880045C95002447780030E94032EDF0003C80D0020C660002C15C0094404000C9D300076938000878413D38100189B2000CF500800F58DC03995C800455AA002414480030A88032C578003C59E0020B710002C0600094B2E000CA9700077888000889C0337F30003D1F300215500002CCF40099024000D09B0007C5180008E140099024000D09B0007C5180008E140024ADA00029EB00014F5800017F4147D85801C6BD800D190A8012051C039F2880050D7800236C100030A880332F6600473C500202C60002C060009091E000CA97000654B8000889C033D322004848F00209D08002CCF400942C2000D09B000684D80008E1400942C2000D09B000684D80008E14001D4F200029EB00014F5800017F40354446004A59700218FD8002E29C0099024000D7940006BCA000093000099024000D7940006BCA00009300001EA460002BD500015EA8000190C00ADE02000F5230007A918000A6CC002464200034410001A2080001DDC002464200034410001A2080001DDC0006882000077700003BB800004441414050019C0AF00E35EC0012051C038D7B0004814700286BC00030A88031F13A003F4EC00239E28002C060008E78A000B018000654B8000889C03256D6003FCFD00242478002CCF4009091E000B33D000684D80008E14009091E000B33D000684D80008E14001A136000238500014F5800017F4033A770004193C00252CB8002E29C0094B2E000B8A70006BCA000093000094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C00A735E000CDFB0007A918000A6CC001EA4600029B30001A2080001DDC001EA4600029B30001A2080001DDC0006882000077700003BB80000444034EF66004A20200251010003426C0094404000D09B000684D800093000094404000D09B000684D80009300001A13600024C000012600000190C00A5F92000EA79000753C8000A6CC001D4F200029B300014D980001DDC001D4F200029B300014D980001DDC0005366000077700003BB8000044400CF822001256D00092B68000D1040024ADA00034410001A20800025840024ADA00034410001A20800025840006882000096100004B08000055C0024ADA00034410001A20800025840006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C4779DCD60965BEA04CF665805DF7D413D73280188CA700CA1DD000EC41C15A23BA01AF6C900DE17180106B9C038D7B0004447E00232990002F33C13AA09A018545B00C90CD000EB248034642A003E7B7002069A0002B714039F2880045C95002447780030E940094404000C9D3000769380008784135DB5A017F19F00C604E800E724C033D402003DC1F00201108002AF8803995C800455AA002414480030A880094B2E000CA9700077888000889C0327E0C003BEA5001F4640002A0A800863F6000B69A0006B7980007AD40099024000D09B0007C5180008E140024ADA00029EB00014F5800017F4140B67C01BC2E300C90CD00113A1C034481C00488FD001FA4F8002AF88039F2880050D7800236C100030A88009091E000CA97000654B8000889C032D73E0046D82001EB378002A0A80082742000B69A0005B4D00007AD400942C2000D09B000684D80008E14001D4F200029EB00014F5800017F4033C1F60048289001F4640002AD900085540000BAB40005D5A00007D900099024000D7940006BCA00009300001EA460002BD500015EA8000190C0099024000D7940006BCA00009300001EA460002BD500015EA8000190C002464200034410001A2080001DDC0006882000077700003BB8000044413C2456019291700DE17180113A1C03379E20040C69002447E8002AF88038D7B0004814700286BC00030A88008E78A000B018000654B8000889C031DBA0003EB7D00236C10002A0A80080B180009E830005B4D00007AD4009091E000B33D000684D80008E14001A136000238500014F5800017F4032A5CE003FBBB00241448002AD900082DC4000A10E0005D5A00007D900094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C0094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C001EA4600029B30001A2080001DDC0006882000077700003BB8000044403401BA00488EF002447780032A5C0083198000B69A0005B4D00007D900094404000D09B000684D80009300001A13600024C000012600000190C0094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB8000044400B098A000F8A30007C518000AF54001F1460002BD500015EA80001DDC0024ADA00034410001A20800025840006882000096100004B08000055C0024ADA00034410001A20800025840006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C41347EF0018336000CA1DD000F80AC03785C60044E87002447E8002AF8803785C60044E87002447E8002AF8800A1AF0000C2A2000654B8000889C03060B2003B5C9001FA4F80024F48008DB04000A82A0005B4D00007AD4008DB04000A82A0005B4D00007AD4001A136000238500014F5800017F4030F104003C0C00020110800256800090512000AB640005D5A00007D900090512000AB640005D5A00007D90001AF2800024C000015EA8000190C0090512000AB640005D5A00007D90001AF2800024C000015EA8000190C001AF2800024C000015EA8000190C0006882000077700003BB80000444032AFDE0046532002069A0002C9AC00911DE000CA970005B4D00007D9000911DE000CA970005B4D00007D90001A13600024C000012600000190C00911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB8000044400AB306000EF110006B79800093C4001F1460002BD500015EA80001DDC001F1460002BD500015EA80001DDC0006882000096100004B08000055C001F1460002BD500015EA80001DDC0006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C4031645A003F19600232990002C9AC008CA64000B26B000654B80007D90008CA64000B26B000654B80007D90001952E0001F6400012600000190C008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB8000044400A5352000D1350007788800093C4001DE2200024F100015EA80001DDC001DE2200024F100015EA80001DDC00057AA000077700004B08000055C001DE2200024F100015EA80001DDC00057AA000077700004B08000055C00057AA000077700004B08000055C00012C2000015700000AB800000C400A8E46000ED2700076938000A7AC001DA4E00029EB00014F580001DDC001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C4001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C7547CFC0933BC204B2DF5005B8D8C132FE26017A7CA00C19B0000E077013BA10A0186F6300C948B800EBCAC033815E003D534001F8CB0002A32C15A23BA01AF6C900DE17180106B9C038D7B0004447E00232990002F33C039F2880045C95002447780030E940094404000C9D300076938000878412CEFA601739B300BF8CF800DF0240313640003A529001E060000283580335F24003D47E001FDDD8002AE700083278000B26B000689A8000778C03995C800455AA002414480030A880094B2E000CA9700077888000889C0099024000D09B0007C5180008E140024ADA00029EB00014F5800017F413791FE01AF6C900C2A2D8010A9F4031ADD80044E87001DAE480028358033BFFC0048147001F5BE8002AE70007F9FA000B26B00059358000778C039F2880050D7800236C100030A88009091E000CA97000654B8000889C00942C2000D09B000684D80008E14001D4F200029EB00014F5800017F4031B5AC00455AA001DF5280029104007A3E6000AB6400055B20000732C008310C000B8A70005C5380007D900019BF600024F100012788000151C0099024000D7940006BCA00009300001EA460002BD500015EA8000190C002464200034410001A2080001DDC0006882000077700003BB80000444133A7F60186F6300D7B648010A9F40311BB6003D6D1002274380028358032E0F8004024400240A38002AE70007E9D80009B7A00059358000778C038D7B0004814700286BC00030A88008E78A000B018000654B8000889C009091E000B33D000684D80008E14001A136000238500014F5800017F4030BFE8003D47E0022AD5000291040078B3C000937000055B20000732C00800520009DD40005C5380007D90001714E0001F6400012788000151C0094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C001EA4600029B30001A2080001DDC0006882000077700003BB800004440320D540045C950022E4A80030A88007901A000A82A00054150000732C007FCA8000B33D000599E80007D90001667A0001F640000FB20000151C0094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB800004440094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB800004440024ADA00034410001A20800025840006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C412E0FEE017A7CA00C4653800EFEBC035ED920042A7D002274380028358031DB82003D6D1002063480025F78009028E000AB9C00059358000778C03785C60044E87002447E8002AF8800A1AF0000C2A2000654B8000889C008DB04000A82A0005B4D00007AD4001A136000238500014F5800017F402F8EF8003A529001EE0F80023E8C008AB54000A44100055B20000732C007D8660009370000508700006C48001714E0001F6400012788000151C0090512000AB640005D5A00007D90001AF2800024C000015EA8000190C001AF2800024C000015EA8000190C0006882000077700003BB800004440313F52004447E001F3DB8002AE70008B92A000C2A200054150000732C007E8B2000B0180004F4180006C48001667A0001F640000FB20000151C00911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB8000044400911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB80000444001F1460002BD500015EA80001DDC0006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C40302590003D534002223F0002AE7000888FC000AB9C00061510000732C007B29C0009B7A000580C00006C4800160300001B120000FB20000151C008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB80000444008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB80000444001DE2200024F100015EA80001DDC00057AA000077700004B08000055C00057AA000077700004B08000055C00012C2000015700000AB800000C400900EA000C9D300064E980008E1400193A6000238500011C28000190C00193A6000238500011C28000190C000470A0000643000032180000444001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C4001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C125AC10016E36300BBEFA800E2D80030EBA0003BFAF001F01580023BD0035ED920042A7D002274380028358009028E000AB9C00059358000778C035ED920042A7D002274380028358009028E000AB9C00059358000778C00A1AF0000C2A2000654B8000889C001A136000238500014F5800017F402DB8DC0037C09001CE4980020F4C007AC6E0008FA30004AD000006414008AB54000A44100055B20000732C001714E0001F6400012788000151C008AB54000A44100055B20000732C001714E0001F6400012788000151C001AF2800024C000015EA8000190C0006882000077700003BB8000044402F72F20041AE7001D64900028358007BE96000ABE200049E900006414008B92A000C2A200054150000732C001667A0001F640000FB20000151C008B92A000C2A200054150000732C001667A0001F640000FB20000151C001A13600024C000012600000190C0005366000077700003BB80000444008B92A000C2A200054150000732C001667A0001F640000FB20000151C001A13600024C000012600000190C0005366000077700003BB80000444001A13600024C000012600000190C0005366000077700003BB800004440006882000096100004B08000055C00012C2000015700000AB800000C402EB56C003AF2B0020D73800283580079D0200097DE00055F10000641400888FC000AB9C00061510000732C00160300001B120000FB20000151C00888FC000AB9C00061510000732C00160300001B120000FB20000151C001952E0001F6400012600000190C0004980000064300003BB8000044400888FC000AB9C00061510000732C00160300001B120000FB20000151C001952E0001F6400012600000190C0004980000064300003BB80000444001952E0001F6400012600000190C0004980000064300003BB8000044400057AA000077700004B08000055C00012C2000015700000AB800000C4008C2E6000C3A500061D28000889C00160AE0001EB50000F5A8000151C00193A6000238500011C28000190C000470A000064300003218000044400193A6000238500011C28000190C000470A000064300003218000044400053D6000077700003BB8000055C0000EEE000015700000AB800000C400193A6000238500011C28000190C000470A000064300003218000044400053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C02D3AB200381DC001D88380023BD000835CE000A0D600055F10000641400835CE000A0D600055F10000641400185440001CCB0000FB20000151C00835CE000A0D600055F10000641400185440001CCB0000FB20000151C00185440001CCB0000FB20000151C0004980000064300003BB8000044400835CE000A0D600055F10000641400185440001CCB0000FB20000151C00185440001CCB0000FB20000151C0004980000064300003BB8000044400185440001CCB0000FB20000151C0004980000064300003BB800004440004980000064300003BB8000044400012C2000015700000AB800000C400880F2000BCCF00056E28000778C001874A00022270000F5A8000151C001874A00022270000F5A8000151C000470A0000643000032180000444001874A00022270000F5A8000151C000470A0000643000032180000444000470A00006430000321800004440000EEE000015700000AB800000C4001874A00022270000F5A8000151C000470A0000643000032180000444000470A00006430000321800004440000EEE000015700000AB800000C4000470A00006430000321800004440000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C00844AE000A8CB0005E678000778C001799E0001DE300011138000151C001799E0001DE300011138000151C000444E0000547000032180000444001799E0001DE300011138000151C000444E0000547000032180000444000444E00005470000321800004440000C86000011100000AB800000C4001799E0001DE300011138000151C000444E0000547000032180000444000444E00005470000321800004440000C86000011100000AB800000C4000444E00005470000321800004440000C86000011100000AB800000C40000C86000011100000AB800000C400002AE000003100000188000001C001820A00021E100010F0800017F400043C200005FD00002FE8000044400043C200005FD00002FE800004440000BFA00001110000088800000C400043C200005FD00002FE800004440000BFA00001110000088800000C40000BFA00001110000088800000C40000222000003100000188000001C00043C200005FD00002FE800004440000BFA00001110000088800000C40000BFA00001110000088800000C40000222000003100000188000001C0000BFA00001110000088800000C40000222000003100000188000001C0000222000003100000188000001C00000620000007000000380000005D
  | 7 => 0x3D74D0D010CA9CE0222C05D0091C00488ABF3D302559E3804C19238013844A08C98043025F4BE804DC13AC01412F1813B5E5B0052724000A8C6BC003069808E117E002660F7404EBDEEC0145A5B014115200054193C00ACAC200031A090144FC43005547FC00B091680032EFB002CD97A000D0D30001DF64000077D9089FBD080253DB5604C6F2B8013B73401381FAE0051A06C00A79EA800302B6013E10B800536A6E00ACBA740031D6D002BF862000CCCFC001D6F8000075BE014367490054DB5A00B00E440032CD9002D2D49000D2842001E5F40000797D002E09C2000D6A0C001F3D800007CF60008FB8000023EE000047DC000011F708E117E002A08AF004D7CA14016B627813AC5EB005D391400A5E6F800302B601404037005F2CFA00AA531C0031D6D002AF73E000CCCFC001999F800075BE01455E740060CD6C00AD45240032CD9002C13B3000D2842001A5084000797D002CC15C000D6A0C001AD4180007CF60007650900023EE000047DC000011F7014367490060446000AC39B8003284F002BD833000D1866001A30CC00078F1002CDFAF000D7542001AEA840007D70800772A70002434000048680000121A002E0A94000DD034001BA06800080D10007B78F000258400004B08000012C20008E1E80002B50000056A0000015A800015A80000056A00000AD4000002B508C98043026D9BB0054115E0016B6278137CD4800550E6600BA722800302B6013BCE1A0056933A00BE59F40031D6D002AA57C000B6F42001999F800075BE014040370057E04600C19AD80032CD9002B92D4000BB56C001A5084000797D002BDB51000BD0D2001AD4180007CF60006B5060001F3D800047DC000011F7013E10B800574D5C00C088C0003284F002B45C6000BA096001A30CC00078F1002BE816000BD70E001AEA840007D708006BAA10001F5C200048680000121A002CDFAF000C198E001BA06800080D10006E81A000203440004B08000012C20007A7BA00023A1E00056A0000015A800015A80000056A00000AD4000002B50144FC430060CD6C00C19AD80039A24002B5E7E000CE2340019C46800078F1002BDB51000D1F9E001A3F3C0007D7080068FCF0001F5C20003EB84000121A002CC15C000D6C04001AD80800080D10006B602000203440004068800012C200075CEA00023A1E0004743C00015A800011D0F000056A00000AD4000002B5002E09C2000DD034001BA06800084A50006E81A000212940004252800013550007A7BA000251160004A22C00016880001288B00005A200000B44000002D10008E1E80002B110000562200001A4000015888000069000000D200000034800015888000069000000D20000003480000348000000D2000001A40000006908ABF3D3025EA8C404E194A0014E8DD01504578005AD89E00BA722800302B60137CD480053F42000AEF5D4002D3F0802F967D000C75B4001999F800075BE013AC5EB0054CCB800B1570C002DEDD003066B6000CB364001A5084000797D002B5E7E000B44E000182B900006F660006B5060001F3D800047DC000011F701381FAE005415EE00AFFAB0002D8E380302230000CA13C001A30CC00078F1002B45C6000B3FAE001825C40006F548006BAA10001F5C200048680000121A002BD833000B62920018904C00071298006E81A000203440004B08000012C20006E81A000203440004B08000012C200015A80000056A00000AD4000002B501411520005F2CFA00B1AB7C00343F0803066B6000E68900019C46800078F1002B92D4000CF2D40017C9740006F5480068FCF0001F5C20003EB84000121A002C13B3000D1F9E001816E400071298006B602000203440004068800012C20006B602000203440004068800012C200011D0F000056A00000AD4000002B5002D2D49000D75420018B678000742F0006E81A000212940004252800013550006E81A000212940004252800013550001288B00005A200000B44000002D10007B78F000251160004A22C000159300015888000069000000D200000034800015888000069000000D20000003480000348000000D2000001A400000069013B5E5B0057815600BE59F400343F0802F967D000D0FC2001CD12000078F1002AA57C000BB63E0019E5A80006F548006796A0001BD520003EB84000121A002AF73E000BCDB4001A3F3C000712980068FCF0001C4A60004068800012C200068FCF0001C4A60004068800012C2000101A200004B080000AD4000002B5002BF862000C17CE001AEA84000742F0006BAA10001D0BC0004252800013550006BAA10001D0BC0004252800013550001094A00004D540000B44000002D1000772A70001FF620004A22C00015930001288B0000564C0000D20000003480001288B0000564C0000D20000003480000348000000D2000001A400000069002CD97A000D6A0C001AD41800080D10006B506000203440004068800013550006B50600020344000406880001355000101A200004D5400009AA800002D10007650900023A1E0004743C000159300011D0F0000564C0000AC98000034800011D0F0000564C0000AC98000034800002B2600000D2000001A4000000690008FB800002B50000056A000001A4000015A80000069000000D200000040000015A80000069000000D2000000400000034800000100000002000000008000015A80000069000000D2000000400000034800000100000002000000008000003480000010000000200000000800000080000000200000004000000010088B01740253CBD404C068F00143068013865280053EA8000AC1C14002C0D701504578005AD89E00BA722800302B6002F967D000C75B4001999F800075BE0135F2850053485400AB5F30002BEA3802C6ADF000B91E00017EAB40006DDE003066B6000CB364001A5084000797D0006B5060001F3D800047DC000011F70131BCAE0052198000A912C0002B420002BFEAC000B73860017B2980006CD780302230000CA13C001A30CC00078F10006BAA10001F5C200048680000121A002B0E6E000B2D9400173CE80006B0D00062D9E0001CC240004248000010920006E81A000203440004B08000012C200015A80000056A00000AD4000002B5013AF7BB005D391400AB5F3000323A9002C55C3000D239C00176B2C0006CD7803066B6000E68900019C46800078F100068FCF0001F5C20003EB84000121A002B5149000CE2340016DC380006B0D000605B90001CC240003984800010920006B602000203440004068800012C200011D0F000056A00000AD4000002B5002C0391000D186600173CE80006CDB000624130001D5540003AAA800010E60006E81A000212940004252800013550001288B00005A200000B44000002D10006E81A000212940004252800013550001288B00005A200000B44000002D100015888000069000000D20000003480000348000000D2000001A400000069013704EB0055C0BC00BA722800323A9002BBD75000BEE3E001A47380006CD7802F967D000D0FC2001CD12000078F10006796A0001BD520003EB84000121A002A94C7000B9EC80019C4680006B0D0005F25D0001980600039848000109200068FCF0001C4A60004068800012C2000101A200004B080000AD4000002B5002B2E9D000BC970001A30CC0006CDB0006097100019DFC0003AAA800010E60006BAA10001D0BC0004252800013550001094A00004D540000B44000002D10006BAA10001D0BC0004252800013550001094A00004D540000B44000002D10001288B0000564C0000D20000003480000348000000D2000001A400000069002C245A000D2842001A50840007D7080060AE40001CC240003984800010E60006B50600020344000406880001355000101A200004D5400009AA800002D10006B50600020344000406880001355000101A200004D5400009AA800002D100011D0F0000564C0000AC98000034800002B2600000D2000001A4000000690007CF60000258400004B080000168800012C2000005A200000B440000034800015A80000069000000D2000000400000034800000100000002000000008000015A80000069000000D20000004000000348000001000000020000000080000034800000100000002000000008000000800000002000000040000000100130648E0052E30400AC1C14002DF15002E9C8A000C8EA4001A47380006CD7802E9C8A000C8EA4001A47380006CD7800734480001E3C40003EB84000121A002979BE000B153000176B2C00060080006711A0001AC340003984800010920006711A0001AC34000398480001092000101A200004B080000AD4000002B50029E7AA000B323A0017B298000611900068C330001B36C0003AAA800010E600068C330001B36C0003AAA800010E60001094A00004D540000B44000002D100068C330001B36C0003AAA800010E60001094A00004D540000B44000002D10001094A00004D540000B44000002D10000348000000D2000001A400000069002B2B08000CCCFC0017EAB40007096800694210001F5C20003984800010E6000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000101A200004D5400009AA800002D100002B2600000D2000001A400000069000797D00002434000042480000137800012C2000005A200000B440000034800012C2000005A200000B4400000348000034800000100000002000000008000012C2000005A200000B4400000348000034800000100000002000000008000003480000010000000200000000800000080000000200000004000000010002A31AF000BADFC001999F800070968006667E0001C25A0003EB8400010E60006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10000FAE10000439800009AA800002D1000026AA00000B4400001A40000006900075BE000020520000486800001378000121A000004DE00000B4400000348000121A000004DE00000B440000034800002D1000000D20000020000000080000121A000004DE00000B440000034800002D1000000D2000002000000008000002D1000000D20000020000000080000008000000020000000400000001000077D9000023EE000047DC000015A800011F70000056A00000AD40000034800011F70000056A00000AD40000034800002B5000000D2000001A40000008000011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000002B5000000D2000001A40000008000000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000208654E700248E48004A797A8013BC29812F546200513EFE00A5C608002A2920136CDD80053936000AB8178002BFDB002BC0AB000B616C00175BF80006B1B01504578005AD89E00BA722800302B6002F967D000C75B4001999F800075BE003066B6000CB364001A5084000797D0006B5060001F3D800047DC000011F70129EDAB004FECB800A433000029EDD802A0AF7000AE6440016647400066CC802BA6AE000B5FE4001792E00006CB800060BE70001C25A00040A40000102900302230000CA13C001A30CC00078F10006BAA10001F5C200048680000121A0006E81A000203440004B08000012C200015A80000056A00000AD4000002B5013307BA005AD89E00A690A80030C79002A665C000C8EA400162A6000066CC802BF023000D0FC200173D900006CB80005E6DA0001C25A000384B40001029003066B6000E68900019C46800078F100068FCF0001F5C20003EB84000121A0006B602000203440004068800012C200011D0F000056A00000AD4000002B5002A6DAD000CA13C00165B2800068C10005B1490001B36C000366D80000FAB00060CC70001D0BC0003A17800010E60000FFB100004DE000009BC0000026F0006E81A000212940004252800013550001288B00005A200000B44000002D100015888000069000000D20000003480000348000000D2000001A400000069012FA5F40053936000B5B13C0030C790029FA10000B650800191D4800066CC802B499D000BD428001A1F840006CB80005DB1F000190C0000384B40001029002F967D000D0FC2001CD12000078F10006796A0001BD520003EB84000121A00068FCF0001C4A60004068800012C2000101A200004B080000AD4000002B50029B537000B5FE40019427800068C100059FD700017FA2000366D80000FAB0005EB87000196C40003A17800010E60000E85E0000439800009BC0000026F0006BAA10001D0BC0004252800013550001094A00004D540000B44000002D10001288B0000564C0000D20000003480000348000000D2000001A400000069002AA3FE000CB364001966C800078F10005A2700001AC34000358680000FAB0005E8690001C4A60003894C00010E60000E2530000439800008730000026F0006B50600020344000406880001355000101A200004D5400009AA800002D100011D0F0000564C0000AC98000034800002B2600000D2000001A4000000690006B50600020344000406880001355000101A200004D5400009AA800002D100011D0F0000564C0000AC98000034800002B2600000D2000001A40000006900015A80000069000000D2000000400000034800000100000002000000008000003480000010000000200000000800000080000000200000004000000010012ACF1C00513EFE00A7D500002CA1C002D6C4F000C31E400191D4800066CC802A8733000B65080017DC7C0006211800687E10001B2E0000384B40001029002E9C8A000C8EA4001A47380006CD7800734480001E3C40003EB84000121A0006711A0001AC34000398480001092000101A200004B080000AD4000002B50028D036000AE6440016E70C0005DA00006509E0001A304000366D80000FAB0005D04B00017FA200033BF80000EE70000E85E0000439800009BC0000026F00068C330001B36C0003AAA800010E60001094A00004D540000B44000002D10001094A00004D540000B44000002D10000348000000D2000001A400000069002A0C9E000C75B4001723C00006CB8000659B20001E3C4000358680000FAB0005DAB60001BD520003300C0000EE70000E2530000439800008730000026F000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000101A200004D5400009AA800002D100002B2600000D2000001A400000069000694210001F5C20003984800010E6000101A200004D5400009AA800002D1000101A200004D5400009AA800002D100002B2600000D2000001A40000006900012C2000005A200000B440000034800003480000010000000200000000800000348000001000000020000000080000008000000020000000400000001000293920000B616C0018EB680006CB800063ADA0001B2E00003C7880000FAB0005B7A1000190C000037AA40000EE70000DEA900003B9C00008730000026F0006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10000FAE10000439800009AA800002D1000026AA00000B4400001A4000000690006667E0001C25A0003EB8400010E60000FAE10000439800009AA800002D10000FAE10000439800009AA800002D1000026AA00000B4400001A400000069000121A000004DE00000B440000034800002D1000000D2000002000000008000002D1000000D200000200000000800000080000000200000004000000010000686980001F3D80003E7B000012C20000F9EC00004B080000961000002D10000F9EC00004B080000961000002D10000258400000B4400001688000006900011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000011F70000056A00000AD40000034800002B5000000D2000001A40000008000002B5000000D2000001A400000080000006900000020000000400000001000002B5000000D2000001A40000008000000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000201238009004EF0A600A18340002A8810029D1BA000B28700016F8A80005D22002D6C4F000C31E400191D4800066CC800687E10001B2E0000384B40001029002D6C4F000C31E400191D4800066CC800687E10001B2E0000384B40001029000734480001E3C40003EB84000121A000101A200004B080000AD4000002B500276E68000A7B760015A100000571E0005B1C700017680000308C80000DEB0006509E0001A304000366D80000FAB0000E85E0000439800009BC0000026F0006509E0001A304000366D80000FAB0000E85E0000439800009BC0000026F0001094A00004D540000B44000002D10000348000000D2000001A4000000690028B4B6000C0AD80015F51C00066CC8005BDBA0001B35E000300400000DEB000659B20001E3C4000358680000FAB0000E2530000439800008730000026F000659B20001E3C4000358680000FAB0000E2530000439800008730000026F000101A200004D5400009AA800002D100002B2600000D2000001A400000069000659B20001E3C4000358680000FAB0000E2530000439800008730000026F000101A200004D5400009AA800002D100002B2600000D2000001A400000069000101A200004D5400009AA800002D100002B2600000D2000001A40000006900003480000010000000200000000800000080000000200000004000000010002825E3000AFF6C001815B000066CC8005A7E100018846000366BC0000DEB00063ADA0001B2E00003C7880000FAB0000DEA900003B9C00008730000026F00063ADA0001B2E00003C7880000FAB0000DEA900003B9C00008730000026F0000FAE10000439800009AA800002D1000026AA00000B4400001A40000006900063ADA0001B2E00003C7880000FAB0000DEA900003B9C00008730000026F0000FAE10000439800009AA800002D1000026AA00000B4400001A4000000690000FAE10000439800009AA800002D1000026AA00000B4400001A40000006900002D1000000D20000020000000080000008000000020000000400000001000065DF60001E5F40003CBE8000121A0000DECC0000424800008490000026F0000F9EC00004B080000961000002D10000258400000B440000168800000690000F9EC00004B080000961000002D10000258400000B4400001688000006900002B5000000D2000001A40000008000000690000002000000040000000100000F9EC00004B080000961000002D10000258400000B4400001688000006900002B5000000D2000001A400000080000006900000020000000400000001000002B5000000D2000001A40000008000000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000200270894000A8A48001606B80005D220006056C00019B32000366BC0000DEB0006056C00019B32000366BC0000DEB0000F1E200003EAC00008730000026F0006056C00019B32000366BC0000DEB0000F1E200003EAC00008730000026F0000F1E200003EAC00008730000026F000026AA00000B4400001A4000000690006056C00019B32000366BC0000DEB0000F1E200003EAC00008730000026F0000F1E200003EAC00008730000026F000026AA00000B4400001A4000000690000F1E200003EAC00008730000026F000026AA00000B4400001A400000069000026AA00000B4400001A4000000690000080000000200000004000000010000634120001D6F800036EF000010290000F2FA0000486800008490000026F0000F2FA0000486800008490000026F0000258400000B440000168800000690000F2FA0000486800008490000026F0000258400000B440000168800000690000258400000B4400001688000006900000690000002000000040000000100000F2FA0000486800008490000026F0000258400000B440000168800000690000258400000B4400001688000006900000690000002000000040000000100000258400000B4400001688000006900000690000002000000040000000100000069000000200000004000000010000001000000004000000080000000200060D300001AC6C0003ADF000010290000EB7C000040A4000090D0000026F0000EB7C000040A4000090D0000026F00002434000009BC0000168800000690000EB7C000040A4000090D0000026F00002434000009BC00001688000006900002434000009BC000016880000069000005A2000001A40000040000000100000EB7C000040A4000090D0000026F00002434000009BC00001688000006900002434000009BC000016880000069000005A2000001A400000400000001000002434000009BC000016880000069000005A2000001A4000004000000010000005A2000001A400000400000001000000100000000400000008000000020000EFB2000047DC00008FB800002B5000023EE00000AD4000015A80000069000023EE00000AD4000015A800000690000056A000001A4000003480000010000023EE00000AD4000015A800000690000056A000001A40000034800000100000056A000001A4000003480000010000000D200000040000000800000002000023EE00000AD4000015A800000690000056A000001A40000034800000100000056A000001A4000003480000010000000D2000000400000008000000020000056A000001A4000003480000010000000D200000040000000800000002000000D20000004000000080000000200000020000000080000001000000005F
  | 8 => 0x20C388C480FC7B76F8401C0DF601E3310E040F7AE2E01EDF9DA007D8C734003930F9041BC3C4A01F5153F007FFBB5E003AA37480818F4C0003C06FD800F548E20007B144042594B2201FA0C9700816E84A003B5D460083A8BB0003D1902800FA56300007DD6600850F6A4003DD9FD000FF514800080C6700103073400083B14000252EC400010869040A9C80801ECCFE4007E17A6C0039BCAC00807060C003B87A0000F3FB580007AA0C00829E678003CB016000FA945E0007E676800FEC9C40008193300024A3F80001048E008493C0C003D9EC1800FEE0BC0008093E80105047400084C8D00025ADC000010BF00010990CE0008725380026A8C4000112E90002BBCFC0001370700004DC1C0000228F042594B2202244324007FA95E00041568480816AE900042DE49800F1BCCC0007AA0C00836B22400441E40000F770CA0007E676800F9867C000819330002064CC0001048E008549FE8004527BE800FB3ED40008093E800FF42D800084C8D00021323400010BF000102DBE40008725380021C94E000112E900024D1460001370700004DC1C0000228F008493C0C0044CFD9000F9E4D20007FED3800FE1B5E000843D0800210F4200010ADF00103983C0008797680021E5DA000113EF8002511960001393E00004E4F8000022CE00109C8C00008ADCC80022B73200011AB40002649F600014394000050E50000023F40002B5E1000016F5900005BD64000028D100005BD64000028D100000A34400000489041BC3C4A01FFE319808910C9000415684808058A74003DBD278010B79260007AA0C0081CBA54003EB6FB0011079000007E676800F7C9E0000757698002064CC0001048E00836B224003F8D9D801149EFA0008093E800FC912000077F5C80021323400010BF0000FE135400078FA500021C94E000112E900021C94E000112E900004DC1C0000228F00829E678003F2DAC801133F640007FED3800FB0AD2000773A1800210F4200010ADF000FE70D8000793C980021E5DA000113EF80021E5DA000113EF80004E4F8000022CE00103983C0007BAFF80022B73200011AB400022B73200011AB4000050E50000023F40002601480001351080005BD64000028D100005BD64000028D100000A3440000048900850F6A4004527BE801149EFA0008F955000FB761E0008252280020948A00010ADF000FE1354000848C700021231C000113EF80021231C000113EF800044FBE000022CE00102DBE4000874E900021D3A400011AB400021D3A400011AB4000046AD0000023F400024B2440001351080004D442000028D100004D442000028D100000A344000004890010990CE0008ADCC80022B7320001224000022B73200012240000048900000024F0000260148000140388000500E200002A4B0000500E200002A4B00000A92C000004B30002B5E1000016DC400005B7100000306900005B7100000306900000C1A40000056100005B7100000306900000C1A40000056100000C1A40000056100000158400000099040F7AE2E01F4EB2400808F632003CD0E1808910C90004156848010B79260007AA0C008058A74003D0939800FD3824000744030011079000007E6768002064CC0001048E00816AE90003D94190010042F200075CF3001149EFA0008093E80021323400010BF0000FB761E0007405C8001EDC140000F8C100021C94E000112E900004DC1C0000228F00807060C003D1C1F000FE7F9C00074F35801133F640007FED3800210F4200010ADF000FB0AD200073DDC0001ED8CC0000F8B680021E5DA000113EF80004E4F8000022CE000FE1B5E000752F10001F557C0000FC7C80022B73200011AB4000050E50000023F400022B73200011AB4000050E50000023F400005BD64000028D100000A344000004890083A8BB000441E4000100B0B400083CA3001149EFA0008F95500020948A00010ADF000FC912000082EC60001E6DD40000F8B680021231C000113EF800044FBE000022CE000FF42D8000848C70001EC9B40000FC7C80021D3A400011AB4000046AD0000023F400021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489001050474000879768001F80F60001028400022B73200012240000048900000024F000022B73200012240000048900000024F00000500E200002A4B00000A92C000004B30002649F6000140388000500E2000028B300005B7100000306900000C1A40000056100005B7100000306900000C1A40000056100000C1A4000005610000015840000009900818F4C0003F4FE300110790000083CA300110790000083CA300023E55400010ADF000F7C9E000077F9B80020BB180000F8B680020BB180000F8B6800044FBE000022CE000F9867C00078E0B80021231C0000FC7C80021231C0000FC7C800046AD0000023F400021231C0000FC7C800046AD0000023F4000046AD0000023F400000A34400000489000FEC9C40007B88980021E5DA0001028400021E5DA00010284000048900000024F000021E5DA00010284000048900000024F0000048900000024F000000A92C000004B3000251196000119718000500E2000028B30000500E2000028B300000C1A4000005610000500E2000028B300000C1A40000056100000C1A400000561000001584000000990010307340008725380021C94E00011AB400021C94E00011AB4000046AD0000024F000021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300024D1460001351080004D442000028B300004D442000028B300000A2CC0000056100004D442000028B300000A2CC0000056100000A2CC00000561000001584000000990002BBCFC00016F5900005BD640000306900005BD640000306900000C1A40000066840005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D9000000144401C0DF601ECF0EE807D85BD0003AF66380808F632003D0009800F985FE00071889008910C90004156848010B79260007AA0C0011079000007E6768002064CC0001048E007FA95E0003C9A84800F8A14A000714AE00100B0B4000769F38001E8E500000F58E001149EFA0008093E80021323400010BF000021C94E000112E900004DC1C0000228F007E17A6C003BD361800F5A1500006FC85800FE7F9C0007588F8001E4F7A0000F38B801133F640007FED3800210F4200010ADF00021E5DA000113EF80004E4F8000022CE000F9E4D2000733860001DD5400000F0630001F80F6000100380000489D80000204600022B73200011AB4000050E50000023F400005BD64000028D100000A3440000048900816E84A0042DE49800F8A14A0007F4340010042F2000847E00001DFD1E0000F38B801149EFA0008F95500020948A00010ADF00021231C000113EF800044FBE000022CE000FB3ED4000825228001D66040000F0630001EC9B4000100380000400E00000204600021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489000FEE0BC000843D08001DD5400000F3FF0001F557C000104D0000041340000020D900022B73200012240000048900000024F00000500E200002A4B00000A92C000004B300022B73200012240000048900000024F00000500E200002A4B00000A92C000004B300005B7100000306900000C1A40000056100000C1A40000056100000158400000099007FFBB5E003E30B20010B79260007F434000FD382400079D58000211F800000F38B80110790000083CA300023E55400010ADF00020BB180000F8B6800044FBE000022CE000F770CA000772A580020948A0000F0630001E6DD40000E6CB8000400E00000204600021231C0000FC7C800046AD0000023F4000046AD0000023F400000A34400000489000FA945E00078B22000210F420000F3FF0001ED8CC0000E9DF000041340000020D900021E5DA00010284000048900000024F0000048900000024F000000A92C000004B300021E5DA00010284000048900000024F0000048900000024F000000A92C000004B30000500E2000028B300000C1A40000056100000C1A40000056100000158400000099000FF514800084C8D000213234000113EF8001EDC14000100380000400E0000020D900021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900026A8C400014394000050E5000002A4B000050E5000002A4B00000A92C0000056100005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014407D8C734003C57CA800F985FE00075CDE0010B79260007F434000211F800000F38B8010B79260007F434000211F800000F38B80023E55400010ADF000044FBE000022CE000F1BCCC0007250B8001DFD1E0000DADC00020948A0000F0630000400E00000204600020948A0000F0630000400E000002046000046AD0000023F400000A34400000489000F3FB58000735D20001E4F7A0000DD13000210F420000F3FF000041340000020D9000210F420000F3FF000041340000020D9000048900000024F000000A92C000004B3000210F420000F3FF000041340000020D9000048900000024F000000A92C000004B3000048900000024F000000A92C000004B300000C1A40000056100000158400000099000FA5630000819330001E8E500000FB2C800213234000113EF8000400E0000020D9000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC000005610000015840000009900025ADC00001393E0000489D80000253B000050E5000002A4B00000A92C00000561000050E5000002A4B00000A92C0000056100000C1A4000006684000019A1000000B6400050E5000002A4B00000A92C0000056100000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014400F548E200077B0E0002064CC0000FB2C8002064CC0000FB2C800044FBE000020D90002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B30002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900024A3F800011BD100004E4F80000253B00004E4F80000253B00000A92C0000056100004E4F80000253B00000A92C0000056100000A92C000005610000019A1000000B640004E4F80000253B00000A92C0000056100000A92C000005610000019A1000000B640000A92C000005610000019A1000000B64000019A1000000B64000002D900000014400252EC40001370700004DC1C000028D100004DC1C000028D100000A3440000056100004DC1C000028D100000A3440000056100000A34400000561000001584000000B640004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D9000000144000000510000000243F1EDDBE01E4E27F007B3C3BA0039C8AC007D3AC90003B4747000F15F2A0006D41F007FF8C66003CC7FB000F8C2C8000716A6000FD3F8C00074E2F0001DEC380000F00F008910C90004156848010B79260007AA0C0011079000007E6768002064CC0001048E001149EFA0008093E80021323400010BF000021C94E000112E900004DC1C0000228F007B33F90003A68C6000EF4D860006CBD6000F4707C000708B40001CD7480000E7A6800FCB6B200074D720001E2C880000F3570001EE2260000FB2C800046F4400001F89001133F640007FED3800210F4200010ADF00021E5DA000113EF80004E4F8000022CE00022B73200011AB4000050E50000023F400005BD64000028D100000A34400000489007E8325C00415684800F26A120007BFB4000F650640007F4340001C942E0000E7A6800FE367600083CA30001DCA960000F3570001E382E0000FB2C80003ECB200001F89001149EFA0008F95500020948A00010ADF00021231C000113EF800044FBE000022CE00021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489000F67B060007FED38001CCE180000EBA10001D4BC40000F3FF00003CFFC00001EB70001EEBFE00010284000040A10000020D90000465C60000253B0000094EC0000042300022B73200012240000048900000024F00000500E200002A4B00000A92C000004B300005B7100000306900000C1A40000056100000C1A40000056100000158400000099007D454FC003CC7FB001055A120007BFB4000F424E600074FFD0001FD0D00000E7A6800FADBEC00078E9400020F28C0000F3570001DFE6E0000E2FB00003ECB200001F8900110790000083CA300023E55400010ADF00020BB180000F8B6800044FBE000022CE00021231C0000FC7C800046AD0000023F4000046AD0000023F400000A34400000489000F2C05800074D720001FFB4E0000EBA10001CF7700000DABC80003CFFC00001EB70001E4F260000E643000040A10000020D9000040A10000020D90000094EC0000042300021E5DA00010284000048900000024F0000048900000024F000000A92C000004B30000500E2000028B300000C1A40000056100000C1A40000056100000158400000099000F767F40008093E8002024FA00010ADF0001D01720000F06300003C18C00001EB70001E3E940000FC7C80003F1F2000020D900003F1F2000020D90000083640000042300021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014407B7E768003B4747000F4002600072D3F801055A120007BFB40001FD0D00000E7A6800F6F49E00074FFD0001E75600000DE9780020F28C0000F35700003ECB200001F890010B79260007F434000211F800000F38B80023E55400010ADF000044FBE000022CE00020948A0000F0630000400E000002046000046AD0000023F400000A34400000489000EE1E80000708B40001D623E0000D5F00001FFB4E0000EBA100003CFFC00001EB70001DCE860000DABC80003A77C00001D73000040A10000020D90000094EC00000423000210F420000F3FF000041340000020D9000048900000024F000000A92C000004B3000048900000024F000000A92C000004B300000C1A40000056100000158400000099000F4640A0007E6768001DA7CE0000F3570002024FA00010ADF00003C18C00001EB70001DFD720000F8B6800039B2E00001D7300003F1F2000020D900000836400000423000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000050E5000002A4B00000A92C0000056100000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014400F01BF600074E2F0001F99DA0000F3570001F99DA0000F357000042B7C00001EB70001D5DA60000E2FB00003E2DA00001D7300003E2DA00001D73000008364000004230002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B3000001584000000990002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900004E4F80000253B00000A92C0000056100000A92C000005610000019A1000000B640000A92C000005610000019A1000000B64000019A1000000B64000002D90000001440020EC50000112E9000044BA4000023F4000044BA4000023F4000008FD0000004B3000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D900000014400000051000000024078CC4380039C8AC000EBD98E0006E13F000F3438600072D3F8001D73780000D4CA001055A120007BFB40001FD0D00000E7A680020F28C0000F35700003ECB200001F89001055A120007BFB40001FD0D00000E7A680020F28C0000F35700003ECB200001F8900023E55400010ADF000044FBE000022CE000046AD0000023F400000A34400000489000E6F2B00006CBD60001BF2160000C90F0001D3CD60000D5F000003744C00001BBA0001FFB4E0000EBA100003CFFC00001EB7000040A10000020D90000094EC000004230001FFB4E0000EBA100003CFFC00001EB7000040A10000020D90000094EC00000423000048900000024F000000A92C000004B300000C1A40000056100000158400000099000ED75180007AA0C0001C52B80000E7A68001D73CC0000F38B800036B7000001BBA0002024FA00010ADF00003C18C00001EB700003F1F2000020D9000008364000004230002024FA00010ADF00003C18C00001EB700003F1F2000020D900000836400000423000046AD0000024F00000093C0000004B300000A2CC00000561000001584000000990002024FA00010ADF00003C18C00001EB700003F1F2000020D900000836400000423000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000046AD0000024F00000093C0000004B300000A2CC000005610000015840000009900000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014400EA8DD2000716A60001EA8300000E7A68001D100C0000DE9780003CE2E00001BBA0001F99DA0000F357000042B7C00001EB700003E2DA00001D73000008364000004230001F99DA0000F357000042B7C00001EB700003E2DA00001D7300000836400000423000044FBE000020D90000093C0000004B30000093C0000004B3000001584000000990001F99DA0000F357000042B7C00001EB700003E2DA00001D7300000836400000423000044FBE000020D90000093C0000004B30000093C0000004B300000158400000099000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900000A92C000005610000019A1000000B64000019A1000000B64000002D90000001440020319C00010BF0000042FC0000022CE00003E3040000204600000811800000423000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC00000099000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900000A34400000561000001584000000B6400001584000000B64000002D900000014400044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D90000001440000005100000002400E4C3E40006D41F0001C62240000D4CA0001EA8300000E7A680003CE2E00001BBA0001EA8300000E7A680003CE2E00001BBA000042B7C00001EB7000008364000004230001EA8300000E7A680003CE2E00001BBA000042B7C00001EB700000836400000423000042B7C00001EB7000008364000004230000093C0000004B3000001584000000990001EA8300000E7A680003CE2E00001BBA000042B7C00001EB700000836400000423000042B7C00001EB7000008364000004230000093C0000004B300000158400000099000042B7C00001EB7000008364000004230000093C0000004B3000001584000000990000093C0000004B3000001584000000990000019A1000000B64000002D9000000144001F75980001048E00003D63800001F89000042FC0000022CE00000811800000423000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000008FD0000004B30000012CC00000099000001584000000B64000002D900000014400042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000008FD0000004B30000012CC00000099000001584000000B64000002D900000014400008FD0000004B30000012CC00000099000001584000000B64000002D900000014400001584000000B64000002D9000000144000002D900000014400000051000000024001EC5100000F00F00004123800001F8900004123800001F89000008B380000042300004123800001F89000008B3800000423000008B38000004230000012CC0000009900004123800001F89000008B3800000423000008B38000004230000012CC00000099000008B38000004230000012CC000000990000012CC000000990000002D90000001440004123800001F89000008B3800000423000008B38000004230000012CC00000099000008B38000004230000012CC000000990000012CC000000990000002D900000014400008B38000004230000012CC000000990000012CC000000990000002D9000000144000012CC000000990000002D9000000144000002D900000014400000051000000024000421A40000228F000008A3C00000489000008A3C0000048900000122400000099000008A3C00000489000001224000000990000012240000009900000026400000014400008A3C0000048900000122400000099000001224000000990000002640000001440000122400000099000000264000000144000002640000001440000005100000002400008A3C0000048900000122400000099000001224000000990000002640000001440000122400000099000000264000000144000002640000001440000005100000002400001224000000990000002640000001440000026400000014400000051000000024000002640000001440000005100000002400000051000000024000000090000000062
  | 9 => 0x3B23B5BBD8CBA425B219D0C47EC0571DC01068813E44016377D8602D197D0C0093C1DAC699D83AE01681164602DE3365800971CA240B991E9A0026946CF004EB099A00118B12C6A80D461016B4884602E5B24280098CC64C0BC49B2E002732FC7005026DA60011E5E7C0BE119990027A141B005193E8E001245CFC014AA58B8004A9B3B000A65FCC00021465C6814B50D0162C9CFC02D49EB0400951420C0B83123200264EC1F004E5B75E00117ECAC0BB026450026FA171005042A420011FAC0C0146055780049944F000A44FFC00020DCCC0BD8A381002783F5500517FF62001241F4C014D33BE8004B380D000A8816C00021B37C015289B18004C71C3000AC85DC00022812C00302B0E00009A23600013446C00003DA7C6A80D46101863D1FA02DCD768800A661EB00B9773DA002A7A052004DB45B600117ECAC0BC0B0A1002B31574004F590420011FAC0C013FE2D180049944F00093289E00020DCCC0BE73F97002BC8F36005071F02001241F4C01467FA08004B380D00096701A00021B37C014ABBE78004C71C300098E38600022812C0029454180009A23600013446C00003DA7C0BD8A381002B966B600500DEEE00122C58C014534A48004AF1BD00095E37A0002194BC014BB05E8004CB12900099625200022A0C40029893380009B29E00013653C00003E10C0152F7498004E64230009CC8460002367FC002AC9D380009FD9E00013FB3C00003FF0C002FD8E08000B313C000166278000047A180005989E000011E86000023D0C00000729C699D83AE016F366C2030C7A3F400A661EB00B819A210027946650054F40A400117ECAC0B9F4267002823F45005662AE80011FAC0C013DCDC780043763700093289E00020DCCC0BC0B0A100289F91D005791E6C001241F4C01434EB380044BFD100096701A00021B37C01451752800454ABB00098E38600022812C002638E180008A04B00013446C00003DA7C0BB02645002867B0B00572CD6C00122C58C014192AD800445FE300095E37A0002194BC01459ABF80045708300099625200022A0C40026589480008A83100013653C00003E10C014BB05E80046BC630009CC8460002367FC0027321180008D9FF00013FB3C00003FF0C002A7E888000995F7000166278000047A180005989E000011E86000023D0C00000729C0BE11999002BC8F36005791E6C0014239380141FD0F80049F5DB00093EBB60002194BC014517528004B203100096406200022A0C40025901880008A83100011506200003E10C014ABBE78004C901700099202E0002367FC0026480B80008D9FF00011B3FE00003FF0C002929CC8000995F7000132BEE000047A180004CAFB800011E86000023D0C00000729C015289B18004E64230009CC84600024435C002732118000910D70001221AE00004185C002A7E8880009E61F00013CC3E000049F980004F30F8000127E6000024FCC00000765C002FD8E08000B2791000164F220000537F0000593C8800014DFC000029BF8000008598000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C68813E4401681F57E02E17CDD4009C2CEEC0C31E8FD0029987AC0054F40A400117ECAC0B819A2100272DA770050F78E20010B336C01598ABA00047EB0300093289E00020DCCC0B9773DA00277D5830051D66620010E6BF4015E479B0004907D300096701A00021B37C0141FD0F80042BF3D0008D20820001F9524002638E180008A04B00013446C00003DA7C0B831232002737365005153C2E0010CA34C015CB35B00048B16300095E37A0002194BC014192AD80042AD670008D1D160001F95FC0026589480008A83100013653C00003E10C014534A480043630B0008F29FE00020076C0027321180008D9FF00013FB3C00003FF0C0027321180008D9FF00013FB3C00003FF0C0005989E000011E86000023D0C00000729C0BC49B2E002B315740051F64320012AA0F4015E479B000508E4E00093EBB60002194BC01434EB38004A46870008B5E460001F95FC0025901880008A83100011506200003E10C01467FA08004B20310008CE50600020076C0026480B80008D9FF00011B3FE00003FF0C0026480B80008D9FF00011B3FE00003FF0C0004CAFB800011E86000023D0C00000729C014D33BE8004CB1290008FDD6200020B854002732118000910D70001221AE00004185C002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C002AC9D380009E61F00013CC3E000047784000593C8800014DFC000029BF8000008598000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C0B991E9A00287BD3D005662AE80012AA0F401598ABA0004AA83D000A11C9C0002194BC013DCDC780044C0BB000948D0E0001F95FC0025234380007E57F00011506200003E10C013FE2D1800453EC100096406200020076C002590188000801DB00011B3FE00003FF0C002590188000801DB00011B3FE00003FF0C00046CFF80000FFC3000023D0C00000729C01460557800469F0B00099625200020B85400265894800082E150001221AE00004185C00265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C0029893380008D45F00013CC3E0000477840004F30F800011DE1000029BF80000085980004F30F800011DE1000029BF80000085980000A6FE0000021660000042CC000000D5C014AA58B8004C71C300098E3860002367FC002638E180008D9FF00011B3FE00004185C002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C002945418000995F7000132BEE0000477840004CAFB800011DE1000023BC20000085980004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C00302B0E0000B313C0001662780000537F00005989E000014DFC000029BF8000009C400005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D0000000190674311FB0162F5D2A02D1CC6BC0097E972C0B85F37500272701B004FE5DA20010598F40C31E8FD0029987AC0054F40A400117ECAC01598ABA00047EB0300093289E00020DCCC0B735DA20026EDE9B004FA75760010536FC0147D90C8004407BD0008BD3760001F3404015E479B0004907D300096701A00021B37C002638E180008A04B00013446C00003DA7C0B527AC1002679627004EC7E9600102149401454F0B8004377930008AD3620001EF9CC015CB35B00048B16300095E37A0002194BC0026589480008A83100013653C00003E10C014037BB8004257D50008900CA0001EA6740023F758800081D350001228D400003A1C40027321180008D9FF00013FB3C00003FF0C0005989E000011E86000023D0C00000729C0B96C90A002A7A052004FA75760012165FC014759988004B048F000897C960001EF9CC015E479B000508E4E00093EBB60002194BC0025901880008A83100011506200003E10C0141C7C080049F5DB00087329A0001EA67400233941800081D35000103A6A00003A1C40026480B80008D9FF00011B3FE00003FF0C0004CAFB800011E86000023D0C00000729C0145FFD88004AF1BD0008900CA0001F10940023CA7F800083EF5000107DEA00003B0C4002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C0B78CD960027D73F70054F40A40012165FC0143DE3880045A82700096091E0001EF9CC01598ABA0004AA83D000A11C9C0002194BC0025234380007E57F00011506200003E10C013D641080044582D00093EBB60001EA6740022D7918000765D2000103A6A00003A1C4002590188000801DB00011B3FE00003FF0C00046CFF80000FFC3000023D0C00000729C01410A9080045236100095E37A0001F109400234745800077CF4000107DEA00003B0C400265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C00265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C0004F30F800011DE1000029BF80000085980000A6FE0000021660000042CC000000D5C01464FA38004B380D00096701A00022A0C400234820800081D35000103A6A00003B0C4002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C0004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C002B217700009FD9E00013FB3C000049F980004FECF0000127E6000024FCC0000085980005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D00000001900B465F430026C6D57004FE5DA20010E5AB40153D02900048597F00096091E0001EF9CC0153D02900048597F00096091E0001EF9CC0028472700008652F00011506200003E10C0136D16D80041DCA5000897C960001C38C00024FAED80007A99D000103A6A00003A1C40024FAED80007A99D000103A6A00003A1C400046CFF80000FFC3000023D0C00000729C01396DD780042688B0008AD3620001C7BB0002578DE80007C425000107DEA00003B0C4002578DE80007C425000107DEA00003B0C40004886B800010617000024FCC00000765C002578DE80007C425000107DEA00003B0C40004886B800010617000024FCC00000765C0004886B800010617000024FCC00000765C0000A6FE0000021660000042CC000000D5C01409B6980049944F0008BD3760001FDD3C00259C0680008A831000103A6A00003B0C400259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C002A205B00009B29E0001228D40000421080004FECF0000127E6000024FCC0000085980004FECF0000127E6000024FCC0000085980000A6FE000002710000004E20000000FA00004FECF0000127E6000024FCC0000085980000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D0000000190013AC266800449C0D00093289E0001FDD3C0024CA2780007F74F00011506200003B0C40024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C002913FF00008E33200013653C0000421080004D94F000010842000024FCC0000085980004D94F000010842000024FCC000008598000093F3000002166000004E20000000FA00004D94F000010842000024FCC000008598000093F3000002166000004E20000000FA0000093F3000002166000004E20000000FA0000013880000003E80000007D0000000190002997F300009A23600013446C000047A180004D11B000011E86000023D0C0000085980004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA00004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D00000001900004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D000000019000008F430000021660000042CC000000FA0000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C800000002865D212D9015DB86A602C5EBA5400952E1A40B40FABF002628F39004D8DAAE000FCD4040B79B361002706BEB004FAE7EE0010563540143DE9E80043217D00089381A0001E92F40C31E8FD0029987AC0054F40A400117ECAC01598ABA00047EB0300093289E00020DCCC015E479B0004907D300096701A00021B37C002638E180008A04B00013446C00003DA7C0B164E7E0025A6C8B004CF2C4E000FBC6DC0139B9B280040E85500084D1160001DA03C01433D85800431C3D0008A46C20001EF4A400234F8580007F74F00011C664000038E14015CB35B00048B16300095E37A0002194BC0026589480008A83100013653C00003E10C0027321180008D9FF00013FB3C00003FF0C0005989E000011E86000023D0C00000729C0B5A44230029987AC004DDBD360011AA8FC013BEAC180048597F00083B94A0001DA03C0144FC8E8004AA83D00088B05A0001EF4A400229F6080007F74F0000FEE9E000038E14015E479B000508E4E00093EBB60002194BC0025901880008A83100011506200003E10C0026480B80008D9FF00011B3FE00003FF0C0004CAFB800011E86000023D0C00000729C013C1FAA80048B16300084AFAA0001E16D40021B18580007C4250000F884A00003797400235E31800082E15000105C2A00003B0C400046A2F8000108420000210840000069B4002732118000910D70001221AE00004185C0004F30F8000127E6000024FCC00000765C000593C8800014DFC000029BF80000085980000A6FE0000021660000042CC000000D5C0B408B23002706BEB005330F580011AA8FC01396D3B800432EC100090B2FE0001DA03C01411FA2800452ED100095507A0001EF4A40022605D8000748C80000FEE9E000038E1401598ABA0004AA83D000A11C9C0002194BC0025234380007E57F00011506200003E10C002590188000801DB00011B3FE00003FF0C00046CFF80000FFC3000023D0C00000729C0137D0B8800431C3D0009162C60001E16D4002156B3800070DEE0000F884A0000379740022B84180007626C000105C2A00003B0C40004170A80000EC310000210840000069B400265894800082E150001221AE00004185C0004886B800010617000024FCC00000765C0004F30F800011DE1000029BF80000085980000A6FE0000021660000042CC000000D5C013D0A0D8004907D3000920FA60002194BC00215F9E80007A99D0000F533A0000379740022A55D8000801DB0001003B600003B0C4000400ED80000EC3100001D8620000069B4002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C0004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C002638E180008D9FF00011B3FE00004185C00046CFF800010617000020C2E00000765C0004CAFB800011DE1000023BC200000859800008EF08000021660000042CC000000D5C0005989E000014DFC000029BF8000009C400000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D00000001900B1BBEC3002628F39004E4E036001083A74014CC3D600046AA3F00090B2FE0001DA03C013CA332800432EC10008B504E0001C9EA80025541E80007BD290000FEE9E000038E140153D02900048597F00096091E0001EF9CC0028472700008652F00011506200003E10C0024FAED80007A99D000103A6A00003A1C400046CFF80000FFC3000023D0C00000729C0132760F80040E85500086EF260001BA560002458B18000785B50000F884A00003797400222FF1800070DEE0000EF9E80000359D00004170A80000EC310000210840000069B4002578DE80007C425000107DEA00003B0C40004886B800010617000024FCC00000765C0004886B800010617000024FCC00000765C0000A6FE0000021660000042CC000000D5C013997E380047EB03000880F7A0001EF4A4002483E980008652F0000F533A00003797400225FE880007E57F0000ECBA40000359D0000400ED80000EC3100001D8620000069B400259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C00259C0680008A831000103A6A00003B0C400046CFF800010617000020C2E00000765C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C0004FECF0000127E6000024FCC0000085980000A6FE000002710000004E20000000FA00000A6FE000002710000004E20000000FA0000013880000003E80000007D00000001900134A36780043217D0008FD6060001EF4A40023F58180007BD2900010CA5E0000379740021BB1B8000748C80000FCAFE0000359D00003F2BF80000D67400001D8620000069B40024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0024CA2780007F74F00011506200003B0C40004541880000EC31000020C2E00000765C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0004D94F000010842000024FCC000008598000093F3000002166000004E20000000FA0000093F3000002166000004E20000000FA0000013880000003E80000007D000000019000254D9D80008A04B00011409600003FF0C0004502580000FFC300001FF8600000765C0004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C0004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D00000001900004D11B000011E86000023D0C00000859800008F430000021660000042CC000000FA000008F430000021660000042CC000000FA0000010B30000003E80000007D000000019000008F430000021660000042CC000000FA0000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C80000000280AE3B80200254B869004BF4B96000FE7B94013859DD800420E9D000872D5A0001B7FE0014CC3D600046AA3F00090B2FE0001DA03C0025541E80007BD290000FEE9E000038E14014CC3D600046AA3F00090B2FE0001DA03C0025541E80007BD290000FEE9E000038E140028472700008652F00011506200003E10C00046CFF80000FFC3000023D0C00000729C012A28418003EF1B7000810A4A0001A2DA00021946980006E9580000E3DD8000032CD0002458B18000785B50000F884A0000379740004170A80000EC310000210840000069B4002458B18000785B50000F884A0000379740004170A80000EC310000210840000069B40004886B800010617000024FCC00000765C0000A6FE0000021660000042CC000000D5C013198C980045FB2B000829B7E0001DA03C0021CD7E80007BE730000E1C60000032CD0002483E980008652F0000F533A000037974000400ED80000EC3100001D8620000069B4002483E980008652F0000F533A000037974000400ED80000EC3100001D8620000069B400046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C002483E980008652F0000F533A000037974000400ED80000EC3100001D8620000069B400046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C00046CFF800010617000020C2E00000765C00008EF08000021660000042CC000000D5C0000A6FE000002710000004E20000000FA0000013880000003E80000007D0000000190012E39448004158D50008BF6560001DA03C0021666D8000727AA0000F7CE6000032CD00023F58180007BD2900010CA5E0000379740003F2BF80000D67400001D8620000069B40023F58180007BD2900010CA5E0000379740003F2BF80000D67400001D8620000069B40004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0023F58180007BD2900010CA5E0000379740003F2BF80000D67400001D8620000069B40004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C0004541880000EC31000020C2E00000765C0000830B800001D970000042CC000000D5C000093F3000002166000004E20000000FA0000013880000003E80000007D000000019000248B9F800086CDF00010D9BE00003E10C0003F2A480000E87100001D0E20000069B40004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C0004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C00008F430000021660000042CC000000FA0000010B30000003E80000007D00000001900004502580000FFC300001FF8600000765C00007FE1800001D97000003B2E000000D5C00008F430000021660000042CC000000FA0000010B30000003E80000007D000000019000008F430000021660000042CC000000FA0000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C8000000028012783B58003F350100082CC7A0001B7FE00022FD9580007680F0000F7CE6000032CD00022FD9580007680F0000F7CE6000032CD00004329780000DE5D00001D8620000069B40022FD9580007680F0000F7CE6000032CD00004329780000DE5D00001D8620000069B40004329780000DE5D00001D8620000069B40000830B800001D970000042CC000000D5C0022FD9580007680F0000F7CE6000032CD00004329780000DE5D00001D8620000069B40004329780000DE5D00001D8620000069B40000830B800001D970000042CC000000D5C0004329780000DE5D00001D8620000069B40000830B800001D970000042CC000000D5C0000830B800001D970000042CC000000D5C000013880000003E80000007D00000001900023CBCF8000837330000F9A02000038E140004366F80000F84300001D0E20000069B40004366F80000F84300001D0E20000069B400007FE1800001D97000003B2E000000D5C0004366F80000F84300001D0E20000069B400007FE1800001D97000003B2E000000D5C00007FE1800001D97000003B2E000000D5C000010B30000003E80000007D00000001900004366F80000F84300001D0E20000069B400007FE1800001D97000003B2E000000D5C00007FE1800001D97000003B2E000000D5C000010B30000003E80000007D000000019000007FE1800001D97000003B2E000000D5C000010B30000003E80000007D0000000190000010B30000003E80000007D0000000190000001F40000000640000000C80000000280023162580007A4BD000106E66000038E1400041B9980000E38500001F0860000069B400041B9980000E38500001F0860000069B400007C21800001A6D000003B2E000000D5C00041B9980000E38500001F0860000069B400007C21800001A6D000003B2E000000D5C00007C21800001A6D000003B2E000000D5C00000ECB8000003570000007D000000019000041B9980000E38500001F0860000069B400007C21800001A6D000003B2E000000D5C00007C21800001A6D000003B2E000000D5C00000ECB8000003570000007D000000019000007C21800001A6D000003B2E000000D5C00000ECB8000003570000007D000000019000000ECB8000003570000007D0000000190000001F40000000640000000C8000000028000428CB80000F69F00001ED3E00000729C00007B4F800001CA700000394E000000D5C00007B4F800001CA700000394E000000D5C00000E538000003570000006AE00000019000007B4F800001CA700000394E000000D5C00000E538000003570000006AE00000019000000E538000003570000006AE000000190000001AB8000000640000000C800000002800007B4F800001CA700000394E000000D5C00000E538000003570000006AE00000019000000E538000003570000006AE000000190000001AB8000000640000000C800000002800000E538000003570000006AE000000190000001AB8000000640000000C8000000028000001AB8000000640000000C80000000280000003200000000A0000000140000000063
  | 10 => 0x2EBDE6A8F6245CF1DF9126A8DC4C00E106B7784A786CAA403948CE3701D0864DC001597E69C4B3068660039F5314501D7E817F001609A6040772648C80059D86D9002DBF2C500024B4B7C4BC39F86C03A6DC21101DC4B482801642F9BC078BDACE6005B281BA002E8539B8002561C64079C4A98A005C0F3CA002F44CDE800261746400BF6348A0009B462D00055AC6E80003E4EDC4A346950603931B12901D265FBE8015C64E1807660834E00594BF1C002D96EC100024A140C078062526005AB62FE002E980ED000258CD4400BD0E87400099691800054C10C80003DA3AC07980B5E6005BD98E3002F3F7888002613E4000C0D80C60009C840F00056B86D80003F11C400C3B26E60009EDDCB00058A035800040748400187C4EE00011CEC500008E76280000679BC4BC39F86C03E551D7D01D742658801808B2000772071BA0061FE3C6002D3E2EA80024A140C078A117AA00637F2A8002E1C059800258CD4400B9CB1A60009969180004CB48C00003DA3AC07A08BEF40064BC9F3002EB04188002613E4000BD47E860009C840F0004E420780003F11C400BF8D56E0009EDDCB0004F6EE58000407484001548A1800011CEC500008E76280000679BC07980B5E60064521AE002E7B5D380025EA7AC00BC9D23A0009C00720004E003900003EDDB000C0196560009F5D480004FAEA4000040ACB800156999400011EB2100008F590800006840C00C3FECEE000A29FB1000514FD8800042039C001601DE8000126ABF00009355F800006B27400185AA1A0001469370000A349B8000076C1400028D26E00001DB0500000ED82800000ACBC4B306866003B05970A01F2A8EBE801808B200076565D96005BFA7FC0030FF1E300024A140C077696E6E005D289F80031BF954000258CD4400B8A941E0008DECF50004CB48C00003DA3AC078A117AA005E2D3F500325E4F98002613E4000BB8FEB20009061E40004E420780003F11C400BC85BE20009172240004F6EE580004074840013DBB96000101D2100008E76280000679BC078062526005DB64C90032290D700025EA7AC00BAA7FBE0008FAC220004E003900003EDDB000BCD4A2200091BF7C0004FAEA4000040ACB80013EBA90000102B2E00008F590800006840C00C01965600094452D000514FD8800042039C001453F620001080E700009355F800006B2740015DDDB200011BC820000A349B8000076C1400028D26E00001DB0500000ED82800000ACBC079C4A98A0064BC9F300325E4F98002996D1800BAD918E0009A21D10004D10E880003EDDB000BC85BE20009C61830004E30C1800040ACB800138C306000102B2E000081597000006840C00BF8D56E0009F24F30004F9279800042039C0013E49E60001080E7000084073800006B27400153D2CA00011BC8200008DE410000076C1400023790400001DB0500000ED82800000ACBC00C3B26E6000A29FB1000514FD88000437970001453F6200010DE5C000086F2E000006D9200015DDDB20001243DC0000921EE000007A4CC0002487B800001E93300000F499800000B1E400185AA1A000145B090000A2D8480000887AC00028B6120000221EB0000110F5800000C68400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C4A786CAA4039FC3EBB01D9F9C5F8016B5DBF407CAA3AFA006022C800030FF1E300024A140C076565D96005B235AC002EF19E98002326EF400C6FE5500009633510004CB48C00003DA3AC0772071BA005BCAEAA002F667B280023896B400C9793E6000984F900004E420780003F11C400BAD918E0008C9B1800049F01F00003B89B40013DBB96000101D2100008E76280000679BC07660834E005B35396002F214A68002352AA800C8A435C00097A9EB0004E003900003EDDB000BAA7FBE0008C7D3000049F22F00003B8DD40013EBA90000102B2E00008F590800006840C00BC9D23A0008DE36B0004AF08400003C5458001453F620001080E700009355F800006B274001453F620001080E700009355F800006B27400028D26E00001DB0500000ED82800000ACBC078BDACE600637F2A8002F7766680026D7AAC00C9793E6000A65B460004D10E880003EDDB000BB8FEB20009ABD89000491B0A00003B8DD400138C306000102B2E000081597000006840C00BD47E860009C618300049D9E280003C54580013E49E60001080E7000084073800006B2740013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC00C0D80C60009F5D480004B461C00003D840C001453F6200010DE5C000086F2E000006D920001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E4001601DE80001243DC0000921EE00000768A400028B6120000221EB0000110F5800000C68400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C0772648C8005DE1A4D0031BF95400026D7AAC00C6FE5500009B5EAB000532DA300003EDDB000B8A941E0009062470004D5EC480003B8DD4001357B120000EE375000081597000006840C00B9CB1A6000915D420004E30C180003C545800138C3060000F1516000084073800006B27400138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC00BD0E87400093FFD30004FAEA400003D840C0013EBA900000F6103000086F2E000006D9200013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E4001569994000107BF60000921EE00000768A40002487B800001DA290000110F5800000C6840002487B800001DA290000110F5800000C6840000443D60000031A10000018D0800000120C00BF6348A0009EDDCB0004F6EE5800042039C0013DBB960001080E7000084073800006D9200013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E4001548A1800011BC8200008DE4100000768A400023790400001DA2900000ED14800000C68400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C00187C4EE0001469370000A349B80000887AC00028D26E0000221EB0000110F5800000E4C400028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC00028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E449AA371300393AD61901D0CF84B80162630F00767E717E005B13082002E60D56800227BE0407CAA3AFA006022C800030FF1E300024A140C00C6FE5500009633510004CB48C00003DA3AC075D09962005A9D04A002E414ED8002272F3000BDDD99A0008EF768000494CAB00003ADE8400C9793E6000984F900004E420780003F11C40013DBB96000101D2100008E76280000679BC074997EFA0059A4260002DCA8768002212C9000BC8529A0008DE34A00048D3A000003A7B8400C8A435C00097A9EB0004E003900003EDDB00013EBA90000102B2E00008F590800006840C00B9ED74E0008BD959000480350000039F9100012D18700000F44020000873958000062584001453F620001080E700009355F800006B27400028D26E00001DB0500000ED82800000ACBC07712D20A0061FE3C6002E414ED80025C074C00BD99ECA0009C0E3D000482F0300003A7B8400C9793E6000A65B460004D10E880003EDDB000138C306000102B2E000081597000006840C00BAC10620009A21D10004725A8800039F91000127678A0000F440200007A20100000625840013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC00BCFDE220009C007200048035000003AAF980012BC2100000F7E0400007BF020000063CB8001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E4001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C075FA05FC005C87FF70030FF1E300025C074C00BBC67A60009206830004E071E80003A7B8400C6FE5500009B5EAB000532DA300003EDDB0001357B120000EE375000081597000006840C00B8701660008F9E360004D10E8800039F910001246C280000E0D4200007A201000006258400138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC00BA603B40009123A30004E003900003AAF9800127C8BC0000E35BC00007BF020000063CB80013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E40013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E40002487B800001DA290000110F5800000C6840000443D60000031A10000018D0800000120C00BD1337A0009C840F0004E4207800040ACB800127C07C0000F440200007A2010000063CB80013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E40013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C0016280D6000126ABF00009355F800007A4CC00024D57E00001E93300000F499800000C68400028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC00028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E4074219370005A498B1002E60D56800238600C00C3FC78C0009701D30004E071E80003A7B8400C3FC78C0009701D30004E071E80003A7B840014CB68C0000FB76C000081597000006840C00B4F8BAA0008AE8AE000482F03000035DAC80013443A20000E7E4400007A20100000625840013443A20000E7E4400007A20100000625840002101CE00001AC9D00000ED82800000ACBC00B65BB040008BF5D600048D3A000003650580013800E40000EABE600007BF020000063CB80013800E40000EABE600007BF020000063CB800021BCB800001B64800000F499800000B1E40013800E40000EABE600007BF020000063CB800021BCB800001B64800000F499800000B1E400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C00BA14E6E000996918000494CAB00003C070000139081E000102B2E00007A2010000063CB800139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E400139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0015AE1B600011EB21000087395800006E7BC00024D57E00001E93300000F499800000C68400024D57E00001E93300000F499800000C6840000443D6000003931000001C9880000014CC00024D57E00001E93300000F499800000C6840000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E400B6FCB14000901D920004CB48C00003C070000132D2300000F01C00000815970000063CB800132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00153043200010921700008F590800006E7BC00023D64200001B9EF00000F499800000C68400023D64200001B9EF00000F499800000C68400003D2660000031A1000001C9880000014CC00023D64200001B9EF00000F499800000C68400003D2660000031A1000001C9880000014CC00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E400156B1BA00011CEC500008E7628000076C14000239D8A00001DB0500000ED82800000C684000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C48B9E3BF203875AD8001C9D6B0C8015C98AB4073F87D760058FAF16002D24C5880021715480760B2E14005ACF069002E43FFB800227644C00BBC349A0008D3E4A000480EC9000039CA2407CAA3AFA006022C800030FF1E300024A140C00C6FE5500009633510004CB48C00003DA3AC00C9793E6000984F900004E420780003F11C40013DBB96000101D2100008E76280000679BC0726362520057E50FB002CD21300002151A6C00B66A72C00089067100045FAEB0000382EAC00BB6C9920008D35860004891D180003A73C800127FFA60000F01C000008490B800006069400C8A435C00097A9EB0004E003900003EDDB00013EBA90000102B2E00008F590800006840C001453F620001080E700009355F800006B27400028D26E00001DB0500000ED82800000ACBC074DB8422006022C80002D4E82500024F36E400B795D540009701D30004574570000382EAC00BC5A7EA0009B5EAB00047CF1B00003A73C800122BA840000F01C00000780E0000006069400C9793E6000A65B460004D10E880003EDDB000138C306000102B2E000081597000006840C0013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC00B7B31C600097A9EB00045ECAC800038FCEC0011BC6D60000EABE60000755F3000005E7A4001288A5A0000F610300007B0818000063CB800020F7EC00001B9EF00000DCF7800000A0B4001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C073EA628A005ACF06900301164000024F36E400B646B580008D551B0004B80E98000382EAC00BA513F0000911FA40004DAF5580003A73C800120C48E0000DD9F40000780E0000006069400C6FE5500009B5EAB000532DA300003EDDB0001357B120000EE375000081597000006840C00138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC00B56C5FC0008D35860004BD4F5800038FCEC00118FA600000D77150000755F3000005E7A4001237EF80000E081A00007B0818000063CB80001EC206000018F2E00000DCF7800000A0B40013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E40002487B800001DA290000110F5800000C6840000443D60000031A10000018D0800000120C00B81E794000984F900004C27C800003EDDB00011936300000E7E44000073F22000005E7A400122E4480000F1516000078A8B0000063CB80001E2A2C000018F2E00000C797000000A0B40013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C0013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C00028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E4072919C6E0058FAF16002D8984100022CB40000C04590000093CDB90004B80E98000382EAC00B7F4FF80008D551B0004903418000367F4400136BD560000E9CF20000780E0000006069400C3FC78C0009701D30004E071E80003A7B840014CB68C0000FB76C000081597000006840C0013443A20000E7E4400007A20100000625840002101CE00001AC9D00000ED82800000ACBC00B297E3800089067100046F1A5000034D97C0012F53D60000E3F3B0000755F3000005E7A40011F58440000D7715000071ADE000005B8600001EC206000018F2E00000DCF7800000A0B40013800E40000EABE600007BF020000063CB800021BCB800001B64800000F499800000B1E400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C00B650374000963351000477BB400003A73C8001309F200000FB76C000073F22000005E7A400120C3C80000EE3750000706A1000005B8600001E2A2C000018F2E00000C797000000A0B400139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00024D57E00001E93300000F499800000C6840000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E400B3B0DB20008D3E4A0004B19A880003A73C80012C66A20000E9CF200007DBB6000005E7A40011BD9EA0000DD9F40000771BA800005B8600001DC6EA000016E1800000C797000000A0B400132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00023D64200001B9EF00000F499800000C68400003D2660000031A1000001C9880000014CC00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E4001368C5A000101D21000080E90800006B274000203A4200001AC9D00000D64E800000B1E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C070835BBC0057262AD002C4C61E00021A2F5800B5AEDFA0008B2D00000470C0180003493E000C04590000093CDB90004B80E98000382EAC00136BD560000E9CF20000780E0000006069400C04590000093CDB90004B80E98000382EAC00136BD560000E9CF20000780E000000606940014CB68C0000FB76C000081597000006840C0002101CE00001AC9D00000ED82800000ACBC00AE3270C00085469B00044259200003257040011A95540000D365F00006CA0B00000572C40012F53D60000E3F3B0000755F3000005E7A40001EC206000018F2E00000DCF7800000A0B40012F53D60000E3F3B0000755F3000005E7A40001EC206000018F2E00000DCF7800000A0B400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C00B217CDE00092850300044E5E60000382EAC0011C4B5A0000E9EE100006BB5900000572C4001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B4001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E400B04D30200089D9130004942818000382EAC00119377A0000D9FD1000074F7080000572C40012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B40012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C0012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E400130BA320000FC47100007E238800006840C0001DC4DA00001896100000C4B0800000A0B4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C00ACBF34E00085C55200044F7C080003493E0001250A060000E0BAB000074F7080000572C4001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B4001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B40001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B40001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C0001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C000036C90000002C790000018D0800000120C00000726200000053300000029980000001E40012B0E320000F68EB000075BD080000606940001F88E200001A10300000C4B0800000A0B40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C0001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C00003593A000002C7900000163C800000120C00000634200000053300000029980000001E40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C00003593A000002C7900000163C800000120C00000634200000053300000029980000001E400003593A000002C7900000163C800000120C00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C00125A5BE0000E728900007B47580000606940001ED1D60000181A500000D081800000A0B40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C0001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00003420600000282D00000163C800000120C0000058F200000048300000029980000001E40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00003420600000282D00000163C800000120C0000058F200000048300000029980000001E400003420600000282D00000163C800000120C0000058F200000048300000029980000001E40000058F200000048300000029980000001E4000000A6600000007900000003C800000002C0001F276E000019E6F00000CF37800000ACBC000033CDE000002B2F000001597800000120C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E4000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E400000565E00000048300000024180000001E400000090600000007900000003C800000002C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E400000565E00000048300000024180000001E400000090600000007900000003C800000002C00000565E00000048300000024180000001E400000090600000007900000003C800000002C00000090600000007900000003C800000002C0000000F200000000B00000000580000000065
  | 11 => 0x2128EAEA5E05E1C378AC0BE73F5D3802135B5D143017161BB808710371C0111814F14002E90DA403083E589A808884818401157D5DD6002F710FBC0460057C5800C119A8000188C900E000479C51030DB026F9008989092E0117DB9756002FE251D8046DC3D27000C3AECFA0018EE0E4800048D2198047687544800C57261600194BBC2C0004A1544800665465300012D93AC000293E95000006DFC382FEFF69740086E2A99B01128FDD9C002EEEF91004599767C000C0106D200187AAC5C000477F3A00467CB756000C2D901B0018F8FA9A00049240A800653A74B00012A5FEA00028DAF0000006CF28004748ABF9800C515F5100194B2BE20004A14EC80067164F280012FE7DD00029B94D000006F4378006880D3100013422CE0002A92C400000718760000BA915000001F183800003E307000000A5D6830DB026F90091E44B9001153527D2003355DC7C046019171800D0FC94200184EE14C000477F3A0046D06B66800D3ED8E10018BBC6A600049240A800639D94700012A5FEA000254BFD400006CF28004791CE36000D65910A00190490D20004A14EC8006553D2780012FE7DD00025FCFBA00006F437800667518E00013422CE000268459C0000718760000A41F1480001F183800003E307000000A5D6804748ABF9800D587E080018EA887400049CA7580065016DF80012EFF9300025DFF2600006EEF980066BE2D7800135106100026A20C2000071E564000A50E5F80001F46A000003E8D4000000A6CE00068AD9F400013AEDAA000275DB5400007414D8000A94D7B80002014E000004029C000000AB1A0000B9BE2A0000233D600000467AC000000BBF20000119EB0000002EFC8000005DF90000000FA983083E589A808AD9152C0123C89720003355DC7C04595AB4E000C553F4B001A1F9284000477F3A004628E6C3000C7A40C9001A7DB1C200049240A800630BC760001160F89000254BFD400006CF280046D06B66800C9A38B3001ACB22140004A14EC800647832600011A76A600025FCFBA00006F43780064F2EE280011C694D000268459C00007187600009A116700001C61D800003E307000000A5D680467CB756000C8B829E001AB0FC1000049CA7580064072A300011932CB00025DFF2600006EEF9800651D5F100011CFB4F00026A20C2000071E5640009A883080001C795900003E8D4000000A6CE00066BE2D7800121923F000275DB5400007414D80009D76D500001D053600004029C000000AB1A0000A84AEB00001EFDF70000467AC000000BBF20000119EB0000002EFC8000005DF90000000FA98047687544800D65910A001ACB221400050433A000641C91900012BA8E200025751C400006EEF980064F2EE280012FB9E300025F73C6000071E56400097DCF180001C7959000038F2B200000A6CE000667518E000134B53E0002696A7C00007414D80009A5A9F00001D053600003A0A6C00000AB1A0000A3D62F00001EFDF700003DFBEE00000BBF200000F7EFB800002EFC8000005DF90000000FA98006880D3100013AEDAA000275DB5400007671D80009D76D500001D9C7600003B38EC00000AEA58000A84AEB00001FD76300003FAEC600000C11A00000FEBB1800003046800000608D00000010178000B9BE2A0000232944000046528800000D57800001194A200000355E0000006ABC00000011CA00001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B83017161BB80889CD7E60116ABF4180030C56C48048F225C8000CD5771F001A1F9284000477F3A004595AB4E000C3B015800192296BA00044E7B140069F6C70800124902A000254BFD400006CF280046019171800C4F842000195BB02E0004598698006B2C88500012853B200025FCFBA00006F437800641C919000113C2E80002418B00000069A6400009A116700001C61D800003E307000000A5D6804599767C000C3CF6BF00193996E80004535DFC006AC3F0400012729D600025DFF2600006EEF980064072A3000113932B000241AEAA000069B0640009A883080001C795900003E8D4000000A6CE00065016DF800116260D000248E46E00006AF8AC0009D76D500001D053600004029C000000AB1A00009D76D500001D053600004029C000000AB1A0000119EB0000002EFC8000005DF90000000FA98046DC3D27000D3ED8E10019640B560004B6F9B4006B2C8850001410CE800025751C400006EEF9800647832600012CC29600023B9D42000069B06400097DCF180001C7959000038F2B200000A6CE0006553D2780012FB9E30002410F2A00006AF8AC0009A5A9F00001D053600003A0A6C00000AB1A00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA980067164F2800135106100024B4A1C00006CE7280009D76D500001D9C7600003B38EC00000AEA580009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D00000010178000A94D7B80001FD76300003FAEC600000BBAA80001194A200000355E0000006ABC00000011CA00001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B80460057C5800C90EDF3001A7DB1C20004B6F9B40069F6C7080012DBE6D00028219D000006EEF9800630BC7600011A75BF000259852C000069B06400096614B00001A6C19000038F2B200000A6CE000639D94700011C46E200025F73C600006AF8AC00097DCF180001ABE2B00003A0A6C00000AB1A000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA9800653A74B00012102E700026A20C200006CE7280009A883080001B39CA00003B38EC00000AEA580009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D00000010178000A50E5F80001D033100003FAEC600000BBAA80000FEBB1800002EEAA000006ABC00000011CA00000FEBB1800002EEAA000006ABC00000011CA000001AAF000000047280000008E5000000017B800665465300013422CE000268459C00007414D80009A116700001D053600003A0A6C00000AEA580009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C0000010178000A41F1480001EFDF700003DFBEE00000BBAA80000F7EFB800002EEAA000005DD540000011CA00000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8000BA91500000233D600000467AC000000D5780000119EB000000355E0000006ABC00000014400000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B00000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D8000000002402F9CFD74E0086FB4A320111BC0D48002FABB530045AAFD06000C38C52C0018DB580A00043B5248048F225C8000CD5771F001A1F9284000477F3A00069F6C70800124902A000254BFD400006CF2800454D49F4800C2A88D20018CC734000043A924C0065902D5800117DCB800023CDCF200006889A0006B2C88500012853B200025FCFBA00006F43780009A116700001C61D800003E307000000A5D68044A3F767000C0BAE38001891BF8800042FC2400064E65BA000115EC630002397F6C000067E99C006AC3F0400012729D600025DFF2600006EEF980009A883080001C795900003E8D4000000A6CE00063AA21D0001126C9E000233FD5C00006725D800092D28700001B0A8600003B5C80000009E4C00009D76D500001D053600004029C000000AB1A0000119EB0000002EFC8000005DF90000000FA98045F6E5D5800D0FC9420018CC7340000497F01800656EC0B80012EF83A000234DD66000067E99C006B2C8850001410CE800025751C400006EEF9800097DCF180001C7959000038F2B200000A6CE000641243480012BA8E200022DC20400006725D80009043CA80001B0A86000036150C000009E4C00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA9800652CAF880012EFF93000233FD5C0000684F8800092391B80001B690E000036D21C00000A07200009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D000000101780009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D000000101780001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B80455F5775800C66A9F2001A1F9284000497F01800648A5AE80011D477300025DF074000067E99C0069F6C7080012DBE6D00028219D000006EEF9800096614B00001A6C19000038F2B200000A6CE00062EF1A98001191B3400025751C400006725D80008EE75080001915CF000036150C000009E4C000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA980063E3EA680011BD76C00025DFF260000684F88000906BAA80001958B6000036D21C00000A07200009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D000000101780009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D000000101780000FEBB1800002EEAA000006ABC00000011CA000001AAF000000047280000008E5000000017B800652EF0B00012FE7DD00025FCFBA000071E5640009062C000001B0A86000036150C00000A07200009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8000AA4B1000002014E000004029C000000C11A0000100A70000003046800000608D00000011CA0000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B00000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D8000000002400446053C5000C2030660018DB580A000459055800687E4A1000125FC0600025DF074000067E99C00687E4A1000125FC0600025DF074000067E99C000A0867400001BBBE6000038F2B200000A6CE000613B853000110B538000234DD66000060820000095D471000019C976000036150C000009E4C000095D471000019C976000036150C000009E4C00000E829B000002AC68000005DF90000000FA980061EAB170001129AB90002397F6C00006144E8000977FC980001A13E2000036D21C00000A0720000977FC980001A13E2000036D21C00000A07200000ECE3B000002BA9600000608D00000010178000977FC980001A13E2000036D21C00000A07200000ECE3B000002BA9600000608D000000101780000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B80063B839200012A5FEA00023CDCF200006A745400097F3EE80001C7959000036150C00000A072000097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C000001017800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B8000A6E53400001F46A000003B5C8000000B0160000100A70000003046800000608D00000011CA0000100A70000003046800000608D00000011CA000001AAF00000005100000000A2000000001B00000100A70000003046800000608D00000011CA000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D800000000240006232403800119FC72000254BFD400006A7454000952FF500001A9D15000038F2B200000A0720000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C0000010178000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000A36BC000001D230800003E8D4000000B01600000FA350000002C05800000608D00000011CA00000FA350000002C05800000608D00000011CA00000182340000004728000000A2000000001B000000FA350000002C05800000608D00000011CA00000182340000004728000000A2000000001B000000182340000004728000000A2000000001B0000000288000000006C00000000D800000000240000A4FA5400001F183800003E307000000BBF200000F8C1C000002EFC8000005DF900000011CA00000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000302F0E1BC560085501848010DF69464002EF506DC0444E6BF3000BF6F5DB00184060CC00041D92800456C8A96000C306D740018CD53E400043AC3480064876F9800114C39A000233F8E4000066C7A8048F225C8000CD5771F001A1F9284000477F3A00069F6C70800124902A000254BFD400006CF280006B2C88500012853B200025FCFBA00006F43780009A116700001C61D800003E307000000A5D680437154CD800BD486580018175C7000041A101C0061E7B5F80010D3D660002253572000064306400645C14F000114B5AE000237AED8000067DE7000090817380001A9D1500003A4610000009B658006AC3F0400012729D600025DFF2600006EEF980009A883080001C795900003E8D4000000A6CE00009D76D500001D053600004029C000000AB1A0000119EB0000002EFC8000005DF90000000FA98044C48497000CD5771F00185511A4000481091800627C210000125FC060002216A7000006430640064D1C5980012DBE6D0002323668000067DE700008E237100001A9D150000353A2A000009B658006B2C8850001410CE800025751C400006EEF9800097DCF180001C7959000038F2B200000A6CE00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA9800628AFA880012729D6000224D93C00006583D80008B130680001A13E200003427C400000989A800090C91F80001B39CA000036739400000A07200000E8198800002C05800000580B0000000EAC80009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D000000101780001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B80444240C2000C306D740019AAEE3E00048109180061D80AC000114E8D000024BF80C00006430640063D206480011BAA9000025B7CDA000067DE700008D3ADF800018C0580000353A2A000009B6580069F6C7080012DBE6D00028219D000006EEF9800096614B00001A6C19000038F2B200000A6CE000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA9800616C80D800114B5AE00024E53AC00006583D800089C995800018222D00003427C400000989A80008E7DA78000190E4A000036739400000A07200000D9CE500000281C800000580B0000000EAC80009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D000000101780000FEBB1800002EEAA000006ABC00000011CA000001AAF000000047280000008E5000000017B80062B930B00012853B2000250A76400006EEF9800089E174000019C97600003392EC00000989A80008E34A680001ABE2B0000357C5600000A07200000D5F1580000281C80000050390000000EAC80009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B80009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D800000000240043881B8E000BF6F5DB0018718A5800044420400066ABB8F800120424600024BF80C00006430640062A9FA5800114E8D000023A8EE60000617FDC00096DF36800019F79C0000353A2A000009B65800687E4A1000125FC0600025DF074000067E99C000A0867400001BBBE6000038F2B200000A6CE000095D471000019C976000036150C000009E4C00000E829B000002AC68000005DF90000000FA9800600836900010D3D6600022BD8C600005ED9200009394EB00001960F600003427C400000989A80008C9965800018222D000032B16C00000945980000D9CE500000281C800000580B0000000EAC8000977FC980001A13E2000036D21C00000A07200000ECE3B000002BA9600000608D000000101780000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B80061D767D000124902A00022FB970000067DE700009429D900001BBBE600003392EC00000989A80008D3B5300001A6C190000322B9E00000945980000D5F1580000281C80000050390000000EAC800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B8000100A70000003046800000608D00000011CA000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D80000000024000608CD40000114C39A0002492054000067DE70000924815000019F79C00003777CC00000989A80008B07C4800018C058000034D83200000945980000D360C80000251660000050390000000EAC8000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000FA350000002C05800000608D00000011CA00000182340000004728000000A2000000001B000000182340000004728000000A2000000001B0000000288000000006C00000000D80000000024000096C9D600001C61D8000038C3B000000AB1A00000E30EC000002AC6800000558D000000101780000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000300426B6BA2800BBD41B70017D5DA980004230D5800618AD89000111081000022C82AC00005E60D00066ABB8F800120424600024BF80C000064306400096DF36800019F79C0000353A2A000009B6580066ABB8F800120424600024BF80C000064306400096DF36800019F79C0000353A2A000009B658000A0867400001BBBE6000038F2B200000A6CE00000E829B000002AC68000005DF90000000FA98005DDDF220001068407000217E12000005AC6300008A6BBF800017B648000030A274000008DE780009394EB00001960F600003427C400000989A80000D9CE500000281C800000580B0000000EAC80009394EB00001960F600003427C400000989A80000D9CE500000281C800000580B0000000EAC80000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B8005FC4A3B00011DFCE800021D492600006430640008B30D3000019FA670000304100000008DE780009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B80009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B800001AAF00000005100000000A2000000001B0000000288000000006C00000000D800000000240005EE21F780010EB0D200023BF9D0000064306400089CF628000185FF7000033F4CE000008DE78000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC8000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000182340000004728000000A2000000001B0000000288000000006C00000000D800000000240000942A8900001BD0DE000037A1BC00000A6CE00000D34C80000027930000004F260000000EAC80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D800000000240000000360000000009000000001200000000030005D21B4800010764A000021DA92400005E60D00008EFE740000190C19000033F4CE000008DE780008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B80008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B8000015D4B000000405E0000008E5000000017B800000288000000006C00000000D80000000024000091A43300001B3CA000003444D0000009B6580000DE86F0000029B38000004F260000000EAC80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B8000015634000000405E00000080BC00000017B800000239400000006C00000000D8000000002400000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B8000015634000000405E00000080BC00000017B800000239400000006C00000000D800000000240000015634000000405E00000080BC00000017B800000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000300008F38A2000019B1EA0000367940000009B6580000D9E500000026D960000053670000000EAC80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B8000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D8000000002400000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B8000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D800000000240000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D80000000024000000202F00000005EE0000000D8000000002400000003600000000090000000012000000000300000DBF87000002975A0000052EB4000000FA98000014BAD0000003EA60000007D4C00000017B8000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000001F5300000005EE0000000BDC00000002400000002F7000000009000000001200000000030000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000001F5300000005EE0000000BDC00000002400000002F7000000009000000001200000000030000001F5300000005EE0000000BDC00000002400000002F70000000090000000012000000000300000002F7000000009000000001200000000030000000048000000000C000000001800000000067
  | 12 => 0x2B03E3D0D80381953F64C38B6DFDCBC048CCB7640393D08CA1C049EC9C40004AC72B838005DEAE6D839B47A361C04AA88DE2804BC891E2C005F8B33D404C6A32760006116BD3C0062A2617400083D86B03A1425B82C04B2C27CA804C618D2C400605DF0D004D482538800624975A400640C143000085E72C004DD43A1A00063198FD8006565BE60000880A5080066778AB80008A484500009635C580000B8DFB83913198440049D7806A004B0DE8018005E9DD80004C05987F00060A02B40006265EBF000083AF15004CEAAC7600061EA5E20006439AECC000867962400657B05C800088F7B7800094F2A000000B7520004DB82DF000062F3C73C006569EA680008811B7400673343A80008B4F16800097DE9500000BAEA90006885C36C0008D1D76C0009ABFA580000BE75B8000A84E1680000CF25080000CF250800000FEF283A1425B82C04F5C3A55004BBA098300066B62E0404C6F26780006865C7DC0061C324D800083AF15004D3F449500069C113E0006356368400086796240063FAE27800088F7B7800088F7B780000B7520004E01CD730006ADE3B24006463B0D80008811B740065905F100008B4F1680008B4F1680000BAEA9000669F07080008D1D76C0008D1D76C0000BE75B8000958E41C0000CF25080000CF250800000FEF2804DB82DF00006A7D604800640319040008792A2C0065452DEC0008AED7940008AED7940000BA68F80066E5E6280008D85A440008D85A440000BF0B6C000965BD1C0000D047800000D0478000001005800068B4BF10000900659400090065940000C2751000099F57FC0000D545900000D5459000001067D0000A7AEA900000E884F80000E884F8000011E2D80000E884F8000011E2D8000011E2D8000001603839B47A361C04BD940E4C04F5C3A5500066B62E0404C033E9C800630F76AC006865C7DC00083AF15004C96CCF48006420F9480069C113E000086796240063713E60000806ADAC00088F7B780000B7520004D3F4495000650D878C006ADE3B240008811B740064C25AE0000824A6840008B4F1680000BAEA900065358C2800083227180008D1D76C0000BE75B80008D1D76C0000BE75B80000CF250800000FEF2804CEAAC76000649FE354006A7D60480008792A2C00645A57D400081C145C0008AED7940000BA68F800655F9960000836319C0008D85A440000BF0B6C0008D85A440000BF0B6C0000D0478000001005800066E5E628000855D2FC00090065940000C2751000090065940000C275100000D5459000001067D000099194600000CE92940000E884F8000011E2D80000E884F8000011E2D8000011E2D8000001603804DD43A1A0006ADE3B24006ADE3B24000926ED8800646C217C0008982F240008982F240000BA68F80065358C280008B411F80008B411F80000BF0B6C0008B411F80000BF0B6C0000BF0B6C000010058000669F07080008D624F80008D624F80000C275100008D624F80000C275100000C2751000001067D000095568980000CE92940000CE9294000011E2D80000CE9294000011E2D8000011E2D80000016038006885C36C000900659400090065940000C61F8000090065940000C61F800000C61F80000010B84000099194600000D3CF340000D3CF3400001257080000D3CF34000012570800001257080000016928000A7AEA900000E816100000E816100000141D380000E816100000141D380000141D380000018C180000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E78393D08CA1C04AB8C1B9004C187CA94006204B33C04F5C3A5500066B62E04006865C7DC00083AF15004C033E9C800624E30AC0064CC6D580007F59D780069C113E0000867962400088F7B780000B7520004C6F267800062E5B7A800659EF4B40008086EC8006ADE3B240008811B740008B4F1680000BAEA9000646C217C0007F7678400084FDCE80000B255F80008D1D76C0000BE75B80000CF250800000FEF2804C05987F000625B389800652049380007FDEA5C006A7D60480008792A2C0008AED7940000BA68F800645A57D40007F642D00008508FA80000B26A140008D85A440000BF0B6C0000D0478000001005800065452DEC000808274800086959480000B4707400090065940000C275100000D5459000001067D000090065940000C275100000D5459000001067D00000E884F8000011E2D8000011E2D8000001603804D48253880069C113E00065BE0DC80008A59DD8006ADE3B24000926ED880008982F240000BA68F80064C25AE000089FBBE000083BC9D80000B26A140008B411F80000BF0B6C0000BF0B6C00001005800065905F100008B411F800084E9B280000B470740008D624F80000C275100000C2751000001067D00008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D8000001603800673343A80008D85A44000871826C0000B7735000090065940000C61F800000C61F80000010B84000090065940000C61F800000C61F80000010B8400000D3CF3400001257080000125708000001692800099F57FC0000D3CF340000D3CF34000011DD280000E816100000141D380000141D380000018C180000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E7804C6A327600064C8B1080069C113E00008A59DD80069C113E00008A59DD8000926ED880000BA68F80063713E60000824991C00089FBBE00000B26A1400089FBBE00000B26A140000BF0B6C00001005800063FAE2780008314E5C0008B411F80000B470740008B411F80000B470740000C2751000001067D00008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D8000001603800657B05C8000851998C0008D85A440000B773500008D85A440000B773500000C61F80000010B8400008D85A440000B773500000C61F80000010B8400000C61F80000010B84000001257080000016928000965BD1C0000C286BC0000D3CF34000011DD280000D3CF34000011DD280000141D380000018C180000D3CF34000011DD280000141D380000018C180000141D380000018C180000018C180000001E780066778AB80008D1D76C0008D1D76C0000C275100008D1D76C0000C275100000C27510000010B8400008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B8400000016928000958E41C0000CE92940000CE9294000011DD280000CE9294000011DD28000011DD280000018C180000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E78000A84E1680000E884F80000E884F80000141D380000E884F80000141D380000141D38000001BE440000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A438B6DFDCBC049E60882404ADA1D810005FFBEA8C04C187CA9400623C35DC0063C4341C0007D501D804F5C3A5500066B62E04006865C7DC00083AF1500069C113E0000867962400088F7B780000B7520004BBA098300061D45D4400638EE0140007D415000065BE0DC8000812955C00083FA5700000B092A0006ADE3B240008811B740008B4F1680000BAEA900008D1D76C0000BE75B80000CF250800000FEF2804B0DE80180060EDFF2C0062B455900007C19F4C00652049380008055A0C00083441940000AF9A9C006A7D60480008792A2C0008AED7940000BA68F80008D85A440000BF0B6C0000D04780000010058000640319040007EE67E00008226CC00000AE7ED8000871826C0000B64C600000C69FE000000F476000090065940000C275100000D5459000001067D00000E884F8000011E2D8000011E2D8000001603804C618D2C4006865C7DC00638EE014000871205000659EF4B40008ADF1700008246C6C0000AF9A9C006ADE3B24000926ED880008982F240000BA68F80008B411F80000BF0B6C0000BF0B6C0000100580006463B0D80008982F2400080D25580000AE7ED800084E9B280000B64C600000B64C6000000F47600008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D80000016038006569EA680008AED7940008226CC00000B04F9800086959480000B89A400000B89A4000000F788800090065940000C61F800000C61F80000010B8400000D3CF3400001257080000125708000001692800090065940000C61F800000C61F80000010B8400000D3CF340000125708000012570800000169280000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E7804BC891E2C006390BC00006865C7DC00087120500064CC6D5800083717C00008ADF1700000AF9A9C0069C113E00008A59DD8000926ED880000BA68F800089FBBE00000B26A140000BF0B6C0000100580006356368400081B7C6C0008982F240000AE7ED800083BC9D80000AA348C0000B64C6000000F47600008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D80000016038006439AECC00082E27C00008AED7940000B04F980008508FA80000ABDAD80000B89A4000000F78880008D85A440000B773500000C61F80000010B8400000C61F80000010B840000012570800000169280008D85A440000B773500000C61F80000010B8400000C61F80000010B840000012570800000169280000D3CF34000011DD280000141D380000018C180000141D380000018C180000018C180000001E78006565BE600008B4F1680008B4F1680000BF0B6C00084FDCE80000B64C600000B64C6000000F78880008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780009ABFA580000D545900000D5459000001257080000D54590000012570800001257080000018C180000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A404AC72B8380061872C740063C4341C0008076720006865C7DC00087120500008ADF1700000AF9A9C006865C7DC00087120500008ADF1700000AF9A9C000926ED880000BA68F80000BF0B6C00001005800061C324D80007E28B5C0008246C6C0000A43A000008982F240000AE7ED80000B64C6000000F47600008982F240000AE7ED80000B64C6000000F47600000C2751000001067D0000011E2D80000016038006265EBF00007EF85E000083441940000A56E580008AED7940000B04F980000B89A4000000F78880008AED7940000B04F980000B89A4000000F78880000C61F80000010B840000012570800000169280008AED7940000B04F980000B89A4000000F78880000C61F80000010B840000012570800000169280000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E7800640C143000088F7B7800083FA5700000B399F40008B4F1680000BF0B6C0000B64C6000000F78880008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E7800097DE9500000D047800000C69FE0000010DAC80000D54590000012570800001257080000018C180000D54590000012570800001257080000018C180000141D38000001BE44000001BE4400000022540000D54590000012570800001257080000018C180000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A40062A26174000821699000088F7B780000B399F400088F7B780000B399F40000BF0B6C00000F788800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B840000001692800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800094F2A000000C338780000D04780000010DAC80000D04780000010DAC800001257080000018C180000D04780000010DAC800001257080000018C1800001257080000018C18000001BE4400000022540000D04780000010DAC800001257080000018C1800001257080000018C18000001BE44000000225400001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A40009635C580000CF25080000CF2508000011E2D80000CF2508000011E2D8000011E2D80000018C180000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C1800000022540000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A40000000034381953F64C0490DC5958049E608824005EA898C004AB8C1B90006054E1880061872C740007A2863804BD940E4C0061FE75A8006390BC000007D426E00064C8B1080007FD6F7800082169900000ADD50804F5C3A5500066B62E04006865C7DC00083AF1500069C113E0000867962400088F7B780000B75200006ADE3B240008811B740008B4F1680000BAEA900008D1D76C0000BE75B80000CF250800000FEF28049D7806A0005F53E0200060EDFF2C00079C9B5000625B38980007CA69500007EF85E00000A9D37400649FE3540007FD1A9000082E27C00000AF8AF8000851998C0000B399F40000C3387800000F0458006A7D60480008792A2C0008AED7940000BA68F80008D85A440000BF0B6C0000D04780000010058000090065940000C275100000D5459000001067D00000E884F8000011E2D8000011E2D8000001603804B2C27CA80066B62E040061D45D4400084A3BF00062E5B7A800087120500007E28B5C0000A9D37400650D878C0008A59DD800081B7C6C0000AF8AF80008314E5C0000B399F40000B399F400000F0458006ADE3B24000926ED880008982F240000BA68F80008B411F80000BF0B6C0000BF0B6C00001005800008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D800000160380062F3C73C0008792A2C0007EE67E00000ABE97800080827480000B04F980000B04F9800000EC5C8000855D2FC0000B773500000B7735000000F78880000C286BC000010DAC8000010DAC80000014BE800090065940000C61F800000C61F80000010B8400000D3CF340000125708000012570800000169280000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E7804AA88DE280061FE75A80066B62E0400084A3BF000624E30AC0007FE57D800087120500000A9D374006420F94800082C21600008A59DD80000AF8AF8000824991C0000A815980000B399F400000F04580069C113E00008A59DD8000926ED880000BA68F800089FBBE00000B26A140000BF0B6C00001005800008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D800000160380061EA5E200007FD1A900008792A2C0000ABE9780007F642D00000A449A40000B04F9800000EC5C8000836319C0000AA0A180000B7735000000F78880000B7735000000F7888000010DAC80000014BE80008D85A440000B773500000C61F80000010B8400000C61F80000010B840000012570800000169280000D3CF34000011DD280000141D380000018C180000141D380000018C180000018C180000001E780063198FD80008811B740008811B740000BA68F80007F767840000AE7ED80000AE7ED800000EC5C800083227180000B470740000B4707400000F78880000B4707400000F788800000F78880000014BE80008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A4049EC9C400006054E18800623C35DC0007E3DEFC0066B62E0400084A3BF000087120500000A9D37400630F76AC0007FE57D800083717C00000A5B39C0008A59DD80000AF8AF80000B399F400000F0458006865C7DC00087120500008ADF1700000AF9A9C000926ED880000BA68F80000BF0B6C00001005800008982F240000AE7ED80000B64C6000000F47600000C2751000001067D0000011E2D800000160380060A02B400007CA69500008055A0C0000A19BB00008792A2C0000ABE9780000B04F9800000EC5C800081C145C0000A449A40000ABDAD800000E66B80000B7735000000F7888000010DAC80000014BE80008AED7940000B04F980000B89A4000000F78880000C61F80000010B840000012570800000169280000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E7800624975A40008679624000812955C0000AF8AF80008811B740000BA68F80000AE7ED800000EC5C8000824A6840000B26A140000AA348C00000E66B80000B4707400000F788800000F78880000014BE80008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000D54590000012570800001257080000018C180000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A4006116BD3C0007FD6F7800086796240000AF8AF800086796240000AF8AF80000BA68F800000EC5C8000806ADAC0000A815980000B26A1400000E66B80000B26A1400000E66B800000F78880000014BE800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780000D04780000010DAC800001257080000018C1800001257080000018C18000001BE44000000225400001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A40008A484500000BE75B80000BE75B800001067D00000BE75B800001067D000001067D000000169280000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A40000000034048CCB7640005EA898C0005FFBEA8C0007ABBDB8006204B33C0007E3DEFC00080767200000A0D7100066B62E0400084A3BF000087120500000A9D3740008A59DD80000AF8AF80000B399F400000F04580066B62E0400084A3BF000087120500000A9D3740008A59DD80000AF8AF80000B399F400000F0458000926ED880000BA68F80000BF0B6C00001005800000C2751000001067D0000011E2D80000016038005E9DD80000079C9B500007C19F4C00009B45880007FDEA5C0000A19BB00000A56E5800000DD3400008792A2C0000ABE9780000B04F9800000EC5C80000B7735000000F7888000010DAC80000014BE80008792A2C0000ABE9780000B04F9800000EC5C80000B7735000000F7888000010DAC80000014BE80000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E7800605DF0D000083AF1500007D415000000A9D3740008086EC80000AF9A9C0000A43A0000000DD3400008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A4005F8B33D40007D426E000083AF1500000A9D3740007F59D780000A5B39C0000AF9A9C00000DD34000086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE800086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE80000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE80000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A4000880A5080000BAEA900000BAEA9000001005800000B255F800000F476000000F47600000014BE80000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A40000000034005DEAE6D80007A286380007D501D80000A0D71000083AF1500000A9D3740000AF9A9C00000DD34000083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE800083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE80000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E7800083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE80000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E780000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E78000010B84000000169280000018C180000001E78000001BE440000002254000000225400000002A400085E72C00000B752000000B092A000000F04580000BAEA90000010058000000F47600000014BE80000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E780000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800001067D0000001692800000169280000001E780000018C180000002254000000225400000002A40000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800001067D0000001692800000169280000001E780000018C180000002254000000225400000002A400001067D0000001692800000169280000001E780000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A4000000003400083D86B00000ADD5080000B7520000000F04580000B7520000000F045800001005800000014BE80000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E780000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A40000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A400001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A400000169280000001E78000000225400000002A4000000225400000002A400000002A400000000340000B8DFB800000FEF2800000FEF28000001603800000FEF28000001603800000160380000001E7800000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000160380000001E780000001E7800000002A40000001E7800000002A400000002A4000000003400000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000160380000001E780000001E7800000002A40000001E7800000002A400000002A4000000003400000160380000001E780000001E7800000002A40000001E7800000002A400000002A400000000340000001E7800000002A400000002A4000000003400000002A40000000034000000003400000000068
  | _ => 0

def BaseTab (u : Fin 2048) : Prop :=
    G 0 u = tb (tabT 0) u.val

instance (u : Fin 2048) : Decidable (BaseTab u) := by
  unfold BaseTab
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_0 : ∀ i : Fin 32, BaseTab (idIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_1 : ∀ i : Fin 32, BaseTab (idIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_2 : ∀ i : Fin 32, BaseTab (idIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_3 : ∀ i : Fin 32, BaseTab (idIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_4 : ∀ i : Fin 32, BaseTab (idIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_5 : ∀ i : Fin 32, BaseTab (idIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_6 : ∀ i : Fin 32, BaseTab (idIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_7 : ∀ i : Fin 32, BaseTab (idIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_8 : ∀ i : Fin 32, BaseTab (idIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_9 : ∀ i : Fin 32, BaseTab (idIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_10 : ∀ i : Fin 32, BaseTab (idIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_11 : ∀ i : Fin 32, BaseTab (idIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_12 : ∀ i : Fin 32, BaseTab (idIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_13 : ∀ i : Fin 32, BaseTab (idIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_14 : ∀ i : Fin 32, BaseTab (idIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_15 : ∀ i : Fin 32, BaseTab (idIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_16 : ∀ i : Fin 32, BaseTab (idIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_17 : ∀ i : Fin 32, BaseTab (idIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_18 : ∀ i : Fin 32, BaseTab (idIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_19 : ∀ i : Fin 32, BaseTab (idIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_20 : ∀ i : Fin 32, BaseTab (idIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_21 : ∀ i : Fin 32, BaseTab (idIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_22 : ∀ i : Fin 32, BaseTab (idIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_23 : ∀ i : Fin 32, BaseTab (idIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_24 : ∀ i : Fin 32, BaseTab (idIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_25 : ∀ i : Fin 32, BaseTab (idIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_26 : ∀ i : Fin 32, BaseTab (idIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_27 : ∀ i : Fin 32, BaseTab (idIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_28 : ∀ i : Fin 32, BaseTab (idIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_29 : ∀ i : Fin 32, BaseTab (idIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_30 : ∀ i : Fin 32, BaseTab (idIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_31 : ∀ i : Fin 32, BaseTab (idIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_32 : ∀ i : Fin 32, BaseTab (idIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_33 : ∀ i : Fin 32, BaseTab (idIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_34 : ∀ i : Fin 32, BaseTab (idIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_35 : ∀ i : Fin 32, BaseTab (idIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_36 : ∀ i : Fin 32, BaseTab (idIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_37 : ∀ i : Fin 32, BaseTab (idIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_38 : ∀ i : Fin 32, BaseTab (idIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_39 : ∀ i : Fin 32, BaseTab (idIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_40 : ∀ i : Fin 32, BaseTab (idIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_41 : ∀ i : Fin 32, BaseTab (idIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_42 : ∀ i : Fin 32, BaseTab (idIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_43 : ∀ i : Fin 32, BaseTab (idIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_44 : ∀ i : Fin 32, BaseTab (idIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_45 : ∀ i : Fin 32, BaseTab (idIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_46 : ∀ i : Fin 32, BaseTab (idIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_47 : ∀ i : Fin 32, BaseTab (idIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_48 : ∀ i : Fin 32, BaseTab (idIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_49 : ∀ i : Fin 32, BaseTab (idIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_50 : ∀ i : Fin 32, BaseTab (idIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_51 : ∀ i : Fin 32, BaseTab (idIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_52 : ∀ i : Fin 32, BaseTab (idIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_53 : ∀ i : Fin 32, BaseTab (idIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_54 : ∀ i : Fin 32, BaseTab (idIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_55 : ∀ i : Fin 32, BaseTab (idIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_56 : ∀ i : Fin 32, BaseTab (idIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_57 : ∀ i : Fin 32, BaseTab (idIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_58 : ∀ i : Fin 32, BaseTab (idIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_59 : ∀ i : Fin 32, BaseTab (idIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_60 : ∀ i : Fin 32, BaseTab (idIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_61 : ∀ i : Fin 32, BaseTab (idIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_62 : ∀ i : Fin 32, BaseTab (idIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T_chunk_63 : ∀ i : Fin 32, BaseTab (idIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T (u : Fin 2048) : G 0 u = tb (tabT 0) u.val := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, BaseTab (idIndex k i) := by
    intro k
    fin_cases k
    · exact base_T_chunk_0
    · exact base_T_chunk_1
    · exact base_T_chunk_2
    · exact base_T_chunk_3
    · exact base_T_chunk_4
    · exact base_T_chunk_5
    · exact base_T_chunk_6
    · exact base_T_chunk_7
    · exact base_T_chunk_8
    · exact base_T_chunk_9
    · exact base_T_chunk_10
    · exact base_T_chunk_11
    · exact base_T_chunk_12
    · exact base_T_chunk_13
    · exact base_T_chunk_14
    · exact base_T_chunk_15
    · exact base_T_chunk_16
    · exact base_T_chunk_17
    · exact base_T_chunk_18
    · exact base_T_chunk_19
    · exact base_T_chunk_20
    · exact base_T_chunk_21
    · exact base_T_chunk_22
    · exact base_T_chunk_23
    · exact base_T_chunk_24
    · exact base_T_chunk_25
    · exact base_T_chunk_26
    · exact base_T_chunk_27
    · exact base_T_chunk_28
    · exact base_T_chunk_29
    · exact base_T_chunk_30
    · exact base_T_chunk_31
    · exact base_T_chunk_32
    · exact base_T_chunk_33
    · exact base_T_chunk_34
    · exact base_T_chunk_35
    · exact base_T_chunk_36
    · exact base_T_chunk_37
    · exact base_T_chunk_38
    · exact base_T_chunk_39
    · exact base_T_chunk_40
    · exact base_T_chunk_41
    · exact base_T_chunk_42
    · exact base_T_chunk_43
    · exact base_T_chunk_44
    · exact base_T_chunk_45
    · exact base_T_chunk_46
    · exact base_T_chunk_47
    · exact base_T_chunk_48
    · exact base_T_chunk_49
    · exact base_T_chunk_50
    · exact base_T_chunk_51
    · exact base_T_chunk_52
    · exact base_T_chunk_53
    · exact base_T_chunk_54
    · exact base_T_chunk_55
    · exact base_T_chunk_56
    · exact base_T_chunk_57
    · exact base_T_chunk_58
    · exact base_T_chunk_59
    · exact base_T_chunk_60
    · exact base_T_chunk_61
    · exact base_T_chunk_62
    · exact base_T_chunk_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he, BaseTab] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

def StepTab (u : Fin 2048) : Prop :=
    ∀ n < (12 : ℕ), (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) = tb (tabT (n + 1)) u.val

instance (u : Fin 2048) : Decidable (StepTab u) := by
  unfold StepTab
  infer_instance

-- The state index is split into its quotient and remainder modulo 16.
-- Each block checks the table equation for all 16 remainder values.

private def stepIndex (k : Fin 128) (i : Fin 16) : Fin 2048 :=
  ⟨16 * k.val + i.val, by have hk := k.isLt; have hi := i.isLt; omega⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock0 : ∀ i : Fin 16, StepTab (stepIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock1 : ∀ i : Fin 16, StepTab (stepIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock2 : ∀ i : Fin 16, StepTab (stepIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock3 : ∀ i : Fin 16, StepTab (stepIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock4 : ∀ i : Fin 16, StepTab (stepIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock5 : ∀ i : Fin 16, StepTab (stepIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock6 : ∀ i : Fin 16, StepTab (stepIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock7 : ∀ i : Fin 16, StepTab (stepIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock8 : ∀ i : Fin 16, StepTab (stepIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock9 : ∀ i : Fin 16, StepTab (stepIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock10 : ∀ i : Fin 16, StepTab (stepIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock11 : ∀ i : Fin 16, StepTab (stepIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock12 : ∀ i : Fin 16, StepTab (stepIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock13 : ∀ i : Fin 16, StepTab (stepIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock14 : ∀ i : Fin 16, StepTab (stepIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock15 : ∀ i : Fin 16, StepTab (stepIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock16 : ∀ i : Fin 16, StepTab (stepIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock17 : ∀ i : Fin 16, StepTab (stepIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock18 : ∀ i : Fin 16, StepTab (stepIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock19 : ∀ i : Fin 16, StepTab (stepIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock20 : ∀ i : Fin 16, StepTab (stepIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock21 : ∀ i : Fin 16, StepTab (stepIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock22 : ∀ i : Fin 16, StepTab (stepIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock23 : ∀ i : Fin 16, StepTab (stepIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock24 : ∀ i : Fin 16, StepTab (stepIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock25 : ∀ i : Fin 16, StepTab (stepIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock26 : ∀ i : Fin 16, StepTab (stepIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock27 : ∀ i : Fin 16, StepTab (stepIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock28 : ∀ i : Fin 16, StepTab (stepIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock29 : ∀ i : Fin 16, StepTab (stepIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock30 : ∀ i : Fin 16, StepTab (stepIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock31 : ∀ i : Fin 16, StepTab (stepIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock32 : ∀ i : Fin 16, StepTab (stepIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock33 : ∀ i : Fin 16, StepTab (stepIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock34 : ∀ i : Fin 16, StepTab (stepIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock35 : ∀ i : Fin 16, StepTab (stepIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock36 : ∀ i : Fin 16, StepTab (stepIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock37 : ∀ i : Fin 16, StepTab (stepIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock38 : ∀ i : Fin 16, StepTab (stepIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock39 : ∀ i : Fin 16, StepTab (stepIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock40 : ∀ i : Fin 16, StepTab (stepIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock41 : ∀ i : Fin 16, StepTab (stepIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock42 : ∀ i : Fin 16, StepTab (stepIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock43 : ∀ i : Fin 16, StepTab (stepIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock44 : ∀ i : Fin 16, StepTab (stepIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock45 : ∀ i : Fin 16, StepTab (stepIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock46 : ∀ i : Fin 16, StepTab (stepIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock47 : ∀ i : Fin 16, StepTab (stepIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock48 : ∀ i : Fin 16, StepTab (stepIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock49 : ∀ i : Fin 16, StepTab (stepIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock50 : ∀ i : Fin 16, StepTab (stepIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock51 : ∀ i : Fin 16, StepTab (stepIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock52 : ∀ i : Fin 16, StepTab (stepIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock53 : ∀ i : Fin 16, StepTab (stepIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock54 : ∀ i : Fin 16, StepTab (stepIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock55 : ∀ i : Fin 16, StepTab (stepIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock56 : ∀ i : Fin 16, StepTab (stepIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock57 : ∀ i : Fin 16, StepTab (stepIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock58 : ∀ i : Fin 16, StepTab (stepIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock59 : ∀ i : Fin 16, StepTab (stepIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock60 : ∀ i : Fin 16, StepTab (stepIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock61 : ∀ i : Fin 16, StepTab (stepIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock62 : ∀ i : Fin 16, StepTab (stepIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock63 : ∀ i : Fin 16, StepTab (stepIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock64 : ∀ i : Fin 16, StepTab (stepIndex 64 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock65 : ∀ i : Fin 16, StepTab (stepIndex 65 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock66 : ∀ i : Fin 16, StepTab (stepIndex 66 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock67 : ∀ i : Fin 16, StepTab (stepIndex 67 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock68 : ∀ i : Fin 16, StepTab (stepIndex 68 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock69 : ∀ i : Fin 16, StepTab (stepIndex 69 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock70 : ∀ i : Fin 16, StepTab (stepIndex 70 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock71 : ∀ i : Fin 16, StepTab (stepIndex 71 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock72 : ∀ i : Fin 16, StepTab (stepIndex 72 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock73 : ∀ i : Fin 16, StepTab (stepIndex 73 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock74 : ∀ i : Fin 16, StepTab (stepIndex 74 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock75 : ∀ i : Fin 16, StepTab (stepIndex 75 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock76 : ∀ i : Fin 16, StepTab (stepIndex 76 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock77 : ∀ i : Fin 16, StepTab (stepIndex 77 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock78 : ∀ i : Fin 16, StepTab (stepIndex 78 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock79 : ∀ i : Fin 16, StepTab (stepIndex 79 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock80 : ∀ i : Fin 16, StepTab (stepIndex 80 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock81 : ∀ i : Fin 16, StepTab (stepIndex 81 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock82 : ∀ i : Fin 16, StepTab (stepIndex 82 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock83 : ∀ i : Fin 16, StepTab (stepIndex 83 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock84 : ∀ i : Fin 16, StepTab (stepIndex 84 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock85 : ∀ i : Fin 16, StepTab (stepIndex 85 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock86 : ∀ i : Fin 16, StepTab (stepIndex 86 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock87 : ∀ i : Fin 16, StepTab (stepIndex 87 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock88 : ∀ i : Fin 16, StepTab (stepIndex 88 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock89 : ∀ i : Fin 16, StepTab (stepIndex 89 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock90 : ∀ i : Fin 16, StepTab (stepIndex 90 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock91 : ∀ i : Fin 16, StepTab (stepIndex 91 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock92 : ∀ i : Fin 16, StepTab (stepIndex 92 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock93 : ∀ i : Fin 16, StepTab (stepIndex 93 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock94 : ∀ i : Fin 16, StepTab (stepIndex 94 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock95 : ∀ i : Fin 16, StepTab (stepIndex 95 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock96 : ∀ i : Fin 16, StepTab (stepIndex 96 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock97 : ∀ i : Fin 16, StepTab (stepIndex 97 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock98 : ∀ i : Fin 16, StepTab (stepIndex 98 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock99 : ∀ i : Fin 16, StepTab (stepIndex 99 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock100 : ∀ i : Fin 16, StepTab (stepIndex 100 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock101 : ∀ i : Fin 16, StepTab (stepIndex 101 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock102 : ∀ i : Fin 16, StepTab (stepIndex 102 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock103 : ∀ i : Fin 16, StepTab (stepIndex 103 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock104 : ∀ i : Fin 16, StepTab (stepIndex 104 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock105 : ∀ i : Fin 16, StepTab (stepIndex 105 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock106 : ∀ i : Fin 16, StepTab (stepIndex 106 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock107 : ∀ i : Fin 16, StepTab (stepIndex 107 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock108 : ∀ i : Fin 16, StepTab (stepIndex 108 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock109 : ∀ i : Fin 16, StepTab (stepIndex 109 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock110 : ∀ i : Fin 16, StepTab (stepIndex 110 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock111 : ∀ i : Fin 16, StepTab (stepIndex 111 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock112 : ∀ i : Fin 16, StepTab (stepIndex 112 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock113 : ∀ i : Fin 16, StepTab (stepIndex 113 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock114 : ∀ i : Fin 16, StepTab (stepIndex 114 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock115 : ∀ i : Fin 16, StepTab (stepIndex 115 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock116 : ∀ i : Fin 16, StepTab (stepIndex 116 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock117 : ∀ i : Fin 16, StepTab (stepIndex 117 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock118 : ∀ i : Fin 16, StepTab (stepIndex 118 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock119 : ∀ i : Fin 16, StepTab (stepIndex 119 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock120 : ∀ i : Fin 16, StepTab (stepIndex 120 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock121 : ∀ i : Fin 16, StepTab (stepIndex 121 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock122 : ∀ i : Fin 16, StepTab (stepIndex 122 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock123 : ∀ i : Fin 16, StepTab (stepIndex 123 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock124 : ∀ i : Fin 16, StepTab (stepIndex 124 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock125 : ∀ i : Fin 16, StepTab (stepIndex 125 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock126 : ∀ i : Fin 16, StepTab (stepIndex 126 i) := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def stepBlock127 : ∀ i : Fin 16, StepTab (stepIndex 127 i) := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem step_T (u : Fin 2048) : StepTab u := by
  have allBlocks (k : Fin 128) (i : Fin 16) : StepTab (stepIndex k i) := by
    fin_cases k
    · exact stepBlock0 i
    · exact stepBlock1 i
    · exact stepBlock2 i
    · exact stepBlock3 i
    · exact stepBlock4 i
    · exact stepBlock5 i
    · exact stepBlock6 i
    · exact stepBlock7 i
    · exact stepBlock8 i
    · exact stepBlock9 i
    · exact stepBlock10 i
    · exact stepBlock11 i
    · exact stepBlock12 i
    · exact stepBlock13 i
    · exact stepBlock14 i
    · exact stepBlock15 i
    · exact stepBlock16 i
    · exact stepBlock17 i
    · exact stepBlock18 i
    · exact stepBlock19 i
    · exact stepBlock20 i
    · exact stepBlock21 i
    · exact stepBlock22 i
    · exact stepBlock23 i
    · exact stepBlock24 i
    · exact stepBlock25 i
    · exact stepBlock26 i
    · exact stepBlock27 i
    · exact stepBlock28 i
    · exact stepBlock29 i
    · exact stepBlock30 i
    · exact stepBlock31 i
    · exact stepBlock32 i
    · exact stepBlock33 i
    · exact stepBlock34 i
    · exact stepBlock35 i
    · exact stepBlock36 i
    · exact stepBlock37 i
    · exact stepBlock38 i
    · exact stepBlock39 i
    · exact stepBlock40 i
    · exact stepBlock41 i
    · exact stepBlock42 i
    · exact stepBlock43 i
    · exact stepBlock44 i
    · exact stepBlock45 i
    · exact stepBlock46 i
    · exact stepBlock47 i
    · exact stepBlock48 i
    · exact stepBlock49 i
    · exact stepBlock50 i
    · exact stepBlock51 i
    · exact stepBlock52 i
    · exact stepBlock53 i
    · exact stepBlock54 i
    · exact stepBlock55 i
    · exact stepBlock56 i
    · exact stepBlock57 i
    · exact stepBlock58 i
    · exact stepBlock59 i
    · exact stepBlock60 i
    · exact stepBlock61 i
    · exact stepBlock62 i
    · exact stepBlock63 i
    · exact stepBlock64 i
    · exact stepBlock65 i
    · exact stepBlock66 i
    · exact stepBlock67 i
    · exact stepBlock68 i
    · exact stepBlock69 i
    · exact stepBlock70 i
    · exact stepBlock71 i
    · exact stepBlock72 i
    · exact stepBlock73 i
    · exact stepBlock74 i
    · exact stepBlock75 i
    · exact stepBlock76 i
    · exact stepBlock77 i
    · exact stepBlock78 i
    · exact stepBlock79 i
    · exact stepBlock80 i
    · exact stepBlock81 i
    · exact stepBlock82 i
    · exact stepBlock83 i
    · exact stepBlock84 i
    · exact stepBlock85 i
    · exact stepBlock86 i
    · exact stepBlock87 i
    · exact stepBlock88 i
    · exact stepBlock89 i
    · exact stepBlock90 i
    · exact stepBlock91 i
    · exact stepBlock92 i
    · exact stepBlock93 i
    · exact stepBlock94 i
    · exact stepBlock95 i
    · exact stepBlock96 i
    · exact stepBlock97 i
    · exact stepBlock98 i
    · exact stepBlock99 i
    · exact stepBlock100 i
    · exact stepBlock101 i
    · exact stepBlock102 i
    · exact stepBlock103 i
    · exact stepBlock104 i
    · exact stepBlock105 i
    · exact stepBlock106 i
    · exact stepBlock107 i
    · exact stepBlock108 i
    · exact stepBlock109 i
    · exact stepBlock110 i
    · exact stepBlock111 i
    · exact stepBlock112 i
    · exact stepBlock113 i
    · exact stepBlock114 i
    · exact stepBlock115 i
    · exact stepBlock116 i
    · exact stepBlock117 i
    · exact stepBlock118 i
    · exact stepBlock119 i
    · exact stepBlock120 i
    · exact stepBlock121 i
    · exact stepBlock122 i
    · exact stepBlock123 i
    · exact stepBlock124 i
    · exact stepBlock125 i
    · exact stepBlock126 i
    · exact stepBlock127 i
  have hu := u.isLt
  have recover : stepIndex ⟨u.val / 16, by omega⟩ ⟨u.val % 16, by omega⟩ = u := by
    apply Fin.ext
    change 16 * (u.val / 16) + u.val % 16 = u.val
    omega
  simpa only [recover] using allBlocks ⟨u.val / 16, by omega⟩ ⟨u.val % 16, by omega⟩

theorem step_all (n : ℕ) (hn : n < 12) (u : Fin 2048) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := step_T u n hn

theorem G_eq_T (n : ℕ) (hn : n ≤ 12) : ∀ u : Fin 2048, G n u = tb (tabT n) u.val := by
  induction n with
  | zero => exact base_T
  | succ n ih =>
    intro u
    rw [G_succ]
    have ih' := ih (by omega)
    simp only [ih']
    exact step_all n (by omega) u

def DiffTab (u : Fin 2048) : Prop :=
    tb (tabT 12) u.val + 66 * tb (tabT 10) u.val + 495 * tb (tabT 8) u.val + 924 * tb (tabT 6) u.val + 495 * tb (tabT 4) u.val + 66 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      12 * tb (tabT 11) u.val + 220 * tb (tabT 9) u.val + 792 * tb (tabT 7) u.val + 792 * tb (tabT 5) u.val + 220 * tb (tabT 3) u.val + 12 * tb (tabT 1) u.val

instance (u : Fin 2048) : Decidable (DiffTab u) := by
  unfold DiffTab
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_0 : ∀ i : Fin 32, DiffTab (idIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_1 : ∀ i : Fin 32, DiffTab (idIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_2 : ∀ i : Fin 32, DiffTab (idIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_3 : ∀ i : Fin 32, DiffTab (idIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_4 : ∀ i : Fin 32, DiffTab (idIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_5 : ∀ i : Fin 32, DiffTab (idIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_6 : ∀ i : Fin 32, DiffTab (idIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_7 : ∀ i : Fin 32, DiffTab (idIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_8 : ∀ i : Fin 32, DiffTab (idIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_9 : ∀ i : Fin 32, DiffTab (idIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_10 : ∀ i : Fin 32, DiffTab (idIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_11 : ∀ i : Fin 32, DiffTab (idIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_12 : ∀ i : Fin 32, DiffTab (idIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_13 : ∀ i : Fin 32, DiffTab (idIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_14 : ∀ i : Fin 32, DiffTab (idIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_15 : ∀ i : Fin 32, DiffTab (idIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_16 : ∀ i : Fin 32, DiffTab (idIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_17 : ∀ i : Fin 32, DiffTab (idIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_18 : ∀ i : Fin 32, DiffTab (idIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_19 : ∀ i : Fin 32, DiffTab (idIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_20 : ∀ i : Fin 32, DiffTab (idIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_21 : ∀ i : Fin 32, DiffTab (idIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_22 : ∀ i : Fin 32, DiffTab (idIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_23 : ∀ i : Fin 32, DiffTab (idIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_24 : ∀ i : Fin 32, DiffTab (idIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_25 : ∀ i : Fin 32, DiffTab (idIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_26 : ∀ i : Fin 32, DiffTab (idIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_27 : ∀ i : Fin 32, DiffTab (idIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_28 : ∀ i : Fin 32, DiffTab (idIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_29 : ∀ i : Fin 32, DiffTab (idIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_30 : ∀ i : Fin 32, DiffTab (idIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_31 : ∀ i : Fin 32, DiffTab (idIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_32 : ∀ i : Fin 32, DiffTab (idIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_33 : ∀ i : Fin 32, DiffTab (idIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_34 : ∀ i : Fin 32, DiffTab (idIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_35 : ∀ i : Fin 32, DiffTab (idIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_36 : ∀ i : Fin 32, DiffTab (idIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_37 : ∀ i : Fin 32, DiffTab (idIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_38 : ∀ i : Fin 32, DiffTab (idIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_39 : ∀ i : Fin 32, DiffTab (idIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_40 : ∀ i : Fin 32, DiffTab (idIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_41 : ∀ i : Fin 32, DiffTab (idIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_42 : ∀ i : Fin 32, DiffTab (idIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_43 : ∀ i : Fin 32, DiffTab (idIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_44 : ∀ i : Fin 32, DiffTab (idIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_45 : ∀ i : Fin 32, DiffTab (idIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_46 : ∀ i : Fin 32, DiffTab (idIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_47 : ∀ i : Fin 32, DiffTab (idIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_48 : ∀ i : Fin 32, DiffTab (idIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_49 : ∀ i : Fin 32, DiffTab (idIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_50 : ∀ i : Fin 32, DiffTab (idIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_51 : ∀ i : Fin 32, DiffTab (idIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_52 : ∀ i : Fin 32, DiffTab (idIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_53 : ∀ i : Fin 32, DiffTab (idIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_54 : ∀ i : Fin 32, DiffTab (idIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_55 : ∀ i : Fin 32, DiffTab (idIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_56 : ∀ i : Fin 32, DiffTab (idIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_57 : ∀ i : Fin 32, DiffTab (idIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_58 : ∀ i : Fin 32, DiffTab (idIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_59 : ∀ i : Fin 32, DiffTab (idIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_60 : ∀ i : Fin 32, DiffTab (idIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_61 : ∀ i : Fin 32, DiffTab (idIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_62 : ∀ i : Fin 32, DiffTab (idIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base_chunk_63 : ∀ i : Fin 32, DiffTab (idIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base (u : Fin 2048) : tb (tabT 12) u.val + 66 * tb (tabT 10) u.val + 495 * tb (tabT 8) u.val + 924 * tb (tabT 6) u.val + 495 * tb (tabT 4) u.val + 66 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      12 * tb (tabT 11) u.val + 220 * tb (tabT 9) u.val + 792 * tb (tabT 7) u.val + 792 * tb (tabT 5) u.val + 220 * tb (tabT 3) u.val + 12 * tb (tabT 1) u.val := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, DiffTab (idIndex k i) := by
    intro k
    fin_cases k
    · exact tab_base_chunk_0
    · exact tab_base_chunk_1
    · exact tab_base_chunk_2
    · exact tab_base_chunk_3
    · exact tab_base_chunk_4
    · exact tab_base_chunk_5
    · exact tab_base_chunk_6
    · exact tab_base_chunk_7
    · exact tab_base_chunk_8
    · exact tab_base_chunk_9
    · exact tab_base_chunk_10
    · exact tab_base_chunk_11
    · exact tab_base_chunk_12
    · exact tab_base_chunk_13
    · exact tab_base_chunk_14
    · exact tab_base_chunk_15
    · exact tab_base_chunk_16
    · exact tab_base_chunk_17
    · exact tab_base_chunk_18
    · exact tab_base_chunk_19
    · exact tab_base_chunk_20
    · exact tab_base_chunk_21
    · exact tab_base_chunk_22
    · exact tab_base_chunk_23
    · exact tab_base_chunk_24
    · exact tab_base_chunk_25
    · exact tab_base_chunk_26
    · exact tab_base_chunk_27
    · exact tab_base_chunk_28
    · exact tab_base_chunk_29
    · exact tab_base_chunk_30
    · exact tab_base_chunk_31
    · exact tab_base_chunk_32
    · exact tab_base_chunk_33
    · exact tab_base_chunk_34
    · exact tab_base_chunk_35
    · exact tab_base_chunk_36
    · exact tab_base_chunk_37
    · exact tab_base_chunk_38
    · exact tab_base_chunk_39
    · exact tab_base_chunk_40
    · exact tab_base_chunk_41
    · exact tab_base_chunk_42
    · exact tab_base_chunk_43
    · exact tab_base_chunk_44
    · exact tab_base_chunk_45
    · exact tab_base_chunk_46
    · exact tab_base_chunk_47
    · exact tab_base_chunk_48
    · exact tab_base_chunk_49
    · exact tab_base_chunk_50
    · exact tab_base_chunk_51
    · exact tab_base_chunk_52
    · exact tab_base_chunk_53
    · exact tab_base_chunk_54
    · exact tab_base_chunk_55
    · exact tab_base_chunk_56
    · exact tab_base_chunk_57
    · exact tab_base_chunk_58
    · exact tab_base_chunk_59
    · exact tab_base_chunk_60
    · exact tab_base_chunk_61
    · exact tab_base_chunk_62
    · exact tab_base_chunk_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he, DiffTab] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

theorem G_base : ∀ u : Fin 2048,
    G 12 u + 66 * G 10 u + 495 * G 8 u + 924 * G 6 u + 495 * G 4 u + 66 * G 2 u + G 0 u =
      12 * G 11 u + 220 * G 9 u + 792 * G 7 u + 792 * G 5 u + 220 * G 3 u + 12 * G 1 u := by
  intro u
  rw [G_eq_T 12 (by norm_num) u, G_eq_T 11 (by norm_num) u, G_eq_T 10 (by norm_num) u, G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 2048,
    G (m + 12) u + 66 * G (m + 10) u + 495 * G (m + 8) u + 924 * G (m + 6) u + 495 * G (m + 4) u + 66 * G (m + 2) u + G m u =
      12 * G (m + 11) u + 220 * G (m + 9) u + 792 * G (m + 7) u + 792 * G (m + 5) u + 220 * G (m + 3) u + 12 * G (m + 1) u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega, show m + 1 + 10 = (m + 10) + 1 by omega, show m + 1 + 11 = (m + 11) + 1 by omega, show m + 1 + 12 = (m + 12) + 1 by omega]
    rw [G_succ (m + 12), G_succ (m + 10), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m, G_succ (m + 11), G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 12) + 66 * a (m + 10) + 495 * a (m + 8) + 924 * a (m + 6) + 495 * a (m + 4) + 66 * a (m + 2) + a m =
      12 * a (m + 11) + 220 * a (m + 9) + 792 * a (m + 7) + 792 * a (m + 5) + 220 * a (m + 3) + 12 * a (m + 1) := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 2047

theorem G_vals : G 1 2047 = 15 ∧ G 2 2047 = 4999 ∧ G 3 2047 = 267004 ∧ G 4 2047 = 5207128 ∧ G 5 2047 = 55191061 ∧ G 6 2047 = 389769865 ∧ G 7 2047 = 2062131616 ∧ G 8 2047 = 8794967112 ∧ G 9 2047 = 31750272891 ∧ G 10 2047 = 100377252987 ∧ G 11 2047 = 284840809660 ∧ G 12 2047 = 738995422048 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num), G_eq_T 10 (by norm_num), G_eq_T 11 (by norm_num), G_eq_T 12 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 15 ∧ a 2 = 4999 ∧ a 3 = 267004 ∧ a 4 = 5207128 ∧ a 5 = 55191061 ∧ a 6 = 389769865 ∧ a 7 = 2062131616 ∧ a 8 = 8794967112 ∧ a 9 = 31750272891 ∧ a 10 = 100377252987 ∧ a 11 = 284840809660 ∧ a 12 = 738995422048 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  norm_num

theorem recurrence (n : ℕ) (hn : 13 ≤ n) :
    (a n : ℚ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 12) + 66 * a (m + 10) + 495 * a (m + 8) + 924 * a (m + 6) + 495 * a (m + 4) + 66 * a (m + 2) + a m : ℤ) : ℚ) =
      ((12 * a (m + 11) + 220 * a (m + 9) + 792 * a (m + 7) + 792 * a (m + 5) + 220 * a (m + 3) + 12 * a (m + 1) : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 12 - 1 = (m + 11) by omega, show m + 12 - 2 = (m + 10) by omega, show m + 12 - 3 = (m + 9) by omega, show m + 12 - 4 = (m + 8) by omega, show m + 12 - 5 = (m + 7) by omega, show m + 12 - 6 = (m + 6) by omega, show m + 12 - 7 = (m + 5) by omega, show m + 12 - 8 = (m + 4) by omega, show m + 12 - 9 = (m + 3) by omega, show m + 12 - 10 = (m + 2) by omega, show m + 12 - 11 = (m + 1) by omega, show m + 12 - 12 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 12 : PowerSeries ℚ) =
      X * (15 + 4819 * X + 208006 * X ^ 2 + 2329714 * X ^ 3 + 9235434 * X ^ 4 + 14869326 * X ^ 5 + 10156734 * X ^ 6 + 2833778 * X ^ 7 + 273635 * X ^ 8 + 5339 * X ^ 9) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 12 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 12 * (PowerSeries.mk F * X ^ 1) + C 66 * (PowerSeries.mk F * X ^ 2) - C 220 * (PowerSeries.mk F * X ^ 3) + C 495 * (PowerSeries.mk F * X ^ 4) - C 792 * (PowerSeries.mk F * X ^ 5) + C 924 * (PowerSeries.mk F * X ^ 6) - C 792 * (PowerSeries.mk F * X ^ 7) + C 495 * (PowerSeries.mk F * X ^ 8) - C 220 * (PowerSeries.mk F * X ^ 9) + C 66 * (PowerSeries.mk F * X ^ 10) - C 12 * (PowerSeries.mk F * X ^ 11) + C 1 * (PowerSeries.mk F * X ^ 12) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (15 + 4819 * X + 208006 * X ^ 2 + 2329714 * X ^ 3 + 9235434 * X ^ 4 + 14869326 * X ^ 5 + 10156734 * X ^ 6 + 2833778 * X ^ 7 + 273635 * X ^ 8 + 5339 * X ^ 9) : ℚ⟦X⟧) =
      C 15 * X ^ 1 + C 4819 * X ^ 2 + C 208006 * X ^ 3 + C 2329714 * X ^ 4 + C 9235434 * X ^ 5 + C 14869326 * X ^ 6 + C 10156734 * X ^ 7 + C 2833778 * X ^ 8 + C 273635 * X ^ 9 + C 5339 * X ^ 10 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 13
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 13 := ⟨k - 13, by omega⟩
    have hr := recurrence (j + 13) (by omega)
    simp only [show j + 13 - 1 = j + 12 by omega, show j + 13 - 2 = j + 11 by omega, show j + 13 - 3 = j + 10 by omega, show j + 13 - 4 = j + 9 by omega, show j + 13 - 5 = j + 8 by omega, show j + 13 - 6 = j + 7 by omega, show j + 13 - 7 = j + 6 by omega, show j + 13 - 8 = j + 5 by omega, show j + 13 - 9 = j + 4 by omega, show j + 13 - 10 = j + 3 by omega, show j + 13 - 11 = j + 2 by omega, show j + 13 - 12 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 13 by omega,
      show 1 ≤ j + 13 by omega,
      show 2 ≤ j + 13 by omega,
      show 3 ≤ j + 13 by omega,
      show 4 ≤ j + 13 by omega,
      show 5 ≤ j + 13 by omega,
      show 6 ≤ j + 13 by omega,
      show 7 ≤ j + 13 by omega,
      show 8 ≤ j + 13 by omega,
      show 9 ≤ j + 13 by omega,
      show 10 ≤ j + 13 by omega,
      show 11 ≤ j + 13 by omega,
      show 12 ≤ j + 13 by omega,
      show j + 13 - 0 = j + 13 by omega,
      show j + 13 - 1 = j + 12 by omega,
      show j + 13 - 2 = j + 11 by omega,
      show j + 13 - 3 = j + 10 by omega,
      show j + 13 - 4 = j + 9 by omega,
      show j + 13 - 5 = j + 8 by omega,
      show j + 13 - 6 = j + 7 by omega,
      show j + 13 - 7 = j + 6 by omega,
      show j + 13 - 8 = j + 5 by omega,
      show j + 13 - 9 = j + 4 by omega,
      show j + 13 - 10 = j + 3 by omega,
      show j + 13 - 11 = j + 2 by omega,
      show j + 13 - 12 = j + 1 by omega,
      show ¬ (j + 13 = 1) by omega,
      show ¬ (j + 13 = 2) by omega,
      show ¬ (j + 13 = 3) by omega,
      show ¬ (j + 13 = 4) by omega,
      show ¬ (j + 13 = 5) by omega,
      show ¬ (j + 13 = 6) by omega,
      show ¬ (j + 13 = 7) by omega,
      show ¬ (j + 13 = 8) by omega,
      show ¬ (j + 13 = 9) by omega,
      show ¬ (j + 13 = 10) by omega,
      show ¬ (j + 13 < 1) by omega,
      show ¬ (j + 12 < 1) by omega,
      show ¬ (j + 11 < 1) by omega,
      show ¬ (j + 10 < 1) by omega,
      show ¬ (j + 9 < 1) by omega,
      show ¬ (j + 8 < 1) by omega,
      show ¬ (j + 7 < 1) by omega,
      show ¬ (j + 6 < 1) by omega,
      show ¬ (j + 5 < 1) by omega,
      show ¬ (j + 4 < 1) by omega,
      show ¬ (j + 3 < 1) by omega,
      show ¬ (j + 2 < 1) by omega,
      show ¬ (j + 1 < 1) by omega,
      if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a249966.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
