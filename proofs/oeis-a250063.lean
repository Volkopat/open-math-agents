import OMAStatements.S_oeis_a250063

/-!
A250063: exact eleven-position/five-window adaptation of the threshold-chain proof
by @Salofe for A250064, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
This follows our A249850 proof, PR #27268, with regenerated tables for this target.
Conjecture: Colin Barker (2017); registered statement: @clementtrecourt, PR #19401.
The finite tables certify a recurrence on every subset state; linearity then proves
it for all levels. All computations are kernel checked.
-/

namespace OMA.A250063

open OMA.S_oeis_a250063 Finset

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
def fget (f : Fin 11 → Bool) (k : ℕ) : Bool := if h : k < 11 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 11 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 7 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 11 → Bool) : Prop := ∀ i < (5 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 11 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 11 → Fin (n + 1)) (v : ℕ) : Fin 11 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 11 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250063.get x k ≤ n := by
  unfold OMA.S_oeis_a250063.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (5 : ℕ), cntW (fun _ => true) i = 7 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 11 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (5 : ℕ), ¬ Cy (fun t : Fin 7 => OMA.S_oeis_a250063.get x (i + t)) := by
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
  have step2 : ∀ i < (5 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 7 => OMA.S_oeis_a250063.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 11 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250063.get fget Lt
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

/-- The code of a set of positions. -/
def code (f : Fin 11 → Bool) : ℕ := ∑ p : Fin 11, if f p = true then 2 ^ p.val else 0

def idIndex (k : Fin 64) (i : Fin 32) : Fin 2048 := ⟨32 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩

set_option maxRecDepth 20000 in
abbrev code_row_chunk_0 : ∀ i : Fin 32, code (row (idIndex 0 i)) = (idIndex 0 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_1 : ∀ i : Fin 32, code (row (idIndex 1 i)) = (idIndex 1 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_2 : ∀ i : Fin 32, code (row (idIndex 2 i)) = (idIndex 2 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_3 : ∀ i : Fin 32, code (row (idIndex 3 i)) = (idIndex 3 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_4 : ∀ i : Fin 32, code (row (idIndex 4 i)) = (idIndex 4 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_5 : ∀ i : Fin 32, code (row (idIndex 5 i)) = (idIndex 5 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_6 : ∀ i : Fin 32, code (row (idIndex 6 i)) = (idIndex 6 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_7 : ∀ i : Fin 32, code (row (idIndex 7 i)) = (idIndex 7 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_8 : ∀ i : Fin 32, code (row (idIndex 8 i)) = (idIndex 8 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_9 : ∀ i : Fin 32, code (row (idIndex 9 i)) = (idIndex 9 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_10 : ∀ i : Fin 32, code (row (idIndex 10 i)) = (idIndex 10 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_11 : ∀ i : Fin 32, code (row (idIndex 11 i)) = (idIndex 11 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_12 : ∀ i : Fin 32, code (row (idIndex 12 i)) = (idIndex 12 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_13 : ∀ i : Fin 32, code (row (idIndex 13 i)) = (idIndex 13 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_14 : ∀ i : Fin 32, code (row (idIndex 14 i)) = (idIndex 14 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_15 : ∀ i : Fin 32, code (row (idIndex 15 i)) = (idIndex 15 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_16 : ∀ i : Fin 32, code (row (idIndex 16 i)) = (idIndex 16 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_17 : ∀ i : Fin 32, code (row (idIndex 17 i)) = (idIndex 17 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_18 : ∀ i : Fin 32, code (row (idIndex 18 i)) = (idIndex 18 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_19 : ∀ i : Fin 32, code (row (idIndex 19 i)) = (idIndex 19 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_20 : ∀ i : Fin 32, code (row (idIndex 20 i)) = (idIndex 20 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_21 : ∀ i : Fin 32, code (row (idIndex 21 i)) = (idIndex 21 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_22 : ∀ i : Fin 32, code (row (idIndex 22 i)) = (idIndex 22 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_23 : ∀ i : Fin 32, code (row (idIndex 23 i)) = (idIndex 23 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_24 : ∀ i : Fin 32, code (row (idIndex 24 i)) = (idIndex 24 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_25 : ∀ i : Fin 32, code (row (idIndex 25 i)) = (idIndex 25 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_26 : ∀ i : Fin 32, code (row (idIndex 26 i)) = (idIndex 26 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_27 : ∀ i : Fin 32, code (row (idIndex 27 i)) = (idIndex 27 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_28 : ∀ i : Fin 32, code (row (idIndex 28 i)) = (idIndex 28 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_29 : ∀ i : Fin 32, code (row (idIndex 29 i)) = (idIndex 29 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_30 : ∀ i : Fin 32, code (row (idIndex 30 i)) = (idIndex 30 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_31 : ∀ i : Fin 32, code (row (idIndex 31 i)) = (idIndex 31 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_32 : ∀ i : Fin 32, code (row (idIndex 32 i)) = (idIndex 32 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_33 : ∀ i : Fin 32, code (row (idIndex 33 i)) = (idIndex 33 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_34 : ∀ i : Fin 32, code (row (idIndex 34 i)) = (idIndex 34 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_35 : ∀ i : Fin 32, code (row (idIndex 35 i)) = (idIndex 35 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_36 : ∀ i : Fin 32, code (row (idIndex 36 i)) = (idIndex 36 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_37 : ∀ i : Fin 32, code (row (idIndex 37 i)) = (idIndex 37 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_38 : ∀ i : Fin 32, code (row (idIndex 38 i)) = (idIndex 38 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_39 : ∀ i : Fin 32, code (row (idIndex 39 i)) = (idIndex 39 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_40 : ∀ i : Fin 32, code (row (idIndex 40 i)) = (idIndex 40 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_41 : ∀ i : Fin 32, code (row (idIndex 41 i)) = (idIndex 41 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_42 : ∀ i : Fin 32, code (row (idIndex 42 i)) = (idIndex 42 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_43 : ∀ i : Fin 32, code (row (idIndex 43 i)) = (idIndex 43 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_44 : ∀ i : Fin 32, code (row (idIndex 44 i)) = (idIndex 44 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_45 : ∀ i : Fin 32, code (row (idIndex 45 i)) = (idIndex 45 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_46 : ∀ i : Fin 32, code (row (idIndex 46 i)) = (idIndex 46 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_47 : ∀ i : Fin 32, code (row (idIndex 47 i)) = (idIndex 47 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_48 : ∀ i : Fin 32, code (row (idIndex 48 i)) = (idIndex 48 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_49 : ∀ i : Fin 32, code (row (idIndex 49 i)) = (idIndex 49 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_50 : ∀ i : Fin 32, code (row (idIndex 50 i)) = (idIndex 50 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_51 : ∀ i : Fin 32, code (row (idIndex 51 i)) = (idIndex 51 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_52 : ∀ i : Fin 32, code (row (idIndex 52 i)) = (idIndex 52 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_53 : ∀ i : Fin 32, code (row (idIndex 53 i)) = (idIndex 53 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_54 : ∀ i : Fin 32, code (row (idIndex 54 i)) = (idIndex 54 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_55 : ∀ i : Fin 32, code (row (idIndex 55 i)) = (idIndex 55 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_56 : ∀ i : Fin 32, code (row (idIndex 56 i)) = (idIndex 56 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_57 : ∀ i : Fin 32, code (row (idIndex 57 i)) = (idIndex 57 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_58 : ∀ i : Fin 32, code (row (idIndex 58 i)) = (idIndex 58 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_59 : ∀ i : Fin 32, code (row (idIndex 59 i)) = (idIndex 59 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_60 : ∀ i : Fin 32, code (row (idIndex 60 i)) = (idIndex 60 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_61 : ∀ i : Fin 32, code (row (idIndex 61 i)) = (idIndex 61 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_62 : ∀ i : Fin 32, code (row (idIndex 62 i)) = (idIndex 62 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev code_row_chunk_63 : ∀ i : Fin 32, code (row (idIndex 63 i)) = (idIndex 63 i).val := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem code_row (u : Fin 2048) : code (row u) = u.val := by
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, code (row (idIndex k i)) = (idIndex k i).val := by
    intro k
    fin_cases k
    · exact code_row_chunk_0
    · exact code_row_chunk_1
    · exact code_row_chunk_2
    · exact code_row_chunk_3
    · exact code_row_chunk_4
    · exact code_row_chunk_5
    · exact code_row_chunk_6
    · exact code_row_chunk_7
    · exact code_row_chunk_8
    · exact code_row_chunk_9
    · exact code_row_chunk_10
    · exact code_row_chunk_11
    · exact code_row_chunk_12
    · exact code_row_chunk_13
    · exact code_row_chunk_14
    · exact code_row_chunk_15
    · exact code_row_chunk_16
    · exact code_row_chunk_17
    · exact code_row_chunk_18
    · exact code_row_chunk_19
    · exact code_row_chunk_20
    · exact code_row_chunk_21
    · exact code_row_chunk_22
    · exact code_row_chunk_23
    · exact code_row_chunk_24
    · exact code_row_chunk_25
    · exact code_row_chunk_26
    · exact code_row_chunk_27
    · exact code_row_chunk_28
    · exact code_row_chunk_29
    · exact code_row_chunk_30
    · exact code_row_chunk_31
    · exact code_row_chunk_32
    · exact code_row_chunk_33
    · exact code_row_chunk_34
    · exact code_row_chunk_35
    · exact code_row_chunk_36
    · exact code_row_chunk_37
    · exact code_row_chunk_38
    · exact code_row_chunk_39
    · exact code_row_chunk_40
    · exact code_row_chunk_41
    · exact code_row_chunk_42
    · exact code_row_chunk_43
    · exact code_row_chunk_44
    · exact code_row_chunk_45
    · exact code_row_chunk_46
    · exact code_row_chunk_47
    · exact code_row_chunk_48
    · exact code_row_chunk_49
    · exact code_row_chunk_50
    · exact code_row_chunk_51
    · exact code_row_chunk_52
    · exact code_row_chunk_53
    · exact code_row_chunk_54
    · exact code_row_chunk_55
    · exact code_row_chunk_56
    · exact code_row_chunk_57
    · exact code_row_chunk_58
    · exact code_row_chunk_59
    · exact code_row_chunk_60
    · exact code_row_chunk_61
    · exact code_row_chunk_62
    · exact code_row_chunk_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 11 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2 + m / 256 % 2 + m / 512 % 2 + m / 1024 % 2

def CntRow (u : Fin 2048) : Prop := cntW (row u) 0 = pcb (u.val &&& 127) ∧ cntW (row u) 1 = pcb (u.val &&& 254) ∧ cntW (row u) 2 = pcb (u.val &&& 508) ∧ cntW (row u) 3 = pcb (u.val &&& 1016) ∧ cntW (row u) 4 = pcb (u.val &&& 2032)

instance (u : Fin 2048) : Decidable (CntRow u) := by
  unfold CntRow
  infer_instance

set_option maxRecDepth 20000 in
abbrev cnt_row_block_0 : ∀ i : Fin 32, CntRow (idIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_1 : ∀ i : Fin 32, CntRow (idIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_2 : ∀ i : Fin 32, CntRow (idIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_3 : ∀ i : Fin 32, CntRow (idIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_4 : ∀ i : Fin 32, CntRow (idIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_5 : ∀ i : Fin 32, CntRow (idIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_6 : ∀ i : Fin 32, CntRow (idIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_7 : ∀ i : Fin 32, CntRow (idIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_8 : ∀ i : Fin 32, CntRow (idIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_9 : ∀ i : Fin 32, CntRow (idIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_10 : ∀ i : Fin 32, CntRow (idIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_11 : ∀ i : Fin 32, CntRow (idIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_12 : ∀ i : Fin 32, CntRow (idIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_13 : ∀ i : Fin 32, CntRow (idIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_14 : ∀ i : Fin 32, CntRow (idIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_15 : ∀ i : Fin 32, CntRow (idIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_16 : ∀ i : Fin 32, CntRow (idIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_17 : ∀ i : Fin 32, CntRow (idIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_18 : ∀ i : Fin 32, CntRow (idIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_19 : ∀ i : Fin 32, CntRow (idIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_20 : ∀ i : Fin 32, CntRow (idIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_21 : ∀ i : Fin 32, CntRow (idIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_22 : ∀ i : Fin 32, CntRow (idIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_23 : ∀ i : Fin 32, CntRow (idIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_24 : ∀ i : Fin 32, CntRow (idIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_25 : ∀ i : Fin 32, CntRow (idIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_26 : ∀ i : Fin 32, CntRow (idIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_27 : ∀ i : Fin 32, CntRow (idIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_28 : ∀ i : Fin 32, CntRow (idIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_29 : ∀ i : Fin 32, CntRow (idIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_30 : ∀ i : Fin 32, CntRow (idIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_31 : ∀ i : Fin 32, CntRow (idIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_32 : ∀ i : Fin 32, CntRow (idIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_33 : ∀ i : Fin 32, CntRow (idIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_34 : ∀ i : Fin 32, CntRow (idIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_35 : ∀ i : Fin 32, CntRow (idIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_36 : ∀ i : Fin 32, CntRow (idIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_37 : ∀ i : Fin 32, CntRow (idIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_38 : ∀ i : Fin 32, CntRow (idIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_39 : ∀ i : Fin 32, CntRow (idIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_40 : ∀ i : Fin 32, CntRow (idIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_41 : ∀ i : Fin 32, CntRow (idIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_42 : ∀ i : Fin 32, CntRow (idIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_43 : ∀ i : Fin 32, CntRow (idIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_44 : ∀ i : Fin 32, CntRow (idIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_45 : ∀ i : Fin 32, CntRow (idIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_46 : ∀ i : Fin 32, CntRow (idIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_47 : ∀ i : Fin 32, CntRow (idIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_48 : ∀ i : Fin 32, CntRow (idIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_49 : ∀ i : Fin 32, CntRow (idIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_50 : ∀ i : Fin 32, CntRow (idIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_51 : ∀ i : Fin 32, CntRow (idIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_52 : ∀ i : Fin 32, CntRow (idIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_53 : ∀ i : Fin 32, CntRow (idIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_54 : ∀ i : Fin 32, CntRow (idIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_55 : ∀ i : Fin 32, CntRow (idIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_56 : ∀ i : Fin 32, CntRow (idIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_57 : ∀ i : Fin 32, CntRow (idIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_58 : ∀ i : Fin 32, CntRow (idIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_59 : ∀ i : Fin 32, CntRow (idIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_60 : ∀ i : Fin 32, CntRow (idIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_61 : ∀ i : Fin 32, CntRow (idIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_62 : ∀ i : Fin 32, CntRow (idIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev cnt_row_block_63 : ∀ i : Fin 32, CntRow (idIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem cnt_row : ∀ u : Fin 2048, cntW (row u) 0 = pcb (u.val &&& 127) ∧ cntW (row u) 1 = pcb (u.val &&& 254) ∧ cntW (row u) 2 = pcb (u.val &&& 508) ∧ cntW (row u) 3 = pcb (u.val &&& 1016) ∧ cntW (row u) 4 = pcb (u.val &&& 2032) := by
  intro u
  have hall : ∀ k : Fin 64, ∀ i : Fin 32, CntRow (idIndex k i) := by
    intro k
    fin_cases k
    · exact cnt_row_block_0
    · exact cnt_row_block_1
    · exact cnt_row_block_2
    · exact cnt_row_block_3
    · exact cnt_row_block_4
    · exact cnt_row_block_5
    · exact cnt_row_block_6
    · exact cnt_row_block_7
    · exact cnt_row_block_8
    · exact cnt_row_block_9
    · exact cnt_row_block_10
    · exact cnt_row_block_11
    · exact cnt_row_block_12
    · exact cnt_row_block_13
    · exact cnt_row_block_14
    · exact cnt_row_block_15
    · exact cnt_row_block_16
    · exact cnt_row_block_17
    · exact cnt_row_block_18
    · exact cnt_row_block_19
    · exact cnt_row_block_20
    · exact cnt_row_block_21
    · exact cnt_row_block_22
    · exact cnt_row_block_23
    · exact cnt_row_block_24
    · exact cnt_row_block_25
    · exact cnt_row_block_26
    · exact cnt_row_block_27
    · exact cnt_row_block_28
    · exact cnt_row_block_29
    · exact cnt_row_block_30
    · exact cnt_row_block_31
    · exact cnt_row_block_32
    · exact cnt_row_block_33
    · exact cnt_row_block_34
    · exact cnt_row_block_35
    · exact cnt_row_block_36
    · exact cnt_row_block_37
    · exact cnt_row_block_38
    · exact cnt_row_block_39
    · exact cnt_row_block_40
    · exact cnt_row_block_41
    · exact cnt_row_block_42
    · exact cnt_row_block_43
    · exact cnt_row_block_44
    · exact cnt_row_block_45
    · exact cnt_row_block_46
    · exact cnt_row_block_47
    · exact cnt_row_block_48
    · exact cnt_row_block_49
    · exact cnt_row_block_50
    · exact cnt_row_block_51
    · exact cnt_row_block_52
    · exact cnt_row_block_53
    · exact cnt_row_block_54
    · exact cnt_row_block_55
    · exact cnt_row_block_56
    · exact cnt_row_block_57
    · exact cnt_row_block_58
    · exact cnt_row_block_59
    · exact cnt_row_block_60
    · exact cnt_row_block_61
    · exact cnt_row_block_62
    · exact cnt_row_block_63
  have hu := u.isLt
  have he : idIndex ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩ = u := by
    apply Fin.ext
    change 32 * (u.val / 32) + u.val % 32 = u.val
    omega
  simpa only [he, CntRow] using hall ⟨u.val / 32, by omega⟩ ⟨u.val % 32, Nat.mod_lt _ (by decide)⟩

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 127) ≤ 1 ∧ 3 ≤ pcb (t &&& 127)) ∧
    ¬ (pcb (s &&& 254) ≤ 1 ∧ 3 ≤ pcb (t &&& 254)) ∧
    ¬ (pcb (s &&& 508) ≤ 1 ∧ 3 ≤ pcb (t &&& 508)) ∧
    ¬ (pcb (s &&& 1016) ≤ 1 ∧ 3 ≤ pcb (t &&& 1016)) ∧
    ¬ (pcb (s &&& 2032) ≤ 1 ∧ 3 ≤ pcb (t &&& 2032)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (5 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 2048) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4]

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

/-! ### The recurrence -/

theorem G_succ (n : ℕ) (u : Fin 2048) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl

/-! Packed tables certify the recursion on every state. -/
/-- The low six bits record the slot width of this packed vector. -/
def tb (T w : ℕ) : ℕ := (T >>> (6 + (T % 64) * w)) % 2 ^ (T % 64)

def tabT : ℕ → ℕ
  | 0 => 0x5DFC0000000000000000000000000000000000000000000000000000000000001DFC00000000000000000000000000000CFC000000000000045C0000045C045C5DFC00000000000000000000000000000000000000000000000000000000000001FC000000000000000000000000000000FC000000000000005C0000005C005C5DFC0000000000000000000000000000003C000000000000001C0000001C001C1DFC000000000000000C0000000C000C0CFC000000040004045C0004045C045C5DFC1
  | 1 => 0x2AF7A9EA519EA5194630DEA5194630D4630CC318DEA5194630D4630CC318D4630CC318CC318C6330DEA5194630D4630CC318D4630CC318CC318C6330D4630CC318CC318C6330CC318C6330C6330D8630DEF5294A3194A318C618D4A318C618CC618C6318D4A318C618CC618C6318CC618C6318C6318CA630D4A318C618CC618C6318CC618C6318C6318CA630CC618C6318C6318CA630C6318CA630D2C6198630DEA7A94651946518C330D46518C330CC330C6118D46518C330CC330C6118CC330C6118C6118C6330D46518C330CC330C6118CC330C6118C6118C6330CC330C6118C6118C6330C6118C6330CA56198630D4A528C6318C63186318CC63186318C6318C6318CC63186318C6318C6318C6318C6318CA5298A630CC63186318C6318C6318C6318C6318CA5298A630C6318C6318CA5298A630D8C641908219082208411EA519EA5194630D4630D4630D4630CC3184C318D4630D4630CC3184C318CC3184C318C610846330D4630D4630CC3184C318CC3184C318C610846330CC3184C318C610846330C610846330C6330D8630D4A3194A318C618CC618CC618CC618C630846318CC618CC618C630846318C630846318C6318CA630CC618CC618C630846318C630846318C6318CA630C630846318C6318CA630CC63199082190822084114651946518C330CC330CC330CC330C611846118CC330CC330C611846118C611846118C6118C6330CC330CC330C611846118C611846118C6118C6330C611846118C6118C6330CC2318C6820C682208410C6318C63186318C6318C6318C6318C6318C6318C6318C6318C6318C6318CC6318C6320C6320C84106318C6318C6318C6318CC6318C6320C6320C8410C6318C6320C6320C8410C6320C8410C841104209EA5194630DEA5194630D4630CC31854630CC318D4630CC31854630CC318CC318461084C318C6330D4630CC31854630CC318CC318461084C318C6330CC318461084C318C6330C61084211046330D8630D4A318C618D4A318C618CC618C63084C618C6318CC618C63084C618C6318C63084210846318CA630CC618C63084C618C6318C63084210846318CA630C63084210846318CA630C6318CA630D908220841146518C330D46518C330CC330C61184C330C6118CC330C61184C330C6118C61184200846118C6330CC330C61184C330C6118C61184200846118C6330C61184200846118C6330C6118C6330CC682208410C63186318CC63186318C6318C210846318C6318C6318C210846318C6318C6318C6318CC6320C84106318C210846318C6318C6318C6318CC6320C84106318C6318CC6320C8410C6320C8410C8411042094630D4630D4630D4630CC3184C3184C3184C318CC3184C3184C3184C318C6108061084610846330CC3184C3184C3184C318C6108061084610846330C6108061084610846330C610846330C6330E08410C618CC618CC618CC618C6308463084630846318C6308463084630846318C630846318C6318CC84106308463084630846318C630846318C6318CC8410630846318C6318CC84106318CC8410C841104208C330CC330CC330CC330C6118461184611846118C6118461184611846118C611846118C6118C634106118461184611846118C611846118C6118C63410611846118C6118C634106118C6341063411042086318C6318C6318C6318C6318C6318C6318C631906318C6318C6318C631906318C6319063190642086318C6318C6318C631906318C6319063190642086318C631906319064208631906420864208821045
  | 2 => 0x371CB6B5DB92E17FE4E028587BD8804FF2980804AB4219118830D612478252871499E1DD0F8829C9E81EE10382C44360BD062818D612478252871499E1DD0F8829C9E81EE10382C44360BD062818C94A1CE0F2028C3F00AF05A016C4120B605F818418A06504C80CD612478252871499E1DD0F8829C9E81EE10382C44360BD062818C94A1CE0F2028C3F00AF05A016C4120B605F818418A06504C80CC94A1CE0F2028C3F00AF05A016C4120B605F818418A06504C80CC4040B505E018018406404C80CC18E06704F80D41E6051028806D8806392800A2CA502A31008414A9C2B810B044445011D061818C9E828D0F783FC40210B058816C42411505D818417E06503280CC9E828D0F783FC40210B058816C42411505D818417E06503280CC41211205B818017606403200CC17E06703380D4118051028806C9E828D0F783FC40210B058816C42411505D818417E06503280CC41211205B818017606403200CC17E06703380D4118051028806C41211205B818017606403200CC17E06703380D4118051028806C18E06C03600E012C05702B80741C208704380B410E02D016803D7FE4EE31C8A2CA0C2041518414A5021515C04444320CF08E818C99E1F014683FC3E60BF085816C4020C608A818417A04103280CC99E1F014683FC3E60BF085816C4020C608A818417A04103280CC3F00C3089018017203F03200CC17604003380D40CE035028806C99E1F014683FC3E60BF085816C4020C608A818417A04103280CC3F00C3089018017203F03200CC17604003380D40CE035028806C3F00C3089018017203F03200CC17604003380D40CE035028806C18404303600E00D803802B807412C04D04380B410E02D016803CAB42B815C059C432111088823445011A08D024C18606303180CC43611508A824817A06103080CC17E06303180D40C603501A806C43611508A824817A06103080CC17E06303180D40C603501A806C18A06703380E00CE03801C007411804D02680B409A02D016803C43611508A824817A06103080CC17E06303180D40C603501A806C18A06703380E00CE03801C007411804D02680B409A02D016803C18A06703380E00CE03801C007411804D02680B409A02D016803C1E6087043814410E051028806C10E051028806C0A201B00D802576E4C427907D0C7228B1518414A001FB10C832457011108E818C94A1D50F982E451A0FF085816C3DE0B7064810422A06103280CC94A1D50F982E451A0FF085816C3DE0B7064810422A06103280CC3C80B306280FC22406003200CC16E03802100840CE035028806C94A1D50F982E451A0FF085816C3DE0B7064810422A06103280CC3C80B306280FC22406003200CC16E03802100840CE035028806C3C80B306280FC22406003200CC16E03802100840CE035028806C17803A02200880D803802B80740D803802B807410E02D016803CA602A310C8444570167088823442C11106781A423409303180CC40E10B064819C22A09203080CC17606102080840C603501A806C40E10B064819C22A09203080CC17606102080840C603501A806C17E06402100880CE03801C00740CE03801C007409A02D016803C40E10B064819C22A09203080CC17606102080840C603501A806C17E06402100880CE03801C00740CE03801C007409A02D016803C17E06402100880CE03801C00740CE03801C007409A02D016803C13E05702B80B410E051028806C10E051028806C0A201B00D8024A1620915184445461110B382344020C908881A422206904980CC3E20C3085819C21606704900CC16204103080840C202101A806C3E20C3085819C21606704900CC16204103080840C202101A806C16804203200880C802201C00740C802201C007407001D016803C3E20C3085819C21606704900CC16204103080840C202101A806C16804203200880C802201C00740C802201C007407001D016803C16804203200880C802201C00740C802201C007407001D016803C13203302B80B40AE02D028806C0AE02D028806C0A201B00D802446211D08E824C23A093049813818606303180CC0C6033019806C18A06503280D40CA03501A80740CA03501A807406A01D00E803C18A06503280D40CA03501A80740CA03501A807406A01D00E803C13205102880B40A202D016806C0A202D016806C05A01B00D802418A06503280D40CA03501A80740CA03501A807406A01D00E803C13205102880B40A202D016806C0A202D016806C05A01B00D802413205102880B40A202D016806C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800D6D64A026207709DC1F31048300C7228B151841457011108E818C8F01C00EA82A43E00B806180F451A0FF085816C22A06103280CC8F01C00EA82A43E00B806180F451A0FF085816C22A06103280CC39C0A905980D418603E021008422406003200CC0CE035028806C8F01C00EA82A43E00B806180F451A0FF085816C22A06103280CC39C0A905980D418603E021008422406003200CC0CE035028806C39C0A905980D418603E021008422406003200CC0CE035028806C16A03701D007408602201980440D803802B807410E02D016803C9FE28B0FD840842A1110648198570167088823423409303180CC3DC0FF05B817818C067020808422A09203080CC0C603501A806C3DC0FF05B817818C067020808422A09203080CC0C603501A806C16C06001C007408002201100440CE03801C007409A02D016803C3DC0FF05B817818C067020808422A09203080CC0C603501A806C16C06001C007408002201100440CE03801C007409A02D016803C16C06001C007408002201100440CE03801C007409A02D016803C0CE03801C007409A02D016803C10E051028806C0A201B00D80249C01F314584084080C908881985461110B3823422206904980CC3BA0B807F817817E046033808421606704900CC0C202101A806C3BA0B807F817817E046033808421606704900CC0C202101A806C15E03E030007407E01401100440C802201C007407001D016803C3BA0B807F817817E046033808421606704900CC0C202101A806C15E03E030007407E01401100440C802201C007407001D016803C15E03E030007407E01401100440C802201C007407001D016803C0C802201C007407001D016803C0AE02D028806C0A201B00D8024432111088823419E06903480D823A09304981380C6033019806C17A06103080CC08202101080440CA03501A807406A01D00E803C17A06103080CC08202101080440CA03501A807406A01D00E803C0CA03501A807406A01D00E803C0A202D016806C05A01B00D802417A06103080CC08202101080440CA03501A807406A01D00E803C0CA03501A807406A01D00E803C0A202D016806C05A01B00D80240CA03501A807406A01D00E803C0A202D016806C05A01B00D80240A202D016806C05A01B00D802405A01B00D8024036009004800C9701DC0FA02F8516102088819851610208881982CE08D04980CC38A0A905C81001FE05E03380841FE05E033808412403301A806C38A0A905C81001FE05E03380841FE05E033808412403301A806C14603501F80440C001D01100440C001D011004407001D016803C38A0A905C81001FE05E03380841FE05E033808412403301A806C14603501F80440C001D01100440C001D011004407001D016803C14603501F80440C001D01100440C001D011004407001D016803C0C001D011004407001D016803C07001D016803C0A201B00D8024402105064819822208D03480D822208D03480D812604E019806C16205B02080840C203301080440C2033010804406A01D00E803C16205B02080840C203301080440C2033010804406A01D00E803C0C2033010804406A01D00E803C06A01D00E803C05A01B00D802416205B02080840C203301080440C2033010804406A01D00E803C0C2033010804406A01D00E803C06A01D00E803C05A01B00D80240C2033010804406A01D00E803C06A01D00E803C05A01B00D802406A01D00E803C05A01B00D802405A01B00D8024036009004800C3DE0C0082819820A06604680D820A06604680D811A036027006C14E03D02D80840B602101980440B6021019804406601100E803C14E03D02D80840B602101980440B6021019804406601100E803C0B6021019804406601100E803C06601100E803C03A00F00D802414E03D02D80840B602101980440B6021019804406601100E803C0B6021019804406601100E803C06601100E803C03A00F00D80240B6021019804406601100E803C06601100E803C03A00F00D802406601100E803C03A00F00D802403A00F00D8024036009004800C18606303180CC0C6033019806C0C6033019806C06601B00D803C0C6033019806C06601B00D803C06601B00D803C03600F00780240C6033019806C06601B00D803C06601B00D803C03600F007802406601B00D803C03600F007802403600F007802401E009004800C0C6033019806C06601B00D803C06601B00D803C03600F007802406601B00D803C03600F007802403600F007802401E009004800C06601B00D803C03600F007802403600F007802401E009004800C03600F007802401E009004800C01E009004800C0120030018004D
  | 3 => 0x2A7D11940B33A281DF98D2C487B760FD5408E14D63207DDE10376092884253025F204E8A028F8C3C6072860EC820847C3CD182298047B4024D03E330238804A3E02688131E80A260151800E28C3C6072860EC820847C3CD182298047B4024D03E330238804A3E02688131E80A260151800E283AC002179045FC02400122780996013DC00D6012B7009EE014E600E280561003B0009F0004F8C3C6072860EC820847C3CD182298047B4024D03E330238804A3E02688131E80A260151800E283AC002179045FC02400122780996013DC00D6012B7009EE014E600E280561003B0009F0004F83AC002179045FC02400122780996013DC00D6012B7009EE014E600E280561003B0009F0004F81284009DA014AA00E08055B803AF00A0000500058B003D200A80005400390001C800390001C8D632092D00FC800ACE0409F82C8D049C803264420202DA404C2003450137B80D8F014D000E283E3302B2C0478603164126E80CE60138400D6012F800D570146C00E280531003B000760004F83E3302B2C0478603164126E80CE60138400D6012F800D570146C00E280531003B000760004F812B700D380141C00E080526803AF0075E00500054D003D2007A4005400260801C800390001C83E3302B2C0478603164126E80CE60138400D6012F800D570146C00E280531003B000760004F812B700D380141C00E080526803AF0075E00500054D003D2007A4005400260801C800390001C812B700D380141C00E080526803AF0075E00500054D003D2007A4005400260801C800390001C8058B004020080400588028A801E8003D0001E80372002A000540002A00150000A800150000A8D2C487DA9125A00ACE03F7A0253F0591A03264409F8262305B4803450131400AF501B1E00E283CD1823DE0565803164120400A57019CC00D60126E80AA701AAE00E280520002C800760004F83CD1823DE0565803164120400A57019CC00D60126E80AA701AAE00E280520002C800760004F8122780A8301A7000E080511002BF0075E005000526802CD007A40054001E90015000390001C83CD1823DE0565803164120400A57019CC00D60126E80AA701AAE00E280520002C800760004F8122780A8301A7000E080511002BF0075E005000526802CD007A40054001E90015000390001C8122780A8301A7000E080511002BF0075E005000526802CD007A40054001E90015000390001C8055B802EE0080400588020100162003D0001E8028A801BE00540002A00150000A800150000A8425302DA405B4803F80131400D2901A520123C137B80D8601B0C012FC05370039C00738004F8131E80D5701AAE012E005200039400728005000531003AA007540054001D500150002A0001C8131E80D5701AAE012E005200039400728005000531003AA007540054001D500150002A0001C80561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A8131E80D5701AAE012E005200039400728005000531003AA007540054001D500150002A0001C80561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A80561003D2007A40058801E900162002C4001E80260801BE0037C002A000DF000A800150000A80390002A00054000400015000100002000010001500010000200001000080000400008000040CE8A079EA0FC2C091BC496802B380591A032643F20024A004CC802AE416D200D1401B1E00E283B20822380482802828159600C59019CC00D6011E1809FA0159800B0006AB8038A00760004F83B20822380482802828159600C59019CC00D6011E1809FA0159800B0006AB8038A00760004F8117F009C20153C00AC4069C003820075E00500050700282005C4003E001E90015000390001C83B20822380482802828159600C59019CC00D6011E1809FA0159800B0006AB8038A00760004F8117F009C20153C00AC4069C003820075E00500050700282005C4003E001E90015000390001C8117F009C20153C00AC4069C003820075E00500050700282005C4003E001E90015000390001C8052A80296005F400400020100162003D0001E8020100162003D0001E80150000A800150000A840DD82C8D04CC8034B016D200FE001A520123C130800D290161400F2406C3004BF00738004F8128F80CE60159800EEC06AB804B80072800500051B00394005A4003E001D500150002A0001C8128F80CE60159800EEC06AB804B80072800500051B00394005A4003E001D500150002A0001C80539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A8128F80CE60159800EEC06AB804B80072800500051B00394005A4003E001D500150002A0001C80539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A80539803AF005C40040001E900162002C4001E801E900162002C4001E800DF000A800150000A802A0001E8003D0002A00150001000020000100015000100002000010000800004000080000403F550259D0591A034B0164680D2C01FC00123C127200AC801A5200F240694803C90097E004F811ED00A81019CC00EEC0673003BB009700050004E1002C600728003E001CA000F8002A0001C811ED00A81019CC00EEC0673003BB009700050004E1002C600728003E001CA000F8002A0001C804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A811ED00A81019CC00EEC0673003BB009700050004E1002C600728003E001CA000F8002A0001C804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A804F7002D30075E0040001D780100002C4001E801D780100002C4001E800B10007A00150000A8028000158003D0002A000F4000A8002000010000F4000A80020000100008000040000800004013A280D8F01B1E012FC06C7804BF0097E006C005340039C007380051001CE0014400288001C80546003B0007600054001D800150002A0001E801D800150002A0001E800A80007A000F4000A80546003B0007600054001D800150002A0001E801D800150002A0001E800A80007A000F4000A8027C001C800390002A000E4000A8001500010000E4000A8001500010000540004000080000400546003B0007600054001D800150002A0001E801D800150002A0001E800A80007A000F4000A8027C001C800390002A000E4000A8001500010000E4000A800150001000054000400008000040027C001C800390002A000E4000A8001500010000E4000A80015000100005400040000800004000E4000A80015000100005400040000800004000540004000080000400020000100002000010CA05876C60F3D408B7C3ED48246004B3A02988496802B380591A0326416D200D1401B1E00E283943020F0044700255C11EF00A020150200A78159600C59019CC00D6006AB8038A00760004F83943020F0044700255C11EF00A020150200A78159600C59019CC00D6006AB8038A00760004F810BC80942013840097C0541802AC005A6003C8069C003820075E0050001E90015000390001C83943020F0044700255C11EF00A020150200A78159600C59019CC00D6006AB8038A00760004F810BC80942013840097C0541802AC005A6003C8069C003820075E0050001E90015000390001C810BC80942013840097C0541802AC005A6003C8069C003820075E0050001E90015000390001C804ED002720052C00378017700100002B000158020100162003D0001E80150000A800150000A83EEF02B380494003230131180D2C0159000EB816D200FE001A520123C06C3004BF00738004F811C400C59013F400DC00553803BB0058C003C806AB804B8007280050001D500150002A0001C811C400C59013F400DC00553803BB0058C003C806AB804B8007280050001D500150002A0001C804F7003820050400378016680100002000015801E900162002C4001E800DF000A800150000A811C400C59013F400DC00553803BB0058C003C806AB804B8007280050001D500150002A0001C804F7003820050400378016680100002000015801E900162002C4001E800DF000A800150000A804F7003820050400378016680100002000015801E900162002C4001E800DF000A800150000A801E900162002C4001E800DF000A800150000A8015000100002000010000800004000080000403DBB024600567003230129F80AD001A5800EB8164680D2C01FC00123C0694803C90097E004F8114C00A02018B200DC0052B802EC00776003C80673003BB009700050001CA000F8002A0001C8114C00A02018B200DC0052B802EC00776003C80673003BB009700050001CA000F8002A0001C804CB002AC0070400378015F800BA002000015801D780100002C4001E800B10007A00150000A8114C00A02018B200DC0052B802EC00776003C80673003BB009700050001CA000F8002A0001C804CB002AC0070400378015F800BA002000015801D780100002C4001E800B10007A00150000A804CB002AC0070400378015F800BA002000015801D780100002C4001E800B10007A00150000A801D780100002C4001E800B10007A00150000A800F4000A80020000100008000040000800004012F900D1401A280123C057A803C9007920054006C7804BF0097E006C001CE0014400288001C805130038A00714005000164000F8001F00015801D800150002A0001E800A80007A000F4000A805130038A00714005000164000F8001F00015801D800150002A0001E800A80007A000F4000A801D800150002A0001E800A80007A000F4000A800E4000A80015000100005400040000800004005130038A00714005000164000F8001F00015801D800150002A0001E800A80007A000F4000A801D800150002A0001E800A80007A000F4000A800E4000A80015000100005400040000800004001D800150002A0001E800A80007A000F4000A800E4000A80015000100005400040000800004000E4000A800150001000054000400008000040005400040000800004000200001000020000103BF3022DF048DE02970159C00C8C01A5800EB8159C00C8C01A5800EB807F00048F0097E004F8108F809570141400AD8062C8037000776003C8062C8037000776003C8025C00140002A0001C8108F809570141400AD8062C8037000776003C8062C8037000776003C8025C00140002A0001C804800025F005620028801C1000DE002000015801C1000DE002000015800B10007A00150000A8108F809570141400AD8062C8037000776003C8062C8037000776003C8025C00140002A0001C804800025F005620028801C1000DE002000015801C1000DE002000015800B10007A00150000A804800025F005620028801C1000DE002000015801C1000DE002000015800B10007A00150000A801C1000DE002000015800B10007A00150000A800B10007A00150000A80080000400008000040125100C990157200EB8068A0048F0079200540068A0048F0079200540025F801B000288001C804D10035800580003C801C500140001F00015801C500140001F00015800A80007A000F4000A804D10035800580003C801C500140001F00015801C500140001F00015800A80007A000F4000A801C500140001F00015800A80007A000F4000A800A80007A000F4000A8005400040000800004004D10035800580003C801C500140001F00015801C500140001F00015800A80007A000F4000A801C500140001F00015800A80007A000F4000A800A80007A000F4000A8005400040000800004001C500140001F00015800A80007A000F4000A800A80007A000F4000A8005400040000800004000A80007A000F4000A800540004000080000400054000400008000040002000010000200001011C280A620193200EB8064C803AE0091E00540064C803AE0091E0054002478015000360001C8049A0029E006B0003C801AC000F2002800015801AC000F2002800015800A000056000F4000A8049A0029E006B0003C801AC000F2002800015801AC000F2002800015800A000056000F4000A801AC000F2002800015800A000056000F4000A800A000056000F4000A8003D0002A0008000040049A0029E006B0003C801AC000F2002800015801AC000F2002800015800A000056000F4000A801AC000F2002800015800A000056000F4000A800A000056000F4000A8003D0002A000800004001AC000F2002800015800A000056000F4000A800A000056000F4000A8003D0002A000800004000A000056000F4000A8003D0002A0008000040003D0002A00080000400020000100002000010051F0038A00714004F801C50013E0027C001C801C50013E0027C001C8009F00072000E4000A801C50013E0027C001C8009F00072000E4000A8009F00072000E4000A800390002A000540004001C50013E0027C001C8009F00072000E4000A8009F00072000E4000A800390002A0005400040009F00072000E4000A800390002A000540004000390002A0005400040001500010000200001001C50013E0027C001C8009F00072000E4000A8009F00072000E4000A800390002A0005400040009F00072000E4000A800390002A000540004000390002A00054000400015000100002000010009F00072000E4000A800390002A000540004000390002A0005400040001500010000200001000390002A00054000400015000100002000010001500010000200001000080000400008000053
  | 4 => 0x30F28B16A46B2E20CE14E410BB9A7055B0D0AED7C04CF8CBE04E8570B10B269804F0BC2D593814541029C520115F8B0AD3050B3F0A5BDE0491302A653812F2502707A0101B02B2898135B40282C2010BA00A47D8045C60090680048A8B0AD3050B3F0A5BDE0491302A653812F2502707A0101B02B2898135B40282C2010BA00A47D8045C60090680048A8292FA0126F702651200FDD009E2C0042E7008A840045E00A2538044EB00908C0049500251A80130A00300C001338B0AD3050B3F0A5BDE0491302A653812F2502707A0101B02B2898135B40282C2010BA00A47D8045C60090680048A8292FA0126F702651200FDD009E2C0042E7008A840045E00A2538044EB00908C0049500251A80130A00300C001338292FA0126F702651200FDD009E2C0042E7008A840045E00A2538044EB00908C0049500251A80130A00300C0013380A0EF004465008F560048C80251F801315003070001360026658013C40032C80014500101D000672000CE4000528BE04E86225A0AEF6E05A0E82C8B4017185027FF60147E42D49C0178DC02907C01527C0A6F500572D008E980048A82B28981681E0270E40143480A0298053F50088600045E00A410005667008D90004950023E700130A0026140013382B28981681E0270E40143480A0298053F50088600045E00A410005667008D90004950023E700130A0026140013380A2538055BE008BEE0048C8023D100131500262A001360024DD0013C400278800145000BB5800672000CE40005282B28981681E0270E40143480A0298053F50088600045E00A410005667008D90004950023E700130A0026140013380A2538055BE008BEE0048C8023D100131500262A001360024DD0013C400278800145000BB5800672000CE40005280A2538055BE008BEE0048C8023D100131500262A001360024DD0013C400278800145000BB5800672000CE4000528026658014A000294000154000C698006D6000DAC00057800FD20008CA001194000708004650001C2000384000168BB9A705759E0C44B405A0E82BF6501433302E30A0147E42C8B401493102F1B801527C0A450804A5500AE5A0048A82A65381395002D03C01434809D4600473800A7EA0045E00A0298048FA00ACCE00495002373000F7A0026140013382A65381395002D03C01434809D4600473800A7EA0045E00A0298048FA00ACCE00495002373000F7A00261400133809E2C00482A00AB7C0048C802338000F6300262A001360023D1000FB3002788001450009E2000514000CE40005282A65381395002D03C01434809D4600473800A7EA0045E00A0298048FA00ACCE00495002373000F7A00261400133809E2C00482A00AB7C0048C802338000F6300262A001360023D1000FB3002788001450009E2000514000CE400052809E2C00482A00AB7C0048C802338000F6300262A001360023D1000FB3002788001450009E2000514000CE40005280251F80105400294000154000A50000550000DAC00057800C6980065E001194000708004650001C20003840001682D5938178DC02F1B80189D80A45080556E00AADC0058A40A6F500575A00AEB4005BD4023D30012AE00255C0013380A47D80566700ACCE005B600237300129C002538001360023E700130A00261400145000985000514000A280005280A47D80566700ACCE005B600237300129C002538001360023E700130A00261400145000985000514000A280005280251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C20003840001680A47D80566700ACCE005B600237300129C002538001360023E700130A00261400145000985000514000A280005280251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C20003840001680251A8013C4002788001540009E2000550000AA000057800BB580065E000CBC0007080032F0001C20003840001680101D0008CA0011940009C4004650002710004E20001F4004650002710004E20001F40013880007D0000FA000064B88338551DA0AF3D804F62C3112D01683A02E30A0147E42BBDB813E740296380124440BC6E00549F00AE5A0048A8296F7812D400275DC0115980B40F0050D200A7EA0045E009C3900452A0093A6003D0002B33801254002614001338296F7812D400275DC0115980B40F0050D200A7EA0045E009C3900452A0093A6003D0002B33801254002614001338099448043D4009198003C0402ADF00123200262A001360022FB800E5A002030001040009E2000514000CE4000528296F7812D400275DC0115980B40F0050D200A7EA0045E009C3900452A0093A6003D0002B33801254002614001338099448043D4009198003C0402ADF00123200262A001360022FB800E5A002030001040009E2000514000CE4000528099448043D4009198003C0402ADF00123200262A001360022FB800E5A002030001040009E2000514000CE4000528023D5800EBA0021200010B800A50000550000DAC00057800A50000550000DAC000578004650001C20003840001682C9A60171850296380156000BC6E00627600AADC0058A40A41F00556E009648004D7C02BAD0016F500255C0013380A0B08053F50093A6004C9402B338016D80025380013600236400129C001F8400104000985000514000A280005280A0B08053F50093A6004C9402B338016D80025380013600236400129C001F8400104000985000514000A28000528024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C20003840001680A0B08053F50093A6004C9402B338016D80025380013600236400129C001F8400104000985000514000A28000528024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C2000384000168024230013150020300010B8009E2000550000AA0000578009E2000550000AA00005780032F0001C200038400016800CB20006D6000DAC000708004650002710004E20001F4004650002710004E20001F40013880007D0000FA0000642BB5F0145D502E30A0156000B8C280558000C4EC0058A409FFD8049B000AADC004D7C02AB700135F002DEA00133809C1E80481700A7EA004C94029FA801325002DB000136002218000F700025380010400094E000410000A2800052809C1E80481700A7EA004C94029FA801325002DB000136002218000F700025380010400094E000410000A28000528022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E00038400016809C1E80481700A7EA004C94029FA801325002DB000136002218000F700025380010400094E000410000A28000528022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E000384000168022A1000FB300262A0010B80098A80042E000AA00005780098A80042E000AA0000578002A800015E00038400016800C1C000546000DAC0007080036B0001C20004E20001F40036B0001C20004E20001F40013880007D0000FA0000640A71480572D00AE5A005BD402B968016F5002DEA001860023A60012AE00255C0013B0009570004EC0009D80005280241A00130A00261400145000985000514000A2800057800985000514000A280005780028A00015E0002BC0001680241A00130A00261400145000985000514000A2800057800985000514000A280005780028A00015E0002BC00016800C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA0000640241A00130A00261400145000985000514000A2800057800985000514000A280005780028A00015E0002BC00016800C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA00006400C03000672000CE4000708003390001C20003840001F4003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E800019000032000014B52358534400AA3B404C74C2BACF013D34028BAA011CB83112D01683A02E30A0147E40BC6E00549F00AE5A0048A82859F8123E8025A800105B409CA800454500902E003A980B40F0050D200A7EA0045E002B338012540026140013382859F8123E8025A800105B409CA800454500902E003A980B40F0050D200A7EA0045E002B338012540026140013380937B8040DC0087A800366C02415000EF2001F66000FC802ADF00123200262A001360009E2000514000CE40005282859F8123E8025A800105B409CA800454500902E003A980B40F0050D200A7EA0045E002B338012540026140013380937B8040DC0087A800366C02415000EF2001F66000FC802ADF00123200262A001360009E2000514000CE40005280937B8040DC0087A800366C02415000EF2001F66000FC802ADF00123200262A001360009E2000514000CE400052802232800DFA001D74000ED80082A00042E000A8C00043800A50000550000DAC000578004650001C20003840001682B85881683A027CE80148180A498805580009360004B900BC6E00627600AADC0058A402BAD0016F500255C00133809ADA0050D2008A540047780247D001325001EE0000FC802B338016D800253800136000985000514000A2800052809ADA0050D2008A540047780247D001325001EE0000FC802B338016D800253800136000985000514000A2800052802275801232001CB4000ED8007D980042E00085C000438009E2000550000AA00005780032F0001C200038400016809ADA0050D2008A540047780247D001325001EE0000FC802B338016D800253800136000985000514000A2800052802275801232001CB4000ED8007D980042E00085C000438009E2000550000AA00005780032F0001C200038400016802275801232001CB4000ED8007D980042E00085C000438009E2000550000AA00005780032F0001C2000384000168009E2000550000AA00005780032F0001C2000384000168004650002710004E20001F40013880007D0000FA0000642AD86813D3402D0740148180A1998049EA00AB00004B900B8C280558000C4EC0058A402AB700135F002DEA0013380979280454500A1A40047780239C00100200264A000FC8029FA801325002DB00013600094E000410000A280005280979280454500A1A40047780239C00100200264A000FC8029FA801325002DB00013600094E000410000A2800052802173800EF2002464000ED8007B180035200085C0004380098A80042E000AA0000578002A800015E0003840001680979280454500A1A40047780239C00100200264A000FC8029FA801325002DB00013600094E000410000A2800052802173800EF2002464000ED8007B180035200085C0004380098A80042E000AA0000578002A800015E00038400016802173800EF2002464000ED8007B180035200085C0004380098A80042E000AA0000578002A800015E0003840001680098A80042E000AA0000578002A800015E0003840001680036B0001C20004E20001F40013880007D0000FA0000640A2A080549F00A93E0058A40252A80135F0026BE00142802B968016F5002DEA001860009570004EC0009D8000528022E30012540024A8001360007BD00041000082000043800985000514000A280005780028A00015E0002BC000168022E30012540024A8001360007BD00041000082000043800985000514000A280005780028A00015E0002BC00016800985000514000A280005780028A00015E0002BC000168003390001C20003840001F4000E100007D0000FA000064022E30012540024A8001360007BD00041000082000043800985000514000A280005780028A00015E0002BC00016800985000514000A280005780028A00015E0002BC000168003390001C20003840001F4000E100007D0000FA00006400985000514000A280005780028A00015E0002BC000168003390001C20003840001F4000E100007D0000FA000064003390001C20003840001F4000E100007D0000FA000064000E100007D0000FA0000640003E80001900003200001429C820131D3027B16011D500B41D00520600AB00004B900B41D00520600AB00004B900313B001629002DEA0013380922600416D008ACC003C30028690011DE00264A000FC8028690011DE00264A000FC800B6C0004D8000A280005280922600416D008ACC003C30028690011DE00264A000FC8028690011DE00264A000FC800B6C0004D8000A2800052801FBA000D9B001E02000BE0009190003B600085C000438009190003B600085C000438002A800015E0003840001680922600416D008ACC003C30028690011DE00264A000FC8028690011DE00264A000FC800B6C0004D8000A2800052801FBA000D9B001E02000BE0009190003B600085C000438009190003B600085C000438002A800015E00038400016801FBA000D9B001E02000BE0009190003B600085C000438009190003B600085C000438002A800015E000384000168009190003B600085C000438002A800015E000384000168002A800015E0003840001680013880007D0000FA00006409E178051F9009222004B9002A4F8016290026BE00142802A4F8016290026BE00142800B7A8006180009D800052802174001178001E80000FC80092A0004D80008200004380092A0004D80008200004380028A00015E0002BC00016802174001178001E80000FC80092A0004D80008200004380092A0004D80008200004380028A00015E0002BC0001680092A0004D80008200004380028A00015E0002BC0001680028A00015E0002BC000168000E100007D0000FA00006402174001178001E80000FC80092A0004D80008200004380092A0004D80008200004380028A00015E0002BC0001680092A0004D80008200004380028A00015E0002BC0001680028A00015E0002BC000168000E100007D0000FA0000640092A0004D80008200004380028A00015E0002BC0001680028A00015E0002BC000168000E100007D0000FA0000640028A00015E0002BC000168000E100007D0000FA000064000E100007D0000FA0000640003E800019000032000014099F180472E00A3F2004B90028FC8012E4002C52001428028FC8012E4002C5200142800B1480050A000C3000052802036000EA60022F0000FC8008BC0003F20009B0000438008BC0003F20009B00004380026C00010E0002BC00016802036000EA60022F0000FC8008BC0003F20009B0000438008BC0003F20009B00004380026C00010E0002BC000168008BC0003F20009B00004380026C00010E0002BC0001680026C00010E0002BC000168000AF00005A0000FA00006402036000EA60022F0000FC8008BC0003F20009B0000438008BC0003F20009B00004380026C00010E0002BC000168008BC0003F20009B00004380026C00010E0002BC0001680026C00010E0002BC000168000AF00005A0000FA000064008BC0003F20009B00004380026C00010E0002BC0001680026C00010E0002BC000168000AF00005A0000FA0000640026C00010E0002BC000168000AF00005A0000FA000064000AF00005A0000FA0000640003E800019000032000014022BF00122A002454001338009150004CE00099C000528009150004CE00099C0005280026700014A000294000168009150004CE00099C0005280026700014A0002940001680026700014A000294000168000A500005A0000B4000064009150004CE00099C0005280026700014A0002940001680026700014A000294000168000A500005A0000B40000640026700014A000294000168000A500005A0000B4000064000A500005A0000B40000640002D000019000032000014009150004CE00099C0005280026700014A0002940001680026700014A000294000168000A500005A0000B40000640026700014A000294000168000A500005A0000B4000064000A500005A0000B40000640002D0000190000320000140026700014A000294000168000A500005A0000B4000064000A500005A0000B40000640002D000019000032000014000A500005A0000B40000640002D0000190000320000140002D0000190000320000140000C80000500000A0000057
  | 5 => 0x3E637932F29AA8BFA79B08E1C80C25DCE091411824EA7201AB5B4C4732D093327825914101B56882610D601BFE700727B3004F164B8FDAF08A5AD82360BF019AA842410F701A7AB006C980004AB6C249B3801AF57806F4D7004D2A407173D004FE840149830010914B8FDAF08A5AD82360BF019AA842410F701A7AB006C980004AB6C249B3801AF57806F4D7004D2A407173D004FE84014983001091423355A019E45C06B1300049F4C06E017004D5AC013F89001019C070792004F54C014B4E0010C6401534300115CC0054060003804B8FDAF08A5AD82360BF019AA842410F701A7AB006C980004AB6C249B3801AF57806F4D7004D2A407173D004FE84014983001091423355A019E45C06B1300049F4C06E017004D5AC013F89001019C070792004F54C014B4E0010C6401534300115CC005406000380423355A019E45C06B1300049F4C06E017004D5AC013F89001019C070792004F54C014B4E0010C6401534300115CC005406000380406FA96004EC8C01491A0010AC401540C00116C00054BA000387C015EDB0011FE400587A0003AFC006B9400047B80011EE0000BF4C4732D0A27A5C25069801E796825944301F263C06EEEC005ACB426183201FABE0071598005D540072DD1005FB2C0145D70010914249B3801E7F1806CE2B0059E2C06F2E5005CE98013B39001019C071782005F39C0145490010C6401497100115CC0045730003804249B3801E7F1806CE2B0059E2C06F2E5005CE98013B39001019C071782005F39C0145490010C6401497100115CC0045730003804070792005E9880142470010AC401496C00116C00045B0000387C0152650011FE40047F90003AFC0052A800047B80011EE0000BF4249B3801E7F1806CE2B0059E2C06F2E5005CE98013B39001019C071782005F39C0145490010C6401497100115CC0045730003804070792005E9880142470010AC401496C00116C00045B0000387C0152650011FE40047F90003AFC0052A800047B80011EE0000BF4070792005E9880142470010AC401496C00116C00045B0000387C0152650011FE40047F90003AFC0052A800047B80011EE0000BF4015EDB0012AD4004AB50003D540056F40004B780012DE0000C94006A590005CD00017340000F780017340000F780003DE0000294C25DCE0940B5C289E9701E796825311E01BFF0C07C98F005ACB425944301C6C3C07EAF8005D5400716BE0054498017ECB00109142410F701B4988079FC60059E2C06D89200518680173A6001019C06F2E50053358017CE70010C6401458F000EBE400457300038042410F701B4988079FC60059E2C06D89200518680173A6001019C06F2E50053358017CE70010C6401458F000EBE4004573000380406E0170052698017A620010AC401443D000EB380045B0000387C01496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF42410F701B4988079FC60059E2C06D89200518680173A6001019C06F2E50053358017CE70010C6401458F000EBE4004573000380406E0170052698017A620010AC401443D000EB380045B0000387C01496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF406E0170052698017A620010AC401443D000EB380045B0000387C01496C000EFC00047F90003AFC0047F90003AFC0011EE0000BF401540C000F80C004AB50003D54004AB50003D540012DE0000C940056F4000472C0017340000F780017340000F780003DE00002942610D601FABE007EAF80069B680716BE005E56C01795B001383C072DD100601B001806C00141FC0147E1001113C00444F000380407173D005F39C017CE7001409801458F00110CC004433000387C01497100116940045A50003AFC0045A50003AFC000EBF0000BF407173D005F39C017CE7001409801458F00110CC004433000387C01497100116940045A50003AFC0045A50003AFC000EBF0000BF40153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE000029407173D005F39C017CE7001409801458F00110CC004433000387C01497100116940045A50003AFC0045A50003AFC000EBF0000BF40153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE00002940153430011FE40047F90003D540047F90003D54000F550000C940052A8000472C0011CB0000F780011CB0000F780003DE0000294006B940005CD00017340001440001734000144000051000003600017340001440000510000036000051000003600000D80000090BFA79B090C060251CCC01B940C289E9701E796807C98F005ACB425069801BA368072468005317807EAF8005D540017ECB00109142360BF01A63C006DA42004FB34079FC60059E2C0173A6001019C06CE2B004F8E401502D000E854017CE70010C6400457300038042360BF01A63C006DA42004FB34079FC60059E2C0173A6001019C06CE2B004F8E401502D000E854017CE70010C64004573000380406B130004E364014C29000E550017A620010AC40045B0000387C014247000DE7C003D3B00031740047F90003AFC0011EE0000BF42360BF01A63C006DA42004FB34079FC60059E2C0173A6001019C06CE2B004F8E401502D000E854017CE70010C64004573000380406B130004E364014C29000E550017A620010AC40045B0000387C014247000DE7C003D3B00031740047F90003AFC0011EE0000BF406B130004E364014C29000E550017A620010AC40045B0000387C014247000DE7C003D3B00031740047F90003AFC0011EE0000BF401491A000E36C003ECB00032B4004AB50003D540012DE0000C94004AB50003D540012DE0000C940017340000F780003DE000029425914101F263C072468005E66807EAF80069B6801795B001383C071598005E56C015531001192801806C00141FC00444F000380406F4D7005CE9801502D0011660017CE70014098004433000387C01454900110CC003C1300031740045A50003AFC000EBF0000BF406F4D7005CE9801502D0011660017CE70014098004433000387C01454900110CC003C1300031740045A50003AFC000EBF0000BF4014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE000029406F4D7005CE9801502D0011660017CE70014098004433000387C01454900110CC003C1300031740045A50003AFC000EBF0000BF4014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE0000294014B4E00116C0003D3B00032B40047F90003D54000F550000C940047F90003D54000F550000C940011CB0000F780003DE000029400587A0004B780012DE0000F78001734000144000051000003600017340001440000510000036000051000003600000D8000009024EA7201C2F3407C98F005E66807C98F005E66801A6DA001383C06EEEC0053E5C01795B001192801795B001192800507F000380406C98000525480173A600116600173A60011660005026000387C013B39000EB6C00443300031740044330003174000EBF0000BF406C98000525480173A600116600173A60011660005026000387C013B39000EB6C00443300031740044330003174000EBF0000BF4013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE000029406C98000525480173A600116600173A60011660005026000387C013B39000EB6C00443300031740044330003174000EBF0000BF4013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE0000294013F89000EEF80045B000032B40045B000032B4000F550000C940045B000032B4000F550000C94000F550000C940003DE00002940054BA0003D680012DE0000F780012DE0000F7800051000003600012DE0000F78000510000036000051000003600000D800000900727B3005FB2C017ECB00141FC017ECB00141FC00507F00043F80145D7001113C00444F000396C00444F000396C000E5B0000BF401498300115CC0045730003AFC0045730003AFC000EBF0000C940045730003AFC000EBF0000C94000EBF0000C94000325000029401498300115CC0045730003AFC0045730003AFC000EBF0000C940045730003AFC000EBF0000C94000EBF0000C94000325000029400540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D8000009001498300115CC0045730003AFC0045730003AFC000EBF0000C940045730003AFC000EBF0000C94000EBF0000C94000325000029400540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D8000009000540600047B80011EE0000F780011EE0000F780003DE00003600011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D800000900000240000018BCA6AA08E098024301801AB1EC2502D701B8EE8070BCD0051414289E9701E796807C98F005ACB407EAF8005D540017ECB00109142296B6019B1580698F0004BDA006D262004F9AC014952000E09C079FC60059E2C0173A6001019C017CE70010C6400457300038042296B6019B1580698F0004BDA006D262004F9AC014952000E09C079FC60059E2C0173A6001019C017CE70010C640045730003804067917004B4640138D9000D3D80149A6000E4C4003BBE000300C017A620010AC40045B0000387C0047F90003AFC0011EE0000BF42296B6019B1580698F0004BDA006D262004F9AC014952000E09C079FC60059E2C0173A6001019C017CE70010C640045730003804067917004B4640138D9000D3D80149A6000E4C4003BBE000300C017A620010AC40045B0000387C0047F90003AFC0011EE0000BF4067917004B4640138D9000D3D80149A6000E4C4003BBE000300C017A620010AC40045B0000387C0047F90003AFC0011EE0000BF4013B23000D8EC0038DB0002DDC003E0300032B4000F5A0000A3C004AB50003D540012DE0000C940017340000F780003DE000029424CC9E01E796806E8DA005B128071B0F005E668014F97001130407EAF80069B6801795B001383C01806C00141FC00444F000380406BD5E0059E2C013E39001067C014CD60011660003ADB000300C017CE70014098004433000387C0045A50003AFC000EBF0000BF406BD5E0059E2C013E39001067C014CD60011660003ADB000300C017CE70014098004433000387C0045A50003AFC000EBF0000BF4013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C0047F90003D54000F550000C940011CB0000F780003DE000029406BD5E0059E2C013E39001067C014CD60011660003ADB000300C017CE70014098004433000387C0045A50003AFC000EBF0000BF4013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C0047F90003D54000F550000C940011CB0000F780003DE0000294013D530010AC400379F0002DDC003BF000032B4000CAD0000A3C0047F90003D54000F550000C940011CB0000F780003DE00002940047F90003D54000F550000C940011CB0000F780003DE00002940017340001440000510000036000051000003600000D8000009024504601B8EE8079E5A005B12806FFC3005421C01799A001130407C98F005E66801A6DA001383C01795B001192800507F0003804069EAC004F9AC01678B001067C01461A000F1C4004598000300C0173A60011660005026000387C0044330003174000EBF0000BF4069EAC004F9AC01678B001067C01461A000F1C4004598000300C0173A60011660005026000387C0044330003174000EBF0000BF401356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C0045B000032B4000F550000C94000F550000C940003DE0000294069EAC004F9AC01678B001067C01461A000F1C4004598000300C0173A60011660005026000387C0044330003174000EBF0000BF401356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C0045B000032B4000F550000C94000F550000C940003DE000029401356B000E4C40042B10002DDC003ACE0002A58000CAD0000A3C0045B000032B4000F550000C94000F550000C940003DE00002940045B000032B4000F550000C94000F550000C940003DE00002940012DE0000F78000510000036000051000003600000D8000009006FF9C005D540017550001383C015126001192800464A0003A5C017ECB00141FC00507F00043F800444F000396C000E5B0000BF4013FA10010C64004319000387C003AF90003174000C5D0000A3C0045730003AFC000EBF0000C94000EBF0000C940003250000294013FA10010C64004319000387C003AF90003174000C5D0000A3C0045730003AFC000EBF0000C94000EBF0000C9400032500002940045730003AFC000EBF0000C94000EBF0000C9400032500002940011EE0000F780003DE00003600003DE00003600000D80000090013FA10010C64004319000387C003AF90003174000C5D0000A3C0045730003AFC000EBF0000C94000EBF0000C9400032500002940045730003AFC000EBF0000C94000EBF0000C9400032500002940011EE0000F780003DE00003600003DE00003600000D800000900045730003AFC000EBF0000C94000EBF0000C9400032500002940011EE0000F780003DE00003600003DE00003600000D800000900011EE0000F780003DE00003600003DE00003600000D800000900003DE00003600000D800000900000D80000090000024000001823872001AB1EC06E503005198C079E5A005B12801799A0011304079E5A005B12801799A001130401A6DA001383C00507F0003804066AA1004BDA0013ECD000E57C01678B001067C004598000300C01678B001067C004598000300C005026000387C000EBF0000BF4066AA1004BDA0013ECD000E57C01678B001067C004598000300C01678B001067C004598000300C005026000387C000EBF0000BF40127D3000D3D800395400026980042B10002DDC000CAD0000A3C0042B10002DDC000CAD0000A3C000F550000C940003DE0000294066AA1004BDA0013ECD000E57C01678B001067C004598000300C01678B001067C004598000300C005026000387C000EBF0000BF40127D3000D3D800395400026980042B10002DDC000CAD0000A3C0042B10002DDC000CAD0000A3C000F550000C940003DE00002940127D3000D3D800395400026980042B10002DDC000CAD0000A3C0042B10002DDC000CAD0000A3C000F550000C940003DE00002940042B10002DDC000CAD0000A3C000F550000C940003DE0000294000F550000C940003DE000029400051000003600000D8000009006D5A2005ACB4014C5E0011304017550001383C00464A0003A5C017550001383C00464A0003A5C00507F00043F8000E5B0000BF40134A9001019C003A15000300C004319000387C000C5D0000A3C004319000387C000C5D0000A3C000EBF0000C9400032500002940134A9001019C003A15000300C004319000387C000C5D0000A3C004319000387C000C5D0000A3C000EBF0000C940003250000294004319000387C000C5D0000A3C000EBF0000C940003250000294000EBF0000C9400032500002940003DE00003600000D800000900134A9001019C003A15000300C004319000387C000C5D0000A3C004319000387C000C5D0000A3C000EBF0000C940003250000294004319000387C000C5D0000A3C000EBF0000C940003250000294000EBF0000C9400032500002940003DE00003600000D80000090004319000387C000C5D0000A3C000EBF0000C940003250000294000EBF0000C9400032500002940003DE00003600000D80000090000EBF0000C9400032500002940003DE00003600000D800000900003DE00003600000D800000900000D80000090000024000001806AD6D0051414016B2D0011304016B2D0011304004E0F0003A5C016B2D0011304004E0F0003A5C004E0F0003A5C0010FE0000BF4012ADB000E09C004067000300C004067000300C000E1F0000A3C004067000300C000E1F0000A3C000E1F0000A3C0003250000294012ADB000E09C004067000300C004067000300C000E1F0000A3C004067000300C000E1F0000A3C000E1F0000A3C0003250000294004067000300C000E1F0000A3C000E1F0000A3C0003250000294000E1F0000A3C000325000029400032500002940000D80000090012ADB000E09C004067000300C004067000300C000E1F0000A3C004067000300C000E1F0000A3C000E1F0000A3C0003250000294004067000300C000E1F0000A3C000E1F0000A3C0003250000294000E1F0000A3C000325000029400032500002940000D80000090004067000300C000E1F0000A3C000E1F0000A3C0003250000294000E1F0000A3C000325000029400032500002940000D80000090000E1F0000A3C000325000029400032500002940000D8000009000032500002940000D800000900000D800000900000240000018013C59001091400424500038040042450003804000E010000BF40042450003804000E010000BF4000E010000BF40002FD00002940042450003804000E010000BF4000E010000BF40002FD0000294000E010000BF40002FD00002940002FD00002940000A500000900042450003804000E010000BF4000E010000BF40002FD0000294000E010000BF40002FD00002940002FD00002940000A50000090000E010000BF40002FD00002940002FD00002940000A500000900002FD00002940000A500000900000A5000009000002400000180042450003804000E010000BF4000E010000BF40002FD0000294000E010000BF40002FD00002940002FD00002940000A50000090000E010000BF40002FD00002940002FD00002940000A500000900002FD00002940000A500000900000A500000900000240000018000E010000BF40002FD00002940002FD00002940000A500000900002FD00002940000A500000900000A5000009000002400000180002FD00002940000A500000900000A5000009000002400000180000A50000090000024000001800002400000180000060000005A
  | 6 => 0x3596A78844697AA22AE87802B7FFC08C6DA6A0B16431059F2A9806E64F08DB91420B3755005B585C0070B06017167C601CC0F800EA60300114B6486B159E0AA57FF056DC43006AF22C161459001B793200E09280010895C165CF2E01BE70600E5721001101E403A4B800046173002403A8003041486B159E0AA57FF056DC43006AF22C161459001B793200E09280010895C165CF2E01BE70600E5721001101E403A4B800046173002403A8003041415A23BA01AF6C900DE17180106B9C038D7B0004447E00232990002F33C039F2880045C95002447780030E940094404000C9D300076938000878486B159E0AA57FF056DC43006AF22C161459001B793200E09280010895C165CF2E01BE70600E5721001101E403A4B800046173002403A8003041415A23BA01AF6C900DE17180106B9C038D7B0004447E00232990002F33C039F2880045C95002447780030E940094404000C9D300076938000878415A23BA01AF6C900DE17180106B9C038D7B0004447E00232990002F33C039F2880045C95002447780030E940094404000C9D300076938000878403995C800455AA002414480030A880094B2E000CA9700077888000889C0099024000D09B0007C5180008E140024ADA00029EB00014F5800017F48DB91420C32D9705A5349807BB51416DDC6C01F86D000E4D80001378E01721F5C01FFBE200E927D0013F2F003AEB1000518A00023A9180030414165CF2E01EF87300E16C68013543C0395F24004F9900022BF08002F33C03A633C00515120023B2B80030E9400906D2000C9D300064E980008784165CF2E01EF87300E16C68013543C0395F24004F9900022BF08002F33C03A633C00515120023B2B80030E9400906D2000C9D300064E980008784039F2880050D7800236C100030A88009091E000CA97000654B8000889C00942C2000D09B000684D80008E14001D4F200029EB00014F5800017F4165CF2E01EF87300E16C68013543C0395F24004F9900022BF08002F33C03A633C00515120023B2B80030E9400906D2000C9D300064E980008784039F2880050D7800236C100030A88009091E000CA97000654B8000889C00942C2000D09B000684D80008E14001D4F200029EB00014F5800017F4039F2880050D7800236C100030A88009091E000CA97000654B8000889C00942C2000D09B000684D80008E14001D4F200029EB00014F5800017F40099024000D7940006BCA00009300001EA460002BD500015EA8000190C002464200034410001A2080001DDC0006882000077700003BB800004448C6DA6A0B4A76206196CB807BB51416ABED801CDAC500FC368001378E016DDC6C01D3A9800FFDF10013F2F003A4F8800496320028C5000030414161459001C3CA200F7C398013543C038A7EE00476D50027CC80002F33C0395F240048B0A0028A8900030E94008EDC6000B05700064E980008784161459001C3CA200F7C398013543C038A7EE00476D50027CC80002F33C0395F240048B0A0028A8900030E94008EDC6000B05700064E980008784038D7B0004814700286BC00030A88008E78A000B018000654B8000889C009091E000B33D000684D80008E14001A136000238500014F5800017F4161459001C3CA200F7C398013543C038A7EE00476D50027CC80002F33C0395F240048B0A0028A8900030E94008EDC6000B05700064E980008784038D7B0004814700286BC00030A88008E78A000B018000654B8000889C009091E000B33D000684D80008E14001A136000238500014F5800017F4038D7B0004814700286BC00030A88008E78A000B018000654B8000889C009091E000B33D000684D80008E14001A136000238500014F5800017F40094B2E000B8A70006BCA00009300001AF2800024C000015EA8000190C001EA4600029B30001A2080001DDC0006882000077700003BB8000044417167C601FFBE200FFDF100162D5403A4F880050AED00285768003774003AEB100051F840028FC200038F88008F9B2000C6ED00063768000878403A4B8000515120028A8900038C08008EDC6000C6D100063688000889C00906D2000CAA5000655280008E14001954A000238500011C2800017F403A4B8000515120028A8900038C08008EDC6000C6D100063688000889C00906D2000CAA5000655280008E14001954A000238500011C2800017F40094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB8000044403A4B8000515120028A8900038C08008EDC6000C6D100063688000889C00906D2000CAA5000655280008E14001954A000238500011C2800017F40094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB800004440094404000D09B000684D80009300001A13600024C000012600000190C001D4F200029B300014D980001DDC0005366000077700003BB800004440024ADA00034410001A20800025840006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C48ABA1E00B11D0205A8C330071E7F41865B2E01EED4500FC368001378E01694D2601C880300EAE6B80121FB003FF7C4004FCBC0028C500003041415B710C01B6DCB00E2CB0801180FC03DF0E6004D50F0027CC80002F33C0385B1A0045F350024AA20002B71400A2A24000C3A500064E98000878415B710C01B6DCB00E2CB0801180FC03DF0E6004D50F0027CC80002F33C0385B1A0045F350024AA20002B71400A2A24000C3A500064E98000878403785C60044E87002447E8002AF8800A1AF0000C2A2000654B8000889C008DB04000A82A0005B4D00007AD4001A136000238500014F5800017F415B710C01B6DCB00E2CB0801180FC03DF0E6004D50F0027CC80002F33C0385B1A0045F350024AA20002B71400A2A24000C3A500064E98000878403785C60044E87002447E8002AF8800A1AF0000C2A2000654B8000889C008DB04000A82A0005B4D00007AD4001A136000238500014F5800017F403785C60044E87002447E8002AF8800A1AF0000C2A2000654B8000889C008DB04000A82A0005B4D00007AD4001A136000238500014F5800017F40090512000AB640005D5A00007D90001AF2800024C000015EA8000190C001AF2800024C000015EA8000190C0006882000077700003BB8000044416D617001F86D000EAE6B80142E5403FF7C40058B5500285768003774003A49F40050AED002523180032E6800A3F08000E3E20006376800087840395C84004F9900024AA20003276800A2A24000E30200063688000889C008ECAE000C6D100059C180007AD4001954A000238500011C2800017F40395C84004F9900024AA20003276800A2A24000E30200063688000889C008ECAE000C6D100059C180007AD4001954A000238500011C2800017F400911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB800004440395C84004F9900024AA20003276800A2A24000E30200063688000889C008ECAE000C6D100059C180007AD4001954A000238500011C2800017F400911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB8000044400911DE000CA970005B4D00007D90001A13600024C000012600000190C001A13600024C000012600000190C0005366000077700003BB80000444001F1460002BD500015EA80001DDC0006882000096100004B08000055C0006882000096100004B08000055C00012C2000015700000AB800000C4167CAA601D049400FC36800142E5403F0DA00050B95002C5AA800377400393600004937D002857680032E6800A15DA000CB9A00071F10000878403824A000480440027CC800032768009F320000C9DA00071810000889C008AFC2000B011000636880007AD40018DA20001EB500011C2800017F403824A000480440027CC800032768009F320000C9DA00071810000889C008AFC2000B011000636880007AD40018DA20001EB500011C2800017F4008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB8000044403824A000480440027CC800032768009F320000C9DA00071810000889C008AFC2000B011000636880007AD40018DA20001EB500011C2800017F4008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB80000444008CA64000B26B000654B80007D90001952E0001F6400012600000190C001952E0001F6400012600000190C0004980000064300003BB80000444001DE2200024F100015EA80001DDC00057AA000077700004B08000055C00057AA000077700004B08000055C00012C2000015700000AB800000C403A980C00518A00028C5000038F8800A3140000E3E200071F100009F78008EA46000C6ED000637680008ACC0018DDA00022B30001159800017F400900EA000C9D300064E980008E1400193A6000238500011C28000190C00193A6000238500011C28000190C000470A000064300003218000044400900EA000C9D300064E980008E1400193A6000238500011C28000190C00193A6000238500011C28000190C000470A0000643000032180000444001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C400900EA000C9D300064E980008E1400193A6000238500011C28000190C00193A6000238500011C28000190C000470A0000643000032180000444001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C4001DA4E00029EB00014F580001DDC00053D6000077700003BB8000055C00053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C88D2F540AE31E40588E81006EB3541694EC401C763700E824A0011C5C81865B2E01EED4500FC368001378E003FF7C4004FCBC0028C5000030414154AFFE01ACC8000DB6E58010C68003879440045F5100240220002A32C03DF0E6004D50F0027CC80002F33C00A2A24000C3A500064E980008784154AFFE01ACC8000DB6E58010C68003879440045F5100240220002A32C03DF0E6004D50F0027CC80002F33C00A2A24000C3A500064E980008784035ED920042A7D002274380028358009028E000AB9C00059358000778C00A1AF0000C2A2000654B8000889C001A136000238500014F5800017F4154AFFE01ACC8000DB6E58010C68003879440045F5100240220002A32C03DF0E6004D50F0027CC80002F33C00A2A24000C3A500064E980008784035ED920042A7D002274380028358009028E000AB9C00059358000778C00A1AF0000C2A2000654B8000889C001A136000238500014F5800017F4035ED920042A7D002274380028358009028E000AB9C00059358000778C00A1AF0000C2A2000654B8000889C001A136000238500014F5800017F4008AB54000A44100055B20000732C001714E0001F6400012788000151C001AF2800024C000015EA8000190C0006882000077700003BB80000444166EAA001EED4500E440180138E5003A75300050B9500249BE80031EA803FF7C40058B5500285768003774000A3F08000E3E2000637680008784037CE0C004D50F0022F9A8002FF600091614000C9DA00058088000778C00A2A24000E30200063688000889C001954A000238500011C2800017F4037CE0C004D50F0022F9A8002FF600091614000C9DA00058088000778C00A2A24000E30200063688000889C001954A000238500011C2800017F4008B92A000C2A200054150000732C001667A0001F640000FB20000151C001A13600024C000012600000190C0005366000077700003BB80000444037CE0C004D50F0022F9A8002FF600091614000C9DA00058088000778C00A2A24000E30200063688000889C001954A000238500011C2800017F4008B92A000C2A200054150000732C001667A0001F640000FB20000151C001A13600024C000012600000190C0005366000077700003BB80000444008B92A000C2A200054150000732C001667A0001F640000FB20000151C001A13600024C000012600000190C0005366000077700003BB80000444001A13600024C000012600000190C0005366000077700003BB800004440006882000096100004B08000055C00012C2000015700000AB800000C4162C86201C763700F76A280138E50039B58A004966300285CA80031EA803F0DA00050B95002C5AA8003774000A15DA000CB9A00071F100008784036F2640045F510026A878002FF60008EDAA000B3B400064ED0000778C009F320000C9DA00071810000889C0018DA20001EB500011C2800017F4036F2640045F510026A878002FF60008EDAA000B3B400064ED0000778C009F320000C9DA00071810000889C0018DA20001EB500011C2800017F400888FC000AB9C00061510000732C00160300001B120000FB20000151C001952E0001F6400012600000190C0004980000064300003BB80000444036F2640045F510026A878002FF60008EDAA000B3B400064ED0000778C009F320000C9DA00071810000889C0018DA20001EB500011C2800017F400888FC000AB9C00061510000732C00160300001B120000FB20000151C001952E0001F6400012600000190C0004980000064300003BB8000044400888FC000AB9C00061510000732C00160300001B120000FB20000151C001952E0001F6400012600000190C0004980000064300003BB80000444001952E0001F6400012600000190C0004980000064300003BB8000044400057AA000077700004B08000055C00012C2000015700000AB800000C403981F0004FCBC0027E5E000377400092C64000CB9A00065CD00008C7000A3140000E3E200071F100009F780018DDA00022B30001159800017F4008C2E6000C3A500061D28000889C00160AE0001EB50000F5A8000151C00193A6000238500011C28000190C000470A0000643000032180000444008C2E6000C3A500061D28000889C00160AE0001EB50000F5A8000151C00193A6000238500011C28000190C000470A000064300003218000044400193A6000238500011C28000190C000470A000064300003218000044400053D6000077700003BB8000055C0000EEE000015700000AB800000C4008C2E6000C3A500061D28000889C00160AE0001EB50000F5A8000151C00193A6000238500011C28000190C000470A000064300003218000044400193A6000238500011C28000190C000470A000064300003218000044400053D6000077700003BB8000055C0000EEE000015700000AB800000C400193A6000238500011C28000190C000470A000064300003218000044400053D6000077700003BB8000055C0000EEE000015700000AB800000C400053D6000077700003BB8000055C0000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C15BFFE001BACD500E3CFE8011DD6803DDA8A004E39400285CA80031EA803DDA8A004E39400285CA80031EA800B16AA000DDD000071F100008784035791600431A0002301F8002AF50009AA1E000BFD800064ED0000778C009AA1E000BFD800064ED0000778C001C604000222700011C2800017F4035791600431A0002301F8002AF50009AA1E000BFD800064ED0000778C009AA1E000BFD800064ED0000778C001C604000222700011C2800017F400835CE000A0D600055F10000641400185440001CCB0000FB20000151C00185440001CCB0000FB20000151C0004980000064300003BB80000444035791600431A0002301F8002AF50009AA1E000BFD800064ED0000778C009AA1E000BFD800064ED0000778C001C604000222700011C2800017F400835CE000A0D600055F10000641400185440001CCB0000FB20000151C00185440001CCB0000FB20000151C0004980000064300003BB8000044400835CE000A0D600055F10000641400185440001CCB0000FB20000151C00185440001CCB0000FB20000151C0004980000064300003BB8000044400185440001CCB0000FB20000151C0004980000064300003BB800004440004980000064300003BB8000044400012C2000015700000AB800000C40385830004DE3800243F600031EA8009F978000DDD000065CD00008C70009F978000DDD000065CD00008C70001C7C400027DE0001159800017F400880F2000BCCF00056E28000778C001874A00022270000F5A8000151C001874A00022270000F5A8000151C000470A000064300003218000044400880F2000BCCF00056E28000778C001874A00022270000F5A8000151C001874A00022270000F5A8000151C000470A0000643000032180000444001874A00022270000F5A8000151C000470A0000643000032180000444000470A00006430000321800004440000EEE000015700000AB800000C400880F2000BCCF00056E28000778C001874A00022270000F5A8000151C001874A00022270000F5A8000151C000470A0000643000032180000444001874A00022270000F5A8000151C000470A0000643000032180000444000470A00006430000321800004440000EEE000015700000AB800000C4001874A00022270000F5A8000151C000470A0000643000032180000444000470A00006430000321800004440000EEE000015700000AB800000C4000470A00006430000321800004440000EEE000015700000AB800000C40000EEE000015700000AB800000C400002AE000003100000188000001C037327800471720026F1C00031EA8009BC70000C7AA0006EE800008C70009BC70000C7AA0006EE800008C70001BBA0000231C00013EF000017F400844AE000A8CB0005E678000778C001799E0001DE300011138000151C001799E0001DE300011138000151C000444E000054700003218000044400844AE000A8CB0005E678000778C001799E0001DE300011138000151C001799E0001DE300011138000151C000444E0000547000032180000444001799E0001DE300011138000151C000444E0000547000032180000444000444E00005470000321800004440000C86000011100000AB800000C400844AE000A8CB0005E678000778C001799E0001DE300011138000151C001799E0001DE300011138000151C000444E0000547000032180000444001799E0001DE300011138000151C000444E0000547000032180000444000444E00005470000321800004440000C86000011100000AB800000C4001799E0001DE300011138000151C000444E0000547000032180000444000444E00005470000321800004440000C86000011100000AB800000C4000444E00005470000321800004440000C86000011100000AB800000C40000C86000011100000AB800000C400002AE000003100000188000001C008A5B2000C105000608280008784001820A00021E100010F0800017F4001820A00021E100010F0800017F400043C200005FD00002FE80000444001820A00021E100010F0800017F400043C200005FD00002FE8000044400043C200005FD00002FE800004440000BFA00001110000088800000C4001820A00021E100010F0800017F400043C200005FD00002FE8000044400043C200005FD00002FE800004440000BFA00001110000088800000C400043C200005FD00002FE800004440000BFA00001110000088800000C40000BFA00001110000088800000C40000222000003100000188000001C001820A00021E100010F0800017F400043C200005FD00002FE8000044400043C200005FD00002FE800004440000BFA00001110000088800000C400043C200005FD00002FE800004440000BFA00001110000088800000C40000BFA00001110000088800000C40000222000003100000188000001C00043C200005FD00002FE800004440000BFA00001110000088800000C40000BFA00001110000088800000C40000222000003100000188000001C0000BFA00001110000088800000C40000222000003100000188000001C0000222000003100000188000001C00000620000007000000380000005D
  | 7 => 0x22BC0B5904CAF48084DA1B4400A8A1A504E78E9180AB905B00ADAD4900171F9784F1BB1E00AD564300B0154680178D8500B1BE5F0017FAC300185F118003237F04BB3CFC00A5BBBB00A8A31B8016873480AB1FF08017139E001784730003069800AD0CE5001764C00017F7EA80031A0900184E1380032EFB0003434C000077D904BB3CFC00A5BBBB00A8A31B8016873480AB1FF08017139E001784730003069800AD0CE5001764C00017F7EA80031A0900184E1380032EFB0003434C000077D900A822BC0016B62780174E45000302B60017CB3E80031D6D0003333F000075BE0018335B00032CD900034A108000797D00035A8300007CF600008FB8000011F704BB3CFC00A5BBBB00A8A31B8016873480AB1FF08017139E001784730003069800AD0CE5001764C00017F7EA80031A0900184E1380032EFB0003434C000077D900A822BC0016B62780174E45000302B60017CB3E80031D6D0003333F000075BE0018335B00032CD900034A108000797D00035A8300007CF600008FB8000011F700A822BC0016B62780174E45000302B60017CB3E80031D6D0003333F000075BE0018335B00032CD900034A108000797D00035A8300007CF600008FB8000011F7001811180003284F00034619800078F100035D5080007D70800090D00000121A0003740D000080D100009610000012C20000AD40000015A8000015A8000002B504F1BB1E00BA78AE00AE82FE00198FA000B06B36801A005D8017EAF400037B7980B2349A001A55780018508200038EE0001888A88003A04E80033C06000077D900AD0CE500199B6E00179E9C8003767F8017FD9380038DB300032AA9000075BE00185CB800039EFE80033E130000797D000346A900007CF600007CF6000011F700AD0CE500199B6E00179E9C8003767F8017FD9380038DB300032AA9000075BE00185CB800039EFE80033E130000797D000346A900007CF600007CF6000011F70018335B00039A240003388D000078F1000347E780007D7080007D708000121A00035B01000080D1000080D1000012C200008E87800015A8000015A8000002B500AD0CE500199B6E00179E9C8003767F8017FD9380038DB300032AA9000075BE00185CB800039EFE80033E130000797D000346A900007CF600007CF6000011F70018335B00039A240003388D000078F1000347E780007D7080007D708000121A00035B01000080D1000080D1000012C200008E87800015A8000015A8000002B50018335B00039A240003388D000078F1000347E780007D7080007D708000121A00035B01000080D1000080D1000012C200008E87800015A8000015A8000002B50003740D000084A5000084A500001355000094458000168800001688000002D10000AC4400001A4000001A400000034800001A4000000348000003480000006904E78E9180AE8AF380BA78AE00198FA000AF235A00181B9E801A005D80037B7980B06B368018616C801A557800038EE0001851FC0003507D8003A04E800077D900AB1FF08017A99F00199B6E0003767F8017BB8C00033D6E80038DB3000075BE0017FD9380034A3A80039EFE8000797D00033E5200006F6600007CF6000011F700AB1FF08017A99F00199B6E0003767F8017BB8C00033D6E80038DB3000075BE0017FD9380034A3A80039EFE8000797D00033E5200006F6600007CF6000011F70017CB3E800343F080039A24000078F100033CB500006F5480007D708000121A000347E780007129800080D1000012C2000080D1000012C2000015A8000002B500AB1FF08017A99F00199B6E0003767F8017BB8C00033D6E80038DB3000075BE0017FD9380034A3A80039EFE8000797D00033E5200006F6600007CF6000011F70017CB3E800343F080039A24000078F100033CB500006F5480007D708000121A000347E780007129800080D1000012C2000080D1000012C2000015A8000002B50017CB3E800343F080039A24000078F100033CB500006F5480007D708000121A000347E780007129800080D1000012C2000080D1000012C2000015A8000002B500035D508000742F000084A500001355000084A50000135500001688000002D1000094458000159300001A400000034800001A4000000348000003480000006900B1BE5F001A5578001A55780003E6B4001851FC000398D7800398D78000873A801888A88003A5990003A59900008A82800341AF00007B6000007B60000011F700184E1380039EFE80039EFE80008A0800033E5200007B6000007B600000121A000346A900007D8900007D89000012C200007D89000012C2000012C2000002B500184E1380039EFE80039EFE80008A0800033E5200007B6000007B600000121A000346A900007D8900007D89000012C200007D89000012C2000012C2000002B500035A83000080D1000080D100001355000080D10000135500001355000002D100008E878000159300001593000003480000159300000348000003480000006900184E1380039EFE80039EFE80008A0800033E5200007B6000007B600000121A000346A900007D8900007D89000012C200007D89000012C2000012C2000002B500035A83000080D1000080D100001355000080D10000135500001355000002D100008E878000159300001593000003480000159300000348000003480000006900035A83000080D1000080D100001355000080D10000135500001355000002D100008E87800015930000159300000348000015930000034800000348000000690000AD4000001A4000001A400000040000001A4000000400000004000000008000001A400000040000000400000000800000040000000080000000800000001004DA1B4400AB7E0F00AEED1D0017D37680BA78AE00198FA0001A005D80037B7980AE82FE0017DE6800187B1C00034777801A557800038EE00003A04E800077D900A8A31B8017108E0017BF1A00032ED100199B6E0003767F80038DB3000075BE00179E9C80032E7D000350CE00006DDE00039EFE8000797D00007CF6000011F700A8A31B8017108E0017BF1A00032ED100199B6E0003767F80038DB3000075BE00179E9C80032E7D000350CE00006DDE00039EFE8000797D00007CF6000011F700174E45000323A9000348E700006CD780039A24000078F100007D708000121A0003388D00006B0D0000730900001092000080D1000012C2000015A8000002B500A8A31B8017108E0017BF1A00032ED100199B6E0003767F80038DB3000075BE00179E9C80032E7D000350CE00006DDE00039EFE8000797D00007CF6000011F700174E45000323A9000348E700006CD780039A24000078F100007D708000121A0003388D00006B0D0000730900001092000080D1000012C2000015A8000002B500174E45000323A9000348E700006CD780039A24000078F100007D708000121A0003388D00006B0D0000730900001092000080D1000012C2000015A8000002B50003461980006CDB00007555000010E6000084A50000135500001688000002D1000084A50000135500001688000002D100001A4000000348000003480000006900B01546801A005D80187B1C00039936001A55780003E6B4000398D78000873A80185082000398D780035A7500007DCB8003A59900008A8280007B60000011F70017F7EA80038DB3000350CE00007CD680039EFE80008A0800007B600000121A00033E1300007B60000071490000109200007D89000012C2000012C2000002B50017F7EA80038DB3000350CE00007CD680039EFE80008A0800007B600000121A00033E1300007B60000071490000109200007D89000012C2000012C2000002B500034A1080007D7080007309000010E6000080D10000135500001355000002D1000080D10000135500001355000002D1000015930000034800000348000000690017F7EA80038DB3000350CE00007CD680039EFE80008A0800007B600000121A00033E1300007B60000071490000109200007D89000012C2000012C2000002B500034A1080007D7080007309000010E6000080D10000135500001355000002D1000080D10000135500001355000002D10000159300000348000003480000006900034A1080007D7080007309000010E6000080D10000135500001355000002D1000080D10000135500001355000002D1000015930000034800000348000000690000961000001688000016880000034800001A4000000400000004000000008000001A400000040000000400000000800000040000000080000000800000001000ADAD49001839AB801A005D80039936001A005D800399360003E6B40000873A8017EAF400034FB6000398D780007DCB800398D780007DCB80008A82800011F7001784730003434F80038DB300007CD680038DB300007CD680008A080000121A00032AA900006F4300007B600000109200007B6000001092000012C2000002B5001784730003434F80038DB300007CD680038DB300007CD680008A080000121A00032AA900006F4300007B600000109200007B6000001092000012C2000002B50003333F0000709680007D70800010E600007D70800010E600001355000002D100007D70800010E600001355000002D100001355000002D10000034800000069001784730003434F80038DB300007CD680038DB300007CD680008A080000121A00032AA900006F4300007B600000109200007B6000001092000012C2000002B50003333F0000709680007D70800010E600007D70800010E600001355000002D100007D70800010E600001355000002D100001355000002D100000348000000690003333F0000709680007D70800010E600007D70800010E600001355000002D100007D70800010E600001355000002D100001355000002D10000034800000069000090D000001378000016880000034800001688000003480000040000000080000016880000034800000400000000800000040000000080000000800000001000185F118003A04E8003A04E80008A828003A04E80008A8280008A82800014AC00033C0600007B6000007B600000126000007B600000126000001260000002B50003434C00007CF600007CF6000012C200007CF6000012C2000012C2000002D100007CF6000012C2000012C2000002D1000012C2000002D1000002D1000000690003434C00007CF600007CF6000012C200007CF6000012C2000012C2000002D100007CF6000012C2000012C2000002D1000012C2000002D1000002D10000006900008FB8000015A8000015A800000348000015A8000003480000034800000080000015A8000003480000034800000080000003480000008000000080000000100003434C00007CF600007CF6000012C200007CF6000012C2000012C2000002D100007CF6000012C2000012C2000002D1000012C2000002D1000002D10000006900008FB8000015A8000015A800000348000015A8000003480000034800000080000015A80000034800000348000000800000034800000080000000800000001000008FB8000015A8000015A800000348000015A8000003480000034800000080000015A800000348000003480000008000000348000000800000008000000010000015A800000348000003480000008000000348000000800000008000000010000003480000008000000080000000100000008000000010000000100000000204CAF48080A8F95D00AB7E0F00173AD680AE8AF38017D120001839AB800338FD00BA78AE00198FA0001A005D80037B79801A557800038EE00003A04E800077D900A5BBBB001698A40017108E000311148017A99F00032E530003434F80006B1B00199B6E0003767F80038DB3000075BE00039EFE8000797D00007CF6000011F700A5BBBB001698A40017108E000311148017A99F00032E530003434F80006B1B00199B6E0003767F80038DB3000075BE00039EFE8000797D00007CF6000011F70016B62780030C79000323A9000066CC800343F080006CB8000070968000102900039A24000078F100007D708000121A000080D1000012C2000015A8000002B500A5BBBB001698A40017108E000311148017A99F00032E530003434F80006B1B00199B6E0003767F80038DB3000075BE00039EFE8000797D00007CF6000011F70016B62780030C79000323A9000066CC800343F080006CB8000070968000102900039A24000078F100007D708000121A000080D1000012C2000015A8000002B50016B62780030C79000323A9000066CC800343F080006CB8000070968000102900039A24000078F100007D708000121A000080D1000012C2000015A8000002B50003284F000068C100006CDB00000FAB0000742F000010E6000013780000026F000084A50000135500001688000002D100001A4000000348000003480000006900AD564300198FA00017DE6800037FD60018616C8003993600034FB600007B9F001A55780003E6B4000398D78000873A8003A59900008A8280007B60000011F7001764C00003767F80032E7D0000776200034A3A80007CD680006F430000102900039EFE80008A0800007B600000121A00007D89000012C2000012C2000002B5001764C00003767F80032E7D0000776200034A3A80007CD680006F430000102900039EFE80008A0800007B600000121A00007D89000012C2000012C2000002B500032CD9000078F100006B0D00000FAB00007129800010E6000010E60000026F000080D10000135500001355000002D100001593000003480000034800000069001764C00003767F80032E7D0000776200034A3A80007CD680006F430000102900039EFE80008A0800007B600000121A00007D89000012C2000012C2000002B500032CD9000078F100006B0D00000FAB00007129800010E6000010E60000026F000080D10000135500001355000002D10000159300000348000003480000006900032CD9000078F100006B0D00000FAB00007129800010E6000010E60000026F000080D10000135500001355000002D100001593000003480000034800000069000080D10000135500001355000002D10000159300000348000003480000006900001A400000040000000400000000800000040000000080000000800000001000AB905B0017D12000198FA000037FD600181B9E800351920003993600007B9F001A005D800399360003E6B40000873A800398D780007DCB80008A82800011F70017139E00032E530003767F8000776200033D6E8000711800007CD68000102900038DB300007CD680008A080000121A00007B6000001092000012C2000002B50017139E00032E530003767F8000776200033D6E8000711800007CD68000102900038DB300007CD680008A080000121A00007B6000001092000012C2000002B500031D6D00006CB8000078F100000FAB00006F5480000EE7000010E60000026F00007D70800010E600001355000002D100001355000002D100000348000000690017139E00032E530003767F8000776200033D6E8000711800007CD68000102900038DB300007CD680008A080000121A00007B6000001092000012C2000002B500031D6D00006CB8000078F100000FAB00006F5480000EE7000010E60000026F00007D70800010E600001355000002D100001355000002D1000003480000006900031D6D00006CB8000078F100000FAB00006F5480000EE7000010E60000026F00007D70800010E600001355000002D100001355000002D1000003480000006900007D70800010E600001355000002D100001355000002D1000003480000006900001688000003480000040000000080000004000000008000000080000000100017FAC300038EE000038EE00000873A8003507D80007DCB80007DCB8000128A0003A04E80008A8280008A82800014AC00007B600000126000001260000002B500032EFB0000797D0000797D0000121A00006F6600001092000010920000026F00007CF6000012C2000012C2000002D1000012C2000002D1000002D10000006900032EFB0000797D0000797D0000121A00006F6600001092000010920000026F00007CF6000012C2000012C2000002D1000012C2000002D1000002D10000006900007CF6000012C2000012C2000002D1000012C2000002D1000002D100000069000015A80000034800000348000000800000034800000080000000800000001000032EFB0000797D0000797D0000121A00006F6600001092000010920000026F00007CF6000012C2000012C2000002D1000012C2000002D1000002D10000006900007CF6000012C2000012C2000002D1000012C2000002D1000002D100000069000015A80000034800000348000000800000034800000080000000800000001000007CF6000012C2000012C2000002D1000012C2000002D1000002D100000069000015A800000348000003480000008000000348000000800000008000000010000015A800000348000003480000008000000348000000800000008000000010000003480000008000000080000000100000008000000010000000100000000200A8A1A500173AD68017D37680033D9C00198FA000037FD60003993600007B9F00198FA000037FD60003993600007B9F0003E6B40000873A80008A82800011F7001687348003111480032ED100006CBF0003767F8000776200007CD6800010290003767F8000776200007CD68000102900008A080000121A000012C2000002B5001687348003111480032ED100006CBF0003767F8000776200007CD6800010290003767F8000776200007CD68000102900008A080000121A000012C2000002B5000302B6000066CC80006CD780000DEB000078F100000FAB000010E60000026F000078F100000FAB000010E60000026F00001355000002D10000034800000069001687348003111480032ED100006CBF0003767F8000776200007CD6800010290003767F8000776200007CD68000102900008A080000121A000012C2000002B5000302B6000066CC80006CD780000DEB000078F100000FAB000010E60000026F000078F100000FAB000010E60000026F00001355000002D10000034800000069000302B6000066CC80006CD780000DEB000078F100000FAB000010E60000026F000078F100000FAB000010E60000026F00001355000002D10000034800000069000078F100000FAB000010E60000026F00001355000002D1000003480000006900001355000002D100000348000000690000040000000080000000800000001000178D8500037B798003477780007B9F00038EE00000873A80007DCB8000128A00038EE00000873A80007DCB8000128A00008A82800014AC00001260000002B500031A09000075BE00006DDE000010290000797D0000121A000010920000026F0000797D0000121A000010920000026F000012C2000002D1000002D10000006900031A09000075BE00006DDE000010290000797D0000121A000010920000026F0000797D0000121A000010920000026F000012C2000002D1000002D1000000690000797D0000121A000010920000026F000012C2000002D1000002D100000069000012C2000002D1000002D1000000690000034800000080000000800000001000031A09000075BE00006DDE000010290000797D0000121A000010920000026F0000797D0000121A000010920000026F000012C2000002D1000002D1000000690000797D0000121A000010920000026F000012C2000002D1000002D100000069000012C2000002D1000002D100000069000003480000008000000080000000100000797D0000121A000010920000026F000012C2000002D1000002D100000069000012C2000002D1000002D10000006900000348000000800000008000000010000012C2000002D1000002D10000006900000348000000800000008000000010000003480000008000000080000000100000008000000010000000100000000200171F97800338FD00037B7980007B9F00037B7980007B9F0000873A8000128A00037B7980007B9F0000873A8000128A0000873A8000128A000014AC000002B50003069800006B1B000075BE00001029000075BE000010290000121A0000026F000075BE000010290000121A0000026F0000121A0000026F000002D1000000690003069800006B1B000075BE00001029000075BE000010290000121A0000026F000075BE000010290000121A0000026F0000121A0000026F000002D100000069000075BE000010290000121A0000026F0000121A0000026F000002D1000000690000121A0000026F000002D100000069000002D10000006900000080000000100003069800006B1B000075BE00001029000075BE000010290000121A0000026F000075BE000010290000121A0000026F0000121A0000026F000002D100000069000075BE000010290000121A0000026F0000121A0000026F000002D1000000690000121A0000026F000002D100000069000002D1000000690000008000000010000075BE000010290000121A0000026F0000121A0000026F000002D1000000690000121A0000026F000002D100000069000002D10000006900000080000000100000121A0000026F000002D100000069000002D1000000690000008000000010000002D1000000690000008000000010000000800000001000000010000000020003237F000077D9000077D9000011F7000077D9000011F7000011F7000002B5000077D9000011F7000011F7000002B5000011F7000002B5000002B500000069000077D9000011F7000011F7000002B5000011F7000002B5000002B500000069000011F7000002B5000002B500000069000002B5000000690000006900000010000077D9000011F7000011F7000002B5000011F7000002B5000002B500000069000011F7000002B5000002B500000069000002B5000000690000006900000010000011F7000002B5000002B500000069000002B5000000690000006900000010000002B500000069000000690000001000000069000000100000001000000002000077D9000011F7000011F7000002B5000011F7000002B5000002B500000069000011F7000002B5000002B500000069000002B5000000690000006900000010000011F7000002B5000002B500000069000002B5000000690000006900000010000002B500000069000000690000001000000069000000100000001000000002000011F7000002B5000002B500000069000002B5000000690000006900000010000002B500000069000000690000001000000069000000100000001000000002000002B500000069000000690000001000000069000000100000001000000002000000690000001000000010000000020000001000000002000000020000000060
  | 8 => 0x24795650411B9222C847AE08C20225016E0485FF334022D9C7D808CED57400424732848E5FB060232CA59808EAFF2800436366808FDD58A004479DF80115D8E60007EEDF04621089C021D18A88089658D20040D62E008B345C200423FA38010D7FF60007B144008C9930A00430F8600112204E0007DD6600115823A00080C6700020EC500001086904621089C021D18A88089658D20040D62E008B345C200423FA38010D7FF60007B144008C9930A00430F8600112204E0007DD6600115823A00080C6700020EC5000010869008910C90004156848010B79260007AA0C0011079000007E6768002064CC0001048E001149EFA0008093E80021323400010BF000021C94E000112E900004DC1C0000228F04621089C021D18A88089658D20040D62E008B345C200423FA38010D7FF60007B144008C9930A00430F8600112204E0007DD6600115823A00080C6700020EC5000010869008910C90004156848010B79260007AA0C0011079000007E6768002064CC0001048E001149EFA0008093E80021323400010BF000021C94E000112E900004DC1C0000228F008910C90004156848010B79260007AA0C0011079000007E6768002064CC0001048E001149EFA0008093E80021323400010BF000021C94E000112E900004DC1C0000228F001133F640007FED3800210F4200010ADF00021E5DA000113EF80004E4F8000022CE00022B73200011AB4000050E50000023F400005BD64000028D100000A34400000489048E5FB0602585CF1008DA474200487BC9008F01FA800499B2B80111A6F20008B37B809049F50004A727C00115B3FC0008DF0A80117D944000905AD80020AAB000010869008C9930A0048A1130010EBC940008A9C3001127FCA0008DDCF8002017080001048E0011645A00009044880020C59800010BF00002114AC000112E9000044BA40000228F008C9930A0048A1130010EBC940008A9C3001127FCA0008DDCF8002017080001048E0011645A00009044880020C59800010BF00002114AC000112E9000044BA40000228F001149EFA0008F95500020948A00010ADF00021231C000113EF800044FBE000022CE00021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489008C9930A0048A1130010EBC940008A9C3001127FCA0008DDCF8002017080001048E0011645A00009044880020C59800010BF00002114AC000112E9000044BA40000228F001149EFA0008F95500020948A00010ADF00021231C000113EF800044FBE000022CE00021D3A400011AB4000046AD0000023F400004D442000028D100000A34400000489001149EFA0008F95500020948A00010ADF00021231C000113EF800044FBE000022CE00021D3A400011AB4000046AD0000023F400004D442000028D100000A3440000048900022B73200012240000048900000024F00000500E200002A4B00000A92C000004B300005B7100000306900000C1A40000056100000C1A400000561000001584000000990485FF3340236B44F0096173C400487BC9008E1A4EC0044E900801266CAE0008B37B808F01FA8004599F780129C9F00008DF0A80115BF4E000857958002416B600010869008B345C20043CAEE00122844C0008A9C30010FE90000082E4800023773E0001048E001127FCA00084AE900024112200010BF000020C73C0000F8C1000044BA40000228F008B345C20043CAEE00122844C0008A9C30010FE90000082E4800023773E0001048E001127FCA00084AE900024112200010BF000020C73C0000F8C1000044BA40000228F00110790000083CA300023E55400010ADF00020BB180000F8B6800044FBE000022CE00021231C0000FC7C800046AD0000023F4000046AD0000023F400000A34400000489008B345C20043CAEE00122844C0008A9C30010FE90000082E4800023773E0001048E001127FCA00084AE900024112200010BF000020C73C0000F8C1000044BA40000228F00110790000083CA300023E55400010ADF00020BB180000F8B6800044FBE000022CE00021231C0000FC7C800046AD0000023F4000046AD0000023F400000A3440000048900110790000083CA300023E55400010ADF00020BB180000F8B6800044FBE000022CE00021231C0000FC7C800046AD0000023F4000046AD0000023F400000A3440000048900021E5DA00010284000048900000024F0000048900000024F000000A92C000004B30000500E2000028B300000C1A40000056100000C1A40000056100000158400000099008FDD58A004A727C00129C9F000099FAB00115BF4E0008F70900023DC240001262B80117D94400091317000244C5C00012C9180020E2CC00010FCB000043F2C0000228F00115823A0009044880024112200012BA000020C73C00010FE0000043F80000022CE0002114AC000114390000450E4000023F40000450E4000023F4000008FD00000048900115823A0009044880024112200012BA000020C73C00010FE0000043F80000022CE0002114AC000114390000450E4000023F40000450E4000023F4000008FD00000048900021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900115823A0009044880024112200012BA000020C73C00010FE0000043F80000022CE0002114AC000114390000450E4000023F40000450E4000023F4000008FD00000048900021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900021C94E00011AB4000046AD0000024F0000046AD0000024F00000093C0000004B300004D442000028B300000A2CC0000056100000A2CC000005610000015840000009900005BD640000306900000C1A40000066840000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014447AE08C2022DC80B008DF54D800442EC48096173C400487BC9001266CAE0008B37B808DA474200444C780011771E80008436780129C9F00008DF0A8002416B6000108690089658D2004242CC00110097C00080D0F00122844C0008A9C300023773E0001048E0010EBC9400080CE50002167320000F58E00024112200010BF0000044BA40000228F0089658D2004242CC00110097C00080D0F00122844C0008A9C300023773E0001048E0010EBC9400080CE50002167320000F58E00024112200010BF0000044BA40000228F0010B79260007F434000211F800000F38B80023E55400010ADF000044FBE000022CE00020948A0000F0630000400E000002046000046AD0000023F400000A344000004890089658D2004242CC00110097C00080D0F00122844C0008A9C300023773E0001048E0010EBC9400080CE50002167320000F58E00024112200010BF0000044BA40000228F0010B79260007F434000211F800000F38B80023E55400010ADF000044FBE000022CE00020948A0000F0630000400E000002046000046AD0000023F400000A344000004890010B79260007F434000211F800000F38B80023E55400010ADF000044FBE000022CE00020948A0000F0630000400E000002046000046AD0000023F400000A34400000489000210F420000F3FF000041340000020D9000048900000024F000000A92C000004B3000048900000024F000000A92C000004B300000C1A40000056100000158400000099008EAFF2800499B2B8011771E80008F7C600129C9F000099FAB00023DC240001262B80115B3FC0008F70900021BE5000011458800244C5C00012C91800043F2C0000228F00112204E0008DDCF8002167320001127580024112200012BA0000043F80000022CE00020C59800010FE000003F2C4000020460000450E4000023F4000008FD00000048900112204E0008DDCF8002167320001127580024112200012BA0000043F80000022CE00020C59800010FE000003F2C4000020460000450E4000023F4000008FD000000489000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC000005610000015840000009900112204E0008DDCF8002167320001127580024112200012BA0000043F80000022CE00020C59800010FE000003F2C4000020460000450E4000023F4000008FD000000489000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000213234000113EF8000400E0000020D9000046AD0000024F00000093C0000004B3000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000050E5000002A4B00000A92C0000056100000C1A4000006684000019A1000000B640000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014408CED57400453439801266CAE0008F7C6001266CAE0008F7C6000267EAC0001262B80111A6F20008577600023DC240001145880023DC240001145880004B2460000228F0010D7FF600083B4880023773E0001127580023773E0001127580004AE80000022CE0002017080000F882000043F8000002046000043F8000002046000008FD0000004890010D7FF600083B4880023773E0001127580023773E0001127580004AE80000022CE0002017080000F882000043F8000002046000043F8000002046000008FD0000004890002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B3000001584000000990010D7FF600083B4880023773E0001127580023773E0001127580004AE80000022CE0002017080000F882000043F8000002046000043F8000002046000008FD0000004890002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B3000001584000000990002064CC0000FB2C800044FBE000020D9000044FBE000020D90000093C0000004B3000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900004E4F80000253B00000A92C0000056100000A92C000005610000019A1000000B640000A92C000005610000019A1000000B64000019A1000000B64000002D90000001440115D8E6000905AD8002416B600012C918002416B600012C9180004B2460000271800020AAB000010FCB000043F2C0000234C000043F2C0000234C000008D300000048900020EC50000112E9000044BA4000023F4000044BA4000023F4000008FD0000004B3000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900020EC50000112E9000044BA4000023F4000044BA4000023F4000008FD0000004B3000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440020EC50000112E9000044BA4000023F4000044BA4000023F4000008FD0000004B3000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440004DC1C000028D100000A3440000056100000A34400000561000001584000000B640000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D90000001440000005100000002446E488B202266638008B7202C0042A648808DAD13C004429A400114D0E60008228D0096173C400487BC9001266CAE0008B37B80129C9F00008DF0A8002416B6000108690087462A200410E44001090B300007CA298010F2BB800080C1D80020ED220000F00F00122844C0008A9C300023773E0001048E00024112200010BF0000044BA40000228F0087462A200410E44001090B300007CA298010F2BB800080C1D80020ED220000F00F00122844C0008A9C300023773E0001048E00024112200010BF0000044BA40000228F001055A120007BFB40001FD0D00000E7A680020F28C0000F35700003ECB200001F8900023E55400010ADF000044FBE000022CE000046AD0000023F400000A344000004890087462A200410E44001090B300007CA298010F2BB800080C1D80020ED220000F00F00122844C0008A9C300023773E0001048E00024112200010BF0000044BA40000228F001055A120007BFB40001FD0D00000E7A680020F28C0000F35700003ECB200001F8900023E55400010ADF000044FBE000022CE000046AD0000023F400000A34400000489001055A120007BFB40001FD0D00000E7A680020F28C0000F35700003ECB200001F8900023E55400010ADF000044FBE000022CE000046AD0000023F400000A344000004890001FFB4E0000EBA100003CFFC00001EB7000040A10000020D90000094EC00000423000048900000024F000000A92C000004B300000C1A40000056100000158400000099008CB296600487BC90011131E00008BEED0011667DE0008F7C6000215DD80001100A00129C9F000099FAB00023DC240001262B800244C5C00012C91800043F2C0000228F0010C3E180008A9C3000203394000107C1000212BA40001127580003E20800001F8900024112200012BA0000043F80000022CE0000450E4000023F4000008FD0000004890010C3E180008A9C3000203394000107C1000212BA40001127580003E20800001F8900024112200012BA0000043F80000022CE0000450E4000023F4000008FD0000004890002024FA00010ADF00003C18C00001EB700003F1F2000020D900000836400000423000046AD0000024F00000093C0000004B300000A2CC00000561000001584000000990010C3E180008A9C3000203394000107C1000212BA40001127580003E20800001F8900024112200012BA0000043F80000022CE0000450E4000023F4000008FD0000004890002024FA00010ADF00003C18C00001EB700003F1F2000020D900000836400000423000046AD0000024F00000093C0000004B300000A2CC00000561000001584000000990002024FA00010ADF00003C18C00001EB700003F1F2000020D900000836400000423000046AD0000024F00000093C0000004B300000A2CC0000056100000158400000099000046AD0000024F00000093C0000004B300000A2CC000005610000015840000009900000C1A4000006684000019A1000000B64000019A1000000B64000002D900000014408B671F6004429A400121EF240008BEED00113A40200085BA500023DF180001100A001266CAE0008F7C6000267EAC0001262B80023DC240001145880004B2460000228F00108FE8E00080C1D80022A70C000107C100020B9200000FBDF0000449D600001F8900023773E0001127580004AE80000022CE000043F8000002046000008FD00000048900108FE8E00080C1D80022A70C000107C100020B9200000FBDF0000449D600001F8900023773E0001127580004AE80000022CE000043F8000002046000008FD0000004890001F99DA0000F357000042B7C00001EB700003E2DA00001D7300000836400000423000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900108FE8E00080C1D80022A70C000107C100020B9200000FBDF0000449D600001F8900023773E0001127580004AE80000022CE000043F8000002046000008FD0000004890001F99DA0000F357000042B7C00001EB700003E2DA00001D7300000836400000423000044FBE000020D90000093C0000004B30000093C0000004B3000001584000000990001F99DA0000F357000042B7C00001EB700003E2DA00001D7300000836400000423000044FBE000020D90000093C0000004B30000093C0000004B300000158400000099000044FBE000020D90000093C0000004B30000093C0000004B30000015840000009900000A92C000005610000019A1000000B64000019A1000000B64000002D90000001440111E77E0008DF0A800237C2A0001262B800215E56000114588000451620000238B0002416B600012C9180004B24600002718000043F2C0000234C000008D300000048900020319C00010BF0000042FC0000022CE00003E3040000204600000811800000423000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900020319C00010BF0000042FC0000022CE00003E3040000204600000811800000423000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC00000099000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900000A34400000561000001584000000B6400001584000000B64000002D90000001440020319C00010BF0000042FC0000022CE00003E3040000204600000811800000423000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC00000099000044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900000A34400000561000001584000000B6400001584000000B64000002D900000014400044BA4000023F4000008FD0000004B3000008FD0000004B30000012CC0000009900000A34400000561000001584000000B6400001584000000B64000002D90000001440000A34400000561000001584000000B6400001584000000B64000002D900000014400001584000000B64000002D9000000144000002D900000014400000051000000024089405B80042A64880110BB1200082E7200121EF240008BEED00023DF180001100A00121EF240008BEED00023DF180001100A000267EAC0001262B80004B2460000228F0010358B80007CA2980020343C0000F34200022A70C000107C10000449D600001F8900022A70C000107C10000449D600001F8900004AE80000022CE000008FD0000004890010358B80007CA2980020343C0000F34200022A70C000107C10000449D600001F8900022A70C000107C10000449D600001F8900004AE80000022CE000008FD0000004890001EA8300000E7A680003CE2E00001BBA000042B7C00001EB700000836400000423000042B7C00001EB7000008364000004230000093C0000004B3000001584000000990010358B80007CA2980020343C0000F34200022A70C000107C10000449D600001F8900022A70C000107C10000449D600001F8900004AE80000022CE000008FD0000004890001EA8300000E7A680003CE2E00001BBA000042B7C00001EB700000836400000423000042B7C00001EB7000008364000004230000093C0000004B3000001584000000990001EA8300000E7A680003CE2E00001BBA000042B7C00001EB700000836400000423000042B7C00001EB7000008364000004230000093C0000004B300000158400000099000042B7C00001EB7000008364000004230000093C0000004B3000001584000000990000093C0000004B3000001584000000990000019A1000000B64000002D9000000144010D8D9A0008B37B800210D9E0001100A000237C2A0001262B8000451620000238B000237C2A0001262B8000451620000238B00004B24600002718000008D30000004890001F75980001048E00003D63800001F89000042FC0000022CE00000811800000423000042FC0000022CE00000811800000423000008FD0000004B30000012CC000000990001F75980001048E00003D63800001F89000042FC0000022CE00000811800000423000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000008FD0000004B30000012CC00000099000001584000000B64000002D9000000144001F75980001048E00003D63800001F89000042FC0000022CE00000811800000423000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000008FD0000004B30000012CC00000099000001584000000B64000002D900000014400042FC0000022CE00000811800000423000008FD0000004B30000012CC00000099000008FD0000004B30000012CC00000099000001584000000B64000002D900000014400008FD0000004B30000012CC00000099000001584000000B64000002D900000014400001584000000B64000002D9000000144000002D90000001440000005100000002401091CCA0008228D00022CDEE0001100A00022CDEE0001100A0000498AE0000238B00022CDEE0001100A0000498AE0000238B0000498AE0000238B000009C60000004890001EC5100000F00F00004123800001F8900004123800001F89000008B380000042300004123800001F89000008B3800000423000008B38000004230000012CC000000990001EC5100000F00F00004123800001F8900004123800001F89000008B380000042300004123800001F89000008B3800000423000008B38000004230000012CC0000009900004123800001F89000008B3800000423000008B38000004230000012CC00000099000008B38000004230000012CC000000990000012CC000000990000002D9000000144001EC5100000F00F00004123800001F8900004123800001F89000008B380000042300004123800001F89000008B3800000423000008B38000004230000012CC0000009900004123800001F89000008B3800000423000008B38000004230000012CC00000099000008B38000004230000012CC000000990000012CC000000990000002D90000001440004123800001F89000008B3800000423000008B38000004230000012CC00000099000008B38000004230000012CC000000990000012CC000000990000002D900000014400008B38000004230000012CC000000990000012CC000000990000002D9000000144000012CC000000990000002D9000000144000002D900000014400000051000000024001FBB7C000108690000421A40000228F0000421A40000228F000008A3C000004890000421A40000228F000008A3C00000489000008A3C00000489000001224000000990000421A40000228F000008A3C00000489000008A3C0000048900000122400000099000008A3C000004890000012240000009900000122400000099000000264000000144000421A40000228F000008A3C00000489000008A3C0000048900000122400000099000008A3C00000489000001224000000990000012240000009900000026400000014400008A3C00000489000001224000000990000012240000009900000026400000014400001224000000990000002640000001440000026400000014400000051000000024000421A40000228F000008A3C00000489000008A3C0000048900000122400000099000008A3C00000489000001224000000990000012240000009900000026400000014400008A3C0000048900000122400000099000001224000000990000002640000001440000122400000099000000264000000144000002640000001440000005100000002400008A3C0000048900000122400000099000001224000000990000002640000001440000122400000099000000264000000144000002640000001440000005100000002400001224000000990000002640000001440000026400000014400000051000000024000002640000001440000005100000002400000051000000024000000090000000062
  | 9 => 0x2086D4A7043872BAEA43904710FC06196ACB839848C784062FAC9A8063F40E4800A8545A039E4C624C063D07AA806516C45000AAE4E98065D4A86800AD618E800AF9C95000120393C37ED44E1C06062BEA8061C1322000A52C820062EA4E4000A86CC4800AB0118800118B12C063CEAF7800AA49F1800ADA8C100011E5E7C00AF91CA0001245CFC0012A6CEC00021465C37ED44E1C06062BEA8061C1322000A52C820062EA4E4000A86CC4800AB0118800118B12C063CEAF7800AA49F1800ADA8C100011E5E7C00AF91CA0001245CFC0012A6CEC00021465C0618F47E800A661EB000A9E814800117ECAC00ACC55D00011FAC0C00126513C00020DCCC00AF23CD8001241F4C0012CE03400021B37C00131C70C00022812C0002688D800003DA7C37ED44E1C06062BEA8061C1322000A52C820062EA4E4000A86CC4800AB0118800118B12C063CEAF7800AA49F1800ADA8C100011E5E7C00AF91CA0001245CFC0012A6CEC00021465C0618F47E800A661EB000A9E814800117ECAC00ACC55D00011FAC0C00126513C00020DCCC00AF23CD8001241F4C0012CE03400021B37C00131C70C00022812C0002688D800003DA7C0618F47E800A661EB000A9E814800117ECAC00ACC55D00011FAC0C00126513C00020DCCC00AF23CD8001241F4C0012CE03400021B37C00131C70C00022812C0002688D800003DA7C00AE59AD800122C58C0012BC6F40002194BC00132C4A400022A0C400026CA7800003E10C00139908C0002367FC00027F67800003FF0C0002CC4F0000047A18000047A1800000729C39E4C624C069C4F11C06477E05800B6807E806555A92000B9114A000AD68F0800139386006626002800BAFA81800AFBA0680013EC6A800B0E97A000143A7B000128544C00021465C063CEAF7800B6E2B8800ABCCF3000138201000ADF0A600013EC1F800123D2FC00020DCCC00B01613800143A0900012964BC00021B37C0012BF73C00022812C00022812C00003DA7C063CEAF7800B6E2B8800ABCCF3000138201000ADF0A600013EC1F800123D2FC00020DCCC00B01613800143A0900012964BC00021B37C0012BF73C00022812C00022812C00003DA7C00AF23CD800142393800127D76C0002194BC0012C80C400022A0C400022A0C400003E10C00132405C0002367FC0002367FC00003FF0C0002657DC000047A18000047A1800000729C063CEAF7800B6E2B8800ABCCF3000138201000ADF0A600013EC1F800123D2FC00020DCCC00B01613800143A0900012964BC00021B37C0012BF73C00022812C00022812C00003DA7C00AF23CD800142393800127D76C0002194BC0012C80C400022A0C400022A0C400003E10C00132405C0002367FC0002367FC00003FF0C0002657DC000047A18000047A1800000729C00AF23CD800142393800127D76C0002194BC0012C80C400022A0C400022A0C400003E10C00132405C0002367FC0002367FC00003FF0C0002657DC000047A18000047A1800000729C00139908C00024435C00024435C00004185C00027987C000049F98000049F9800000765C0002C9E440000537F00000537F00000085980000537F0000008598000008598000000D5C39848C7840647E6DA0069C4F11C00B6807E8064C426C800AE9117000B9114A000139386006555A92000B023E9000BAFA8180013EC6A800AFBF0D80012DF25400143A7B000021465C062EA4E4000AC0BC1800B6E2B8800138201000AC7AEB800128D3540013EC1F800020DCCC00ADF0A600012C773400143A09000021B37C001296F0C0001F952400022812C00003DA7C062EA4E4000AC0BC1800B6E2B8800138201000AC7AEB800128D3540013EC1F800020DCCC00ADF0A600012C773400143A09000021B37C001296F0C0001F952400022812C00003DA7C00ACC55D00012AA0F40014239380002194BC001291A1C0001F95FC00022A0C400003E10C0012C80C400020076C0002367FC00003FF0C0002367FC00003FF0C000047A1800000729C062EA4E4000AC0BC1800B6E2B8800138201000AC7AEB800128D3540013EC1F800020DCCC00ADF0A600012C773400143A09000021B37C001296F0C0001F952400022812C00003DA7C00ACC55D00012AA0F40014239380002194BC001291A1C0001F95FC00022A0C400003E10C0012C80C400020076C0002367FC00003FF0C0002367FC00003FF0C000047A1800000729C00ACC55D00012AA0F40014239380002194BC001291A1C0001F95FC00022A0C400003E10C0012C80C400020076C0002367FC00003FF0C0002367FC00003FF0C000047A1800000729C00132C4A400020B85400024435C00004185C00024435C00004185C000049F9800000765C00027987C0000477840000537F00000085980000537F0000008598000008598000000D5C065D4A86800BAFA81800BAFA81800156E86800AFBF0D800141FF9000141FF90000249BD000B0E97A00014584680014584680002554500012A407C0002226CC0002226CC00003DA7C00AF91CA000143A09000143A0900002538D8001296F0C000222AEC000222AEC00003E10C0012BF73C00022AB5C00022AB5C00003FF0C00022AB5C00003FF0C00003FF0C00000729C00AF91CA000143A09000143A0900002538D8001296F0C000222AEC000222AEC00003E10C0012BF73C00022AB5C00022AB5C00003FF0C00022AB5C00003FF0C00003FF0C00000729C00131C70C0002367FC0002367FC00004185C0002367FC00004185C00004185C00000765C0002657DC000047784000047784000008598000047784000008598000008598000000D5C00AF91CA000143A09000143A0900002538D8001296F0C000222AEC000222AEC00003E10C0012BF73C00022AB5C00022AB5C00003FF0C00022AB5C00003FF0C00003FF0C00000729C00131C70C0002367FC0002367FC00004185C0002367FC00004185C00004185C00000765C0002657DC000047784000047784000008598000047784000008598000008598000000D5C00131C70C0002367FC0002367FC00004185C0002367FC00004185C00004185C00000765C0002657DC000047784000047784000008598000047784000008598000008598000000D5C0002CC4F00000537F00000537F0000009C400000537F0000009C40000009C40000000FA00000537F0000009C40000009C40000000FA0000009C40000000FA0000000FA00000001903904710FC0630E3CB8064AD39D800ACE3270069C4F11C00B6807E800B9114A000139386006477E05800AD2AEF800B0BDC280012B615400BAFA8180013EC6A800143A7B000021465C061C1322000A8888A800AC8BA78001248C9C00B6E2B880013820100013EC1F800020DCCC00ABCCF300012495FC0012E607C0001F340400143A09000021B37C00022812C00003DA7C061C1322000A8888A800AC8BA78001248C9C00B6E2B880013820100013EC1F800020DCCC00ABCCF300012495FC0012E607C0001F340400143A09000021B37C00022812C00003DA7C00A9E81480012165FC0012C123C0001EF9CC0014239380002194BC00022A0C400003E10C00127D76C0001EA6740002074D400003A1C40002367FC00003FF0C000047A1800000729C061C1322000A8888A800AC8BA78001248C9C00B6E2B880013820100013EC1F800020DCCC00ABCCF300012495FC0012E607C0001F340400143A09000021B37C00022812C00003DA7C00A9E81480012165FC0012C123C0001EF9CC0014239380002194BC00022A0C400003E10C00127D76C0001EA6740002074D400003A1C40002367FC00003FF0C000047A1800000729C00A9E81480012165FC0012C123C0001EF9CC0014239380002194BC00022A0C400003E10C00127D76C0001EA6740002074D400003A1C40002367FC00003FF0C000047A1800000729C0012BC6F40001F109400020FBD400003B0C400024435C00004185C000049F9800000765C00024435C00004185C000049F9800000765C0000537F0000008598000008598000000D5C06516C45000B9114A000B0BDC2800142153800BAFA81800156E86800141FF90000249BD000AFBA06800141FF90001312B3C00022A6340014584680002554500002226CC00003DA7C00ADA8C100013EC1F80012E607C000226F4400143A0900002538D8000222AEC00003E10C0012964BC000222AEC000200C9400003A1C400022AB5C00003FF0C00003FF0C00000729C00ADA8C100013EC1F80012E607C000226F4400143A0900002538D8000222AEC00003E10C0012964BC000222AEC000200C9400003A1C400022AB5C00003FF0C00003FF0C00000729C0012CE03400022A0C40002074D400003B0C40002367FC00004185C00004185C00000765C0002367FC00004185C00004185C00000765C000047784000008598000008598000000D5C00ADA8C100013EC1F80012E607C000226F4400143A0900002538D8000222AEC00003E10C0012964BC000222AEC000200C9400003A1C400022AB5C00003FF0C00003FF0C00000729C0012CE03400022A0C40002074D400003B0C40002367FC00004185C00004185C00000765C0002367FC00004185C00004185C00000765C000047784000008598000008598000000D5C0012CE03400022A0C40002074D400003B0C40002367FC00004185C00004185C00000765C0002367FC00004185C00004185C00000765C000047784000008598000008598000000D5C00027F678000049F98000049F980000085980000537F0000009C40000009C40000000FA00000537F0000009C40000009C40000000FA0000009C40000000FA0000000FA0000000190063F40E4800AF3A6A000B9114A000142153800B9114A000142153800156E868000249BD000AD68F080012E184C00141FF9000022A63400141FF9000022A63400025545000003DA7C00AB011880012A76F40013EC1F8000226F440013EC1F8000226F440002538D800003E10C00123D2FC0001F8E94000222AEC00003A1C4000222AEC00003A1C400003FF0C00000729C00AB011880012A76F40013EC1F8000226F440013EC1F8000226F440002538D800003E10C00123D2FC0001F8E94000222AEC00003A1C4000222AEC00003A1C400003FF0C00000729C00126513C0001FDD3C00022A0C400003B0C400022A0C400003B0C400004185C00000765C00022A0C400003B0C400004185C00000765C00004185C00000765C000008598000000D5C00AB011880012A76F40013EC1F8000226F440013EC1F8000226F440002538D800003E10C00123D2FC0001F8E94000222AEC00003A1C4000222AEC00003A1C400003FF0C00000729C00126513C0001FDD3C00022A0C400003B0C400022A0C400003B0C400004185C00000765C00022A0C400003B0C400004185C00000765C00004185C00000765C000008598000000D5C00126513C0001FDD3C00022A0C400003B0C400022A0C400003B0C400004185C00000765C00022A0C400003B0C400004185C00000765C00004185C00000765C000008598000000D5C00026CA78000042108000049F98000008598000049F98000008598000009C40000000FA0000049F98000008598000009C40000000FA0000009C40000000FA0000000FA000000019000AF9C95000143A7B000143A7B000025545000143A7B0000255450000255450000044D1800128544C0002226CC0002226CC00003EE2C0002226CC00003EE2C00003EE2C00000729C0012A6CEC00022812C00022812C00003FF0C00022812C00003FF0C00003FF0C00000765C00022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C0012A6CEC00022812C00022812C00003FF0C00022812C00003FF0C00003FF0C00000765C00022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C0002688D8000047A18000047A18000008598000047A18000008598000008598000000FA0000047A18000008598000008598000000FA0000008598000000FA0000000FA00000001900012A6CEC00022812C00022812C00003FF0C00022812C00003FF0C00003FF0C00000765C00022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C0002688D8000047A18000047A18000008598000047A18000008598000008598000000FA0000047A18000008598000008598000000FA0000008598000000FA0000000FA00000001900002688D8000047A18000047A18000008598000047A18000008598000008598000000FA0000047A18000008598000008598000000FA0000008598000000FA0000000FA0000000190000047A18000008598000008598000000FA0000008598000000FA0000000FA0000000190000008598000000FA0000000FA0000000190000000FA00000001900000001900000000283872BAEA4061DCF5380630E3CB800A95C9300647E6DA000ACD8E7800AF3A6A000127275C069C4F11C00B6807E800B9114A000139386000BAFA8180013EC6A800143A7B000021465C06062BEA800A5C24D800A8888A80011C018400AC0BC180012471CC0012A76F40001E92F400B6E2B880013820100013EC1F800020DCCC00143A09000021B37C00022812C00003DA7C06062BEA800A5C24D800A8888A80011C018400AC0BC180012471CC0012A76F40001E92F400B6E2B880013820100013EC1F800020DCCC00143A09000021B37C00022812C00003DA7C00A661EB00011AA8FC0012165FC0001DA03C0012AA0F40001EF4A40001FDD3C000038E140014239380002194BC00022A0C400003E10C0002367FC00003FF0C000047A1800000729C06062BEA800A5C24D800A8888A80011C018400AC0BC180012471CC0012A76F40001E92F400B6E2B880013820100013EC1F800020DCCC00143A09000021B37C00022812C00003DA7C00A661EB00011AA8FC0012165FC0001DA03C0012AA0F40001EF4A40001FDD3C000038E140014239380002194BC00022A0C400003E10C0002367FC00003FF0C000047A1800000729C00A661EB00011AA8FC0012165FC0001DA03C0012AA0F40001EF4A40001FDD3C000038E140014239380002194BC00022A0C400003E10C0002367FC00003FF0C000047A1800000729C00122C58C0001E16D40001F109400003797400020B85400003B0C40000421080000069B400024435C00004185C000049F9800000765C0000537F0000008598000008598000000D5C063D07AA800B6807E800AD2AEF80013AD8B800B023E900014215380012E184C00022287C00BAFA81800156E86800141FF90000249BD00014584680002554500002226CC00003DA7C00AA49F180013820100012495FC00021390C0012C7734000226F440001F8E94000038E1400143A0900002538D8000222AEC00003E10C00022AB5C00003FF0C00003FF0C00000729C00AA49F180013820100012495FC00021390C0012C7734000226F440001F8E94000038E1400143A0900002538D8000222AEC00003E10C00022AB5C00003FF0C00003FF0C00000729C001241F4C0002194BC0001EA67400003797400020076C00003B0C400003B0C40000069B40002367FC00004185C00004185C00000765C000047784000008598000008598000000D5C00AA49F180013820100012495FC00021390C0012C7734000226F440001F8E94000038E1400143A0900002538D8000222AEC00003E10C00022AB5C00003FF0C00003FF0C00000729C001241F4C0002194BC0001EA67400003797400020076C00003B0C400003B0C40000069B40002367FC00004185C00004185C00000765C000047784000008598000008598000000D5C001241F4C0002194BC0001EA67400003797400020076C00003B0C400003B0C40000069B40002367FC00004185C00004185C00000765C000047784000008598000008598000000D5C0002367FC00004185C00004185C00000765C000047784000008598000008598000000D5C0000537F0000009C40000009C40000000FA0000009C40000000FA0000000FA0000000190062FAC9A800ACD8E7800B6807E80013AD8B800AE911700012EA0CC00142153800022287C00B9114A000142153800156E868000249BD000141FF9000022A63400025545000003DA7C00A86CC480012471CC00138201000021390C00128D3540001FEAA4000226F44000038E140013EC1F8000226F440002538D800003E10C000222AEC00003A1C400003FF0C00000729C00A86CC480012471CC00138201000021390C00128D3540001FEAA4000226F44000038E140013EC1F8000226F440002538D800003E10C000222AEC00003A1C400003FF0C00000729C0011FAC0C0001EF4A40002194BC0000379740001F95FC0000359D000003B0C40000069B400022A0C400003B0C400004185C00000765C00004185C00000765C000008598000000D5C00A86CC480012471CC00138201000021390C00128D3540001FEAA4000226F44000038E140013EC1F8000226F440002538D800003E10C000222AEC00003A1C400003FF0C00000729C0011FAC0C0001EF4A40002194BC0000379740001F95FC0000359D000003B0C40000069B400022A0C400003B0C400004185C00000765C00004185C00000765C000008598000000D5C0011FAC0C0001EF4A40002194BC0000379740001F95FC0000359D000003B0C40000069B400022A0C400003B0C400004185C00000765C00004185C00000765C000008598000000D5C00022A0C400003B0C400004185C00000765C00004185C00000765C000008598000000D5C000049F98000008598000009C40000000FA0000009C40000000FA0000000FA000000019000AD618E80013EC6A80013EC6A8000249BD00012DF25400022A63400022A63400003F3CC00143A7B0000255450000255450000044D180002226CC00003EE2C00003EE2C00000729C001245CFC00021B37C00021B37C00003E10C0001F952400003A1C400003A1C40000069B400022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C001245CFC00021B37C00021B37C00003E10C0001F952400003A1C400003A1C40000069B400022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C00022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C000047A18000008598000008598000000FA0000008598000000FA0000000FA0000000190001245CFC00021B37C00021B37C00003E10C0001F952400003A1C400003A1C40000069B400022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C00022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C000047A18000008598000008598000000FA0000008598000000FA0000000FA000000019000022812C00003FF0C00003FF0C00000765C00003FF0C00000765C00000765C000000D5C000047A18000008598000008598000000FA0000008598000000FA0000000FA0000000190000047A18000008598000008598000000FA0000008598000000FA0000000FA0000000190000008598000000FA0000000FA0000000190000000FA000000019000000019000000002806196ACB800A95C93000ACE327000128D36C00B6807E80013AD8B800142153800022287C00B6807E80013AD8B800142153800022287C00156E868000249BD000025545000003DA7C00A52C8200011C0184001248C9C0001EEF3400138201000021390C000226F44000038E1400138201000021390C000226F44000038E140002538D800003E10C00003FF0C00000729C00A52C8200011C0184001248C9C0001EEF3400138201000021390C000226F44000038E1400138201000021390C000226F44000038E140002538D800003E10C00003FF0C00000729C00117ECAC0001DA03C0001EF9CC000032CD00002194BC00003797400003B0C40000069B40002194BC00003797400003B0C40000069B400004185C00000765C000008598000000D5C00A52C8200011C0184001248C9C0001EEF3400138201000021390C000226F44000038E1400138201000021390C000226F44000038E140002538D800003E10C00003FF0C00000729C00117ECAC0001DA03C0001EF9CC000032CD00002194BC00003797400003B0C40000069B40002194BC00003797400003B0C40000069B400004185C00000765C000008598000000D5C00117ECAC0001DA03C0001EF9CC000032CD00002194BC00003797400003B0C40000069B40002194BC00003797400003B0C40000069B400004185C00000765C000008598000000D5C0002194BC00003797400003B0C40000069B400004185C00000765C000008598000000D5C00004185C00000765C000008598000000D5C000009C40000000FA0000000FA000000019000AAE4E980013938600012B615400022287C0013EC6A8000249BD000022A63400003F3CC0013EC6A8000249BD000022A63400003F3CC000255450000044D1800003EE2C00000729C0011E5E7C00020DCCC0001F3404000038E1400021B37C00003E10C00003A1C40000069B400021B37C00003E10C00003A1C40000069B400003FF0C00000765C00000765C000000D5C0011E5E7C00020DCCC0001F3404000038E1400021B37C00003E10C00003A1C40000069B400021B37C00003E10C00003A1C40000069B400003FF0C00000765C00000765C000000D5C00021B37C00003E10C00003A1C40000069B400003FF0C00000765C00000765C000000D5C00003FF0C00000765C00000765C000000D5C000008598000000FA0000000FA00000001900011E5E7C00020DCCC0001F3404000038E1400021B37C00003E10C00003A1C40000069B400021B37C00003E10C00003A1C40000069B400003FF0C00000765C00000765C000000D5C00021B37C00003E10C00003A1C40000069B400003FF0C00000765C00000765C000000D5C00003FF0C00000765C00000765C000000D5C000008598000000FA0000000FA000000019000021B37C00003E10C00003A1C40000069B400003FF0C00000765C00000765C000000D5C00003FF0C00000765C00000765C000000D5C000008598000000FA0000000FA000000019000003FF0C00000765C00000765C000000D5C000008598000000FA0000000FA0000000190000008598000000FA0000000FA0000000190000000FA000000019000000019000000002800A8545A000127275C00139386000022287C00139386000022287C000249BD000003F3CC00139386000022287C000249BD000003F3CC000249BD000003F3CC000044D1800000729C00118B12C0001E92F400020DCCC000038E1400020DCCC000038E1400003E10C0000069B400020DCCC000038E1400003E10C0000069B400003E10C0000069B400000765C000000D5C00118B12C0001E92F400020DCCC000038E1400020DCCC000038E1400003E10C0000069B400020DCCC000038E1400003E10C0000069B400003E10C0000069B400000765C000000D5C00020DCCC000038E1400003E10C0000069B400003E10C0000069B400000765C000000D5C00003E10C0000069B400000765C000000D5C00000765C000000D5C000000FA000000019000118B12C0001E92F400020DCCC000038E1400020DCCC000038E1400003E10C0000069B400020DCCC000038E1400003E10C0000069B400003E10C0000069B400000765C000000D5C00020DCCC000038E1400003E10C0000069B400003E10C0000069B400000765C000000D5C00003E10C0000069B400000765C000000D5C00000765C000000D5C000000FA000000019000020DCCC000038E1400003E10C0000069B400003E10C0000069B400000765C000000D5C00003E10C0000069B400000765C000000D5C00000765C000000D5C000000FA000000019000003E10C0000069B400000765C000000D5C00000765C000000D5C000000FA000000019000000765C000000D5C000000FA0000000190000000FA000000019000000019000000002800120393C00021465C00021465C00003DA7C00021465C00003DA7C00003DA7C00000729C00021465C00003DA7C00003DA7C00000729C00003DA7C00000729C00000729C000000D5C00021465C00003DA7C00003DA7C00000729C00003DA7C00000729C00000729C000000D5C00003DA7C00000729C00000729C000000D5C00000729C000000D5C000000D5C00000019000021465C00003DA7C00003DA7C00000729C00003DA7C00000729C00000729C000000D5C00003DA7C00000729C00000729C000000D5C00000729C000000D5C000000D5C00000019000003DA7C00000729C00000729C000000D5C00000729C000000D5C000000D5C00000019000000729C000000D5C000000D5C000000190000000D5C00000019000000019000000002800021465C00003DA7C00003DA7C00000729C00003DA7C00000729C00000729C000000D5C00003DA7C00000729C00000729C000000D5C00000729C000000D5C000000D5C00000019000003DA7C00000729C00000729C000000D5C00000729C000000D5C000000D5C00000019000000729C000000D5C000000D5C000000190000000D5C00000019000000019000000002800003DA7C00000729C00000729C000000D5C00000729C000000D5C000000D5C00000019000000729C000000D5C000000D5C000000190000000D5C00000019000000019000000002800000729C000000D5C000000D5C000000190000000D5C000000190000000190000000028000000D5C0000001900000001900000000280000001900000000280000000280000000064
  | 10 => 0x32ECB0734427E77274D1422E2A6E80F939BC205130D158603F1EC2E601FD7A34D801844783451ACB012C03F9B87AD0202C862000189B340C0818BCF700063BA8D3003271BA38002590E3C4F2A7528A03DA35D3201F3800ED8017DE6EA407E39B3EA00613059300314574D80024B4B7C07F42C88C00622B49E0031F81CC8002561C6400C9DC152000985D190004DA31680003E4EDC4F2A7528A03DA35D3201F3800ED8017DE6EA407E39B3EA00613059300314574D80024B4B7C07F42C88C00622B49E0031F81CC8002561C6400C9DC152000985D190004DA31680003E4EDC07CAA3AFA006022C800030FF1E300024A140C00C6FE5500009633510004CB48C00003DA3AC00C9793E6000984F900004E420780003F11C40013DBB96000101D2100008E76280000679BC4F2A7528A03DA35D3201F3800ED8017DE6EA407E39B3EA00613059300314574D80024B4B7C07F42C88C00622B49E0031F81CC8002561C6400C9DC152000985D190004DA31680003E4EDC07CAA3AFA006022C800030FF1E300024A140C00C6FE5500009633510004CB48C00003DA3AC00C9793E6000984F900004E420780003F11C40013DBB96000101D2100008E76280000679BC07CAA3AFA006022C800030FF1E300024A140C00C6FE5500009633510004CB48C00003DA3AC00C9793E6000984F900004E420780003F11C40013DBB96000101D2100008E76280000679BC00C8A435C00097A9EB0004E003900003EDDB00013EBA90000102B2E00008F590800006840C001453F620001080E700009355F800006B27400028D26E00001DB0500000ED82800000ACBC51ACB012C043098A95020015C69001A1F943C0810519680069D67290031E8AF1800288405C081F5705C006AD593C003284283000292C3EC00CB45E80000A6FB3F0004D241D80003E4EDC07F42C88C0068B73E900317FC9580028665FC00C83AA6E000A4BC110004C1D0480003DA3AC00CA78134000A706130004D6E5D80003F11C40013832A6000101D21000080E9080000679BC07F42C88C0068B73E900317FC9580028665FC00C83AA6E000A4BC110004C1D0480003DA3AC00CA78134000A706130004D6E5D80003F11C40013832A6000101D21000080E9080000679BC00C9793E6000A65B460004D10E880003EDDB000138C306000102B2E000081597000006840C0013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC07F42C88C0068B73E900317FC9580028665FC00C83AA6E000A4BC110004C1D0480003DA3AC00CA78134000A706130004D6E5D80003F11C40013832A6000101D21000080E9080000679BC00C9793E6000A65B460004D10E880003EDDB000138C306000102B2E000081597000006840C0013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC00C9793E6000A65B460004D10E880003EDDB000138C306000102B2E000081597000006840C0013E49E60001080E7000084073800006B27400023790400001DB0500000ED82800000ACBC001453F6200010DE5C000086F2E000006D9200002487B800001E93300000F499800000B1E400028B6120000221EB0000110F5800000C6840000443D60000031A10000018D0800000120C5130D158604006DE7E02184C54A801A1F943C0805EBC5400646EA020034EB394800288405C0810519680065410A700356AC9E000292C3EC00CA14D560009CE541000537D9F80003E4EDC07E39B3EA00632021400345B9F480028665FC00C6B75A60009A8723000525E0880003DA3AC00C83AA6E0009C3ED600053830980003F11C400135C1320000EE26D000080E9080000679BC07E39B3EA00632021400345B9F480028665FC00C6B75A60009A8723000525E0880003DA3AC00C83AA6E0009C3ED600053830980003F11C400135C1320000EE26D000080E9080000679BC00C6FE5500009B5EAB000532DA300003EDDB0001357B120000EE375000081597000006840C00138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC07E39B3EA00632021400345B9F480028665FC00C6B75A60009A8723000525E0880003DA3AC00C83AA6E0009C3ED600053830980003F11C400135C1320000EE26D000080E9080000679BC00C6FE5500009B5EAB000532DA300003EDDB0001357B120000EE375000081597000006840C00138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC00C6FE5500009B5EAB000532DA300003EDDB0001357B120000EE375000081597000006840C00138C3060000F1516000084073800006B2740002101CE00001AC9D00000ED82800000ACBC0013EBA900000F6103000086F2E000006D92000021BCB800001B64800000F499800000B1E40002487B800001DA290000110F5800000C6840000443D60000031A10000018D0800000120C0818BCF70006AD593C00356AC9E0002BFCA8C00CA14D56000A64709000532384800043EE7C00CB45E80000A7EB6600053F5B300004526F4001367C5E0000FF6B700007FB5B80000679BC00C9DC152000A70613000538309800044F80800135C1320000FF90900007FC84800006840C0013832A600010307700008183B800006B2740002060EE00001AC9D00000D64E800000ACBC00C9DC152000A70613000538309800044F80800135C1320000FF90900007FC84800006840C0013832A600010307700008183B800006B2740002060EE00001AC9D00000D64E800000ACBC0013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C00C9DC152000A70613000538309800044F80800135C1320000FF90900007FC84800006840C0013832A600010307700008183B800006B2740002060EE00001AC9D00000D64E800000ACBC0013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C0013DBB960001080E7000084073800006D9200002101CE00001B64800000DB24000000B1E400023790400001DA2900000ED14800000C68400003B4520000031A10000018D0800000120C00028D26E0000221EB0000110F5800000E4C40000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E4508B8A9BA03F3002F802011255D0018E2DF8808613152A00687E50F0034EB394800288405C0800571A40063B2F230032C936E80026EBC6C00D5AB278000A4B0FB000537D9F80003E4EDC07CE003B6006147DB90031B1D17800261F65400D16E7D2000A1997F000525E0880003DA3AC00C5FF2560009887A30004E93C180003ADE840014E0C260000FC471000080E9080000679BC07CE003B6006147DB90031B1D17800261F65400D16E7D2000A1997F000525E0880003DA3AC00C5FF2560009887A30004E93C180003ADE840014E0C260000FC471000080E9080000679BC00C3FC78C0009701D30004E071E80003A7B840014CB68C0000FB76C000081597000006840C0013443A20000E7E4400007A20100000625840002101CE00001AC9D00000ED82800000ACBC07CE003B6006147DB90031B1D17800261F65400D16E7D2000A1997F000525E0880003DA3AC00C5FF2560009887A30004E93C180003ADE840014E0C260000FC471000080E9080000679BC00C3FC78C0009701D30004E071E80003A7B840014CB68C0000FB76C000081597000006840C0013443A20000E7E4400007A20100000625840002101CE00001AC9D00000ED82800000ACBC00C3FC78C0009701D30004E071E80003A7B840014CB68C0000FB76C000081597000006840C0013443A20000E7E4400007A20100000625840002101CE00001AC9D00000ED82800000ACBC0013800E40000EABE600007BF020000063CB800021BCB800001B64800000F499800000B1E400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C080B218800069D67290032C936E800299414400D5AB278000AFF2A3000532384800043EE7C00CA10A0C000A647090004F3DA7800040AD3C0014FD6CC0001149BD00007FB5B80000679BC00C7E0732000A4BC110004E93C18000404F640014E0C26000113E0200007FC84800006840C00135B9760000FF909000078B8280000625840002060EE00001AC9D00000D64E800000ACBC00C7E0732000A4BC110004E93C18000404F640014E0C26000113E0200007FC84800006840C00135B9760000FF909000078B8280000625840002060EE00001AC9D00000D64E800000ACBC00139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00C7E0732000A4BC110004E93C18000404F640014E0C26000113E0200007FC84800006840C00135B9760000FF909000078B8280000625840002060EE00001AC9D00000D64E800000ACBC00139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00139081E000102B2E00007A2010000063CB80002101CE00001B64800000DB24000000B1E40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00024D57E00001E93300000F499800000C6840000443D6000003931000001C9880000014CC0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E407F5E8D360064C639B0034EB394800299414400D3ACE52000A6505100057F951800043EE7C00C7A2BC60009D0749000532384800040AD3C0014C8E12000102B4F00008A4DE80000679BC00C515D360009B4BD9000525E088000404F640014978220001013D9000089F01000006840C0013074120000EDFD900007FC8480000625840001FF21200001896100000D64E800000ACBC00C515D360009B4BD9000525E088000404F640014978220001013D9000089F01000006840C0013074120000EDFD900007FC8480000625840001FF21200001896100000D64E800000ACBC00132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00C515D360009B4BD9000525E088000404F640014978220001013D9000089F01000006840C0013074120000EDFD900007FC8480000625840001FF21200001896100000D64E800000ACBC00132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00132D2300000F01C00000815970000063CB800020565C000018F2E00000DB24000000B1E400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00023D64200001B9EF00000F499800000C68400003D2660000031A1000001C9880000014CC00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E400C9C6E8E000A6FB3F000537D9F80004526F40014DF67E0001149BD00008A4DE80000726780013490760000FF6B700007FB5B80000698AC0001FED6E00001A62B00000D315800000ACBC001368C5A000101D21000080E90800006B274000203A4200001AC9D00000D64E800000B1E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C001368C5A000101D21000080E90800006B274000203A4200001AC9D00000D64E800000B1E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4001368C5A000101D21000080E90800006B274000203A4200001AC9D00000D64E800000B1E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000239D8A00001DB0500000ED82800000C68400003B60A0000031A10000018D080000014CC00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C4FCEE4E9A03E7D7E1801F98017C00186C1A280800DBCFC006386BB30032631CD800266AE7008613152A00687E50F0034EB394800288405C00D5AB278000A4B0FB000537D9F80003E4EDC07B46BA64005FD19200030A3EDC800251C7CC00C64042800098725E0004DA5EC800039CA2400D16E7D2000A1997F000525E0880003DA3AC0014E0C260000FC471000080E9080000679BC07B46BA64005FD19200030A3EDC800251C7CC00C64042800098725E0004DA5EC800039CA2400D16E7D2000A1997F000525E0880003DA3AC0014E0C260000FC471000080E9080000679BC00C04590000093CDB90004B80E98000382EAC00136BD560000E9CF20000780E000000606940014CB68C0000FB76C000081597000006840C0002101CE00001AC9D00000ED82800000ACBC07B46BA64005FD19200030A3EDC800251C7CC00C64042800098725E0004DA5EC800039CA2400D16E7D2000A1997F000525E0880003DA3AC0014E0C260000FC471000080E9080000679BC00C04590000093CDB90004B80E98000382EAC00136BD560000E9CF20000780E000000606940014CB68C0000FB76C000081597000006840C0002101CE00001AC9D00000ED82800000ACBC00C04590000093CDB90004B80E98000382EAC00136BD560000E9CF20000780E000000606940014CB68C0000FB76C000081597000006840C0002101CE00001AC9D00000ED82800000ACBC0012F53D60000E3F3B0000755F3000005E7A40001EC206000018F2E00000DCF7800000A0B400021BCB800001B64800000F499800000B1E40000443D60000031A10000018D0800000120C07F370F5A00687E50F0031D979180028B95B800CA8214E000A650510004E83A480003FD63800D5AB278000AFF2A3000532384800043EE7C0014FD6CC0001149BD00007FB5B80000679BC00C45693C000A1997F0004C43D180003E3FE8001387DAC0001013D9000076FEC80000606940014E0C26000113E0200007FC84800006840C0002060EE00001AC9D00000D64E800000ACBC00C45693C000A1997F0004C43D180003E3FE8001387DAC0001013D9000076FEC80000606940014E0C26000113E0200007FC84800006840C0002060EE00001AC9D00000D64E800000ACBC001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C00C45693C000A1997F0004C43D180003E3FE8001387DAC0001013D9000076FEC80000606940014E0C26000113E0200007FC84800006840C0002060EE00001AC9D00000D64E800000ACBC001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C001309F200000FB76C000073F22000005E7A40001E2A2C000018F2E00000C797000000A0B40002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0002101CE00001B64800000DB24000000B1E400003B4520000031A10000018D0800000120C0000443D6000003931000001C9880000014CC00000726200000053300000029980000001E407E3D85CC006386BB300343F28780028B95B800C8DD4040009D47BD00053282880003FD63800D3ACE52000A6505100057F951800043EE7C0014C8E12000102B4F00008A4DE80000679BC00C260B2600098725E00050CCBF80003E3FE8001350E460000F051A0000809EC80000606940014978220001013D9000089F01000006840C0001FF21200001896100000D64E800000ACBC00C260B2600098725E00050CCBF80003E3FE8001350E460000F051A0000809EC80000606940014978220001013D9000089F01000006840C0001FF21200001896100000D64E800000ACBC0012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00C260B2600098725E00050CCBF80003E3FE8001350E460000F051A0000809EC80000606940014978220001013D9000089F01000006840C0001FF21200001896100000D64E800000ACBC0012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C0012C66A20000E9CF200007DBB6000005E7A40001DC6EA000016E1800000C797000000A0B400020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00020565C000018F2E00000DB24000000B1E4000036C90000002C790000018D0800000120C00003D2660000031A1000001C9880000014CC00000726200000053300000029980000001E400C7751A6000A4B0FB00052587D800043EE7C00139CA82000102B4F0000815A7800006A0680014DF67E0001149BD00008A4DE80000726780001FED6E00001A62B00000D315800000ACBC00130BA320000FC47100007E238800006840C0001DC4DA00001896100000C4B0800000A0B4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00130BA320000FC47100007E238800006840C0001DC4DA00001896100000C4B0800000A0B4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400130BA320000FC47100007E238800006840C0001DC4DA00001896100000C4B0800000A0B4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E4000203A4200001AC9D00000D64E800000B1E400003593A000002C7900000163C800000120C00003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400003B60A0000031A10000018D080000014CC00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C07C9CDE100061B068A0031C5BF100026A15D800D0FCA1E000A2E56E00053282880003FD63800D0FCA1E000A2E56E00053282880003FD6380015FE54600010FB9F00008A4DE80000679BC00BEF37520009471F30004C3ECA80003A66600014332FE0000F8FFA0000809EC80000606940014332FE0000F8FFA0000809EC8000060694000227C0400001A10300000D64E800000ACBC00BEF37520009471F30004C3ECA80003A66600014332FE0000F8FFA0000809EC80000606940014332FE0000F8FFA0000809EC8000060694000227C0400001A10300000D64E800000ACBC001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B40001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C00BEF37520009471F30004C3ECA80003A66600014332FE0000F8FFA0000809EC80000606940014332FE0000F8FFA0000809EC8000060694000227C0400001A10300000D64E800000ACBC001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B40001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C001250A060000E0BAB000074F7080000572C40001F6ED80000179E900000C797000000A0B40001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C0001F6ED80000179E900000C797000000A0B4000036C90000002C790000018D0800000120C000036C90000002C790000018D0800000120C00000726200000053300000029980000001E400C4D9A06000A210170004DD78D80003FD6380014961F600010FB9F0000815A7800006A0680014961F600010FB9F0000815A7800006A06800022937A00001C99E00000D315800000ACBC0012B0E320000F68EB000075BD080000606940001F88E200001A10300000C4B0800000A0B40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C0012B0E320000F68EB000075BD080000606940001F88E200001A10300000C4B0800000A0B40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C0001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C00003593A000002C7900000163C800000120C00000634200000053300000029980000001E40012B0E320000F68EB000075BD080000606940001F88E200001A10300000C4B0800000A0B40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C0001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C00003593A000002C7900000163C800000120C00000634200000053300000029980000001E40001F88E200001A10300000C4B0800000A0B400003593A000002C7900000163C800000120C00003593A000002C7900000163C800000120C00000634200000053300000029980000001E400003593A000002C7900000163C800000120C00000634200000053300000029980000001E400000634200000053300000029980000001E4000000A6600000007900000003C800000002C00C223C1A00099AB9C00051080B80003FD63800144202E0000FF58E000087DCF800006A06800144202E0000FF58E000087DCF800006A06800021F73E00001A81A00000E4CF000000ACBC00125A5BE0000E728900007B47580000606940001ED1D60000181A500000D081800000A0B40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00125A5BE0000E728900007B47580000606940001ED1D60000181A500000D081800000A0B40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C0001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00003420600000282D00000163C800000120C0000058F200000048300000029980000001E400125A5BE0000E728900007B47580000606940001ED1D60000181A500000D081800000A0B40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C0001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00003420600000282D00000163C800000120C0000058F200000048300000029980000001E40001ED1D60000181A500000D081800000A0B400003420600000282D00000163C800000120C00003420600000282D00000163C800000120C0000058F200000048300000029980000001E400003420600000282D00000163C800000120C0000058F200000048300000029980000001E40000058F200000048300000029980000001E4000000A6600000007900000003C800000002C0012C871E0000F93B700007C9DB80000679BC0001F276E000019E6F00000CF37800000ACBC0001F276E000019E6F00000CF37800000ACBC000033CDE000002B2F000001597800000120C0001F276E000019E6F00000CF37800000ACBC000033CDE000002B2F000001597800000120C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E40001F276E000019E6F00000CF37800000ACBC000033CDE000002B2F000001597800000120C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E4000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E400000565E00000048300000024180000001E400000090600000007900000003C800000002C0001F276E000019E6F00000CF37800000ACBC000033CDE000002B2F000001597800000120C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E4000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E400000565E00000048300000024180000001E400000090600000007900000003C800000002C000033CDE000002B2F000001597800000120C00000565E00000048300000024180000001E400000565E00000048300000024180000001E400000090600000007900000003C800000002C00000565E00000048300000024180000001E400000090600000007900000003C800000002C00000090600000007900000003C800000002C0000000F200000000B00000000580000000065
  | 11 => 0x23D8197A930666745B550CE8CF18A8024709D6A83404B98CB809383F2F201297337FC0033C1B72C344DA9EB6009490CADA012C4EC99A00346C501804B873D09000D43D94E001ACFC2E60004918DE832D66E2F60090614FC2012434862E0033007B24049C6C3FE800CF5ED10001A409A6C000479C51004A54D595000D14A928001A98168200048D2198006B56559800128551200025B275800006DFC3832D66E2F60090614FC2012434862E0033007B24049C6C3FE800CF5ED10001A409A6C000479C51004A54D595000D14A928001A98168200048D2198006B56559800128551200025B275800006DFC38048F225C8000CD5771F001A1F9284000477F3A00069F6C70800124902A000254BFD400006CF280006B2C88500012853B200025FCFBA00006F43780009A116700001C61D800003E307000000A5D6832D66E2F60090614FC2012434862E0033007B24049C6C3FE800CF5ED10001A409A6C000479C51004A54D595000D14A928001A98168200048D2198006B56559800128551200025B275800006DFC38048F225C8000CD5771F001A1F9284000477F3A00069F6C70800124902A000254BFD400006CF280006B2C88500012853B200025FCFBA00006F43780009A116700001C61D800003E307000000A5D68048F225C8000CD5771F001A1F9284000477F3A00069F6C70800124902A000254BFD400006CF280006B2C88500012853B200025FCFBA00006F43780009A116700001C61D800003E307000000A5D68006AC3F0400012729D600025DFF2600006EEF980009A883080001C795900003E8D4000000A6CE00009D76D500001D053600004029C000000AB1A0000119EB0000002EFC8000005DF90000000FA98344DA9EB6009BDF6CD8012AF1C0B0003761CD6004B44AF58800E0277AB001A911D280004E56F1C04BC4D686000E217F84001ADD13700004F826D0006C07DF880014216C10002579FA000006DFC3804A54D595000DDFF1A4001A5F175A0004E273FC006A9270980013E30A2000250860C00006CF280006BA97780001423E49000259E88400006F43780009797B300001C61D8000038C3B000000A5D6804A54D595000DDFF1A4001A5F175A0004E273FC006A9270980013E30A2000250860C00006CF280006BA97780001423E49000259E88400006F43780009797B300001C61D8000038C3B000000A5D68006B2C8850001410CE800025751C400006EEF9800097DCF180001C7959000038F2B200000A6CE00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA9804A54D595000DDFF1A4001A5F175A0004E273FC006A9270980013E30A2000250860C00006CF280006BA97780001423E49000259E88400006F43780009797B300001C61D8000038C3B000000A5D68006B2C8850001410CE800025751C400006EEF9800097DCF180001C7959000038F2B200000A6CE00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA98006B2C8850001410CE800025751C400006EEF9800097DCF180001C7959000038F2B200000A6CE00009A5A9F00001D053600003A0A6C00000AB1A00000F7EFB800002EFC8000005DF90000000FA980009D76D500001D9C7600003B38EC00000AEA580000FEBB1800003046800000608D000000101780001194A200000355E0000006ABC00000011CA000001AAF000000047280000008E5000000017B83404B98CB809582317F0137BED9B0003761CD6004AEC9E2E000D5BF4B1001C04EF560004E56F1C04B44AF58800D7595AD001C42FF080004F826D0006B75FAC00013065C30002842D8200006DFC38049C6C3FE800D337B2A001BBFE3480004E273FC0069D712C00012C431900027C614400006CF280006A9270980012F50190002847C9200006F4378000967CEC00001A6990000038C3B000000A5D68049C6C3FE800D337B2A001BBFE3480004E273FC0069D712C00012C431900027C614400006CF280006A9270980012F50190002847C9200006F4378000967CEC00001A6990000038C3B000000A5D680069F6C7080012DBE6D00028219D000006EEF9800096614B00001A6C19000038F2B200000A6CE000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA98049C6C3FE800D337B2A001BBFE3480004E273FC0069D712C00012C431900027C614400006CF280006A9270980012F50190002847C9200006F4378000967CEC00001A6990000038C3B000000A5D680069F6C7080012DBE6D00028219D000006EEF9800096614B00001A6C19000038F2B200000A6CE000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA980069F6C7080012DBE6D00028219D000006EEF9800096614B00001A6C19000038F2B200000A6CE000097DCF180001ABE2B00003A0A6C00000AB1A00000E829B000002AC68000005DF90000000FA980009A883080001B39CA00003B38EC00000AEA580000ECE3B000002BA9600000608D000000101780000FEBB1800002EEAA000006ABC00000011CA000001AAF000000047280000008E5000000017B804B873D09000E217F84001C42FF080005476640006B75FAC000140F3AF000281E75E00007703C4006C07DF8800143D77A000287AEF4000078FB0400096CC7500001C23CC000038479800000A5D68006B565598001423E490002847C92000078AEE0000967CEC00001C2844000038508800000A6CE00009797B300001C82EE00003905DC00000AB1A00000E4177000002AC6800000558D0000000FA98006B565598001423E490002847C92000078AEE0000967CEC00001C2844000038508800000A6CE00009797B300001C82EE00003905DC00000AB1A00000E4177000002AC6800000558D0000000FA980009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8006B565598001423E490002847C92000078AEE0000967CEC00001C2844000038508800000A6CE00009797B300001C82EE00003905DC00000AB1A00000E4177000002AC6800000558D0000000FA980009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B80009A116700001D053600003A0A6C00000AEA580000E829B000002BA96000005752C00000101780000F7EFB800002EEAA000005DD540000011CA000001775500000047280000008E5000000017B8000119EB000000355E0000006ABC0000001440000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D80000000024033A33C62A0093B39FF6012B7AE3B4003500230404DEFB66C000DD87358001C04EF560004E56F1C04ABC702C000D450CE0001AFF33280004B8FA3C00710BFC200013E09B40002842D8200006DFC380490D218B800CF9B7D0001A778B780004A275B8006EFF8D20001389CFF00027C614400006CF28000697C5D6800128B78E000261E02800006889A0000A11F2480001BD0DE000038C3B000000A5D680490D218B800CF9B7D0001A778B780004A275B8006EFF8D20001389CFF00027C614400006CF28000697C5D6800128B78E000261E02800006889A0000A11F2480001BD0DE000038C3B000000A5D6800687E4A1000125FC0600025DF074000067E99C000A0867400001BBBE6000038F2B200000A6CE000095D471000019C976000036150C000009E4C00000E829B000002AC68000005DF90000000FA980490D218B800CF9B7D0001A778B780004A275B8006EFF8D20001389CFF00027C614400006CF28000697C5D6800128B78E000261E02800006889A0000A11F2480001BD0DE000038C3B000000A5D6800687E4A1000125FC0600025DF074000067E99C000A0867400001BBBE6000038F2B200000A6CE000095D471000019C976000036150C000009E4C00000E829B000002AC68000005DF90000000FA9800687E4A1000125FC0600025DF074000067E99C000A0867400001BBBE6000038F2B200000A6CE000095D471000019C976000036150C000009E4C00000E829B000002AC68000005DF90000000FA98000977FC980001A13E2000036D21C00000A07200000ECE3B000002BA9600000608D000000101780000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B804B13B266800E0277AB001AFF33280005040B1000710BFC2000151D990000281E75E00007703C4006B744DC000140F3AF0002669F7C000071DABC000A1EBBD00001E3EC1000038479800000A5D68006A605A080013E30A2000261E0280000714274000A11F2480001E2BB8000038508800000A6CE0000967A2100001C284400003581EC000009E4C00000E4177000002AC6800000558D0000000FA98006A605A080013E30A2000261E0280000714274000A11F2480001E2BB8000038508800000A6CE0000967A2100001C284400003581EC000009E4C00000E4177000002AC6800000558D0000000FA9800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B8006A605A080013E30A2000261E0280000714274000A11F2480001E2BB8000038508800000A6CE0000967A2100001C284400003581EC000009E4C00000E4177000002AC6800000558D0000000FA9800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B800097F3EE80001C7959000036150C00000A07200000E829B000002BA96000005752C00000101780000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B8000100A70000003046800000608D00000011CA000001AAF00000005100000000A2000000001B0000001AAF00000005100000000A2000000001B0000000288000000006C00000000D80000000024004A5CCDFF000D6689B3001C04EF560005040B10007013BD580014102C40002A3B32000007703C4006A4474A000130B9F0000281E75E000071DABC000A079D780001C76AF00003C7D8200000A5D6800690269B00012D9EB700027C614400007142740009F185100001C509D00003C577000000A6CE000094218300001A65B20000385088000009E4C00000E1422000002793000000558D0000000FA9800690269B00012D9EB700027C614400007142740009F185100001C509D00003C577000000A6CE000094218300001A65B20000385088000009E4C00000E1422000002793000000558D0000000FA98000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B800690269B00012D9EB700027C614400007142740009F185100001C509D00003C577000000A6CE000094218300001A65B20000385088000009E4C00000E1422000002793000000558D0000000FA98000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000952FF500001A9D15000038F2B200000A07200000E3CAC80000281C8000005752C00000101780000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000FA350000002C05800000608D00000011CA00000182340000004728000000A2000000001B000000182340000004728000000A2000000001B0000000288000000006C00000000D800000000240006B3F0B980014216C10002842D82000078FB04000A10B6080001E3EC100003C7D8200000B580000095E7E800001C23CC000038479800000A8BD00000E11E6000002A2F400000545E8000000FA9800096C9D600001C61D8000038C3B000000AB1A00000E30EC000002AC6800000558D000000101780000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B800096C9D600001C61D8000038C3B000000AB1A00000E30EC000002AC6800000558D000000101780000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000096C9D600001C61D8000038C3B000000AB1A00000E30EC000002AC6800000558D000000101780000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000F8C1C000002EFC8000005DF900000011CA00000177E400000047280000008E500000001B000000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000303333A2DAA8092328B2A0127673FEC0034174CC404AC118BF800D3F8340001ACD13660004AA8DD804DEFB66C000DD87358001C04EF560004E56F1C00710BFC200013E09B40002842D8200006DFC3804830A7E1000CCBCDA00019F36FA0000485A24400699BD950001288B8E00025B3D6E000066C7A8006EFF8D20001389CFF00027C614400006CF280000A11F2480001BD0DE000038C3B000000A5D6804830A7E1000CCBCDA00019F36FA0000485A24400699BD950001288B8E00025B3D6E000066C7A8006EFF8D20001389CFF00027C614400006CF280000A11F2480001BD0DE000038C3B000000A5D680066ABB8F800120424600024BF80C000064306400096DF36800019F79C0000353A2A000009B658000A0867400001BBBE6000038F2B200000A6CE00000E829B000002AC68000005DF90000000FA9804830A7E1000CCBCDA00019F36FA0000485A24400699BD950001288B8E00025B3D6E000066C7A8006EFF8D20001389CFF00027C614400006CF280000A11F2480001BD0DE000038C3B000000A5D680066ABB8F800120424600024BF80C000064306400096DF36800019F79C0000353A2A000009B658000A0867400001BBBE6000038F2B200000A6CE00000E829B000002AC68000005DF90000000FA980066ABB8F800120424600024BF80C000064306400096DF36800019F79C0000353A2A000009B658000A0867400001BBBE6000038F2B200000A6CE00000E829B000002AC68000005DF90000000FA980009394EB00001960F600003427C400000989A80000D9CE500000281C800000580B0000000EAC80000ECE3B000002BA9600000608D0000001017800001AAF000000047280000008E5000000017B804A48656D000DD87358001A8A19C00004EBBE90006BACAD680014102C400026173E00000707DA800710BFC2000151D990000281E75E00007703C4000A1EBBD00001E3EC1000038479800000A5D680068A54940001389CFF0002516F1C00006DEE2000097A80C80001C509D000034CB64000009B658000A11F2480001E2BB8000038508800000A6CE00000E4177000002AC6800000558D0000000FA980068A54940001389CFF0002516F1C00006DEE2000097A80C80001C509D000034CB64000009B658000A11F2480001E2BB8000038508800000A6CE00000E4177000002AC6800000558D0000000FA980009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B80068A54940001389CFF0002516F1C00006DEE2000097A80C80001C509D000034CB64000009B658000A11F2480001E2BB8000038508800000A6CE00000E4177000002AC6800000558D0000000FA980009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B80009429D900001BBBE600003392EC00000989A80000D5F1580000281C80000050390000000EAC80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B80000E829B000002BA96000005752C000001017800001775500000047280000008E5000000017B800001AAF00000005100000000A2000000001B0000000288000000006C00000000D800000000240049C1F979000D3F8340001BB0E6B00004EBBE90006ADFA588001312C6800028205880000707DA8007013BD580014102C40002A3B32000007703C4000A079D780001C76AF00003C7D8200000A5D680067AF6880001288B8E00027139FE00006DEE2000096218C80001A9F5C000038A13A000009B6580009F185100001C509D00003C577000000A6CE00000E1422000002793000000558D0000000FA980067AF6880001288B8E00027139FE00006DEE2000096218C80001A9F5C000038A13A000009B6580009F185100001C509D00003C577000000A6CE00000E1422000002793000000558D0000000FA98000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80067AF6880001288B8E00027139FE00006DEE2000096218C80001A9F5C000038A13A000009B6580009F185100001C509D00003C577000000A6CE00000E1422000002793000000558D0000000FA98000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B8000924815000019F79C00003777CC00000989A80000D360C80000251660000050390000000EAC80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000E3CAC80000281C8000005752C0000010178000015D4B000000405E0000008E5000000017B80000182340000004728000000A2000000001B0000000288000000006C00000000D800000000240006A1ECA700013E09B400027C136800007703C40009832E180001C76AF000038ED5E00000A9620000A10B6080001E3EC100003C7D8200000B58000000E11E6000002A2F400000545E8000000FA98000942A8900001BD0DE000037A1BC00000A6CE00000D34C80000027930000004F260000000EAC80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B8000942A8900001BD0DE000037A1BC00000A6CE00000D34C80000027930000004F260000000EAC80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000177E400000047280000008E500000001B0000000239400000006C00000000D800000000240000942A8900001BD0DE000037A1BC00000A6CE00000D34C80000027930000004F260000000EAC80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000E30EC000002AC6800000558D00000010178000015634000000405E00000080BC00000017B80000177E400000047280000008E500000001B0000000239400000006C00000000D8000000002400000177E400000047280000008E500000001B0000000239400000006C00000000D80000000024000000239400000006C00000000D800000000240000000360000000009000000001200000000030048E13AD5000D05D331001A8011820004B0F7F0006EC39AC00013AEFA400028205880000707DA8006EC39AC00013AEFA400028205880000707DA8000A8ECC800001DC0F100003C7D8200000A5D68006600F6480012168910002513ADC000067C3480009C4E7F80001B7B88000038A13A000009B6580009C4E7F80001B7B88000038A13A000009B6580000F15DC0000029B3800000558D0000000FA98006600F6480012168910002513ADC000067C3480009C4E7F80001B7B88000038A13A000009B6580009C4E7F80001B7B88000038A13A000009B6580000F15DC0000029B3800000558D0000000FA980008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B8006600F6480012168910002513ADC000067C3480009C4E7F80001B7B88000038A13A000009B6580009C4E7F80001B7B88000038A13A000009B6580000F15DC0000029B3800000558D0000000FA980008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B80008EFE740000190C19000033F4CE000008DE780000DDDF3000002626A0000050390000000EAC80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B80000DDDF3000002626A0000050390000000EAC8000015D4B000000405E0000008E5000000017B8000015D4B000000405E0000008E5000000017B800000288000000006C00000000D8000000002400068D8A030001395BC700025C7D1E0000707DA80009F04DA00001DC0F1000038ED5E00000A96200009F04DA00001DC0F1000038ED5E00000A96200000F1F60800002D60000000545E8000000FA9800091A43300001B3CA000003444D0000009B6580000DE86F0000029B38000004F260000000EAC80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B800091A43300001B3CA000003444D0000009B6580000DE86F0000029B38000004F260000000EAC80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B8000015634000000405E00000080BC00000017B800000239400000006C00000000D80000000024000091A43300001B3CA000003444D0000009B6580000DE86F0000029B38000004F260000000EAC80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B80000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B8000015634000000405E00000080BC00000017B800000239400000006C00000000D8000000002400000DE86F0000029B38000004F260000000EAC8000015634000000405E00000080BC00000017B8000015634000000405E00000080BC00000017B800000239400000006C00000000D800000000240000015634000000405E00000080BC00000017B800000239400000006C00000000D80000000024000000239400000006C00000000D8000000002400000003600000000090000000012000000000300067836E580012AA376000272B78E0000707DA80009CADE380001C1F6A00003B81E200000A96200009CADE380001C1F6A00003B81E200000A96200000EE078800002A588000005AC00000000FA980008F38A2000019B1EA0000367940000009B6580000D9E500000026D960000053670000000EAC80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B80008F38A2000019B1EA0000367940000009B6580000D9E500000026D960000053670000000EAC80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B8000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D8000000002400008F38A2000019B1EA0000367940000009B6580000D9E500000026D960000053670000000EAC80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B80000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B8000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D8000000002400000D9E500000026D960000053670000000EAC8000014D9C0000003AB200000080BC00000017B8000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D800000000240000014D9C0000003AB200000080BC00000017B800000202F00000005EE0000000D80000000024000000202F00000005EE0000000D8000000002400000003600000000090000000012000000000300009231BD00001B7F0E000036FE1C00000A5D680000DBF87000002975A0000052EB4000000FA980000DBF87000002975A0000052EB4000000FA98000014BAD0000003EA60000007D4C00000017B80000DBF87000002975A0000052EB4000000FA98000014BAD0000003EA60000007D4C00000017B8000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC00000002400000DBF87000002975A0000052EB4000000FA98000014BAD0000003EA60000007D4C00000017B8000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000001F5300000005EE0000000BDC00000002400000002F70000000090000000012000000000300000DBF87000002975A0000052EB4000000FA98000014BAD0000003EA60000007D4C00000017B8000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000001F5300000005EE0000000BDC00000002400000002F7000000009000000001200000000030000014BAD0000003EA60000007D4C00000017B8000001F5300000005EE0000000BDC0000000240000001F5300000005EE0000000BDC00000002400000002F7000000009000000001200000000030000001F5300000005EE0000000BDC00000002400000002F70000000090000000012000000000300000002F7000000009000000001200000000030000000048000000000C000000001800000000067
  | 12 => 0x2E3186E57A83C9CD28D943D175DE94404F4308CF03D8226C84805025C112C050C119BC800676F2DD43DD1EF202C050AD3A7BC05179620D00068AB60C4051EC65F240069D820DC006AE07B9C000864C8E83C3A343C8804E9792EE404F75C36A400661470D00503058C440067A2A82C0068DB782C00083D86B0050BEE87D4006885DB30006A1EA69C00085E72C0006AFFD9F4000880A5080008A484500000B8DFB83C3A343C8804E9792EE404F75C36A400661470D00503058C440067A2A82C0068DB782C00083D86B0050BEE87D4006885DB30006A1EA69C00085E72C0006AFFD9F4000880A5080008A484500000B8DFB804F5C3A5500066B62E04006865C7DC00083AF1500069C113E0000867962400088F7B780000B75200006ADE3B240008811B740008B4F1680000BAEA900008D1D76C0000BE75B80000CF250800000FEF283C3A343C8804E9792EE404F75C36A400661470D00503058C440067A2A82C0068DB782C00083D86B0050BEE87D4006885DB30006A1EA69C00085E72C0006AFFD9F4000880A5080008A484500000B8DFB804F5C3A5500066B62E04006865C7DC00083AF1500069C113E0000867962400088F7B780000B75200006ADE3B240008811B740008B4F1680000BAEA900008D1D76C0000BE75B80000CF250800000FEF2804F5C3A5500066B62E04006865C7DC00083AF1500069C113E0000867962400088F7B780000B75200006ADE3B240008811B740008B4F1680000BAEA900008D1D76C0000BE75B80000CF250800000FEF28006A7D60480008792A2C0008AED7940000BA68F80008D85A440000BF0B6C0000D04780000010058000090065940000C275100000D5459000001067D00000E884F8000011E2D8000011E2D800000160383DD1EF202C05452FE378051264D744006E1DE1F8051AE61BC0006F53A62C006A06C9D40008F295FC0522E6D220007037AFB0006B1EE12800091244C4006BA4357800092D8D6C00089893B00000B8DFB8050BEE87D4006E586E2800695213180008EDFC78006A518014000913B7AC00088126A00000B75200006B51CC8000092F09440008A0EBC00000BAEA900008B031E80000BE75B80000BE75B800000FEF28050BEE87D4006E586E2800695213180008EDFC78006A518014000913B7AC00088126A00000B75200006B51CC8000092F09440008A0EBC00000BAEA900008B031E80000BE75B80000BE75B800000FEF28006ADE3B24000926ED880008982F240000BA68F80008B411F80000BF0B6C0000BF0B6C00001005800008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D80000016038050BEE87D4006E586E2800695213180008EDFC78006A518014000913B7AC00088126A00000B75200006B51CC8000092F09440008A0EBC00000BAEA900008B031E80000BE75B80000BE75B800000FEF28006ADE3B24000926ED880008982F240000BA68F80008B411F80000BF0B6C0000BF0B6C00001005800008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D80000016038006ADE3B24000926ED880008982F240000BA68F80008B411F80000BF0B6C0000BF0B6C00001005800008D624F80000C275100000C2751000001067D00000CE9294000011E2D8000011E2D8000001603800090065940000C61F800000C61F80000010B8400000D3CF340000125708000012570800000169280000E816100000141D380000141D380000018C180000141D380000018C180000018C180000001E783D8226C8480512B191A805452FE378006E1DE1F805156EA398006A96F9B4006F53A62C0008F295FC051AE61BC0006B538D9C007037AFB000091244C4006B20299C0008B73D0C00092D8D6C0000B8DFB80503058C4400696ED320006E586E280008EDFC780069A63AF000089BAF20000913B7AC0000B75200006A5180140008B04CB800092F09440000BAEA900008A10B080000B255F80000BE75B800000FEF280503058C4400696ED320006E586E280008EDFC780069A63AF000089BAF20000913B7AC0000B75200006A5180140008B04CB800092F09440000BAEA900008A10B080000B255F80000BE75B800000FEF280069C113E00008A59DD8000926ED880000BA68F800089FBBE00000B26A140000BF0B6C00001005800008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D800000160380503058C4400696ED320006E586E280008EDFC780069A63AF000089BAF20000913B7AC0000B75200006A5180140008B04CB800092F09440000BAEA900008A10B080000B255F80000BE75B800000FEF280069C113E00008A59DD8000926ED880000BA68F800089FBBE00000B26A140000BF0B6C00001005800008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D800000160380069C113E00008A59DD8000926ED880000BA68F800089FBBE00000B26A140000BF0B6C00001005800008B411F80000B470740000C2751000001067D00000C2751000001067D0000011E2D800000160380008D85A440000B773500000C61F80000010B8400000C61F80000010B840000012570800000169280000D3CF34000011DD280000141D380000018C180000141D380000018C180000018C180000001E78051EC65F24007037AFB0007037AFB00009972788006B20299C000926824800092682480000C6CABC006BA43578000939E298000939E2980000C9D44C0008A517C80000BCF5680000BCF56800000FEF28006AFFD9F400092F094400092F09440000C95DE00008A10B080000BD14B00000BD14B000001005800008B031E80000BF4C380000BF4C3800001067D00000BF4C3800001067D000001067D00000016038006AFFD9F400092F094400092F09440000C95DE00008A10B080000BD14B00000BD14B000001005800008B031E80000BF4C380000BF4C3800001067D00000BF4C3800001067D000001067D000000160380008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E78006AFFD9F400092F094400092F09440000C95DE00008A10B080000BD14B00000BD14B000001005800008B031E80000BF4C380000BF4C3800001067D00000BF4C3800001067D000001067D000000160380008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780008D1D76C0000C275100000C27510000010B8400000C27510000010B840000010B84000000169280000CE9294000011DD28000011DD280000018C18000011DD280000018C180000018C180000001E780000E884F80000141D380000141D38000001BE440000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A43D175DE944050423A4D805149056100069C7F25405452FE378006E1DE1F8006F53A62C0008F295FC051264D7440069EE3810006B9DDF500008A8AE1C007037AFB000091244C400092D8D6C0000B8DFB804F75C36A40067C468800069AC40A8000882E108006E586E280008EDFC78000913B7AC0000B752000069521318000883C0780008BB57340000B092A000092F09440000BAEA900000BE75B800000FEF2804F75C36A40067C468800069AC40A8000882E108006E586E280008EDFC78000913B7AC0000B752000069521318000883C0780008BB57340000B092A000092F09440000BAEA900000BE75B800000FEF28006865C7DC00087120500008ADF1700000AF9A9C000926ED880000BA68F80000BF0B6C00001005800008982F240000AE7ED80000B64C6000000F47600000C2751000001067D0000011E2D8000001603804F75C36A40067C468800069AC40A8000882E108006E586E280008EDFC78000913B7AC0000B752000069521318000883C0780008BB57340000B092A000092F09440000BAEA900000BE75B800000FEF28006865C7DC00087120500008ADF1700000AF9A9C000926ED880000BA68F80000BF0B6C00001005800008982F240000AE7ED80000B64C6000000F47600000C2751000001067D0000011E2D80000016038006865C7DC00087120500008ADF1700000AF9A9C000926ED880000BA68F80000BF0B6C00001005800008982F240000AE7ED80000B64C6000000F47600000C2751000001067D0000011E2D800000160380008AED7940000B04F980000B89A4000000F78880000C61F80000010B840000012570800000169280000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E7805179620D0006F53A62C006B9DDF50000926E020007037AFB0000997278800092682480000C6CABC006B1EE12800092682480008CB7A900000BEEC24000939E2980000C9D44C0000BCF56800000FEF28006A1EA69C000913B7AC0008BB57340000BDFF4C00092F09440000C95DE00000BD14B000001005800008A0EBC00000BD14B00000B4801800000F47600000BF4C3800001067D000001067D00000016038006A1EA69C000913B7AC0008BB57340000BDFF4C00092F09440000C95DE00000BD14B000001005800008A0EBC00000BD14B00000B4801800000F47600000BF4C3800001067D000001067D000000160380008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E78006A1EA69C000913B7AC0008BB57340000BDFF4C00092F09440000C95DE00000BD14B000001005800008A0EBC00000BD14B00000B4801800000F47600000BF4C3800001067D000001067D000000160380008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780008B4F1680000BF0B6C0000B64C6000000F78880000C27510000010B840000010B84000000169280000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000D54590000012570800001257080000018C180000141D38000001BE44000001BE4400000022540000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A4050C119BC8006AE449CC006F53A62C000926E020006F53A62C000926E02000099727880000C6CABC006A06C9D40008B9FCE000092682480000BEEC2400092682480000BEEC240000C9D44C00000FEF280068DB782C0008A4D284000913B7AC0000BDFF4C000913B7AC0000BDFF4C0000C95DE0000010058000088126A00000B23FA00000BD14B000000F47600000BD14B000000F476000001067D000000160380068DB782C0008A4D284000913B7AC0000BDFF4C000913B7AC0000BDFF4C0000C95DE0000010058000088126A00000B23FA00000BD14B000000F47600000BD14B000000F476000001067D0000001603800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780068DB782C0008A4D284000913B7AC0000BDFF4C000913B7AC0000BDFF4C0000C95DE0000010058000088126A00000B23FA00000BD14B000000F47600000BD14B000000F476000001067D0000001603800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800088F7B780000B399F40000BF0B6C00000F78880000BF0B6C00000F7888000010B84000000169280000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780000D04780000010DAC800001257080000018C1800001257080000018C18000001BE44000000225400001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A4006AE07B9C00092D8D6C00092D8D6C0000C9D44C00092D8D6C0000C9D44C0000C9D44C0000114F6000089893B00000BCF5680000BCF56800001032300000BCF5680000103230000010323000000160380008A484500000BE75B80000BE75B800001067D00000BE75B800001067D000001067D000000169280000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780008A484500000BE75B80000BE75B800001067D00000BE75B800001067D000001067D000000169280000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40008A484500000BE75B80000BE75B800001067D00000BE75B800001067D000001067D000000169280000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000CF2508000011E2D8000011E2D80000018C18000011E2D80000018C180000018C180000002254000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A400000000343C9CD28D9404F8006100050423A4D80068199EB40512B191A80069C476D0006AE449CC000890254805452FE378006E1DE1F8006F53A62C0008F295FC007037AFB000091244C400092D8D6C0000B8DFB804E9792EE400667092E00067C46880000852102C00696ED320000882738C0008A4D2840000ADD508006E586E280008EDFC78000913B7AC0000B7520000092F09440000BAEA900000BE75B800000FEF2804E9792EE400667092E00067C46880000852102C00696ED320000882738C0008A4D2840000ADD508006E586E280008EDFC78000913B7AC0000B7520000092F09440000BAEA900000BE75B800000FEF280066B62E0400084A3BF000087120500000A9D3740008A59DD80000AF8AF80000B399F400000F0458000926ED880000BA68F80000BF0B6C00001005800000C2751000001067D0000011E2D8000001603804E9792EE400667092E00067C46880000852102C00696ED320000882738C0008A4D2840000ADD508006E586E280008EDFC78000913B7AC0000B7520000092F09440000BAEA900000BE75B800000FEF280066B62E0400084A3BF000087120500000A9D3740008A59DD80000AF8AF80000B399F400000F0458000926ED880000BA68F80000BF0B6C00001005800000C2751000001067D0000011E2D800000160380066B62E0400084A3BF000087120500000A9D3740008A59DD80000AF8AF80000B399F400000F0458000926ED880000BA68F80000BF0B6C00001005800000C2751000001067D0000011E2D800000160380008792A2C0000ABE9780000B04F9800000EC5C80000B7735000000F7888000010DAC80000014BE80000C61F80000010B840000012570800000169280000141D380000018C180000018C180000001E78050AD3A7BC006E1DE1F80069EE38100008FDCD28006B538D9C000926E0200008B9FCE00000BCCD30007037AFB0000997278800092682480000C6CABC000939E2980000C9D44C0000BCF56800000FEF28006885DB300008EDFC78000883C0780000B8D6C80008B04CB80000BDFF4C0000B23FA000000F045800092F09440000C95DE00000BD14B000001005800000BF4C3800001067D000001067D00000016038006885DB300008EDFC78000883C0780000B8D6C80008B04CB80000BDFF4C0000B23FA000000F045800092F09440000C95DE00000BD14B000001005800000BF4C3800001067D000001067D000000160380008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E78006885DB300008EDFC78000883C0780000B8D6C80008B04CB80000BDFF4C0000B23FA000000F045800092F09440000C95DE00000BD14B000001005800000BF4C3800001067D000001067D000000160380008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780008811B740000BA68F80000AE7ED800000EC5C80000B4707400000F788800000F78880000014BE80000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000C27510000010B840000010B8400000016928000011DD280000018C180000018C180000001E780000141D38000001BE44000001BE440000002254000001BE440000002254000000225400000002A405025C112C0069C476D0006E1DE1F80008FDCD28006A96F9B40008BD01F8000926E0200000BCCD30006F53A62C000926E02000099727880000C6CABC00092682480000BEEC240000C9D44C00000FEF280067A2A82C000882738C0008EDFC780000B8D6C800089BAF200000B397B80000BDFF4C00000F0458000913B7AC0000BDFF4C0000C95DE000001005800000BD14B000000F476000001067D000000160380067A2A82C000882738C0008EDFC780000B8D6C800089BAF200000B397B80000BDFF4C00000F0458000913B7AC0000BDFF4C0000C95DE000001005800000BD14B000000F476000001067D0000001603800086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE80000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780067A2A82C000882738C0008EDFC780000B8D6C800089BAF200000B397B80000BDFF4C00000F0458000913B7AC0000BDFF4C0000C95DE000001005800000BD14B000000F476000001067D0000001603800086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE80000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800086796240000AF8AF80000BA68F800000EC5C80000B26A1400000E66B800000F78880000014BE80000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E780000BF0B6C00000F7888000010B8400000016928000010B84000000169280000018C180000001E7800001257080000018C18000001BE440000002254000001BE440000002254000000225400000002A40069D820DC00091244C400091244C40000C6CABC0008B73D0C0000BEEC240000BEEC240000103F9800092D8D6C0000C9D44C0000C9D44C0000114F600000BCF568000010323000001032300000016038000880A5080000BAEA900000BAEA9000001005800000B255F800000F476000000F47600000014BE80000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000880A5080000BAEA900000BAEA9000001005800000B255F800000F476000000F47600000014BE80000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000880A5080000BAEA900000BAEA9000001005800000B255F800000F476000000F47600000014BE80000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E780000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000BE75B800001067D000001067D0000001692800001067D0000001692800000169280000001E78000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A4000011E2D80000018C180000018C1800000022540000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A4000000003404F4308CF00068199EB40069C7F25400089B8270006E1DE1F80008FDCD28000926E0200000BCCD30006E1DE1F80008FDCD28000926E0200000BCCD3000099727880000C6CABC0000C9D44C00000FEF2800661470D0000852102C000882E1080000AF59D00008EDFC780000B8D6C80000BDFF4C00000F04580008EDFC780000B8D6C80000BDFF4C00000F04580000C95DE0000010058000001067D0000001603800661470D0000852102C000882E1080000AF59D00008EDFC780000B8D6C80000BDFF4C00000F04580008EDFC780000B8D6C80000BDFF4C00000F04580000C95DE0000010058000001067D0000001603800083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE80000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E7800661470D0000852102C000882E1080000AF59D00008EDFC780000B8D6C80000BDFF4C00000F04580008EDFC780000B8D6C80000BDFF4C00000F04580000C95DE0000010058000001067D0000001603800083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE80000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E7800083AF1500000A9D3740000AF9A9C00000DD3400000BA68F800000EC5C800000F78880000014BE80000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E780000BA68F800000EC5C800000F78880000014BE8000010B84000000169280000018C180000001E78000010B84000000169280000018C180000001E78000001BE440000002254000000225400000002A40068AB60C40008F295FC0008A8AE1C0000BCCD3000091244C40000C6CABC0000BEEC240000103F9800091244C40000C6CABC0000BEEC240000103F980000C9D44C0000114F600000103230000001603800085E72C00000B752000000B092A000000F04580000BAEA90000010058000000F47600000014BE80000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800085E72C00000B752000000B092A000000F04580000BAEA90000010058000000F47600000014BE80000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E780000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800001067D0000001692800000169280000001E780000018C180000002254000000225400000002A400085E72C00000B752000000B092A000000F04580000BAEA90000010058000000F47600000014BE80000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E780000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800001067D0000001692800000169280000001E780000018C180000002254000000225400000002A40000BAEA90000010058000000F47600000014BE800001067D0000001692800000169280000001E7800001067D0000001692800000169280000001E780000018C180000002254000000225400000002A400001067D0000001692800000169280000001E780000018C180000002254000000225400000002A40000018C180000002254000000225400000002A4000000225400000002A400000002A4000000003400676F2DD400089025480008F295FC0000BCCD300008F295FC0000BCCD300000C6CABC0000103F980008F295FC0000BCCD300000C6CABC0000103F980000C6CABC0000103F980000114F60000001603800083D86B00000ADD5080000B7520000000F04580000B7520000000F045800001005800000014BE80000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800083D86B00000ADD5080000B7520000000F04580000B7520000000F045800001005800000014BE80000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E780000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A400083D86B00000ADD5080000B7520000000F04580000B7520000000F045800001005800000014BE80000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E780000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A40000B7520000000F045800001005800000014BE800001005800000014BE800000169280000001E7800001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A400001005800000014BE800000169280000001E7800000169280000001E78000000225400000002A400000169280000001E78000000225400000002A4000000225400000002A400000002A40000000034000864C8E80000B8DFB80000B8DFB800000FEF280000B8DFB800000FEF2800000FEF2800000160380000B8DFB800000FEF2800000FEF28000001603800000FEF28000001603800000160380000001E780000B8DFB800000FEF2800000FEF28000001603800000FEF28000001603800000160380000001E7800000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A40000B8DFB800000FEF2800000FEF28000001603800000FEF28000001603800000160380000001E7800000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000160380000001E780000001E7800000002A40000001E7800000002A400000002A400000000340000B8DFB800000FEF2800000FEF28000001603800000FEF28000001603800000160380000001E7800000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000160380000001E780000001E7800000002A40000001E7800000002A400000002A4000000003400000FEF28000001603800000160380000001E7800000160380000001E780000001E7800000002A400000160380000001E780000001E7800000002A40000001E7800000002A400000002A4000000003400000160380000001E780000001E7800000002A40000001E7800000002A400000002A400000000340000001E7800000002A400000002A4000000003400000002A40000000034000000003400000000068
  | _ => 0

def BaseTab (u : Fin 2048) : Prop :=
    G 0 u = tb (tabT 0) u.val

instance (u : Fin 2048) : Decidable (BaseTab u) := by
  unfold BaseTab
  infer_instance

set_option maxRecDepth 20000 in
abbrev base_T_chunk_0 : ∀ i : Fin 32, BaseTab (idIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_1 : ∀ i : Fin 32, BaseTab (idIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_2 : ∀ i : Fin 32, BaseTab (idIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_3 : ∀ i : Fin 32, BaseTab (idIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_4 : ∀ i : Fin 32, BaseTab (idIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_5 : ∀ i : Fin 32, BaseTab (idIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_6 : ∀ i : Fin 32, BaseTab (idIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_7 : ∀ i : Fin 32, BaseTab (idIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_8 : ∀ i : Fin 32, BaseTab (idIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_9 : ∀ i : Fin 32, BaseTab (idIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_10 : ∀ i : Fin 32, BaseTab (idIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_11 : ∀ i : Fin 32, BaseTab (idIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_12 : ∀ i : Fin 32, BaseTab (idIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_13 : ∀ i : Fin 32, BaseTab (idIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_14 : ∀ i : Fin 32, BaseTab (idIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_15 : ∀ i : Fin 32, BaseTab (idIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_16 : ∀ i : Fin 32, BaseTab (idIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_17 : ∀ i : Fin 32, BaseTab (idIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_18 : ∀ i : Fin 32, BaseTab (idIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_19 : ∀ i : Fin 32, BaseTab (idIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_20 : ∀ i : Fin 32, BaseTab (idIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_21 : ∀ i : Fin 32, BaseTab (idIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_22 : ∀ i : Fin 32, BaseTab (idIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_23 : ∀ i : Fin 32, BaseTab (idIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_24 : ∀ i : Fin 32, BaseTab (idIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_25 : ∀ i : Fin 32, BaseTab (idIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_26 : ∀ i : Fin 32, BaseTab (idIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_27 : ∀ i : Fin 32, BaseTab (idIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_28 : ∀ i : Fin 32, BaseTab (idIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_29 : ∀ i : Fin 32, BaseTab (idIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_30 : ∀ i : Fin 32, BaseTab (idIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_31 : ∀ i : Fin 32, BaseTab (idIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_32 : ∀ i : Fin 32, BaseTab (idIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_33 : ∀ i : Fin 32, BaseTab (idIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_34 : ∀ i : Fin 32, BaseTab (idIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_35 : ∀ i : Fin 32, BaseTab (idIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_36 : ∀ i : Fin 32, BaseTab (idIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_37 : ∀ i : Fin 32, BaseTab (idIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_38 : ∀ i : Fin 32, BaseTab (idIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_39 : ∀ i : Fin 32, BaseTab (idIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_40 : ∀ i : Fin 32, BaseTab (idIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_41 : ∀ i : Fin 32, BaseTab (idIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_42 : ∀ i : Fin 32, BaseTab (idIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_43 : ∀ i : Fin 32, BaseTab (idIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_44 : ∀ i : Fin 32, BaseTab (idIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_45 : ∀ i : Fin 32, BaseTab (idIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_46 : ∀ i : Fin 32, BaseTab (idIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_47 : ∀ i : Fin 32, BaseTab (idIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_48 : ∀ i : Fin 32, BaseTab (idIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_49 : ∀ i : Fin 32, BaseTab (idIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_50 : ∀ i : Fin 32, BaseTab (idIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_51 : ∀ i : Fin 32, BaseTab (idIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_52 : ∀ i : Fin 32, BaseTab (idIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_53 : ∀ i : Fin 32, BaseTab (idIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_54 : ∀ i : Fin 32, BaseTab (idIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_55 : ∀ i : Fin 32, BaseTab (idIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_56 : ∀ i : Fin 32, BaseTab (idIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_57 : ∀ i : Fin 32, BaseTab (idIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_58 : ∀ i : Fin 32, BaseTab (idIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_59 : ∀ i : Fin 32, BaseTab (idIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_60 : ∀ i : Fin 32, BaseTab (idIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_61 : ∀ i : Fin 32, BaseTab (idIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_62 : ∀ i : Fin 32, BaseTab (idIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev base_T_chunk_63 : ∀ i : Fin 32, BaseTab (idIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev base_T : ∀ u : Fin 2048, G 0 u = tb (tabT 0) u.val := by
  intro u
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

def tableIndex (k : Fin 2048) (i : Fin 1) : Fin 2048 := ⟨1 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩

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
abbrev tab_base_chunk_0 : ∀ i : Fin 32, DiffTab (idIndex 0 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_1 : ∀ i : Fin 32, DiffTab (idIndex 1 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_2 : ∀ i : Fin 32, DiffTab (idIndex 2 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_3 : ∀ i : Fin 32, DiffTab (idIndex 3 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_4 : ∀ i : Fin 32, DiffTab (idIndex 4 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_5 : ∀ i : Fin 32, DiffTab (idIndex 5 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_6 : ∀ i : Fin 32, DiffTab (idIndex 6 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_7 : ∀ i : Fin 32, DiffTab (idIndex 7 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_8 : ∀ i : Fin 32, DiffTab (idIndex 8 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_9 : ∀ i : Fin 32, DiffTab (idIndex 9 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_10 : ∀ i : Fin 32, DiffTab (idIndex 10 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_11 : ∀ i : Fin 32, DiffTab (idIndex 11 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_12 : ∀ i : Fin 32, DiffTab (idIndex 12 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_13 : ∀ i : Fin 32, DiffTab (idIndex 13 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_14 : ∀ i : Fin 32, DiffTab (idIndex 14 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_15 : ∀ i : Fin 32, DiffTab (idIndex 15 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_16 : ∀ i : Fin 32, DiffTab (idIndex 16 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_17 : ∀ i : Fin 32, DiffTab (idIndex 17 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_18 : ∀ i : Fin 32, DiffTab (idIndex 18 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_19 : ∀ i : Fin 32, DiffTab (idIndex 19 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_20 : ∀ i : Fin 32, DiffTab (idIndex 20 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_21 : ∀ i : Fin 32, DiffTab (idIndex 21 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_22 : ∀ i : Fin 32, DiffTab (idIndex 22 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_23 : ∀ i : Fin 32, DiffTab (idIndex 23 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_24 : ∀ i : Fin 32, DiffTab (idIndex 24 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_25 : ∀ i : Fin 32, DiffTab (idIndex 25 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_26 : ∀ i : Fin 32, DiffTab (idIndex 26 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_27 : ∀ i : Fin 32, DiffTab (idIndex 27 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_28 : ∀ i : Fin 32, DiffTab (idIndex 28 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_29 : ∀ i : Fin 32, DiffTab (idIndex 29 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_30 : ∀ i : Fin 32, DiffTab (idIndex 30 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_31 : ∀ i : Fin 32, DiffTab (idIndex 31 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_32 : ∀ i : Fin 32, DiffTab (idIndex 32 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_33 : ∀ i : Fin 32, DiffTab (idIndex 33 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_34 : ∀ i : Fin 32, DiffTab (idIndex 34 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_35 : ∀ i : Fin 32, DiffTab (idIndex 35 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_36 : ∀ i : Fin 32, DiffTab (idIndex 36 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_37 : ∀ i : Fin 32, DiffTab (idIndex 37 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_38 : ∀ i : Fin 32, DiffTab (idIndex 38 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_39 : ∀ i : Fin 32, DiffTab (idIndex 39 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_40 : ∀ i : Fin 32, DiffTab (idIndex 40 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_41 : ∀ i : Fin 32, DiffTab (idIndex 41 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_42 : ∀ i : Fin 32, DiffTab (idIndex 42 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_43 : ∀ i : Fin 32, DiffTab (idIndex 43 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_44 : ∀ i : Fin 32, DiffTab (idIndex 44 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_45 : ∀ i : Fin 32, DiffTab (idIndex 45 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_46 : ∀ i : Fin 32, DiffTab (idIndex 46 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_47 : ∀ i : Fin 32, DiffTab (idIndex 47 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_48 : ∀ i : Fin 32, DiffTab (idIndex 48 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_49 : ∀ i : Fin 32, DiffTab (idIndex 49 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_50 : ∀ i : Fin 32, DiffTab (idIndex 50 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_51 : ∀ i : Fin 32, DiffTab (idIndex 51 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_52 : ∀ i : Fin 32, DiffTab (idIndex 52 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_53 : ∀ i : Fin 32, DiffTab (idIndex 53 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_54 : ∀ i : Fin 32, DiffTab (idIndex 54 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_55 : ∀ i : Fin 32, DiffTab (idIndex 55 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_56 : ∀ i : Fin 32, DiffTab (idIndex 56 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_57 : ∀ i : Fin 32, DiffTab (idIndex 57 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_58 : ∀ i : Fin 32, DiffTab (idIndex 58 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_59 : ∀ i : Fin 32, DiffTab (idIndex 59 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_60 : ∀ i : Fin 32, DiffTab (idIndex 60 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_61 : ∀ i : Fin 32, DiffTab (idIndex 61 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_62 : ∀ i : Fin 32, DiffTab (idIndex 62 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
abbrev tab_base_chunk_63 : ∀ i : Fin 32, DiffTab (idIndex 63 i) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
abbrev tab_base : ∀ u : Fin 2048, tb (tabT 12) u.val + 66 * tb (tabT 10) u.val + 495 * tb (tabT 8) u.val + 924 * tb (tabT 6) u.val + 495 * tb (tabT 4) u.val + 66 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      12 * tb (tabT 11) u.val + 220 * tb (tabT 9) u.val + 792 * tb (tabT 7) u.val + 792 * tb (tabT 5) u.val + 220 * tb (tabT 3) u.val + 12 * tb (tabT 1) u.val := by
  intro u
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

theorem G_vals : G 1 2047 = 21 ∧ G 2 2047 = 7054 ∧ G 3 2047 = 348066 ∧ G 4 2047 = 6415638 ∧ G 5 2047 = 65419155 ∧ G 6 2047 = 449532868 ∧ G 7 2047 = 2330996068 ∧ G 8 2047 = 9790907652 ∧ G 9 2047 = 34925259201 ∧ G 10 2047 = 109359675810 ∧ G 11 2047 = 307898807590 ∧ G 12 2047 = 793597679082 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num), G_eq_T 10 (by norm_num), G_eq_T 11 (by norm_num), G_eq_T 12 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 21 ∧ a 2 = 7054 ∧ a 3 = 348066 ∧ a 4 = 6415638 ∧ a 5 = 65419155 ∧ a 6 = 449532868 ∧ a 7 = 2330996068 ∧ a 8 = 9790907652 ∧ a 9 = 34925259201 ∧ a 10 = 109359675810 ∧ a 11 = 307898807590 ∧ a 12 = 793597679082 := by
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
      X * (21 + 6802 * X + 264804 * X ^ 2 + 2699790 * X ^ 3 + 9862370 * X ^ 4 + 14835694 * X ^ 5 + 9550828 * X ^ 6 + 2483826 * X ^ 7 + 209945 * X ^ 8 + 2720 * X ^ 9) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 12 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 12 * (PowerSeries.mk F * X ^ 1) + C 66 * (PowerSeries.mk F * X ^ 2) - C 220 * (PowerSeries.mk F * X ^ 3) + C 495 * (PowerSeries.mk F * X ^ 4) - C 792 * (PowerSeries.mk F * X ^ 5) + C 924 * (PowerSeries.mk F * X ^ 6) - C 792 * (PowerSeries.mk F * X ^ 7) + C 495 * (PowerSeries.mk F * X ^ 8) - C 220 * (PowerSeries.mk F * X ^ 9) + C 66 * (PowerSeries.mk F * X ^ 10) - C 12 * (PowerSeries.mk F * X ^ 11) + C 1 * (PowerSeries.mk F * X ^ 12) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (21 + 6802 * X + 264804 * X ^ 2 + 2699790 * X ^ 3 + 9862370 * X ^ 4 + 14835694 * X ^ 5 + 9550828 * X ^ 6 + 2483826 * X ^ 7 + 209945 * X ^ 8 + 2720 * X ^ 9) : ℚ⟦X⟧) =
      C 21 * X ^ 1 + C 6802 * X ^ 2 + C 264804 * X ^ 3 + C 2699790 * X ^ 4 + C 9862370 * X ^ 5 + C 14835694 * X ^ 6 + C 9550828 * X ^ 7 + C 2483826 * X ^ 8 + C 209945 * X ^ 9 + C 2720 * X ^ 10 := by
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

end OMA.A250063

theorem OMA.solution : type_of% @OMA.S_oeis_a250063.main :=
  ⟨OMA.A250063.gen_fun, OMA.A250063.recurrence⟩
