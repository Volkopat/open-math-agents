import OMAStatements.S_oeis_a250391

/-!
A250391: exact eight-position/five-window adaptation of the threshold-chain proof
by @Salofe for A250064, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
Conjecture: Colin Barker (2017); registered statement: @clementtrecourt, PR #19870.
The finite tables certify a recurrence on every subset state; linearity then proves
it for all levels. All computations are kernel checked.
-/

namespace OMA.A250391

open OMA.S_oeis_a250391 Finset

/-! ### The window condition -/

/-- The condition of the statement on 4 values (without the bound on `v`). -/
def Cy (y : Fin 4 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 4)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 4 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
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

theorem cy_of (y : Fin 4 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 4)) y Finset.univ_nonempty
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

theorem window_iff (y : Fin 4 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 4 → ℕ) :
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
def fget (f : Fin 8 → Bool) (k : ℕ) : Bool := if h : k < 8 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 8 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 4 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 8 → Bool) : Prop := ∀ i < (5 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 8 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 8 → Fin (n + 1)) (v : ℕ) : Fin 8 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 8 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a250391.get x k ≤ n := by
  unfold OMA.S_oeis_a250391.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (5 : ℕ), cntW (fun _ => true) i = 4 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 8 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (5 : ℕ), ¬ Cy (fun t : Fin 4 => OMA.S_oeis_a250391.get x (i + t)) := by
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
      (univ.filter (fun t : Fin 4 => OMA.S_oeis_a250391.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 8 := by have := t.isLt; omega
    unfold OMA.S_oeis_a250391.get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 8 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 8 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 8 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 8 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) : Fin 8 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) : Fin 8 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 8 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 8 → Bool) (x : Fin 8 → Fin (n + 1)) (p : Fin 8) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 8 → Bool) :
    M (n + 1) T = ∑ S : Fin 8 → Bool,
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
def row (u : Fin 256) : Fin 8 → Bool := fun p => Nat.testBit u.val p.val

/-- The code of a set of positions. -/
def code (f : Fin 8 → Bool) : ℕ := ∑ p : Fin 8, if f p = true then 2 ^ p.val else 0

theorem code_row : ∀ u : Fin 256, code (row u) = u.val := by
  decide +kernel

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  rw [← code_row a, ← code_row b, h]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- Number of set bits among the low 8 bits. -/
def pcb (m : ℕ) : ℕ :=
  m % 2 + m / 2 % 2 + m / 4 % 2 + m / 8 % 2 + m / 16 % 2 + m / 32 % 2 + m / 64 % 2 + m / 128 % 2

theorem cnt_row : ∀ u : Fin 256, cntW (row u) 0 = pcb (u.val &&& 15) ∧
    cntW (row u) 1 = pcb (u.val &&& 30) ∧
    cntW (row u) 2 = pcb (u.val &&& 60) ∧
    cntW (row u) 3 = pcb (u.val &&& 120) ∧
    cntW (row u) 4 = pcb (u.val &&& 240) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 15) ≤ 1 ∧ 3 ≤ pcb (t &&& 15)) ∧
    ¬ (pcb (s &&& 30) ≤ 1 ∧ 3 ≤ pcb (t &&& 30)) ∧
    ¬ (pcb (s &&& 60) ≤ 1 ∧ 3 ≤ pcb (t &&& 60)) ∧
    ¬ (pcb (s &&& 120) ≤ 1 ∧ 3 ≤ pcb (t &&& 120)) ∧
    ¬ (pcb (s &&& 240) ≤ 1 ∧ 3 ≤ pcb (t &&& 240)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (5 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 256) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4]

theorem sub_iff (w u : Fin 256) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 8
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (256 : ℕ) ≤ 2 ^ i := by
          calc (256 : ℕ) = 2 ^ 8 := by norm_num
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
def subs (u : Fin 256) : Finset (Fin 256) :=
  univ.filter (fun w : Fin 256 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 256 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 256, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 255 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = (G n 255 : ℤ) := by
  classical
  have h1 : (univ.filter (fun x : Fin 8 → Fin (n + 1) => good x)) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 255 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 255)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 255 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 255 := by
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

theorem G_succ (n : ℕ) (u : Fin 256) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl


/-! Packed tables certify the recursion on every state. -/
-- Each table row stores its field width followed by its packed coefficients.
def tb (T : ℕ × ℕ) (w : ℕ) : ℕ := (T.2 >>> (T.1 * w)) % 2 ^ T.1

def tabT : ℕ → ℕ × ℕ
  | 0 => (1, 0x177f0000077f033f177f0000007f003f177f000f077f033f177f)
  | 1 => (5, 0x30c6318cc318cc3618c318c63298c34b186618c31846318cc329586618c3631906420864208821041842118cc318cc3618c3318c6642086420882104308c631a0831a0882104318c8321043210441082184210844118cc3618c318c63298c364208821041846318cc331a0882104318c83210432104410821842118cc318cc38210418c633210432104410821846318d0418d044108218c64190821908220841)
  | 2 => (10, 0x808b52f060308642643331c6727c353cc511441b31c6c1b0382585715c1d3848721c2d21c2d0b40f308431b0381b03815c1d2584d21c2d21c2d0b40f3cc8721c5121c511441b21c511441b1441b06c092f03a110221b03815c1d1b03815c1d21c2d0b40f27c5715c2d21c511441b21c511441b1441b06c092643315c2d15c2d1441b15c2d1441b1441b06c091442d0b41b0b41b06c090b41b06c0906c09024032d4370e81d10c220cc111b03815c1d21c2d0b40f19c380e01d1342d0b40f21c511441b1441b06c09190220e01d0e01d0b40f15c2d1441b1441b06c091442d0b41b0b41b06c090b41b06c0906c09024031801d088110e01d0b40f0e01d0b40f1441b06c090d41d0740f0b41b06c090b41b06c0906c09024030cc110740f0740f06c090740f06c0906c090240306c0f03c0903c090240303c09024030240300c01)
  | 3 => (14, 0x94209da29543822adc3af14001402c583d215001501c801c807200722c58402100816214541e807a007a1b902a00a800a80a800a802a002a2adc2ee1008162100816207a007a14541be0a800a80a800a802a002a1c802a00a801000a8010004000400a8010004000400400040010001029542960be8100100816207a007a100816207a007a0a800a802a002a15001e807a00a80a8010004000400a80100040004004000400100010140015807a00a807a00a8040004007a00a804000400400040010001007200a802a004002a0040010001002a004001000100100010004000427682720a580de0bb81000560056100816207a007a0a800a802a002a0f48162058807a06f80a802a002a0a801000400040040004001000100ebc100058807a058807a02a002a07a00a804000400400040010001007200a802a004002a0040010001002a00400100010010001000400040e080de0400056058807a02a002a058807a02a002a04000400100010054007a01e802a02a0040010001002a0040010001001000100040004050005601e802a01e802a010001001e802a01000100100010004000401c802a00a801000a8010004000400a8010004000400400040010001)
  | 4 => (17, 0xa0ef111948f561232251f84c54307004d8266584f1032c80514101d019c80ce4014a266585280294005500c6981b580dac015e0fd202328119401c20465007080384005a251f84150294005500a50015400dac015e0c6981978119401c20465007080384005a101d02328119402710465009c404e2007d0465009c404e2007d0138801f400fa001923d583ae82120042e0a50015400dac015e0a50015400dac015e0465007080384005a0cb201b580dac01c20465009c404e2007d0465009c404e2007d0138801f400fa00190c1c015180dac01c2036b0070804e2007d036b0070804e2007d0138801f400fa00190339007080384007d00e1001f400fa001900e1001f400fa0019003e80064003200052232837e81d7403b6082a010b80a8c010e0a50015400dac015e0465007080384005a09e2015400aa0015e032f007080384005a0465009c404e2007d0138801f400fa0019098a810b80aa0015e02a8005780384005a036b0070804e2007d0138801f400fa00190339007080384007d00e1001f400fa001900e1001f400fa0019003e8006400320005091900ed8085c010e02a8005780384005a02a8005780384005a0138801f400fa0019028a0057802bc005a00e1001f400fa001900e1001f400fa0019003e8006400320005026c0043802bc005a00af0016800fa001900af0016800fa0019003e800640032000500a50016800b40019002d0006400320005002d0006400320005000c80014000a0001)
  | 5 => (19, 0xdf52c4ec8ca48d042b12a818116c02a5d00e1f2bdb611fe42c3d00ebf0d728047b808f7002fd2bdb612ad4255a80f550ade804b78096f003250d4b205cd00b9a003de02e6800f7801ef000a52a8180f80c255a80f550956a03d54096f003250ade80472c0b9a003de02e6800f7801ef000a50d72805cd00b9a0051002e68014400288000d802e68014400288000d800a2000360006c00024292340e36c1f6580cad0956a03d54096f003250956a03d54096f0032502e6800f7801ef000a50b0f404b78096f003de02e68014400288000d802e68014400288000d800a2000360006c000240a97403d68096f003de025bc00f780288000d8025bc00f780288000d800a2000360006c00024023dc00f7801ef000d8007bc00360006c00024007bc00360006c00024001b000090001200006276460d8ec1c6d80b7707c06032b407ad0028f0956a03d54096f0032502e6800f7801ef000a508ff203d5407aa803250239600f7801ef000a502e68014400288000d800a2000360006c0002408b60032b407aa8032501eaa00c9401ef000a5025bc00f780288000d800a2000360006c00024023dc00f7801ef000d8007bc00360006c00024007bc00360006c00024001b0000900012000060856202ddc06568028f01eaa00c9401ef000a501eaa00c9401ef000a500a2000360006c0002401d7e00c940192800a5007bc00360006c00024007bc00360006c00024001b00009000120000601c3e00a3c0192800a50064a00294006c000240064a00294006c00024001b000090001200006005fa002940052800240014a000900012000060014a000900012000060004800018000300001)
  | 6 => (21, 0xe65721156a8905120c2a2252cb832a5c1de22022272640903426c1f14602385092b680a7ac053d6005fd26409035e501af28024c007a9180af54057aa006430919080d104068820077701a20801ddc00eee00111252cb82e29c1af28024c006bca009300057aa0064307a9180a6cc068820077701a20801ddc00eee00111092b680d104068820096101a20802584012c20015701a20802584012c200157004b080055c002ae000312414482ad901756801f6406bca009300057aa0064306bca009300057aa0064301a20801ddc00eee0011107c5180af54057aa0077701a20802584012c20015701a20802584012c200157004b080055c002ae00031077888093c4057aa00777015ea801ddc012c200157015ea801ddc012c200157004b080055c002ae00031014f5801ddc00eee00157003bb80055c002ae00031003bb80055c002ae00031000ab8000c4000620000722ad5029104156c801ccb05c53807d90049e20054706bca009300057aa0064301a20801ddc00eee001110684d8093000498000643014d9801ddc00eee0011101a20802584012c200157004b080055c002ae000310654b807d9004980006430126000190c00eee00111015ea801ddc012c200157004b080055c002ae00031014f5801ddc00eee00157003bb80055c002ae00031003bb80055c002ae00031000ab8000c400062000070615100732c03ec8005470126000190c00eee001110126000190c00eee00111004b080055c002ae00031011c280190c00c8600111003bb80055c002ae00031003bb80055c002ae00031000ab8000c400062000070111380151c00c860011100321800444002ae0003100321800444002ae00031000ab8000c40006200007002fe8004440022200031000888000c40006200007000888000c400062000070001880001c0000e00001)
  | 7 => (23, 0xc088c03284f068c3301e3c41aea8407d708121a00048681ba068080d1012c20004b08056a00015a8002b50000ad41ba068084a501094a004d5404a22c01688002d10000b4405622001a40003480000d2000d200003480006900001a41aea840742f01094a004d5404252801355002d10000b4404a22c01593003480000d2000d200003480006900001a4056a0001a4000348000100000d2000040000080000020000d20000400000800000200002000000800001000000401a30cc06cdb00eaaa00439804252801355002d10000b4404252801355002d10000b4400d200003480006900001a404b08001688002d10000d2000d2000040000080000020000d200004000008000002000020000008000010000004004868001378002d10000d2000b4400034800080000020000b440003480008000002000020000008000010000004000ad4000348000690000200001a4000080000100000040001a400008000010000004000040000010000020000008194278068c100d9b6003eac03a178010e60026f00009bc04252801355002d10000b4400d200003480006900001a4040688013550026aa000b4400ac98003480006900001a400d200004000008000002000020000008000010000004003eb84010e60026aa000b44009aa8002d10006900001a400b440003480008000002000020000008000010000004000ad4000348000690000200001a4000080000100000040001a40000800001000000400004000001000002000000803c78800fab0021cc0009bc009aa8002d10006900001a4009aa8002d10006900001a400200000080000100000040009610002d10005a20001a4001a4000080000100000040001a4000080000100000040000400000100000200000080090d00026f0005a20001a40016880006900010000004000168800069000100000040000400000100000200000080015a8000690000d2000040000348000100000200000080003480001000002000000800008000002000004000001)
  | 8 => (25, 0x899fb207fed38421e84042b7c10f2ed0113ef809c9f0008b38115b99011ab400a1ca0008fd002deb20028d10014688001224115b9901224000912000093c0028071002a4b00152580012cc02db8800306900183480015840060d20005610002b0800026410f2ed01028400912000093c00244800024f000152580012cc0280710028b300183480015840060d20005610002b0800026402deb200306900183480019a10060d200066840033420002d90060d200066840033420002d9000cd08000b640005b20000511087a100f3ff00826800083640244800024f000152580012cc0244800024f000152580012cc0060d20005610002b08000264028728002a4b00152580015840060d200066840033420002d90060d200066840033420002d9000cd08000b640005b200005102727c00253b001525800158400549600056100033420002d900549600056100033420002d9000cd08000b640005b20000510051a20005610002b080002d9000ac20000b640005b2000051000ac20000b640005b200005100016c80001440000a20000090ffda700eba10079ff8007adc0205080020d900129d800108c0244800024f000152580012cc0060d20005610002b080002640235680024f000127800012cc0051660005610002b080002640060d200066840033420002d9000cd08000b640005b20000510227df0020d900127800012cc0049e00004b30002b0800026400549600056100033420002d9000cd08000b640005b20000510051a20005610002b080002d9000ac20000b640005b2000051000ac20000b640005b200005100016c80001440000a20000090215be001eb700106c800108c0049e00004b30002b080002640049e00004b30002b08000264000cd08000b640005b20000510047e80004b30002598000264000ac20000b640005b2000051000ac20000b640005b200005100016c80001440000a200000900459c000423000259800026400096600009900005b200005100096600009900005b200005100016c80001440000a200000900091200009900004c800005100013200001440000a200000900013200001440000a20000090000288000024000012000001)
  | 9 => (26, 0xae59ad848b16312bc6f408652f132c4a408a831026ca7800f843139908c08d9ff027f67800ffc302cc4f0011e860047a18001ca7139908c0910d7024435c010617027987c0127e60049f98001d9702c9e44014dfc00537f000216600537f00021660008598000357132c4a4082e15024435c010617024435c0106170049f98001d97027987c011de100537f000216600537f0002166000859800035702cc4f0014dfc00537f000271000537f00027100009c400003e800537f00027100009c400003e80009c400003e80000fa000006412bc6f407c425020fbd400ec31024435c0106170049f98001d97024435c0106170049f98001d9700537f00021660008598000357027f6780127e60049f9800216600537f00027100009c400003e800537f00027100009c400003e80009c400003e80000fa0000064026ca780108420049f980021660049f980021660009c400003e80049f980021660009c400003e80009c400003e80000fa00000640047a1800216600085980003e800085980003e80000fa000006400085980003e80000fa00000640000fa0000064000019000000a122c58c0785b501f109400de5d020b85400ec310042108001a6d024435c0106170049f98001d9700537f0002166000859800035702367fc010617004185c001d970047784002166000859800035700537f00027100009c400003e80009c400003e80000fa0000064022a0c400ec31004185c001d97004185c001d9700085980003570049f980021660009c400003e80009c400003e80000fa00000640047a1800216600085980003e800085980003e80000fa000006400085980003e80000fa00000640000fa0000064000019000000a02194bc00de5d003b0c4001a6d004185c001d970008598000357004185c001d9700085980003570009c400003e80000fa0000064003ff0c001d97000765c00035700085980003e80000fa000006400085980003e80000fa00000640000fa0000064000019000000a003e10c001a6d000765c000357000765c0003570000fa0000064000765c0003570000fa00000640000fa0000064000019000000a000729c0003570000d5c0000640000d5c000064000019000000a0000d5c000064000019000000a000019000000a0000028000001)
  | _ => (1, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def base_T : ∀ u : Fin 256, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_0 : ∀ u : Fin 256, u.val / 16 = 0 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_1 : ∀ u : Fin 256, u.val / 16 = 1 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_2 : ∀ u : Fin 256, u.val / 16 = 2 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_3 : ∀ u : Fin 256, u.val / 16 = 3 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_4 : ∀ u : Fin 256, u.val / 16 = 4 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_5 : ∀ u : Fin 256, u.val / 16 = 5 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_6 : ∀ u : Fin 256, u.val / 16 = 6 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_7 : ∀ u : Fin 256, u.val / 16 = 7 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_8 : ∀ u : Fin 256, u.val / 16 = 8 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_9 : ∀ u : Fin 256, u.val / 16 = 9 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_10 : ∀ u : Fin 256, u.val / 16 = 10 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_11 : ∀ u : Fin 256, u.val / 16 = 11 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_12 : ∀ u : Fin 256, u.val / 16 = 12 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_13 : ∀ u : Fin 256, u.val / 16 = 13 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_14 : ∀ u : Fin 256, u.val / 16 = 14 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_15 : ∀ u : Fin 256, u.val / 16 = 15 → ∀ n < (9 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

theorem step_all (n : ℕ) (hn : n < 9) (u : Fin 256) :
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  have hu := u.isLt
  obtain ⟨c, hc⟩ : ∃ c, u.val / 16 = c := ⟨_, rfl⟩
  have hc2 : c < 16 := by omega
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

theorem G_eq_T (n : ℕ) (hn : n ≤ 9) : ∀ u : Fin 256, G n u = tb (tabT n) u.val := by
  induction n with
  | zero => exact base_T
  | succ n ih =>
    intro u
    rw [G_succ]
    have ih' := ih (by omega)
    simp only [ih']
    exact step_all n (by omega) u

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def tab_base : ∀ u : Fin 256,
    tb (tabT 9) u.val + 36 * tb (tabT 7) u.val + 126 * tb (tabT 5) u.val + 84 * tb (tabT 3) u.val + 9 * tb (tabT 1) u.val =
      9 * tb (tabT 8) u.val + 84 * tb (tabT 6) u.val + 126 * tb (tabT 4) u.val + 36 * tb (tabT 2) u.val + tb (tabT 0) u.val := by
  decide +kernel

theorem G_base : ∀ u : Fin 256,
    G 9 u + 36 * G 7 u + 126 * G 5 u + 84 * G 3 u + 9 * G 1 u =
      9 * G 8 u + 84 * G 6 u + 126 * G 4 u + 36 * G 2 u + G 0 u := by
  intro u
  rw [G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 256,
    G (m + 9) u + 36 * G (m + 7) u + 126 * G (m + 5) u + 84 * G (m + 3) u + 9 * G (m + 1) u =
      9 * G (m + 8) u + 84 * G (m + 6) u + 126 * G (m + 4) u + 36 * G (m + 2) u + G m u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega]
    rw [G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 9) + 36 * a (m + 7) + 126 * a (m + 5) + 84 * a (m + 3) + 9 * a (m + 1) =
      9 * a (m + 8) + 84 * a (m + 6) + 126 * a (m + 4) + 36 * a (m + 2) + a m := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 255

theorem G_vals : G 1 255 = 6 ∧ G 2 255 = 514 ∧ G 3 255 = 9480 ∧ G 4 255 = 82398 ∧ G 5 255 = 457366 ∧ G 6 255 = 1886948 ∧ G 7 255 = 6308960 ∧ G 8 255 = 18038628 ∧ G 9 255 = 45704886 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 6 ∧ a 2 = 514 ∧ a 3 = 9480 ∧ a 4 = 82398 ∧ a 5 = 457366 ∧ a 6 = 1886948 ∧ a 7 = 6308960 ∧ a 8 = 18038628 ∧ a 9 = 45704886 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num

theorem recurrence (n : ℕ) (hn : 10 ≤ n) :
    (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 9) + 36 * a (m + 7) + 126 * a (m + 5) + 84 * a (m + 3) + 9 * a (m + 1) : ℤ) : ℚ) =
      ((9 * a (m + 8) + 84 * a (m + 6) + 126 * a (m + 4) + 36 * a (m + 2) + a m : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 9 - 1 = (m + 8) by omega, show m + 9 - 2 = (m + 7) by omega, show m + 9 - 3 = (m + 6) by omega, show m + 9 - 4 = (m + 5) by omega, show m + 9 - 5 = (m + 4) by omega, show m + 9 - 6 = (m + 3) by omega, show m + 9 - 7 = (m + 2) by omega, show m + 9 - 8 = (m + 1) by omega, show m + 9 - 9 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 9 : PowerSeries ℚ) =
      2 * X * (3 + 230 * X + 2535 * X ^ 2 + 7539 * X ^ 3 + 7322 * X ^ 4 + 2335 * X ^ 5 + 196 * X ^ 6) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 9 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 9 * (PowerSeries.mk F * X ^ 1) + C 36 * (PowerSeries.mk F * X ^ 2) - C 84 * (PowerSeries.mk F * X ^ 3) + C 126 * (PowerSeries.mk F * X ^ 4) - C 126 * (PowerSeries.mk F * X ^ 5) + C 84 * (PowerSeries.mk F * X ^ 6) - C 36 * (PowerSeries.mk F * X ^ 7) + C 9 * (PowerSeries.mk F * X ^ 8) - C 1 * (PowerSeries.mk F * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (3 + 230 * X + 2535 * X ^ 2 + 7539 * X ^ 3 + 7322 * X ^ 4 + 2335 * X ^ 5 + 196 * X ^ 6) : ℚ⟦X⟧) =
      C 6 * X ^ 1 + C 460 * X ^ 2 + C 5070 * X ^ 3 + C 15078 * X ^ 4 + C 14644 * X ^ 5 + C 4670 * X ^ 6 + C 392 * X ^ 7 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    have hr := recurrence (j + 10) (by omega)
    simp only [show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 10 by omega,
      show 1 ≤ j + 10 by omega,
      show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega,
      show 4 ≤ j + 10 by omega,
      show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega,
      show 7 ≤ j + 10 by omega,
      show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega,
      show j + 10 - 0 = j + 10 by omega,
      show j + 10 - 1 = j + 9 by omega,
      show j + 10 - 2 = j + 8 by omega,
      show j + 10 - 3 = j + 7 by omega,
      show j + 10 - 4 = j + 6 by omega,
      show j + 10 - 5 = j + 5 by omega,
      show j + 10 - 6 = j + 4 by omega,
      show j + 10 - 7 = j + 3 by omega,
      show j + 10 - 8 = j + 2 by omega,
      show j + 10 - 9 = j + 1 by omega,
      show ¬ (j + 10 = 1) by omega,
      show ¬ (j + 10 = 2) by omega,
      show ¬ (j + 10 = 3) by omega,
      show ¬ (j + 10 = 4) by omega,
      show ¬ (j + 10 = 5) by omega,
      show ¬ (j + 10 = 6) by omega,
      show ¬ (j + 10 = 7) by omega,
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

end OMA.A250391

theorem OMA.solution : type_of% @OMA.S_oeis_a250391.main :=
  ⟨OMA.A250391.gen_fun, OMA.A250391.recurrence⟩
