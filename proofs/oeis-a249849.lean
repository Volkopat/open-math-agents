import OMAStatements.S_oeis_a249849

/-!
A249849: exact nine-position/five-window adaptation of the threshold-chain proof
by @Salofe for A250064, PR #23285, commit bd4969a8ddc52c3bd7f8d30008570b9868fd00b6.
This uses the same counting infrastructure as our A250390 proof, PR #26510.
Conjecture: Colin Barker (2017); registered statement: @clementtrecourt, PR #19348.
The finite tables certify a recurrence on every subset state; linearity then proves
it for all levels. All computations are kernel checked.
-/

namespace OMA.A249849

open OMA.S_oeis_a249849 Finset

/-! ### The window condition -/

/-- The condition of the statement on 5 values (without the bound on `v`). -/
def Cy (y : Fin 5 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 5)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)

theorem cy_to (y : Fin 5 → ℕ) (h : Cy y) (w : ℕ) : (univ.filter (fun t => y t ≤ w)).card ≠ 2 := by
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

theorem cy_of (y : Fin 5 → ℕ) (h : ∀ w : ℕ, (univ.filter (fun t => y t ≤ w)).card ≠ 2) :
    Cy y := by
  set U := univ.filter (fun s => 2 ≤ (univ.filter (fun t => y t ≤ y s)).card) with hU
  have hUne : U.Nonempty := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image (univ : Finset (Fin 5)) y Finset.univ_nonempty
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

theorem window_iff (y : Fin 5 → ℕ) :
    Cy y ↔ ∀ v : ℕ, (univ.filter (fun t => y t ≤ v)).card ≠ 2 :=
  ⟨cy_to y, cy_of y⟩

/-! ### Negated window condition as a condition on consecutive strict threshold counts -/

theorem not_cy_iff (y : Fin 5 → ℕ) :
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
  (univ.filter (fun t : Fin 5 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 9 → Bool) : Prop := ∀ i < (5 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 9 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 9 → Fin (n + 1)) (v : ℕ) : Fin 9 → Bool :=
  fun p => decide ((x p : ℕ) < v)

theorem get_le {n : ℕ} (x : Fin 9 → Fin (n + 1)) (k : ℕ) : OMA.S_oeis_a249849.get x k ≤ n := by
  unfold OMA.S_oeis_a249849.get
  split_ifs
  · have := (x ⟨k, by assumption⟩).isLt
    omega
  · omega

theorem cnt_univ : ∀ i < (5 : ℕ), cntW (fun _ => true) i = 5 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 9 → Fin (n + 1)) :
    good x = true ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by
  have step1 : good x = true ↔
      ∀ i < (5 : ℕ), ¬ Cy (fun t : Fin 5 => OMA.S_oeis_a249849.get x (i + t)) := by
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
      (univ.filter (fun t : Fin 5 => OMA.S_oeis_a249849.get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 9 := by have := t.isLt; omega
    unfold OMA.S_oeis_a249849.get fget Lt
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

theorem cnt_row : ∀ u : Fin 512, cntW (row u) 0 = pcb (u.val &&& 31) ∧
    cntW (row u) 1 = pcb (u.val &&& 62) ∧
    cntW (row u) 2 = pcb (u.val &&& 124) ∧
    cntW (row u) 3 = pcb (u.val &&& 248) ∧
    cntW (row u) 4 = pcb (u.val &&& 496) := by
  decide +kernel

def compc (s t : ℕ) : Bool :=
  decide (¬ (pcb (s &&& 31) ≤ 1 ∧ 3 ≤ pcb (t &&& 31)) ∧
    ¬ (pcb (s &&& 62) ≤ 1 ∧ 3 ≤ pcb (t &&& 62)) ∧
    ¬ (pcb (s &&& 124) ≤ 1 ∧ 3 ≤ pcb (t &&& 124)) ∧
    ¬ (pcb (s &&& 248) ≤ 1 ∧ 3 ≤ pcb (t &&& 248)) ∧
    ¬ (pcb (s &&& 496) ≤ 1 ∧ 3 ≤ pcb (t &&& 496)))

theorem forall_lt_nw (P : ℕ → Prop) : (∀ i < (5 : ℕ), P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num)⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ i hi
    interval_cases i <;> assumption

theorem compc_iff (s t : Fin 512) : Comp (row s) (row t) ↔ compc s.val t.val = true := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := cnt_row s
  obtain ⟨b0, b1, b2, b3, b4⟩ := cnt_row t
  unfold Comp compc
  refine (forall_lt_nw _).trans ?_
  rw [decide_eq_true_iff, a0, a1, a2, a3, a4, b0, b1, b2, b3, b4]

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

/-! Packed tables certify the recursion on every state. -/
def tb (T w : ℕ) : ℕ := (T >>> (32 * w)) % 2 ^ 32

def tabT : ℕ → ℕ
  | 0 => 0x1000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000000000000000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000001000000000000000100000001000000010000000000000000000000000000000100000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000010000000100000001000000000000000000000000000000010000000000000001000000010000000100000000000000010000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000010000000000000000000000000000000000000000000000010000000100000001000000000000000100000001000000010000000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000000000000000000000000000000000000000000000000000010000000100000000000000000000000100000001000000010000000100000001000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000010000000000000001000000010000000100000000000000000000000000000001000000000000000100000001000000010000000000000001000000010000000100000001000000010000000100000001
  | 1 => 0xA0000000600000006000000030000000600000003000000030000000300000006000000030000000300000003000000030000000300000006000000030000000600000003000000030000000300000003000000030000000600000003000000030000000300000006000000030000000C000000060000000600000003000000060000000600000003000000030000000300000003000000030000000300000003000000030000000300000003000000050000000600000006000000030000000300000003000000030000000300000005000000060000000600000003000000090000000C0000000C000000060000000C00000006000000060000000300000006000000030000000600000003000000030000000100000003000000030000000300000001000000030000000300000003000000030000000600000003000000030000000100000003000000030000000300000003000000060000000300000005000000050000000C000000060000000C000000060000000600000003000000030000000300000003000000030000000300000003000000030000000300000005000000050000000500000006000000050000000600000006000000030000000C0000000C0000000C000000100000000C0000001000000010000000080000000C00000010000000100000000800000010000000080000000800000004000000060000000300000003000000010000000600000003000000030000000300000003000000010000000100000001000000030000000300000006000000030000000300000001000000010000000100000003000000030000000600000003000000030000000300000006000000030000000C00000006000000060000000300000003000000030000000100000001000000030000000300000003000000030000000300000003000000030000000300000005000000060000000600000003000000060000000600000006000000060000000C0000001000000010000000080000000C0000001000000010000000080000001000000008000000080000000400000003000000010000000300000001000000030000000100000003000000030000000300000001000000030000000300000003000000030000000600000003000000060000000200000006000000060000000600000006000000100000000800000006000000060000001000000008000000100000000800000008000000040000000600000006000000060000000600000006000000060000000600000008000000060000000600000006000000080000000600000008000000080000000400000006000000060000000600000008000000060000000800000008000000040000000600000008000000080000000400000008000000040000000400000002000000060000000300000003000000010000000300000001000000010000000100000006000000030000000300000003000000030000000300000006000000030000000300000001000000010000000100000001000000010000000200000001000000030000000300000006000000030000000C0000000600000006000000030000000300000003000000010000000100000001000000010000000100000001000000030000000300000003000000030000000500000006000000060000000300000003000000030000000300000003000000050000000600000006000000030000000C00000010000000100000000800000010000000080000000800000004000000030000000100000003000000010000000100000000000000010000000100000003000000010000000300000003000000030000000300000006000000030000000300000001000000030000000300000003000000030000000600000003000000060000000600000010000000080000001000000008000000080000000400000003000000030000000300000003000000030000000300000003000000030000000600000006000000060000000800000006000000080000000800000004000000060000000600000006000000080000000600000008000000080000000400000006000000080000000800000004000000080000000400000004000000020000000300000001000000010000000000000003000000010000000100000001000000030000000100000001000000010000000300000003000000060000000300000003000000010000000100000001000000030000000300000006000000030000000300000003000000060000000300000010000000080000000800000004000000030000000300000001000000010000000300000003000000030000000300000003000000030000000300000003000000060000000800000008000000040000000300000003000000030000000300000006000000080000000800000004000000060000000800000008000000040000000800000004000000040000000200000003000000010000000300000001000000030000000100000003000000030000000300000001000000030000000300000003000000030000000800000004000000030000000100000003000000030000000300000003000000080000000400000003000000030000000800000004000000080000000400000004000000020000000300000003000000030000000300000003000000030000000300000004000000030000000300000003000000040000000300000004000000040000000200000003000000030000000300000004000000030000000400000004000000020000000300000004000000040000000200000004000000020000000200000001
  | 2 => 0x4A5000001CE000001E4000000A3000001F8000000AF000000B40000005B00000209000000B6000000BF00000061000000C500000065000000990000003300000202000000B5000000BC00000060000000C2000000640000009900000033000000C7000000670000009F00000035000000F300000051000000510000001B0000020900000112000000B700000060000000BB000000640000006400000033000000BF0000006700000067000000350000008C00000051000000510000001B000000C70000006C0000006C000000380000009600000057000000570000001D000000E100000087000000870000002D000000870000002D0000002D0000000F000001F8000000C30000011200000060000000B90000003F0000006400000033000000BB0000004000000067000000350000006700000035000000510000001B000000C2000000430000006C000000380000006C00000038000000570000001D000000960000004D000000870000002D000000870000002D0000002D0000000F000000C50000006700000067000000380000006700000038000000380000001D0000008C0000004D0000004D0000002D0000004D0000002D0000002D0000000F000000F30000008700000087000000510000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B00000009000001E4000000B3000000C50000003F00000112000000600000006400000033000000B70000003800000042000000210000006700000035000000510000001B000000BC0000003A00000044000000220000006C00000038000000570000001D0000006C00000038000000570000001D000000870000002D0000002D0000000F000000BF0000006400000042000000220000006700000038000000380000001D0000006700000038000000380000001D0000004D0000002D0000002D0000000F0000009F00000057000000570000002D0000008700000051000000510000001B0000008700000051000000510000001B000000510000001B0000001B00000009000000B40000004200000064000000220000006400000022000000380000001D0000006400000022000000380000001D000000380000001D0000002D0000000F0000009900000033000000570000002D000000570000002D000000510000001B000000570000002D000000510000001B000000510000001B0000001B000000090000009900000051000000510000002D000000510000002D0000002D0000001B000000510000002D0000002D0000001B0000002D0000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000001CE000000A9000000B300000035000000C30000003E0000004200000021000001120000006000000064000000330000006700000035000000510000001B000000B5000000370000003A0000001D000000430000002200000033000000110000006C00000038000000570000001D000000870000002D0000002D0000000F000000B600000060000000380000001D000000400000002200000022000000110000006700000038000000380000001D0000004D0000002D0000002D0000000F0000006700000038000000380000001D0000004D0000002D0000002D0000000F0000008700000051000000510000001B000000510000001B0000001B00000009000000AF0000003E000000600000001D0000003F0000001400000022000000110000006400000022000000380000001D000000380000001D0000002D0000000F0000006400000022000000380000001D000000380000001D0000002D0000000F000000570000002D000000510000001B000000510000001B0000001B000000090000006500000035000000350000001D000000350000001D0000001D0000000F000000510000002D0000002D0000001B0000002D0000001B0000001B00000009000000510000002D0000002D0000001B0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B000000090000000900000003000000A3000000350000003F00000011000000600000001D0000002200000011000000600000001D0000002200000011000000380000001D0000002D0000000F000000600000001D0000002200000011000000380000001D0000002D0000000F000000380000001D0000002D0000000F000000510000001B0000001B0000000900000061000000330000002100000011000000350000001D0000001D0000000F000000350000001D0000001D0000000F0000002D0000001B0000001B00000009000000350000001D0000001D0000000F0000002D0000001B0000001B000000090000002D0000001B0000001B000000090000001B0000000900000009000000030000005B00000021000000330000001100000033000000110000001D0000000F00000033000000110000001D0000000F0000001D0000000F0000001B0000000900000033000000110000001D0000000F0000001D0000000F0000001B000000090000001D0000000F0000001B000000090000001B000000090000000900000003000000330000001B0000001B0000000F0000001B0000000F0000000F000000090000001B0000000F0000000F000000090000000F0000000900000009000000030000001B0000000F0000000F000000090000000F0000000900000009000000030000000F00000009000000090000000300000009000000030000000300000001
  | 3 => 0x758000002179000022FE000009000000244F00000996000009EE000003580000256E000009EE00000A730000038A00000AC2000003B0000004F80000013E00002508000009DA00000A550000038200000AB7000003AF000005000000014000000B16000003D2000005400000015000000720000001C8000001C8000000720000256E00000D3800000A0E0000038200000A4D000003AF000003AF0000014000000A9A000003D2000003D200000150000004C1000001C8000001C80000007200000B1600000402000004020000016200000515000001E8000001E80000007A000006E4000002A0000002A0000000A8000002A0000000A8000000A80000002A0000244F00000A8300000D380000038200000A22000002BF000003AF0000014000000A4D000002CD000003D200000150000003D200000150000001C80000007200000AB7000002EE00000402000001620000040200000162000001E80000007A00000515000001BE000002A0000000A8000002A0000000A8000000A80000002A00000AC2000003D2000003D200000162000003D200000162000001620000007A000004C1000001BE000001BE000000A8000001BE000000A8000000A80000002A00000720000002A0000002A000000100000002A0000001000000010000000040000002A000000100000001000000004000000100000000400000004000000010000022FE000009C200000A9E000002B100000D3800000382000003AF0000014000000A0E00000282000002E2000000F8000003D200000150000001C80000007200000A5500000296000002FA000001000000040200000162000001E80000007A0000040200000162000001E80000007A000002A0000000A8000000A80000002A00000A73000003AF000002E200000100000003D200000162000001620000007A000003D200000162000001620000007A000001BE000000A8000000A80000002A00000540000001E8000001E8000000A8000002A0000001000000010000000040000002A000000100000001000000004000000100000000400000004000000010000009EE000002D3000003AF00000100000003AF00000100000001620000007A000003AF00000100000001620000007A000001620000007A000000A80000002A0000050000000158000001E8000000A8000001E8000000A80000010000000040000001E8000000A8000001000000004000000100000000400000004000000010000004F8000001C8000001C8000000A8000001C8000000A8000000A800000040000001C8000000A8000000A800000040000000A8000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A8000000400000004000000010000000400000001000000010000000040000217900000942000009C20000025F00000A83000002AC000002D3000000F200000D3800000382000003AF00000140000003D200000150000001C800000072000009DA0000027200000296000000DE000002EE0000010000000158000000560000040200000162000001E80000007A000002A0000000A8000000A80000002A000009EE0000038200000282000000DE000002CD000001000000010000000056000003D200000162000001620000007A000001BE000000A8000000A80000002A000003D200000162000001620000007A000001BE000000A8000000A80000002A000002A00000010000000100000000400000010000000040000000400000001000000996000002AC00000382000000DE000002BF000000BA0000010000000056000003AF00000100000001620000007A000001620000007A000000A80000002A000003AF00000100000001620000007A000001620000007A000000A80000002A000001E8000000A8000001000000004000000100000000400000004000000010000003B000000150000001500000007A000001500000007A0000007A0000002A000001C8000000A8000000A800000040000000A8000000400000004000000010000001C8000000A8000000A800000040000000A8000000400000004000000010000000A800000040000000400000001000000040000000100000001000000004000009000000025F000002B1000000A200000382000000DE000001000000005600000382000000DE0000010000000056000001620000007A000000A80000002A00000382000000DE0000010000000056000001620000007A000000A80000002A000001620000007A000000A80000002A000001000000004000000040000000100000038A00000140000000F800000056000001500000007A0000007A0000002A000001500000007A0000007A0000002A000000A8000000400000004000000010000001500000007A0000007A0000002A000000A8000000400000004000000010000000A80000004000000040000000100000004000000010000000100000000400000358000000F2000001400000005600000140000000560000007A0000002A00000140000000560000007A0000002A0000007A0000002A000000400000001000000140000000560000007A0000002A0000007A0000002A00000040000000100000007A0000002A0000004000000010000000400000001000000010000000040000013E00000072000000720000002A000000720000002A0000002A00000010000000720000002A0000002A000000100000002A000000100000001000000004000000720000002A0000002A000000100000002A0000001000000010000000040000002A00000010000000100000000400000010000000040000000400000001
  | 4 => 0x525F4000126F70001328900003F7400013C58000042E70000454200001178000144A7000044EB000048460000125400004A350000130A00001806000004CE000141DE00004465000047AB0000123200004A3F0000131500001838000004D800004CCB000013C400001964000005140000203A00000672000006720000014A000144A7000055BE000045F700001232000047A20000131500001315000004D8000049BA000013C4000013C4000005140000176B00000672000006720000014A00004CCB000014A0000014A000000550000018D3000006D6000006D60000015E00001FA4000008CA000008CA000001C2000008CA000001C2000001C20000005A00013C580000482A000055BE000012320000467000000F6300001315000004D8000047A200000FB3000013C400000514000013C400000514000006720000014A00004A3F00001054000014A000000550000014A000000550000006D60000015E000018D30000065E000008CA000001C2000008CA000001C2000001C20000005A00004A35000013C4000013C400000550000013C400000550000005500000015E0000176B0000065E0000065E000001C20000065E000001C2000001C20000005A0000203A000008CA000008CA00000271000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D0000001900013289000043D4000048CC00000F01000055BE0000123200001315000004D8000045F700000E5A0000101800000410000013C400000514000006720000014A000047AB00000EBA000010900000042E000014A000000550000006D60000015E000014A000000550000006D60000015E000008CA000001C2000001C20000005A0000484600001315000010180000042E000013C400000550000005500000015E000013C400000550000005500000015E0000065E000001C2000001C20000005A00001964000006D6000006D6000001C2000008CA00000271000002710000007D000008CA00000271000002710000007D000002710000007D0000007D000000190000454200000FB3000013150000042E000013150000042E000005500000015E000013150000042E000005500000015E000005500000015E000001C20000005A0000183800000546000006D6000001C2000006D6000001C2000002710000007D000006D6000001C2000002710000007D000002710000007D0000007D00000019000018060000067200000672000001C200000672000001C2000001C20000007D00000672000001C2000001C20000007D000001C20000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D000000190000001900000005000126F7000040DC000043D400000D9B0000482A00000EF200000FB3000003F2000055BE0000123200001315000004D8000013C400000514000006720000014A0000446500000DFA00000EBA000003B6000010540000042E000005460000010E000014A000000550000006D60000015E000008CA000001C2000001C20000005A000044EB0000123200000E5A000003B600000FB30000042E0000042E0000010E000013C400000550000005500000015E0000065E000001C2000001C20000005A000013C400000550000005500000015E0000065E000001C2000001C20000005A000008CA00000271000002710000007D000002710000007D0000007D00000019000042E700000EF200001232000003B600000F63000003520000042E0000010E000013150000042E000005500000015E000005500000015E000001C20000005A000013150000042E000005500000015E000005500000015E000001C20000005A000006D6000001C2000002710000007D000002710000007D0000007D000000190000130A00000514000005140000015E000005140000015E0000015E0000005A00000672000001C2000001C20000007D000001C20000007D0000007D0000001900000672000001C2000001C20000007D000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D00000019000000190000000500003F7400000D9B00000F01000002F800001232000003B60000042E0000010E00001232000003B60000042E0000010E000005500000015E000001C20000005A00001232000003B60000042E0000010E000005500000015E000001C20000005A000005500000015E000001C20000005A000002710000007D0000007D0000001900001254000004D8000004100000010E000005140000015E0000015E0000005A000005140000015E0000015E0000005A000001C20000007D0000007D00000019000005140000015E0000015E0000005A000001C20000007D0000007D00000019000001C20000007D0000007D000000190000007D00000019000000190000000500001178000003F2000004D80000010E000004D80000010E0000015E0000005A000004D80000010E0000015E0000005A0000015E0000005A0000007D00000019000004D80000010E0000015E0000005A0000015E0000005A0000007D000000190000015E0000005A0000007D000000190000007D000000190000001900000005000004CE0000014A0000014A0000005A0000014A0000005A0000005A000000190000014A0000005A0000005A000000190000005A0000001900000019000000050000014A0000005A0000005A000000190000005A0000001900000019000000050000005A00000019000000190000000500000019000000050000000500000001
  | 5 => 0x23355A000679170006B130000127D30006E0170001356B00013F89000040670007079200013D5300014B4E0000431900015343000045730000540600000E010006FA9600013B230001491A000042B10001540C000045B0000054BA00000E1F00015EDB000047F90000587A00000EBF00006B94000011EE000011EE000002FD0007079200017A6200014247000042B10001496C000045B0000045B000000E1F00015265000047F9000047F900000EBF000052A8000011EE000011EE000002FD00015EDB00004AB500004AB500000F55000056F4000012DE000012DE0000032500006A590000173400001734000003DE00001734000003DE000003DE000000A50006E017000149A600017A62000042B10001443D00003ACE000045B000000E1F0001496C00003BF0000047F900000EBF000047F900000EBF000011EE000002FD0001540C00003E0300004AB500000F5500004AB500000F55000012DE00000325000056F4000011CB00001734000003DE00001734000003DE000003DE000000A500015343000047F9000047F900000F55000047F900000F5500000F5500000325000052A8000011CB000011CB000003DE000011CB000003DE000003DE000000A500006B94000017340000173400000510000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D8000000240006B130000138D900014C290000395400017A62000042B1000045B000000E1F000142470000379F00003D3B00000C5D000047F900000EBF000011EE000002FD0001491A000038DB00003ECB00000CAD00004AB500000F55000012DE0000032500004AB500000F55000012DE0000032500001734000003DE000003DE000000A500014B4E000045B000003D3B00000CAD000047F900000F5500000F5500000325000047F900000F5500000F5500000325000011CB000003DE000003DE000000A50000587A000012DE000012DE000003DE000017340000051000000510000000D8000017340000051000000510000000D800000510000000D8000000D80000002400013F8900003BBE000045B000000CAD000045B000000CAD00000F5500000325000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000054BA00000F5A000012DE000003DE000012DE000003DE00000510000000D8000012DE000003DE00000510000000D800000510000000D8000000D80000002400005406000011EE000011EE000003DE000011EE000003DE000003DE000000D8000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D80000002400000024000000060006791700012D19000138D9000034F6000149A60000393100003BBE00000C0300017A62000042B1000045B000000E1F000047F900000EBF000011EE000002FD00013B230000363B000038DB00000B7700003E0300000CAD00000F5A0000028F00004AB500000F55000012DE0000032500001734000003DE000003DE000000A500013D53000042B10000379F00000B7700003BF000000CAD00000CAD0000028F000047F900000F5500000F5500000325000011CB000003DE000003DE000000A5000047F900000F5500000F5500000325000011CB000003DE000003DE000000A5000017340000051000000510000000D800000510000000D8000000D8000000240001356B00003931000042B100000B7700003ACE00000A9600000CAD0000028F000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000045B000000CAD00000F550000032500000F5500000325000003DE000000A5000012DE000003DE00000510000000D800000510000000D8000000D8000000240000457300000EBF00000EBF0000032500000EBF0000032500000325000000A5000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000011EE000003DE000003DE000000D8000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D8000000240000002400000006000127D3000034F600003954000009A6000042B100000B7700000CAD0000028F000042B100000B7700000CAD0000028F00000F5500000325000003DE000000A5000042B100000B7700000CAD0000028F00000F5500000325000003DE000000A500000F5500000325000003DE000000A500000510000000D8000000D8000000240000431900000E1F00000C5D0000028F00000EBF0000032500000325000000A500000EBF0000032500000325000000A5000003DE000000D8000000D80000002400000EBF0000032500000325000000A5000003DE000000D8000000D800000024000003DE000000D8000000D800000024000000D80000002400000024000000060000406700000C0300000E1F0000028F00000E1F0000028F00000325000000A500000E1F0000028F00000325000000A500000325000000A5000000D80000002400000E1F0000028F00000325000000A500000325000000A5000000D80000002400000325000000A5000000D800000024000000D800000024000000240000000600000E01000002FD000002FD000000A5000002FD000000A5000000A500000024000002FD000000A5000000A500000024000000A5000000240000002400000006000002FD000000A5000000A500000024000000A5000000240000002400000006000000A500000024000000240000000600000024000000060000000600000001
  | 6 => 0xAD11DD001AF6C9001BC2E300041AE7001C6BD80004447E000465320000BCCF001CF94400045C95000488EF0000C3A50004A2020000C9D30000ED27000021E1001CCAE4000455AA000482890000C2A20004A5970000CA970000EF11000022270004C8120000D09B0000F8A3000023850001256D000029EB000029EB000005FD001CF94400050D7800046D820000C2A20004848F0000CA970000CA97000022270004A1610000D09B0000D09B000023850000EA79000029EB000029EB000005FD0004C8120000D7940000D794000024C00000F52300002BD500002BD5000006430001232100003441000034410000077700003441000007770000077700000111001C6BD80004814700050D780000C2A2000473C50000B0180000CA97000022270004848F0000B33D0000D09B000023850000D09B00002385000029EB000005FD0004A5970000B8A70000D794000024C00000D794000024C000002BD5000006430000F523000029B30000344100000777000034410000077700000777000001110004A2020000D09B0000D09B000024C00000D09B000024C0000024C0000006430000EA79000029B3000029B300000777000029B30000077700000777000001110001256D000034410000344100000961000034410000096100000961000001570000344100000961000009610000015700000961000001570000015700000031001BC2E300044E87000488FD0000ABE200050D780000C2A20000CA970000222700046D820000A82A0000B69A00001EB50000D09B00002385000029EB000005FD000482890000AB640000BAB400001F640000D794000024C000002BD5000006430000D794000024C000002BD50000064300003441000007770000077700000111000488EF0000CA970000B69A00001F640000D09B000024C0000024C0000006430000D09B000024C0000024C000000643000029B30000077700000777000001110000F8A300002BD500002BD500000777000034410000096100000961000001570000344100000961000009610000015700000961000001570000015700000031000465320000B26B0000CA9700001F640000CA9700001F64000024C0000006430000CA9700001F64000024C000000643000024C00000064300000777000001110000EF11000024F100002BD50000077700002BD500000777000009610000015700002BD5000007770000096100000157000009610000015700000157000000310000ED27000029EB000029EB00000777000029EB000007770000077700000157000029EB00000777000007770000015700000777000001570000015700000031000029EB000007770000077700000157000007770000015700000157000000310000077700000157000001570000003100000157000000310000003100000007001AF6C900042A7D00044E870000A0D6000481470000AB9C0000B26B00001DE300050D780000C2A20000CA97000022270000D09B00002385000029EB000005FD000455AA0000A4410000AB6400001CCB0000B8A700001F64000024F1000005470000D794000024C000002BD5000006430000344100000777000007770000011100045C950000C2A20000A82A00001CCB0000B33D00001F6400001F64000005470000D09B000024C0000024C000000643000029B30000077700000777000001110000D09B000024C0000024C000000643000029B300000777000007770000011100003441000009610000096100000157000009610000015700000157000000310004447E0000AB9C0000C2A200001CCB0000B01800001B1200001F64000005470000CA9700001F64000024C000000643000024C00000064300000777000001110000CA9700001F64000024C000000643000024C000000643000007770000011100002BD5000007770000096100000157000009610000015700000157000000310000C9D300002385000023850000064300002385000006430000064300000111000029EB00000777000007770000015700000777000001570000015700000031000029EB00000777000007770000015700000777000001570000015700000031000007770000015700000157000000310000015700000031000000310000000700041AE70000A0D60000ABE2000019050000C2A200001CCB00001F64000005470000C2A200001CCB00001F6400000547000024C00000064300000777000001110000C2A200001CCB00001F6400000547000024C0000006430000077700000111000024C0000006430000077700000111000009610000015700000157000000310000C3A50000222700001EB500000547000023850000064300000643000001110000238500000643000006430000011100000777000001570000015700000031000023850000064300000643000001110000077700000157000001570000003100000777000001570000015700000031000001570000003100000031000000070000BCCF00001DE3000022270000054700002227000005470000064300000111000022270000054700000643000001110000064300000111000001570000003100002227000005470000064300000111000006430000011100000157000000310000064300000111000001570000003100000157000000310000003100000007000021E1000005FD000005FD00000111000005FD000001110000011100000031000005FD00000111000001110000003100000111000000310000003100000007000005FD000001110000011100000031000001110000003100000031000000070000011100000031000000310000000700000031000000070000000700000001
  | 7 => 0x2A08AF0005AD89E005D3914000C0AD8005F2CFA000C75B4000CCCFC0001D6F80060CD6C000CB364000D28420001E5F4000D6A0C0001F3D800023EE0000047DC00604460000CA13C000D18660001E3C4000D75420001F5C20002434000004868000DD034000203440002584000004B080002B500000056A0000056A000000AD40060CD6C000E6890000CE2340001E3C4000D1F9E0001F5C20001F5C200004868000D6C04000203440002034400004B0800023A1E000056A0000056A000000AD4000DD034000212940002129400004D540002511600005A2000005A2000000B440002B110000069000000690000000D200000690000000D2000000D20000001A4005F2CFA000D0FC2000E68900001E3C4000CF2D40001BD520001F5C200004868000D1F9E0001C4A60002034400004B080002034400004B08000056A000000AD4000D75420001D0BC0002129400004D540002129400004D5400005A2000000B44000251160000564C0000690000000D200000690000000D2000000D20000001A4000D6A0C000203440002034400004D540002034400004D5400004D5400000B4400023A1E0000564C0000564C00000D200000564C00000D2000000D20000001A40002B500000069000000690000001000000069000000100000001000000002000000690000001000000010000000020000001000000002000000020000000040005D3914000C8EA4000D239C0001B35E000E68900001E3C40001F5C200004868000CE2340001AC340001CC24000042480002034400004B08000056A000000AD4000D18660001B36C0001D554000043980002129400004D5400005A2000000B440002129400004D5400005A2000000B440000690000000D2000000D20000001A4000D28420001F5C20001CC24000043980002034400004D5400004D5400000B440002034400004D5400004D5400000B440000564C00000D2000000D20000001A40002584000005A2000005A2000000D20000069000000100000001000000002000000690000001000000010000000020000001000000002000000020000000040000CCCFC0001C25A0001F5C2000043980001F5C20000439800004D5400000B440001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A40002434000004DE000005A2000000D2000005A2000000D20000010000000020000005A2000000D2000001000000002000000100000000200000002000000004000023EE0000056A0000056A000000D20000056A000000D2000000D2000000200000056A000000D2000000D200000020000000D20000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D2000000200000002000000004000000200000000400000004000000008005AD89E000C31E4000C8EA400019B32000D0FC20001B2E00001C25A000040A4000E68900001E3C40001F5C2000048680002034400004B08000056A000000AD4000CA13C0001A3040001B36C00003EAC0001D0BC0000439800004DE0000009BC0002129400004D5400005A2000000B440000690000000D2000000D20000001A4000CB3640001E3C40001AC3400003EAC0001C4A60000439800004398000009BC0002034400004D5400004D5400000B440000564C00000D2000000D20000001A40002034400004D5400004D5400000B440000564C00000D2000000D20000001A40000690000001000000010000000020000001000000002000000020000000040000C75B40001B2E00001E3C400003EAC0001BD5200003B9C00004398000009BC0001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A40001F5C20000439800004D5400000B4400004D5400000B4400000D20000001A400005A2000000D200000100000000200000010000000020000000200000000400001F3D800004B0800004B0800000B4400004B0800000B4400000B44000001A4000056A000000D2000000D200000020000000D20000002000000020000000040000056A000000D2000000D200000020000000D2000000200000002000000004000000D2000000200000002000000004000000200000000400000004000000008000C0AD800019B320001B35E000037AC0001E3C400003EAC00004398000009BC0001E3C400003EAC00004398000009BC00004D5400000B4400000D20000001A40001E3C400003EAC00004398000009BC00004D5400000B4400000D20000001A400004D5400000B4400000D20000001A4000010000000020000000200000000400001E5F40000486800004248000009BC00004B0800000B4400000B44000001A400004B0800000B4400000B44000001A400000D2000000200000002000000004000004B0800000B4400000B44000001A400000D2000000200000002000000004000000D20000002000000020000000040000002000000004000000040000000080001D6F8000040A400004868000009BC00004868000009BC00000B44000001A400004868000009BC00000B44000001A400000B44000001A4000002000000004000004868000009BC00000B44000001A400000B44000001A4000002000000004000000B44000001A4000002000000004000000200000000400000004000000008000047DC00000AD400000AD4000001A400000AD4000001A4000001A40000004000000AD4000001A4000001A400000040000001A400000040000000400000000800000AD4000001A4000001A400000040000001A4000000400000004000000008000001A400000040000000400000000800000040000000080000000800000001
  | 8 => 0x8910C9001055A12010B7926001EA83001107900001F99DA002064CC0004123801149EFA002024FA0021323400042FC00021C94E00044BA40004DC1C00008A3C01133F64001FFB4E00210F4200042B7C0021E5DA00044FBE0004E4F800008B380022B73200046AD000050E5000008FD00005BD640000A3440000A3440000122401149EFA0023E5540020948A00042B7C0021231C00044FBE00044FBE00008B380021D3A400046AD000046AD000008FD00004D4420000A3440000A344000012240022B7320004890000048900000093C0000500E20000A92C0000A92C000012CC0005B7100000C1A40000C1A4000015840000C1A4000015840000158400000264011079000020F28C0023E55400042B7C0020BB180003E2DA00044FBE00008B380021231C0003F1F200046AD000008FD000046AD000008FD00000A344000012240021E5DA00040A1000048900000093C000048900000093C00000A92C000012CC000500E20000A2CC0000C1A4000015840000C1A40000158400001584000002640021C94E00046AD000046AD0000093C000046AD0000093C0000093C0000012CC0004D4420000A2CC0000A2CC000015840000A2CC0000158400001584000002640005BD640000C1A40000C1A4000019A10000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D900000051010B7926001FD0D000211F800003CE2E0023E55400042B7C00044FBE00008B380020948A0003C18C000400E00000811800046AD000008FD00000A3440000122400210F420003CFFC000413400000836400048900000093C00000A92C000012CC00048900000093C00000A92C000012CC0000C1A40000158400001584000002640021323400044FBE000400E00000836400046AD0000093C0000093C0000012CC00046AD0000093C0000093C0000012CC0000A2CC00001584000015840000026400050E500000A92C0000A92C000015840000C1A4000019A1000019A1000002D90000C1A4000019A1000019A1000002D9000019A1000002D9000002D900000051002064CC0003ECB200044FBE0000836400044FBE00008364000093C0000012CC00044FBE00008364000093C0000012CC000093C0000012CC00001584000002640004E4F8000094EC0000A92C000015840000A92C00001584000019A1000002D90000A92C00001584000019A1000002D9000019A1000002D9000002D9000000510004DC1C0000A3440000A344000015840000A3440000158400001584000002D90000A3440000158400001584000002D900001584000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D900000051000000510000000901055A12001EFED0001FD0D000039E9A0020F28C0003CD5C0003ECB200007E240023E55400042B7C00044FBE00008B3800046AD000008FD00000A34400001224001FFB4E0003AE840003CFFC00007ADC00040A1000008364000094EC0000108C00048900000093C00000A92C000012CC0000C1A4000015840000158400000264002024FA00042B7C0003C18C00007ADC0003F1F200008364000083640000108C00046AD0000093C0000093C0000012CC0000A2CC00001584000015840000026400046AD0000093C0000093C0000012CC0000A2CC0000158400001584000002640000C1A4000019A1000019A1000002D9000019A1000002D9000002D900000051001F99DA0003CD5C00042B7C00007ADC0003E2DA000075CC000083640000108C00044FBE00008364000093C0000012CC000093C0000012CC000015840000026400044FBE00008364000093C0000012CC000093C0000012CC00001584000002640000A92C00001584000019A1000002D9000019A1000002D9000002D90000005100044BA400008FD000008FD0000012CC00008FD0000012CC000012CC000002640000A3440000158400001584000002D900001584000002D9000002D9000000510000A3440000158400001584000002D900001584000002D9000002D90000005100001584000002D9000002D900000051000002D9000000510000005100000009001EA83000039E9A0003CE2E00006EE800042B7C00007ADC000083640000108C00042B7C00007ADC000083640000108C000093C0000012CC000015840000026400042B7C00007ADC000083640000108C000093C0000012CC0000158400000264000093C0000012CC0000158400000264000019A1000002D9000002D90000005100042FC000008B38000081180000108C00008FD0000012CC000012CC0000026400008FD0000012CC000012CC0000026400001584000002D9000002D90000005100008FD0000012CC000012CC0000026400001584000002D9000002D90000005100001584000002D9000002D900000051000002D90000005100000051000000090004123800007E2400008B380000108C00008B380000108C000012CC0000026400008B380000108C000012CC00000264000012CC00000264000002D90000005100008B380000108C000012CC00000264000012CC00000264000002D900000051000012CC00000264000002D900000051000002D900000051000000510000000900008A3C00001224000012240000026400001224000002640000026400000051000012240000026400000264000000510000026400000051000000510000000900001224000002640000026400000051000002640000005100000051000000090000026400000051000000510000000900000051000000090000000900000001
  | 9 => 0x1863D1FA029987AC02A7A0520045FB2B02B315740047EB030049944F0008373302BC8F36004907D3004B380D00086CDF004C71C30008A04B0009A2360000F69F02B966B60048B163004AF1BD0008652F004CB1290008A8310009B29E0000F843004E64230008D9FF0009FD9E0000FFC3000B313C00011E8600011E8600001CA702BC8F3600508E4E0049F5DB0008652F004B20310008A8310008A8310000F843004C90170008D9FF0008D9FF0000FFC3000995F700011E8600011E8600001CA7004E6423000910D7000910D7000106170009E61F000127E6000127E600001D97000B279100014DFC00014DFC0000216600014DFC00002166000021660000035702B31574004AA83D00508E4E0008652F004A46870007E57F0008A8310000F843004B2031000801DB0008D9FF0000FFC30008D9FF0000FFC300011E8600001CA7004CB12900082E15000910D700010617000910D700010617000127E600001D970009E61F00011DE100014DFC0000216600014DFC000021660000216600000357004C71C30008D9FF0008D9FF000106170008D9FF000106170001061700001D97000995F700011DE100011DE10000216600011DE1000021660000216600000357000B313C00014DFC00014DFC0000271000014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E80000006402A7A0520048597F004B048F0007BE7300508E4E0008652F0008A8310000F8430049F5DB0007A99D00081D350000E8710008D9FF0000FFC300011E8600001CA7004AF1BD0007C42500083EF50000EC31000910D700010617000127E600001D97000910D700010617000127E600001D9700014DFC000021660000216600000357004B380D0008A83100081D350000EC310008D9FF000106170001061700001D970008D9FF000106170001061700001D9700011DE10000216600002166000003570009FD9E000127E6000127E60000216600014DFC0000271000002710000003E800014DFC0000271000002710000003E800002710000003E8000003E8000000640049944F0007F74F0008A8310000EC310008A8310000EC310001061700001D970008A8310000EC310001061700001D970001061700001D9700002166000003570009B29E00010842000127E600002166000127E60000216600002710000003E8000127E60000216600002710000003E800002710000003E8000003E8000000640009A23600011E8600011E860000216600011E860000216600002166000003E800011E860000216600002166000003E800002166000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A029987AC0046AA3F0048597F0007680F004AA83D0007BD290007F74F0000E38500508E4E0008652F0008A8310000F8430008D9FF0000FFC300011E8600001CA70048B163000785B50007C4250000DE5D00082E150000EC310001084200001A6D000910D700010617000127E600001D9700014DFC000021660000216600000357004907D30008652F0007A99D0000DE5D000801DB0000EC310000EC3100001A6D0008D9FF000106170001061700001D9700011DE10000216600002166000003570008D9FF000106170001061700001D9700011DE100002166000021660000035700014DFC0000271000002710000003E800002710000003E8000003E8000000640047EB030007BD290008652F0000DE5D0007E57F0000D6740000EC3100001A6D0008A8310000EC310001061700001D970001061700001D9700002166000003570008A8310000EC310001061700001D970001061700001D970000216600000357000127E60000216600002710000003E800002710000003E8000003E8000000640008A04B0000FFC30000FFC300001D970000FFC300001D9700001D970000035700011E860000216600002166000003E800002166000003E8000003E80000006400011E860000216600002166000003E800002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A0045FB2B0007680F0007BE730000CB340008652F0000DE5D0000EC3100001A6D0008652F0000DE5D0000EC3100001A6D0001061700001D9700002166000003570008652F0000DE5D0000EC3100001A6D0001061700001D9700002166000003570001061700001D97000021660000035700002710000003E8000003E80000006400086CDF0000F8430000E87100001A6D0000FFC300001D9700001D97000003570000FFC300001D9700001D970000035700002166000003E8000003E8000000640000FFC300001D9700001D970000035700002166000003E8000003E80000006400002166000003E8000003E800000064000003E800000064000000640000000A000837330000E3850000F84300001A6D0000F84300001A6D00001D97000003570000F84300001A6D00001D970000035700001D9700000357000003E8000000640000F84300001A6D00001D970000035700001D9700000357000003E80000006400001D9700000357000003E800000064000003E800000064000000640000000A0000F69F00001CA700001CA70000035700001CA700000357000003570000006400001CA70000035700000357000000640000035700000064000000640000000A00001CA70000035700000357000000640000035700000064000000640000000A0000035700000064000000640000000A000000640000000A0000000A00000001
  | 10 => 0x3E551D7D06022C80061FE3C6009285030637F2A80096335100996918000F68EB064BC9F300984F90009C840F000FC471009EDDCB00101D210011CEC500019E6F064521AE0097A9EB009C0072000FB76C009F5D4800102B2E0011EB210001A10300A29FB1001080E700126ABF0001AC9D001469370001DB050001DB0500002B2F064BC9F300A65B46009A21D1000FB76C009C618300102B2E00102B2E0001A103009F24F3001080E7001080E70001AC9D0011BC820001DB050001DB0500002B2F00A29FB10010DE5C0010DE5C0001B648001243DC0001E9330001E93300002C7900145B09000221EB000221EB000031A1000221EB000031A1000031A1000004830637F2A8009B5EAB00A65B46000FB76C009ABD89000EE37500102B2E0001A103009C6183000F1516001080E70001AC9D001080E70001AC9D0001DB0500002B2F009F5D48000F61030010DE5C0001B6480010DE5C0001B6480001E93300002C79001243DC0001DA29000221EB000031A1000221EB000031A1000031A100000483009EDDCB001080E7001080E70001B648001080E70001B6480001B64800002C790011BC820001DA290001DA29000031A10001DA29000031A1000031A10000048300146937000221EB000221EB00003931000221EB000039310000393100000533000221EB00003931000039310000053300003931000005330000053300000079061FE3C6009701D3009C0E3D000E9EE100A65B46000FB76C00102B2E0001A103009A21D1000E7E44000F440200018961001080E70001AC9D0001DB0500002B2F009C0072000EABE6000F7E0400018F2E0010DE5C0001B6480001E93300002C790010DE5C0001B6480001E93300002C79000221EB000031A1000031A100000483009C840F00102B2E000F440200018F2E001080E70001B6480001B64800002C79001080E70001B6480001B64800002C790001DA29000031A1000031A10000048300126ABF0001E9330001E933000031A1000221EB000039310000393100000533000221EB0000393100003931000005330000393100000533000005330000007900996918000F01C000102B2E00018F2E00102B2E00018F2E0001B64800002C7900102B2E00018F2E0001B64800002C790001B64800002C79000031A1000004830011EB210001B9EF0001E933000031A10001E933000031A100003931000005330001E933000031A10000393100000533000039310000053300000533000000790011CEC50001DB050001DB05000031A10001DB05000031A1000031A1000005330001DB05000031A1000031A100000533000031A10000053300000533000000790001DB05000031A1000031A100000533000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B06022C800093CDB9009701D3000E0BAB009B5EAB000E9CF2000F01C0000181A500A65B46000FB76C00102B2E0001A103001080E70001AC9D0001DB0500002B2F0097A9EB000E3F3B000EABE6000179E9000F610300018F2E0001B9EF0000282D0010DE5C0001B6480001E93300002C79000221EB000031A1000031A10000048300984F90000FB76C000E7E44000179E9000F151600018F2E00018F2E0000282D001080E70001B6480001B64800002C790001DA29000031A1000031A100000483001080E70001B6480001B64800002C790001DA29000031A1000031A100000483000221EB0000393100003931000005330000393100000533000005330000007900963351000E9CF2000FB76C000179E9000EE37500016E1800018F2E0000282D00102B2E00018F2E0001B64800002C790001B64800002C79000031A10000048300102B2E00018F2E0001B64800002C790001B64800002C79000031A1000004830001E933000031A100003931000005330000393100000533000005330000007900101D210001AC9D0001AC9D00002C790001AC9D00002C7900002C79000004830001DB05000031A1000031A100000533000031A10000053300000533000000790001DB05000031A1000031A100000533000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B00928503000E0BAB000E9EE100015CB1000FB76C000179E900018F2E0000282D000FB76C000179E900018F2E0000282D0001B64800002C79000031A100000483000FB76C000179E900018F2E0000282D0001B64800002C79000031A1000004830001B64800002C79000031A10000048300003931000005330000053300000079000FC4710001A103000189610000282D0001AC9D00002C7900002C79000004830001AC9D00002C7900002C7900000483000031A10000053300000533000000790001AC9D00002C7900002C7900000483000031A1000005330000053300000079000031A10000053300000533000000790000053300000079000000790000000B000F68EB000181A50001A1030000282D0001A1030000282D00002C79000004830001A1030000282D00002C790000048300002C790000048300000533000000790001A1030000282D00002C790000048300002C7900000483000005330000007900002C790000048300000533000000790000053300000079000000790000000B00019E6F00002B2F00002B2F0000048300002B2F00000483000004830000007900002B2F0000048300000483000000790000048300000079000000790000000B00002B2F0000048300000483000000790000048300000079000000790000000B0000048300000079000000790000000B000000790000000B0000000B00000001
  | _ => 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def base_T : ∀ u : Fin 512, G 0 u = tb (tabT 0) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_0 : ∀ u : Fin 512, u.val / 16 = 0 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_1 : ∀ u : Fin 512, u.val / 16 = 1 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_2 : ∀ u : Fin 512, u.val / 16 = 2 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_3 : ∀ u : Fin 512, u.val / 16 = 3 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_4 : ∀ u : Fin 512, u.val / 16 = 4 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_5 : ∀ u : Fin 512, u.val / 16 = 5 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_6 : ∀ u : Fin 512, u.val / 16 = 6 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_7 : ∀ u : Fin 512, u.val / 16 = 7 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_8 : ∀ u : Fin 512, u.val / 16 = 8 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_9 : ∀ u : Fin 512, u.val / 16 = 9 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_10 : ∀ u : Fin 512, u.val / 16 = 10 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_11 : ∀ u : Fin 512, u.val / 16 = 11 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_12 : ∀ u : Fin 512, u.val / 16 = 12 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_13 : ∀ u : Fin 512, u.val / 16 = 13 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_14 : ∀ u : Fin 512, u.val / 16 = 14 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_15 : ∀ u : Fin 512, u.val / 16 = 15 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_16 : ∀ u : Fin 512, u.val / 16 = 16 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_17 : ∀ u : Fin 512, u.val / 16 = 17 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_18 : ∀ u : Fin 512, u.val / 16 = 18 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_19 : ∀ u : Fin 512, u.val / 16 = 19 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_20 : ∀ u : Fin 512, u.val / 16 = 20 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_21 : ∀ u : Fin 512, u.val / 16 = 21 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_22 : ∀ u : Fin 512, u.val / 16 = 22 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_23 : ∀ u : Fin 512, u.val / 16 = 23 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_24 : ∀ u : Fin 512, u.val / 16 = 24 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_25 : ∀ u : Fin 512, u.val / 16 = 25 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_26 : ∀ u : Fin 512, u.val / 16 = 26 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_27 : ∀ u : Fin 512, u.val / 16 = 27 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_28 : ∀ u : Fin 512, u.val / 16 = 28 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_29 : ∀ u : Fin 512, u.val / 16 = 29 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_30 : ∀ u : Fin 512, u.val / 16 = 30 → ∀ n < (10 : ℕ),
    (∑ w ∈ subs u, if compc w.val u.val = true then tb (tabT n) w.val else 0) =
      tb (tabT (n + 1)) u.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def chunk_31 : ∀ u : Fin 512, u.val / 16 = 31 → ∀ n < (10 : ℕ),
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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def tab_base : ∀ u : Fin 512,
    tb (tabT 10) u.val + 45 * tb (tabT 8) u.val + 210 * tb (tabT 6) u.val + 210 * tb (tabT 4) u.val + 45 * tb (tabT 2) u.val + tb (tabT 0) u.val =
      10 * tb (tabT 9) u.val + 120 * tb (tabT 7) u.val + 252 * tb (tabT 5) u.val + 120 * tb (tabT 3) u.val + 10 * tb (tabT 1) u.val := by
  decide +kernel

theorem G_base : ∀ u : Fin 512,
    G 10 u + 45 * G 8 u + 210 * G 6 u + 210 * G 4 u + 45 * G 2 u + G 0 u =
      10 * G 9 u + 120 * G 7 u + 252 * G 5 u + 120 * G 3 u + 10 * G 1 u := by
  intro u
  rw [G_eq_T 10 (by norm_num) u, G_eq_T 9 (by norm_num) u, G_eq_T 8 (by norm_num) u, G_eq_T 7 (by norm_num) u, G_eq_T 6 (by norm_num) u, G_eq_T 5 (by norm_num) u, G_eq_T 4 (by norm_num) u, G_eq_T 3 (by norm_num) u, G_eq_T 2 (by norm_num) u, G_eq_T 1 (by norm_num) u, G_eq_T 0 (by norm_num) u]
  exact tab_base u

theorem G_rec (m : ℕ) : ∀ u : Fin 512,
    G (m + 10) u + 45 * G (m + 8) u + 210 * G (m + 6) u + 210 * G (m + 4) u + 45 * G (m + 2) u + G m u =
      10 * G (m + 9) u + 120 * G (m + 7) u + 252 * G (m + 5) u + 120 * G (m + 3) u + 10 * G (m + 1) u := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 3 = (m + 3) + 1 by omega, show m + 1 + 4 = (m + 4) + 1 by omega, show m + 1 + 5 = (m + 5) + 1 by omega, show m + 1 + 6 = (m + 6) + 1 by omega, show m + 1 + 7 = (m + 7) + 1 by omega, show m + 1 + 8 = (m + 8) + 1 by omega, show m + 1 + 9 = (m + 9) + 1 by omega, show m + 1 + 10 = (m + 10) + 1 by omega]
    rw [G_succ (m + 10), G_succ (m + 8), G_succ (m + 6), G_succ (m + 4), G_succ (m + 2), G_succ m, G_succ (m + 9), G_succ (m + 7), G_succ (m + 5), G_succ (m + 3), G_succ (m + 1)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem a_rec (m : ℕ) :
    a (m + 10) + 45 * a (m + 8) + 210 * a (m + 6) + 210 * a (m + 4) + 45 * a (m + 2) + a m =
      10 * a (m + 9) + 120 * a (m + 7) + 252 * a (m + 5) + 120 * a (m + 3) + 10 * a (m + 1) := by
  simp only [a_eq_G]
  exact_mod_cast G_rec m 511

theorem G_vals : G 1 511 = 10 ∧ G 2 511 = 1189 ∧ G 3 511 = 30080 ∧ G 4 511 = 337396 ∧ G 5 511 = 2307418 ∧ G 6 511 = 11342301 ∧ G 7 511 = 44075760 ∧ G 8 511 = 143723664 ∧ G 9 511 = 409195002 ∧ G 10 511 = 1045765501 := by
  rw [G_eq_T 1 (by norm_num), G_eq_T 2 (by norm_num), G_eq_T 3 (by norm_num), G_eq_T 4 (by norm_num), G_eq_T 5 (by norm_num), G_eq_T 6 (by norm_num), G_eq_T 7 (by norm_num), G_eq_T 8 (by norm_num), G_eq_T 9 (by norm_num), G_eq_T 10 (by norm_num)]
  decide +kernel

theorem a_vals : a 1 = 10 ∧ a 2 = 1189 ∧ a 3 = 30080 ∧ a 4 = 337396 ∧ a 5 = 2307418 ∧ a 6 = 11342301 ∧ a 7 = 44075760 ∧ a 8 = 143723664 ∧ a 9 = 409195002 ∧ a 10 = 1045765501 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := G_vals
  simp only [a_eq_G, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  norm_num

theorem recurrence (n : ℕ) (hn : 11 ≤ n) :
    (a n : ℚ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have h := a_rec m
  have hq : ((a (m + 10) + 45 * a (m + 8) + 210 * a (m + 6) + 210 * a (m + 4) + 45 * a (m + 2) + a m : ℤ) : ℚ) =
      ((10 * a (m + 9) + 120 * a (m + 7) + 252 * a (m + 5) + 120 * a (m + 3) + 10 * a (m + 1) : ℤ) : ℚ) := by
    rw [h]
  push_cast at hq
  rw [show m + 10 - 1 = (m + 9) by omega, show m + 10 - 2 = (m + 8) by omega, show m + 10 - 3 = (m + 7) by omega, show m + 10 - 4 = (m + 6) by omega, show m + 10 - 5 = (m + 5) by omega, show m + 10 - 6 = (m + 4) by omega, show m + 10 - 7 = (m + 3) by omega, show m + 10 - 8 = (m + 2) by omega, show m + 10 - 9 = (m + 1) by omega, show m + 10 - 10 = m by omega]
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 10 : PowerSeries ℚ) =
      X * (10 + 1089 * X + 18640 * X ^ 2 + 88901 * X ^ 3 + 146478 * X ^ 4 + 88511 * X ^ 5 + 18312 * X ^ 6 + 939 * X ^ 7) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10⟩ := a_vals
  have key : PowerSeries.mk F * (1 - X) ^ 10 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 10 * (PowerSeries.mk F * X ^ 1) + C 45 * (PowerSeries.mk F * X ^ 2) - C 120 * (PowerSeries.mk F * X ^ 3) + C 210 * (PowerSeries.mk F * X ^ 4) - C 252 * (PowerSeries.mk F * X ^ 5) + C 210 * (PowerSeries.mk F * X ^ 6) - C 120 * (PowerSeries.mk F * X ^ 7) + C 45 * (PowerSeries.mk F * X ^ 8) - C 10 * (PowerSeries.mk F * X ^ 9) + C 1 * (PowerSeries.mk F * X ^ 10) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X * (10 + 1089 * X + 18640 * X ^ 2 + 88901 * X ^ 3 + 146478 * X ^ 4 + 88511 * X ^ 5 + 18312 * X ^ 6 + 939 * X ^ 7) : ℚ⟦X⟧) =
      C 10 * X ^ 1 + C 1089 * X ^ 2 + C 18640 * X ^ 3 + C 88901 * X ^ 4 + C 146478 * X ^ 5 + C 88511 * X ^ 6 + C 18312 * X ^ 7 + C 939 * X ^ 8 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 11
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 11 := ⟨k - 11, by omega⟩
    have hr := recurrence (j + 11) (by omega)
    simp only [show j + 11 - 1 = j + 10 by omega, show j + 11 - 2 = j + 9 by omega, show j + 11 - 3 = j + 8 by omega, show j + 11 - 4 = j + 7 by omega, show j + 11 - 5 = j + 6 by omega, show j + 11 - 6 = j + 5 by omega, show j + 11 - 7 = j + 4 by omega, show j + 11 - 8 = j + 3 by omega, show j + 11 - 9 = j + 2 by omega, show j + 11 - 10 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 11 by omega,
      show 1 ≤ j + 11 by omega,
      show 2 ≤ j + 11 by omega,
      show 3 ≤ j + 11 by omega,
      show 4 ≤ j + 11 by omega,
      show 5 ≤ j + 11 by omega,
      show 6 ≤ j + 11 by omega,
      show 7 ≤ j + 11 by omega,
      show 8 ≤ j + 11 by omega,
      show 9 ≤ j + 11 by omega,
      show 10 ≤ j + 11 by omega,
      show j + 11 - 0 = j + 11 by omega,
      show j + 11 - 1 = j + 10 by omega,
      show j + 11 - 2 = j + 9 by omega,
      show j + 11 - 3 = j + 8 by omega,
      show j + 11 - 4 = j + 7 by omega,
      show j + 11 - 5 = j + 6 by omega,
      show j + 11 - 6 = j + 5 by omega,
      show j + 11 - 7 = j + 4 by omega,
      show j + 11 - 8 = j + 3 by omega,
      show j + 11 - 9 = j + 2 by omega,
      show j + 11 - 10 = j + 1 by omega,
      show ¬ (j + 11 = 1) by omega,
      show ¬ (j + 11 = 2) by omega,
      show ¬ (j + 11 = 3) by omega,
      show ¬ (j + 11 = 4) by omega,
      show ¬ (j + 11 = 5) by omega,
      show ¬ (j + 11 = 6) by omega,
      show ¬ (j + 11 = 7) by omega,
      show ¬ (j + 11 = 8) by omega,
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

end OMA.A249849

theorem OMA.solution : type_of% @OMA.S_oeis_a249849.main :=
  ⟨OMA.A249849.gen_fun, OMA.A249849.recurrence⟩
