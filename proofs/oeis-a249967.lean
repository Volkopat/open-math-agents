import OMAStatements.S_oeis_a249967
import Mathlib

/- The threshold-set recursion is adapted from @Salofe’s merged proofs of A249963 and A250064. -/
namespace OMA.WindowCount
open OMA.S_oeis_a249967 Finset

def Cy (y : Fin 6 → ℕ) : Prop :=
  ∃ S ∈ (univ : Finset (Fin 6)).powersetCard 2, ∃ v, (∀ t ∈ S, y t ≤ v) ∧ (∃ t ∈ S, y t = v) ∧
    (∀ t ∉ S, v ≤ y t) ∧ (∃ t ∉ S, y t = v)



theorem pair_iff (y : Fin 6 → ℕ) : MaxPairEqMinRest y ↔ Cy y := by
  constructor
  · rintro ⟨i,j,hij,hm⟩
    let S : Finset (Fin 6) := {i,j}
    have hS : S.card = 2 := by simp [S,hij]
    have hc : Sᶜ.Nonempty := by
      apply card_pos.mp
      rw [card_compl,hS]
      decide
    let v := max (y i) (y j)
    have he : (v : WithTop ℕ) = Sᶜ.inf (fun k => (y k : WithTop ℕ)) := hm
    obtain ⟨k,hk,ek⟩ := exists_mem_eq_inf Sᶜ hc (fun t => (y t : WithTop ℕ))
    refine ⟨S,mem_powersetCard.mpr ⟨subset_univ _,hS⟩,v,?_,?_,?_,?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact le_max_left _ _
      · obtain rfl := mem_singleton.mp ht
        exact le_max_right _ _
    · rcases le_total (y i) (y j) with h|h
      · exact ⟨j,by simp [S],(max_eq_right h).symm⟩
      · exact ⟨i,by simp [S],(max_eq_left h).symm⟩
    · intro t ht
      exact WithTop.coe_le_coe.mp (he.trans_le (inf_le (mem_compl.mpr ht)))
    · exact ⟨k,mem_compl.mp hk,WithTop.coe_injective (he.trans ek).symm⟩
  · rintro ⟨S,hS,v,hlo,⟨i0,hi0,ei⟩,hhi,⟨k,hk,ek⟩⟩
    obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hS).2
    refine ⟨i,j,hij,?_⟩
    have hm : max (y i) (y j) = v := by
      apply le_antisymm (max_le (hlo i (by simp)) (hlo j (by simp)))
      rcases mem_insert.mp hi0 with rfl | hj
      · exact ei ▸ le_max_left _ _
      · obtain rfl := mem_singleton.mp hj
        exact ei ▸ le_max_right _ _
    rw [hm]
    apply le_antisymm
    · exact Finset.le_inf (fun t ht => WithTop.coe_le_coe.mpr (hhi t (mem_compl.mp ht)))
    · rw [← ek]
      exact inf_le (mem_compl.mpr hk)

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



def fget (f : Fin 12 → Bool) (k : ℕ) : Bool := if h : k < 12 then f ⟨k, h⟩ else false

/-- Number of positions of window `i` lying in the set `f`. -/
def cntW (f : Fin 12 → Bool) (i : ℕ) : ℕ :=
  (univ.filter (fun t : Fin 6 => fget f (i + t) = true)).card

/-- Two consecutive strict threshold sets: no window goes from at most one position to at least
three positions. -/
def Comp (S T : Fin 12 → Bool) : Prop := ∀ i < (7 : ℕ), ¬ (cntW S i ≤ 1 ∧ 3 ≤ cntW T i)

instance decComp (S T : Fin 12 → Bool) : Decidable (Comp S T) := by
  unfold Comp
  infer_instance

/-- The positions where `x` is below `v`. -/
def Lt {n : ℕ} (x : Fin 12 → Fin (n + 1)) (v : ℕ) : Fin 12 → Bool :=
  fun p => decide ((x p : ℕ) < v)



def get {n : ℕ} (x : Fin 12 → Fin (n+1)) (k : ℕ) : ℕ := if h : k < 12 then (x ⟨k,h⟩).val else 0

theorem cnt_univ : ∀ i < (7 : ℕ), cntW (fun _ => true) i = 6 := by
  decide

theorem good_iff {n : ℕ} (x : Fin 12 → Fin (n + 1)) :
    (∀ s, ¬ MaxPairEqMinRest (window x s)) ↔ ∀ v ≤ n, Comp (Lt x v) (Lt x (v + 1)) := by


  have step1 : (∀ s, ¬ MaxPairEqMinRest (window x s)) ↔
      ∀ i < (7 : ℕ), ¬ Cy (fun t : Fin 6 => get x (i + t)) := by
    have aux (i : Fin 7) : window x i = fun t : Fin 6 => get x (i.val + t) := by
      funext t
      have ht := t.isLt
      have hi := i.isLt
      simp [window,get,show i.val+t.val < 12 by omega]
    constructor
    · intro h i hi
      simpa only [pair_iff,aux] using h ⟨i,hi⟩
    · intro h i
      simpa only [pair_iff,aux] using h i.val i.isLt

  have step2 : ∀ i < (7 : ℕ), ∀ v : ℕ,
      (univ.filter (fun t : Fin 6 => get x (i + t) < v)).card = cntW (Lt x v) i := by
    intro i hi v
    unfold cntW
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ht : i + (t : ℕ) < 12 := by have := t.isLt; omega
    unfold get fget Lt
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
noncomputable def M (n : ℕ) (T : Fin 12 → Bool) : ℕ := by
  classical
  exact ((univ : Finset (Fin 12 → Fin (n + 1))).filter
    (fun x => (∀ p, Lt x n p = true → T p = true) ∧ (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧
      Comp (Lt x n) T)).card

theorem Lt_zero {n : ℕ} (x : Fin 12 → Fin (n + 1)) : Lt x 0 = fun _ => false := by
  funext p
  unfold Lt
  simp

theorem M_zero (T : Fin 12 → Bool) : M 0 T = if Comp (fun _ => false) T then 1 else 0 := by
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
def lower {n : ℕ} (x : Fin 12 → Fin (n + 2)) : Fin 12 → Fin (n + 1) :=
  fun p => ⟨min (x p : ℕ) n, by omega⟩

/-- Extension of an array with entries in `0..n` by the top value `n + 1` outside `S`. -/
def raise {n : ℕ} (S : Fin 12 → Bool) (x : Fin 12 → Fin (n + 1)) : Fin 12 → Fin (n + 2) :=
  fun p => if S p = true then ⟨x p, by omega⟩ else ⟨n + 1, by omega⟩

theorem Lt_lower {n : ℕ} (x : Fin 12 → Fin (n + 2)) (v : ℕ) (hv : v ≤ n) :
    Lt (lower x) v = Lt x v := by
  funext p
  show decide (min (x p : ℕ) n < v) = decide ((x p : ℕ) < v)
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem raise_val {n : ℕ} (S : Fin 12 → Bool) (x : Fin 12 → Fin (n + 1)) (p : Fin 12) :
    ((raise S x p : Fin (n + 2)) : ℕ) = if S p = true then (x p : ℕ) else n + 1 := by
  unfold raise
  split_ifs <;> rfl

theorem M_succ (n : ℕ) (T : Fin 12 → Bool) :
    M (n + 1) T = ∑ S : Fin 12 → Bool,
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
def row (u : Fin 4096) : Fin 12 → Bool := fun p => Nat.testBit u.val p.val

theorem blocks (P : Fin 4096 → Prop)
    (h : ∀ j : Fin 64, ∀ i : Fin 64, P ⟨j.val*64+i.val,by have := j.isLt; have := i.isLt; omega⟩) :
    ∀ u : Fin 4096, P u := by
  intro u
  have hu := u.isLt
  have e := h ⟨u.val / 64,by omega⟩ ⟨u.val % 64, Nat.mod_lt _ (by decide)⟩
  convert e using 2
  dsimp
  omega

theorem row_injective : Function.Injective row := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · exact congrFun h ⟨i,hi⟩
  · have hb : 4096 ≤ 2^i := by
      calc 4096 = 2^12 := by decide
           _ ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hb), Nat.testBit_eq_false_of_lt (b.isLt.trans_le hb)]

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩



def lowPack : ℕ → ℕ
  | 0 => 0xc183060c183060c183060c183060e1c3870e1c3870f1e3c78f9f3f7fe1c3870e1c3870f1e3c78f9f3f7ff1e3c78f9f3f7ff9f3f7ffdfffff
  | 1 => 0x81020408102040810204081020408102040810204081020408102041c183060c183060c183060c183061e1c3870e1c3871f1e3c79f9f7fff
  | 2 => 0x81020408102040810204081020408102040810204081020408102143c183060c183060c183060c183163e1c3870e1c3973f1e3d7bfdfffff
  | 3 => 0x100000000000000000000000000010000000000000100000010004183
  | 4 => 0x81020408102040810204081020408102040810204081020408912347c183060c183060c183060c993367e1c3870e9d3b77f9f3f7ffdfffff
  | 5 => 0x100000000000000000000000000010000000000000100000010814387
  | 6 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 7 => 0x100000000000000000000000000010000000000000100000010004183
  | 8 => 0x8102040810204081020408102040810204081020409122448993274fc183060c183060d1a3468d9b376ff1e3c78f9f3f7ff9f3f7ffdfffff
  | 9 => 0x10000000000000000000000000001000000000000011020409183478f
  | 10 => 0x103000000000000000000000000010300000000000103102050b1c3c78f
  | 11 => 0x100000000000000000000000000010000000000000100000010004183
  | 12 => 0x810307000000000000000000000081030700000000810307183070f1c3c78f
  | 13 => 0x100000000000000000000000000010000000000000100000010814387
  | 14 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 15 => 0x100000000000000000000000000010000000000000100000010004183
  | 16 => 0x8102040810204081020408102040a142850a142850b162c58b972f5fe1c3870e1c3870f1e3c78f9f3f7ff1e3c78f9f3f7ff9f3f7ffdfffff
  | 17 => 0x10000000000000000000000000001204081020408113060c193874f9f
  | 18 => 0x1030000000000000000000000000103204081020409133060d1b3c7cf9f
  | 19 => 0x100000000000000000000000000010000000000000100000010004183
  | 20 => 0x810307000000000000000000000081030720408102850b173870f1f3c7cf9f
  | 21 => 0x100000000000000000000000000010000000000000100000010814387
  | 22 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 23 => 0x100000000000000000000000000010000000000000100000010004183
  | 24 => 0x1020408183070f000000000000001020408183070f3060c183870f1f3870f1f3c7cf9f
  | 25 => 0x10000000000000000000000000001000000000000011020409183478f
  | 26 => 0x103000000000000000000000000010300000000000103102050b1c3c78f
  | 27 => 0x100000000000000000000000000010000000000000100000010004183
  | 28 => 0x810307000000000000000000000081030700000000810307183070f1c3c78f
  | 29 => 0x100000000000000000000000000010000000000000100000010814387
  | 30 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 31 => 0x100000000000000000000000000010000000000000100000010004183
  | 32 => 0xc183060c183060c183060c183060e1c3870e1c3870f1e3c78f9f3f7fe1c3870e1c3870f1e3c78f9f3f7ff1e3c78f9f3f7ff9f3f7ffdfffff
  | 33 => 0x1408102040810204081020408102160c183060c183170e1c3978f5fbf
  | 34 => 0x103408102040810204081020408112360c183060c193370e1d3b7cfdfbf
  | 35 => 0x100000000000000000000000000010000000000000100000010004183
  | 36 => 0x810307408102040810204081020489132760c183068d1b3778f1f3f7cfdfbf
  | 37 => 0x100000000000000000000000000010000000000000100000010814387
  | 38 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 39 => 0x100000000000000000000000000010000000000000100000010004183
  | 40 => 0x1020408183070f4081020408102050a142858b172f70e1c3878f1f3f78f1f3f7cfdfbf
  | 41 => 0x10000000000000000000000000001000000000000011020409183478f
  | 42 => 0x103000000000000000000000000010300000000000103102050b1c3c78f
  | 43 => 0x100000000000000000000000000010000000000000100000010004183
  | 44 => 0x810307000000000000000000000081030700000000810307183070f1c3c78f
  | 45 => 0x100000000000000000000000000010000000000000100000010814387
  | 46 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 47 => 0x100000000000000000000000000010000000000000100000010004183
  | 48 => 0x204081020408103060c183870f1f60c183060c183070e1c3878f1f3f70e1c3878f1f3f78f1f3f7cfdfbf
  | 49 => 0x10000000000000000000000000001204081020408113060c193874f9f
  | 50 => 0x1030000000000000000000000000103204081020409133060d1b3c7cf9f
  | 51 => 0x100000000000000000000000000010000000000000100000010004183
  | 52 => 0x810307000000000000000000000081030720408102850b173870f1f3c7cf9f
  | 53 => 0x100000000000000000000000000010000000000000100000010814387
  | 54 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 55 => 0x100000000000000000000000000010000000000000100000010004183
  | 56 => 0x1020408183070f000000000000001020408183070f3060c183870f1f3870f1f3c7cf9f
  | 57 => 0x10000000000000000000000000001000000000000011020409183478f
  | 58 => 0x103000000000000000000000000010300000000000103102050b1c3c78f
  | 59 => 0x100000000000000000000000000010000000000000100000010004183
  | 60 => 0x810307000000000000000000000081030700000000810307183070f1c3c78f
  | 61 => 0x100000000000000000000000000010000000000000100000010814387
  | 62 => 0x10300000000000000000000000001030000000000010300001030c1c387
  | 63 => 0x100000000000000000000000000010000000000000100000010004183
  | _ => 0

def low (u : ℕ) : ℕ := (lowPack (u / 64) >>> (7*(u % 64))) % 128

def highPack : ℕ → ℕ
  | 0 => 0x1e3c78f1e3c78f0e1c387060c0800e1c387060c080060c08002000000e1c387060c080060c0800200000060c080020000002000000000000
  | 1 => 0x3e7cf9f3e7cf9f3e7cf9f3e7cf9e1e3c78f1e3c78e0e1c38606080001e3c78f1e3c78e0e1c38606080000e1c386060800006080000000000
  | 2 => 0x3e7cf9f3e7cf9f3e7cf9f3e7ce9c1e3c78f1e3c68c0e1c28402000001e3c78f1e3c68c0e1c28402000000e1c284020000002000000000000
  | 3 => 0x7efdfbf7efdfbf7efdfbf7efdfbe7efdfbf7efdfbe7efdfbe7ef9e3c3e7cf9f3e7cf9e3e7cf9e3e78e1c1e3c78e1e3860c0e182040000000
  | 4 => 0x3e7cf9f3e7cf9f3e7cf9f366cc981e3c78f162c488060c08002000001e3c78f162c488060c0800200000060c080020000002000000000000
  | 5 => 0x7efdfbf7efdfbf7efdfbf7efdfbe7efdfbf7efdfbe7efdfbe76e9c383e7cf9f3e7cf9e3e7cf9e3668c181e3c78e162840806080000000000
  | 6 => 0x7efdfbf7efdfbf7efdfbf7efdebc7efdfbf7efdebc7efdebc72e1c383e7cf9f3e7ce9c3e7ce9c3260c181e3c68c122040802000000000000
  | 7 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | 8 => 0x3e7cf9f3e7cf9f2e5cb97264c8900e1c387060c080060c08002000000e1c387060c080060c0800200000060c080020000002000000000000
  | 9 => 0x7efdfbf7efdfbf7efdfbf7efdfbe7efdfbf7efdfbe6eddbb666c98303e7cf9f3e7cf9e2e5cb9626488100e1c386060800006080000000000
  | 10 => 0x7efdfbf7efdfbf7efdfbf7efdebc7efdfbf7efdebc6eddab462c18303e7cf9f3e7ce9c2e5ca9422408100e1c284020000002000000000000
  | 11 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cefdba74e1c3870
  | 12 => 0x7efdfbf7efdfbf7efdfbf76edcb87efdfbf76edcb866cd8b062c18303e7cf9f366cc98264c8902240810060c080020000002000000000000
  | 13 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffef7ebc78fffffffffffffeffffffef7ebc78ffffffef7ebc78e7cb870e1c3870
  | 14 => 0xfffffffffffffffffffffffffefcfffffffffffefcffffefcf3e3c78fffffffffffefcffffefcf3e3c78ffffefcf3e3c78e3c3870e1c3870
  | 15 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | 16 => 0x1e3c78f1e3c78f0e1c387060c0800e1c387060c080060c08002000000e1c387060c080060c0800200000060c080020000002000000000000
  | 17 => 0x7efdfbf7efdfbf7efdfbf7efdfbe5ebd7af5ebd7ae4e9d3a646890201e3c78f1e3c78e0e1c38606080000e1c386060800006080000000000
  | 18 => 0x7efdfbf7efdfbf7efdfbf7efdebc5ebd7af5ebd6ac4e9d2a442810201e3c78f1e3c68c0e1c28402000000e1c284020000002000000000000
  | 19 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cdfbf7eedfbb66ccf9b264c183060
  | 20 => 0x7efdfbf7efdfbf7efdfbf76edcb85ebd7af56ad4a8468d0a042810201e3c78f162c488060c0800200000060c080020000002000000000000
  | 21 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffef7ebc78fffffffffffffeffffffef7ebc78dfbf7eed7ab468c78b060c183060
  | 22 => 0xfffffffffffffffffffffffffefcfffffffffffefcffffefcf3e3c78fffffffffffefcffffefcf3e3c78dfbf6ecd3a3468c383060c183060
  | 23 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | 24 => 0x7efdfbf7efdfbf6eddbb766cd8b04e9d3a7468d0a0468d0a042810200e1c387060c080060c0800200000060c080020000002000000000000
  | 25 => 0xfffffffffffffffffffffffffffefffffffffffffeefdfbf6e7cb870fffffffffffffeefdfbf6e7cb870cf9f3e6c78b060c78b060c183060
  | 26 => 0xfffffffffffffffffffffffffefcfffffffffffefcefdfaf4e3c3870fffffffffffefcefdfaf4e3c3870cf9f2e4c383060c383060c183060
  | 27 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cefdba74e1c3870
  | 28 => 0xffffffffffffffffffffff7efcf8ffffffff7efcf8e7cf8f0e3c3870ffffffff7efcf8e7cf8f0e3c3870c78f0e0c383060c383060c183060
  | 29 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffef7ebc78fffffffffffffeffffffef7ebc78ffffffef7ebc78e7cb870e1c3870
  | 30 => 0xfffffffffffffffffffffffffefcfffffffffffefcffffefcf3e3c78fffffffffffefcffffefcf3e3c78ffffefcf3e3c78e3c3870e1c3870
  | 31 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | 32 => 0x1e3c78f1e3c78f0e1c387060c0800e1c387060c080060c08002000000e1c387060c080060c0800200000060c080020000002000000000000
  | 33 => 0x3e7cf9f3e7cf9f3e7cf9f3e7cf9e1e3c78f1e3c78e0e1c38606080001e3c78f1e3c78e0e1c38606080000e1c386060800006080000000000
  | 34 => 0x3e7cf9f3e7cf9f3e7cf9f3e7ce9c1e3c78f1e3c68c0e1c28402000001e3c78f1e3c68c0e1c28402000000e1c284020000002000000000000
  | 35 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cbf7efdfbf7efdebf7efdebf7ae5c9f3e7ce9f3a64c8f1a2448102040
  | 36 => 0x3e7cf9f3e7cf9f3e7cf9f366cc981e3c78f162c488060c08002000001e3c78f162c488060c0800200000060c080020000002000000000000
  | 37 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffef7ebc78bf7efdfbf7efdebf7efdeb76ac589f3e7ce972a448870a0408102040
  | 38 => 0xfffffffffffffffffffffffffefcfffffffffffefcffffefcf3e3c78bf7efdfbf7eedcbf7eedcb362c589f3e6cc932244883020408102040
  | 39 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | 40 => 0x3e7cf9f3e7cf9f2e5cb97264c8900e1c387060c080060c08002000000e1c387060c080060c0800200000060c080020000002000000000000
  | 41 => 0xfffffffffffffffffffffffffffefffffffffffffeefdfbf6e7cb870bf7efdfbf7efdeaf5ebd6a74a8508f1e3c6870a040870a0408102040
  | 42 => 0xfffffffffffffffffffffffffefcfffffffffffefcefdfaf4e3c3870bf7efdfbf7eedcaf5ead4a3428508f1e2c4830204083020408102040
  | 43 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cefdba74e1c3870
  | 44 => 0xffffffffffffffffffffff7efcf8ffffffff7efcf8e7cf8f0e3c3870bf7efdfb76ecd8a74e8d0a342850870e0c0830204083020408102040
  | 45 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffef7ebc78fffffffffffffeffffffef7ebc78ffffffef7ebc78e7cb870e1c3870
  | 46 => 0xfffffffffffffffffffffffffefcfffffffffffefcffffefcf3e3c78fffffffffffefcffffefcf3e3c78ffffefcf3e3c78e3c3870e1c3870
  | 47 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | 48 => 0x1e3c78f1e3c78f0e1c387060c0800e1c387060c080060c08002000000e1c387060c080060c0800200000060c080020000002000000000000
  | 49 => 0xfffffffffffffffffffffffffffedfbf7efdfbf7eecf9f3e6c78b0609f3e7cf9f3e7ce8f1e3c6870a0408f1e3c6870a040870a0408102040
  | 50 => 0xfffffffffffffffffffffffffefcdfbf7efdfbf6eccf9f2e4c3830609f3e7cf9f3e6cc8f1e2c483020408f1e2c4830204083020408102040
  | 51 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cdfbf7eedfbb66ccf9b264c183060
  | 52 => 0xffffffffffffffffffffff7efcf8dfbf7efd7af4e8c78f0e0c3830609f3e7cf972e4c8870e0c08302040870e0c0830204083020408102040
  | 53 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffef7ebc78fffffffffffffeffffffef7ebc78dfbf7eed7ab468c78b060c183060
  | 54 => 0xfffffffffffffffffffffffffefcfffffffffffefcffffefcf3e3c78fffffffffffefcffffefcf3e3c78dfbf6ecd3a3468c383060c183060
  | 55 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | 56 => 0xffffffffffffffefdfbf7e7cf8f0cf9f3e7c78f0e0c78f0e0c3830608f1e3c7870e0c0870e0c08302040870e0c0830204083020408102040
  | 57 => 0xfffffffffffffffffffffffffffefffffffffffffeefdfbf6e7cb870fffffffffffffeefdfbf6e7cb870cf9f3e6c78b060c78b060c183060
  | 58 => 0xfffffffffffffffffffffffffefcfffffffffffefcefdfaf4e3c3870fffffffffffefcefdfaf4e3c3870cf9f2e4c383060c383060c183060
  | 59 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cefdba74e1c3870
  | 60 => 0xffffffffffffffffffffff7efcf8ffffffff7efcf8e7cf8f0e3c3870ffffffff7efcf8e7cf8f0e3c3870c78f0e0c383060c383060c183060
  | 61 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffef7ebc78fffffffffffffeffffffef7ebc78ffffffef7ebc78e7cb870e1c3870
  | 62 => 0xfffffffffffffffffffffffffefcfffffffffffefcffffefcf3e3c78fffffffffffefcffffefcf3e3c78ffffefcf3e3c78e3c3870e1c3870
  | 63 => 0xfffffffffffffffffffffffffffefffffffffffffeffffffefffbe7cfffffffffffffeffffffefffbe7cffffffefffbe7cfffbe7cf1e3c78
  | _ => 0

def high (u : ℕ) : ℕ := (highPack (u / 64) >>> (7*(u % 64))) % 128

def compc (s t : ℕ) : Bool := (low s &&& high t) == 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem compc_iff (s t : Fin 4096) : Comp (row s) (row t) ↔ compc s.val t.val = true := by

  have lowSpec : ∀ u : Fin 4096, (((low u.val).testBit 0) = true ↔ cntW (row u) 0 ≤ 1) ∧ (((low u.val).testBit 1) = true ↔ cntW (row u) 1 ≤ 1) ∧ (((low u.val).testBit 2) = true ↔ cntW (row u) 2 ≤ 1) ∧ (((low u.val).testBit 3) = true ↔ cntW (row u) 3 ≤ 1) ∧ (((low u.val).testBit 4) = true ↔ cntW (row u) 4 ≤ 1) ∧ (((low u.val).testBit 5) = true ↔ cntW (row u) 5 ≤ 1) ∧ (((low u.val).testBit 6) = true ↔ cntW (row u) 6 ≤ 1) := by
    apply blocks
    intro j
    fin_cases j <;> decide +kernel

  have highSpec : ∀ u : Fin 4096, (((high u.val).testBit 0) = true ↔ cntW (row u) 0 ≥ 3) ∧ (((high u.val).testBit 1) = true ↔ cntW (row u) 1 ≥ 3) ∧ (((high u.val).testBit 2) = true ↔ cntW (row u) 2 ≥ 3) ∧ (((high u.val).testBit 3) = true ↔ cntW (row u) 3 ≥ 3) ∧ (((high u.val).testBit 4) = true ↔ cntW (row u) 4 ≥ 3) ∧ (((high u.val).testBit 5) = true ↔ cntW (row u) 5 ≥ 3) ∧ (((high u.val).testBit 6) = true ↔ cntW (row u) 6 ≥ 3) := by
    apply blocks
    intro j
    fin_cases j <;> decide +kernel

  have maskSpec : ∀ a : Fin 128, ∀ b : Fin 128, ((a.val &&& b.val) == 0) = true ↔ ¬ (a.val.testBit 0 = true ∧ b.val.testBit 0 = true) ∧ ¬ (a.val.testBit 1 = true ∧ b.val.testBit 1 = true) ∧ ¬ (a.val.testBit 2 = true ∧ b.val.testBit 2 = true) ∧ ¬ (a.val.testBit 3 = true ∧ b.val.testBit 3 = true) ∧ ¬ (a.val.testBit 4 = true ∧ b.val.testBit 4 = true) ∧ ¬ (a.val.testBit 5 = true ∧ b.val.testBit 5 = true) ∧ ¬ (a.val.testBit 6 = true ∧ b.val.testBit 6 = true) := by
    intro u v
    simp only [beq_iff_eq]
    constructor
    · intro h
      have bit (i : ℕ) : ¬ (u.val.testBit i = true ∧ v.val.testBit i = true) := by
        rintro ⟨hu,hv⟩
        have eq := congrArg (fun w : ℕ => w.testBit i) h
        simp [Nat.testBit_and,hu,hv] at eq
      exact ⟨bit 0,bit 1,bit 2,bit 3,bit 4,bit 5,bit 6⟩
    · rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and,Nat.zero_testBit]
      have eq (x y : Bool) : ¬ (x = true ∧ y = true) → (x && y) = false := by cases x <;> cases y <;> decide
      by_cases hi : i < 7
      · apply eq
        interval_cases i <;> assumption
      · have hpow : 128 ≤ 2^i := by
          calc 128 = 2^7 := by decide
               _ ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_eq_false_of_lt (u.isLt.trans_le hpow),Bool.false_and]

  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := lowSpec s
  obtain ⟨g0,g1,g2,g3,g4,g5,g6⟩ := highSpec t

  unfold compc
  rw [maskSpec ⟨low s.val, Nat.mod_lt _ (by decide)⟩ ⟨high t.val,Nat.mod_lt _ (by decide)⟩]
  simp only [h0,h1,h2,h3,h4,h5,h6,g0,g1,g2,g3,g4,g5,g6]
  constructor
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide),h 5 (by decide),h 6 (by decide)⟩
  · rintro ⟨p0,p1,p2,p3,p4,p5,p6⟩ i hi
    interval_cases i <;> assumption

theorem sub_iff (w u : Fin 4096) : (∀ p, row w p = true → row u p = true) ↔
    (w.val &&& u.val == w.val) = true := by
  rw [beq_iff_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land]
    by_cases hi : i < 12
    · have := h ⟨i, hi⟩
      unfold row at this
      cases hw : w.val.testBit i <;> simp_all
    · have hw : w.val.testBit i = false := by
        apply Nat.testBit_eq_false_of_lt
        have h1 : (4096 : ℕ) ≤ 2 ^ i := by
          calc (4096 : ℕ) = 2 ^ 12 := by norm_num
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
def subs (u : Fin 4096) : Finset (Fin 4096) :=
  univ.filter (fun w : Fin 4096 => (w.val &&& u.val == w.val) = true)

/-- The chain recursion on codes. -/
def G : ℕ → Fin 4096 → ℕ
  | 0, u => if compc 0 u.val = true then 1 else 0
  | n + 1, u => ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0

theorem row_zero : row 0 = fun _ => false := by
  funext p
  simp [row]

theorem M_eq_G (n : ℕ) : ∀ u : Fin 4096, M n (row u) = G n u := by
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

theorem row_full : ∀ p, row 4095 p = true := by
  decide

theorem a_eq_G (n : ℕ) : a n = G n 4095 := by
  classical
  have h1 : (univ.filter (fun x : Fin 12 → Fin (n + 1) => ∀ s, ¬ MaxPairEqMinRest (window x s))) =
      univ.filter (fun x => (∀ p, Lt x n p = true → row 4095 p = true) ∧
        (∀ v < n, Comp (Lt x v) (Lt x (v + 1))) ∧ Comp (Lt x n) (row 4095)) := by
    apply Finset.filter_congr
    intro x _
    rw [good_iff]
    have hr : row 4095 = fun _ => true := funext row_full
    have hn : Lt x (n + 1) = row 4095 := by
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
  rfl



theorem G_succ (n : ℕ) (u : Fin 4096) :
    G (n + 1) u = ∑ w ∈ subs u, if compc w.val u.val = true then G n w else 0 :=
  rfl



def stateIndexPack : ℕ → ℕ
  | 0 => 0x30140a040281008030281008030200c06020281008030200c06020200c06020180804010281008030200c06020200c06020180804010200c0602018080401018080401010040200
  | 1 => 0x7034180b0602c14090602c14090502410030602c14090502410030502410030400c0e020602c14090502410030502410030400c0e020502410030400c0e020400c0e02038080401
  | 2 => 0xa030260b0902822090902822090802010030902822090802010030802010030781c0e020902822090802010030802010030781c0e020802010030781c0e020781c0e02038080401
  | 3 => 0x108803e1e0e870361a0e870361a0c8602e090e870361a0c8602e090c8602e090b0201e030e870361a0c8602e090c8602e090b0201e030c8602e090b0201e030b0201e030a81c0e02
  | 4 => 0x12848240a1204422091184020080802010031184020080802010031103c1e070781c0e021184020080802010031103c1e070781c0e021103c1e070781c0e020781c0e02038080401
  | 5 => 0x178b83a1c168b0361a158a83218148a02e09158a83218148a02e091385c2c080b0201e03158a83218148a02e091385c2c080b0201e031385c2c080b0201e031303c2a070a81c0e02
  | 6 => 0x1c874701c1b86c6c1a1a86468181985c2e091a86468181985c2e09190582c081883c1e031a86468181985c2e09190582c081883c1e03190582c081883c1e03180542a070a81c0e02
  | 7 => 0x27134984b25124904723114884321104801a23114884321104801a1f8f87a181e05c760923114884321104801a1f8f87a181e05c76091f8f87a181e05c76091d0584c081803c1e03
  | 8 => 0x2808c461011840200811840200808020100327888440f1103c1e071103c1e070781c0e0227888440f1103c1e071103c1e070781c0e021103c1e070781c0e020781c0e02038080401
  | 9 => 0x2b958562a158a832182a9505228148a02e09299484e171385c2c081385c2c080b0201e03299484e171385c2c081385c2c080b0201e03288ec4c0f1303c2a071303c2a070a81c0e02
  | 10 => 0x2f0acba2a1a86468182e0a4b6281985c2e092d09cb217190582c08190582c081883c1e032d09cb217190582c08190582c081883c1e032c0984c0f180542a07180542a070a81c0e02
  | 11 => 0x371b4d86b231148843351a4d06721104801a33194c8411f8f87a1831988c2281e05c760933194c8411f8f87a1831988c2281e05c7609300f4be171d0584c081d0584c081803c1e03
  | 12 => 0x3a0d46a19398d06818390cc66171985c2e09388c86416190582c08380c4620f1883c1e03388c86416190582c08380c4620f1883c1e03378c06015180542a07180542a070a81c0e02
  | 13 => 0x41a088c4540a0088433f9f884413e9f0801a3d9e87e3e3c9887a183c1dc78171e05c76093d9e87e3e3c9887a183c1dc78171e05c76093b0f074161d0584c083a8c4600f1803c1e03
  | 14 => 0x489192045479111c4346909184145900801a450fd123e440f47a18438f07817430ec7609450fd123e440f47a18438f07817430ec7609428e874163a8984c08420c0600f1803c1e03
  | 15 => 0x5429d4ca55228d444b50a813e6b4f275381e4da6932454c1952e1c4b1e92a2a4a149260b4da6932454c1952e1c4b1e92a2a4a149260b490fcc0193b09ca20a428c8b010378884404
  | 16 => 0x5493c9e2227888440f27888440f1103c1e0727888440f1103c1e071103c1e070781c0e0227888440f1103c1e071103c1e070781c0e021103c1e070781c0e020781c0e02038080401
  | 17 => 0x562aca652299484e17299484e171385c2c08299484e171385c2c081385c2c080b0201e035524ca23b288ec4c0f288ec4c0f1303c2a07288ec4c0f1303c2a071303c2a070a81c0e02
  | 18 => 0x5814d5e522d09cb2172d09cb217190582c082d09cb217190582c08190582c081883c1e03571455a3b2c0984c0f2c0984c0f180542a072c0984c0f180542a07180542a070a81c0e02
  | 19 => 0x5c2dd6c9d33194c84133194c8411f8f87a185aad1667c31988c22831988c2281e05c76095925d6240300f4be17300f4be171d0584c08300f4be171d0584c081d0584c081803c1e03
  | 20 => 0x5d968b4275d164b217388c86416190582c08388c86416190582c08380c4620f1883c1e035c960b0262c0984c0f378c06015180542a07378c06015180542a07180542a070a81c0e02
  | 21 => 0x62b10cc6561b08c8413d9e87e3e3c9887a1860b00c6625faf8c2283c1dc78171e05c76095ea54c03d5e184be173b0f074161d0584c083b0f074161d0584c083a8c4600f1803c1e03
  | 22 => 0x679999c65669919841450fd123e440f47a186598d946264984c228438f07817430ec7609641818e3d6317cbe17428e874163a8984c08428e874163a8984c08420c0600f1803c1e03
  | 23 => 0x6fb79baa36e36db4494da6932454c1952e1c6cb61ae806b309aa2c4b1e92a2a4a149260b6a265a64469191621b490fcc0193b09ca20a68a258e34681655a11428c8b010378884404
  | 24 => 0x711c4e232388c86416388c86416190582c08709c0e031380c4620f380c4620f1883c1e03701bcde30378c06015378c06015180542a07378c06015180542a07180542a070a81c0e02
  | 25 => 0x753a4f67a3d9e87e3e7439cf2623c9887a1873394f0773c1dc78173c1dc78171e05c760972250ec3c3b0f074163b0f074161d0584c0871a18ea313a8c4600f3a8c4600f1803c1e03
  | 26 => 0x791ede27a450fd123e781e5de62440f47a18771e1da77438f07817438f07817430ec7609761d9a03c428e87416428e874163a8984c08759d4ea31420c0600f420c0600f1803c1e03
  | 27 => 0x803fdfca04da6932457ebf1f6694c1952e1c7d3e5f07e4b1e92a2a7bb9dec544a149260b7aa61a442490fcc0197a1e578293b09ca20a79a218c33428c8b010428c8b010378884404
  | 28 => 0x84229143f83a25123e83221103d440f47a1882a1d0e3c438f07817822190c3b430ec760981a150a3a428e87416811d4ea263a8984c0880a110830420c0600f420c0600f1803c1e03
  | 29 => 0x8a44d369a89361324588be53065882d12e1c87c392c7a86b012a2a8639528524a149260b85a59243f7a18cc019851e0ec273b09ca20a84a1d0a32428c8b010811c0de22378884404
  | 30 => 0x9126e429a902663e458f2623a658e25d2e1c8da5a347a8ca552a2a8c25128528ba4d260b8b249a23f79980c019849d8ec2771944a20a8aa150a3275960b010809bcde22378884404
  | 31 => 0x9a4ce64a798b7a604d97bfe5c6d96ade582095c4e548294b12502e93ba64c5692aae480d91a6da8467a999641d859ed7a2b7214d540c8b2299035761695c12819c572237013c9e05
  | 32 => 0x5493c9e2227888440f27888440f1103c1e0727888440f1103c1e071103c1e070781c0e0227888440f1103c1e071103c1e070781c0e021103c1e070781c0e020781c0e02038080401
  | 33 => 0x9ac9154935524ca23b5524ca23b288ec4c0f5524ca23b288ec4c0f288ec4c0f1303c2a075524ca23b288ec4c0f288ec4c0f1303c2a07288ec4c0f1303c2a071303c2a070a81c0e02
  | 34 => 0x9baaa6c93571455a3b571455a3b2c0984c0f571455a3b2c0984c0f2c0984c0f180542a07571455a3b2c0984c0f2c0984c0f180542a072c0984c0f180542a07180542a070a81c0e02
  | 35 => 0x9ccb2709c5925d62405925d6240300f4be175925d6240300f4be17300f4be171d0584c085925d6240300f4be17300f4be171d0584c08300f4be171d0584c081d0584c081803c1e03
  | 36 => 0x9dab95c519d2b55a3b5c960b0262c0984c0f5c960b0262c0984c0f378c06015180542a075c960b0262c0984c0f378c06015180542a07378c06015180542a07180542a070a81c0e02
  | 37 => 0x9eca164979e35562405ea54c03d5e184be175ea54c03d5e184be173b0f074161d0584c085ea54c03d5e184be173b0f074161d0584c083b0f074161d0584c083a8c4600f1803c1e03
  | 38 => 0xa0aca80979fac67c40641818e3d6317cbe17641818e3d6317cbe17428e874163a8984c08641818e3d6317cbe17428e874163a8984c08428e874163a8984c08420c0600f1803c1e03
  | 39 => 0xa44c28ea2a336a8a486a265a64469191621b6a265a64469191621b490fcc0193b09ca20aa247e868ea13327c3668a258e34681655a1168a258e34681655a11428c8b010378884404
  | 40 => 0xa4ae572585c960b0265c960b0262c0984c0f701bcde30378c06015378c06015180542a07701bcde30378c06015378c06015180542a07378c06015180542a07180542a070a81c0e02
  | 41 => 0xa5c997a955ea54c03da53d978615e184be1772250ec3c3b0f074163b0f074161d0584c0872250ec3c3b0f074163b0f074161d0584c0871a18ea313a8c4600f3a8c4600f1803c1e03
  | 42 => 0xa7af69c95641818e3da6af298616317cbe17761d9a03c428e87416428e874163a8984c08761d9a03c428e87416428e874163a8984c08759d4ea31420c0600f420c0600f1803c1e03
  | 43 => 0xab4baaa9f6a265a644aa3eea66869191621b7aa61a442490fcc0197a1e578293b09ca20aa9476a28c68a258e34a83be985b681655a1179a218c33428c8b010428c8b010378884404
  | 44 => 0xacb219060ac31d8e3dabb198c5f6317cbe1781a150a3a428e87416811d4ea263a8984c0881a150a3a428e87416811d4ea263a8984c0880a110830420c0600f420c0600f1803c1e03
  | 45 => 0xb04a9a899afb5da644af3e1a464aeacd621b85a59243f7a18cc019851e0ec273b09ca20aae469a289adb298e34ad3b5a059681655a1184a1d0a32428c8b010811c0de22378884404
  | 46 => 0xb5352d299b434e8644b3b4aa264b32c5621b8b249a23f79980c019849d8ec2771944a20ab2b46c889b1b1d8e34b1341a059b0ab55a118aa150a3275960b010809bcde22378884404
  | 47 => 0xb9ccae4a6b8b768e4cb83faaa6cb7ada701f91a6da8467a999641d859ed7a2b7214d540cb7486d290b6b3a8038b63c69c5db5abe6c138b2299035761695c12819c572237013c9e05
  | 48 => 0xba381c06f701bcde30701bcde30378c06015701bcde30378c06015378c06015180542a07701bcde30378c06015378c06015180542a07378c06015180542a07180542a070a81c0e02
  | 49 => 0xbb495c89472250ec3c72250ec3c3b0f0741672250ec3c3b0f074163b0f074161d0584c08bac5dc68671a18ea3171a18ea313a8c4600f71a18ea313a8c4600f3a8c4600f1803c1e03
  | 50 => 0xbc392d694761d9a03c761d9a03c428e87416761d9a03c428e87416428e874163a8984c08bbb8ec286759d4ea31759d4ea31420c0600f759d4ea31420c0600f420c0600f1803c1e03
  | 51 => 0xbdcb6de9e7aa61a4427aa61a442490fcc019bd442ba7d7a1e578297a1e578293b09ca20abcc72cc8b79a218c3379a218c33428c8b01079a218c33428c8b010428c8b010378884404
  | 52 => 0xbf3b1d876beb41a03c81a150a3a428e8741681a150a3a428e87416811d4ea263a8984c08be3add675759d4ea3180a110830420c0600f80a110830420c0600f420c0600f1803c1e03
  | 53 => 0xc24a5ea98c1b59a44285a59243f7a18cc019c1435e879c0afd7829851e0ec273b09ca20ac0465e688bfb258c3384a1d0a32428c8b01084a1d0a32428c8b010811c0de22378884404
  | 54 => 0xc4bd6da98c434a84428b249a23f79980c019c3bd2b679bfaf17829849d8ec2771944a20ac33cec688c2b198c338aa150a3275960b0108aa150a3275960b010809bcde22378884404
  | 55 => 0xc74c6e2a4c6b728c4a91a6da8467a999641dc644abe81c1b0e782d859ed7a2b7214d540cc5c82d08fc43367e378b2299035761695c12c541eb073beaea7424819c572237013c9e05
  | 56 => 0xc8c0e068581a150a3a81a150a3a428e87416c840a0475811d4ea26811d4ea263a8984c08c7c06028480a11083080a110830420c0600f80a110830420c0600f420c0600f1803c1e03
  | 57 => 0xcb49e169685a59243fcabdde8637a18cc019ca4321478851e0ec27851e0ec273b09ca20ac9c62128784a1d0a3284a1d0a32428c8b010c94120470811c0de22811c0de22378884404
  | 58 => 0xcdc2ed8968b249a23fcd3d2a06379980c019ccc2ab478849d8ec27849d8ec2771944a20acc426c4878aa150a328aa150a3275960b010cbc0a0470809bcde22809bcde22378884404
  | 59 => 0xd04bee0a191a6da846cfbf6a86a7a999641dcf446bc7f859ed7a2bcaba294557214d540ccec7ace8d8b2299035cd3c29a5c761695c12ce41aae72819c57223819c572237013c9e05
  | 60 => 0xd245a2c92c5345a23fce3cde66079980c019d1c261276849d8ec27c938dc65171944a20ad14562a858aa150a32cbbadd65875960b010d0c06026f809bcde22809bcde22378884404
  | 61 => 0xd3cae469bc6365a846cf3e9ea66bd2d5641dd343e167bc13057a2bca399c8537214d540cd2c6e2c8ac3b2d9035ccbb9d85a761695c12d1c160671819c57223c8385c04f7013c9e05
  | 62 => 0xd4c8edc9bc5b528846cebd6a466bcac9641dd2c2eb87bc02f57a2bc9b91c853baaa9540cd445aca8ac33219035cc3b1d85abbab95c12d140e0671be2e57223c7b81c04f7013c9e05
  | 63 => 0xd54d2e6a8c737e904ed0402ac6ebdae27221d3c52c083c23167a2fcb3aa9657bb2b26a0ed4c8ad491c4b3e8239cdbca9e5ebc2c26e14d2422b274bf2ee7625c8b8a9250ba2a55206
  | _ => 0

def stateIndex (u : ℕ) : ℕ := (stateIndexPack (u / 64) >>> (9*(u % 64))) % 512

def packedClassPack : ℕ → ℕ
  | 0 => 0x4cc80000000000003cf00000000000002f7000000000000024180000000000001ab800000000000013200000000000000d200000000000000888000000000000052800000000000002d000000000000001500000000000000078000000000000001800000000000000000000000031000000000000002a4000000000000024000000000000001e400000000000001900000000000000144000000000000010000000000000000c40000000000000090000000000000006400000000000000400000000000000024000000000000001000000000000000040000000001c000000000000001a00000000000000180000000000000016000000000000001400000000000000120000000000000010000000000000000e000000000000000c000000000000000a0000000000000008000000000000000600000000000000040000000000000002000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x55c000000000000044a8000000000000360000000000000029980000000000001f4000000000000016c800000000000010000000000000000ab800000000000006c000000000000003e8000000000000020000000000000000d800000000000000400000000000000008000012a35e40000000000b8dfb800000000006dfc3800000000003e4edc000000000021465c00000000001086900000000000077d900000000000030414000000000001091400000000000048a80000000000000e28000000000000018c000000000000000c0000000000000000000000bd6ba000000000007f7940000000000052eb40000000000033cde000000000001ed3e00000000000114780000000000008fb800000000000043c20000000000001c02000000000000099c000000000000027c00000000000000660000000000000006000000000000000000000007881000000000000580e0000000000003ea60000000000002b2f0000000000001ca700000000000012240000000000000ad400000000000005fd00000000000002fd000000000000014a0000000000000072000000000000001b00000000000000030000000000000000
  | 2 => 0x2cd83800000000001e08b00000000000136cb000000000000c0d280000000000071c28000000000003f1200000000000020520000000000000ef1800000000000060180000000000001f9000000000000007900000000000000108000000000000000800000000000000000000017ccbc000000000010058000000000000a6ce0000000000006840c000000000003e10c0000000000022ce000000000000121a0000000000000889c000000000000387c0000000000001360000000000000050000000000000000cc000000000000000c00000000000000000000000e436000000000000a5f40000000000007564000000000000505a00000000000034da000000000000211800000000000013780000000000000a8e000000000000051e000000000000021c00000000000000ac00000000000000220000000000000002000000000000000000000007b590000000000005a4a000000000000405e0000000000002c790000000000001d9700000000000012cc0000000000000b4400000000000006430000000000000325000000000000015e000000000000007a000000000000001d00000000000000030000000000000000
  | 3 => 0x432f0000000000003183000000000000239400000000000018d080000000000010b30000000000000ac2000000000000069000000000000003bb80000000000001ef00000000000000e1000000000000005400000000000000168000000000000003000000000000000000000e733c4c00000000083d86b0000000000479c51000000000024b4b7c000000000118b12c00000000007b14400000000000306980000000000010895c000000000004ab6c00000000000101b000000000000024d0000000000000029c000000000000000c0000000000000000000008cec86000000000056ea8400000000003363d400000000001ce51200000000000f497a000000000007807800000000000358d80000000000015196000000000000704e0000000000001d4c000000000000053c000000000000007a000000000000000200000000000000000000049fd2700000000002dd48000000000001b3ca000000000000f68eb00000000000837330000000000041238000000000001d6f8000000000000bccf000000000000406700000000000011780000000000000358000000000000005b00000000000000030000000000000000
  | 4 => 0x23bf02800000000016125400000000000d11340000000000075bd0800000000003e680800000000001eb1c000000000000dbbc00000000000056e28000000000001d0a80000000000007a000000000000001600000000000000020800000000000000080000000000000000000012d57d40000000000baea9000000000006f437800000000003f11c4000000000021b37c000000000010bf0000000000000797d00000000000030e940000000000010c6400000000000049500000000000000e280000000000000184000000000000000c0000000000000000000000b64fa000000000007a3b0000000000004f26000000000000312c2000000000001d0e2000000000001023000000000000084900000000000003d6a00000000000018ba000000000000082000000000000001f00000000000000042000000000000000200000000000000000000006154f00000000000419f4000000000002ac68000000000001ac9d000000000000ffc30000000000008fd00000000000004b0800000000000023850000000000000ebf00000000000005140000000000000150000000000000003500000000000000030000000000000000
  | 5 => 0x2e1c6800000000001ef1100000000000140e4000000000000c797000000000000761880000000000041b200000000000021cc0000000000000fb200000000000006568000000000000217000000000000008000000000000000110000000000000000800000000000000000000018c424000000000010b84000000000000aea58000000000006d920000000000004185c0000000000024f00000000000001355000000000000093000000000000003d540000000000001540000000000000058800000000000000e0000000000000000c000000000000000000000012c20000000000000df22000000000000a20000000000000072620000000000004e200000000000003342000000000000200000000000000012c20000000000000a2000000000000004e2000000000000020000000000000000a20000000000000020000000000000000200003aa36c50000000002179cb000000000012348660000000000958719000000000047979f00000000001f759800000000000c6824000000000004407900000000000134a900000000000042e800000000000009a200000000000000b100000000000000030000000000000000
  | 6 => 0x23909f000000000015f35380000000000cfd338000000000074f70800000000003df39800000000001e717000000000000d9af00000000000055f10000000000001caa00000000000007808000000000000158800000000000001f8000000000000000800000000000000000000014c8a800000000000dd340000000000008de7800000000000572c40000000000032cd0000000000001bba0000000000000deb0000000000000641400000000000026980000000000000be0000000000000028800000000000000440000000000000000000000000000000000000964b3a00000000005d347c00000000003777cc00000000001f6ed8000000000010ca5e00000000000856f8000000000003c788000000000001854400000000000085620000000000002464000000000000070400000000000000c000000000000000060000000000000000000000585b3000000000003b172000000000002626a00000000000179e9000000000000de5d0000000000007adc0000000000003eac0000000000001ccb0000000000000b7700000000000003b600000000000000de000000000000001d00000000000000010000000000000000
  | 7 => 0x1b968d98000000000faa03b0000000000876a49000000000044f7c0800000000020b31e80000000000e311200000000000581ae000000000001d88380000000000081cb8000000000001ac9000000000000038b0000000000000036800000000000000080000000000000000000010672700000000000a0d71000000000005e60d000000000003493e000000000001b7fe000000000000d4ca0000000000005d2200000000000023bd0000000000000b7100000000000002cf000000000000007300000000000000080000000000000000000000000000000000000737dcd600000000041d78a800000000023bf9d00000000001250a0600000000008bf65600000000003d506000000000001815b000000000000835ce0000000000024fa60000000000007ee800000000000012000000000000000146000000000000000600000000000000000000044f76c00000000002a74dd0000000000190c1900000000000e0bab000000000007680f0000000000039e9a0000000000019b32000000000000a0d600000000000034f60000000000000d9b000000000000025f000000000000003500000000000000010000000000000000
  | 8 => 0x2655f5800000000017ceb700000000000e30ec0000000000080e90800000000004502580000000000225d2000000000000f9ec00000000000064e980000000000022b9800000000000098500000000000001d80000000000000032800000000000000180000000000000000000001a5c38000000000011e2d800000000000bbf200000000000076c140000000000047a180000000000028d100000000000015a80000000000000a7ac00000000000047b800000000000019c8000000000000072000000000000001440000000000000018000000000000000000059875a16000000002ef5736c0000000017486d20000000000acbf34e00000000049e0ed60000000001c987c800000000009c225000000000002d3ab200000000000a7fe6000000000001c7640000000000002fb0000000000000023600000000000000060000000000000000000035e4c950000000001e8a18e00000000010764a0000000000085c55200000000003f350100000000001b507c00000000000a8a4800000000000381dc000000000000f42500000000000031a20000000000000668000000000000005e00000000000000010000000000000000
  | 9 => 0x267293000000000017e16d80000000000e3cac8000000000081597000000000004541880000000000227df000000000000fae1000000000000654b80000000000022d8000000000000098a80000000000001d78000000000000032000000000000000180000000000000000000001afb78000000000012570800000000000c11a0000000000007a4cc0000000000049f98000000000002a4b00000000000016880000000000000af540000000000004b780000000000001b5800000000000007a0000000000000015c0000000000000018000000000000000000007702d3a0000000004405284000000000250aa24000000000130ba320000000000922e7e000000000040633800000000001977d8000000000008c2e60000000000027f420000000000008b8c000000000000144c000000000000017a0000000000000006000000000000000000000482a1100000000002c957e00000000001a699000000000000ee26d000000000007e549000000000003e304000000000001bd98000000000000b0570000000000003af90000000000000f7a00000000000002c8000000000000004100000000000000010000000000000000
  | 10 => 0x1d70a8d80000000010cf2c4800000000092481500000000004b19a8800000000023f58180000000000fcced0000000000063ada000000000002223f0000000000009ab5800000000000217380000000000004cb0000000000000057800000000000000180000000000000000000011c6fa40000000000af8af8000000000067de7000000000003a73c800000000001ef4a400000000000f3570000000000006cb80000000000002ae70000000000000e4c40000000000003bc80000000000000ab000000000000000f800000000000000040000000000000000000009065e8000000000059350a000000000034d83200000000001dc6ea00000000000fcafe000000000007c5b40000000000037aa40000000000016030000000000000759c0000000000001ec6000000000000057e000000000000007e000000000000000200000000000000000000005655a00000000000399ae00000000000251660000000000016e18000000000000d67400000000000075cc0000000000003b9c0000000000001b120000000000000a96000000000000035200000000000000ba000000000000001400000000000000000000000000000000
  | 11 => 0x16bdbc3b000000000bf1667a8000000005ee21f78000000002c134c080000000012e394480000000007546e900000000002825e300000000000bad5b000000000002b9a4000000000000770d8000000000000c9880000000000000978000000000000001800000000000000000000dca029c0000000007d426e000000000043ac348000000000227644c00000000010563540000000000716a6000000000002bfdb000000000000ebcac0000000000040b4c000000000000d5400000000000001c1800000000000001ac000000000000000400000000000000000000700365c0000000003facebc0000000002273d8a000000000119377a00000000008599b600000000003a20180000000000169f840000000000079d020000000000021a380000000000006fe40000000000000ef600000000000000ea000000000000000200000000000000000000043700d0000000000296ce70000000000185ff700000000000d9fd100000000000727aa0000000000037a5e000000000001884600000000000097de000000000000313b0000000000000c510000000000000209000000000000002700000000000000000000000000000000
  | 12 => 0x247bf10000000000168e0e80000000000d5f158000000000078a8b00000000000400ed800000000001f8f9000000000000e253000000000000599e8000000000001df800000000000007d9800000000000016680000000000000200000000000000000800000000000000000000138b7d40000000000c2751000000000007414d8000000000042039c00000000002367fc000000000011ab400000000000080d10000000000003426c0000000000011fe40000000000004f100000000000000f48000000000000019c000000000000000c0000000000000000000000d2a8e000000000008ee94000000000005dd54000000000003b4520000000000023bc20000000000014598000000000000ac98000000000000536600000000000023960000000000000cbc000000000000037c000000000000009a000000000000000a000000000000000000000075924000000000005074e00000000000355e000000000000221eb0000000000014dfc000000000000c1a400000000000069000000000000003441000000000000173400000000000008ca00000000000002a00000000000000087000000000000000c0000000000000000
  | 13 => 0x1c3e3ed8000000001010dd900000000008b30d300000000004712d6800000000021cd7e80000000000eb9e6000000000005bdba000000000001efa5800000000000893f8000000000001ca300000000000003d9000000000000003c800000000000000080000000000000000000010b9fa00000000000a43a000000000000608200000000000035dac800000000001c38c000000000000dadc000000000000600800000000000024f48000000000000bde00000000000002ec000000000000007800000000000000088000000000000000000000000000000000000770e4a60000000004408dba000000000250a7640000000001309f200000000000920fa600000000004049f400000000001966c8000000000008b92a0000000000027aa600000000000089d600000000000013dc000000000000016c000000000000000600000000000000000000046bd5b00000000002b9fb6000000000019c97600000000000e7e44000000000007a99d000000000003c18c000000000001ac34000000000000a82a000000000000379f0000000000000e5a0000000000000282000000000000003800000000000000010000000000000000
  | 14 => 0x31ebd0000000000021b59000000000001602c000000000000dcf780000000000084210000000000004a7600000000000026f0000000000000127880000000000007ad00000000000002a300000000000000ac0000000000000019800000000000000100000000000000000000013e34a40000000000c61f8000000000007671d80000000000437970000000000024435c00000000001224000000000000084a500000000000035e500000000000012ad40000000000005280000000000000100800000000000001b0000000000000000c00000000000000000005bb160e600000000302ef8680000000017f128ec000000000b217cde0000000004c663260000000001daea300000000000a2d2d800000000002f72f200000000000b1a26000000000001e6d800000000000033d400000000000002760000000000000006000000000000000000003728ff00000000001f5054000000000010ea493000000000089cbcc0000000000414dbf00000000001c52b800000000000afa8e000000000003ac9200000000000101aa00000000000034e800000000000006ed000000000000006800000000000000010000000000000000
  | 15 => 0x1da99f980000000010f254580000000009394eb00000000004bd4f580000000002458b180000000000ffda7000000000006509e0000000000022ad50000000000009d91800000000000223280000000000004ed000000000000005a800000000000000180000000000000000000011706bc0000000000abe97800000000006583d8000000000038fcec00000000001e16d400000000000eba100000000000068c100000000000029104000000000000d8ec00000000000037e800000000000009c800000000000000dc00000000000000040000000000000000000008ed87e00000000005827cc00000000003427c400000000001d57cc00000000000f884a0000000000079ff800000000000366d800000000000156c800000000000071b60000000000001d74000000000000052c000000000000007400000000000000020000000000000000000004a199700000000002ddcd400000000001b39ca00000000000f61030000000000082e150000000000040a10000000000001d0bc000000000000b8a70000000000003e03000000000000105400000000000002ee000000000000004300000000000000010000000000000000
  | 16 => 0x1fc46a00000000001368b100000000000b58c60000000000064ae080000000000345b4000000000001921e000000000000ae3c00000000000041e980000000000014a600000000000004e300000000000000ba000000000000000a8000000000000000000000000000000000000e0deeb80000000007fdea5c0000000004535dfc0000000002352aa800000000010ca34c000000000074f35800000000002d8e3800000000000f58dc0000000000043e90000000000000e2640000000000001e6400000000000001e0000000000000000400000000000000000000083d2c8000000000050cdd800000000002f6c9000000000001a6cbe00000000000dd2b0000000000006af80000000000002ed000000000000011f460000000000005bd800000000000016780000000000000390000000000000003e0000000000000000000000000000000000000435d360000000000295b96000000000018513a00000000000d94160000000000071eec000000000003744c000000000001846400000000000095a0000000000000301a0000000000000bda00000000000001e6000000000000002200000000000000000000000000000000
  | 17 => 0x1e2d0c000000000012593700000000000aaa3c000000000005df5e80000000000306d80000000000016faa0000000000009cd80000000000003a09800000000000119400000000000003ed00000000000000840000000000000004800000000000000000000000000000000000b4510c1c000000005e9dd800000000002eeef9100000000015c64e18000000000951420c00000000039bcac000000000013b734000000000005b71b80000000000153edc0000000000039ac000000000000061100000000000000498000000000000000c000000000000000000006b7d0380000000003ce4da800000000020d080e00000000010a8d3600000000007de36e0000000000365eb0000000000014f6ec000000000006f812000000000001e47c00000000000062580000000000000cb200000000000000be00000000000000020000000000000000000036b05630000000001f067d300000000010bf0900000000000884b24000000000040852500000000001bf21600000000000ad0800000000000039c93000000000000fc9f00000000000033b500000000000006c0000000000000006600000000000000010000000000000000
  | 18 => 0x18e83b58000000000e033c9800000000077d09e80000000003c364980000000001c13eb00000000000bee1b000000000004805900000000000173a8000000000000607e800000000000123280000000000002098000000000000014800000000000000000000000000000000000ac7b405c000000005a247d78000000002c7ff29000000000148669540000000008b811f400000000035878b0000000000120e6e00000000000525934000000000012aaec0000000000030bc80000000000004c7000000000000003140000000000000004000000000000000000006691dac00000000039db52a0000000001f042180000000000fa58940000000000754c08000000000032249400000000001312800000000000063856000000000001a44400000000000051660000000000000998000000000000007000000000000000000000000000000000000034252990000000001d744850000000000fd0d1b00000000007fe7bc00000000003c1242000000000019c182000000000009d56e0000000000033927000000000000db4f0000000000002aeb0000000000000525000000000000003e00000000000000000000000000000000
  | 19 => 0x296f8b000000000019e4a100000000000f8c1c000000000008e762800000000004d11b0000000000026e0e0000000000011f7000000000000076938000000000002a030000000000000c03000000000000027c000000000000004c800000000000000300000000000000000008ab1dabac000000042e91edec00000001e48d5e5800000000cb462244000000004dc9cd0c000000001a93adf80000000007de2db00000000001eec3d000000000005e676c00000000000c9194000000000000f728000000000000078c000000000000000c0000000000000000000533f246a000000002b6042e800000000155644480000000009cca73c00000000042419e20000000001941bd00000000000872980000000000026179c0000000000087faa0000000000015a9800000000000020a8000000000000013c000000000000000200000000000000000002a2edb21000000001600ed10000000000ad66f4e0000000004fc2b0e00000000021c49410000000000ce6ef8000000000045400c00000000001397d40000000000046531000000000000b4b8000000000000114200000000000000aa00000000000000010000000000000000
  | 20 => 0x1df3a0a800000000111ef6f0000000000952ff500000000004cb48c000000000024ca278000000000103266000000000006667e00000000000232990000000000009fc480000000000022a100000000000004f7000000000000005a000000000000000180000000000000000000012292d00000000000b399f400000000006a745400000000003c070000000000001fdd3c00000000000fb2c80000000000070968000000000002c9ac000000000000eef80000000000003ecc0000000000000b4c00000000000001080000000000000004000000000000000000000a6992400000000006823c000000000003e8d40000000000023d642000000000013653c000000000009c9f00000000000048680000000000001de22000000000000a97400000000000030700000000000000a000000000000000132000000000000000c000000000000000000003c6c3eb000000000229211400000000012d93ac00000000009b462d00000000004a9b3b000000000020ec5000000000000d0d300000000000048075000000000001498300000000000048340000000000000a8c00000000000000c500000000000000030000000000000000
  | 21 => 0x1714f214800000000c22d7a7800000000608cd400000000002cec36c800000000134a3678000000000780dfb000000000029392000000000000c0964000000000002d2de8000000000007c408000000000000d4800000000000000a18000000000000001800000000000000000000e0d374c0000000007fd6f780000000004530e68000000000234f92800000000010c85f4000000000074e2f000000000002d85b000000000000f54d00000000000043cdc000000000000e1c80000000000001e3800000000000001d800000000000000040000000000000000000070e6cf000000000040356d600000000022c1f1200000000011bd9ea000000000086ec6e00000000003abb4c000000000016de84000000000007b29c0000000000021ff400000000000070da0000000000000efe00000000000000e6000000000000000200000000000000000000044582c00000000002a0566000000000018c05800000000000dd9f400000000000748c80000000000038bec00000000000190c00000000000009b7a00000000000032840000000000000caa0000000000000218000000000000002800000000000000000000000000000000
  | 22 => 0x2293b4800000000015469180000000000c8ae780000000000706a1000000000003b2e9000000000001cd97000000000000cc030000000000004f4180000000000019c78000000000000676800000000000011080000000000000140000000000000000000000000000000000000f369ac00000000008b4f1680000000004bf9f74000000000272103c00000000012ce034000000000084c8d0000000000034a10800000000001223bc0000000000052d38000000000001211800000000000029cc00000000000002fc000000000000000c00000000000000000000093555e00000000005b2630000000000036150c00000000001e88040000000000103a6a00000000000801c000000000000398480000000000016d340000000000007a76000000000000203000000000000005c400000000000000840000000000000002000000000000000000000552a52000000000035516400000000002014e00000000000126abf000000000009fd9e0000000000050e500000000000025840000000000000f8a3000000000000587a00000000000019640000000000000540000000000000009f00000000000000060000000000000000
  | 23 => 0x25443f800000000017134800000000000db487000000000007bf020000000000041f7a80000000000209a0000000000000eaaa0000000000005d5a0000000000001f658000000000000848000000000000017d0000000000000022000000000000000080000000000000000000bac4f9c400000000624975a40000000030ebb3e80000000016ca06e80000000009ccbf1c0000000003d1902800000000015064f00000000000627ea400000000001730b4000000000004019c0000000000006e780000000000000550000000000000000c00000000000000000000717e1ae0000000004094aae00000000022fb97000000000011deed00000000000880f7a00000000003b4f9c00000000001723c0000000000007cf6e0000000000022a3600000000000073c20000000000000f9000000000000000f40000000000000002000000000000000000003936cd100000000020929a100000000011a76a600000000009061e4000000000044bfd100000000001dfd7200000000000bb56c000000000003f45900000000000118b10000000000003a9700000000000007da000000000000007a00000000000000010000000000000000
  | 24 => 0x1c7f92f000000000103828b80000000008c9965800000000047d6110000000000222ff180000000000ee743000000000005d04b000000000001f6198000000000008b020000000000001cf480000000000003de800000000000003c000000000000000080000000000000000000010bbd7c0000000000a449a400000000006088b4000000000035dc5400000000001c37b800000000000dabc8000000000005fe880000000000024dc0000000000000bce40000000000002e3c000000000000074c000000000000007c00000000000000000000000000000000000008b8f74000000000055ed6c000000000032b16c00000000001c6b7800000000000ef9e80000000000074ef80000000000033bf8000000000001421c00000000000068ec0000000000001a54000000000000045400000000000000500000000000000000000000000000000000003cb30cc00000000022bb5e500000000012eff9300000000009c007200000000004af1bd0000000000210f4200000000000d18660000000000048289000000000001491a00000000000047ab0000000000000a5500000000000000bc00000000000000030000000000000000
  | 25 => 0x1f34ce000000000013089d00000000000b1aba00000000000624768000000000032f1c00000000000185a6000000000000a7e40000000000003f038000000000001382000000000000048700000000000000a60000000000000008800000000000000000000000000000000000b7dcfd340000000060a02b400000000030041b48000000001652fc70000000000993b07c0000000003b87a0000000000014681b000000000005f1df00000000000163dc4000000000003ce40000000000000679800000000000004f0000000000000000c000000000000000000006dd299e0000000003e534a800000000021a7acc0000000001120ce2000000000081d0aa00000000003845a0000000000015cc880000000000074a52000000000001fef600000000000068e80000000000000dc400000000000000d200000000000000020000000000000000000038689b60000000002015683000000000115ec6300000000008de34a000000000043779300000000001d623e00000000000b7386000000000003dc1f000000000001116c00000000000038fd00000000000007a5000000000000007800000000000000010000000000000000
  | 26 => 0x19a33280000000000e75f9b00000000007c079600000000003e908980000000001d4fa800000000000c8742000000000004c3a40000000000018d9e80000000000068e000000000000014490000000000000262000000000000001b800000000000000000000000000000000000aef94358000000005b8d7248000000002d42248c0000000014e8ce200000000008e66c8c00000000036c6d500000000001289058000000000054e16800000000001359700000000000032eb800000000000050d400000000000003500000000000000004000000000000000000006851d580000000003aed85c0000000001fa4ca80000000000ffee2600000000007836300000000000338c88000000000013af900000000000067462000000000001b76800000000000056140000000000000a58000000000000007e000000000000000000000000000000000000358e62a0000000001e5240f00000000010537c000000000008478ea00000000003e78ac00000000001aec6e00000000000a59480000000000036c49000000000000ebee0000000000002f1900000000000005d8000000000000004c00000000000000000000000000000000
  | 27 => 0x2e216200000000001d109f0000000000119eb000000000000a349b800000000005989e000000000002deb20000000000015a8000000000000092b680000000000035ca000000000000101d00000000000003900000000000000079800000000000000600000000000000000008cf58f02800000004417af6f400000001eddf704c00000000cf909a38000000004f9b5a84000000001b45ce8800000000081a0bf80000000001ffc0140000000000623b1000000000000d300c00000000000106740000000000000820000000000000000c000000000000000000054ca1bc6000000002c3f721c0000000015ce2ac0000000000a094bee0000000004409baa0000000001a058d800000000008bd820000000000027a1d6000000000008e91e0000000000016f840000000000002340000000000000015e000000000000000200000000000000000002b351707000000001695854c000000000b268646000000000524d54400000000022f7da50000000000d6b9a800000000004871e4000000000014a73c000000000004aea3000000000000c384000000000000132200000000000000c400000000000000010000000000000000
  | 28 => 0x1c08f838000000000feecf0800000000089e1740000000000464d8c0000000000215f9e80000000000e80b9000000000005a270000000000001e40680000000000085058000000000001b6b800000000000039c00000000000000370000000000000000800000000000000000000e640b780000000008322718000000000471a534000000000245c8900000000001152aec000000000078fa5000000000002f434800000000000ff9500000000000046eb0000000000000ed080000000000001fcc00000000000001f00000000000000004000000000000000000007b2ebe6000000000468ebb6000000000268459c00000000013dbb96000000000098e386000000000043929c00000000001ad4180000000000094404000000000002a686000000000000946a0000000000001584000000000000018a000000000000000600000000000000000000052ad52000000000033a4a500000000001efdf7000000000011bc8200000000000995f7000000000004d4420000000000023a1e000000000000ea7900000000000052a8000000000000176b00000000000004c1000000000000008c00000000000000050000000000000000
  | 29 => 0x228c6b000000000015414300000000000c8725000000000007040d000000000003b136000000000001cc86000000000000cb620000000000004eea000000000000199d0000000000000665000000000000010b00000000000000130000000000000000000000000000000000000f70b6680000000008d85a440000000004d4418400000000027d7520000000000132c4a40000000000879768000000000035d508000000000012965c000000000005503000000000000128fc0000000000002adc0000000000000308000000000000000c000000000000000000000a940cc000000000069e79a00000000003faec600000000002487b8000000000013cc3e00000000000a01c4000000000004a22c000000000001ea46000000000000ade800000000000031a60000000000000a2a000000000000012c000000000000000a00000000000000000002f0c919f0000000018c663f6000000000c5726160000000005c0f3ca00000000027a141b0000000000f767f400000000005547fc00000000001906aa000000000005e91700000000000106920000000000001c7a000000000000016200000000000000030000000000000000
  | 30 => 0x174467b9000000000c3d4bc4000000000616c80d8000000002d5b17f000000000137d0b8800000000079602c000000000029b53700000000000c2ffa000000000002dc6e0000000000007df80000000000000d7a80000000000000a50000000000000001800000000000000000000e0cba2c0000000007fd1a90000000000452d6b8000000000234d61800000000010c70f4000000000074d72000000000002d7f9000000000000f51f80000000000043bbc000000000000e1700000000000001e2800000000000001d800000000000000040000000000000000000070165380000000003fb21680000000002272656000000000118fa600000000000855ace000000000039eee00000000000167f5c0000000000078b3c000000000002121c0000000000006d080000000000000e4a00000000000000d800000000000000020000000000000000000039ab5f600000000020d8c6700000000011cfb4f000000000091bf7c000000000045708300000000001e4f2600000000000bd70e00000000000400290000000000011bfc0000000000003b3900000000000007e9000000000000007a00000000000000010000000000000000
  | 31 => 0x1617d0f7000000000b91bb780000000005b982258000000002a5d542000000000120ea1980000000006f5250000000000025bf8300000000000ad54c0000000000027a7200000000000068d80000000000000a76800000000000006e0000000000000000800000000000000000000d51df74000000000789adf800000000040e77d400000000020e4f640000000000f8014800000000006ac770000000000028fda800000000000d88e4000000000003a28c000000000000b90800000000000016cc00000000000001240000000000000000000000000000000000006a289040000000003c097f600000000020484f00000000001057e9000000000007b0a38000000000034de2c0000000000143c70000000000006a706000000000001c62c000000000000593a0000000000000ac0000000000000008400000000000000000000000000000000000003f4600000000000026a158000000000016900800000000000c7f320000000000067ce00000000000031b600000000000015770000000000000813a000000000000282000000000000009580000000000000158000000000000001200000000000000000000000000000000
  | 32 => 0x11c955b0a00000000899354c8000000003e6b5225800000001a42cc5e000000000a15a086800000000375d11c000000000107a8db000000000041389f00000000000c9009000000000001b1ec00000000000021fe8000000000000110000000000000000180000000000000000000ac671f7c000000005a180250000000002c7885a000000000148234b40000000008b5d3740000000003575be0000000000120664000000000005225cc000000000012998c00000000000307300000000000004ba00000000000000304000000000000000400000000000000000005671fea2000000002d2e70e200000000164e3928000000000a49dc0800000000045ed6d20000000001ad4314000000000090c1000000000000293bb60000000000095572000000000001849e00000000000025c8000000000000017c00000000000000020000000000000000000033eb21d0000000001d505ba0000000000fbb7ad00000000007f26a200000000003bab520000000000198e7c000000000009be5a0000000000032fe2000000000000d8230000000000002a0e00000000000004fb000000000000003a00000000000000000000000000000000
  | 33 => 0x1d3dd6b00000000010aba5f800000000090c91f80000000004a22968000000000235e3180000000000f75ff0000000000060cc70000000000020c43000000000000919e0000000000001e64800000000000040c800000000000003d8000000000000000800000000000000000000138f7d00000000000c286bc0000000000740cc4000000000041efd8000000000023517c0000000000119718000000000007fd8800000000000337ec00000000000119b80000000000004c040000000000000e1c00000000000001500000000000000004000000000000000000007d9115600000000048032ca000000000275db540000000001453f6200000000009cc8460000000000456e6400000000001ba0680000000000099024000000000002bdb60000000000009996000000000000162c000000000000018e00000000000000060000000000000000000005c1d7100000000003a058400000000002329440000000000145b0900000000000b2791000000000005b710000000000002b11000000000000123210000000000006a590000000000001fa400000000000006e400000000000000e100000000000000090000000000000000
  | 34 => 0x1aad2790000000000f16e71800000000081d798000000000041be4200000000001eef8e00000000000d4a9300000000000515e4000000000001ab8f80000000000071c3000000000000163a80000000000002a4000000000000001f000000000000000000000000000000000000bbf71db00000000062f3c73c0000000031457d440000000016f6638c0000000009e0fd540000000003d9ec180000000001536d680000000000636b5800000000001769080000000000040ac40000000000006f3c0000000000000554000000000000000c000000000000000000006fafa3e0000000003f733f0000000000224d93c000000000117b2b2000000000084afaa0000000000399c300000000000165b280000000000077d4a0000000000020d960000000000006be00000000000000e1400000000000000d20000000000000002000000000000000000003881d8600000000020209d2000000000116260d00000000008de36b000000000043630b00000000001d4bc400000000000b6292000000000003d1f30000000000010c84000000000000372e0000000000000733000000000000006b00000000000000010000000000000000
  | 35 => 0x15b9c9b0000000000b5c155300000000059c5b34800000000296e2ce000000000119c54b80000000006c30de00000000002484c900000000000a6a310000000000025c71000000000000627d000000000000099780000000000000600000000000000000800000000000000000000cccaaa000000000073706700000000003dd42400000000001f26b880000000000e91cc00000000000636420000000000025a70000000000000c33180000000000032ee00000000000009a50000000000000114000000000000000a800000000000000000000000000000000000591f7006000000002eb355ee0000000017202684000000000ab4a636000000000491645a0000000001c327bc000000000099391800000000002c0f2000000000000a1aae000000000001acc20000000000002aec00000000000001c200000000000000020000000000000000000034d7a140000000001ddf142000000000100db14000000000081f31800000000003d17a800000000001a387400000000000a0548000000000003495e000000000000df8c0000000000002b9e000000000000052c000000000000003c00000000000000000000000000000000
  | 36 => 0x273d31000000000018670f00000000000e9184000000000008490b800000000004719900000000000237a20000000000010290000000000000689a800000000000240900000000000009dd00000000000001e40000000000000031800000000000000100000000000000000000c9227598000000006a7d6048000000003561f82000000000191486b8000000000ae59ad800000000044cfd9000000000018111800000000000732b9000000000001bea58000000000005077800000000000094200000000000000808000000000000001800000000000000000047994f22a000000022a1273d800000000fb8720e40000000069e460060000000028b2197e000000000dfa1f6000000000042a49f80000000001082cee000000000032fdf2000000000006e6d80000000000008b2c0000000000000466000000000000000600000000000000000002b0261900000000016782464000000000b1647a100000000051c55d800000000022b55770000000000d4da68000000000047af8200000000001462780000000000049a72000000000000befc000000000000127700000000000000b800000000000000010000000000000000
  | 37 => 0x1bef40f0000000000fdf0bc0000000000894d5c800000000045faeb000000000021344580000000000e6ba4000000000005991d000000000001e06000000000000083ce0000000000001b18000000000000038b8000000000000035000000000000000080000000000000000000bee5a63c00000000649fe35400000000322e0a7800000000176d9324000000000a19ec2c0000000003f2dac800000000015d3570000000000066be4800000000001856dc0000000000043cec000000000000760800000000000005bc000000000000000c0000000000000000000072eae7a00000000041713e0000000000237aed8000000000122474600000000008a46c200000000003c591000000000001792e0000000000007f77600000000000235da00000000000076300000000000000fd800000000000000f60000000000000002000000000000000000003a5de82000000000214666300000000012102e7000000000093ffd30000000000469f0b00000000001ee22600000000000c17ce000000000004193c00000000000124200000000000003d450000000000000841000000000000008100000000000000010000000000000000
  | 38 => 0x12fd13bde8000000093af00d400000000437154cd800000001c98d894800000000b164e7e0000000003d99fc8000000000129edab00000000004b3be980000000000eead78000000000021a440000000000002d5e80000000000001a2800000000000000300000000000000000000b58f866c000000005f53e020000000002f5219600000000015f943ec000000000969b22c0000000003a68c6000000000013fb2e000000000005ce6cc000000000015a88c000000000003b180000000000000644000000000000004cc000000000000000c00000000000000000005c32417a000000003076ff960000000018175c70000000000b3484c00000000004cf2c4e0000000001de9b0c0000000000a4330000000000002fe33e00000000000b3732000000000001ec7a00000000000034900000000000000284000000000000000600000000000000000002eba1158000000001896ce26000000000c3cf6bf0000000005b3539600000000027373650000000000f4707c00000000005415ee0000000000189b20000000000005c9be000000000000ff9a0000000000001b79000000000000015200000000000000030000000000000000
  | 39 => 0x160a4bc4000000000b8a22720000000005b574aa8000000002a3cd7180000000011ff8db80000000006eec98000000000025999d00000000000ac955800000000002777500000000000068520000000000000a69800000000000006d800000000000000080000000000000000000b2982194000000005d9af600000000002e5d98f8000000001578de3400000000092a8c64000000000389e440000000000133f170000000000058ab3c00000000001460f40000000000036400000000000000578800000000000003a400000000000000040000000000000000000068b72fe0000000003b2b74e0000000001fc90220000000001012fa4000000000078dd7c000000000033dcec000000000013d274000000000006819e000000000001bb9200000000000057120000000000000a7e00000000000000800000000000000000000000000000000000003537c8c0000000001e1a7fc0000000001030e7c00000000008330b800000000003dc03800000000001a8b7800000000000a2a780000000000035814000000000000e4740000000000002ce40000000000000564000000000000004000000000000000000000000000000000
  | 40 => 0x15435bc2000000000b198aba800000000578da8a80000000028514be8000000001117d77800000000068af5d00000000002333cd000000000009fe4400000000000240b70000000000005d598000000000000909800000000000005b800000000000000080000000000000000000ac1508c80000000059e925f4000000002c5f157400000000147534dc0000000008afa80c000000000354b08800000000011f5fc8000000000051cfc000000000001282e000000000000302cc0000000000004b0c00000000000002f4000000000000000400000000000000000048c5c6b6a0000000233dd233a0000000100596cb4000000006c1c16580000000029a2881e000000000e5615a40000000004493638000000000110f79e000000000034fbd20000000000073a66000000000000937c00000000000004bc000000000000000600000000000000000002b6bea8f0000000016b51201000000000b37d71a00000000052dd136000000000233d8b50000000000d8aafa000000000049398c000000000014ed25000000000004c2fb000000000000c80f00000000000013ce00000000000000d000000000000000010000000000000000
  | 41 => 0x1177c689b0000000086e6a629800000003d17d3eb8000000019a56eb70000000009d2670c80000000035bdb8f0000000000fed70300000000003eafd380000000000bfbac00000000000199868000000000001f9c80000000000000fa000000000000000180000000000000000008d47a308c000000044401b62400000001ef08830800000000d00deefc000000004fcae74c000000001b558ca800000000081e6590000000000200aff00000000000625f8c00000000000d33dc00000000000106f80000000000000834000000000000000c00000000000000000005392f34a000000002b9048700000000015707f180000000009da303c00000000042a9f62000000000196ff200000000000884fe00000000000267db40000000000089d0a00000000000161100000000000002198000000000000014c000000000000000200000000000000000023b7a3c53000000011452df20000000007d65d6020000000034c50249000000001444e9330000000006f4ea980000000002123c4400000000008334c5000000000019487300000000000369f8000000000000449e000000000000022900000000000000030000000000000000
  | 42 => 0x1c90e458000000001042d3200000000008cfe390000000000480ec90000000000224e0680000000000ef61c000000000005d6fe000000000001f8cb0000000000008bef8000000000001d3600000000000003eb000000000000003d000000000000000080000000000000000000102f608800000000094f2a0000000000051b5e000000000002a608640000000001489ff80000000000928fe000000000003adf00000000000014a6a400000000000609a80000000000015d6000000000000035800000000000000444000000000000001800000000000000000000827793c0000000004b1ae2c000000000293e950000000000156b1ba0000000000a65fcc00000000004a5d8800000000001df64000000000000a8e460000000000031b3c000000000000b5a40000000000001c500000000000000252000000000000000c000000000000000001d0e28262b0000000cfaf208eb00000005680831a500000002126118bd00000000b7c9b6d00000000038433b5e000000000ebb69720000000003263dfe00000000008324e900000000000e7d85000000000000e44b000000000000055300000000000000060000000000000000
  | 43 => 0x1cf35e3000000000107f4ae00000000008f373c8000000000494cab000000000022f4dd80000000000f4728000000000005faad000000000002069a000000000000906a0000000000001e56000000000000041b8000000000000041000000000000000080000000000000000000107acd9800000000097de95000000000053729a00000000002b5c36c00000000015102d8000000000096b70000000000003cbe80000000000015660c0000000000064a580000000000016e9000000000000038a0000000000000048c00000000000000180000000000000000000009f85ac0000000000634ff000000000003b5c80000000000021ce5600000000001228d400000000000913b00000000000042480000000000001ade6000000000000945c00000000000028a000000000000007c000000000000000c6000000000000000400000000000000000002eda3b6c0000000018a8985d000000000c4648070000000005b7e58a00000000027584cd0000000000f548e2000000000054635e000000000018b22d000000000005ceea00000000000100430000000000001b71000000000000014c00000000000000030000000000000000
  | 44 => 0x1b19b788000000000f5afb380000000008467eb800000000043375f80000000001fbc2100000000000db1ef000000000005459b000000000001bf200000000000007893800000000000181880000000000002fc8000000000000026800000000000000000000000000000000000bb070374000000006265ebf00000000030f558b80000000016cb76080000000009cb6ebc0000000003cfed6000000000014f3d50000000000061e208000000000016f0c4000000000003ee900000000000006ae80000000000000508000000000000000c000000000000000000007339a4200000000041a20ca0000000002397f6c0000000001234e8000000000008ad36200000000003c9ef4000000000017b29800000000000804420000000000023a420000000000007766000000000000101400000000000000fc000000000000000200000000000000000002f79c88f000000001903050c000000000c7707240000000005d0a73700000000028136d30000000000fa5630000000000056561000000000001957ef000000000005fbef000000000001096c0000000000001ca4000000000000015f00000000000000030000000000000000
  | 45 => 0x1588aada800000000b407d1180000000058da32b00000000028f81f1000000000116577480000000006abd9b000000000023f99e00000000000a3dba800000000002510e8000000000006062800000000000095d000000000000005e000000000000000080000000000000000000b01b5184000000005c30ccd8000000002d998e28000000001514cefc0000000008fafd4400000000037530f000000000012be250000000000055f50c000000000013a1840000000000033c680000000000005258000000000000035c00000000000000040000000000000000000581c62dc000000002e1eaf2c0000000016ceda16000000000a8aa87600000000047d27660000000001ba3368000000000095ab0c00000000002ad5aa000000000009c1c800000000000199c4000000000000285a000000000000019e0000000000000002000000000000000000003492f530000000001db5f3c0000000000ff639300000000008128f800000000003cb26e00000000001a0a30000000000009f28600000000000342ea000000000000ddcd0000000000002b4c0000000000000525000000000000003c00000000000000000000000000000000
  | 46 => 0x1808c9d8800000000cacb7cc000000000652ef0b0000000002f44cde8000000001464fa380000000007fa8a400000000002c245a00000000000d006e800000000003158680000000000089b00000000000000f0100000000000000ba8000000000000001800000000000000000000e94815400000000084fdce8000000000483160000000000024f80f800000000011a410400000000007b7050000000000030572000000000001063300000000000049094000000000000f55800000000000021200000000000000208000000000000000400000000000000000000862cdb40000000004d5fd2c0000000002a92c4000000000016280d60000000000ac85dc00000000004d518800000000001f3d8000000000000b098a0000000000034164000000000000be640000000000001d80000000000000025e000000000000000c00000000000000000023c367a350000000114bd61c3000000007d9f007a0000000034e1cdeb000000001452549f0000000006fa96b6000000000214592c000000000083dea4000000000019723900000000000370f5000000000000452e000000000000022900000000000000030000000000000000
  | 47 => 0x1b644118000000000f87f2b800000000086061880000000004418b38000000000202e7b00000000000de7170000000000055ba5000000000001c6f20000000000007aca8000000000001888800000000000030780000000000000268000000000000000000000000000000000000105e7180000000000a05e6800000000005dfe28000000000034479000000000001b483000000000000d2690000000000005ba100000000000022e08000000000000b0280000000000002a1800000000000006580000000000000060000000000000000000000000000000000005f1f91ec00000000321cd7660000000018f8fa9a000000000ba603b40000000005042a420000000001f528bc0000000000acba74000000000032a5ce00000000000befa00000000000020f9a000000000000389600000000000002b00000000000000006000000000000000000003a57c6600000000021423ea000000000120d755000000000093e45e0000000000468e8b00000000001ed8cc00000000000c12e200000000000416e200000000000123240000000000003cee000000000000082b000000000000007e00000000000000010000000000000000
  | 48 => 0x163b66b0800000000ba5bafb0000000005c42e820000000002ab303d800000000123682c80000000007060c2000000000026253800000000000af5f280000000000282dc8000000000006a690000000000000aa2000000000000006f8000000000000000800000000000000000000d62641c000000000793c07000000000041457bc0000000002118f180000000000f9b05800000000006b9580000000000029567800000000000daa40000000000003ace4000000000000bb70000000000000172400000000000001280000000000000000000000000000000000059716d8a000000002edfab70000000001736b2c4000000000abf4832000000000495f2520000000001c4df60000000000099c36800000000002c2f9e00000000000a1e9a000000000001ac300000000000002a9c00000000000001ba00000000000000020000000000000000000035fa2300000000001e9286e0000000001077f70000000000085b0bd00000000003f132000000000001b31d400000000000a74a00000000000037533000000000000ee100000000000002f5a00000000000005d0000000000000004900000000000000000000000000000000
  | 49 => 0x1c96cd38000000001044d9800000000008cff570000000000480350000000000022403280000000000eeaa0000000000005cf3a000000000001f46400000000000089e18000000000001c7800000000000003bd00000000000000380000000000000000800000000000000000000ebeada00000000008695948000000000491c8dc000000000257842000000000011e53fc00000000007d55f00000000000312098000000000010aa80000000000004a488000000000000f9180000000000002164000000000000020000000000000000040000000000000000004873910a4000000023136411200000000ff0f0b56000000006b862ca200000000296405e2000000000e3e97c400000000044175dc00000000010ecd180000000000347ef8000000000007253e000000000000910a0000000000000496000000000000000600000000000000000002bf031fc0000000016ff4084000000000b5f5451000000000541910b00000000023cffdf0000000000dc869000000000004aaa12000000000015621b000000000004e096000000000000cd64000000000000145700000000000000d300000000000000010000000000000000
  | 50 => 0x1693ac5f000000000bd722618000000005de6ac28000000002b845188000000001297255800000000072e937000000000027159900000000000b418a00000000000295be0000000000006dbe8000000000000af580000000000000718000000000000000800000000000000000000d66610400000000079506a800000000041446e4000000000210fa140000000000f908e800000000006b0e50000000000028fcc800000000000d784400000000000395fc000000000000b358000000000000153c00000000000000f40000000000000000000000000000000000006e6c1e80000000003ea2c8600000000021cc174000000000112e2b2000000000081f8a00000000000382cbc000000000015a8380000000000072f08000000000001f00800000000000062da0000000000000c1c0000000000000096000000000000000000000000000000000003015b80e00000000195a7a9a000000000ca595f10000000005e7ef1100000000028bffb10000000000fee0bc0000000000580722000000000019e0fb0000000000061e780000000000010f9e0000000000001d47000000000000016500000000000000030000000000000000
  | 51 => 0x123ef5911800000008d699b3580000000404f8374000000001b21c169800000000a7429c580000000039a0473000000000113d824000000000044afea00000000000d58e5800000000001d2b680000000000025380000000000000130800000000000000180000000000000000000afa9d2ec000000005bedcdc8000000002d73bb680000000015008ee40000000008f0d2340000000003707970000000000129e7b00000000000553aac000000000013683c0000000000032ed80000000000005038000000000000033400000000000000040000000000000000000599653c4000000002ef650860000000017440196000000000ac6b54e000000000499d6760000000001c6c20c00000000009a970c00000000002c80f000000000000a38a0000000000001b28a0000000000002b9a00000000000001ca000000000000000200000000000000000000350c1b20000000001dff44800000000010209aa0000000000829bf600000000003d703400000000001a637000000000000a183400000000000350b2000000000000e1ee0000000000002c380000000000000546000000000000003e00000000000000000000000000000000
  | 52 => 0x1770d469800000000c568ab20000000006246fe20000000002dca87680000000013b1fa580000000007ad0a800000000002a44b000000000000c604e800000000002e9cd80000000000080c20000000000000dda00000000000000aa800000000000000180000000000000000000bfc8731400000000652049380000000032732dd0000000001790a534000000000a2a785c0000000003f9fe7000000000015ff560000000000067a804000000000018964400000000000449c800000000000077b000000000000005d4000000000000000c00000000000000000005eeeac720000000032018c820000000018ea8874000000000b9ed74e000000000500deee0000000001f3c9a40000000000ac39b80000000000327e0c00000000000be60a0000000000020e0e000000000000387c00000000000002b20000000000000006000000000000000000003b2fec100000000021c609b000000000125a50e0000000000968c38000000000047eeb100000000001f80f600000000000c5b3c00000000000431fb0000000000012b810000000000003edd0000000000000872000000000000008200000000000000010000000000000000
  | 53 => 0x164b5362000000000baed7638000000005c9265c8000000002adbf57800000000124a32f800000000070ebf70000000000265c8900000000000b091a000000000002885f0000000000006ba08000000000000acf8000000000000072800000000000000080000000000000000000b6523804000000005fb7d638000000002f8146b000000000160d0fd400000000097097640000000003a829d000000000013f9f0000000000005c8cec0000000000156e640000000000039a680000000000005e7000000000000004040000000000000004000000000000000000006d410960000000003df03e00000000002166a8600000000010f7ea400000000008049fc0000000000376ad00000000000155b8c00000000000715e0000000000001e9ea00000000000062100000000000000c2a000000000000009c0000000000000000000000000000000000268e92b5c000000012c37a006000000008947eece000000003a4cbf7d0000000016a4f5820000000007e17a6c000000000263795c00000000009aedad00000000001ed9300000000000045efa0000000000005ee2000000000000036d00000000000000060000000000000000
  | 54 => 0x15c25acd800000000b6183aa00000000059fa72d000000000298c95c80000000011accd680000000006cb508000000000024c0e600000000000a82408000000000026487800000000000649a00000000000009f70000000000000068800000000000000080000000000000000000b0a2d744000000005c7ea0c4000000002dc42bc000000000152adc0c000000000905a564000000000379ed0800000000012dc6a00000000000569d98000000000013d224000000000003471c00000000000053e0000000000000037400000000000000040000000000000000004977091600000000239a3adb400000001033129f2000000006d6a8dbe000000002a2ffe1a000000000e8c117800000000045b4b3400000000011612d2000000000036205c000000000007693c00000000000097ee00000000000004e6000000000000000600000000000000000002bdc50bd0000000016f46cc6000000000b59c62e00000000053eeaff00000000023bd9490000000000dc155c00000000004a857c0000000000155923000000000004df65000000000000cd8a000000000000147200000000000000d700000000000000010000000000000000
  | 55 => 0xebc80c0c18000000697389bf080000002bfa80b31800000010e10e702000000005dc1c098000000001cc4342d00000000078db5df00000000019edf6f800000000043cde88000000000078a5780000000000077de80000000000002d3000000000000000300000000000000000008ddab13e80000000448d4a61800000001f16d190c00000000d12a06dc0000000050445504000000001b84777000000000082e57f800000000020544dc0000000000636b5000000000000d5fa80000000000010b34000000000000085c000000000000000c00000000000000000047cc6cf7e000000022baf260800000000fc4a936c000000006a3a23da0000000028d46156000000000e06508000000000042e05580000000001091c8a0000000000332b8e000000000006eca80000000000008b94000000000000046a0000000000000006000000000000000000247f0dc7b000000011ad89c6100000000809f64aa00000000364277fd0000000014e74b43000000000733613a0000000002275e7400000000008940ae00000000001aa90b000000000003a3df0000000000004a56000000000000026300000000000000030000000000000000
  | 56 => 0x20a922d00000000012cb7a38000000000a50e5f800000000055a665000000000029893380000000001288cb00000000000772a70000000000029cd7800000000000c3600000000000002c0480000000000006ac8000000000000084000000000000000280000000000000000000c22bec240000000066778ab800000000332a32980000000017ec6914000000000a552c5c00000000040c1cd0000000000166cbd0000000000069decc0000000000192b5400000000000466e80000000000007b480000000000000604000000000000000c0000000000000000000081fbc900000000004ac720e0000000002907c520000000001548a180000000000a51506000000000049a28c00000000001d942400000000000a5f9200000000000307c4000000000000aef20000000000001a9e0000000000000214000000000000000a0000000000000000000048833340000000002a1385a00000000017522a00000000000c3e277000000000060561c00000000002bbcfc000000000011f7000000000000067c11000000000001f824000000000000781e00000000000013e000000000000001cb000000000000000c0000000000000000
  | 57 => 0x1a87baf8000000000f00c040000000000811053800000000041551200000000001ebc4300000000000d34040000000000050d47000000000001a8e50000000000007130800000000000163000000000000002a88000000000000020000000000000000000000000000000000000b3ec55dc000000005e521330000000002eba25400000000015a41ebc00000000093cd2b4000000000390a020000000000135f80000000000005917a400000000001466ac0000000000035e500000000000005580000000000000036c0000000000000004000000000000000000006cfe07e0000000003dc570a000000000214c54200000000010e86e200000000007fbffc00000000003722f400000000001539340000000000070738000000000001e49200000000000060860000000000000bde000000000000009600000000000000000000000000000000000301ee3ed00000000195ec172000000000ca74e960000000005e8743a00000000028c0aaf0000000000fec9c4000000000057f0c4000000000019d3b800000000000618c10000000000010dde0000000000001cf2000000000000015e00000000000000030000000000000000
  | 58 => 0x21644a5000000000133eaff8000000000a94d7b800000000058077a00000000002ac9d380000000001324fb000000000007b78f000000000002b780800000000000cbf80000000000002e208000000000000700800000000000008900000000000000028000000000000000000920709948000000046bd901440000000202c81c0c00000000d934d9540000000053b3b5c4000000001cd818c80000000008a1ce780000000002267e2000000000006b08f000000000000ea15c0000000000012ab4000000000000097c000000000000000c000000000000000000058e484c6000000002e91eefa00000000170e23f8000000000aab80c200000000048d12aa0000000001c14aa4000000000098819000000000002bd26c00000000000a0a5e000000000001a9860000000000002a8800000000000001be000000000000000200000000000000000002bddd4740000000016f30c4d000000000b579d2100000000053cf61100000000023a6e7f0000000000db353a00000000004a0e220000000000152338000000000004cb8e000000000000c80b000000000000137700000000000000c300000000000000010000000000000000
  | 59 => 0x1ad09720000000000f2c99c000000000082a3020000000000422f4f00000000001f2a7400000000000d66e00000000000052224000000000001b02b000000000000732e000000000000168c00000000000002ae000000000000001f000000000000000000000000000000000000b6963c4c000000005fd3d1a0000000002f89a07800000000160d32e400000000096e49b40000000003a5e46000000000013e1d9000000000005bc6140000000000151e1c000000000003828000000000000059e800000000000003a40000000000000004000000000000000000006e7084a0000000003ea5b7200000000021cdf9e000000000112f542000000000082037400000000003832a4000000000015ab2c0000000000073058000000000001f08600000000000062fe0000000000000c2200000000000000960000000000000000000000000000000000030e0aaa80000000019ccd0ea000000000ce2c9e5000000000606c06300000000029a677d000000000105047400000000005a5a9200000000001aa223000000000006511600000000000119560000000000001e6b000000000000017300000000000000030000000000000000
  | 60 => 0x1803639b000000000ca8a5bd80000000065016df8000000002f2748e80000000014534a480000000007f0daf00000000002bd83300000000000cdfcc00000000000309e400000000000086828000000000000e7080000000000000af80000000000000018000000000000000000939b1c8c4000000047908d05c000000020948d90c00000000dc33bb7c0000000054f9012c000000001d54b4e80000000008cbc3880000000002326f0400000000006dbde400000000000f1314000000000001362400000000000009fc000000000000000c000000000000000000059b1f704000000002f05f12c00000000174c691e000000000acaf75600000000049bd8360000000001c79f8800000000009aec5c00000000002c9d5200000000000a4060000000000001b4240000000000002bd200000000000001ce000000000000000200000000000000000002c6a304d00000000174263e3000000000b82418e00000000055289f500000000024494790000000000df912e00000000004bb94c000000000015afc4000000000004f125000000000000cf7d000000000000146200000000000000cf00000000000000010000000000000000
  | 61 => 0x1695d6e7000000000bd883698000000005df433c8000000002b8c411800000000129b8ed8000000000730df7000000000027273500000000000b491d000000000002988e0000000000006e968000000000000b2380000000000000768000000000000000800000000000000000000dcfb4080000000007d60cc000000000043ac348000000000226a3a000000000010481d0000000000070b0c000000000002b809000000000000e75b0000000000003e9f8000000000000c90000000000000018f8000000000000014000000000000000000000000000000000004e09559b600000002602cc3f8000000011665d9f0000000007660834e000000002e0c48c800000000100e0c180000000004e07eb800000000013d381000000000003f63ca0000000000090600000000000000c4f80000000000000722000000000000000c00000000000000000002f9e2f8700000000191695f5000000000c80e5460000000005d53fdf000000000283255b0000000000fb0ad20000000000568b8c00000000001962bc000000000005fc5f00000000000108db0000000000001c7a000000000000015d00000000000000030000000000000000
  | 62 => 0x16540f75800000000bb3db510000000005cbe4ec0000000002af2a57800000000125522280000000007139520000000000267b3000000000000b139d8000000000028b538000000000006c3f0000000000000ae40000000000000073800000000000000080000000000000000009463c47c8000000047f83e600000000020c71226400000000dda2c2bc0000000055920564000000001d8e19800000000008de97480000000002379ea400000000006eded000000000000f40400000000000013a7c0000000000000a2c000000000000000c000000000000000000058ba0496000000002e7a918e0000000017020128000000000aa59e9e00000000048a748a0000000001c03f8c00000000009825b000000000002bb8d400000000000a054e000000000001a9120000000000002a9800000000000001c2000000000000000200000000000000000002d86dba90000000017e63957000000000bdc2a480000000005812a2900000000025b28e90000000000e99dae00000000004fbdf8000000000017155e00000000000557d1000000000000e5d1000000000000178000000000000000ff00000000000000010000000000000000
  | 63 => 0x11ee15cfc000000008ac2bfc1800000003efeecbc800000001a85baa6800000000a317fa680000000038043ab00000000010b16a50000000000422b1100000000000cc52b000000000001ba5a80000000000022d380000000000001198000000000000001800000000000000000091fb48524000000046b5a031c0000000202790a8000000000d907942400000000539c17bc000000001ccd0d1800000000089d4b80000000000224f34000000000006a9ff400000000000e8ea40000000000012940000000000000098c000000000000000c00000000000000000048fd018560000000235a26e9c00000001013438e0000000006c7e41220000000029caced6000000000e64dba800000000044de6d0000000000112318e0000000000353a26000000000007427400000000000093f000000000000004ba000000000000000600000000000000000002b980dff0000000016cd862a000000000b44aa160000000005341c69000000000236b1550000000000d9d40c000000000049a3440000000000150c53000000000004c9eb000000000000c8fe00000000000013d200000000000000cd00000000000000010000000000000000
  | 64 => 0x18bb68fd800000000d10b86d8000000006880d3100000000030ec9b980000000015289b1800000000084c86700000000002e09c200000000000d98810000000000033b35800000000000903a8000000000000f9f00000000000000be800000000000000180000000000000000000109bb35c000000000991946000000000054257580000000002bbbb64000000000153f444000000000098052000000000003d3dd00000000000158be400000000000650ac0000000000016d80000000000000378800000000000004440000000000000014000000000000000000009091c3200000000053d75480000000002e6f8a8000000000185aa1a0000000000bf6382000000000056bc2000000000002387a000000000000cc59a000000000003da22000000000000e8080000000000002568000000000000032a0000000000000012000000000000000001dbf6efc2c0000000d50743609000000058eb9cb0a00000002229b839200000000bdff0be2000000003a6211ca000000000f5c12b400000000034db48500000000008aad8000000000000f7ea7000000000000f80600000000000005e400000000000000060000000000000000
  | 65 => 0x16212fcb800000000b9601320000000005bb279b0000000002a645ba800000000120e54280000000006f3168000000000025a3e200000000000ac5b680000000000273e980000000000066e20000000000000a190000000000000066800000000000000080000000000000000000b24e1900000000005d643a3c000000002e37fa4c000000001560d6cc00000000091c5f3c00000000038241d800000000013042f80000000000572068000000000013d828000000000003400400000000000051740000000000000334000000000000000400000000000000000005c27aaac000000003064f980000000001805ecee000000000b26eaa60000000004c5fa260000000001d91e700000000000a1525c00000000002e968600000000000abad8000000000001c8b00000000000002da200000000000001d60000000000000002000000000000000000003d6a67b0000000002325eac000000000132a59600000000009ddb0900000000004bcb9d000000000021657000000000000d32b4000000000004865d000000000001473f00000000000045ec00000000000009a2000000000000009900000000000000010000000000000000
  | 66 => 0x13b8e68820000000099d558ec00000000467cb756000000001e018949800000000bb02645000000000414f33c00000000013e10b800000000005105138000000000103e18000000000002525800000000000032ee00000000000001d9800000000000000300000000000000000000c04a81b400000000655f996000000000328eaf8800000000179a9444000000000a2cd5fc0000000003f9c36000000000015f40b000000000006726f400000000001859c4000000000004364000000000000073d80000000000000584000000000000000c0000000000000000000618050d8000000003372f3140000000019af8b5e000000000c01965600000000052ec17a00000000020730780000000000b37ebc000000000034d00200000000000c7db400000000000229dc0000000000003b7200000000000002ce000000000000000600000000000000000025239645a0000000120413a3000000000834ffd6c000000003782d57f000000001570c905000000000768c9cc000000000239a7a400000000008e8f8e00000000001be400000000000003d8940000000000004f98000000000000029500000000000000030000000000000000
  | 67 => 0x12bb40e5e800000009178124380000000424fa9b8800000001c0db5fa800000000ad843658000000003c05dc9000000000120c1730000000000485bea80000000000e2d62800000000001f53e80000000000028918000000000000150800000000000000180000000000000000000b51de274000000005f0934d8000000002f2330d00000000015dd4cd000000000095a080400000000039e6a3000000000013bdb8000000000005b4bc800000000001516b400000000000388680000000000005c1000000000000003e0000000000000000400000000000000000005a48fea4000000002f592f86000000001777cd3a000000000ae01bda0000000004a553060000000001cb72fc00000000009c44e400000000002d01c800000000000a56b0000000000001b75a0000000000002c0600000000000001ce000000000000000200000000000000000002d7b81590000000017dd3fd8000000000bd5b79800000000057cea7300000000025898790000000000e8363800000000004f0e88000000000016cb4b0000000000053e11000000000000df10000000000000166000000000000000eb00000000000000010000000000000000
  | 68 => 0x123067217800000008cedd2770000000040113d9e000000001b046a0b800000000a676521800000000394fba200000000011217f80000000000442be480000000000d39ff800000000001cd9500000000000024be000000000000012d8000000000000001800000000000000000091c64dbdc000000046990fc8800000002018f48c800000000d897490400000000536a16ec000000001cb8c6d0000000000895fe90000000000222b31400000000006a103c00000000000e743800000000000126380000000000000964000000000000000c000000000000000000497e0f9960000000239dc468200000001034bd490000000006d762296000000002a3487b6000000000e8d9ea400000000045bbb1000000000011629a40000000000362246000000000007688e00000000000097a000000000000004da000000000000000600000000000000000002c0dc33c00000000170e6fc5000000000b6685870000000005449ebb00000000023e19c70000000000dcd20200000000004ab0c60000000000155ac8000000000004db2e000000000000cb5b00000000000013e900000000000000c900000000000000010000000000000000
  | 69 => 0x1ebec4500000000011996f480000000009996a980000000004f1840000000000025ff75800000000010c13d000000000006a0fb00000000000246d1800000000000a524000000000000237b80000000000004f28000000000000051000000000000000080000000000000000009f4ea84d800000004db82df00000000023a455fcc00000000f3016bcc000000005ec51c08000000002124f030000000000a1b3a480000000002947ab8000000000084c6280000000000130b10000000000001a3640000000000000f4400000000000000180000000000000000000631b100e00000000345a5f88000000001a2b67d0000000000c3fecee00000000054bdd2600000000021391800000000000b82a5000000000003650ae00000000000ce0ce0000000000023c280000000000003d6000000000000002de0000000000000006000000000000000001df9b6270a0000000d6c985e55000000059b7a1fc00000000227f6d63600000000c00cc582000000003b1622b6000000000f9193c400000000035aed0d00000000008d3a0600000000000fd73f000000000000ff14000000000000061c00000000000000060000000000000000
  | 70 => 0x12e6719f30000000092e150408000000043020500800000001c5ff933000000000afb32508000000003cdc23900000000012543b1000000000049a39f80000000000e7710000000000002010b80000000000029ab800000000000015a000000000000000180000000000000000000b3ea5490000000005e538a90000000002ebc96b40000000015a65d2400000000093e757c000000000391a40000000000013682e800000000005956a40000000000147df800000000000364d000000000000056ac0000000000000384000000000000000400000000000000000005ae9638c000000002fb209760000000017a66376000000000af6f72a0000000004afa7e60000000001cfa88c00000000009dc3ec00000000002d728c00000000000a6fb8000000000001baba0000000000002c1a00000000000001c6000000000000000200000000000000000002e10a41d0000000018308a7c000000000c01d40a000000000592d4f7000000000262aa390000000000ec67d8000000000050986400000000001745150000000000055b95000000000000e3f400000000000016c600000000000000eb00000000000000010000000000000000
  | 71 => 0x15a3d690800000000b4f31b600000000059520a60000000002930c58800000000117dd5c80000000006b51d0000000000024291000000000000a496880000000000252cc800000000000605e000000000000094e000000000000005c800000000000000080000000000000000009423fecc0000000047d616914000000020b5b920000000000dd1e62d400000000555780e4000000001d7688f80000000008d62710000000000235063c00000000006e384800000000000f20fc00000000000136b000000000000009f4000000000000000c0000000000000000000580325dc000000002e0f46620000000016c5d9c2000000000a85abc600000000047a90360000000001b8f574000000000095217400000000002aa1a8000000000009b17800000000000195de00000000000027be0000000000000192000000000000000200000000000000000002c3fd7ed000000001729c4b7000000000b74964400000000054b5b3d0000000002410c710000000000ddf7ae00000000004b1210000000000015741a000000000004df6d000000000000cb7100000000000013c400000000000000c300000000000000010000000000000000
  | 72 => 0xfdb9f2701000000072263308800000002feff69740000000128d1a541800000006814b50d000000002054e40400000000089fbd080000000001e3819780000000005147390000000000096acc0000000000009fcc00000000000004398000000000000005000000000000000000789da7b7d8000000360a77de640000001695b9222800000008b088a858000000030692182800000000ee84d4d8000000003eeac420000000000d94192400000000023ca4e800000000004068cc00000000000411e800000000000019300000000000000018000000000000000000489cbbc4a00000002327ae80000000000ffa42b70000000006bc4fcea00000000297bbd8e000000000e465b200000000004438ca000000000010f38ee0000000000348c820000000000072600000000000000913000000000000004a20000000000000006000000000000000000249e81b31000000011bdc371200000000811d8f6a00000000367b8f1f0000000014fef91700000000073c30ec00000000022a38ec00000000008a056100000000001ad1fd000000000003a9a60000000000004abe000000000000026300000000000000030000000000000000
  | 73 => 0x12de1d85980000000929bf2d60000000042dff922800000001c5066a5000000000af4a9c78000000003cb4c8a000000000124759b0000000000496bc780000000000e6b83800000000001ff7c0000000000002993800000000000015a000000000000000180000000000000000000b5a95d98000000005f5040a8000000002f446c1c0000000015eb1c7400000000095ecd4c00000000039f8a3000000000013bd5b800000000005b174c000000000014f5f00000000000037c78000000000000598400000000000003a4000000000000000400000000000000000005bce55f2000000003033c6540000000017ec53f0000000000b1a7dc20000000004c072320000000001d6eab80000000000a0915000000000002e615e00000000000ab0a2000000000001c7dc0000000000002dc000000000000001da0000000000000002000000000000000000003da77aa000000000234f45a00000000013456f800000000009eebe300000000004c6f62000000000021c21c00000000000d63600000000000049d8d00000000000150ea000000000000493e0000000000000a7800000000000000b700000000000000020000000000000000
  | 74 => 0xf354a151900000006d146b8f380000002d9d19bca0000000118fc2bc40000000061e8e275000000001e2cc06d0000000007f77f220000000001b8947b800000000048a5fb0000000000082d46800000000000843c000000000000032f0000000000000003000000000000000000093b6a55740000000479ce29d00000000209976b6800000000dc4dc4f80000000054feeb3c000000001d549a000000000008cac0b0000000000231cd9000000000006d80c400000000000f0450000000000001343800000000000009e8000000000000000c0000000000000000004ab538e8a000000024407e1820000000108521b8a000000006fc7f3ec000000002b310e56000000000eeea47c00000000047c823c00000000011f85b0000000000038425a000000000007c156000000000000a03e000000000000052c000000000000000600000000000000000002cabcf0b000000001767f532000000000b96bf8600000000055d1751000000000249a5bd0000000000e1cc9c00000000004c9ad4000000000015fccb00000000000506af000000000000d3f600000000000014f200000000000000d500000000000000010000000000000000
  | 75 => 0xf00dfc21800000006b7f22c2000000002ce55080a000000011427f58200000000600eb2c3000000001d8a50fe0000000007c7447a0000000001acb1a70000000000465f3c000000000007df5e0000000000007e3c000000000000030200000000000000030000000000000000000917b8115800000004671f7e0c00000002005a900400000000d808f4e400000000532dabc4000000001ca19c1800000000088e2dc800000000022076b80000000000698c8000000000000e5d94000000000001239c000000000000093c000000000000000c0000000000000000004955e2860000000023888cfd80000000102a251d2000000006d26f3d2000000002a126a1a000000000e80518000000000045728f4000000000114d462000000000035d25c0000000000075ab8000000000000960e00000000000004c2000000000000000600000000000000000002bb4bfe90000000016dbf03c000000000b4b44e8000000000536c35c0000000002378bb90000000000d9fc080000000000499848000000000014fd44000000000004c1a1000000000000c614000000000000133000000000000000bc00000000000000010000000000000000
  | 76 => 0xe946f05180000000683a551cb00000002b6ab1f23000000010a3b9a61000000005c42fabd000000001c3e760e0000000007650d0e0000000001949022000000000041c2d60000000000074195000000000000720d00000000000002a7000000000000000300000000000000000075d9c4366400000034b274e73c00000015f8b477fc000000086e03eca800000002ecd1d77000000000e5990f98000000003c3b0d18000000000ce77df400000000021ac4ec00000000003bb944000000000003b10400000000000016300000000000000018000000000000000003b74aaf3f40000001a9ac137e40000000b1a0557880000000443758b3c000000017b2d6d7c00000000746dde78000000001e993d7000000000069234fc000000000113390400000000001ea54c000000000001e8180000000000000b8c000000000000000c00000000000000000023d847b45000000011561b693000000007dea53d2000000003501736b00000000145e3cff0000000006fe76f6000000000215611c000000000084121400000000001977a900000000000370c50000000000004516000000000000022900000000000000030000000000000000
  | 77 => 0x19a77f63000000000d997a780000000006d3b2640000000003366709800000000165f61b00000000008d912c000000000031a09000000000000ee1a78000000000039dfb000000000000a744000000000000134400000000000001098000000000000003000000000000000000000fa391180000000008f772200000000004e673800000000002878fac000000000138082800000000008a1fe0000000000036ef00000000000013018c00000000000571f800000000000131000000000000002c00000000000000030c000000000000000800000000000000000006526a61400000000358feb78000000001ada9e60000000000c9e1f2a00000000057b75dc000000000229db200000000000c1a600000000000039e0c200000000000e0244000000000002843800000000000049a000000000000003ea000000000000000c0000000000000000183640239bc000000a027e54e460000003d55bef8bc0000001572d7cdfa00000006b8a0722e00000001d71da93c000000006cd6f6e800000000142d32420000000002c84298000000000040b28a00000000000321e40000000000000dba000000000000000a0000000000000000
  | 78 => 0x1a089e4b000000000dd10c2d0000000006f1fe6c000000000346000980000000016d743b000000000090df3e000000000032efb000000000000f5512800000000003bee3000000000000ae6f000000000000144c000000000000011b8000000000000003000000000000000000000fc933b800000000090e5d980000000004f3cb0000000000028eeabc00000000013bd36800000000008bec90000000000037b3000000000000134984000000000005875800000000000135880000000000002c80000000000000030c0000000000000008000000000000000000489482da8000000023229def200000000ff74ef16000000006bab232000000000296e991a000000000e403cb4000000000440fdac00000000010e49a60000000000344324000000000007144e0000000000008e3a0000000000000464000000000000000600000000000000000002cbd9d930000000017723e68000000000b9c6bb20000000005600d6a00000000024b183d0000000000e273a000000000004cdedc000000000016151a0000000000050df7000000000000d5a8000000000000153600000000000000da00000000000000010000000000000000
  | 79 => 0x16e096da000000000c02a3108000000005f5d0e78000000002c41fbe00000000012f080b80000000007550f1000000000028023b00000000000b8fe4800000000002aaeb00000000000072038000000000000b8080000000000000790000000000000000800000000000000000000d8d93300000000007ad10200000000004226540000000000218dab00000000000fd2a2000000000006d0f80000000000029dec000000000000dcfe0000000000003b290000000000000baa000000000000016800000000000000110000000000000000000000000000000000049a716630000000023b21ff260000000103e26fa6000000006db5e704000000002a4c9dca000000000e95641c00000000045db1ac00000000011675d60000000000361cbc000000000007617a00000000000095ca00000000000004b0000000000000000600000000000000000002d5bda150000000017cbdf34000000000bccb49a0000000005788dfe000000000256a8890000000000e770b000000000004eca64000000000016b80400000000000539fd000000000000de84000000000000165600000000000000ea00000000000000010000000000000000
  | 80 => 0x1605270f000000000b862aa48000000005b2a6198000000002a1f8ef00000000011ee03180000000006e53ad0000000000254f3300000000000aa9ee8000000000026c82000000000000656b80000000000009ea8000000000000064000000000000000080000000000000000000b4dd5ef8000000005ede1054000000002f07c9bc0000000015cce488000000000950de4c000000000399b688000000000139b03800000000005a6ce4000000000014ccd000000000000375ec000000000000592400000000000003b000000000000000040000000000000000004a3ed3cd60000000240148e3e0000000106525bdc000000006ed4f49a000000002ac63126000000000ec3e08c00000000046d4fd800000000011ae4d00000000000371d560000000000078b820000000000009a0400000000000004de000000000000000600000000000000000002caec26a0000000017691450000000000b97007300000000055d01880000000002497bdb0000000000e1a98000000000004c84e6000000000015f1d40000000000050258000000000000d2b000000000000014b500000000000000d000000000000000010000000000000000
  | 81 => 0x1227c2c7d000000008ca29a57800000003fea6d3e800000001af19bb8000000000a5ef40480000000039188f7000000000110d81d000000000043c8b980000000000d2116000000000001c8ec800000000000242d8000000000000125000000000000000180000000000000000009417cfdd0000000047cff3620000000020b2d828400000000dd0aa7400000000055500354000000001d7426600000000008d597a8000000000234f90800000000006e3fa800000000000f254000000000000137bc0000000000000a10000000000000000c000000000000000000059bffdf6000000002f0eadc8000000001751a264000000000acdf0ea00000000049d711a0000000001c86ba000000000009b493800000000002cc2ba00000000000a4d1e000000000001b7880000000000002c6c00000000000001da00000000000000020000000000000000002448ea9630000000119010147000000007faba0080000000035cc06a90000000014b1e63b00000000071d708600000000021f5a98000000000086be4400000000001a063b000000000003858900000000000046e0000000000000023b00000000000000030000000000000000
  | 82 => 0x12a569b400000000090bc47bb0000000041eff7c1000000001bdfede3000000000ac3f7c88000000003b82cb400000000011dd150000000000047747280000000000df365000000000001ea5f0000000000002741000000000000013e000000000000000180000000000000000000b67b7848000000005fc37f58000000002f801b1c000000001607ee8800000000096b8e6c0000000003a495b000000000013d8cf800000000005b8f800000000000150d000000000000037e68000000000000594400000000000003980000000000000004000000000000000000069bd6db400000000382d5c08000000001c45d820000000000d5807de0000000005d4209c0000000002509da00000000000d0d30000000000003f066600000000000f7224000000000002d2080000000000005460000000000000049e000000000000000c000000000000000001dc97aae180000000d552ca81a0000000590cbf674000000022371b57400000000be4d47ca000000003a7b3f14000000000f62f25800000000034f341000000000008ae91400000000000f8386000000000000f7ec00000000000005dc00000000000000060000000000000000
  | 83 => 0x12dbca1f0800000009282da730000000042d049d0000000001c47574c800000000aefddbf8000000003c900d20000000001237cd000000000004911a980000000000e5102800000000001f9b100000000000028c8000000000000014e800000000000000180000000000000000000b767049400000000604bf5cc000000002fcb8ff800000000162f67c000000000097ede240000000003ad4858000000000141143000000000005ccefc0000000000156ab400000000000393540000000000005c4800000000000003c8000000000000000400000000000000000005c786212000000003093d81800000000181fe944000000000b348db00000000004ccac820000000001dc26200000000000a28ec800000000002f073c00000000000adc32000000000001d0380000000000002ebc00000000000001e800000000000000020000000000000000000037e3c5d0000000001fbbc4c000000000112468100000000008b9c8c0000000000421e4200000000001ca25000000000000b1132000000000003aede000000000000ff73000000000000333c0000000000000657000000000000005000000000000000000000000000000000
  | 84 => 0x16e5bc65800000000c067a780000000005f879a30000000002c5d50e8000000001300b5e800000000075dd4c000000000028464a00000000000bac9a800000000002b4f780000000000074b40000000000000bf9000000000000008280000000000000008000000000000000000934d255f000000004761ce44c0000000207a035b800000000db519b4c0000000054898224000000001d22b2680000000008b7dde000000000022bab6c00000000006be3b800000000000eb4840000000000012ad8000000000000097c000000000000000c00000000000000000005a676e84000000002f6a873a00000000178135e2000000000ae4ec740000000004a79ea60000000001cc739400000000009ca91400000000002d238600000000000a5ff0000000000001b9360000000000002c3e00000000000001d0000000000000000200000000000000000002da3aa920000000017f3d39d000000000be1c489000000000582f5b600000000025b67b30000000000e9663a00000000004f803a000000000016ef630000000000054728000000000000e0ab000000000000168700000000000000ec00000000000000010000000000000000
  | 85 => 0x1743fe81000000000c3a2ee800000000061341898000000002d2c498000000000135c59580000000007821c00000000000290c0300000000000be2de000000000002bf7000000000000075980000000000000bda800000000000007c000000000000000080000000000000000078a797bbf4000000360efd130000000016979f1db400000008b1410ed80000000306cf1ad000000000ee953d80000000003eedb248000000000d940ce800000000023c5ddc0000000000404c000000000000040c0c00000000000018b800000000000000180000000000000000004a1274d2e000000023eb3eaca0000000105af20c0000000006e8fc188000000002aac0266000000000ebb671400000000046b26f000000000011a8d5a00000000003720ae00000000000792060000000000009bb000000000000005040000000000000006000000000000000000255a57c9e0000000122018664000000008427c4800000000037e356400000000015983c9d000000000777341400000000023e36dc00000000008fc04500000000001c20ec000000000003e0d00000000000005034000000000000029a00000000000000030000000000000000
  | 86 => 0x166effbb000000000bc15b9d8000000005d20dc48000000002b19dec000000000126179580000000007159e30000000000266e2500000000000b044d800000000002833a00000000000069868000000000000a5b8000000000000069000000000000000080000000000000000000b84ac1b80000000060c74dfc00000000300a69b400000000164d1c3000000000098ba0ac0000000003b21cb80000000001429b8800000000005d2c2c00000000001576b000000000000392240000000000005b8c00000000000003b800000000000000040000000000000000004c0334748000000024ee853a4000000010dabc44600000000723ced7e000000002c3ac71a000000000f53e18800000000049e558c00000000012908f600000000003a5f44000000000008169c000000000000a80a000000000000056e000000000000000600000000000000000002d525d850000000017c4b16e000000000bc7b10a000000000575509c000000000254bb090000000000e6654400000000004e48e400000000001681a8000000000005272d000000000000d99a000000000000158600000000000000dc00000000000000010000000000000000
  | 87 => 0x1284fbe6e000000008fae97c700000000416bb7b5800000001ba36f59000000000aaa8b368000000003ae8f1600000000011aa3f300000000004693f200000000000dc34d000000000001e36900000000000026c6800000000000013f0000000000000001800000000000000000096bc72d2000000004932489580000000216229e3000000000e21bde80000000005778bd24000000001e48fc0000000000091dadf00000000002499e14000000000072f3e800000000000fea980000000000014b000000000000000ac8000000000000000c00000000000000000005abf84be000000002f9c8fc800000000179c42a4000000000af2b6ae0000000004ae2b0a0000000001cf4d0000000000009dc55800000000002d838e00000000000a7ab6000000000001bee80000000000002d0c00000000000001de0000000000000002000000000000000000253c6cc450000000120f7083800000000839ab48800000000379d06af000000001577a7d700000000076968a800000000023901a000000000008e0f3700000000001bae71000000000003ca600000000000004d78000000000000027700000000000000030000000000000000
  | 88 => 0x169f0edc000000000bdc19bd8000000005e027038000000002b894c28000000001294477800000000072a8e7000000000026e72b00000000000b28d20000000000028bb10000000000006aca8000000000000a6c8000000000000067800000000000000080000000000000000000badefc00000000006238b5ac0000000030ce78fc0000000016aec6540000000009b8a4fc0000000003c4f0380000000001498d1800000000005f55f0000000000015fe68000000000003a9140000000000005d8400000000000003bc0000000000000004000000000000000000007d0c45800000000047a9b920000000002723782000000000142f8a400000000009b6d1e000000000044ab9400000000001b3b04000000000009604a000000000002a9ec00000000000092ce000000000000146e00000000000001480000000000000002000000000000000001e6c2709f30000000da3c2508600000005b46b8d3b00000002326a5f2000000000c40b1dd0000000003c72c2dc000000000ff8854e0000000003741e820000000000920121000000000010781a0000000000010b05000000000000066c00000000000000060000000000000000
  | 89 => 0x130082dde8000000093bb4c9b00000000436da761000000001c91a472800000000b1050a78000000003d5e016000000000128029e00000000004a6d0680000000000ea52880000000000208b50000000000002a730000000000000162800000000000000180000000000000000000b68f8540000000005fcff190000000002f8785a400000000160c243000000000096dcf5c0000000003a5b52000000000013e0fc800000000005bc4700000000000151f4800000000000383700000000000005a3c00000000000003b000000000000000040000000000000000004b334f0a00000000248059b08000000010a37620400000000709d279a000000002b861542000000000f0c9a0800000000048574e0000000000121a26000000000003899d4000000000007c7600000000000009fa40000000000000516000000000000000600000000000000000002cb41cbf00000000176afec2000000000b9752fe00000000055cbd150000000002491c350000000000e15e5c00000000004c5774000000000015dba7000000000004f9cb000000000000d046000000000000144a00000000000000c900000000000000010000000000000000
  | 90 => 0x1742b668000000000c39c3a80000000006133a728000000002d2e04f000000000135e50380000000007839600000000000291a2d00000000000be9d7000000000002c23100000000000076680000000000000c01800000000000007f00000000000000008000000000000000007a76ec6b0c00000036eeac798000000016fcf2c84c00000008dbcdeb8c00000003171ce1c000000000f429bac0000000004095b2f8000000000dfca9540000000002507e44000000000043060000000000000443b40000000000001a7c000000000000001800000000000000000049becadaa000000023bf06fb400000001044d4b04000000006dea0932000000002a64513e000000000e9f48280000000004616838000000000117adea00000000003672b2000000000007740c000000000000988c00000000000004e20000000000000006000000000000000000253ed7326000000012118675a0000000083b2d9a10000000037ac656b0000000015805f7100000000076dcba400000000023aeeb200000000008ec64b00000000001be4f0000000000003d6360000000000004f07000000000000028b00000000000000030000000000000000
  | 91 => 0x12b97a98400000000916859098000000042476b18800000001c09a9a3000000000ad66dee8000000003bf9d930000000001207c65000000000048471880000000000e287b000000000001f472800000000000287f800000000000015000000000000000018000000000000000007978f9619400000036720fddc800000016c3711ee400000008c322456c000000030d6c49d000000000f0bfebf0000000003f897c68000000000db7e164000000000242af7c00000000004113d80000000000041b9c000000000000195c00000000000000180000000000000000004ab50e21c0000000243ffbdf400000001084a31e8000000006fc22cda000000002b2d841a000000000eecc6b000000000047baaa800000000011f34b00000000000382a58000000000007bc440000000000009fa000000000000005260000000000000006000000000000000000261191a1f0000000128014baa00000000871fffce0000000039431bc500000000162e3b9b0000000007b10464000000000251d22c000000000095604100000000001d69d700000000000416e6000000000000558200000000000002cd00000000000000030000000000000000
  | 92 => 0xc3ad468cb100000050f58470c00000001f085134e88000000add00ce9180000003688cd1ed00000000ef4518100000000037618d41000000000a4a7c3a00000000016c6d250000000000213ecc0000000000019e9f80000000000007288000000000000005000000000000000000771e31e3e8000000354e9e6fd0000000163f334ac0000000088b7f685400000002f80f969800000000e96c08e0000000003d5b67e0000000000d2dea240000000002281fa800000000003d7df0000000000003d3a000000000000017340000000000000018000000000000000003c2bd050580000001af304e95c0000000b41ec03a000000004542c899a0000000181901cf400000000769b4008000000001f3dde300000000006ba8bbe00000000011ae71000000000001faad4000000000001fc300000000000000c22000000000000000c000000000000000001e8595553e0000000daf8e8bbd00000005b982ef8a00000002346db60900000000c4c1fc5e000000003cab554a000000001007237c00000000037711dc0000000000926b8600000000001080ab0000000000010b5e000000000000067300000000000000060000000000000000
  | 93 => 0x19d9785a000000000db4e3a68000000006e1df7780000000033d3894000000000168f3c180000000008eba4d000000000032016300000000000ef95c800000000003a0e7000000000000a6ad80000000000012e880000000000000fb00000000000000028000000000000000000968f6e79000000004916224e4000000021519679c00000000e189fcd000000000572ea3f4000000001e26c9e800000000090fab78000000000244b13c0000000000718ac800000000000f9d1c00000000000140440000000000000a18000000000000000c00000000000000000006587e9f40000000035c29f76000000001af30dae000000000ca8b4dc00000000057f5e0e00000000022aed7c0000000000c1bdbc000000000039c23e00000000000dea800000000000027a6a000000000000474200000000000003a8000000000000000a0000000000000000000391450a4000000001e82ec1e000000000f7777e000000000075cd17f00000000033fdefc00000000014ea4e4000000000077d900000000000024f1f500000000000951b4000000000001c61a00000000000038a0000000000000037b000000000000000c0000000000000000
  | 94 => 0xf31bd97d280000006cfcf93e200000002d9495f630000000118d3bc350000000061e11874000000001e2d47d60000000007f8cf8c0000000001b9404a800000000048dafd800000000008371c000000000000850f000000000000033000000000000000030000000000000000000936f615d4000000047733fce8000000020825f07800000000db8d23a00000000054a1be3c000000001d2b87300000000008baaa1000000000022c68c000000000006c0b2400000000000eba780000000000012b680000000000000980000000000000000c0000000000000000004a14ede6a000000023e9597740000000105827a60000000006e6acc96000000002a93dd8e000000000eae2008000000000464f540000000000118266600000000003663a200000000000767ec000000000000960000000000000004b6000000000000000600000000000000000026236a483000000012882fbaf000000008754a31000000000395519550000000016329e8b0000000007b124fe0000000002513158000000000094f19a00000000001d3c6b0000000000040a99000000000000538800000000000002ab00000000000000030000000000000000
  | 95 => 0x1715e468800000000c1fecca000000000605047a0000000002cb7c7b0000000001324d8c8000000000769e3c00000000002874b800000000000bafd1000000000002b15480000000000072ae0000000000000b7a0000000000000077000000000000000080000000000000000009a70d18d400000004b1e3dd4400000002252dfeb400000000e8f93be4000000005a59616c000000001f5ee7b80000000009796078000000000262fab40000000000787534000000000010c16c0000000000015d9c0000000000000b54000000000000000c00000000000000000005db750fa00000000314749ba00000000187fd1c8000000000b64c32c0000000004e329e20000000001e5b6440000000000a62be0000000000030328a00000000000b2a7a000000000001df460000000000003088000000000000020000000000000000020000000000000000000349c2220000000001bede627000000000e0aeed700000000069e90600000000002e2f1cb000000000124cc6e000000000066d4a600000000001ee0e3000000000007819200000000000159f10000000000002759000000000000020a00000000000000050000000000000000
  | 96 => 0x12e48baa78000000092d0878c8000000042f93eeb000000001c5baf6f000000000af9449d8000000003ccfa7d000000000124fd6e0000000000498f4a80000000000e72b3800000000002008380000000000029ad000000000000015c000000000000000180000000000000000009572e97740000000488107c7800000002107c085c00000000df672ff800000000564579cc000000001dccfa600000000008f148e800000000023c08d400000000006f99f400000000000f4fd80000000000013a140000000000000a10000000000000000c00000000000000000005b945afe000000003012d1540000000017da7e14000000000b1163220000000004bc1dca0000000001d507b800000000009fd4f800000000002e21ee00000000000a9f36000000000001c45c0000000000002d5c00000000000001da000000000000000200000000000000000025a25e7ed0000000124422195000000008535726400000000385773a50000000015c547d700000000078671e20000000002427a68000000000090a37a00000000001c3a99000000000003df0b0000000000004f2c000000000000028300000000000000030000000000000000
  | 97 => 0x12dcd15af80000000928680b28000000042cf3abe800000001c454a64800000000aee333b8000000003c7fe6f000000000122fe7b000000000048dfe780000000000e41f5800000000001f68f800000000000286f800000000000014c8000000000000001800000000000000000098323ebdc000000049eec1660000000021bb2c79000000000e488e9cc00000000586de38c000000001e9e13600000000009367d4000000000024f378c000000000073c31c00000000000ff0c000000000000147900000000000000a6c000000000000000c00000000000000000005d5a777e000000003110db0c0000000018614e94000000000b548b1a0000000004db13ca0000000001e1fc680000000000a49df800000000002fa0be00000000000afdb6000000000001d4a40000000000002edc00000000000001e20000000000000002000000000000000001ebf8f74100000000dcc1b4f9400000005c6bd6122000000023a21297600000000c70236ba000000003d7786d00000000010463cf40000000003875eb4000000000095b72c000000000010f80400000000000114de00000000000006b200000000000000060000000000000000
  | 98 => 0xf50843e4880000006de6d482a80000002dfc76ac8000000011b7d482b8000000062deb17c000000001e80eecf0000000008107e620000000001bebedc800000000049d4eb80000000000855f780000000000087660000000000000347800000000000000300000000000000000009676906bc0000000490a058d40000000214c21cf000000000e1667adc000000005722200c000000001e234be800000000090f1dc0000000000244cee8000000000071acfc00000000000fabcc00000000000143f00000000000000a84000000000000000c000000000000000003df208cd460000001bcfabc30c0000000ba696efd8000000047ecc17d200000001920d4bf8000000007c502c400000000020f52198000000000728819c0000000001305fca0000000000229aec00000000000237600000000000000dd6000000000000000c0000000000000000002611d81ec000000012803b6070000000087214002000000003943b67500000000162e80290000000007b11f9a000000000251db8000000000009562db00000000001d6a5e00000000000416f5000000000000558200000000000002cd00000000000000030000000000000000
  | 99 => 0x1c67f7ca800000000f2bf6560000000007aebbd60000000003a6e76680000000019bd6848000000000a53bb800000000003af27800000000001210788000000000048352800000000000d8360000000000001a16000000000000017e80000000000000048000000000000000062ab5bc00100000028d9ac16508000000faba2426e400000057d9a861140000001b97f7dbb80000000793af211000000001c1b717880000000053bfc120000000000b9e72e0000000000110789800000000000d5adc0000000000003b7c0000000000000028000000000000000003d193385340000001b65ddfa880000000b76121b50000000046a21a4c2000000018a00542c000000007980f75000000000201abcb00000000006f12efa0000000001256af400000000002114f800000000000218400000000000000cf2000000000000000c000000000000000001e79ff37000000000da9e8d04700000005b6ed00690000000233546b6500000000c454c8c6000000003c856e5a000000000ffbbade0000000003743913000000000091df200000000000106e350000000000010a13000000000000066d00000000000000060000000000000000
  | 100 => 0x12fe51efe800000009395894d80000000434faf91000000001c7d9136800000000b048e0f8000000003cfd2e70000000001254f46000000000049692a00000000000e5710800000000001f79a800000000000282b0000000000000143800000000000000180000000000000000000cd2614a4000000006cb44f20000000003689a1680000000019a486fc000000000b2605b4000000000466d40000000000018a0590000000000075af7400000000001c6ac400000000000512e00000000000009258000000000000078c00000000000000140000000000000000004df8fe52e000000025f3215c60000000115a6fbc40000000075e2f33e000000002dc33a56000000000fe86bfc0000000004cf91e8000000000136bffc00000000003d62be0000000000088f1a000000000000b31c00000000000005d2000000000000000600000000000000000003439a515000000001bb64dbe000000000ded1d2400000000068f850b0000000002dbe67d000000000121cb24000000000065b17000000000001e82e1000000000007694d000000000001557a00000000000026e4000000000000020700000000000000050000000000000000
  | 101 => 0x1a36d30c800000000de946170000000006fdc38500000000034b296980000000016f66968000000000916f0e000000000033019200000000000f492d800000000003b450800000000000a9d9000000000000132300000000000000f980000000000000028000000000000000007bcd84236000000037951ebaf40000001748e860a400000008fbfb7ea80000000323923d5800000000f87aea380000000041e296f8000000000e502f48000000000260d6a000000000004541dc0000000000046fcc0000000000001b9800000000000000180000000000000000004a8efbd520000000242a7c41e0000000107919728000000006f64f2e4000000002b01cb9e000000000eda134c0000000004748e1000000000011ce3fe0000000000378eba0000000000079e820000000000009c3800000000000005000000000000000006000000000000000000258162b3400000001232ffabf0000000084af235b00000000381a1d720000000015ab91ad00000000077cc28600000000023f4c5600000000008fc4ef00000000001c0b92000000000003d8510000000000004ead000000000000028000000000000000030000000000000000
  | 102 => 0xfa34a1add0000000706b83f7680000002f234dbe700000001235073888000000065e852cb000000001f8f34650000000008622e620000000001d3538400000000004de1d5000000000008e51d80000000000092bd00000000000003998000000000000003000000000000000000096ef50294000000049484f2b40000000216a65fa000000000e241840c00000000577ce5dc000000001e45058800000000091a0180000000000247b98000000000007246c400000000000fc10c00000000000145600000000000000a84000000000000000c0000000000000000004c19d8a56000000024f7e2fdc000000010ddecf80000000007247dac2000000002c38eed6000000000f501c4800000000049bc490000000000127d526000000000039f626000000000007fe14000000000000a4d0000000000000054a000000000000000600000000000000000026957657c000000012c2a31860000000089176fa1000000003a1ef05f0000000016852ae50000000007cf461c00000000025aaeaa00000000009764c700000000001db66200000000000419ea000000000000546f00000000000002af00000000000000030000000000000000
  | 103 => 0xf3f3d79b500000006d60bfb5c00000002dbf680270000000119e0a4fa80000000623f91ab000000001e4a19480000000008001b620000000001baae2f8000000000490c8d0000000000083b2c000000000000855d000000000000033880000000000000030000000000000000007abedc65e0000000371004dc54000000170b5384b800000008e17bfd9c00000003192072d800000000f4c91d180000000040bedba0000000000e04f558000000000251a7000000000000431c3c00000000000443f80000000000001a740000000000000018000000000000000003ddac76bd00000001bc3a18f360000000ba0b4329e000000047c1c42660000000190ec5514000000007be2a76c0000000020d0b79c00000000071e502e00000000012e1f1800000000002240aa0000000000022f420000000000000d96000000000000000c00000000000000000025e3ce49800000001266b16bc000000008649d31f0000000038d8d5d90000000015fd3f9500000000079c699800000000024a1b7e000000000092e64b00000000001cc52e000000000003f79400000000000051e900000000000002a500000000000000030000000000000000
  | 104 => 0x1334f2a9680000000956039cf00000000443338f3000000001ce71f50800000000b31b56f8000000003e14cfe00000000012b455a00000000004b22b880000000000ebd5880000000000208e100000000000029f90000000000000158800000000000000180000000000000000009c2b2046800000004bfde1c74000000022bcd606c00000000ebdf5d04000000005b7faa44000000001fc5a1880000000009978df8000000000269deb80000000000797b10000000000010cbcc0000000000015a140000000000000afc000000000000000c000000000000000000071726202000000003c934188000000001ea9a748000000000e91a542000000000669e9e20000000002922a200000000000ea7f20000000000047b812000000000011dc1200000000000352c8000000000000658800000000000005b20000000000000012000000000000000018daf65caa3000000a4bed5220f0000003f3df40edb000000162d68ffaf00000006f910960e00000001eac41c9c0000000071f632300000000015440a040000000002f55993000000000045a56f0000000000036eef0000000000000f67000000000000000a0000000000000000
  | 105 => 0xc843ec96f8000000530217cbbd0000001fe2b650f50000000b30a708cf800000038585133f00000000f822142e0000000039b363be000000000ac96d9a80000000018118ee000000000023896f000000000001c2d700000000000007f580000000000000050000000000000000007bddaefe18000000379ac73520000000174a54026000000008fc0223b40000000323515b7800000000f84883800000000041c94520000000000e46bfa400000000025e43f8000000000044caa000000000000464800000000000001b540000000000000018000000000000000003e7d47e30c0000001c123aafcc0000000bc4616c22000000048b1ffd6e0000000196b0753c000000007ddcf04800000000216736b40000000007436d7400000000013538ec0000000000233234000000000002416e0000000000000e12000000000000000c000000000000000001f7a29d2520000000e26886c1000000005efe17da9000000024b7e950500000000cdb3de12000000003fc641f40000000010f715560000000003b3711600000000009e4a36000000000012246c0000000000012cdb000000000000076f00000000000000060000000000000000
  | 106 => 0x50507213947c00001eb7919b30e000000acffd6a5e6800000372e9f674ec000000fa1233203c0000003d344a38c00000000c7763549000000002008d1514000000003bd7f73c000000000475cde000000000002b52d800000000000089dc000000000000003c0000000000000000325d377e12a0000014e2826f6f2000000806cc37ae20000002d18eab6d80000000e33dfbcdc00000003e99c8f0800000000e92aca50000000002ba649820000000006192eba0000000000907192000000000007304a00000000000020c00000000000000014000000000000000001f8bfd36760000000e2e849e2600000005f32984de000000024cb3833200000000ce15764e000000003fdea8e40000000010fadaa40000000003b3394e00000000009df12e0000000000120952000000000001290a000000000000074200000000000000060000000000000000
  | _ => 0

def packedClass (u : ℕ) : ℕ := (packedClassPack (u / 4) >>> (877*(u % 4))) % 1007641851683931820587806291420968258893675472328417820220872324040744595635843008946260940337480903424595632540239579541935629958157893251896932560850028184716008537290582817399466548302510149103210893455908181007667595468047259786297601506742546990374638711734272

def packedRow (u : ℕ) := packedClass (stateIndex u)

def tab (n u : ℕ) : ℕ := (packedRow u >>> (64 * n)) % 1125899906842624

def radixSum : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | d+1, f => f 0 + 18446744073709551616 * radixSum d (fun i => f (i+1))

theorem radix_inj (d : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i < d, f i < 18446744073709551616) (hg : ∀ i < d, g i < 18446744073709551616)
    (h : radixSum d f = radixSum d g) : ∀ i < d, f i = g i := by
  induction d generalizing f g with
  | zero => omega
  | succ d ih =>
    simp only [radixSum] at h
    have f0 := hf 0 (by omega)
    have g0 := hg 0 (by omega)
    have e0 : f 0 = g 0 := by omega
    intro i hi
    cases i with
    | zero => exact e0
    | succ i => exact ih (fun j => f (j+1)) (fun j => g (j+1))
                    (fun j hj => hf _ (by omega)) (fun j hj => hg _ (by omega)) (by omega) i (by omega)

theorem radix_sum {α : Type} (s : Finset α) (d : ℕ) (f : α → ℕ → ℕ) :
    radixSum d (fun i => ∑ w ∈ s, f w i) = ∑ w ∈ s, radixSum d (f w) := by
  induction d generalizing f with
  | zero => simp [radixSum]
  | succ d ih =>
    simp only [radixSum, sum_add_distrib, ← mul_sum]
    rw [ih (fun w i => f w (i+1))]

def subsetSum : ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ
  | 0, _, b, f => f b
  | k+1, u, b, f => subsetSum k u b f +
      if u.testBit k then subsetSum k u (b+2^k) f else 0

theorem subHigh {k i : ℕ} (hi : i < 2^k) (u : ℕ) :
    ((2^k+i) &&& u = 2^k+i) ↔ u.testBit k = true ∧ (i &&& u) = i := by
  have hlt : (i &&& u) < 2^k := Nat.and_le_left.trans_lt hi
  rw [Nat.add_comm (2^k) i, ← Nat.or_two_pow_eq_add_of_lt hi, Nat.and_or_distrib_right,
    Nat.land_comm (2^k) u, Nat.and_two_pow]
  cases h : u.testBit k <;>
    simp [Nat.or_two_pow_eq_add_of_lt hi, Nat.or_two_pow_eq_add_of_lt hlt] <;> omega

theorem subsetSum_eq (k u b : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ range (2^k), if i &&& u = i then f (b+i) else 0) = subsetSum k u b f := by
  induction k generalizing b with
  | zero => simp [subsetSum]
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, sum_range_add, ih, subsetSum]
    congr 1
    by_cases h : u.testBit k = true
    · rw [if_pos h, ← ih]
      apply sum_congr rfl
      intro i hi
      simp only [subHigh (mem_range.mp hi), h, true_and, Nat.add_assoc]
    · rw [if_neg h]
      apply sum_eq_zero
      intro i hi
      rw [if_neg (fun q => h ((subHigh (mem_range.mp hi) u).mp q).1)]

theorem subsetSum_step (u : Fin 4096) (f : ℕ → ℕ) :
    (∑ w ∈ subs u, if compc w.val u.val = true then f w.val else 0) =
      subsetSum 12 u.val 0 (fun w => if compc w u.val = true then f w else 0) := by
  unfold subs
  rw [sum_filter]
  simp only [beq_iff_eq]
  rw [← subsetSum_eq]
  simp only [Nat.zero_add]
  exact Fin.sum_univ_eq_sum_range (fun w => if w &&& u.val = w then
    (if compc w u.val = true then f w else 0) else 0) 4096


def parents (u : Fin 4096) := (subs u).filter (fun w => compc w.val u.val = true)

def inputRow (u : ℕ) := packedRow u % (2 ^ 832)
def outputRow (u : ℕ) := packedRow u >>> 64

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem packInput : ∀ u : Fin 4096, radixSum 13 (fun i => tab i u.val) = inputRow u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem packOutput : ∀ u : Fin 4096, radixSum 13 (fun i => tab (i+1) u.val) = outputRow u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

set_option maxRecDepth 65536 in
theorem step0 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*0+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step1 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*1+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step2 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*2+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step3 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*3+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step4 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*4+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step5 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*5+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step6 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*6+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step7 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*7+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step8 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*8+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step9 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*9+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step10 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*10+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step11 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*11+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step12 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*12+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step13 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*13+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step14 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*14+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step15 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*15+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step16 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*16+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step17 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*17+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step18 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*18+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step19 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*19+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step20 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*20+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step21 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*21+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step22 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*22+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step23 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*23+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step24 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*24+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step25 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*25+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step26 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*26+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step27 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*27+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step28 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*28+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step29 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*29+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step30 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*30+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step31 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*31+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step32 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*32+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step33 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*33+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step34 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*34+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step35 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*35+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step36 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*36+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step37 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*37+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step38 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*38+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step39 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*39+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step40 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*40+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step41 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*41+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step42 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*42+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step43 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*43+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step44 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*44+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step45 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*45+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step46 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*46+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step47 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*47+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step48 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*48+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step49 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*49+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step50 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*50+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step51 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*51+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step52 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*52+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step53 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*53+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step54 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*54+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step55 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*55+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step56 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*56+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step57 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*57+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step58 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*58+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step59 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*59+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step60 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*60+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step61 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*61+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step62 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*62+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxRecDepth 65536 in
theorem step63 : ∀ i : Fin 64, let u : Fin 4096 := ⟨64*63+i.val,by omega⟩; subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by decide +kernel

set_option maxHeartbeats 1600000 in
theorem packedStep (u : Fin 4096) : subsetSum 12 u.val 0 (fun w => if compc w u.val = true then inputRow w else 0) = outputRow u.val := by
  let i : Fin 64 := ⟨u.val % 64, Nat.mod_lt _ (by decide)⟩
  have hu := u.isLt
  generalize h : u.val / 64 = j
  have hj : j < 64 := by omega
  interval_cases j

  · have e : u = ⟨64*0+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step0 i

  · have e : u = ⟨64*1+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step1 i

  · have e : u = ⟨64*2+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step2 i

  · have e : u = ⟨64*3+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step3 i

  · have e : u = ⟨64*4+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step4 i

  · have e : u = ⟨64*5+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step5 i

  · have e : u = ⟨64*6+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step6 i

  · have e : u = ⟨64*7+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step7 i

  · have e : u = ⟨64*8+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step8 i

  · have e : u = ⟨64*9+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step9 i

  · have e : u = ⟨64*10+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step10 i

  · have e : u = ⟨64*11+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step11 i

  · have e : u = ⟨64*12+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step12 i

  · have e : u = ⟨64*13+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step13 i

  · have e : u = ⟨64*14+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step14 i

  · have e : u = ⟨64*15+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step15 i

  · have e : u = ⟨64*16+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step16 i

  · have e : u = ⟨64*17+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step17 i

  · have e : u = ⟨64*18+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step18 i

  · have e : u = ⟨64*19+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step19 i

  · have e : u = ⟨64*20+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step20 i

  · have e : u = ⟨64*21+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step21 i

  · have e : u = ⟨64*22+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step22 i

  · have e : u = ⟨64*23+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step23 i

  · have e : u = ⟨64*24+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step24 i

  · have e : u = ⟨64*25+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step25 i

  · have e : u = ⟨64*26+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step26 i

  · have e : u = ⟨64*27+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step27 i

  · have e : u = ⟨64*28+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step28 i

  · have e : u = ⟨64*29+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step29 i

  · have e : u = ⟨64*30+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step30 i

  · have e : u = ⟨64*31+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step31 i

  · have e : u = ⟨64*32+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step32 i

  · have e : u = ⟨64*33+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step33 i

  · have e : u = ⟨64*34+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step34 i

  · have e : u = ⟨64*35+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step35 i

  · have e : u = ⟨64*36+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step36 i

  · have e : u = ⟨64*37+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step37 i

  · have e : u = ⟨64*38+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step38 i

  · have e : u = ⟨64*39+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step39 i

  · have e : u = ⟨64*40+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step40 i

  · have e : u = ⟨64*41+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step41 i

  · have e : u = ⟨64*42+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step42 i

  · have e : u = ⟨64*43+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step43 i

  · have e : u = ⟨64*44+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step44 i

  · have e : u = ⟨64*45+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step45 i

  · have e : u = ⟨64*46+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step46 i

  · have e : u = ⟨64*47+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step47 i

  · have e : u = ⟨64*48+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step48 i

  · have e : u = ⟨64*49+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step49 i

  · have e : u = ⟨64*50+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step50 i

  · have e : u = ⟨64*51+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step51 i

  · have e : u = ⟨64*52+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step52 i

  · have e : u = ⟨64*53+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step53 i

  · have e : u = ⟨64*54+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step54 i

  · have e : u = ⟨64*55+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step55 i

  · have e : u = ⟨64*56+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step56 i

  · have e : u = ⟨64*57+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step57 i

  · have e : u = ⟨64*58+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step58 i

  · have e : u = ⟨64*59+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step59 i

  · have e : u = ⟨64*60+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step60 i

  · have e : u = ⟨64*61+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step61 i

  · have e : u = ⟨64*62+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step62 i

  · have e : u = ⟨64*63+i.val,by dsimp [i]; omega⟩ := Fin.ext (by dsimp [i]; omega)
    rw [e]
    exact step63 i

theorem transfer (u : Fin 4096) (n : ℕ) (hn : n < 13) : (∑ w ∈ subs u, if compc w.val u.val = true then tab n w.val else 0) = tab (n+1) u.val := by
  have pack : radixSum 13 (fun i => ∑ w ∈ parents u, tab i w.val) =
      radixSum 13 (fun i => tab (i+1) u.val) := by
    rw [radix_sum (parents u) 13 (fun w i => tab i w.val),packOutput]
    simp only [packInput,parents,sum_filter,subsetSum_step]
    exact packedStep u
  have bound (i w : ℕ) : tab i w ≤ 1125899906842624 := (Nat.mod_lt _ (by decide)).le
  have sumBound (i : ℕ) : (∑ w ∈ parents u, tab i w.val) < 18446744073709551616 := by
    have h := sum_le_sum (s:=parents u) (fun w _ => bound i w.val)
    have hc : (parents u).card ≤ 4096 := by simpa only [Fintype.card_fin] using (parents u).card_le_univ
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at h
    omega
  have h := radix_inj _ _ _ (fun i _ => sumBound i) (fun i _ => (bound (i+1) u.val).trans_lt (by decide)) pack n hn
  simpa only [parents,sum_filter] using h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem start : ∀ u : Fin 4096, G 0 u = tab 0 u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

theorem table_ok (n : ℕ) (hn : n ≤ 13) : ∀ u : Fin 4096, G n u = tab n u.val := by
  induction n with
  | zero => exact start
  | succ n ih =>
    intro u
    rw [G_succ]
    simp only [ih (by omega)]
    exact transfer u n (by omega)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem baseCert : ∀ u : Fin 4096, tab 13 u.val + 78 * tab 11 u.val + 715 * tab 9 u.val + 1716 * tab 7 u.val + 1287 * tab 5 u.val + 286 * tab 3 u.val + 13 * tab 1 u.val = 13 * tab 12 u.val + 286 * tab 10 u.val + 1287 * tab 8 u.val + 1716 * tab 6 u.val + 715 * tab 4 u.val + 78 * tab 2 u.val + tab 0 u.val := by
  apply blocks
  intro j
  fin_cases j <;> decide +kernel

theorem recurrenceVec (m : ℕ) : ∀ u : Fin 4096, G (m + 13) u + 78 * G (m + 11) u + 715 * G (m + 9) u + 1716 * G (m + 7) u + 1287 * G (m + 5) u + 286 * G (m + 3) u + 13 * G (m + 1) u = 13 * G (m + 12) u + 286 * G (m + 10) u + 1287 * G (m + 8) u + 1716 * G (m + 6) u + 715 * G (m + 4) u + 78 * G (m + 2) u + G m u := by
  induction m with
  | zero =>
    intro u
    simp only [Nat.zero_add]
    simpa only [table_ok 0 (by decide) u, table_ok 1 (by decide) u, table_ok 2 (by decide) u, table_ok 3 (by decide) u, table_ok 4 (by decide) u, table_ok 5 (by decide) u, table_ok 6 (by decide) u, table_ok 7 (by decide) u, table_ok 8 (by decide) u, table_ok 9 (by decide) u, table_ok 10 (by decide) u, table_ok 11 (by decide) u, table_ok 12 (by decide) u, table_ok 13 (by decide) u] using (show G 13 u + 78 * G 11 u + 715 * G 9 u + 1716 * G 7 u + 1287 * G 5 u + 286 * G 3 u + 13 * G 1 u = 13 * G 12 u + 286 * G 10 u + 1287 * G 8 u + 1716 * G 6 u + 715 * G 4 u + 78 * G 2 u + G 0 u from by
      rw [table_ok 0 (by decide) u, table_ok 1 (by decide) u, table_ok 2 (by decide) u, table_ok 3 (by decide) u, table_ok 4 (by decide) u, table_ok 5 (by decide) u, table_ok 6 (by decide) u, table_ok 7 (by decide) u, table_ok 8 (by decide) u, table_ok 9 (by decide) u, table_ok 10 (by decide) u, table_ok 11 (by decide) u, table_ok 12 (by decide) u, table_ok 13 (by decide) u]
      exact baseCert u)
  | succ m ih =>
    intro u
    rw [show m + 1 + 1 = (m+1)+1 by omega, show m + 1 + 2 = (m+2)+1 by omega, show m + 1 + 3 = (m+3)+1 by omega, show m + 1 + 4 = (m+4)+1 by omega, show m + 1 + 5 = (m+5)+1 by omega, show m + 1 + 6 = (m+6)+1 by omega, show m + 1 + 7 = (m+7)+1 by omega, show m + 1 + 8 = (m+8)+1 by omega, show m + 1 + 9 = (m+9)+1 by omega, show m + 1 + 10 = (m+10)+1 by omega, show m + 1 + 11 = (m+11)+1 by omega, show m + 1 + 12 = (m+12)+1 by omega, show m + 1 + 13 = (m+13)+1 by omega]
    rw [G_succ (m + 13), G_succ (m + 12), G_succ (m + 11), G_succ (m + 10), G_succ (m + 9), G_succ (m + 8), G_succ (m + 7), G_succ (m + 6), G_succ (m + 5), G_succ (m + 4), G_succ (m + 3), G_succ (m + 2), G_succ (m + 1), G_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs
    · exact ih w
    · rfl

theorem recurrence (n : ℕ) (hn : 13 < n) : (a n : ℤ) = 13 * a (n - 1) - 78 * a (n - 2) + 286 * a (n - 3) - 715 * a (n - 4) + 1287 * a (n - 5) - 1716 * a (n - 6) + 1716 * a (n - 7) - 1287 * a (n - 8) + 715 * a (n - 9) - 286 * a (n - 10) + 78 * a (n - 11) - 13 * a (n - 12) + a (n - 13) := by
  obtain ⟨m,rfl⟩ : ∃ m, n = m + 13 := ⟨n-13,by omega⟩
  have h : (a (m + 13) : ℤ) + 78 * (a (m + 11) : ℤ) + 715 * (a (m + 9) : ℤ) + 1716 * (a (m + 7) : ℤ) + 1287 * (a (m + 5) : ℤ) + 286 * (a (m + 3) : ℤ) + 13 * (a (m + 1) : ℤ) = 13 * (a (m + 12) : ℤ) + 286 * (a (m + 10) : ℤ) + 1287 * (a (m + 8) : ℤ) + 1716 * (a (m + 6) : ℤ) + 715 * (a (m + 4) : ℤ) + 78 * (a (m + 2) : ℤ) + (a m : ℤ) := by
    simp only [a_eq_G]
    exact_mod_cast recurrenceVec m 4095
  simp only [show m+13-1 = (m + 12) by omega, show m+13-2 = (m + 11) by omega, show m+13-3 = (m + 10) by omega, show m+13-4 = (m + 9) by omega, show m+13-5 = (m + 8) by omega, show m+13-6 = (m + 7) by omega, show m+13-7 = (m + 6) by omega, show m+13-8 = (m + 5) by omega, show m+13-9 = (m + 4) by omega, show m+13-10 = (m + 3) by omega, show m+13-11 = (m + 2) by omega, show m+13-12 = (m + 1) by omega, show m+13-13 = m by omega]
  linarith

open PowerSeries in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 1500000 in
theorem generating : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 13 =
      X * (15 + 8628 * X + 596285 * X ^ 2 + 10163642 * X ^ 3 + 60659998 * X ^ 4
        + 149218290 * X ^ 5 + 162389570 * X ^ 6 + 78777198 * X ^ 7 + 16029715 * X ^ 8
        + 1141682 * X ^ 9 + 16577 * X ^ 10) := by
  let F : ℕ → ℚ := (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  change PowerSeries.mk F * _ = _

  have lhs : PowerSeries.mk F * (1-X)^13 = C 1 * (PowerSeries.mk F * X ^ 0) - C 13 * (PowerSeries.mk F * X ^ 1) + C 78 * (PowerSeries.mk F * X ^ 2) - C 286 * (PowerSeries.mk F * X ^ 3) + C 715 * (PowerSeries.mk F * X ^ 4) - C 1287 * (PowerSeries.mk F * X ^ 5) + C 1716 * (PowerSeries.mk F * X ^ 6) - C 1716 * (PowerSeries.mk F * X ^ 7) + C 1287 * (PowerSeries.mk F * X ^ 8) - C 715 * (PowerSeries.mk F * X ^ 9) + C 286 * (PowerSeries.mk F * X ^ 10) - C 78 * (PowerSeries.mk F * X ^ 11) + C 13 * (PowerSeries.mk F * X ^ 12) - C 1 * (PowerSeries.mk F * X ^ 13) := by simp only [map_one,map_ofNat]; ring
  have rhs : (X * (15 + 8628 * X + 596285 * X ^ 2 + 10163642 * X ^ 3 + 60659998 * X ^ 4
        + 149218290 * X ^ 5 + 162389570 * X ^ 6 + 78777198 * X ^ 7 + 16029715 * X ^ 8
        + 1141682 * X ^ 9 + 16577 * X ^ 10) : ℚ⟦X⟧) = C 15 * X ^ 1 + C 8628 * X ^ 2 + C 596285 * X ^ 3 + C 10163642 * X ^ 4 + C 60659998 * X ^ 5 + C 149218290 * X ^ 6 + C 162389570 * X ^ 7 + C 78777198 * X ^ 8 + C 16029715 * X ^ 9 + C 1141682 * X ^ 10 + C 16577 * X ^ 11 := by simp only [map_one,map_ofNat]; ring
  rw [lhs,rhs]
  ext k
  simp only [map_sub,map_add,coeff_C_mul_X_pow]
  simp only [coeff_C_mul,coeff_mul_X_pow',coeff_mk]

  by_cases hk : k < 14
  ·

    have v1 : a 1 = 15 := (a_eq_G 1).trans ((table_ok 1 (by decide) 4095).trans (by decide +kernel))

    have v2 : a 2 = 8823 := (a_eq_G 2).trans ((table_ok 2 (by decide) 4095).trans (by decide +kernel))

    have v3 : a 3 = 709814 := (a_eq_G 3).trans ((table_ok 3 (by decide) 4095).trans (by decide +kernel))

    have v4 : a 4 = 18707320 := (a_eq_G 4).trans ((table_ok 4 (by decide) 4095).trans (by decide +kernel))

    have v5 : a 5 = 251002319 := (a_eq_G 5).trans ((table_ok 5 (by decide) 4095).trans (by decide +kernel))

    have v6 : a 6 = 2149795141 := (a_eq_G 6).trans ((table_ok 6 (by decide) 4095).trans (by decide +kernel))

    have v7 : a 7 = 13385651492 := (a_eq_G 7).trans ((table_ok 7 (by decide) 4095).trans (by decide +kernel))

    have v8 : a 8 = 65717571120 := (a_eq_G 8).trans ((table_ok 8 (by decide) 4095).trans (by decide +kernel))

    have v9 : a 9 = 268511791119 := (a_eq_G 9).trans ((table_ok 9 (by decide) 4095).trans (by decide +kernel))

    have v10 : a 10 = 948021599547 := (a_eq_G 10).trans ((table_ok 10 (by decide) 4095).trans (by decide +kernel))

    have v11 : a 11 = 2972106528666 := (a_eq_G 11).trans ((table_ok 11 (by decide) 4095).trans (by decide +kernel))

    have v12 : a 12 = 8443442678840 := (a_eq_G 12).trans ((table_ok 12 (by decide) 4095).trans (by decide +kernel))

    have v13 : a 13 = 22076610372895 := (a_eq_G 13).trans ((table_ok 13 (by decide) 4095).trans (by decide +kernel))

    interval_cases k

    · simp only [F, if_pos (show 0 ≤ 0 by decide), if_neg (show ¬ 1 ≤ 0 by decide), if_neg (show ¬ 2 ≤ 0 by decide), if_neg (show ¬ 3 ≤ 0 by decide), if_neg (show ¬ 4 ≤ 0 by decide), if_neg (show ¬ 5 ≤ 0 by decide), if_neg (show ¬ 6 ≤ 0 by decide), if_neg (show ¬ 7 ≤ 0 by decide), if_neg (show ¬ 8 ≤ 0 by decide), if_neg (show ¬ 9 ≤ 0 by decide), if_neg (show ¬ 10 ≤ 0 by decide), if_neg (show ¬ 11 ≤ 0 by decide), if_neg (show ¬ 12 ≤ 0 by decide), if_neg (show ¬ 13 ≤ 0 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 1 by decide), if_pos (show 1 ≤ 1 by decide), if_neg (show ¬ 2 ≤ 1 by decide), if_neg (show ¬ 3 ≤ 1 by decide), if_neg (show ¬ 4 ≤ 1 by decide), if_neg (show ¬ 5 ≤ 1 by decide), if_neg (show ¬ 6 ≤ 1 by decide), if_neg (show ¬ 7 ≤ 1 by decide), if_neg (show ¬ 8 ≤ 1 by decide), if_neg (show ¬ 9 ≤ 1 by decide), if_neg (show ¬ 10 ≤ 1 by decide), if_neg (show ¬ 11 ≤ 1 by decide), if_neg (show ¬ 12 ≤ 1 by decide), if_neg (show ¬ 13 ≤ 1 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 2 by decide), if_pos (show 1 ≤ 2 by decide), if_pos (show 2 ≤ 2 by decide), if_neg (show ¬ 3 ≤ 2 by decide), if_neg (show ¬ 4 ≤ 2 by decide), if_neg (show ¬ 5 ≤ 2 by decide), if_neg (show ¬ 6 ≤ 2 by decide), if_neg (show ¬ 7 ≤ 2 by decide), if_neg (show ¬ 8 ≤ 2 by decide), if_neg (show ¬ 9 ≤ 2 by decide), if_neg (show ¬ 10 ≤ 2 by decide), if_neg (show ¬ 11 ≤ 2 by decide), if_neg (show ¬ 12 ≤ 2 by decide), if_neg (show ¬ 13 ≤ 2 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 3 by decide), if_pos (show 1 ≤ 3 by decide), if_pos (show 2 ≤ 3 by decide), if_pos (show 3 ≤ 3 by decide), if_neg (show ¬ 4 ≤ 3 by decide), if_neg (show ¬ 5 ≤ 3 by decide), if_neg (show ¬ 6 ≤ 3 by decide), if_neg (show ¬ 7 ≤ 3 by decide), if_neg (show ¬ 8 ≤ 3 by decide), if_neg (show ¬ 9 ≤ 3 by decide), if_neg (show ¬ 10 ≤ 3 by decide), if_neg (show ¬ 11 ≤ 3 by decide), if_neg (show ¬ 12 ≤ 3 by decide), if_neg (show ¬ 13 ≤ 3 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 4 by decide), if_pos (show 1 ≤ 4 by decide), if_pos (show 2 ≤ 4 by decide), if_pos (show 3 ≤ 4 by decide), if_pos (show 4 ≤ 4 by decide), if_neg (show ¬ 5 ≤ 4 by decide), if_neg (show ¬ 6 ≤ 4 by decide), if_neg (show ¬ 7 ≤ 4 by decide), if_neg (show ¬ 8 ≤ 4 by decide), if_neg (show ¬ 9 ≤ 4 by decide), if_neg (show ¬ 10 ≤ 4 by decide), if_neg (show ¬ 11 ≤ 4 by decide), if_neg (show ¬ 12 ≤ 4 by decide), if_neg (show ¬ 13 ≤ 4 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 5 by decide), if_pos (show 1 ≤ 5 by decide), if_pos (show 2 ≤ 5 by decide), if_pos (show 3 ≤ 5 by decide), if_pos (show 4 ≤ 5 by decide), if_pos (show 5 ≤ 5 by decide), if_neg (show ¬ 6 ≤ 5 by decide), if_neg (show ¬ 7 ≤ 5 by decide), if_neg (show ¬ 8 ≤ 5 by decide), if_neg (show ¬ 9 ≤ 5 by decide), if_neg (show ¬ 10 ≤ 5 by decide), if_neg (show ¬ 11 ≤ 5 by decide), if_neg (show ¬ 12 ≤ 5 by decide), if_neg (show ¬ 13 ≤ 5 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 6 by decide), if_pos (show 1 ≤ 6 by decide), if_pos (show 2 ≤ 6 by decide), if_pos (show 3 ≤ 6 by decide), if_pos (show 4 ≤ 6 by decide), if_pos (show 5 ≤ 6 by decide), if_pos (show 6 ≤ 6 by decide), if_neg (show ¬ 7 ≤ 6 by decide), if_neg (show ¬ 8 ≤ 6 by decide), if_neg (show ¬ 9 ≤ 6 by decide), if_neg (show ¬ 10 ≤ 6 by decide), if_neg (show ¬ 11 ≤ 6 by decide), if_neg (show ¬ 12 ≤ 6 by decide), if_neg (show ¬ 13 ≤ 6 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 7 by decide), if_pos (show 1 ≤ 7 by decide), if_pos (show 2 ≤ 7 by decide), if_pos (show 3 ≤ 7 by decide), if_pos (show 4 ≤ 7 by decide), if_pos (show 5 ≤ 7 by decide), if_pos (show 6 ≤ 7 by decide), if_pos (show 7 ≤ 7 by decide), if_neg (show ¬ 8 ≤ 7 by decide), if_neg (show ¬ 9 ≤ 7 by decide), if_neg (show ¬ 10 ≤ 7 by decide), if_neg (show ¬ 11 ≤ 7 by decide), if_neg (show ¬ 12 ≤ 7 by decide), if_neg (show ¬ 13 ≤ 7 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 8 by decide), if_pos (show 1 ≤ 8 by decide), if_pos (show 2 ≤ 8 by decide), if_pos (show 3 ≤ 8 by decide), if_pos (show 4 ≤ 8 by decide), if_pos (show 5 ≤ 8 by decide), if_pos (show 6 ≤ 8 by decide), if_pos (show 7 ≤ 8 by decide), if_pos (show 8 ≤ 8 by decide), if_neg (show ¬ 9 ≤ 8 by decide), if_neg (show ¬ 10 ≤ 8 by decide), if_neg (show ¬ 11 ≤ 8 by decide), if_neg (show ¬ 12 ≤ 8 by decide), if_neg (show ¬ 13 ≤ 8 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 9 by decide), if_pos (show 1 ≤ 9 by decide), if_pos (show 2 ≤ 9 by decide), if_pos (show 3 ≤ 9 by decide), if_pos (show 4 ≤ 9 by decide), if_pos (show 5 ≤ 9 by decide), if_pos (show 6 ≤ 9 by decide), if_pos (show 7 ≤ 9 by decide), if_pos (show 8 ≤ 9 by decide), if_pos (show 9 ≤ 9 by decide), if_neg (show ¬ 10 ≤ 9 by decide), if_neg (show ¬ 11 ≤ 9 by decide), if_neg (show ¬ 12 ≤ 9 by decide), if_neg (show ¬ 13 ≤ 9 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 10 by decide), if_pos (show 1 ≤ 10 by decide), if_pos (show 2 ≤ 10 by decide), if_pos (show 3 ≤ 10 by decide), if_pos (show 4 ≤ 10 by decide), if_pos (show 5 ≤ 10 by decide), if_pos (show 6 ≤ 10 by decide), if_pos (show 7 ≤ 10 by decide), if_pos (show 8 ≤ 10 by decide), if_pos (show 9 ≤ 10 by decide), if_pos (show 10 ≤ 10 by decide), if_neg (show ¬ 11 ≤ 10 by decide), if_neg (show ¬ 12 ≤ 10 by decide), if_neg (show ¬ 13 ≤ 10 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 11 by decide), if_pos (show 1 ≤ 11 by decide), if_pos (show 2 ≤ 11 by decide), if_pos (show 3 ≤ 11 by decide), if_pos (show 4 ≤ 11 by decide), if_pos (show 5 ≤ 11 by decide), if_pos (show 6 ≤ 11 by decide), if_pos (show 7 ≤ 11 by decide), if_pos (show 8 ≤ 11 by decide), if_pos (show 9 ≤ 11 by decide), if_pos (show 10 ≤ 11 by decide), if_pos (show 11 ≤ 11 by decide), if_neg (show ¬ 12 ≤ 11 by decide), if_neg (show ¬ 13 ≤ 11 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false, if_true]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 12 by decide), if_pos (show 1 ≤ 12 by decide), if_pos (show 2 ≤ 12 by decide), if_pos (show 3 ≤ 12 by decide), if_pos (show 4 ≤ 12 by decide), if_pos (show 5 ≤ 12 by decide), if_pos (show 6 ≤ 12 by decide), if_pos (show 7 ≤ 12 by decide), if_pos (show 8 ≤ 12 by decide), if_pos (show 9 ≤ 12 by decide), if_pos (show 10 ≤ 12 by decide), if_pos (show 11 ≤ 12 by decide), if_pos (show 12 ≤ 12 by decide), if_neg (show ¬ 13 ≤ 12 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
      norm_num

    · simp only [F, if_pos (show 0 ≤ 13 by decide), if_pos (show 1 ≤ 13 by decide), if_pos (show 2 ≤ 13 by decide), if_pos (show 3 ≤ 13 by decide), if_pos (show 4 ≤ 13 by decide), if_pos (show 5 ≤ 13 by decide), if_pos (show 6 ≤ 13 by decide), if_pos (show 7 ≤ 13 by decide), if_pos (show 8 ≤ 13 by decide), if_pos (show 9 ≤ 13 by decide), if_pos (show 10 ≤ 13 by decide), if_pos (show 11 ≤ 13 by decide), if_pos (show 12 ≤ 13 by decide), if_pos (show 13 ≤ 13 by decide), Nat.reduceSub, Nat.sub_zero, Nat.reduceEqDiff, if_pos rfl, if_false]
      rw [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13]
      norm_num

  · have eqr := recurrence (k+0) (by omega)
    have hq : (a (k+0) : ℚ) = 13 * a (k+0-1) - 78 * a (k+0-2) + 286 * a (k+0-3) - 715 * a (k+0-4) + 1287 * a (k+0-5) - 1716 * a (k+0-6) + 1716 * a (k+0-7) - 1287 * a (k+0-8) + 715 * a (k+0-9) - 286 * a (k+0-10) + 78 * a (k+0-11) - 13 * a (k+0-12) + a (k+0-13) := by exact_mod_cast eqr
    simp only [F, if_pos (show 0 ≤ k by omega), if_pos (show 1 ≤ k by omega), if_pos (show 2 ≤ k by omega), if_pos (show 3 ≤ k by omega), if_pos (show 4 ≤ k by omega), if_pos (show 5 ≤ k by omega), if_pos (show 6 ≤ k by omega), if_pos (show 7 ≤ k by omega), if_pos (show 8 ≤ k by omega), if_pos (show 9 ≤ k by omega), if_pos (show 10 ≤ k by omega), if_pos (show 11 ≤ k by omega), if_pos (show 12 ≤ k by omega), if_pos (show 13 ≤ k by omega), if_neg (show k ≠ 1 by omega), if_neg (show k ≠ 2 by omega), if_neg (show k ≠ 3 by omega), if_neg (show k ≠ 4 by omega), if_neg (show k ≠ 5 by omega), if_neg (show k ≠ 6 by omega), if_neg (show k ≠ 7 by omega), if_neg (show k ≠ 8 by omega), if_neg (show k ≠ 9 by omega), if_neg (show k ≠ 10 by omega), if_neg (show k ≠ 11 by omega), Nat.sub_zero, if_neg (show k ≠ 0 by omega), if_neg (show k-1 ≠ 0 by omega), if_neg (show k-2 ≠ 0 by omega), if_neg (show k-3 ≠ 0 by omega), if_neg (show k-4 ≠ 0 by omega), if_neg (show k-5 ≠ 0 by omega), if_neg (show k-6 ≠ 0 by omega), if_neg (show k-7 ≠ 0 by omega), if_neg (show k-8 ≠ 0 by omega), if_neg (show k-9 ≠ 0 by omega), if_neg (show k-10 ≠ 0 by omega), if_neg (show k-11 ≠ 0 by omega), if_neg (show k-12 ≠ 0 by omega), if_neg (show k-13 ≠ 0 by omega)]
    simp only [Nat.add_zero] at hq
    linarith

end OMA.WindowCount

theorem OMA.solution : type_of% @OMA.S_oeis_a249967.main := ⟨OMA.WindowCount.generating, OMA.WindowCount.recurrence⟩

